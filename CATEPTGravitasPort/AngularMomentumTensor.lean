import CATEPTGravitasPort.Basic
import CATEPTGravitasPort.MetricTensor
import CATEPTGravitasPort.StressEnergyTensor

/-!
# Gravitas.AngularMomentumTensor

Port of `Gravitas/Kernel/AngularMomentumTensor.wl`.

Canonical angular momentum tensor:

  J^{μν} = ∫_Σ (x^μ T^{νλ} - x^ν T^{μλ}) dΣ_λ

where x^μ are the coordinate position vector components, T^{μν} is the
(contravariant) stress-energy tensor, dΣ_λ is the hypersurface element,
and the integral is over a Cauchy surface Σ.

In the algebraic port the integral is represented symbolically as a product
of the integrand with a volume element symbol `dΩ`.
-/

namespace Gravitas

structure AngularMomentumTensor where
  stressEnergy     : StressEnergyTensor
  positionVector   : Array Expr   -- x^μ (contravariant)
  spacetimeBoundary : Expr        -- the boundary Ω symbol
  surfaceElement   : Array Expr   -- dΣ_λ for each λ
  components       : Mat          -- J^{μν} (without integration)
  idx1 : IndexKind
  idx2 : IndexKind
  deriving Repr

namespace AngularMomentumTensor

/-- Compute the integrand  M^{μν}_λ = x^μ T^{νλ} - x^ν T^{μλ}. -/
private def integrandContracted (n : Nat) (T : Mat) (x dSig : Array Expr)
    (idx1 idx2 : IndexKind) : Mat :=
  -- J^{μν} = Σ_λ (x^μ T^{νλ} - x^ν T^{μλ}) dΣ_λ
  -- Here T is stored as contravariant (false,false).
  matBuild n (fun μ ν =>
    sumN n (fun lam_ =>
      simplify (.mul
        (.sub (.mul (x[μ]!) (matGet T ν lam_))
              (.mul (x[ν]!) (matGet T μ lam_)))
        (dSig[lam_]!))))

private def toIndexed (gCov gInv jcov : Mat) (idx1 idx2 : IndexKind) : Mat :=
  let n := gCov.size
  match idx1, idx2 with
  | false, false => jcov   -- we store contra by default
  | true,  true  =>
      matBuild n (fun i j =>
        sumN n (fun k => sumN n (fun l =>
          simplify (.mul (.mul (matGet gCov i k) (matGet gCov j l)) (matGet jcov k l)))))
  | false, true  =>
      matBuild n (fun i j =>
        sumN n (fun k => simplify (.mul (matGet gCov k j) (matGet jcov i k))))
  | true,  false =>
      matBuild n (fun i j =>
        sumN n (fun k => simplify (.mul (matGet gCov i k) (matGet jcov k j))))

/-- Build an AngularMomentumTensor.
    - `st`  : StressEnergyTensor (must include metric)
    - `x`   : position vector x^μ (contravariant; defaults to coordinate symbols)
    - `dΩ`  : spacetime boundary symbol (default "∂Ω")
    - `dΣ`  : surface element array (defaults to dΣ_λ symbols)
-/
def ofStressEnergy (st : StressEnergyTensor)
    (x : Array Expr := #[])
    (dΩ : Expr := .var "∂Ω")
    (dSig : Array Expr := #[])
    (idx1 : IndexKind := con)
    (idx2 : IndexKind := con) : AngularMomentumTensor :=
  let g  := st.metric
  let n  := g.dim
  -- Ensure contravariant stress-energy  T^{μν} = g^{μk} g^{νl} T_{kl}
  let gInv_ := g.inverseMatrix
  let tCon := matBuild n (fun μ ν =>
    sumN n (fun k => sumN n (fun l =>
      simplify (.mul (.mul (matGet gInv_ μ k) (matGet gInv_ ν l)) (matGet st.components k l)))))
  let x' := if x.isEmpty then
    Array.ofFn (n := n) (fun i : Fin n => .var s!"X{i.val}") else x
  let dSig' := if dSig.isEmpty then
    Array.ofFn (n := n) (fun i : Fin n => .var s!"dΣ{i.val}") else dSig
  let jCon := integrandContracted n tCon x' dSig' idx1 idx2
  let comps := toIndexed g.covariantMatrix g.inverseMatrix jCon idx1 idx2
  { stressEnergy := st, positionVector := x', spacetimeBoundary := dΩ,
    surfaceElement := dSig', components := comps, idx1, idx2 }

def get (jt : AngularMomentumTensor) (i j : Nat) : Expr :=
  matGet jt.components i j

end AngularMomentumTensor
end Gravitas
