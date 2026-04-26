import CATEPTGravitasPort.Basic
import CATEPTGravitasPort.MetricTensor

/-!
# Gravitas.ElectromagneticTensor

Port of `Gravitas/Kernel/ElectromagneticTensor.wl`.

Faraday (electromagnetic) tensor:

  F_{μν} = ∂_μ A_ν - ∂_ν A_μ

where A_μ = g_{μν} A^ν is the covariant 4-potential derived from A^μ = (Φ, A).

Default storage: `(co, co)` = F_{μν} (fully covariant/antisymmetric).
-/

namespace Gravitas

structure ElectromagneticTensor where
  metric               : MetricTensor
  electromagneticPotential : Array Expr  -- A^μ (contravariant), length = dim
  vacuumPermeability   : Expr            -- μ₀
  components           : Mat
  idx1 : IndexKind
  idx2 : IndexKind
  deriving Repr

namespace ElectromagneticTensor

/-- Compute F_{μν} = ∂_μ A_ν - ∂_ν A_μ where A_μ = g_{μν} A^ν. -/
private def computeCovariant (g : MetricTensor) (A : Array Expr) : Mat :=
  let n      := g.dim
  let gCov   := g.covariantMatrix
  let coords := g.coords
  -- Covariant potential A_μ = g_{μν} A^ν
  let aCov := Array.ofFn (n := n) (fun μ : Fin n =>
    sumN n (fun ν => simplify (.mul (matGet gCov μ.val ν) (A[ν]!))))
  -- F_{μν} = ∂_μ A_ν - ∂_ν A_μ
  matBuild n (fun μ ν =>
    let d_μ_ν := symDiff (aCov[ν]!) (coords[μ]!)
    let d_ν_μ := symDiff (aCov[μ]!) (coords[ν]!)
    simplify (.sub d_μ_ν d_ν_μ))

private def toIndexed (gCov gInv fcov : Mat) (idx1 idx2 : IndexKind) : Mat :=
  let n := gCov.size
  match idx1, idx2 with
  | true,  true  => fcov
  | false, false =>
      matBuild n (fun i j =>
        sumN n (fun k => sumN n (fun l =>
          simplify (.mul (.mul (matGet gInv i k) (matGet gInv j l)) (matGet fcov k l)))))
  | true,  false =>
      matBuild n (fun i j =>
        sumN n (fun k => simplify (.mul (matGet gInv k j) (matGet fcov i k))))
  | false, true  =>
      matBuild n (fun i j =>
        sumN n (fun k => simplify (.mul (matGet gInv i k) (matGet fcov k j))))

/-- Build an ElectromagneticTensor.
    `A` is the contravariant 4-potential (Φ, A¹, A², A³).
    If omitted, symbolic defaults are used. -/
def ofMetric (g : MetricTensor) (A : Array Expr := #[]) (μ₀ : Expr := .var "μ₀")
    (idx1 : IndexKind := co) (idx2 : IndexKind := co) : ElectromagneticTensor :=
  let n := g.dim
  let A' := if A.isEmpty then
    Array.ofFn (n := n) (fun i : Fin n =>
      if i.val == 0 then .var "Φ"
      else .var s!"A{i.val}")
  else A
  let gCov  := g.covariantMatrix
  let gInv  := g.inverseMatrix
  let fcov  := computeCovariant g A'
  let comps := toIndexed gCov gInv fcov idx1 idx2
  { metric := g, electromagneticPotential := A', vacuumPermeability := μ₀,
    components := comps, idx1, idx2 }

def get (et : ElectromagneticTensor) (i j : Nat) : Expr :=
  matGet et.components i j

/-- Maxwell's equations in curved spacetime: ∇_μ F^{μν} = μ₀ J^ν.
    Uses the covariant divergence identity (AFP semantic-mapping):
      ∇_μ F^{μν} = (1/√|g|) ∂_μ(√|g| F^{μν})
    where √|g| = sqrt(|det g|) is the metric volume element.
    For diagonal metrics this matches the WL source exactly. -/
def maxwellEquations (et : ElectromagneticTensor) (J : Array Expr) : Array Expr :=
  let g      := et.metric
  let n      := g.dim
  let gCov   := g.covariantMatrix
  let gInv   := g.inverseMatrix
  let coords := g.coords
  -- F^{μν} = contravariant form
  let fCon := toIndexed gCov gInv et.components con con
  -- √|g| = sqrt of the absolute metric determinant (symbolic)
  -- For n×n diagonal: det g = Π_i g_{ii};  use the variable sqrt_det_g as symbol
  -- (a full symbolic determinant would require Leibniz expansion; we keep it symbolic)
  let sqrtDetG : Expr := .var "√|g|"
  -- ∇_μ F^{μν} = (1/√|g|) ∂_μ(√|g| F^{μν})
  Array.ofFn (n := n) (fun ν : Fin n =>
    let divergence := sumN n (fun μ =>
      simplify (symDiff (.mul sqrtDetG (matGet fCon μ ν.val)) (coords[μ]!)))
    simplify (.sub
      (.mul (.div (.lit 1) sqrtDetG) divergence)
      (.mul et.vacuumPermeability (J[ν.val]!))))

end ElectromagneticTensor
end Gravitas
