import CATEPTGravitasPort.Basic
import CATEPTGravitasPort.MetricTensor
import CATEPTGravitasPort.RiemannTensor

/-!
# Gravitas.ElectrograviticTensor

Port of `Gravitas/Kernel/ElectrograviticTensor.wl`.

Electrogravitic (tidal) tensor — the "electric" part of the Riemann curvature
measured by a timelike observer with 4-velocity u^μ:

  E_{μν} = R_{μρνσ} u^ρ u^σ

where R_{μρνσ} is the all-covariant Riemann tensor.  This matches the WL source
`ElectrograviticTensor.wl` which uses `covariantRiemannTensor`, not the Weyl tensor.

Default storage: `(co, co)` = E_{μν} (fully covariant).
-/

namespace Gravitas

structure ElectrograviticTensor where
  metric            : MetricTensor
  timelikeCongruence : Array Expr  -- 4-velocity u^μ (contravariant components)
  components        : Mat
  idx1 : IndexKind
  idx2 : IndexKind
  deriving Repr

namespace ElectrograviticTensor

/-- Compute E_{μν} = R_{μρνσ} u^ρ u^σ (all-covariant Riemann, matching WL source). -/
private def computeCovariant (g : MetricTensor) (u : Array Expr) : Mat :=
  let n      := g.dim
  let gCov   := g.covariantMatrix
  let gInv   := g.inverseMatrix
  let rMixed := RiemannTensor.computeMixed gCov gInv g.coords
  -- Get all-covariant Riemann R_{ρσμν}
  let covR := RiemannTensor.convertIndices n gCov gInv rMixed co co co co
  let getR := fun a b c d => RiemannTensor.getComp n covR a b c d
  matBuild n (fun μ ν =>
    sumN n (fun ρ => sumN n (fun σ =>
      simplify (.mul (.mul (getR μ ρ ν σ) (u[ρ]!)) (u[σ]!)))))

private def toIndexed (gCov gInv ecov : Mat) (idx1 idx2 : IndexKind) : Mat :=
  let n := gCov.size
  match idx1, idx2 with
  | true,  true  => ecov
  | false, false =>
      matBuild n (fun i j =>
        sumN n (fun k => sumN n (fun l =>
          simplify (.mul (.mul (matGet gInv i k) (matGet gInv j l)) (matGet ecov k l)))))
  | true,  false =>
      matBuild n (fun i j =>
        sumN n (fun k => simplify (.mul (matGet gInv k j) (matGet ecov i k))))
  | false, true  =>
      matBuild n (fun i j =>
        sumN n (fun k => simplify (.mul (matGet gInv i k) (matGet ecov k j))))

/-- Build an ElectrograviticTensor.
    `u` is the contravariant 4-velocity array (length = dim).
    If `u` is empty the default symbolic congruence X^μ is used. -/
def ofMetric (g : MetricTensor) (u : Array Expr := #[])
    (idx1 : IndexKind := co) (idx2 : IndexKind := co) : ElectrograviticTensor :=
  let n := g.dim
  let u' := if u.isEmpty then
    Array.ofFn (n := n) (fun i : Fin n => .var s!"X{i.val}")
  else u
  let gCov  := g.covariantMatrix
  let gInv  := g.inverseMatrix
  let ecov  := computeCovariant g u'
  let comps := toIndexed gCov gInv ecov idx1 idx2
  { metric := g, timelikeCongruence := u', components := comps, idx1, idx2 }

def get (et : ElectrograviticTensor) (i j : Nat) : Expr :=
  matGet et.components i j

end ElectrograviticTensor
end Gravitas
