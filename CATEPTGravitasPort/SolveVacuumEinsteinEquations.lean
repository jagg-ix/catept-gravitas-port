import CATEPTGravitasPort.Basic
import CATEPTGravitasPort.MetricTensor
import CATEPTGravitasPort.RicciTensor
import CATEPTGravitasPort.EinsteinTensor
import CATEPTGravitasPort.StressEnergyTensor
import CATEPTGravitasPort.SolveEinsteinEquations

/-!
# Gravitas.SolveVacuumEinsteinEquations

Port of `Gravitas/Kernel/SolveVacuumEinsteinEquations.wl`.

Vacuum Einstein equations (T_{μν} = 0):

  G_{μν} = 0  ⟺  R_{μν} = 0

(In vacuum without cosmological constant the Ricci tensor must vanish.)

With cosmological constant Λ:

  G_{μν} + Λ g_{μν} = 0  ⟺  R_{μν} = Λ g_{μν}
-/

namespace Gravitas

-- ---------------------------------------------------------------------------
-- Vacuum solution structure
-- ---------------------------------------------------------------------------

/-- Vacuum Einstein solution: G_{μν} + Λ g_{μν} = 0. -/
structure VacuumEinsteinSolution where
  metric             : MetricTensor
  cosmologicalConst  : Expr
  /-- R_{μν} - Λ g_{μν} = 0 (residual matrix; vacuum iff this vanishes). -/
  fieldEquations     : Mat
  /-- Einstein tensor G_{μν}. -/
  einsteinTensor     : EinsteinTensor
  /-- Ricci scalar R. -/
  ricciScalar        : Expr
  /-- True if the metric is (syntactically) Ricci-flat: R_{μν} = 0. -/
  isRicciFlat        : Bool
  deriving Repr

namespace VacuumEinsteinSolution

/-- Build the vacuum Einstein solution for a given metric and cosmological constant. -/
def ofMetric (g : MetricTensor) (Λ : Expr := .lit 0) : VacuumEinsteinSolution :=
  let rt   := RicciTensor.ofMetric g
  let et   := EinsteinTensor.ofMetric g
  let R    := RicciTensor.ricciScalar g
  let gCov := g.covariantMatrix
  let n    := g.dim
  -- Vacuum equations: R_{μν} - Λ g_{μν} = 0
  let eqs := matBuild n (fun μ ν =>
    simplify (.sub (matGet rt.components μ ν)
                   (.mul Λ (matGet gCov μ ν))))
  -- Check if Ricci-flat (syntactically)
  let isFlat := rt.components.all (fun row => row.all (· == .lit 0))
  { metric := g, cosmologicalConst := Λ,
    fieldEquations := eqs, einsteinTensor := et,
    ricciScalar := R, isRicciFlat := isFlat }

end VacuumEinsteinSolution

-- ---------------------------------------------------------------------------
-- Top-level API
-- ---------------------------------------------------------------------------

/-- Symbolically "solve" the vacuum Einstein equations for a metric. -/
def solveVacuumEinsteinEquations (g : MetricTensor) (Λ : Expr := .lit 0)
    : VacuumEinsteinSolution :=
  VacuumEinsteinSolution.ofMetric g Λ

/-- Vacuum equations as a `VacuumEinsteinSolution` via the stress-energy route:
    zero T_{μν} gives the same result. -/
def solveVacuumViaStressEnergy (g : MetricTensor) (Λ : Expr := .lit 0)
    : EinsteinSolution :=
  let zeroT : StressEnergyTensor :=
    { metric := g,
      components := matBuild g.dim (fun _ _ => .lit 0),
      idx1 := co, idx2 := co }
  EinsteinSolution.ofStressEnergy zeroT Λ

end Gravitas
