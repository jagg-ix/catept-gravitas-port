import CATEPTGravitasPort.Basic
import CATEPTGravitasPort.MetricTensor
import CATEPTGravitasPort.ADMDecomposition
import CATEPTGravitasPort.ADMStressEnergyDecomposition
import CATEPTGravitasPort.SolveADMEquations

/-!
# Gravitas.SolveVacuumADMEquations

Port of `Gravitas/Kernel/SolveVacuumADMEquations.wl`.

Vacuum ADM equations (T_{μν} = 0):

Hamiltonian constraint (vacuum):
  ³R + K² - K_{ij} K^{ij} = 0

Momentum constraint (vacuum):
  ∇^j K_{ij} - ∇_i K = 0

Evolution equations are the same as in the matter case with ρ = 0, j_i = 0.
-/

namespace Gravitas

-- ---------------------------------------------------------------------------
-- Vacuum ADM solution
-- ---------------------------------------------------------------------------

structure VacuumADMSolution where
  adm                   : ADMDecomposition
  /-- Hamiltonian constraint ³R + K² - K_{ij}K^{ij} = 0. -/
  hamiltonianConstraint  : Expr
  /-- Momentum constraints ∇^j K_{ij} - ∇_i K = 0. -/
  momentumConstraints    : Array Expr
  /-- ∂_t γ_{ij} evolution residuals. -/
  metricEvolution        : Mat
  /-- ∂_t K_{ij} evolution residuals. -/
  extrinEvolution        : Mat
  deriving Repr

namespace VacuumADMSolution

/-- Build the vacuum ADM solution for a given ADM decomposition. -/
def ofADM (adm : ADMDecomposition) : VacuumADMSolution :=
  -- Use zero stress-energy
  let g4    := ADMDecomposition.spacetimeMetric adm
  let zeroT : StressEnergyTensor :=
    { metric := g4,
      components := matBuild g4.dim (fun _ _ => .lit 0),
      idx1 := co, idx2 := co }
  let zeroDecomp : ADMStressEnergyDecomposition :=
    { adm := adm, stressEnergy := zeroT,
      energyDensity := .lit 0,
      momentumDensity := Array.replicate adm.spatialMetric.dim (.lit 0),
      stressTensor := matBuild adm.spatialMetric.dim (fun _ _ => .lit 0) }
  let sol := ADMSolution.ofADM adm zeroDecomp (.lit 0)
  { adm := adm,
    hamiltonianConstraint := sol.hamiltonianConstraint,
    momentumConstraints := sol.momentumConstraints,
    metricEvolution := sol.metricEvolution,
    extrinEvolution := sol.extrinEvolution }

end VacuumADMSolution

-- ---------------------------------------------------------------------------
-- Top-level API
-- ---------------------------------------------------------------------------

def solveVacuumADMEquations (adm : ADMDecomposition) : VacuumADMSolution :=
  VacuumADMSolution.ofADM adm

/-- Solve for all named ADM slicings. -/
def solveVacuumADMEquationsNamed (name : String) : Option VacuumADMSolution :=
  ADMDecomposition.named name |>.map VacuumADMSolution.ofADM

end Gravitas
