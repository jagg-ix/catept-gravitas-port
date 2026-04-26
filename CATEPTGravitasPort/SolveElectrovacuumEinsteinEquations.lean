import CATEPTGravitasPort.Basic
import CATEPTGravitasPort.MetricTensor
import CATEPTGravitasPort.ElectromagneticTensor
import CATEPTGravitasPort.StressEnergyTensor
import CATEPTGravitasPort.EinsteinTensor
import CATEPTGravitasPort.SolveEinsteinEquations

/-!
# Gravitas.SolveElectrovacuumEinsteinEquations

Port of `Gravitas/Kernel/SolveElectrovacuumEinsteinEquations.wl`.

Electrovacuum Einstein–Maxwell equations:

  G_{μν} = 8πG T_{μν}^{EM}
  ∇_μ F^{μν} = 0          (source-free Maxwell)
  ∇_{[μ} F_{νρ]} = 0      (Bianchi for F, automatic from F = dA)

where the electromagnetic stress-energy is:

  T_{μν}^{EM} = (1/μ₀) [F_{μα} F^α_ν - (1/4) g_{μν} F_{αβ} F^{αβ}]
-/

namespace Gravitas

-- ---------------------------------------------------------------------------
-- Electrovacuum solution structure
-- ---------------------------------------------------------------------------

structure ElectrovacuumSolution where
  metric             : MetricTensor
  faradayTensor      : ElectromagneticTensor
  cosmologicalConst  : Expr
  /-- G_{μν} - 8πG T^{EM}_{μν} = 0 (residual). -/
  einsteinEquations  : Mat
  /-- ∇_μ F^{μν} = 0 residuals (source-free Maxwell). -/
  maxwellEquations   : Array Expr
  /-- Bianchi identities for F (trivial from F = dA). -/
  bianchiIdentity    : Array Expr
  einsteinTensor     : EinsteinTensor
  deriving Repr

namespace ElectrovacuumSolution

/-- Covariant Maxwell equations: ∇_μ F^{μν} = (1/√|g|) ∂_μ(√|g| F^{μν}).
    AFP semantic-mapping: uses the exact covariant form matching ElectromagneticTensor.maxwellEquations. -/
private def maxwellResiduals (g : MetricTensor) (F : ElectromagneticTensor) : Array Expr :=
  let n    := g.dim
  let gCov := g.covariantMatrix
  let gInv := g.inverseMatrix
  let fCon : Mat := matBuild n (fun i j =>
    sumN n (fun k => sumN n (fun l =>
      simplify (.mul (.mul (matGet gInv i k) (matGet gInv j l)) (matGet F.components k l)))))
  let sqrtDetG : Expr := .var "√|g|"
  Array.ofFn (n := n) (fun ν : Fin n =>
    let divergence := sumN n (fun μ =>
      simplify (symDiff (.mul sqrtDetG (matGet fCon μ ν.val)) (g.coords[μ]!)))
    simplify (.mul (.div (.lit 1) sqrtDetG) divergence))

/-- Build the electrovacuum solution. -/
def ofMetric (g : MetricTensor) (A : Array Expr := #[]) (μ₀ : Expr := .var "μ₀")
    (Λ : Expr := .lit 0) : ElectrovacuumSolution :=
  let F  := ElectromagneticTensor.ofMetric g A μ₀
  -- Electromagnetic stress-energy
  let st := StressEnergyTensor.electromagneticField g F.components μ₀
  let sol := EinsteinSolution.ofStressEnergy st Λ
  let maxwell := maxwellResiduals g F
  -- Bianchi: ∂_{[μ} F_{νρ]} = 0  — trivial from F = dA, store as zeros
  let bianchi := Array.replicate g.dim (.lit 0)
  { metric := g, faradayTensor := F, cosmologicalConst := Λ,
    einsteinEquations := sol.fieldEquations,
    maxwellEquations := maxwell,
    bianchiIdentity := bianchi,
    einsteinTensor := sol.einsteinTensor }

end ElectrovacuumSolution

-- ---------------------------------------------------------------------------
-- Top-level API
-- ---------------------------------------------------------------------------

/-- Solve the Einstein-Maxwell equations for a metric and 4-potential A^μ. -/
def solveElectrovacuumEinsteinEquations (g : MetricTensor) (A : Array Expr := #[])
    (μ₀ : Expr := .var "μ₀") (Λ : Expr := .lit 0) : ElectrovacuumSolution :=
  ElectrovacuumSolution.ofMetric g A μ₀ Λ

end Gravitas
