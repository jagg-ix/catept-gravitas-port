import CATEPTGravitasPort.Basic
import CATEPTGravitasPort.MetricTensor
import CATEPTGravitasPort.RicciTensor
import CATEPTGravitasPort.EinsteinTensor
import CATEPTGravitasPort.StressEnergyTensor

/-!
# Gravitas.SolveEinsteinEquations

Port of `Gravitas/Kernel/SolveEinsteinEquations.wl`.

Einstein field equations (with cosmological constant Λ):

  G_{μν} + Λ g_{μν} = 8πG T_{μν}

`EinsteinSolution` packages the equations, their integrability conditions,
and related data.  Since Lean 4 is not a CAS, we represent the equations
symbolically as matrices of `Expr` residuals rather than "solving" them;
the structure mirrors what the WL implementation stores for display.
-/

namespace Gravitas

-- ---------------------------------------------------------------------------
-- EinsteinSolution structure
-- ---------------------------------------------------------------------------

/-- The result of `SolveEinsteinEquations`: the symbolic Einstein equations and
    their associated data. -/
structure EinsteinSolution where
  stressEnergy       : StressEnergyTensor
  cosmologicalConst  : Expr
  /-- G_{μν} + Λ g_{μν} - 8πG T_{μν} = 0 (residual matrix). -/
  fieldEquations     : Mat
  /-- Bianchi identity: ∇^μ G_{μν} = 0 (residual vector, should vanish). -/
  bianchiIdentity    : Array Expr
  /-- Einstein tensor G_{μν}. -/
  einsteinTensor     : EinsteinTensor
  /-- Ricci scalar R. -/
  ricciScalar        : Expr
  deriving Repr

namespace EinsteinSolution

-- ---------------------------------------------------------------------------
-- Bianchi identity (contracted): ∇^μ G_{μν} ≈ ∂^μ G_{μν} (partial approx)
-- ---------------------------------------------------------------------------

private def bianchiResidual (g : MetricTensor) (Gcov : Mat) : Array Expr :=
  let n      := g.dim
  let gInv   := g.inverseMatrix
  let coords := g.coords
  -- ∇^μ G_{μν} ≈ g^{μλ} ∂_λ G_{μν} (partial derivative approximation)
  Array.ofFn (n := n) (fun ν : Fin n =>
    sumN n (fun μ => sumN n (fun lam =>
      simplify (.mul (matGet gInv μ lam)
                     (symDiff (matGet Gcov μ ν.val) (coords[lam]!))))))

-- ---------------------------------------------------------------------------
-- Constructor
-- ---------------------------------------------------------------------------

/-- Build an EinsteinSolution from a stress-energy tensor and cosmological constant.
    `Λ` defaults to 0 (no cosmological constant).
    `G_N` defaults to `G_N` (Newton's constant). -/
def ofStressEnergy (st : StressEnergyTensor) (Λ : Expr := .lit 0)
    (G_N : Expr := .var "G_N") : EinsteinSolution :=
  let g    := st.metric
  let et   := EinsteinTensor.ofMetric g
  let R    := RicciTensor.ricciScalar g
  let gCov := g.covariantMatrix
  let n    := g.dim
  -- 8πG T_{μν} (π handled inside EinsteinTensor.fieldEquations)
  let tCov : Mat :=
    match st.idx1, st.idx2 with
    | true, true => st.components
    | _, _ =>
        let gC := gCov; let gI := g.inverseMatrix
        matBuild n (fun i j =>
          sumN n (fun k => sumN n (fun l =>
            simplify (.mul (.mul (matGet gC i k) (matGet gC j l)) (matGet st.components k l)))))
  let eqs := EinsteinTensor.fieldEquations g tCov Λ G_N
  let bianchi := bianchiResidual g et.components
  { stressEnergy := st, cosmologicalConst := Λ,
    fieldEquations := eqs, bianchiIdentity := bianchi,
    einsteinTensor := et, ricciScalar := R }

-- ---------------------------------------------------------------------------
-- Accessors mirroring WL keys
-- ---------------------------------------------------------------------------

/-- The independent field equations (upper triangle, for symmetric metrics). -/
def independentEquations (sol : EinsteinSolution) : List (Nat × Nat × Expr) :=
  let n := sol.stressEnergy.metric.dim
  (List.range n).flatMap (fun i =>
    (List.range (n - i) |>.map (· + i)).map (fun j =>
      (i, j, matGet sol.fieldEquations i j)))

/-- Number of independent equations for an n-dim symmetric metric. -/
def equationCount (sol : EinsteinSolution) : Nat :=
  let n := sol.stressEnergy.metric.dim
  n * (n + 1) / 2

end EinsteinSolution

-- ---------------------------------------------------------------------------
-- Top-level dispatch (mirrors WL's `SolveEinsteinEquations[T, Λ]`)
-- ---------------------------------------------------------------------------

/-- Solve (symbolically) the Einstein equations for a given stress-energy tensor.
    Returns an `EinsteinSolution`. -/
def solveEinsteinEquations (st : StressEnergyTensor) (Λ : Expr := .lit 0)
    : EinsteinSolution :=
  EinsteinSolution.ofStressEnergy st Λ

/-- Solve with an explicit new metric (coordinate change). -/
def solveEinsteinEquationsWithMetric (st : StressEnergyTensor) (g : MetricTensor)
    (Λ : Expr := .lit 0) : EinsteinSolution :=
  let st' : StressEnergyTensor :=
    { st with metric := g,
              components := matRelabel st.components st.metric.coords g.coords }
  EinsteinSolution.ofStressEnergy st' Λ

end Gravitas
