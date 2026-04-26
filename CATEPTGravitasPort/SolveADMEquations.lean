import CATEPTGravitasPort.Basic
import CATEPTGravitasPort.MetricTensor
import CATEPTGravitasPort.RicciTensor
import CATEPTGravitasPort.ChristoffelSymbols
import CATEPTGravitasPort.ExtrinsicCurvatureTensor
import CATEPTGravitasPort.ADMDecomposition
import CATEPTGravitasPort.ADMStressEnergyDecomposition

/-!
# Gravitas.SolveADMEquations

Port of `Gravitas/Kernel/SolveADMEquations.wl`.

ADM evolution and constraint equations:

Hamiltonian constraint:
  H = R_spatial + K² - K_{ij} K^{ij} - 16πG ρ_ADM = 0

Momentum constraints:
  M_i = ∇^j K_{ij} - ∇_i K - 8πG j_i = 0

Evolution equations (lapse/shift gauge + extrinsic curvature):
  ∂_t γ_{ij} = -2α K_{ij} + ∇_i β_j + ∇_j β_i
  ∂_t K_{ij} = α (R_{ij} - 2K_{ik}K^k_j + K K_{ij}) - ∇_i ∇_j α
              + β^k ∂_k K_{ij} + K_{ik} ∂_j β^k + K_{jk} ∂_i β^k
              - 8πG α (S_{ij} - (1/2) γ_{ij} (S - ρ_ADM))
-/

namespace Gravitas

-- ---------------------------------------------------------------------------
-- ADM solution structure
-- ---------------------------------------------------------------------------

structure ADMSolution where
  adm                   : ADMDecomposition
  admDecomp             : ADMStressEnergyDecomposition
  /-- Hamiltonian constraint H = 0 (scalar residual). -/
  hamiltonianConstraint  : Expr
  /-- Momentum constraints M_i = 0 (spatial vector residual). -/
  momentumConstraints    : Array Expr
  /-- Evolution eq for γ_{ij}: ∂_t γ_{ij} = … (residual matrix). -/
  metricEvolution        : Mat
  /-- Evolution eq for K_{ij}: ∂_t K_{ij} = … (residual matrix). -/
  extrinEvolution        : Mat
  deriving Repr

namespace ADMSolution

/-- Compute the spatial Ricci scalar from the 3-metric. -/
private def spatialRicciScalar (adm : ADMDecomposition) : Expr :=
  RicciTensor.ricciScalar adm.spatialMetric

/-- Hamiltonian constraint:
    H = ³R + K² - K_{ij} K^{ij} - 16πG ρ_ADM -/
private def computeHamiltonianConstraint
    (adm : ADMDecomposition) (decomp : ADMStressEnergyDecomposition)
    (G_N : Expr) : Expr :=
  let kt   := ExtrinsicCurvatureTensor.ofADM adm
  let K    := ExtrinsicCurvatureTensor.meanCurvature kt
  let γInv := adm.spatialMetric.inverseMatrix
  let n3   := adm.spatialMetric.dim
  -- K_{ij} K^{ij} = γ^{ik} γ^{jl} K_{ij} K_{kl}
  let kSq := sumN n3 (fun i => sumN n3 (fun j =>
    sumN n3 (fun k => sumN n3 (fun l =>
      simplify (.mul (.mul (.mul (matGet γInv i k) (matGet γInv j l))
                          (matGet kt.components i j)) (matGet kt.components k l))))))
  let R3   := spatialRicciScalar adm
  let ρ    := decomp.energyDensity
  let π    := .var "π"
  simplify (.sub (.sub (.add R3 (.mul K K)) kSq)
                 (.mul (.mul (.mul (.lit 16) π) G_N) ρ))

/-- Momentum constraint M_i = ∇^j K_{ij} - ∇_i K - 8πG j_i.
    Uses the Christoffel-corrected covariant divergence (AFP semantic-mapping technique):
      ∇^j K_{ij} = γ^{jk} ∂_k K_{ij} - γ^{jk} Γ^l_{ki} K_{lj} - γ^{jk} Γ^l_{kj} K_{il}
    which replaces the previous partial-derivative approximation. -/
private def computeMomentumConstraints
    (adm : ADMDecomposition) (decomp : ADMStressEnergyDecomposition)
    (G_N : Expr) : Array Expr :=
  let kt     := ExtrinsicCurvatureTensor.ofADM adm
  let K      := ExtrinsicCurvatureTensor.meanCurvature kt
  let γ      := adm.spatialMetric
  let γCov   := γ.covariantMatrix
  let γInv   := γ.inverseMatrix
  let coords := γ.coords
  let n3     := γ.dim
  let j      := decomp.momentumDensity
  let π      := .var "π"
  -- Spatial Christoffel Γ^l_{km} for the covariant divergence correction
  let Γ3 := ChristoffelSymbols.computeMixed γCov γInv coords
  let getΓ := fun lam μ ν => ChristoffelSymbols.getComp n3 Γ3 lam μ ν
  Array.ofFn (n := n3) (fun i : Fin n3 =>
    -- ∇^j K_{ij} = γ^{jk}(∂_k K_{ij} - Γ^l_{ki} K_{lj} - Γ^l_{kj} K_{il})
    let divK := sumN n3 (fun j_ => sumN n3 (fun k =>
      let partialTerm := symDiff (matGet kt.components i j_) (coords[k]!)
      let conn1 := sumN n3 (fun l_ =>
        simplify (.mul (getΓ l_ k i.val) (matGet kt.components l_ j_)))
      let conn2 := sumN n3 (fun l_ =>
        simplify (.mul (getΓ l_ k j_) (matGet kt.components i l_)))
      simplify (.mul (matGet γInv j_ k)
                     (.sub (.sub partialTerm conn1) conn2))))
    -- ∇_i K = ∂_i K  (K is a scalar, covariant gradient = partial gradient)
    let gradK := symDiff K (coords[i.val]!)
    simplify (.sub (.sub divK gradK)
                   (.mul (.mul (.mul (.lit 8) π) G_N) (j[i.val]!))))

/-- ∂_t γ_{ij} = -2α K_{ij} + ∇_i β_j + ∇_j β_i -/
private def computeMetricEvolution (adm : ADMDecomposition) : Mat :=
  let γ      := adm.spatialMetric
  let gCov   := γ.covariantMatrix
  let gInv   := γ.inverseMatrix
  let coords := γ.coords
  let n3     := γ.dim
  let α      := adm.lapseFunction
  let β      := adm.shiftVector
  let kt     := ExtrinsicCurvatureTensor.ofADM adm
  -- β_i = γ_{ij} β^j
  let βCov := Array.ofFn (n := n3) (fun i : Fin n3 =>
    sumN n3 (fun j => simplify (.mul (matGet gCov i.val j) (β[j]!))))
  -- Spatial Christoffel symbols
  let Γ3 := ChristoffelSymbols.computeMixed gCov gInv coords
  let getΓ := fun lam μ ν => ChristoffelSymbols.getComp n3 Γ3 lam μ ν
  -- ∇_i β_j = ∂_i β_j - Γ^k_{ij} β_k
  let nablaβ := matBuild n3 (fun i j =>
    simplify (.sub (symDiff (βCov[j]!) (coords[i]!))
                   (sumN n3 (fun k => simplify (.mul (getΓ k i j) (βCov[k]!))))))
  -- ∂_t γ_{ij} - (-2α K_{ij} + ∇_i β_j + ∇_j β_i) = 0
  matBuild n3 (fun i j =>
    simplify (.sub (symDiff (matGet gCov i j) adm.timeCoordinate)
                   (.add (.mul (.mul (.lit (-2)) α) (matGet kt.components i j))
                         (.add (matGet nablaβ i j) (matGet nablaβ j i)))))

/-- Build the ADM solution for a given ADM decomposition and matter. -/
def ofADM (adm : ADMDecomposition) (decomp : ADMStressEnergyDecomposition)
    (G_N : Expr := .var "G_N") : ADMSolution :=
  let kt       := ExtrinsicCurvatureTensor.ofADM adm
  let γ        := adm.spatialMetric
  let n3       := γ.dim
  let gCov     := γ.covariantMatrix
  let gInv     := γ.inverseMatrix
  let coords   := γ.coords
  let α        := adm.lapseFunction
  let R3       := RicciTensor.ofMetric γ
  -- ∂_t K_{ij} evolution (full: Lie derivative shift terms + Christoffel-corrected Hessian)
  let K        := ExtrinsicCurvatureTensor.meanCurvature kt
  let S        := decomp.stressTensor   -- S^{ij}
  let ρ        := decomp.energyDensity
  let STr := sumN n3 (fun i => sumN n3 (fun j =>
    simplify (.mul (matGet gCov i j) (matGet S i j))))  -- S = S^i_i = γ_{ij} S^{ij}
  let π  := .var "π"
  let β  := adm.shiftVector
  -- Spatial Christoffel symbols for ∇_i∇_j α and Lie derivative terms
  let Γ3   := ChristoffelSymbols.computeMixed gCov gInv coords
  let getΓ := fun lam μ ν => ChristoffelSymbols.getComp n3 Γ3 lam μ ν
  let extrinEvo := matBuild n3 (fun i j =>
    -- α R_{ij} + α K K_{ij} - 2α K_{ik}K^k_j
    -- - ∇_i∇_j α  (Christoffel-corrected lapse Hessian)
    -- + β^k ∂_k K_{ij} + K_{ik} ∂_j β^k + K_{jk} ∂_i β^k  (Lie derivative shift terms)
    -- - 8πGα(S_{ij} - (1/2)γ_{ij}(S - ρ))
    let rTerm  := simplify (.mul α (matGet R3.components i j))
    let kTerm  := simplify (.mul (.mul α K) (matGet kt.components i j))
    let k2Term := sumN n3 (fun k =>
      simplify (.mul (.mul (.lit 2) α)
                     (.mul (matGet kt.components i k)
                           (sumN n3 (fun l => simplify (.mul (matGet gInv k l) (matGet kt.components l j)))))))
    -- ∇_i∇_j α = ∂_i∂_j α - Γ^k_{ij} ∂_k α
    let lapseHess :=
      let hess := symDiff (symDiff α (coords[i]!)) (coords[j]!)
      let conn := sumN n3 (fun k =>
        simplify (.mul (getΓ k i j) (symDiff α (coords[k]!))))
      simplify (.sub hess conn)
    -- Lie derivative: β^k ∂_k K_{ij} + K_{ik} ∂_j β^k + K_{jk} ∂_i β^k
    let lieShift :=
      let advect := sumN n3 (fun k =>
        simplify (.mul (β[k]!) (symDiff (matGet kt.components i j) (coords[k]!))))
      let shear1 := sumN n3 (fun k =>
        simplify (.mul (matGet kt.components i k) (symDiff (β[k]!) (coords[j]!))))
      let shear2 := sumN n3 (fun k =>
        simplify (.mul (matGet kt.components j k) (symDiff (β[k]!) (coords[i]!))))
      simplify (.add (.add advect shear1) shear2)
    let matterTerm := simplify
      (.mul (.mul (.mul (.lit 8) π) (.mul G_N α))
            (.sub (matGet S i j)
                  (.mul (.mul (.lit (1/2)) (matGet gCov i j)) (.sub STr ρ))))
    simplify (.sub (symDiff (matGet kt.components i j) adm.timeCoordinate)
                   (.sub (.add (.add (.sub rTerm k2Term) kTerm) lieShift)
                         (.add lapseHess matterTerm))))
  let H  := computeHamiltonianConstraint adm decomp G_N
  let Mi := computeMomentumConstraints adm decomp G_N
  let γEvo := computeMetricEvolution adm
  { adm := adm, admDecomp := decomp,
    hamiltonianConstraint := H, momentumConstraints := Mi,
    metricEvolution := γEvo, extrinEvolution := extrinEvo }

end ADMSolution

-- ---------------------------------------------------------------------------
-- Top-level API
-- ---------------------------------------------------------------------------

def solveADMEquations (adm : ADMDecomposition) (decomp : ADMStressEnergyDecomposition)
    (G_N : Expr := .var "G_N") : ADMSolution :=
  ADMSolution.ofADM adm decomp G_N

end Gravitas
