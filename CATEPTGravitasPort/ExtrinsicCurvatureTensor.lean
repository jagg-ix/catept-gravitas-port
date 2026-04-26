import CATEPTGravitasPort.Basic
import CATEPTGravitasPort.MetricTensor
import CATEPTGravitasPort.ChristoffelSymbols
import CATEPTGravitasPort.ADMDecomposition

/-!
# Gravitas.ExtrinsicCurvatureTensor

Port of `Gravitas/Kernel/ExtrinsicCurvatureTensor.wl`.

Extrinsic curvature of the spatial hypersurface Σ in the ADM formalism:

  K_{ij} = (1/(2α)) (∂_t γ_{ij} - ∇_i β_j - ∇_j β_i)

where:
- α is the lapse function
- β^i is the shift vector
- γ_{ij} is the spatial metric
- ∇_i is the spatial covariant derivative

Default storage: `(co, co)` = K_{ij}.
-/

namespace Gravitas

structure ExtrinsicCurvatureTensor where
  adm        : ADMDecomposition
  components : Mat
  idx1 : IndexKind
  idx2 : IndexKind
  deriving Repr

namespace ExtrinsicCurvatureTensor

/-- Compute K_{ij} = (1/2α)(∂_t γ_{ij} - ∇_i β_j - ∇_j β_i). -/
private def computeCovariant (adm : ADMDecomposition) : Mat :=
  let γ      := adm.spatialMetric
  let gCov   := γ.covariantMatrix
  let gInv   := γ.inverseMatrix
  let coords := γ.coords
  let n3     := γ.dim
  let t      := adm.timeCoordinate
  let α      := adm.lapseFunction
  let β      := adm.shiftVector
  -- Spatial Christoffel Γ^k_{ij} of the spatial metric
  let Γ3 := ChristoffelSymbols.computeMixed gCov gInv coords
  let getΓ := fun lam_ μ ν => ChristoffelSymbols.getComp n3 Γ3 lam_ μ ν
  -- β_i = γ_{ij} β^j (covariant shift)
  let βCov := Array.ofFn (n := n3) (fun i : Fin n3 =>
    sumN n3 (fun j => simplify (.mul (matGet gCov i.val j) (β[j]!))))
  -- ∇_i β_j = ∂_i β_j - Γ^k_{ij} β_k
  let nablaβ := matBuild n3 (fun i j =>
    let d_i_βj := symDiff (βCov[j]!) (coords[i]!)
    let christoffel_term := sumN n3 (fun k =>
      simplify (.mul (getΓ k i j) (βCov[k]!)))
    simplify (.sub d_i_βj christoffel_term))
  -- ∂_t γ_{ij}
  let dtγ := matBuild n3 (fun i j =>
    symDiff (matGet gCov i j) t)
  -- K_{ij} = (1/2α)(∂_t γ_{ij} - ∇_i β_j - ∇_j β_i)
  matBuild n3 (fun i j =>
    simplify (.mul (.div (.lit 1) (.mul (.lit 2) α))
                   (.sub (matGet dtγ i j)
                         (.add (matGet nablaβ i j) (matGet nablaβ j i)))))

private def toIndexed (gCov gInv kcov : Mat) (idx1 idx2 : IndexKind) : Mat :=
  let n := gCov.size
  match idx1, idx2 with
  | true,  true  => kcov
  | false, false =>
      matBuild n (fun i j =>
        sumN n (fun k => sumN n (fun l =>
          simplify (.mul (.mul (matGet gInv i k) (matGet gInv j l)) (matGet kcov k l)))))
  | true,  false =>
      matBuild n (fun i j =>
        sumN n (fun k => simplify (.mul (matGet gInv k j) (matGet kcov i k))))
  | false, true  =>
      matBuild n (fun i j =>
        sumN n (fun k => simplify (.mul (matGet gInv i k) (matGet kcov k j))))

def ofADM (adm : ADMDecomposition)
    (idx1 : IndexKind := co) (idx2 : IndexKind := co) : ExtrinsicCurvatureTensor :=
  let gCov  := adm.spatialMetric.covariantMatrix
  let gInv  := adm.spatialMetric.inverseMatrix
  let kcov  := computeCovariant adm
  let comps := toIndexed gCov gInv kcov idx1 idx2
  { adm := adm, components := comps, idx1, idx2 }

def get (kt : ExtrinsicCurvatureTensor) (i j : Nat) : Expr :=
  matGet kt.components i j

/-- Mean curvature (trace): K = γ^{ij} K_{ij}. -/
def meanCurvature (kt : ExtrinsicCurvatureTensor) : Expr :=
  let γInv := kt.adm.spatialMetric.inverseMatrix
  let n3   := kt.adm.spatialMetric.dim
  -- recover covariant form
  let kcov := toIndexed kt.adm.spatialMetric.covariantMatrix γInv kt.components kt.idx1 kt.idx2
  sumN n3 (fun i => sumN n3 (fun j =>
    simplify (.mul (matGet γInv i j) (matGet kcov i j))))

end ExtrinsicCurvatureTensor
end Gravitas
