import CATEPTGravitasPort.Basic
import CATEPTGravitasPort.MetricTensor
import CATEPTGravitasPort.RiemannTensor

/-!
# Gravitas.RicciTensor

Port of `Gravitas/Kernel/RicciTensor.wl`.

Ricci tensor (contraction of Riemann):

  R_{μν} = R^λ_{μλν}   (contraction on first and third indices of R^ρ_{σμν})

Ricci scalar:

  R = g^{μν} R_{μν}

Default storage convention: `(true, true)` = R_{μν} (fully covariant).
-/

namespace Gravitas

-- ---------------------------------------------------------------------------
-- Structure
-- ---------------------------------------------------------------------------

structure RicciTensor where
  metric     : MetricTensor
  /-- n×n matrix of Ricci components in whatever index position is stored. -/
  components : Mat
  idx1 : IndexKind
  idx2 : IndexKind
  deriving Repr

namespace RicciTensor

-- ---------------------------------------------------------------------------
-- Compute covariant R_{μν}
-- ---------------------------------------------------------------------------

/-- Compute the fully covariant Ricci tensor R_{μν} = R^λ_{μλν}
    from the mixed Riemann tensor array. -/
def computeCovariant (n : Nat) (riemannMixed : Array Expr) : Mat :=
  -- R_{μν} = Σ_λ R^λ_{μλν}
  let getR := fun lam μ ν => RiemannTensor.getComp n riemannMixed lam μ lam ν
  matBuild n (fun μ ν =>
    sumN n (fun lam => simplify (getR lam μ ν)))

-- ---------------------------------------------------------------------------
-- Raise/lower from covariant R_{μν}
-- ---------------------------------------------------------------------------

private def raiseMatrix (gInv cov : Mat) : Mat :=
  let n := gInv.size
  matBuild n (fun i j =>
    sumN n (fun k => sumN n (fun l =>
      simplify (.mul (.mul (matGet gInv i k) (matGet gInv j l)) (matGet cov k l)))))

private def lowerFirst (gCov cov : Mat) : Mat :=
  -- Actually for Ricci this gives g_{iμ} R^μ_j
  let n := gCov.size
  matBuild n (fun i j =>
    sumN n (fun k => simplify (.mul (matGet gCov i k) (matGet cov k j))))

private def toIndexed (gCov gInv ricciCov : Mat) (idx1 idx2 : IndexKind) : Mat :=
  let n := gCov.size
  match idx1, idx2 with
  | true,  true  => ricciCov
  | false, false => raiseMatrix gInv ricciCov
  | true,  false =>
      matBuild n (fun i j =>
        sumN n (fun k => simplify (.mul (matGet gInv k j) (matGet ricciCov i k))))
  | false, true  =>
      matBuild n (fun i j =>
        sumN n (fun k => simplify (.mul (matGet gInv i k) (matGet ricciCov k j))))

-- ---------------------------------------------------------------------------
-- Constructor
-- ---------------------------------------------------------------------------

/-- Build a RicciTensor from a MetricTensor. -/
def ofMetric (g : MetricTensor)
    (idx1 : IndexKind := co) (idx2 : IndexKind := co) : RicciTensor :=
  let gCov     := g.covariantMatrix
  let gInv     := g.inverseMatrix
  let rMixed   := RiemannTensor.computeMixed gCov gInv g.coords
  let ricciCov := computeCovariant g.dim rMixed
  let comps    := toIndexed gCov gInv ricciCov idx1 idx2
  { metric := g, components := comps, idx1, idx2 }

-- ---------------------------------------------------------------------------
-- Accessor
-- ---------------------------------------------------------------------------

def get (rt : RicciTensor) (i j : Nat) : Expr :=
  matGet rt.components i j

-- ---------------------------------------------------------------------------
-- Ricci scalar  R = g^{μν} R_{μν}
-- ---------------------------------------------------------------------------

/-- Compute the Ricci scalar R = g^{μν} R_{μν}. -/
def ricciScalar (g : MetricTensor) : Expr :=
  let rt := ofMetric g
  let gInv := g.inverseMatrix
  let n := g.dim
  sumN n (fun μ => sumN n (fun ν =>
    simplify (.mul (matGet gInv μ ν) (matGet rt.components μ ν))))

-- ---------------------------------------------------------------------------
-- Properties mirroring WL keys
-- ---------------------------------------------------------------------------

/-- Re-index to new index positions. -/
def reindex (rt : RicciTensor) (idx1 idx2 : IndexKind) : RicciTensor :=
  let gCov := rt.metric.covariantMatrix
  let gInv := rt.metric.inverseMatrix
  -- Recover covariant form first
  let ricciCov : Mat :=
    match rt.idx1, rt.idx2 with
    | true,  true  => rt.components
    | false, false => raiseMatrix gCov rt.components  -- "lower" contravariant = multiply by gCov
    | true,  false =>
        let n := gCov.size
        matBuild n (fun i j =>
          sumN n (fun k => simplify (.mul (matGet gCov k j) (matGet rt.components i k))))
    | false, true  =>
        let n := gCov.size
        matBuild n (fun i j =>
          sumN n (fun k => simplify (.mul (matGet gCov i k) (matGet rt.components k j))))
  let comps := toIndexed gCov gInv ricciCov idx1 idx2
  { rt with components := comps, idx1, idx2 }

end RicciTensor
end Gravitas
