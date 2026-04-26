import CATEPTGravitasPort.Basic
import CATEPTGravitasPort.MetricTensor
import CATEPTGravitasPort.RicciTensor

/-!
# Gravitas.EinsteinTensor

Port of `Gravitas/Kernel/EinsteinTensor.wl`.

Einstein tensor (with optional cosmological constant Λ):

  G_{μν} = R_{μν} - (1/2) R g_{μν}

With cosmological constant:

  G_{μν} + Λ g_{μν} = 8πG T_{μν}

Default storage: `(true, true)` = G_{μν} (fully covariant).
-/

namespace Gravitas

-- ---------------------------------------------------------------------------
-- Structure
-- ---------------------------------------------------------------------------

structure EinsteinTensor where
  metric     : MetricTensor
  components : Mat
  idx1 : IndexKind
  idx2 : IndexKind
  deriving Repr

namespace EinsteinTensor

-- ---------------------------------------------------------------------------
-- Core computation
-- ---------------------------------------------------------------------------

/-- Compute G_{μν} = R_{μν} - (1/2) R g_{μν} (fully covariant). -/
def computeCovariant (g : MetricTensor) : Mat :=
  let rt   := RicciTensor.ofMetric g
  let R    := RicciTensor.ricciScalar g
  let gCov := g.covariantMatrix
  let n    := g.dim
  matBuild n (fun μ ν =>
    simplify (.sub (matGet rt.components μ ν)
                   (.mul (.mul (.lit (1/2)) R) (matGet gCov μ ν))))

private def toIndexed (gCov gInv gcov : Mat) (idx1 idx2 : IndexKind) : Mat :=
  let n := gCov.size
  match idx1, idx2 with
  | true,  true  => gcov
  | false, false =>
      matBuild n (fun i j =>
        sumN n (fun k => sumN n (fun l =>
          simplify (.mul (.mul (matGet gInv i k) (matGet gInv j l)) (matGet gcov k l)))))
  | true,  false =>
      matBuild n (fun i j =>
        sumN n (fun k => simplify (.mul (matGet gInv k j) (matGet gcov i k))))
  | false, true  =>
      matBuild n (fun i j =>
        sumN n (fun k => simplify (.mul (matGet gInv i k) (matGet gcov k j))))

-- ---------------------------------------------------------------------------
-- Constructor
-- ---------------------------------------------------------------------------

/-- Build an EinsteinTensor from a MetricTensor. -/
def ofMetric (g : MetricTensor)
    (idx1 : IndexKind := co) (idx2 : IndexKind := co) : EinsteinTensor :=
  let gCov   := g.covariantMatrix
  let gInv   := g.inverseMatrix
  let gcov   := computeCovariant g
  let comps  := toIndexed gCov gInv gcov idx1 idx2
  { metric := g, components := comps, idx1, idx2 }

-- ---------------------------------------------------------------------------
-- Accessor
-- ---------------------------------------------------------------------------

def get (et : EinsteinTensor) (i j : Nat) : Expr :=
  matGet et.components i j

-- ---------------------------------------------------------------------------
-- Einstein equations: field equations G_{μν} = 8πG T_{μν} - Λ g_{μν}
-- (returned as symbolic matrix of LHS - RHS = 0 entries)
-- ---------------------------------------------------------------------------

/-- Return the Einstein field equations as a matrix of residuals:
    G_{μν} + Λ g_{μν} - 8πG T_{μν} = 0,  where `stressEnergy` is T_{μν} (covariant),
    `cosmoConst` is Λ (symbolic), and `G_N` is Newton's constant. -/
def fieldEquations (g : MetricTensor) (stressEnergy : Mat)
    (cosmoConst : Expr := .lit 0) (G_N : Expr := .var "G_N") : Mat :=
  let et   := ofMetric g
  let gCov := g.covariantMatrix
  let n    := g.dim
  let pi   := .var "π"
  -- 8πG
  let coeff := simplify (.mul (.mul (.lit 8) pi) G_N)
  matBuild n (fun μ ν =>
    simplify (.sub
      (.add (matGet et.components μ ν) (.mul cosmoConst (matGet gCov μ ν)))
      (.mul coeff (matGet stressEnergy μ ν))))

end EinsteinTensor
end Gravitas
