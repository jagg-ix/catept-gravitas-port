import CATEPTGravitasPort.Basic
import CATEPTGravitasPort.MetricTensor
import CATEPTGravitasPort.RicciTensor

/-!
# Gravitas.SchoutenTensor

Port of `Gravitas/Kernel/SchoutenTensor.wl`.

Schouten tensor (trace-adjusted Ricci):

  S_{μν} = 1/(n-2) [R_{μν} - R/(2(n-1)) g_{μν}]

Default storage: `(co, co)` = S_{μν} (fully covariant).
-/

namespace Gravitas

structure SchoutenTensor where
  metric     : MetricTensor
  components : Mat
  idx1 : IndexKind
  idx2 : IndexKind
  deriving Repr

namespace SchoutenTensor

private def computeCovariant (g : MetricTensor) : Mat :=
  let n    := g.dim
  let gCov := g.covariantMatrix
  let rt   := RicciTensor.ofMetric g
  let R    := RicciTensor.ricciScalar g
  let nE : Expr := .lit (n : Rat)
  -- 1/(n-2) * (R_{μν} - R/(2(n-1)) g_{μν})
  matBuild n (fun μ ν =>
    simplify
      (.mul (.div (.lit 1) (.sub nE (.lit 2)))
            (.sub (matGet rt.components μ ν)
                  (.mul (.div R (.mul (.lit 2) (.sub nE (.lit 1))))
                        (matGet gCov μ ν)))))

private def toIndexed (gCov gInv scov : Mat) (idx1 idx2 : IndexKind) : Mat :=
  let n := gCov.size
  match idx1, idx2 with
  | true,  true  => scov
  | false, false =>
      matBuild n (fun i j =>
        sumN n (fun k => sumN n (fun l =>
          simplify (.mul (.mul (matGet gInv i k) (matGet gInv j l)) (matGet scov k l)))))
  | true,  false =>
      matBuild n (fun i j =>
        sumN n (fun k => simplify (.mul (matGet gInv k j) (matGet scov i k))))
  | false, true  =>
      matBuild n (fun i j =>
        sumN n (fun k => simplify (.mul (matGet gInv i k) (matGet scov k j))))

def ofMetric (g : MetricTensor)
    (idx1 : IndexKind := co) (idx2 : IndexKind := co) : SchoutenTensor :=
  let gCov  := g.covariantMatrix
  let gInv  := g.inverseMatrix
  let scov  := computeCovariant g
  let comps := toIndexed gCov gInv scov idx1 idx2
  { metric := g, components := comps, idx1, idx2 }

def get (st : SchoutenTensor) (i j : Nat) : Expr :=
  matGet st.components i j

end SchoutenTensor
end Gravitas
