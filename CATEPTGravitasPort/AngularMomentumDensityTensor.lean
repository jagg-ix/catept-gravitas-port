import CATEPTGravitasPort.Basic
import CATEPTGravitasPort.MetricTensor
import CATEPTGravitasPort.StressEnergyTensor

/-!
# Gravitas.AngularMomentumDensityTensor

Port of `Gravitas/Kernel/AngularMomentumDensityTensor.wl`.

Angular momentum density tensor (the integrand without the surface element):

  M^{μν λ} = x^μ T^{νλ} - x^ν T^{μλ}

This is the Belinfante–Rosenfeld angular momentum density, a rank-3 tensor.
Components are stored as a flat n³ array with indices (μ, ν, λ).
-/

namespace Gravitas

structure AngularMomentumDensityTensor where
  stressEnergy   : StressEnergyTensor
  positionVector : Array Expr
  components     : Array Expr   -- n³, index order (μ, ν, λ)
  idx1 : IndexKind
  idx2 : IndexKind
  idx3 : IndexKind
  deriving Repr

namespace AngularMomentumDensityTensor

private def getComp (n : Nat) (comps : Array Expr) (i j k : Nat) : Expr :=
  comps[i*n*n + j*n + k]? |>.getD (.lit 0)

/-- Compute M^{μνλ} = x^μ T^{νλ} - x^ν T^{μλ} (all contravariant). -/
private def computeCon (n : Nat) (tCon : Mat) (x : Array Expr) : Array Expr :=
  (List.range n).foldl (fun comps μ =>
    (List.range n).foldl (fun comps ν =>
      (List.range n).foldl (fun comps lam_ =>
        let val := simplify
          (.sub (.mul (x[μ]!) (matGet tCon ν lam_))
                (.mul (x[ν]!) (matGet tCon μ lam_)))
        comps.set! (μ*n*n + ν*n + lam_) val
      ) comps
    ) comps
  ) (List.replicate (n*n*n) (.lit 0) |>.toArray)

/-- Convert all-contravariant M^{μνλ} to any index combination. -/
private def convertIndices (n : Nat) (gCov gInv : Mat) (con : Array Expr)
    (i1 i2 i3 : IndexKind) : Array Expr :=
  let get := fun i j k => getComp n con i j k
  let base := List.replicate (n*n*n) (.lit 0) |>.toArray
  (List.range n).foldl (fun comps i =>
    (List.range n).foldl (fun comps j =>
      (List.range n).foldl (fun comps k =>
        let val : Expr := match i1, i2, i3 with
          | false, false, false => get i j k
          | true,  true,  true  =>
              sumN n (fun a => sumN n (fun b => sumN n (fun c =>
                simplify (.mul (.mul (matGet gCov i a) (matGet gCov j b))
                               (.mul (matGet gCov k c) (get a b c))))))
          | true,  false, false =>
              sumN n (fun a => simplify (.mul (matGet gCov i a) (get a j k)))
          | false, true,  false =>
              sumN n (fun b => simplify (.mul (matGet gCov j b) (get i b k)))
          | false, false, true  =>
              sumN n (fun c => simplify (.mul (matGet gCov k c) (get i j c)))
          | true,  true,  false =>
              sumN n (fun a => sumN n (fun b =>
                simplify (.mul (.mul (matGet gCov i a) (matGet gCov j b)) (get a b k))))
          | true,  false, true  =>
              sumN n (fun a => sumN n (fun c =>
                simplify (.mul (.mul (matGet gCov i a) (matGet gCov k c)) (get a j c))))
          | false, true,  true  =>
              sumN n (fun b => sumN n (fun c =>
                simplify (.mul (.mul (matGet gCov j b) (matGet gCov k c)) (get i b c))))
        comps.set! (i*n*n + j*n + k) val
      ) comps
    ) comps
  ) base

def ofStressEnergy (st : StressEnergyTensor) (x : Array Expr := #[])
    (idx1 : IndexKind := con) (idx2 : IndexKind := con) (idx3 : IndexKind := con)
    : AngularMomentumDensityTensor :=
  let g    := st.metric
  let n    := g.dim
  let gCov := g.covariantMatrix
  let gInv := g.inverseMatrix
  let tCon := matBuild n (fun μ ν =>
    sumN n (fun k => sumN n (fun l =>
      simplify (.mul (.mul (matGet gInv μ k) (matGet gInv ν l)) (matGet st.components k l)))))
  let x' := if x.isEmpty then Array.ofFn (n := n) (fun i : Fin n => .var s!"X{i.val}") else x
  let conComps := computeCon n tCon x'
  let comps := convertIndices n gCov gInv conComps idx1 idx2 idx3
  { stressEnergy := st, positionVector := x', components := comps, idx1, idx2, idx3 }

def get (mt : AngularMomentumDensityTensor) (i j k : Nat) : Expr :=
  getComp mt.stressEnergy.metric.dim mt.components i j k

end AngularMomentumDensityTensor
end Gravitas
