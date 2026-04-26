import CATEPTGravitasPort.Basic
import CATEPTGravitasPort.MetricTensor
import CATEPTGravitasPort.RiemannTensor
import CATEPTGravitasPort.RicciTensor

/-!
# Gravitas.WeylTensor

Port of `Gravitas/Kernel/WeylTensor.wl`.

Weyl (conformal curvature) tensor:

  C_{ρσμν} = R_{ρσμν}
            + 1/(n-2) (R_{ρν} g_{σμ} - R_{ρμ} g_{σν} + R_{σμ} g_{ρν} - R_{σν} g_{ρμ})
            + R/((n-1)(n-2)) (g_{ρμ} g_{σν} - g_{ρν} g_{σμ})

Default storage: all covariant `(co,co,co,co)`.
-/

namespace Gravitas

structure WeylTensor where
  metric     : MetricTensor
  components : Array Expr   -- n⁴, all-covariant by default
  idx1 : IndexKind
  idx2 : IndexKind
  idx3 : IndexKind
  idx4 : IndexKind
  deriving Repr

namespace WeylTensor

private def size4 (n : Nat) := n * n * n * n

def getComp (n : Nat) (comps : Array Expr) (i j k l : Nat) : Expr :=
  (comps[i*n*n*n + j*n*n + k*n + l]?).getD (.lit 0)

private def setComp (n : Nat) (comps : Array Expr) (i j k l : Nat) (e : Expr)
    : Array Expr :=
  comps.set! (i*n*n*n + j*n*n + k*n + l) e

/-- Compute the all-covariant Weyl tensor C_{ρσμν}. -/
def computeCovariant (g : MetricTensor) : Array Expr :=
  let n        := g.dim
  let gCov     := g.covariantMatrix
  let gInv     := g.inverseMatrix
  let rMixed   := RiemannTensor.computeMixed gCov gInv g.coords
  -- Covariant Riemann  R_{ρσμν}
  let covRiemann := RiemannTensor.convertIndices n gCov gInv rMixed co co co co
  -- Covariant Ricci    R_{μν}
  let ricciCov := RicciTensor.computeCovariant n rMixed
  -- Ricci scalar  R
  let R := RicciTensor.ricciScalar g
  -- n as Expr for arithmetic
  let nE : Expr := .lit (n : Rat)
  let comps := Array.replicate (size4 n) (.lit 0)
  (List.range n).foldl (fun comps ρ =>
    (List.range n).foldl (fun comps σ =>
      (List.range n).foldl (fun comps μ =>
        (List.range n).foldl (fun comps ν =>
          let rρσμν := getComp n covRiemann ρ σ μ ν
          let Rρν   := matGet ricciCov ρ ν
          let Rρμ   := matGet ricciCov ρ μ
          let Rσμ   := matGet ricciCov σ μ
          let Rσν   := matGet ricciCov σ ν
          let gσμ   := matGet gCov σ μ
          let gσν   := matGet gCov σ ν
          let gρμ   := matGet gCov ρ μ
          let gρν   := matGet gCov ρ ν
          let gρμgσν := simplify (.mul gρμ gσν)
          let gρνgσμ := simplify (.mul gρν gσμ)
          -- 1/(n-2) term
          let c1 := simplify (.div (.lit 1) (.sub nE (.lit 2)))
          let mixed := simplify (.mul c1
            (.add (.sub (.mul Rρν gσμ) (.mul Rρμ gσν))
                  (.sub (.mul Rσμ gρν) (.mul Rσν gρμ))))
          -- R/((n-1)(n-2)) term
          let c2 := simplify (.div R (.mul (.sub nE (.lit 1)) (.sub nE (.lit 2))))
          let scalar := simplify (.mul c2 (.sub gρμgσν gρνgσμ))
          let val := simplify (.add (.add rρσμν mixed) scalar)
          setComp n comps ρ σ μ ν val
        ) comps
      ) comps
    ) comps
  ) comps

/-- Convert all-covariant Weyl to any index combination. -/
def convertIndices (n : Nat) (gCov gInv : Mat) (cov : Array Expr)
    (i1 i2 i3 i4 : IndexKind) : Array Expr :=
  let get := fun i j k l => getComp n cov i j k l
  let base := Array.replicate (size4 n) (.lit 0)
  (List.range n).foldl (fun comps i =>
    (List.range n).foldl (fun comps j =>
      (List.range n).foldl (fun comps k =>
        (List.range n).foldl (fun comps l =>
          let val : Expr :=
            -- Raise individual indices from all-covariant form
            let raise1 := fun (f : Nat → Nat → Nat → Nat → Expr) i j k l =>
              sumN n (fun α => simplify (.mul (matGet gInv i α) (f α j k l)))
            let raise2 := fun (f : Nat → Nat → Nat → Nat → Expr) i j k l =>
              sumN n (fun α => simplify (.mul (matGet gInv j α) (f i α k l)))
            let raise3 := fun (f : Nat → Nat → Nat → Nat → Expr) i j k l =>
              sumN n (fun α => simplify (.mul (matGet gInv k α) (f i j α l)))
            let raise4 := fun (f : Nat → Nat → Nat → Nat → Expr) i j k l =>
              sumN n (fun α => simplify (.mul (matGet gInv l α) (f i j k α)))
            -- AFP technique: exhaustive pattern coverage — all 16 index combos
            -- (false=raised/contra, true=lowered/co); starting from all-covariant get
            match i1, i2, i3, i4 with
            -- 0 indices raised
            | true,  true,  true,  true  => get i j k l
            -- 1 index raised
            | false, true,  true,  true  => raise1 get i j k l
            | true,  false, true,  true  => raise2 get i j k l
            | true,  true,  false, true  => raise3 get i j k l
            | true,  true,  true,  false => raise4 get i j k l
            -- 2 indices raised
            | false, false, true,  true  =>
                sumN n (fun α => sumN n (fun β =>
                  simplify (.mul (.mul (matGet gInv i α) (matGet gInv j β)) (get α β k l))))
            | false, true,  false, true  =>
                sumN n (fun α => sumN n (fun γ =>
                  simplify (.mul (.mul (matGet gInv i α) (matGet gInv k γ)) (get α j γ l))))
            | false, true,  true,  false =>
                sumN n (fun α => sumN n (fun δ =>
                  simplify (.mul (.mul (matGet gInv i α) (matGet gInv l δ)) (get α j k δ))))
            | true,  false, false, true  =>
                sumN n (fun β => sumN n (fun γ =>
                  simplify (.mul (.mul (matGet gInv j β) (matGet gInv k γ)) (get i β γ l))))
            | true,  false, true,  false =>
                sumN n (fun β => sumN n (fun δ =>
                  simplify (.mul (.mul (matGet gInv j β) (matGet gInv l δ)) (get i β k δ))))
            | true,  true,  false, false =>
                sumN n (fun γ => sumN n (fun δ =>
                  simplify (.mul (.mul (matGet gInv k γ) (matGet gInv l δ)) (get i j γ δ))))
            -- 3 indices raised
            | false, false, false, true  =>
                sumN n (fun α => sumN n (fun β => sumN n (fun γ =>
                  simplify (.mul (.mul (.mul (matGet gInv i α) (matGet gInv j β))
                                      (matGet gInv k γ)) (get α β γ l)))))
            | false, false, true,  false =>
                sumN n (fun α => sumN n (fun β => sumN n (fun δ =>
                  simplify (.mul (.mul (.mul (matGet gInv i α) (matGet gInv j β))
                                      (matGet gInv l δ)) (get α β k δ)))))
            | false, true,  false, false =>
                sumN n (fun α => sumN n (fun γ => sumN n (fun δ =>
                  simplify (.mul (.mul (.mul (matGet gInv i α) (matGet gInv k γ))
                                      (matGet gInv l δ)) (get α j γ δ)))))
            | true,  false, false, false =>
                sumN n (fun β => sumN n (fun γ => sumN n (fun δ =>
                  simplify (.mul (.mul (.mul (matGet gInv j β) (matGet gInv k γ))
                                      (matGet gInv l δ)) (get i β γ δ)))))
            -- 4 indices raised
            | false, false, false, false =>
                sumN n (fun a => sumN n (fun b => sumN n (fun c => sumN n (fun d =>
                  simplify (.mul (.mul (.mul (.mul (matGet gInv i a) (matGet gInv j b))
                                            (matGet gInv k c)) (matGet gInv l d))
                                      (get a b c d))))))
          setComp n comps i j k l val
        ) comps
      ) comps
    ) comps
  ) base

/-- Build a WeylTensor from a MetricTensor. -/
def ofMetric (g : MetricTensor)
    (idx1 : IndexKind := co) (idx2 : IndexKind := co)
    (idx3 : IndexKind := co) (idx4 : IndexKind := co) : WeylTensor :=
  let cov   := computeCovariant g
  let comps := convertIndices g.dim g.covariantMatrix g.inverseMatrix cov idx1 idx2 idx3 idx4
  { metric := g, components := comps, idx1, idx2, idx3, idx4 }

def get (wt : WeylTensor) (i j k l : Nat) : Expr :=
  getComp wt.metric.dim wt.components i j k l

end WeylTensor
end Gravitas
