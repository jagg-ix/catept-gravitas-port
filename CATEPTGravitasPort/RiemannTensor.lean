import CATEPTGravitasPort.Basic
import CATEPTGravitasPort.MetricTensor
import CATEPTGravitasPort.ChristoffelSymbols

/-!
# Gravitas.RiemannTensor

Port of `Gravitas/Kernel/RiemannTensor.wl`.

Riemann curvature tensor:

  R^ρ_{σμν} = ∂_μ Γ^ρ_{νσ} - ∂_ν Γ^ρ_{μσ}
             + Γ^ρ_{μλ} Γ^λ_{νσ} - Γ^ρ_{νλ} Γ^λ_{μσ}

Storage convention (matching WL `(False, True, True, True)` default):
  `components i j k l` = R^i_{jkl}

All 16 index combinations are available via `reindex`.
-/

namespace Gravitas

-- ---------------------------------------------------------------------------
-- Structure
-- ---------------------------------------------------------------------------

structure RiemannTensor where
  metric     : MetricTensor
  /-- Flattened n⁴ array; index order: (ρ, σ, μ, ν). -/
  components : Array Expr
  idx1 : IndexKind
  idx2 : IndexKind
  idx3 : IndexKind
  idx4 : IndexKind
  deriving Repr

namespace RiemannTensor

private def size4 (n : Nat) := n * n * n * n

def getComp (n : Nat) (comps : Array Expr) (i j k l : Nat) : Expr :=
  comps[i*n*n*n + j*n*n + k*n + l]? |>.getD (.lit 0)

private def setComp (n : Nat) (comps : Array Expr) (i j k l : Nat) (e : Expr)
    : Array Expr :=
  comps.set! (i*n*n*n + j*n*n + k*n + l) e

-- ---------------------------------------------------------------------------
-- Compute mixed R^ρ_{σμν} from metric
-- ---------------------------------------------------------------------------

/-- Compute the mixed Riemann tensor R^ρ_{σμν} using the Levi-Civita connection
    of `g`.  Returns a flat n⁴ array. -/
def computeMixed (gCov gInv : Mat) (coords : Array String) : Array Expr :=
  let n := gCov.size
  -- Step 1: Christoffel symbols Γ^λ_{μν}
  let Γ := ChristoffelSymbols.computeMixed gCov gInv coords
  let getΓ := fun lam_ μ ν => ChristoffelSymbols.getComp n Γ lam_ μ ν
  -- Step 2: R^ρ_{σμν}
  let comps := List.replicate (size4 n) (.lit 0) |>.toArray
  (List.range n).foldl (fun comps ρ =>
    (List.range n).foldl (fun comps σ =>
      (List.range n).foldl (fun comps μ =>
        (List.range n).foldl (fun comps ν =>
          -- R^ρ_{σμν} = ∂_μ Γ^ρ_{νσ} - ∂_ν Γ^ρ_{μσ}
          --           + Σ_λ (Γ^ρ_{μλ} Γ^λ_{νσ} - Γ^ρ_{νλ} Γ^λ_{μσ})
          let t1 := symDiff (getΓ ρ ν σ) (coords[μ]!)
          let t2 := symDiff (getΓ ρ μ σ) (coords[ν]!)
          let t3 := sumN n (fun lam_ =>
            simplify (.mul (getΓ ρ μ lam_) (getΓ lam_ ν σ)))
          let t4 := sumN n (fun lam_ =>
            simplify (.mul (getΓ ρ ν lam_) (getΓ lam_ μ σ)))
          let val := simplify (.sub (.add (.sub t1 t2) t3) t4)
          setComp n comps ρ σ μ ν val
        ) comps
      ) comps
    ) comps
  ) comps

-- ---------------------------------------------------------------------------
-- Raise/lower indices
-- ---------------------------------------------------------------------------

/-- Convert mixed R^ρ_{σμν} components to any of the 16 index combinations (public).
    Input `mixed`: flat n⁴ array with (con,co,co,co) convention.
    The covariant Riemann tensor R_{ρσμν} is obtained via:
      R_{ρσμν} = g_{ρλ} R^λ_{σμν} -/
def convertIndices (n : Nat) (gCov gInv : Mat) (mixed : Array Expr)
    (i1 i2 i3 i4 : IndexKind) : Array Expr :=
  let get := fun ρ σ μ ν => getComp n mixed ρ σ μ ν
  let base := List.replicate (size4 n) (.lit 0) |>.toArray
  (List.range n).foldl (fun comps i =>
    (List.range n).foldl (fun comps j =>
      (List.range n).foldl (fun comps k =>
        (List.range n).foldl (fun comps l =>
          let val : Expr :=
            -- We implement a general approach: start from the all-covariant form
            -- R_{ρσμν} = g_{ρα} R^α_{σμν}, then raise as needed.
            -- First lower first index: R_{ρσμν}
            let covariant_ρ : Nat → Nat → Nat → Nat → Expr :=
              fun ρ σ μ ν => sumN n (fun α =>
                simplify (.mul (matGet gCov ρ α) (get α σ μ ν)))
            -- Now raise/lower each index from the all-covariant form
            match i1, i2, i3, i4 with
            -- (con, co, co, co) = R^ρ_{σμν}
            | false, true,  true,  true  => get i j k l
            -- (co, co, co, co) = R_{ρσμν}
            | true,  true,  true,  true  => covariant_ρ i j k l
            -- (con, con, con, con) = R^{ρσμν} = g^{σα}g^{μβ}g^{νγ} R^ρ_{αβγ}
            | false, false, false, false =>
                sumN n (fun α => sumN n (fun β => sumN n (fun γ =>
                  simplify (.mul (.mul (matGet gInv j α) (matGet gInv k β))
                                 (.mul (matGet gInv l γ) (get i α β γ))))))
            -- (co, con, con, con)
            | true,  false, false, false =>
                sumN n (fun ρ => sumN n (fun α => sumN n (fun β => sumN n (fun γ =>
                  simplify (.mul (.mul (.mul (matGet gCov i ρ) (matGet gInv j α))
                                     (.mul (matGet gInv k β) (matGet gInv l γ)))
                                 (get ρ α β γ))))))
            -- (con, co, con, con)
            | false, true,  false, false =>
                sumN n (fun α => sumN n (fun β =>
                  simplify (.mul (.mul (matGet gInv k α) (matGet gInv l β)) (get i j α β))))
            -- (con, con, co, co) = R^{ρσ}_{μν} = g^{σα} R^ρ_{αμν}
            | false, false, true,  true  =>
                sumN n (fun α =>
                  simplify (.mul (matGet gInv j α) (get i α k l)))
            -- (co, co, con, con)
            | true,  true,  false, false =>
                sumN n (fun μ => sumN n (fun ν =>
                  simplify (.mul (.mul (matGet gInv k μ) (matGet gInv l ν))
                                 (covariant_ρ i j μ ν))))
            -- (con, co, co, con)
            | false, true,  true,  false =>
                sumN n (fun γ => simplify (.mul (matGet gInv l γ) (get i j k γ)))
            -- (con, co, con, co)
            | false, true,  false, true  =>
                sumN n (fun β => simplify (.mul (matGet gInv k β) (get i j β l)))
            -- (co, con, co, co)
            | true,  false, true,  true  =>
                sumN n (fun α => simplify (.mul (matGet gInv j α) (covariant_ρ i α k l)))
            -- (co, co, co, con)
            | true,  true,  true,  false =>
                sumN n (fun γ => sumN n (fun ρ =>
                  simplify (.mul (.mul (matGet gCov i ρ) (matGet gInv l γ)) (get ρ j k γ))))
            -- (co, co, con, co)
            | true,  true,  false, true  =>
                sumN n (fun β => sumN n (fun ρ =>
                  simplify (.mul (.mul (matGet gCov i ρ) (matGet gInv k β)) (get ρ j β l))))
            -- (co, con, co, con)
            | true,  false, true,  false =>
                sumN n (fun α => sumN n (fun γ =>
                  simplify (.mul (.mul (matGet gInv j α) (matGet gInv l γ)) (covariant_ρ i α k γ))))
            -- (co, con, con, co)
            | true,  false, false, true  =>
                sumN n (fun α => sumN n (fun β =>
                  simplify (.mul (.mul (matGet gInv j α) (matGet gInv k β)) (covariant_ρ i α β l))))
            -- (con, con, con, co) = R^{ρσμ}_ν = g^{σα}g^{μβ} R^ρ_{αβν}
            | false, false, false, true  =>
                sumN n (fun α => sumN n (fun β =>
                  simplify (.mul (.mul (matGet gInv j α) (matGet gInv k β)) (get i α β l))))
            -- (con, con, co, con) = R^{ρσ}_μ^ν = g^{σα}g^{νγ} R^ρ_{αμγ}
            | false, false, true,  false =>
                sumN n (fun α => sumN n (fun γ =>
                  simplify (.mul (.mul (matGet gInv j α) (matGet gInv l γ)) (get i α k γ))))
          setComp n comps i j k l val
        ) comps
      ) comps
    ) comps
  ) base

-- ---------------------------------------------------------------------------
-- Constructor
-- ---------------------------------------------------------------------------

/-- Build a RiemannTensor from a MetricTensor. -/
def ofMetric (g : MetricTensor)
    (idx1 : IndexKind := con) (idx2 : IndexKind := co)
    (idx3 : IndexKind := co)  (idx4 : IndexKind := co) : RiemannTensor :=
  let gCov  := g.covariantMatrix
  let gInv  := g.inverseMatrix
  let mixed := computeMixed gCov gInv g.coords
  let comps := convertIndices g.dim gCov gInv mixed idx1 idx2 idx3 idx4
  { metric := g, components := comps, idx1, idx2, idx3, idx4 }

-- ---------------------------------------------------------------------------
-- Accessor and properties
-- ---------------------------------------------------------------------------

def get (rt : RiemannTensor) (i j k l : Nat) : Expr :=
  getComp rt.metric.dim rt.components i j k l

/-- Kretschner scalar K = R_{abcd} R^{abcd}. -/
def kretschnerScalar (g : MetricTensor) : Expr :=
  let n    := g.dim
  let gCov := g.covariantMatrix
  let gInv := g.inverseMatrix
  let mixed := computeMixed gCov gInv g.coords
  let covComps := convertIndices n gCov gInv mixed co co co co
  let conComps := convertIndices n gCov gInv mixed con con con con
  let getCov := fun a b c d => getComp n covComps a b c d
  let getCon := fun a b c d => getComp n conComps a b c d
  sumN n (fun a => sumN n (fun b => sumN n (fun c => sumN n (fun d =>
    simplify (.mul (getCov a b c d) (getCon a b c d))))))

end RiemannTensor
end Gravitas
