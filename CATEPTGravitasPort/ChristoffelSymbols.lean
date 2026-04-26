import CATEPTGravitasPort.Basic
import CATEPTGravitasPort.MetricTensor

/-!
# Gravitas.ChristoffelSymbols

Port of `Gravitas/Kernel/ChristoffelSymbols.wl`.

Christoffel symbols of the second kind (Levi-Civita connection):

  Γ^λ_{μν} = (1/2) g^{λσ} (∂_μ g_{σν} + ∂_ν g_{σμ} - ∂_σ g_{μν})

The WL source convention:
- `(False, True, True)` indices = Γ^λ_{μν}  (standard mixed: upper λ, lower μν)
- `(True, True, True)`  indices = Γ_{λμν}   (fully covariant)
- `(False,False,False)` indices = Γ^{λμν}   (fully contravariant)
- etc.

All eight index combinations are computed by raising/lowering from the mixed form.
-/

namespace Gravitas

-- ---------------------------------------------------------------------------
-- Core structure
-- ---------------------------------------------------------------------------

/-- Christoffel symbols Γ associated with a metric, with explicit index positions.
    Components are stored as a 3-index array: `components i j k` = Γ_{ijk}
    in whatever variance is indicated by `idx1 idx2 idx3`. -/
structure ChristoffelSymbols where
  metric     : MetricTensor
  /-- 3-index components as an n×n×n array (flattened: i*n²+j*n+k). -/
  components : Array Expr          -- size n³
  idx1 : IndexKind
  idx2 : IndexKind
  idx3 : IndexKind
  deriving Repr

namespace ChristoffelSymbols

-- ---------------------------------------------------------------------------
-- Internal helpers
-- ---------------------------------------------------------------------------

/-- Get Γ component at (i,j,k) from a flattened n³ array. -/
def getComp (n : Nat) (comps : Array Expr) (i j k : Nat) : Expr :=
  comps[i * n * n + j * n + k]? |>.getD (.lit 0)

/-- Set Γ component at (i,j,k) in a flattened n³ array. -/
private def setComp (n : Nat) (comps : Array Expr) (i j k : Nat) (e : Expr)
    : Array Expr :=
  comps.set! (i * n * n + j * n + k) e

/-- Compute the standard mixed Γ^λ_{μν} (idx = False,True,True) from a
    covariant metric matrix and its inverse. -/
def computeMixed (gCov gInv : Mat) (coords : Array String) : Array Expr :=
  let n := gCov.size
  -- Γ^λ_{μν} = (1/2) Σ_σ gInv^{λσ} (∂_μ g_{σν} + ∂_ν g_{σμ} - ∂_σ g_{μν})
  let size := n * n * n
  let comps := List.replicate size (.lit 0) |>.toArray
  (List.range n).foldl (fun comps lam_ =>
    (List.range n).foldl (fun comps μ =>
      (List.range n).foldl (fun comps ν =>
        let val := sumN n (fun σ =>
          let gInv_lσ := matGet gInv lam_ σ
          let d_μ_σν  := symDiff (matGet gCov σ ν) (coords[μ]!)
          let d_ν_σμ  := symDiff (matGet gCov σ μ) (coords[ν]!)
          let d_σ_μν  := symDiff (matGet gCov μ ν) (coords[σ]!)
          simplify (.mul (.mul (.lit (1/2)) gInv_lσ) (.sub (.add d_μ_σν d_ν_σμ) d_σ_μν)))
        setComp n comps lam_ μ ν val
      ) comps
    ) comps
  ) comps

-- ---------------------------------------------------------------------------
-- Constructor
-- ---------------------------------------------------------------------------

/-- Build ChristoffelSymbols from a MetricTensor with given output index positions.
    The WL default is `(False, True, True)` = Γ^λ_{μν}. -/
def ofMetric (g : MetricTensor)
    (idx1 : IndexKind := con) (idx2 : IndexKind := co) (idx3 : IndexKind := co)
    : ChristoffelSymbols :=
  let gCov := g.covariantMatrix
  let gInv := g.inverseMatrix
  let n    := g.dim
  let coords := g.coords
  -- Always compute mixed Γ^λ_{μν} first
  let mixedComps := computeMixed gCov gInv coords
  -- Then raise/lower indices to match requested positions
  let comps := convertIndices n gCov gInv mixedComps idx1 idx2 idx3
  { metric := g, components := comps, idx1, idx2, idx3 }

where
  /-- Raise/lower the mixed (con,co,co) components to any combination. -/
  convertIndices (n : Nat) (gCov gInv : Mat) (mixed : Array Expr)
      (i1 i2 i3 : IndexKind) : Array Expr :=
    -- mixed: getComp n mixed λ μ ν  = Γ^λ_{μν}
    let get := fun lam_ μ ν => getComp n mixed lam_ μ ν
    let set := fun comps lam_ μ ν e => setComp n comps lam_ μ ν e
    let base := List.replicate (n*n*n) (.lit 0) |>.toArray
    (List.range n).foldl (fun comps i =>
      (List.range n).foldl (fun comps j =>
        (List.range n).foldl (fun comps k =>
          let val := match i1, i2, i3 with
          -- (con, co, co) = standard  Γ^λ_{μν}  -- identity
          | false, true,  true  => get i j k
          -- (co, co, co) = Γ_{λμν} = g_{λσ} Γ^σ_{μν}
          | true,  true,  true  =>
              sumN n (fun σ => simplify (.mul (matGet gCov i σ) (get σ j k)))
          -- (con, con, con) = Γ^{λμν} = g^{μσ₁} g^{νσ₂} Γ^λ_{σ₁σ₂}
          | false, false, false =>
              sumN n (fun s1 => sumN n (fun s2 =>
                simplify (.mul (.mul (matGet gInv j s1) (matGet gInv k s2)) (get i s1 s2))))
          -- (co, con, con)
          | true,  false, false =>
              sumN n (fun σ => sumN n (fun s1 => sumN n (fun s2 =>
                simplify (.mul (.mul (.mul (matGet gCov i σ) (matGet gInv j s1))
                                    (.mul (matGet gInv k s2) (get σ s1 s2))) (.lit 1)))))
          -- (con, co, con)
          | false, true,  false =>
              sumN n (fun σ => simplify (.mul (matGet gInv k σ) (get i j σ)))
          -- (con, con, co)
          | false, false, true  =>
              sumN n (fun σ => simplify (.mul (matGet gInv j σ) (get i σ k)))
          -- (co, co, con)
          | true,  true,  false =>
              sumN n (fun σ => sumN n (fun s =>
                simplify (.mul (.mul (matGet gCov i σ) (matGet gInv k s)) (get σ j s))))
          -- (co, con, co)
          | true,  false, true  =>
              sumN n (fun σ => sumN n (fun s =>
                simplify (.mul (.mul (matGet gCov i σ) (matGet gInv j s)) (get σ s k))))
          set comps i j k val
        ) comps
      ) comps
    ) base

-- ---------------------------------------------------------------------------
-- Accessor
-- ---------------------------------------------------------------------------

/-- Get the component Γ_{ijk} (in whatever variance the struct stores). -/
def get (cs : ChristoffelSymbols) (i j k : Nat) : Expr :=
  getComp cs.metric.dim cs.components i j k

-- ---------------------------------------------------------------------------
-- Properties
-- ---------------------------------------------------------------------------

/-- True iff stored indices are all covariant. -/
def isFullyCovariant (cs : ChristoffelSymbols) : Bool :=
  cs.idx1 && cs.idx2 && cs.idx3

/-- True iff stored indices are all contravariant. -/
def isFullyContravariant (cs : ChristoffelSymbols) : Bool :=
  !cs.idx1 && !cs.idx2 && !cs.idx3

/-- True iff this is the standard mixed Γ^λ_{μν}. -/
def isStandardMixed (cs : ChristoffelSymbols) : Bool :=
  !cs.idx1 && cs.idx2 && cs.idx3

/-- Test whether all Christoffel symbols vanish (syntactically zero). -/
def isVanishing (cs : ChristoffelSymbols) : Bool :=
  cs.components.all (· == .lit 0)

/-- Index list as an array of `IndexKind`. -/
def indices (cs : ChristoffelSymbols) : Array IndexKind :=
  #[cs.idx1, cs.idx2, cs.idx3]

/-- Coordinate one-forms (for display). -/
def coordinateOneForms (cs : ChristoffelSymbols) : Array String :=
  cs.metric.coords.map (fun x => s!"d{x}")

end ChristoffelSymbols
end Gravitas
