/-!
# Gravitas.Basic

Core symbolic expression type and matrix algebra for the Gravitas GR library.

## Design

We use a lightweight symbolic expression ADT `Expr` that supports:
- Rational literals, named variables
- Arithmetic (add, sub, mul, div, pow, neg)
- Transcendental functions (sin, cos, sqrt, log, exp)
- Formal partial differentiation `∂e/∂x`

Matrices are `Array (Array Expr)` (row-major). Index convention matches the
Wolfram Language source: `True` = covariant (lower), `False` = contravariant (upper).
-/

namespace Gravitas

-- ---------------------------------------------------------------------------
-- Symbolic expression type
-- ---------------------------------------------------------------------------

/-- A symbolic scalar expression. `diff e x` denotes ∂e/∂x. -/
inductive Expr : Type where
  | lit  : Rat → Expr
  | var  : String → Expr
  | neg  : Expr → Expr
  | add  : Expr → Expr → Expr
  | sub  : Expr → Expr → Expr
  | mul  : Expr → Expr → Expr
  | div  : Expr → Expr → Expr
  | pow  : Expr → Expr → Expr
  | sin  : Expr → Expr
  | cos  : Expr → Expr
  | sqrt : Expr → Expr
  | log  : Expr → Expr
  | exp  : Expr → Expr
  | diff : Expr → String → Expr   -- formal partial derivative
  deriving Repr, BEq, Inhabited

instance (n : Nat) : OfNat Expr n where
  ofNat := .lit n

instance : Neg Expr where
  neg := .neg

instance : Add Expr where
  add := .add

instance : Sub Expr where
  sub := .sub

instance : Mul Expr where
  mul := .mul

instance : Div Expr where
  div := .div

/-- Shorthand for a rational literal p/d. -/
def q (num den : Int) : Expr := .div (.lit (num : Rat)) (.lit (den : Rat))

-- ---------------------------------------------------------------------------
-- Basic simplification
-- ---------------------------------------------------------------------------

/-- Structural size of an `Expr`, used to bound the fuel passed to
`simplifyN` / `symDiffN`.  Each constructor contributes at least 1; the
`.diff` formal-derivative constructor contributes its subterm's size plus
a small constant so that the recursive
`simplify (.diff a x) = simplify (symDiff a x)` step has enough budget. -/
def Expr.size : Expr → Nat
  | .lit _      => 1
  | .var _      => 1
  | .neg a      => a.size + 1
  | .add a b    => a.size + b.size + 1
  | .sub a b    => a.size + b.size + 1
  | .mul a b    => a.size + b.size + 1
  | .div a b    => a.size + b.size + 1
  | .pow a b    => a.size + b.size + 1
  | .sin a      => a.size + 1
  | .cos a      => a.size + 1
  | .sqrt a     => a.size + 1
  | .log a      => a.size + 1
  | .exp a      => a.size + 1
  | .diff a _   => 2 * a.size + 4

/-- Fuel computed from an `Expr` for the top-level `simplify` wrapper.
We use a generous bound so that even repeated symbolic-derivative chains
within a single call terminate; for the canonical GR-tensor inputs the
budget is comfortably sufficient. -/
def Expr.simplifyFuel (e : Expr) : Nat := e.size * 4 + 64

mutual

/-- Fuel-bounded structural simplifier.  Total, kernel-reducible: structurally
recursive on `n : Nat`.  Returns the input unchanged when fuel is exhausted.
This is the kernel-reducible engine behind `Gravitas.simplify`. -/
def simplifyN : Nat → Expr → Expr
  | 0,     e => e
  | n+1,   e =>
    match e with
    -- .neg: simplify argument first, then apply neg-elim rules
    | .neg a            =>
        match simplifyN n a with
        | .lit 0     => .lit 0
        | .neg inner => inner               -- double-neg elimination
        | a'         => .neg a'
    | .add a (.lit 0)   => simplifyN n a
    | .add (.lit 0) b   => simplifyN n b
    | .add (.lit a) (.lit b) => .lit (a + b)
    -- AFP tier-A: canonical form for neg-in-add
    | .add (.neg a) b   =>
        let a' := simplifyN n a; let b' := simplifyN n b
        if a' == b' then .lit 0 else .sub b' a'
    | .add a (.neg b)   =>
        let a' := simplifyN n a; let b' := simplifyN n b
        if a' == b' then .lit 0 else .sub a' b'
    | .add a b          =>
        let a' := simplifyN n a; let b' := simplifyN n b
        if a' == .lit 0 then b'
        else if b' == .lit 0 then a'
        else .add a' b'
    | .sub a (.lit 0)   => simplifyN n a
    | .sub (.lit 0) b   => simplifyN n (.neg b)
    | .sub (.lit a) (.lit b) => .lit (a - b)
    | .sub a b          =>
        let a' := simplifyN n a; let b' := simplifyN n b
        if a' == b' then .lit 0
        else .sub a' b'
    | .mul (.lit 0) _   => .lit 0
    | .mul _ (.lit 0)   => .lit 0
    | .mul (.lit 1) b   => simplifyN n b
    | .mul a (.lit 1)   => simplifyN n a
    | .mul (.lit (-1)) b => simplifyN n (.neg b)
    | .mul a (.lit (-1)) => simplifyN n (.neg a)
    | .mul (.lit a) (.lit b) => .lit (a * b)
    -- AFP: push neg outward for cleaner canonical form
    | .mul (.neg a) (.neg b) => simplifyN n (.mul a b)
    | .mul (.neg a) b   =>
        let a' := simplifyN n a; let b' := simplifyN n b
        simplifyN n (.neg (.mul a' b'))
    | .mul a (.neg b)   =>
        let a' := simplifyN n a; let b' := simplifyN n b
        simplifyN n (.neg (.mul a' b'))
    | .mul a b          =>
        let a' := simplifyN n a; let b' := simplifyN n b
        if a' == .lit 0 || b' == .lit 0 then .lit 0
        else if a' == .lit 1 then b'
        else if b' == .lit 1 then a'
        else .mul a' b'
    | .div a (.lit 1)   => simplifyN n a
    | .div (.lit 0) _   => .lit 0
    | .div (.lit a) (.lit b) =>
        if b == 0 then .div (.lit a) (.lit b)
        else .lit (a / b)
    -- AFP: push neg outward through division
    | .div (.neg a) (.neg b) => simplifyN n (.div a b)
    | .div (.neg a) b   => simplifyN n (.neg (.div a b))
    | .div a (.neg b)   => simplifyN n (.neg (.div a b))
    | .div a b          => .div (simplifyN n a) (simplifyN n b)
    | .pow _ (.lit 0)   => .lit 1
    | .pow a (.lit 1)   => simplifyN n a
    | .pow (.lit 0) _   => .lit 0
    | .pow (.lit 1) _   => .lit 1
    | .pow (.lit a) (.lit b) =>
        -- only simplify when exponent is a non-negative integer
        if b.den == 1 && b.num ≥ 0 then
          .lit (a ^ b.num.toNat)
        else .pow (.lit a) (.lit b)
    | .pow a b          => .pow (simplifyN n a) (simplifyN n b)
    | .sin (.lit 0)     => .lit 0
    | .cos (.lit 0)     => .lit 1
    | .sin a            => .sin (simplifyN n a)
    | .cos a            => .cos (simplifyN n a)
    | .sqrt (.lit 0)    => .lit 0
    | .sqrt (.lit 1)    => .lit 1
    | .sqrt a           => .sqrt (simplifyN n a)
    | .log (.lit 1)     => .lit 0
    | .log a            => .log (simplifyN n a)
    | .exp (.lit 0)     => .lit 1
    | .exp a            => .exp (simplifyN n a)
    | .diff a x         => simplifyN n (symDiffN n a x)
    | e                 => e

/-- Fuel-bounded symbolic differentiation: ∂e/∂x with immediate simplification.
Total, kernel-reducible: structurally recursive on `n : Nat`.  Returns the
input unchanged when fuel is exhausted.  This is the kernel-reducible engine
behind `Gravitas.symDiff`. -/
def symDiffN : Nat → Expr → String → Expr
  | 0,   e, _ => e
  | n+1, e, x =>
    simplifyN n <| match e with
    | .lit _         => .lit 0
    | .var y         => if y == x then .lit 1 else .lit 0
    | .neg a         => .neg (symDiffN n a x)
    | .add a b       => .add (symDiffN n a x) (symDiffN n b x)
    | .sub a b       => .sub (symDiffN n a x) (symDiffN n b x)
    | .mul a b       => .add (.mul (symDiffN n a x) b) (.mul a (symDiffN n b x))
    | .div a b       => .div (.sub (.mul (symDiffN n a x) b) (.mul a (symDiffN n b x)))
                             (.mul b b)
    | .pow a (.lit k) =>
        .mul (.mul (.lit k) (.pow a (.lit (k - 1)))) (symDiffN n a x)
    | .pow a b       =>
        -- d/dx [a^b] = a^b * (b' ln a + b a'/a)
        .mul (.pow a b)
             (.add (.mul (symDiffN n b x) (.log a))
                   (.mul b (.div (symDiffN n a x) a)))
    | .sin a         => .mul (.cos a) (symDiffN n a x)
    | .cos a         => .mul (.neg (.sin a)) (symDiffN n a x)
    | .sqrt a        => .div (symDiffN n a x) (.mul (.lit 2) (.sqrt a))
    | .log a         => .div (symDiffN n a x) a
    | .exp a         => .mul (.exp a) (symDiffN n a x)
    | .diff e' y     =>
        -- formal mixed partial: keep as nested diff
        if x == y then .diff (symDiffN n e' x) x
        else .diff (symDiffN n e' x) y

end

/-- Structural simplification: collapses obvious algebraic identities.
    Not a complete CAS but sufficient for the GR tensor computations.

    This is a total, kernel-reducible wrapper around `simplifyN` with an
    automatically-computed fuel bound derived from the input's structural
    size.  Replaces the previous `partial def simplify`; downstream call
    sites are unchanged.

    Note: this `def` is kernel-reducible.  Heavy `rfl`/`decide` proofs at
    call sites that exercise deep symbolic reduction may need to bump
    `set_option maxRecDepth` (e.g. `set_option maxRecDepth 4096`). -/
def simplify (e : Expr) : Expr := simplifyN e.simplifyFuel e

/-- Symbolic differentiation: ∂e/∂x, with immediate simplification.

    Total, kernel-reducible wrapper around `symDiffN` with an
    automatically-computed fuel bound.  Replaces the previous
    `partial def symDiff`; downstream call sites are unchanged.

    Note: kernel-reducible; cf. note on `simplify`. -/
def symDiff (e : Expr) (x : String) : Expr := symDiffN e.simplifyFuel e x

-- ---------------------------------------------------------------------------
-- Matrix type and helpers
-- ---------------------------------------------------------------------------

/-- Row-major matrix of symbolic expressions. -/
abbrev Mat := Array (Array Expr)

/-- Build an n×n matrix from a function (row, col) → Expr.  0-indexed. -/
def matBuild (n : Nat) (f : Nat → Nat → Expr) : Mat :=
  Array.ofFn (n := n) (fun i : Fin n => Array.ofFn (n := n) (fun j : Fin n => f i.val j.val))

/-- Get element at (i, j). Returns 0 on out-of-bounds. -/
def matGet (m : Mat) (i j : Nat) : Expr :=
  (m[i]?.bind (·[j]?)).getD (.lit 0)

/-- Number of rows (= cols for square matrices). -/
def matSize (m : Mat) : Nat := m.size

/-- Sum `f k` for k in 0..n-1. -/
def sumN (n : Nat) (f : Nat → Expr) : Expr :=
  (List.range n).foldl (fun acc k => simplify (.add acc (f k))) (.lit 0)

/-- Scalar multiplication of a matrix. -/
def matScale (s : Expr) (m : Mat) : Mat :=
  m.map (·.map (fun e => simplify (.mul s e)))

/-- Pointwise addition of two n×n matrices. -/
def matAdd (a b : Mat) : Mat :=
  let n := a.size
  matBuild n (fun i j => simplify (.add (matGet a i j) (matGet b i j)))

/-- Pointwise subtraction. -/
def matSub (a b : Mat) : Mat :=
  let n := a.size
  matBuild n (fun i j => simplify (.sub (matGet a i j) (matGet b i j)))

/-- n×n matrix multiplication. -/
def matMul (a b : Mat) : Mat :=
  let n := a.size
  matBuild n (fun i j =>
    sumN n (fun k => simplify (.mul (matGet a i k) (matGet b k j))))

/-- Identity matrix of size n. -/
def matId (n : Nat) : Mat :=
  matBuild n (fun i j => if i == j then .lit 1 else .lit 0)

/-- Transpose. -/
def matTranspose (m : Mat) : Mat :=
  let n := m.size
  matBuild n (fun i j => matGet m j i)

-- ---------------------------------------------------------------------------
-- Matrix inverse via Gauss-Jordan elimination over Expr
-- ---------------------------------------------------------------------------

/-- Row-reduce [m | I] to get the inverse. Returns `none` if the pivot is
    syntactically zero at every step (does not attempt full algebraic
    simplification of the pivot). -/
def matInv (m : Mat) : Option Mat :=
  let n := m.size
  -- Augmented matrix [m | I], represented as Array (Array Expr)
  let aug0 : Array (Array Expr) :=
    Array.ofFn (n := n) (fun i : Fin n =>
      Array.ofFn (n := 2 * n) (fun j : Fin (2 * n) =>
        if j.val < n then matGet m i.val j.val
        else if j.val - n == i.val then .lit 1 else .lit 0))
  let aug1 := (List.range n).foldl (fun (aug : Option (Array (Array Expr))) col =>
    match aug with
    | none => none
    | some rows =>
      -- Find pivot row (first non-zero in column `col` from row `col` down)
      let pivot? := (List.range (n - col)).find? (fun k =>
        simplify (rows[col + k]![col]!) != .lit 0)
      match pivot? with
      | none => none
      | some rel =>
        let pivotRow := col + rel
        -- Swap rows col ↔ pivotRow
        let rows := if pivotRow == col then rows
                    else rows.set! col rows[pivotRow]! |>.set! pivotRow rows[col]!
        let pivotVal := simplify (rows[col]![col]!)
        -- Scale pivot row by 1/pivot
        let rows := rows.set! col
          (rows[col]!.map (fun e => simplify (.div e pivotVal)))
        -- Eliminate all other rows
        let rows := (List.range n).foldl (fun rows row =>
          if row == col then rows
          else
            let factor := simplify (rows[row]![col]!)
            rows.set! row
              ((List.range (2 * n)).foldl (fun row_arr j =>
                row_arr.set! j (simplify (.sub (row_arr[j]!)
                  (.mul factor (rows[col]![j]!))))) rows[row]!)
        ) rows
        some rows
  ) (some aug0)
  match aug1 with
  | none => none
  | some rows =>
    -- Extract the right half (columns n..2n-1)
    some (Array.ofFn (n := n) (fun i : Fin n =>
      Array.ofFn (n := n) (fun j : Fin n => simplify (rows[i.val]![(n + j.val)]!))))

/-- Compute matrix inverse, panicking on failure (for use when invertibility
    is guaranteed by construction). -/
def matInv! (m : Mat) : Mat :=
  match matInv m with
  | some inv => inv
  | none     => panic! "matInv!: matrix is not invertible"

-- ---------------------------------------------------------------------------
-- Tensor index convention (matching Wolfram Language True/False)
-- ---------------------------------------------------------------------------

/-- Index position. `true` = covariant (lower/subscript), matching WL `True`.
    `false` = contravariant (upper/superscript), matching WL `False`. -/
abbrev IndexKind := Bool

/-- Covariant (lower) index — WL `True`. -/
abbrev co : IndexKind := true

/-- Contravariant (upper) index — WL `False`. -/
abbrev con : IndexKind := false

-- ---------------------------------------------------------------------------
-- Index raising / lowering helpers
-- ---------------------------------------------------------------------------

/-- Lower a 1-index contravariant tensor using the covariant metric.
    Result_i = g_{ij} v^j. -/
def lowerIndex (g : Mat) (v : Array Expr) : Array Expr :=
  let n := g.size
  Array.ofFn (n := n) (fun i : Fin n => sumN n (fun j => simplify (.mul (matGet g i.val j) (v[j]!))))

/-- Raise a 1-index covariant tensor using the inverse metric.
    Result^i = g^{ij} v_j. -/
def raiseIndex (gInv : Mat) (v : Array Expr) : Array Expr :=
  let n := gInv.size
  Array.ofFn (n := n) (fun i : Fin n => sumN n (fun j => simplify (.mul (matGet gInv i.val j) (v[j]!))))

-- ---------------------------------------------------------------------------
-- Tensor coordinate substitution
-- ---------------------------------------------------------------------------

/-- Substitute `old → new` in an expression (exact variable rename). -/
partial def exprSubst (e : Expr) (old new : String) : Expr :=
  match e with
  | .var y         => if y == old then .var new else e
  | .neg a         => .neg (exprSubst a old new)
  | .add a b       => .add (exprSubst a old new) (exprSubst b old new)
  | .sub a b       => .sub (exprSubst a old new) (exprSubst b old new)
  | .mul a b       => .mul (exprSubst a old new) (exprSubst b old new)
  | .div a b       => .div (exprSubst a old new) (exprSubst b old new)
  | .pow a b       => .pow (exprSubst a old new) (exprSubst b old new)
  | .sin a         => .sin (exprSubst a old new)
  | .cos a         => .cos (exprSubst a old new)
  | .sqrt a        => .sqrt (exprSubst a old new)
  | .log a         => .log (exprSubst a old new)
  | .exp a         => .exp (exprSubst a old new)
  | .diff a y      => .diff (exprSubst a old new) (if y == old then new else y)
  | e              => e

/-- Substitute `old → e'` (expression, not just rename). -/
partial def exprSubstExpr (e : Expr) (old : String) (e' : Expr) : Expr :=
  match e with
  | .var y         => if y == old then e' else e
  | .neg a         => .neg (exprSubstExpr a old e')
  | .add a b       => .add (exprSubstExpr a old e') (exprSubstExpr b old e')
  | .sub a b       => .sub (exprSubstExpr a old e') (exprSubstExpr b old e')
  | .mul a b       => .mul (exprSubstExpr a old e') (exprSubstExpr b old e')
  | .div a b       => .div (exprSubstExpr a old e') (exprSubstExpr b old e')
  | .pow a b       => .pow (exprSubstExpr a old e') (exprSubstExpr b old e')
  | .sin a         => .sin (exprSubstExpr a old e')
  | .cos a         => .cos (exprSubstExpr a old e')
  | .sqrt a        => .sqrt (exprSubstExpr a old e')
  | .log a         => .log (exprSubstExpr a old e')
  | .exp a         => .exp (exprSubstExpr a old e')
  | .diff a y      => .diff (exprSubstExpr a old e') y
  | e              => e

/-- Apply a list of (varName → Expr) substitutions to a matrix. -/
def matSubst (m : Mat) (subs : List (String × Expr)) : Mat :=
  m.map (·.map (fun e =>
    subs.foldl (fun e' (old, new) => exprSubstExpr e' old new) e))

/-- Apply a coordinate relabeling (old strings → new strings) to a matrix. -/
def matRelabel (m : Mat) (oldCoords newCoords : Array String) : Mat :=
  let subs := (List.range oldCoords.size).filterMap (fun i =>
    match oldCoords[i]?, newCoords[i]? with
    | some o, some n => if o == n then none else some (o, .var n)
    | _, _           => none)
  matSubst m subs

end Gravitas
