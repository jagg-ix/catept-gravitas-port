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

mutual

/-- Structural simplification: collapses obvious algebraic identities.
    Not a complete CAS but sufficient for the GR tensor computations. -/
partial def simplify (e : Expr) : Expr :=
  match e with
  -- .neg: simplify argument first, then apply neg-elim rules
  | .neg a            =>
      match simplify a with
      | .lit 0     => .lit 0
      | .neg inner => inner               -- double-neg elimination
      | a'         => .neg a'
  | .add a (.lit 0)   => simplify a
  | .add (.lit 0) b   => simplify b
  | .add (.lit a) (.lit b) => .lit (a + b)
  -- AFP tier-A: canonical form for neg-in-add
  | .add (.neg a) b   =>
      let a' := simplify a; let b' := simplify b
      if a' == b' then .lit 0 else .sub b' a'
  | .add a (.neg b)   =>
      let a' := simplify a; let b' := simplify b
      if a' == b' then .lit 0 else .sub a' b'
  | .add a b          =>
      let a' := simplify a; let b' := simplify b
      if a' == .lit 0 then b'
      else if b' == .lit 0 then a'
      else .add a' b'
  | .sub a (.lit 0)   => simplify a
  | .sub (.lit 0) b   => simplify (.neg b)
  | .sub (.lit a) (.lit b) => .lit (a - b)
  | .sub a b          =>
      let a' := simplify a; let b' := simplify b
      if a' == b' then .lit 0
      else .sub a' b'
  | .mul (.lit 0) _   => .lit 0
  | .mul _ (.lit 0)   => .lit 0
  | .mul (.lit 1) b   => simplify b
  | .mul a (.lit 1)   => simplify a
  | .mul (.lit (-1)) b => simplify (.neg b)
  | .mul a (.lit (-1)) => simplify (.neg a)
  | .mul (.lit a) (.lit b) => .lit (a * b)
  -- AFP: push neg outward for cleaner canonical form
  | .mul (.neg a) (.neg b) => simplify (.mul a b)
  | .mul (.neg a) b   =>
      let a' := simplify a; let b' := simplify b
      simplify (.neg (.mul a' b'))
  | .mul a (.neg b)   =>
      let a' := simplify a; let b' := simplify b
      simplify (.neg (.mul a' b'))
  | .mul a b          =>
      let a' := simplify a; let b' := simplify b
      if a' == .lit 0 || b' == .lit 0 then .lit 0
      else if a' == .lit 1 then b'
      else if b' == .lit 1 then a'
      else .mul a' b'
  | .div a (.lit 1)   => simplify a
  | .div (.lit 0) _   => .lit 0
  | .div (.lit a) (.lit b) =>
      if b == 0 then .div (.lit a) (.lit b)
      else .lit (a / b)
  -- AFP: push neg outward through division
  | .div (.neg a) (.neg b) => simplify (.div a b)
  | .div (.neg a) b   => simplify (.neg (.div a b))
  | .div a (.neg b)   => simplify (.neg (.div a b))
  | .div a b          => .div (simplify a) (simplify b)
  | .pow _ (.lit 0)   => .lit 1
  | .pow a (.lit 1)   => simplify a
  | .pow (.lit 0) _   => .lit 0
  | .pow (.lit 1) _   => .lit 1
  | .pow (.lit a) (.lit b) =>
      -- only simplify when exponent is a non-negative integer
      if b.den == 1 && b.num ≥ 0 then
        .lit (a ^ b.num.toNat)
      else .pow (.lit a) (.lit b)
  | .pow a b          => .pow (simplify a) (simplify b)
  | .sin (.lit 0)     => .lit 0
  | .cos (.lit 0)     => .lit 1
  | .sin a            => .sin (simplify a)
  | .cos a            => .cos (simplify a)
  | .sqrt (.lit 0)    => .lit 0
  | .sqrt (.lit 1)    => .lit 1
  | .sqrt a           => .sqrt (simplify a)
  | .log (.lit 1)     => .lit 0
  | .log a            => .log (simplify a)
  | .exp (.lit 0)     => .lit 1
  | .exp a            => .exp (simplify a)
  | .diff a x         => simplify (symDiff a x)
  | e                 => e

/-- Symbolic differentiation: ∂e/∂x, with immediate simplification. -/
partial def symDiff (e : Expr) (x : String) : Expr :=
  simplify <| match e with
  | .lit _         => .lit 0
  | .var y         => if y == x then .lit 1 else .lit 0
  | .neg a         => .neg (symDiff a x)
  | .add a b       => .add (symDiff a x) (symDiff b x)
  | .sub a b       => .sub (symDiff a x) (symDiff b x)
  | .mul a b       => .add (.mul (symDiff a x) b) (.mul a (symDiff b x))
  | .div a b       => .div (.sub (.mul (symDiff a x) b) (.mul a (symDiff b x)))
                           (.mul b b)
  | .pow a (.lit n) =>
      .mul (.mul (.lit n) (.pow a (.lit (n - 1)))) (symDiff a x)
  | .pow a b       =>
      -- d/dx [a^b] = a^b * (b' ln a + b a'/a)
      .mul (.pow a b)
           (.add (.mul (symDiff b x) (.log a))
                 (.mul b (.div (symDiff a x) a)))
  | .sin a         => .mul (.cos a) (symDiff a x)
  | .cos a         => .mul (.neg (.sin a)) (symDiff a x)
  | .sqrt a        => .div (symDiff a x) (.mul (.lit 2) (.sqrt a))
  | .log a         => .div (symDiff a x) a
  | .exp a         => .mul (.exp a) (symDiff a x)
  | .diff e' y     =>
      -- formal mixed partial: keep as nested diff
      if x == y then .diff (symDiff e' x) x
      else .diff (symDiff e' x) y

end

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
