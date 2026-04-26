import CATEPTGravitasPort.Basic

/-!
# Gravitas.MetricTensor

Port of `Gravitas/Kernel/MetricTensor.wl`.

`MetricTensor` packages:
- `matrix`  : n×n matrix of `Expr` components g_{μν}
- `coords`  : the n coordinate symbols (as `String`)
- `idx1/2`  : index positions (`true` = covariant, `false` = contravariant)

All named metrics from the WL source are reproduced here.  Index raising and
lowering follow the WL convention: `true/true` = fully covariant, `false/false`
= fully contravariant, mixed otherwise.
-/

namespace Gravitas

-- ---------------------------------------------------------------------------
-- Core structure
-- ---------------------------------------------------------------------------

/-- A (pseudo-)Riemannian metric tensor with explicit index positions.
    `idx1` and `idx2` indicate whether the first and second index are covariant
    (`true`) or contravariant (`false`). -/
structure MetricTensor where
  /-- Dimension. -/
  dim    : Nat
  /-- Component matrix in the current index position. -/
  matrix : Mat
  /-- Coordinate labels. -/
  coords : Array String
  /-- First index position: `true` = covariant. -/
  idx1   : IndexKind
  /-- Second index position: `true` = covariant. -/
  idx2   : IndexKind
  deriving Repr, Inhabited

-- ---------------------------------------------------------------------------
-- Smart constructor – normalises to covariant form first then raises
-- ---------------------------------------------------------------------------

/-- Build a MetricTensor from a covariant matrix and raise/lower to the
    requested index positions.
    `gCov` must be the purely covariant (g_{μν}) matrix. -/
def MetricTensor.fromCovariant (gCov : Mat) (coords : Array String)
    (idx1 idx2 : IndexKind) : MetricTensor :=
  let n := gCov.size
  let matrix : Mat :=
    match idx1, idx2 with
    | true,  true  => gCov
    | false, false =>
      -- g^{μν} = (g_{μν})^{-1}
      matInv gCov |>.getD gCov
    | true,  false =>
      -- g^ν_μ = g_{μλ} g^{λν}  — but for a metric this is just δ^ν_μ ... unless
      -- the matrix is not symmetric.  General case: lower first, raise second.
      let gInv := matInv gCov |>.getD gCov
      -- (T)_{ij} = Σ_k g_{ik} gInv_{kj}  -- this is the identity for sym metric
      matMul gCov gInv
    | false, true  =>
      let gInv := matInv gCov |>.getD gCov
      matMul gInv gCov
  { dim := n, matrix, coords, idx1, idx2 }

-- ---------------------------------------------------------------------------
-- Generic symbolic metrics
-- ---------------------------------------------------------------------------

/-- Generic symmetric metric of dimension n with components g_{(ij)}.
    Components are named `g_ij` with sorted index pair. -/
def MetricTensor.symmetric (n : Nat) (coords : Array String)
    (idx1 idx2 : IndexKind) : MetricTensor :=
  let gCov := matBuild n (fun i j =>
    let ij := if i ≤ j then (i, j) else (j, i)
    .var s!"g_{ij.1}{ij.2}")
  MetricTensor.fromCovariant gCov coords idx1 idx2

/-- Generic asymmetric metric of dimension n with components g_{ij}. -/
def MetricTensor.asymmetric (n : Nat) (coords : Array String)
    (idx1 idx2 : IndexKind) : MetricTensor :=
  let gCov := matBuild n (fun i j => .var s!"g_{i}{j}")
  MetricTensor.fromCovariant gCov coords idx1 idx2

/-- Generic symmetric field-dependent metric: components depend on coordinates. -/
def MetricTensor.symmetricField (n : Nat) (coords : Array String)
    (idx1 idx2 : IndexKind) : MetricTensor :=
  let gCov := matBuild n (fun i j =>
    let ij := if i ≤ j then (i, j) else (j, i)
    -- g_{ij}(x^0, ..., x^{n-1})
    let args := String.intercalate "," coords.toList
    .var s!"g_{ij.1}{ij.2}({args})")
  MetricTensor.fromCovariant gCov coords idx1 idx2

/-- Asymmetric field-dependent metric. -/
def MetricTensor.asymmetricField (n : Nat) (coords : Array String)
    (idx1 idx2 : IndexKind) : MetricTensor :=
  let gCov := matBuild n (fun i j =>
    let args := String.intercalate "," coords.toList
    .var s!"g_{i}{j}({args})")
  MetricTensor.fromCovariant gCov coords idx1 idx2

-- ---------------------------------------------------------------------------
-- Euclidean metrics
-- ---------------------------------------------------------------------------

/-- Euclidean metric δ_{ij} of dimension n. -/
def MetricTensor.euclidean (n : Nat) (coords : Array String)
    (idx1 idx2 : IndexKind) : MetricTensor :=
  let gCov := matId n
  MetricTensor.fromCovariant gCov coords idx1 idx2

-- ---------------------------------------------------------------------------
-- Minkowski metric  diag(-1, 1, 1, ..., 1)
-- ---------------------------------------------------------------------------

def minkowskiCovariant (n : Nat) : Mat :=
  matBuild n (fun i j =>
    if i != j then .lit 0
    else if i == 0 then .lit (-1)
    else .lit 1)

/-- Minkowski metric of dimension n (signature −+++) with `coords`. -/
def MetricTensor.minkowski (n : Nat) (coords : Array String)
    (idx1 idx2 : IndexKind) : MetricTensor :=
  MetricTensor.fromCovariant (minkowskiCovariant n) coords idx1 idx2

-- ---------------------------------------------------------------------------
-- Schwarzschild  ds² = -(1-2M/r)dt² + dr²/(1-2M/r) + r²dΩ²
-- ---------------------------------------------------------------------------

/-- Schwarzschild metric.  Coordinates: [t, r, θ, φ].
    Mass parameter `M` is left as the variable `"M"`. -/
def schwarzschildCovariant (t r θ φ M : String) : Mat :=
  let f  := .sub (.lit 1) (.div (.mul (.lit 2) (.var M)) (.var r))  -- 1 - 2M/r
  matBuild 4 (fun i j =>
    if i != j then .lit 0
    else match i with
    | 0 => .neg f                                              -- g_{tt}
    | 1 => .div (.lit 1) f                                    -- g_{rr}
    | 2 => .pow (.var r) (.lit 2)                             -- g_{θθ}
    | 3 => .mul (.pow (.var r) (.lit 2)) (.pow (.sin (.var θ)) (.lit 2))  -- g_{φφ}
    | _ => .lit 0)

def MetricTensor.schwarzschild (mass : String := "M")
    (coords : Array String := #["t","r","θ","φ"])
    (idx1 idx2 : IndexKind := co) : MetricTensor :=
  let t := coords[0]!; let r := coords[1]!; let θ := coords[2]!; let φ := coords[3]!
  MetricTensor.fromCovariant (schwarzschildCovariant t r θ φ mass) coords idx1 idx2

-- ---------------------------------------------------------------------------
-- Isotropic Schwarzschild   ρ = r(1 + M/2ρ)²
-- ---------------------------------------------------------------------------

def MetricTensor.isotropicSchwarzschild (mass : String := "M")
    (coords : Array String := #["t","ρ","θ","φ"])
    (idx1 idx2 : IndexKind := co) : MetricTensor :=
  let t := coords[0]!; let ρ := coords[1]!; let θ := coords[2]!; let φ := coords[3]!
  -- φ = (1 - M/(2ρ))/(1 + M/(2ρ))
  let half_M_ρ := .div (.var mass) (.mul (.lit 2) (.var ρ))
  let φf := .div (.sub (.lit 1) half_M_ρ) (.add (.lit 1) half_M_ρ)
  let ψ  := .add (.lit 1) half_M_ρ   -- conformal factor ψ = 1 + M/(2ρ)
  let ψ4 := .pow ψ (.lit 4)
  let gCov := matBuild 4 (fun i j =>
    if i != j then .lit 0
    else match i with
    | 0 => .neg (.pow φf (.lit 2))
    | 1 => ψ4
    | 2 => .mul ψ4 (.pow (.var ρ) (.lit 2))
    | 3 => .mul ψ4 (.mul (.pow (.var ρ) (.lit 2)) (.pow (.sin (.var θ)) (.lit 2)))
    | _ => .lit 0)
  MetricTensor.fromCovariant gCov coords idx1 idx2

-- ---------------------------------------------------------------------------
-- Eddington–Finkelstein (ingoing and outgoing)
-- ---------------------------------------------------------------------------

def MetricTensor.ingoingEddingtonFinkelstein (mass : String := "M")
    (coords : Array String := #["v","r","θ","φ"])
    (idx1 idx2 : IndexKind := co) : MetricTensor :=
  let v := coords[0]!; let r := coords[1]!; let θ := coords[2]!
  let f := .sub (.lit 1) (.div (.mul (.lit 2) (.var mass)) (.var r))
  let gCov := matBuild 4 (fun i j =>
    match i, j with
    | 0, 0 => .neg f
    | 0, 1 => .lit 1
    | 1, 0 => .lit 1
    | 1, 1 => .lit 0
    | 2, 2 => .pow (.var r) (.lit 2)
    | 3, 3 => .mul (.pow (.var r) (.lit 2)) (.pow (.sin (.var θ)) (.lit 2))
    | _, _ => .lit 0)
  MetricTensor.fromCovariant gCov coords idx1 idx2

def MetricTensor.outgoingEddingtonFinkelstein (mass : String := "M")
    (coords : Array String := #["u","r","θ","φ"])
    (idx1 idx2 : IndexKind := co) : MetricTensor :=
  let r := coords[1]!; let θ := coords[2]!
  let f := .sub (.lit 1) (.div (.mul (.lit 2) (.var mass)) (.var r))
  let gCov := matBuild 4 (fun i j =>
    match i, j with
    | 0, 0 => .neg f
    | 0, 1 => .lit (-1)
    | 1, 0 => .lit (-1)
    | 1, 1 => .lit 0
    | 2, 2 => .pow (.var r) (.lit 2)
    | 3, 3 => .mul (.pow (.var r) (.lit 2)) (.pow (.sin (.var θ)) (.lit 2))
    | _, _ => .lit 0)
  MetricTensor.fromCovariant gCov coords idx1 idx2

-- ---------------------------------------------------------------------------
-- Gullstrand–Painlevé (ingoing and outgoing)
-- ---------------------------------------------------------------------------

def MetricTensor.ingoingGullstrandPainleve (mass : String := "M")
    (coords : Array String := #["t̃","r","θ","φ"])
    (idx1 idx2 : IndexKind := co) : MetricTensor :=
  let t := coords[0]!; let r := coords[1]!; let θ := coords[2]!
  let v := .sqrt (.div (.mul (.lit 2) (.var mass)) (.var r))  -- escape velocity
  let gCov := matBuild 4 (fun i j =>
    match i, j with
    | 0, 0 => .sub (.lit (-1)) (.pow v (.lit 2))
    | 0, 1 => v
    | 1, 0 => v
    | 1, 1 => .lit 1
    | 2, 2 => .pow (.var r) (.lit 2)
    | 3, 3 => .mul (.pow (.var r) (.lit 2)) (.pow (.sin (.var θ)) (.lit 2))
    | _, _ => .lit 0)
  MetricTensor.fromCovariant gCov coords idx1 idx2

def MetricTensor.outgoingGullstrandPainleve (mass : String := "M")
    (coords : Array String := #["t̃","r","θ","φ"])
    (idx1 idx2 : IndexKind := co) : MetricTensor :=
  let r := coords[1]!; let θ := coords[2]!
  let v := .sqrt (.div (.mul (.lit 2) (.var mass)) (.var r))
  let gCov := matBuild 4 (fun i j =>
    match i, j with
    | 0, 0 => .sub (.lit (-1)) (.pow v (.lit 2))
    | 0, 1 => .neg v
    | 1, 0 => .neg v
    | 1, 1 => .lit 1
    | 2, 2 => .pow (.var r) (.lit 2)
    | 3, 3 => .mul (.pow (.var r) (.lit 2)) (.pow (.sin (.var θ)) (.lit 2))
    | _, _ => .lit 0)
  MetricTensor.fromCovariant gCov coords idx1 idx2

-- ---------------------------------------------------------------------------
-- Kruskal–Szekeres
-- ---------------------------------------------------------------------------

def MetricTensor.kruskalSzekeres (mass : String := "M")
    (coords : Array String := #["T","X","θ","φ"])
    (idx1 idx2 : IndexKind := co) : MetricTensor :=
  let T := coords[0]!; let X := coords[1]!; let θ := coords[2]!
  -- r is implicitly defined by T²-X² = (1-r/2M)e^{r/2M}; we leave it symbolic
  let r := .var "r"  -- implicit r(T,X)
  let M := .var mass
  -- ds² = (32M³/r) e^{-r/2M} (-dT²+dX²) + r² dΩ²
  let fac32 := .div (.mul (.lit 32) (.mul (.pow M (.lit 3)) (.exp (.div (.neg r) (.mul (.lit 2) M))))) r
  let gCov := matBuild 4 (fun i j =>
    match i, j with
    | 0, 0 => .neg fac32
    | 1, 1 => fac32
    | 2, 2 => .pow r (.lit 2)
    | 3, 3 => .mul (.pow r (.lit 2)) (.pow (.sin (.var θ)) (.lit 2))
    | _, _ => .lit 0)
  MetricTensor.fromCovariant gCov coords idx1 idx2

-- ---------------------------------------------------------------------------
-- Kerr metric  (Boyer-Lindquist)
-- ds² = -(1-2Mr/Σ)dt² - (4Mar sin²θ/Σ)dt dφ + (Σ/Δ)dr² + Σdθ² + sin²θ(r²+a²+2Ma²r sin²θ/Σ)dφ²
-- where Σ = r²+a²cos²θ, Δ = r²-2Mr+a²,  a = J/M
-- ---------------------------------------------------------------------------

def MetricTensor.kerr (mass : String := "M") (angMom : String := "J")
    (coords : Array String := #["t","r","θ","φ"])
    (idx1 idx2 : IndexKind := co) : MetricTensor :=
  let t := coords[0]!; let r := coords[1]!; let θ := coords[2]!; let φ := coords[3]!
  let M := .var mass; let J := .var angMom
  let a   := .div J M                             -- spin param a = J/M
  let a2  := .pow a (.lit 2)
  let r2  := .pow (.var r) (.lit 2)
  let Sig  := .add r2 (.mul a2 (.pow (.cos (.var θ)) (.lit 2)))  -- r²+a²cos²θ
  let Δ   := .sub (.sub r2 (.mul (.mul (.lit 2) M) (.var r))) (.neg a2)
              -- r²-2Mr+a²
  let sinθ2 := .pow (.sin (.var θ)) (.lit 2)
  let gCov := matBuild 4 (fun i j =>
    match i, j with
    | 0, 0 => .neg (.sub (.lit 1) (.div (.mul (.mul (.lit 2) M) (.var r)) Sig))
    | 0, 3 => .neg (.div (.mul (.mul (.mul (.lit 2) M) (.mul (.var r) a)) sinθ2) Sig)
    | 3, 0 => .neg (.div (.mul (.mul (.mul (.lit 2) M) (.mul (.var r) a)) sinθ2) Sig)
    | 1, 1 => .div Sig Δ
    | 2, 2 => Sig
    | 3, 3 => .mul sinθ2
                (.add (.add Sig (.mul a2 sinθ2))
                      (.div (.mul (.mul (.lit 2) M) (.mul (.var r) (.mul a2 sinθ2))) Sig))
    | _, _ => .lit 0)
  MetricTensor.fromCovariant gCov coords idx1 idx2

-- ---------------------------------------------------------------------------
-- Reissner–Nordström
-- ds² = -f dt² + dr²/f + r²dΩ², f = 1-2M/r+Q²/r²
-- ---------------------------------------------------------------------------

def MetricTensor.reissnerNordstrom (mass : String := "M") (charge : String := "Q")
    (coords : Array String := #["t","r","θ","φ"])
    (idx1 idx2 : IndexKind := co) : MetricTensor :=
  let r := coords[1]!; let θ := coords[2]!
  let M := .var mass; let Q := .var charge
  let r_ := .var r
  let f := .add (.sub (.lit 1) (.div (.mul (.lit 2) M) r_)) (.div (.pow Q (.lit 2)) (.pow r_ (.lit 2)))
  let gCov := matBuild 4 (fun i j =>
    if i != j then .lit 0
    else match i with
    | 0 => .neg f
    | 1 => .div (.lit 1) f
    | 2 => .pow r_ (.lit 2)
    | 3 => .mul (.pow r_ (.lit 2)) (.pow (.sin (.var θ)) (.lit 2))
    | _ => .lit 0)
  MetricTensor.fromCovariant gCov coords idx1 idx2

-- ---------------------------------------------------------------------------
-- Kerr–Newman
-- ---------------------------------------------------------------------------

def MetricTensor.kerrNewman (mass : String := "M") (charge : String := "Q") (angMom : String := "J")
    (coords : Array String := #["t","r","θ","φ"])
    (idx1 idx2 : IndexKind := co) : MetricTensor :=
  let r := coords[1]!; let θ := coords[2]!
  let M := .var mass; let Q := .var charge; let J := .var angMom
  let a   := .div J M
  let a2  := .pow a (.lit 2)
  let r2  := .pow (.var r) (.lit 2)
  let Q2  := .pow Q (.lit 2)
  let Sig  := .add r2 (.mul a2 (.pow (.cos (.var θ)) (.lit 2)))
  let Δ   := .add (.sub (.sub r2 (.mul (.mul (.lit 2) M) (.var r))) (.neg a2)) (.neg Q2)
  let sinθ2 := .pow (.sin (.var θ)) (.lit 2)
  let gCov := matBuild 4 (fun i j =>
    match i, j with
    | 0, 0 => .neg (.sub (.lit 1) (.div (.sub (.mul (.mul (.lit 2) M) (.var r)) Q2) Sig))
    | 0, 3 => .mul (.neg sinθ2) (.div (.mul a (.sub (.mul (.mul (.lit 2) M) (.var r)) Q2)) Sig)
    | 3, 0 => .mul (.neg sinθ2) (.div (.mul a (.sub (.mul (.mul (.lit 2) M) (.var r)) Q2)) Sig)
    | 1, 1 => .div Sig Δ
    | 2, 2 => Sig
    | 3, 3 =>
        let base := .add r2 a2
        let corr := .div (.sub (.sub (.mul a2 sinθ2) (.neg Q2)) (.mul (.mul (.lit 2) M) (.var r))) Sig
        .mul sinθ2 (.add base corr)
    | _, _ => .lit 0)
  MetricTensor.fromCovariant gCov coords idx1 idx2

-- ---------------------------------------------------------------------------
-- Gödel metric
-- ds² = -dt² - e^{√2 ω x} dt dz - (1/2) e^{2√2 ω x} dz² + dx² + dy²
-- (using coordinates t, x, y, z)
-- ---------------------------------------------------------------------------

def MetricTensor.godel (ω : String := "ω")
    (coords : Array String := #["t","x","y","z"])
    (idx1 idx2 : IndexKind := co) : MetricTensor :=
  let x := coords[1]!
  let ω_ := .var ω
  -- g_{tz} = -e^{√2 ω x},  g_{zz} = -½ e^{2√2 ω x}
  let ex  := .exp (.mul (.sqrt (.lit 2)) (.mul ω_ (.var x)))         -- e^{√2 ω x}
  let ex2 := .exp (.mul (.mul (.lit 2) (.sqrt (.lit 2))) (.mul ω_ (.var x)))  -- e^{2√2 ω x}
  let gCov := matBuild 4 (fun i j =>
    match i, j with
    | 0, 0 => .lit (-1)
    | 0, 3 => .neg ex
    | 3, 0 => .neg ex
    | 1, 1 => .lit 1
    | 2, 2 => .lit 1
    | 3, 3 => .mul (.lit (-1)) (.div ex2 (.lit 2))
    | _, _ => .lit 0)
  MetricTensor.fromCovariant gCov coords idx1 idx2

-- ---------------------------------------------------------------------------
-- FLRW  ds² = -dt² + a(t)²(dx²/(1-k r²) + r²dΩ²)
-- ---------------------------------------------------------------------------

def MetricTensor.flrw (scaleParam : String := "a") (curvParam : String := "k")
    (coords : Array String := #["t","r","θ","φ"])
    (idx1 idx2 : IndexKind := co) : MetricTensor :=
  let t := coords[0]!; let r := coords[1]!; let θ := coords[2]!
  let a_t := .var s!"{scaleParam}({t})"     -- a(t) as a named function
  let k   := .var curvParam
  let r_  := .var r
  let a2  := .pow a_t (.lit 2)
  let gCov := matBuild 4 (fun i j =>
    if i != j then .lit 0
    else match i with
    | 0 => .lit (-1)
    | 1 => .div a2 (.sub (.lit 1) (.mul k (.pow r_ (.lit 2))))
    | 2 => .mul a2 (.pow r_ (.lit 2))
    | 3 => .mul a2 (.mul (.pow r_ (.lit 2)) (.pow (.sin (.var θ)) (.lit 2)))
    | _ => .lit 0)
  MetricTensor.fromCovariant gCov coords idx1 idx2

-- ---------------------------------------------------------------------------
-- Named metric dispatch (mirrors WL's `MetricTensor["name"]`)
-- ---------------------------------------------------------------------------

/-- Named metric constructor.  Returns `none` for unknown names. -/
def MetricTensor.named (name : String) (idx1 idx2 : IndexKind := co) : Option MetricTensor :=
  match name with
  | "Symmetric"                 => some (MetricTensor.symmetric 4 #["x0","x1","x2","x3"] idx1 idx2)
  | "Asymmetric"                => some (MetricTensor.asymmetric 4 #["x0","x1","x2","x3"] idx1 idx2)
  | "SymmetricField"            => some (MetricTensor.symmetricField 4 #["x0","x1","x2","x3"] idx1 idx2)
  | "AsymmetricField"           => some (MetricTensor.asymmetricField 4 #["x0","x1","x2","x3"] idx1 idx2)
  | "Euclidean"                 => some (MetricTensor.euclidean 3 #["x1","x2","x3"] idx1 idx2)
  | "Minkowski"                 => some (MetricTensor.minkowski 4 #["t","x1","x2","x3"] idx1 idx2)
  | "Schwarzschild"             => some (MetricTensor.schwarzschild)
  | "IsotropicSchwarzschild"    => some (MetricTensor.isotropicSchwarzschild)
  | "IngoingEddingtonFinkelstein"  => some (MetricTensor.ingoingEddingtonFinkelstein)
  | "OutgoingEddingtonFinkelstein" => some (MetricTensor.outgoingEddingtonFinkelstein)
  | "EddingtonFinkelstein"      => some (MetricTensor.ingoingEddingtonFinkelstein)
  | "IngoingGullstrandPainleve" => some (MetricTensor.ingoingGullstrandPainleve)
  | "OutgoingGullstrandPainleve"=> some (MetricTensor.outgoingGullstrandPainleve)
  | "GullstrandPainleve"        => some (MetricTensor.ingoingGullstrandPainleve)
  | "KruskalSzekeres"           => some (MetricTensor.kruskalSzekeres)
  | "Kerr"                      => some (MetricTensor.kerr)
  | "ReissnerNordstrom"         => some (MetricTensor.reissnerNordstrom)
  | "KerrNewman"                => some (MetricTensor.kerrNewman)
  | "Godel"                     => some (MetricTensor.godel)
  | "FLRW"                      => some (MetricTensor.flrw)
  | _                           => none

-- ---------------------------------------------------------------------------
-- Utility: list all supported named metrics (mirrors WL's `MetricTensor[]`)
-- ---------------------------------------------------------------------------

def MetricTensor.allNames : List String :=
  ["Symmetric", "SymmetricField", "Asymmetric", "AsymmetricField",
   "Euclidean", "Minkowski", "Schwarzschild", "IsotropicSchwarzschild",
   "EddingtonFinkelstein", "IngoingEddingtonFinkelstein",
   "OutgoingEddingtonFinkelstein", "GullstrandPainleve",
   "IngoingGullstrandPainleve", "OutgoingGullstrandPainleve",
   "KruskalSzekeres", "Kerr", "ReissnerNordstrom", "KerrNewman",
   "Godel", "FLRW"]

-- ---------------------------------------------------------------------------
-- Index raising / lowering for the metric itself
-- ---------------------------------------------------------------------------

/-- Return the purely covariant (g_{μν}) matrix regardless of stored index position. -/
def MetricTensor.covariantMatrix (g : MetricTensor) : Mat :=
  match g.idx1, g.idx2 with
  | true, true   => g.matrix
  | false, false => matInv g.matrix |>.getD g.matrix
  | true, false  =>
      -- g.matrix = g^ν_μ = δ^ν_μ for symmetric metric; recover gCov = g * gInv^{-1}
      -- In general: gCov_{ij} = Σ_k gMatrix_{ik} * gInv_{kj}^{-1} … but this is
      -- circular. Store as-is and note this is the mixed matrix.
      g.matrix
  | false, true  => g.matrix

/-- Return the inverse metric matrix g^{μν}. -/
def MetricTensor.inverseMatrix (g : MetricTensor) : Mat :=
  match g.idx1, g.idx2 with
  | false, false => g.matrix
  | true, true   => matInv g.matrix |>.getD g.matrix
  | _, _         => matInv (g.covariantMatrix) |>.getD g.matrix

/-- Re-index the metric to new index positions. -/
def MetricTensor.reindex (g : MetricTensor) (idx1 idx2 : IndexKind) : MetricTensor :=
  MetricTensor.fromCovariant (g.covariantMatrix) g.coords idx1 idx2

end Gravitas
