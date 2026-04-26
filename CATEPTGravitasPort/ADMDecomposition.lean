import CATEPTGravitasPort.Basic
import CATEPTGravitasPort.MetricTensor

/-!
# Gravitas.ADMDecomposition

Port of `Gravitas/Kernel/ADMDecomposition.wl`.

ADM (Arnowitt-Deser-Misner) 3+1 decomposition of a 4D spacetime metric.

Given:
- spatial metric γ_{ij}  (n-1 × n-1)
- lapse function α
- shift vector β^i  (n-1 components)

The spacetime metric is reconstructed as:

  g_{tt}   = β_i β^i - α²
  g_{ti}   = β_i
  g_{ij}   = γ_{ij}

where β_i = γ_{ij} β^j.

Named slicings: Minkowski, Schwarzschild, Kerr, Reissner-Nordström, Kerr-Newman,
Brill-Lindquist, FLRW (matching WL's `ADMDecomposition[]` list).
-/

namespace Gravitas

-- ---------------------------------------------------------------------------
-- Core structure
-- ---------------------------------------------------------------------------

/-- ADM decomposition data: spatial metric, time coordinate, lapse, shift. -/
structure ADMDecomposition where
  /-- Spatial (n-1 dimensional) metric. -/
  spatialMetric    : MetricTensor
  /-- Time coordinate label. -/
  timeCoordinate   : String
  /-- Lapse function α (scalar Expr, may depend on all coordinates). -/
  lapseFunction    : Expr
  /-- Shift vector β^i (n-1 components, contravariant). -/
  shiftVector      : Array Expr
  deriving Repr

namespace ADMDecomposition

-- ---------------------------------------------------------------------------
-- Spacetime metric reconstruction
-- ---------------------------------------------------------------------------

/-- Reconstruct the full n×n spacetime metric g_{μν} from ADM data. -/
def spacetimeMetric (adm : ADMDecomposition) : MetricTensor :=
  let γ    := adm.spatialMetric.covariantMatrix
  let n3   := adm.spatialMetric.dim            -- spatial dim (n-1 for 4D)
  let n    := n3 + 1
  let α    := adm.lapseFunction
  let β    := adm.shiftVector
  -- β_i = γ_{ij} β^j
  let βCov := Array.ofFn (n := n3) (fun i : Fin n3 =>
    sumN n3 (fun j => simplify (.mul (matGet γ i.val j) (β[j]!))))
  -- β_i β^i = Σ_i β_i β^i
  let βNormSq := sumN n3 (fun i => simplify (.mul (βCov[i]!) (β[i]!)))
  -- Build (n+1)×(n+1) spacetime metric
  let gCov := matBuild n (fun μ ν =>
    match μ, ν with
    | 0, 0 => simplify (.sub βNormSq (.mul α α))   -- g_{tt} = β²-α²
    | 0, j => if j > 0 then βCov[(j-1)]! else .lit 0  -- g_{ti} = β_i
    | i, 0 => if i > 0 then βCov[(i-1)]! else .lit 0  -- g_{it} = β_i
    | i, j => matGet γ (i-1) (j-1))                -- g_{ij} = γ_{ij}
  -- Full coordinate list: [t, x1, ..., xn3]
  let allCoords := #[adm.timeCoordinate] ++ adm.spatialMetric.coords
  MetricTensor.fromCovariant gCov allCoords co co

-- ---------------------------------------------------------------------------
-- Named slicings
-- ---------------------------------------------------------------------------

/-- All supported named ADM slicings. -/
def allNames : List String :=
  ["Minkowski", "Schwarzschild", "Kerr", "ReissnerNordstrom", "KerrNewman",
   "BrillLindquist", "FLRW"]

/-- Minkowski spacetime in ADM form. -/
def minkowski (timeCoord : String := "t") (spatialCoords : Array String := #["x1","x2","x3"])
    (α : Expr := .var "α") (β : Array Expr := #[.var "β1",.var "β2",.var "β3"])
    : ADMDecomposition :=
  let n3 := spatialCoords.size
  let γ  := MetricTensor.euclidean n3 spatialCoords co co
  { spatialMetric := γ, timeCoordinate := timeCoord, lapseFunction := α, shiftVector := β }

/-- Schwarzschild spacetime in ADM form (t-slicing). -/
def schwarzschild (mass : String := "M")
    (timeCoord : String := "t")
    (spatialCoords : Array String := #["r","θ","φ"]) : ADMDecomposition :=
  let r  := spatialCoords[0]!; let θ := spatialCoords[1]!
  let M  := .var mass
  let r_ := .var r
  let f  := .sub (.lit 1) (.div (.mul (.lit 2) M) r_)  -- 1-2M/r
  let γCov := matBuild 3 (fun i j =>
    if i != j then .lit 0
    else match i with
    | 0 => .div (.lit 1) f    -- γ_{rr}
    | 1 => .pow r_ (.lit 2)
    | 2 => .mul (.pow r_ (.lit 2)) (.pow (.sin (.var θ)) (.lit 2))
    | _ => .lit 0)
  let γ := MetricTensor.fromCovariant γCov spatialCoords co co
  let α := .sqrt f                                      -- lapse α = √(1-2M/r)
  let β := List.replicate 3 (.lit 0 : Expr) |>.toArray                    -- zero shift
  { spatialMetric := γ, timeCoordinate := timeCoord, lapseFunction := α, shiftVector := β }

/-- Kerr spacetime in ADM form (Boyer-Lindquist t-slicing). -/
def kerr (mass : String := "M") (angMom : String := "J")
    (timeCoord : String := "t")
    (spatialCoords : Array String := #["r","θ","φ"]) : ADMDecomposition :=
  let r := spatialCoords[0]!; let θ := spatialCoords[1]!; let φ := spatialCoords[2]!
  let M := .var mass; let J := .var angMom
  let a   := .div J M
  let a2  := .pow a (.lit 2)
  let r2  := .pow (.var r) (.lit 2)
  let Sig := .add r2 (.mul a2 (.pow (.cos (.var θ)) (.lit 2)))
  let Δ   := .add (.sub r2 (.mul (.mul (.lit 2) M) (.var r))) a2
  let sinθ2 := .pow (.sin (.var θ)) (.lit 2)
  -- Spatial metric γ_{ij} = {Σ/Δ, Σ, sin²θ(r²+a²+2Ma²r sin²θ/Σ)}
  let γ33 := .mul sinθ2
    (.add (.add r2 a2) (.div (.mul (.mul (.lit 2) M) (.mul (.var r) (.mul a2 sinθ2))) Sig))
  let γCov := matBuild 3 (fun i j =>
    if i != j then .lit 0
    else match i with
    | 0 => .div Sig Δ
    | 1 => Sig
    | 2 => γ33
    | _ => .lit 0)
  let γ := MetricTensor.fromCovariant γCov spatialCoords co co
  -- Lapse: α = √(Σ Δ / (Σ Δ + 2Mr(a²+r²)))  (approximate)
  let α := .sqrt (.div (.mul Sig Δ) (.add (.mul Sig Δ) (.mul (.mul (.lit 2) M) (.mul (.var r) (.add a2 r2)))))
  -- Shift: β^φ = -2Mar/(ΣΔ+2Mr(a²+r²)) * a  (only φ component non-zero)
  let βφ := .div (.mul (.mul (.lit (-2)) M) (.mul (.var r) a))
                 (.add (.mul Sig Δ) (.mul (.mul (.lit 2) M) (.mul (.var r) (.add a2 r2))))
  let β := #[.lit 0, .lit 0, βφ]
  { spatialMetric := γ, timeCoordinate := timeCoord, lapseFunction := α, shiftVector := β }

/-- Reissner-Nordström in ADM form. -/
def reissnerNordstrom (mass : String := "M") (charge : String := "Q")
    (timeCoord : String := "t")
    (spatialCoords : Array String := #["r","θ","φ"]) : ADMDecomposition :=
  let r := spatialCoords[0]!; let θ := spatialCoords[1]!
  let M := .var mass; let Q := .var charge
  let r_ := .var r
  let f := .add (.sub (.lit 1) (.div (.mul (.lit 2) M) r_))
                (.div (.pow Q (.lit 2)) (.pow r_ (.lit 2)))
  let γCov := matBuild 3 (fun i j =>
    if i != j then .lit 0
    else match i with
    | 0 => .div (.lit 1) f
    | 1 => .pow r_ (.lit 2)
    | 2 => .mul (.pow r_ (.lit 2)) (.pow (.sin (.var θ)) (.lit 2))
    | _ => .lit 0)
  let γ := MetricTensor.fromCovariant γCov spatialCoords co co
  { spatialMetric := γ, timeCoordinate := timeCoord,
    lapseFunction := .sqrt f, shiftVector := List.replicate 3 (.lit 0 : Expr) |>.toArray }

/-- Kerr-Newman in ADM form. -/
def kerrNewman (mass : String := "M") (charge : String := "Q") (angMom : String := "J")
    (timeCoord : String := "t")
    (spatialCoords : Array String := #["r","θ","φ"]) : ADMDecomposition :=
  let r := spatialCoords[0]!; let θ := spatialCoords[1]!
  let M := .var mass; let Q := .var charge; let J := .var angMom
  let a := .div J M; let a2 := .pow a (.lit 2); let Q2 := .pow Q (.lit 2)
  let r2 := .pow (.var r) (.lit 2)
  let Sig := .add r2 (.mul a2 (.pow (.cos (.var θ)) (.lit 2)))
  let Δ := .add (.add (.sub r2 (.mul (.mul (.lit 2) M) (.var r))) a2) Q2
  let sinθ2 := .pow (.sin (.var θ)) (.lit 2)
  let γ33 := .mul sinθ2
    (.add (.add r2 a2) (.div (.mul a2 (.mul sinθ2 (.sub (.mul (.mul (.lit 2) M) (.var r)) Q2))) Sig))
  let γCov := matBuild 3 (fun i j =>
    if i != j then .lit 0
    else match i with
    | 0 => .div Sig Δ | 1 => Sig | 2 => γ33 | _ => .lit 0)
  let γ := MetricTensor.fromCovariant γCov spatialCoords co co
  let α := .sqrt (.div (.mul Sig Δ) (.add (.mul Sig Δ) (.mul a2 (.mul sinθ2 (.mul (.mul (.lit 2) M) (.var r))))))
  let βφ := .div (.mul (.neg a) (.sub (.mul (.mul (.lit 2) M) (.var r)) Q2))
                 (.add (.mul Sig Δ) (.mul a2 (.mul sinθ2 (.sub (.mul (.mul (.lit 2) M) (.var r)) Q2))))
  { spatialMetric := γ, timeCoordinate := timeCoord,
    lapseFunction := α, shiftVector := #[.lit 0, .lit 0, βφ] }

/-- Brill-Lindquist (two-black-hole) initial data in ADM form.
    Matches WL `ADMDecomposition["BrillLindquist"]` exactly:
    - Single mass M, two black holes at ±z₀ on the z-axis (spherical coords)
    - ψ = 1 + (M/2)(1/r₁ + 1/r₂), where r₁ = √(r²sin²θ + (r·cosθ−z₀)²),
                                          r₂ = √(r²sin²θ + (r·cosθ+z₀)²)
    - Spatial metric: γ_{ij} = ψ⁴ diag(1, r², r²sin²θ) -/
def brillLindquist (mass : String := "M") (sep : String := "z₀")
    (timeCoord : String := "t")
    (spatialCoords : Array String := #["r","θ","φ"]) : ADMDecomposition :=
  let r  := spatialCoords[0]!; let θ := spatialCoords[1]!
  let M  : Expr := .var mass
  let z0 : Expr := .var sep
  let r_ := .var r; let sinθ := .sin (.var θ); let cosθ := .cos (.var θ)
  let r2sin2 := .mul (.pow r_ (.lit 2)) (.pow sinθ (.lit 2))
  let rcosθ  := .mul r_ cosθ
  let r1 := .sqrt (.add r2sin2 (.pow (.sub rcosθ z0) (.lit 2)))
  let r2 := .sqrt (.add r2sin2 (.pow (.add rcosθ z0) (.lit 2)))
  -- ψ = 1 + (M/2)(1/r₁ + 1/r₂)
  let ψ := .add (.lit 1) (.mul (.div M (.lit 2)) (.add (.div (.lit 1) r1) (.div (.lit 1) r2)))
  let ψ4 := .pow ψ (.lit 4)
  -- γ = ψ⁴ diag(1, r², r²sin²θ)  (spherical conformal flat)
  let γCov := matBuild 3 (fun i j =>
    if i != j then .lit 0
    else match i with
    | 0 => ψ4
    | 1 => .mul (.pow r_ (.lit 2)) ψ4
    | 2 => .mul (.mul (.pow r_ (.lit 2)) (.pow sinθ (.lit 2))) ψ4
    | _ => .lit 0)
  let γ := MetricTensor.fromCovariant γCov spatialCoords co co
  -- Lapse: symbolic α (WL default), zero shift
  let α : Expr := .var s!"α({timeCoord},{r},{θ},{spatialCoords[2]!})"
  { spatialMetric := γ, timeCoordinate := timeCoord,
    lapseFunction := α, shiftVector := List.replicate 3 (.lit 0 : Expr) |>.toArray }

/-- FLRW cosmology in ADM form. -/
def flrw (scaleParam : String := "a") (curvParam : String := "k")
    (timeCoord : String := "t")
    (spatialCoords : Array String := #["r","θ","φ"]) : ADMDecomposition :=
  let r := spatialCoords[0]!; let θ := spatialCoords[1]!
  let a_t := .var s!"{scaleParam}({timeCoord})"
  let k   := .var curvParam
  let r_  := .var r
  let a2  := .pow a_t (.lit 2)
  let γCov := matBuild 3 (fun i j =>
    if i != j then .lit 0
    else match i with
    | 0 => .div a2 (.sub (.lit 1) (.mul k (.pow r_ (.lit 2))))
    | 1 => .mul a2 (.pow r_ (.lit 2))
    | 2 => .mul a2 (.mul (.pow r_ (.lit 2)) (.pow (.sin (.var θ)) (.lit 2)))
    | _ => .lit 0)
  let γ := MetricTensor.fromCovariant γCov spatialCoords co co
  { spatialMetric := γ, timeCoordinate := timeCoord,
    lapseFunction := .lit 1, shiftVector := List.replicate 3 (.lit 0 : Expr) |>.toArray }

/-- Named ADM decomposition dispatch. -/
def named (name : String) : Option ADMDecomposition :=
  match name with
  | "Minkowski"         => some minkowski
  | "Schwarzschild"     => some schwarzschild
  | "Kerr"              => some kerr
  | "ReissnerNordstrom" => some reissnerNordstrom
  | "KerrNewman"        => some kerrNewman
  | "BrillLindquist"    => some brillLindquist
  | "FLRW"              => some flrw
  | _                   => none

end ADMDecomposition
end Gravitas
