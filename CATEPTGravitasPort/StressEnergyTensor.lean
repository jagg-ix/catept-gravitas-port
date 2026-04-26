import CATEPTGravitasPort.Basic
import CATEPTGravitasPort.MetricTensor

/-!
# Gravitas.StressEnergyTensor

Port of `Gravitas/Kernel/StressEnergyTensor.wl`.

Stress-energy tensor T_{μν} for various matter models:
- Generic symmetric / asymmetric (parametric)
- Perfect fluid:    T^{μν} = (ρ+P) u^μ u^ν + P g^{μν}
- Dust:             T^{μν} = ρ u^μ u^ν
- Radiation:        T^{μν} = (ρ/3)(4 u^μ u^ν + g^{μν})
- Electromagnetic:  T^{μν} = (1/μ₀)[F^{μα} F^ν_α - (1/4) g^{μν} F_{αβ} F^{αβ}]
- Massive scalar field: T_{μν} = ∇_μ φ ∇_ν φ - (1/2) g_{μν}[(∇φ)² + m²φ²]
-/

namespace Gravitas

-- ---------------------------------------------------------------------------
-- Core structure
-- ---------------------------------------------------------------------------

structure StressEnergyTensor where
  metric     : MetricTensor
  components : Mat
  idx1 : IndexKind
  idx2 : IndexKind
  deriving Repr

namespace StressEnergyTensor

-- ---------------------------------------------------------------------------
-- Generic helpers
-- ---------------------------------------------------------------------------

private def toIndexed (gCov gInv tcov : Mat) (idx1 idx2 : IndexKind) : Mat :=
  let n := gCov.size
  match idx1, idx2 with
  | true,  true  => tcov
  | false, false =>
      matBuild n (fun i j =>
        sumN n (fun k => sumN n (fun l =>
          simplify (.mul (.mul (matGet gInv i k) (matGet gInv j l)) (matGet tcov k l)))))
  | true,  false =>
      matBuild n (fun i j =>
        sumN n (fun k => simplify (.mul (matGet gInv k j) (matGet tcov i k))))
  | false, true  =>
      matBuild n (fun i j =>
        sumN n (fun k => simplify (.mul (matGet gInv i k) (matGet tcov k j))))

/-- Lower a contravariant T^{μν} to covariant T_{μν} = g_{μα} g_{νβ} T^{αβ}. -/
private def lowerBoth (gCov tCon : Mat) : Mat :=
  let n := gCov.size
  matBuild n (fun μ ν =>
    sumN n (fun α => sumN n (fun β =>
      simplify (.mul (.mul (matGet gCov μ α) (matGet gCov ν β)) (matGet tCon α β)))))

/-- All named matter models. -/
def allNames : List String :=
  ["Symmetric", "SymmetricField", "Asymmetric", "AsymmetricField",
   "PerfectFluid", "PerfectFluidField", "Dust", "DustField",
   "Radiation", "RadiationField", "ElectromagneticField", "MassiveScalarField"]

-- ---------------------------------------------------------------------------
-- Generic parametric tensors
-- ---------------------------------------------------------------------------

/-- Symmetric stress-energy with components T^{(ij)} = T^{(ji)}. -/
def symmetric (g : MetricTensor) (idx1 idx2 : IndexKind := con) : StressEnergyTensor :=
  let n := g.dim
  let tCon := matBuild n (fun i j =>
    let ij := if i ≤ j then (i,j) else (j,i)
    .var s!"T{ij.1}{ij.2}")
  let gCov := g.covariantMatrix
  let gInv := g.inverseMatrix
  { metric := g, components := toIndexed gCov gInv (lowerBoth gCov tCon) idx1 idx2, idx1, idx2 }

def asymmetric (g : MetricTensor) (idx1 idx2 : IndexKind := con) : StressEnergyTensor :=
  let n := g.dim
  let tCon := matBuild n (fun i j => .var s!"T{i}{j}")
  let gCov := g.covariantMatrix
  let gInv := g.inverseMatrix
  { metric := g, components := toIndexed gCov gInv (lowerBoth gCov tCon) idx1 idx2, idx1, idx2 }

-- ---------------------------------------------------------------------------
-- Perfect Fluid:  T^{μν} = (ρ+P) u^μ u^ν + P g^{μν}
-- ---------------------------------------------------------------------------

/-- Perfect fluid stress-energy tensor.
    `ρ`: energy density, `P`: pressure, `u`: 4-velocity (contravariant). -/
def perfectFluid (g : MetricTensor) (ρ P : Expr) (u : Array Expr)
    (idx1 idx2 : IndexKind := co) : StressEnergyTensor :=
  let n    := g.dim
  let gCov := g.covariantMatrix
  let gInv := g.inverseMatrix
  -- T^{μν} = (ρ+P) u^μ u^ν + P g^{μν}
  let tCon := matBuild n (fun μ ν =>
    simplify (.add (.mul (.add ρ P) (.mul (u[μ]!) (u[ν]!)))
                   (.mul P (matGet gInv μ ν))))
  let comps := toIndexed gCov gInv (lowerBoth gCov tCon) idx1 idx2
  { metric := g, components := comps, idx1, idx2 }

/-- Default perfect fluid with symbolic variables. -/
def perfectFluidSymbolic (g : MetricTensor)
    (idx1 idx2 : IndexKind := co) : StressEnergyTensor :=
  let n := g.dim
  let ρ := .var "ρ"
  let P := .var "P"
  let u := Array.ofFn (n := n) (fun i : Fin n => .var s!"u{i.val}")
  perfectFluid g ρ P u idx1 idx2

-- ---------------------------------------------------------------------------
-- Dust:  T^{μν} = ρ u^μ u^ν
-- ---------------------------------------------------------------------------

def dust (g : MetricTensor) (ρ : Expr) (u : Array Expr)
    (idx1 idx2 : IndexKind := co) : StressEnergyTensor :=
  let n    := g.dim
  let gCov := g.covariantMatrix
  let gInv := g.inverseMatrix
  let tCon := matBuild n (fun μ ν =>
    simplify (.mul ρ (.mul (u[μ]!) (u[ν]!))))
  let comps := toIndexed gCov gInv (lowerBoth gCov tCon) idx1 idx2
  { metric := g, components := comps, idx1, idx2 }

def dustSymbolic (g : MetricTensor) (idx1 idx2 : IndexKind := co) : StressEnergyTensor :=
  let n := g.dim
  dust g (.var "ρ") (Array.ofFn (n := n) (fun i : Fin n => .var s!"u{i.val}")) idx1 idx2

-- ---------------------------------------------------------------------------
-- Radiation:  T^{μν} = (ρ/3)(4 u^μ u^ν + g^{μν})
-- ---------------------------------------------------------------------------

def radiation (g : MetricTensor) (ρ : Expr) (u : Array Expr)
    (idx1 idx2 : IndexKind := co) : StressEnergyTensor :=
  let n    := g.dim
  let gCov := g.covariantMatrix
  let gInv := g.inverseMatrix
  let tCon := matBuild n (fun μ ν =>
    simplify (.mul (.div ρ (.lit 3))
                   (.add (.mul (.lit 4) (.mul (u[μ]!) (u[ν]!)))
                         (matGet gInv μ ν))))
  let comps := toIndexed gCov gInv (lowerBoth gCov tCon) idx1 idx2
  { metric := g, components := comps, idx1, idx2 }

def radiationSymbolic (g : MetricTensor) (idx1 idx2 : IndexKind := co) : StressEnergyTensor :=
  let n := g.dim
  radiation g (.var "ρ") (Array.ofFn (n := n) (fun i : Fin n => .var s!"u{i.val}")) idx1 idx2

-- ---------------------------------------------------------------------------
-- Electromagnetic field:
-- T^{μν} = (1/μ₀)[F^{μα}F^ν_α - (1/4) g^{μν} F_{αβ}F^{αβ}]
-- ---------------------------------------------------------------------------

/-- Build T_{μν} from the Faraday tensor F_{μν} (covariant form) and μ₀. -/
def electromagneticField (g : MetricTensor) (F : Mat) (μ₀ : Expr)
    (idx1 idx2 : IndexKind := co) : StressEnergyTensor :=
  let n    := g.dim
  let gCov := g.covariantMatrix
  let gInv := g.inverseMatrix
  -- Raise indices: F^{μν} = g^{μα} g^{νβ} F_{αβ}
  let fUp := matBuild n (fun μ ν =>
    sumN n (fun α => sumN n (fun β =>
      simplify (.mul (.mul (matGet gInv μ α) (matGet gInv ν β)) (matGet F α β)))))
  -- F^{μα} F^ν_α = F^{μα} g_{αβ} F^{νβ}
  -- T^{μν} = (1/μ₀)[F^{μα} F_{α}^{ν} - (1/4) g^{μν} F_{αβ}F^{αβ}]
  let fSq := sumN n (fun α => sumN n (fun β =>
    simplify (.mul (matGet F α β) (matGet fUp α β))))
  let tCon := matBuild n (fun μ ν =>
    let term1 := sumN n (fun α =>
      simplify (.mul (matGet fUp μ α)
                     (sumN n (fun β => simplify (.mul (matGet gCov α β) (matGet fUp ν β))))))
    simplify (.mul (.div (.lit 1) μ₀)
                   (.sub term1 (.mul (.mul (.lit (1/4)) (matGet gInv μ ν)) fSq))))
  let comps := toIndexed gCov gInv (lowerBoth gCov tCon) idx1 idx2
  { metric := g, components := comps, idx1, idx2 }

-- ---------------------------------------------------------------------------
-- Massive scalar field:
-- T_{μν} = ∂_μ φ ∂_ν φ - (1/2) g_{μν} [(∂φ)² + m²φ²]
-- ---------------------------------------------------------------------------

/-- Massive scalar field stress-energy.
    `φ`: scalar field (function of coordinates), `m`: mass. -/
def massiveScalarField (g : MetricTensor) (φ m : Expr)
    (idx1 idx2 : IndexKind := co) : StressEnergyTensor :=
  let n      := g.dim
  let gCov   := g.covariantMatrix
  let gInv   := g.inverseMatrix
  let coords := g.coords
  -- ∂_μ φ
  let dφ := Array.ofFn (n := n) (fun μ : Fin n => symDiff φ (coords[μ.val]!))
  -- (∂φ)² = g^{μν} ∂_μ φ ∂_ν φ
  let gradSq := sumN n (fun μ => sumN n (fun ν =>
    simplify (.mul (.mul (matGet gInv μ ν) (dφ[μ]!)) (dφ[ν]!))))
  let kinTerm := simplify (.add gradSq (.mul (.mul m m) (.mul φ φ)))
  let tcov := matBuild n (fun μ ν =>
    simplify (.sub (.mul (dφ[μ]!) (dφ[ν]!))
                   (.mul (.mul (.lit (1/2)) (matGet gCov μ ν)) kinTerm)))
  let comps := toIndexed gCov gInv tcov idx1 idx2
  { metric := g, components := comps, idx1, idx2 }

-- ---------------------------------------------------------------------------
-- Named dispatch
-- ---------------------------------------------------------------------------

/-- Construct a StressEnergyTensor by name (symbolic default matter). -/
def named (name : String) (g : MetricTensor)
    (idx1 idx2 : IndexKind := co) : Option StressEnergyTensor :=
  match name with
  | "Symmetric"         => some (symmetric g idx1 idx2)
  | "Asymmetric"        => some (asymmetric g idx1 idx2)
  | "SymmetricField"    => some (symmetric g idx1 idx2)
  | "AsymmetricField"   => some (asymmetric g idx1 idx2)
  | "PerfectFluid"      => some (perfectFluidSymbolic g idx1 idx2)
  | "PerfectFluidField" => some (perfectFluidSymbolic g idx1 idx2)
  | "Dust"              => some (dustSymbolic g idx1 idx2)
  | "DustField"         => some (dustSymbolic g idx1 idx2)
  | "Radiation"         => some (radiationSymbolic g idx1 idx2)
  | "RadiationField"    => some (radiationSymbolic g idx1 idx2)
  | "MassiveScalarField"=>
      some (massiveScalarField g (.var "φ") (.var "m") idx1 idx2)
  | "ElectromagneticField" =>
      -- Symbolic F_{μν} with default potential A^μ; μ₀ = 1
      let n := g.dim
      let F := matBuild n (fun i j => .var s!"F{i}{j}")
      some (electromagneticField g F (.lit 1) idx1 idx2)
  | _                   => none

end StressEnergyTensor

end Gravitas
