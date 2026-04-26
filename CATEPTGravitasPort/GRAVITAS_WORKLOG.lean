/-!
# GRAVITAS_WORKLOG — Lean4 port of Wolfram Gravitas (Jonathan Gorard, 2020)

WL source: `/Users/macbookpro/lab/tau/Gravitas/Gravitas/Kernel/`
Lean4 root: `CATEPTMain/Gravitas/`
Branch: `private/catept-afp-leverage-20260413`
Phase 1 committed: `957674189` (2026-04-14)
Phase 2 committed: `2a56782a6` (2026-04-14) — fidelity inspection, 4 bugs fixed
Phase 3 committed: `0dad194c7` (2026-04-14) — Lean 4.29.0 compat, build gate lifted

---

## Phase 1 — Status (complete)

All 24 files written and committed. No `sorry` entries. Symbolic ops
via `partial` functions (`simplify`, `symDiff`, `exprSubst`). 20 named
metrics.

---

## Phase 2 — Fidelity inspection (complete)

All 24 modules inspected side-by-side against WL source. 4 bugs fixed:

| File | Bug | Fix |
|------|-----|-----|
| `Basic.lean` | `q` helper coercion: `Rat` constructor wasn't lifted to `Expr.lit` | `.div (.lit num) (.lit den)` |
| `MetricTensor.lean` | Gödel metric `ex` exponent was `2*sqrt2` not `sqrt2` | corrected to `sqrt2`; dead `factor` binding removed |
| `StressEnergyTensor.lean` | `lowerBoth` not applied to perfectFluid/dust/radiation/EM field | `lowerBoth` wired in |
| `SolveADMEquations.lean` | Hamiltonian constraint sign: `R3 - K² + kSq` (wrong) | `R3 + K² - kSq` |

All 20 other files verified clean.

---

## Phase 3 — Lean 4.29.0 compat + build gate (complete)

Build gate lifted: `lake build CATEPTMain.Gravitas` → **26/26 ✔, 0 errors**.

Compat fixes applied across 14 files:

| Pattern | Files affected |
|---------|---------------|
| `Array.get!`/`get?` → `arr[i]!`/`arr[i]?` | 7 |
| `Array.mkArray` → `Array.replicate` | 4 |
| `Array.ofFn` missing `(n :=)` annotation | 3 |
| `let mut`/`while` outside `do` → `Id.run do` | 1 (DiscreteHypersurfaceGeodesic) |
| Combined struct fields `idx1 idx2 : T` → split | 5 (Ricci/Einstein/Electrogravitic/Schouten/Bach/Weyl) |
| `λ_` variable name → `lam` (λ is Lean keyword) | 3 (RicciTensor, SolveADMEquations ×2) |
| `partial` variable name → `partialDeriv` | 1 (BachTensor) |
| Private def names colliding with struct fields | 1 (SolveADMEquations: 3 helpers → `compute*`) |
| `| _ =>` on `Bool×Bool` match → `| _, _ =>` | 1 (SolveEinsteinEquations) |
| Missing type annotation for `.var`/`.lit` | 1 (SolveEinsteinEquations: `π : Expr`) |
| 3/4-index Weyl raise: malformed `.mul` nesting | 1 (WeylTensor: all 5 raise cases) |

---

## Phase 4 — Post-build fidelity fixes (2026-04-14)

### BrillLindquist fidelity rewrite

WL source (`ADMDecomposition.wl`) uses:
- Spherical coordinates (r, θ, φ), not Cartesian
- Single mass M with separation z₀ (black holes at ±z₀ on the z-axis)
- ψ = 1 + (M/2)(1/r₁ + 1/r₂), r₁ = √(r²sin²θ + (r·cosθ−z₀)²)
- Spatial metric ψ⁴ diag(1, r², r²sin²θ) — spherical conformal flat
- Lapse: symbolic α function (not 1/ψ)

Prior Lean port had: Cartesian coords, two separate masses M1/M2, only M1/(2r1), ψ⁴·δ flat metric, 1/ψ lapse. Rewritten to match WL exactly.

### Dead code removal

`SolveEinsteinEquations.lean`: removed unused `let π := .var "π"` — the 8πG coefficient is constructed inside `EinsteinTensor.fieldEquations`, not here.

---

## Phase 2 — Per-module fidelity inspection plan

**Goal**: For each file, verify:
  1. **Formula fidelity** — every WL definition maps 1:1 to its Lean counterpart
  2. **Idiomatic Lean4** — use `match`, `where`, `let`, `Array.map`/`foldl` etc. correctly
  3. **Mathlib leverage** — identify any standard algebraic/analysis theorems available
     in Mathlib or the CATEPT repo that can strengthen definitions or proofs

**Inspection order** (dependency-first):

### Tier 0 — Infrastructure (no WL equiv)
| # | File | Worklog code | Key checks |
|---|------|-------------|-----------|
| 0 | `Basic.lean` | `catept_gravitas_basic_fidelity_20260414` | `Expr` constructors match all WL symbolic ops; `simplify` covers WL's `FullSimplify` patterns; `symDiff` covers `D[...]` for all `Expr` constructors; `matInv` uses correct Gauss-Jordan pivot selection |

### Tier 1 — Metric (all others depend on this)
| # | File | Worklog code | Key checks |
|---|------|-------------|-----------|
| 1 | `MetricTensor.lean` | `catept_gravitas_metric_fidelity_20260414` | `fromCovariant` signature; `inverseMatrix` calls `Basic.matInv`; all 20 named metric formulas match WL `MetricTensor` exactly (Schwarzschild: `diag[-c²(1-rs/r), (1-rs/r)⁻¹, r², r²sin²θ]`; Kerr off-diag components; FLRW scale factor; Gödel rotation; etc.); `reindex` raises/lowers with correct contraction |

### Tier 2 — First-derivative tensors (depend on MetricTensor + Christoffel)
| # | File | Worklog code | Key checks |
|---|------|-------------|-----------|
| 2 | `ChristoffelSymbols.lean` | `catept_gravitas_christoffel_fidelity_20260414` | `computeMixed`: Γ^λ_{μν} = ½ g^{λρ}(∂_μ g_{νρ} + ∂_ν g_{μρ} − ∂_ρ g_{μν}); index symmetry μ↔ν enforced or noted; `symDiff` called with correct coord variable |
| 3 | `RiemannTensor.lean` | `catept_gravitas_riemann_fidelity_20260414` | R^ρ_{σμν} = ∂_μΓ^ρ_{νσ} − ∂_νΓ^ρ_{μσ} + Γ^ρ_{μλ}Γ^λ_{νσ} − Γ^ρ_{νλ}Γ^λ_{μσ}; all 4 index slots correct; contraction works |
| 4 | `RicciTensor.lean` | `catept_gravitas_ricci_fidelity_20260414` | R_{μν} = R^ρ_{μρν} (trace on first+third); scalar R = g^{μν}R_{μν} |
| 5 | `EinsteinTensor.lean` | `catept_gravitas_einstein_fidelity_20260414` | G_{μν} = R_{μν} − ½ g_{μν} R; cosmological constant variant Λg_{μν} |

### Tier 3 — Conformal tensors (depend on Riemann/Ricci/Einstein)
| # | File | Worklog code | Key checks |
|---|------|-------------|-----------|
| 6 | `WeylTensor.lean` | `catept_gravitas_weyl_fidelity_20260414` | C_{ρσμν} = R_{ρσμν} − (g_{ρ[μ}R_{ν]σ} − g_{σ[μ}R_{ν]ρ}) + R/(n-1)(n-2) g_{ρ[μ}g_{ν]σ}; correct for n=4 |
| 7 | `SchoutenTensor.lean` | `catept_gravitas_schouten_fidelity_20260414` | P_{μν} = 1/(n-2)(R_{μν} − R g_{μν}/(2(n-1))); n=4 gives P=½R_{μν} − R g_{μν}/12 |
| 8 | `BachTensor.lean` | `catept_gravitas_bach_fidelity_20260414` | B_{μν} = ∇^ρ∇^σ C_{ρμσν} + ½ R^{ρσ}C_{ρμσν}; 4D only; check covariant derivative term |

### Tier 4 — Field tensors
| # | File | Worklog code | Key checks |
|---|------|-------------|-----------|
| 9 | `ElectrograviticTensor.lean` | `catept_gravitas_electrogravitic_fidelity_20260414` | E_{μν} = C_{μαν}^α u^α u^β (tidal); observer 4-velocity u present |
| 10 | `StressEnergyTensor.lean` | `catept_gravitas_stressenergy_fidelity_20260414` | Perfect fluid T_{μν} = (ρ+p)u_μu_ν + p g_{μν}; Maxwell T_{μν} = F_{μα}F_ν^α − ¼g_{μν}F_{αβ}F^{αβ} |
| 11 | `ElectromagneticTensor.lean` | `catept_gravitas_electromagnetic_fidelity_20260414` | F_{μν} skew; Hodge dual *F; Bianchi identity codified |
| 12 | `AngularMomentumTensor.lean` | `catept_gravitas_angmom_fidelity_20260414` | J^{μν} = x^μ p^ν − x^ν p^μ |
| 13 | `AngularMomentumDensityTensor.lean` | `catept_gravitas_angmomdensity_fidelity_20260414` | j^{μνρ} = x^μ T^{νρ} − x^ν T^{μρ} |

### Tier 5 — ADM decomposition
| # | File | Worklog code | Key checks |
|---|------|-------------|-----------|
| 14 | `ADMDecomposition.lean` | `catept_gravitas_adm_fidelity_20260414` | `lapse`, `shift`, `spatialMetric` extraction; `spacetimeMetric` reconstruction: ds²=−α²dt²+γ_{ij}(dx^i+β^i dt)(dx^j+β^j dt); all 7 named slicings |
| 15 | `ExtrinsicCurvatureTensor.lean` | `catept_gravitas_extrinsic_fidelity_20260414` | K_{ij} = −1/(2α)(∂_t γ_{ij} − ∇_i β_j − ∇_j β_i) |
| 16 | `ADMStressEnergyDecomposition.lean` | `catept_gravitas_admstress_fidelity_20260414` | ρ_ADM = n^μ n^ν T_{μν}; J_i = −γ_i^μ n^ν T_{μν}; S_{ij} = γ_i^μ γ_j^ν T_{μν} |

### Tier 6 — Discrete hypersurface
| # | File | Worklog code | Key checks |
|---|------|-------------|-----------|
| 17 | `DiscreteHypersurfaceDecomposition.lean` | `catept_gravitas_dhdecomp_fidelity_20260414` | Causal graph foliation; matches WL `DiscreteHypersurfaceDecomposition` API |
| 18 | `DiscreteHypersurfaceGeodesic.lean` | `catept_gravitas_dhgeodesic_fidelity_20260414` | Geodesic equation on discrete hypersurface; `symDiff` used for connection |

### Tier 7 — Solvers (depend on all above)
| # | File | Worklog code | Key checks |
|---|------|-------------|-----------|
| 19 | `SolveEinsteinEquations.lean` | `catept_gravitas_solveeq_fidelity_20260414` | G_{μν} + Λg_{μν} = 8πT_{μν} residual; `solveFor` pattern matches WL `SolveEinsteinEquations` |
| 20 | `SolveVacuumEinsteinEquations.lean` | `catept_gravitas_solvevac_fidelity_20260414` | G_{μν}=0 (or R_{μν}=0); vacuum selector |
| 21 | `SolveElectrovacuumEinsteinEquations.lean` | `catept_gravitas_solveelec_fidelity_20260414` | EFE+Maxwell coupled system |
| 22 | `SolveADMEquations.lean` | `catept_gravitas_solveadm_fidelity_20260414` | Hamiltonian+momentum constraints + evolution eqs |
| 23 | `SolveVacuumADMEquations.lean` | `catept_gravitas_solvevacadm_fidelity_20260414` | Vacuum ADM (T=0 sector) |

---

## Inspection checklist (per file)

For each file, the inspector should:

```
[ ] 1. Read WL source side-by-side with Lean4 file
[ ] 2. Verify every exported function/definition exists with matching semantics
[ ] 3. Check all formula indices (covariant/contravariant) are correct
[ ] 4. Check coord variable names match WL convention ({t,r,θ,φ} etc.)
[ ] 5. Verify `partial` tag only where truly needed (mutual recursion / no termination proof)
[ ] 6. Check `Array` operations are off-by-zero safe (WL is 1-indexed, Lean is 0-indexed)
[ ] 7. Identify any Mathlib theorem that could strengthen a definition
       (e.g. `Matrix.det`, `LinearMap`, `InnerProductSpace` for metric positivity)
[ ] 8. Record any fidelity gap or improvement as a worklog note
[ ] 9. Mark worklog task done after inspection passes
```

---

## Known design decisions

- **`partial` for `simplify`/`symDiff`**: Lean4 cannot prove termination for
  structurally recursive CAS operations on `Expr`. `partial` is intentional.
  These match WL's `FullSimplify` / `D` semantics.

- **`Mat = Array (Array Expr)`**: 0-indexed, row-major. All WL 1-indexed
  accesses are offset by -1 in `matGet`/`matBuild`.

- **`IndexKind = Bool`**: `true` = covariant (lower index), `false` = contravariant
  (upper index) — exact Boolean encoding of WL `True`/`False` index flags.

- **`matInv` via Gauss-Jordan**: WL uses `Inverse[]`. Our implementation is
  symbolic Gauss-Jordan over `Expr`. Works for symbolic sparse matrices.
  Dense numeric inversion deferred to later phase.

- **No Mathlib `Matrix` wrapping (yet)**: `Mat` is `Array (Array Expr)`, not
  `Matrix n n Expr`. Bridging to `Mathlib.Matrix` is a future stretch goal.

---

## Stretch goals (future phases)

| Goal | Notes |
|------|-------|
| Bridge `Mat` → `Mathlib.Matrix n n Expr` | Enables Mathlib linear-algebra theorems (det, trace, eigenvalues) |
| `matInv` → `Mathlib.Matrix.inv` | Current: symbolic Gauss-Jordan; Mathlib has `nonsing_inv` |
| Metric positivity axiom | `MetricTensor` has no `isNonDegenerate : Bool`; adding it enables downstream topology |
| BrillLindquist: lapse from conformal factor | Current lapse is symbolic α; WL also symbolic — optionally use `ψ⁻¹` for maximal slicing |
| Numerical evaluation mode | `Expr.eval : HashMap String Float → Float` for concrete metric computations |
| Formal proof of Bianchi identity | `∇^μ G_{μν} = 0` provable from the symbolic `symDiff` algebra via `sorry`-free lemma |
-/
