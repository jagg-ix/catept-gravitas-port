# catept-gravitas-port

**Private** sibling repo of [`jagg-ix/catept-main`](https://github.com/jagg-ix/catept-main).
Class C standalone physics-port sibling — Lean 4 port of the Wolfram
Mathematica Gravitas symbolic general-relativity package.

## What this provides

Symbolic GR primitives (metric tensor, Christoffel symbols, Riemann/Ricci/
Weyl/Schouten/Bach tensors, Einstein tensor, electromagnetic and
electrogravitic tensors, ADM decomposition, hypersurface geometry) plus
Einstein-equation solvers.

```lean
import CATEPTGravitasPort
```

| Module category | Modules |
|---|---|
| Foundations | `Basic`, `MetricTensor` |
| Connection / curvature | `ChristoffelSymbols`, `RiemannTensor`, `RicciTensor`, `WeylTensor`, `SchoutenTensor`, `BachTensor`, `EinsteinTensor` |
| Stress-energy | `StressEnergyTensor`, `ElectromagneticTensor`, `ElectrograviticTensor`, `AngularMomentumTensor`, `AngularMomentumDensityTensor` |
| ADM / hypersurface | `ADMDecomposition`, `ADMStressEnergyDecomposition`, `ExtrinsicCurvatureTensor`, `DiscreteHypersurfaceDecomposition`, `DiscreteHypersurfaceGeodesic` |
| Solvers | `SolveEinsteinEquations`, `SolveVacuumEinsteinEquations`, `SolveElectrovacuumEinsteinEquations`, `SolveADMEquations`, `SolveVacuumADMEquations` |
| History | `GRAVITAS_WORKLOG` |

Total: 25 files / 4,032 LoC.

## Namespace convention

Files declare bare top-level namespaces (e.g. `namespace ADMDecomposition`,
`namespace EinsteinTensor`) preserved verbatim from the upstream Mathematica
port. They are NOT under `CATEPTGravitasPort.*`. The `CATEPTGravitasPort`
prefix exists only at the **module path** level, not at the namespace level.
Catept-main consumers therefore use bare-namespace identifiers (e.g.
`EinsteinTensor.solve`) regardless of which path the file lives at.

## Dependencies

| Pin | Version |
|---|---|
| Lean toolchain | `leanprover/lean4:v4.29.0` |
| Mathlib | `v4.29.0` |

No `catept-plugin-afp-framework` dependency — this port uses only Mathlib.

## Re-import contract

In `catept-main`, consumed via re-export shims under the original module
path `CATEPTMain.Gravitas.*`. Each shim is a 1-line `import` of the
corresponding sibling module — bare namespaces propagate transparently.

## Build locally

```bash
lake exe cache get
lake build
```

## License

MIT, matching `catept-main`.
