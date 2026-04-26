import Lake
open Lake DSL

package «catept-gravitas-port» where
  leanOptions := #[]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.0"

@[default_target]
lean_lib «CATEPTGravitasPort» where
  -- All 25 files live under CATEPTGravitasPort/ but declare bare namespaces
  -- (ADMDecomposition, EinsteinTensor, RicciTensor, …) per the upstream
  -- Wolfram Gravitas port convention.
