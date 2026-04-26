import CATEPTGravitasPort.Basic
import CATEPTGravitasPort.MetricTensor
import CATEPTGravitasPort.ChristoffelSymbols
import CATEPTGravitasPort.RiemannTensor
import CATEPTGravitasPort.RicciTensor
import CATEPTGravitasPort.WeylTensor
import CATEPTGravitasPort.SchoutenTensor
import CATEPTGravitasPort.BachTensor
import CATEPTGravitasPort.EinsteinTensor
import CATEPTGravitasPort.ElectromagneticTensor
import CATEPTGravitasPort.ElectrograviticTensor
import CATEPTGravitasPort.StressEnergyTensor
import CATEPTGravitasPort.AngularMomentumTensor
import CATEPTGravitasPort.AngularMomentumDensityTensor
import CATEPTGravitasPort.ADMDecomposition
import CATEPTGravitasPort.ADMStressEnergyDecomposition
import CATEPTGravitasPort.ExtrinsicCurvatureTensor
import CATEPTGravitasPort.DiscreteHypersurfaceDecomposition
import CATEPTGravitasPort.DiscreteHypersurfaceGeodesic
import CATEPTGravitasPort.SolveEinsteinEquations
import CATEPTGravitasPort.SolveVacuumEinsteinEquations
import CATEPTGravitasPort.SolveElectrovacuumEinsteinEquations
import CATEPTGravitasPort.SolveADMEquations
import CATEPTGravitasPort.SolveVacuumADMEquations
import CATEPTGravitasPort.GRAVITAS_WORKLOG

/-!
# catept-gravitas-port — umbrella

Lean 4 port of the Wolfram Mathematica Gravitas symbolic general-relativity
package. 25 files / 4032 LoC under bare namespaces (ADMDecomposition,
EinsteinTensor, RicciTensor, etc.) preserved verbatim from the original
port convention.

Class C standalone physics-port sibling of catept-main. Consumers in
catept-main `import CATEPTMain.Gravitas.X` via thin re-export shims that
forward to `CATEPTGravitasPort.X`.
-/
