import CATEPTGravitasPort.Basic
import CATEPTGravitasPort.MetricTensor
import CATEPTGravitasPort.ChristoffelSymbols
import CATEPTGravitasPort.WeylTensor
import CATEPTGravitasPort.SchoutenTensor

/-!
# Gravitas.BachTensor

Port of `Gravitas/Kernel/BachTensor.wl`.

Bach tensor (obstruction tensor for conformal flatness in 4D):

  B_{μν} = ∇^ρ ∇^σ C_{ρμσν} + (1/2) R^{ρσ} C_{ρμσν}

where C is the Weyl tensor and ∇ is the covariant derivative.

Equivalently (in 4D):

  B_{μν} = ∇^σ ∇^ρ C_{μρνσ} + R^{ρσ} C_{μρνσ}
         = ∇^σ (∇^ρ C_{μρνσ} + (1/2) R_{μρ} δ^ρ_σ …)

AFP semantic-mapping technique: uses Christoffel-corrected first covariant derivative
of the Schouten tensor ∇_k S_{ij}, then contracts twice with g^{αβ} for the
second covariant divergence.  Matches the WL `covariantDerivatives` block exactly:

  ∇_k S_{ij} = ∂_k S_{ij} - Γ^l_{ki} S_{lj} - Γ^l_{kj} S_{il}

  B_{μν} = Σ_{ρσ} S_{ρσ} W^ρ_μ^σ_ν
          + g^{αβ}(∇_β ∇_α S_{μν} - ∇_μ ∇_α S_{νβ})
-/

namespace Gravitas

structure BachTensor where
  metric     : MetricTensor
  components : Mat
  idx1 : IndexKind
  idx2 : IndexKind
  deriving Repr

namespace BachTensor

/-- Compute the mixed Weyl tensor W^ρ_{μ}^{σ}_{ν} =
    g^{ρα} g^{σβ} W_{αμβν}, needed for the Bach tensor formula. -/
private def mixedWeyl (g : MetricTensor) (covWeyl : Array Expr) : Array Expr :=
  let n    := g.dim
  let gInv := g.inverseMatrix
  let getW := fun a b c d => WeylTensor.getComp n covWeyl a b c d
  let base := Array.replicate (n*n*n*n) (.lit 0)
  -- W^ρ_{μ}^{σ}_{ν} = g^{ρα} g^{σβ} W_{αμβν}
  (List.range n).foldl (fun comps ρ =>
    (List.range n).foldl (fun comps μ =>
      (List.range n).foldl (fun comps σ =>
        (List.range n).foldl (fun comps ν =>
          let val := sumN n (fun α => sumN n (fun β =>
            simplify (.mul (.mul (matGet gInv ρ α) (matGet gInv σ β)) (getW α μ β ν))))
          comps.set! (ρ*n*n*n + μ*n*n + σ*n + ν) val
        ) comps
      ) comps
    ) comps
  ) base

/-- Compute the first covariant derivative of the Schouten tensor:
      ∇_k S_{ij} = ∂_k S_{ij} - Γ^l_{ki} S_{lj} - Γ^l_{kj} S_{il}
    Returns a flat n³ array (k, i, j). -/
private def covDerivSchouten (n : Nat) (scov : Mat) (gCov gInv : Mat)
    (coords : Array String) : Array Expr :=
  let Γ3 := ChristoffelSymbols.computeMixed gCov gInv coords
  let getΓ := fun l k m => ChristoffelSymbols.getComp n Γ3 l k m
  (List.range n).foldl (fun comps k =>
    (List.range n).foldl (fun comps i =>
      (List.range n).foldl (fun comps j =>
        let partialDeriv := symDiff (matGet scov i j) (coords[k]!)
        let conn1 := sumN n (fun l => simplify (.mul (getΓ l k i) (matGet scov l j)))
        let conn2 := sumN n (fun l => simplify (.mul (getΓ l k j) (matGet scov i l)))
        let val := simplify (.sub (.sub partialDeriv conn1) conn2)
        comps.set! (k*n*n + i*n + j) val
      ) comps
    ) comps
  ) (Array.replicate (n*n*n) (.lit 0))

/-- Compute Bach tensor B_{μν} using the WL-faithful formula:
      B_{μν} = Σ_{ρσ} S_{ρσ} W^ρ_μ^σ_ν
             + g^{αβ}(∇_β ∇_α S_{μν} - ∇_μ ∇_α S_{νβ})
    where ∇_k S_{ij} is the Christoffel-corrected first covariant derivative
    and the second derivative is ∂_β(∇_α S_{ij}) - Γ corrections (AFP semantic
    mapping: ∂ → ∇ applied to each stage). -/
private def computeCovariant (g : MetricTensor) : Mat :=
  let n      := g.dim
  let gCov   := g.covariantMatrix
  let gInv   := g.inverseMatrix
  let coords := g.coords
  -- Schouten tensor S_{ij} (covariant) and S^{ij} (contravariant)
  let schoutenCov := SchoutenTensor.ofMetric g co co
  let schoutenCon := SchoutenTensor.ofMetric g con con
  let scov := schoutenCov.components
  -- Christoffel symbols for second-derivative corrections
  let Γ3 := ChristoffelSymbols.computeMixed gCov gInv coords
  let getΓ := fun l k m => ChristoffelSymbols.getComp n Γ3 l k m
  -- First covariant derivative: nablaS[k,i,j] = ∇_k S_{ij}
  let nablaSArr := covDerivSchouten n scov gCov gInv coords
  let nablaS := fun k i j => (nablaSArr[k*n*n + i*n + j]?).getD (.lit 0)
  -- Mixed Weyl W^ρ_μ^σ_ν
  let covW  := WeylTensor.computeCovariant g
  let mixWArr := mixedWeyl g covW
  let getMW := fun ρ μ σ ν => (mixWArr[ρ*n*n*n + μ*n*n + σ*n + ν]?).getD (.lit 0)
  -- Second covariant derivative: g^{αβ}(∇_β ∇_α S_{ij})
  -- ∇_β(∇_α S_{ij}) = ∂_β(∇_α S_{ij}) - Γ^γ_{βα} ∇_γ S_{ij}
  --                  - Γ^γ_{βi} ∇_α S_{γj} - Γ^γ_{βj} ∇_α S_{iγ}
  let nabla2S := fun μ ν =>
    sumN n (fun α => sumN n (fun β =>
      let partialDeriv := symDiff (nablaS α μ ν) (coords[β]!)
      let c1 := sumN n (fun γ => simplify (.mul (getΓ γ β α) (nablaS γ μ ν)))
      let c2 := sumN n (fun γ => simplify (.mul (getΓ γ β μ) (nablaS α γ ν)))
      let c3 := sumN n (fun γ => simplify (.mul (getΓ γ β ν) (nablaS α μ γ)))
      simplify (.mul (matGet gInv α β)
                     (.sub (.sub (.sub partialDeriv c1) c2) c3))))
  -- Cross term: g^{αβ} ∇_μ ∇_α S_{νβ}
  let crossTerm := fun μ ν =>
    sumN n (fun α => sumN n (fun β =>
      let partialDeriv := symDiff (nablaS α ν β) (coords[μ]!)
      let c1 := sumN n (fun γ => simplify (.mul (getΓ γ μ α) (nablaS γ ν β)))
      let c2 := sumN n (fun γ => simplify (.mul (getΓ γ μ ν) (nablaS α γ β)))
      let c3 := sumN n (fun γ => simplify (.mul (getΓ γ μ β) (nablaS α ν γ)))
      simplify (.mul (matGet gInv α β)
                     (.sub (.sub (.sub partialDeriv c1) c2) c3))))
  matBuild n (fun μ ν =>
    -- Term 1: Σ_{ρσ} S^{ρσ} W^ρ_μ^σ_ν   (Schouten × mixed Weyl, WL: schoutenTensor * mixedWeylTensor)
    let schoutenWeylTerm :=
      sumN n (fun ρ => sumN n (fun σ =>
        simplify (.mul (matGet schoutenCon.components ρ σ) (getMW ρ μ σ ν))))
    -- Term 2: g^{αβ}(∇_β ∇_α S_{μν} - ∇_μ ∇_α S_{νβ})
    let covDerivTerm := simplify (.sub (nabla2S μ ν) (crossTerm μ ν))
    simplify (.add schoutenWeylTerm covDerivTerm))

private def toIndexed (gCov gInv bcov : Mat) (idx1 idx2 : IndexKind) : Mat :=
  let n := gCov.size
  match idx1, idx2 with
  | true,  true  => bcov
  | false, false =>
      matBuild n (fun i j =>
        sumN n (fun k => sumN n (fun l =>
          simplify (.mul (.mul (matGet gInv i k) (matGet gInv j l)) (matGet bcov k l)))))
  | true,  false =>
      matBuild n (fun i j =>
        sumN n (fun k => simplify (.mul (matGet gInv k j) (matGet bcov i k))))
  | false, true  =>
      matBuild n (fun i j =>
        sumN n (fun k => simplify (.mul (matGet gInv i k) (matGet bcov k j))))

def ofMetric (g : MetricTensor)
    (idx1 : IndexKind := co) (idx2 : IndexKind := co) : BachTensor :=
  let gCov  := g.covariantMatrix
  let gInv  := g.inverseMatrix
  let bcov  := computeCovariant g
  let comps := toIndexed gCov gInv bcov idx1 idx2
  { metric := g, components := comps, idx1, idx2 }

def get (bt : BachTensor) (i j : Nat) : Expr :=
  matGet bt.components i j

end BachTensor
end Gravitas
