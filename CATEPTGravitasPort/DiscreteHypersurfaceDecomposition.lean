import CATEPTGravitasPort.Basic
import CATEPTGravitasPort.MetricTensor

/-!
# Gravitas.DiscreteHypersurfaceDecomposition

Port of `Gravitas/Kernel/DiscreteHypersurfaceDecomposition.wl`.

Discrete approximation of a spacelike hypersurface by a finite vertex set.

Given a spacetime metric and coordinate ranges, this module:
1. Samples the spatial hypersurface at a finite set of `vertexCount` points
2. Computes the induced metric at each vertex
3. Builds a discrete graph encoding the connectivity (adjacency by proximity)

The WL implementation uses `ParametricRegion` + mesh generation; here we port
the algebraic structure (the data returned by the WL computations):
- `vertices`      : list of coordinate tuples (rational samples)
- `inducedMetrics`: list of 3×3 matrices (the pullback γ_{ij} at each vertex)
- `adjacencyList` : list of (vertex, neighbours) pairs
-/

namespace Gravitas

/-- Integer floor square root: largest k with k*k ≤ n. -/
private def natSqrt (n : Nat) : Nat :=
  ((List.range (n + 1)).reverse.find? (fun k => k * k ≤ n)).getD 0

-- ---------------------------------------------------------------------------
-- Coordinate range
-- ---------------------------------------------------------------------------

structure CoordRange where
  coord      : String
  initial    : Rat
  final      : Rat
  deriving Repr

-- ---------------------------------------------------------------------------
-- Discrete hypersurface
-- ---------------------------------------------------------------------------

structure DiscreteHypersurface where
  metric             : MetricTensor
  timeRange          : CoordRange
  spatialRange1      : CoordRange
  spatialRange2      : CoordRange
  vertexCount        : Nat
  discretizationScale : Rat
  /-- Sampled vertices as (t, x1, x2) triples. -/
  vertices           : Array (Rat × Rat × Rat)
  /-- Induced metric (3×3 symbolic matrix) at each vertex. -/
  inducedMetrics     : Array Mat
  /-- Adjacency list (vertex index → list of neighbour indices). -/
  adjacencyList      : Array (Array Nat)
  deriving Repr

namespace DiscreteHypersurface

/-- Sample `n` equally-spaced rational values in [a, b]. -/
private def linspace (a b : Rat) (n : Nat) : Array Rat :=
  if n ≤ 1 then #[a]
  else Array.ofFn (n := n) (fun i : Fin n =>
    a + (b - a) * (i.val : Rat) / ((n - 1 : Nat) : Rat))

/-- Substitute rational values into a metric matrix component. -/
private def evalAt (e : Expr) (coords : Array String) (vals : Array Rat) : Expr :=
  (List.range (min coords.size vals.size)).foldl (fun e i =>
    exprSubstExpr e coords[i]! (.lit vals[i]!)) e

/-- Compute the induced 3-metric at a spatial slice t = t0. -/
private def inducedMetricAt (g : MetricTensor) (tIdx : Nat) (t0 : Rat)
    (spatialCoords : Array String) : Mat :=
  -- The induced metric is the spatial block of g_{μν} with t substituted
  let n3 := g.dim - 1
  matBuild n3 (fun i j =>
    evalAt (matGet g.covariantMatrix (i+1) (j+1)) g.coords
      (g.coords.mapIdx (fun k _ => if k == tIdx then t0 else 0)))

/-- Build a discrete approximation of the hypersurface. -/
def ofMetric (g : MetricTensor)
    (timeRange : CoordRange := { coord := "t", initial := 0, final := 1 })
    (spatialRange1 : CoordRange := { coord := "x1", initial := -2, final := 2 })
    (spatialRange2 : CoordRange := { coord := "x2", initial := -2, final := 2 })
    (vertexCount : Nat := 100)
    (discretizationScale : Rat := 1) : DiscreteHypersurface :=
  let n   := natSqrt vertexCount  -- grid points per dimension (approx)
  let ts  := linspace timeRange.initial timeRange.final n
  let x1s := linspace spatialRange1.initial spatialRange1.final n
  let x2s := linspace spatialRange2.initial spatialRange2.final n
  -- Generate vertices: (t, x1, x2) sample points on the t-slice grid
  let vertices : Array (Rat × Rat × Rat) :=
    (ts.toList.flatMap (fun t =>
      x1s.toList.flatMap (fun x1 =>
        x2s.toList.map (fun x2 => (t, x1, x2))))).toArray.take vertexCount
  -- Induced metrics at each vertex
  let tIdx := g.coords.findIdx? (· == timeRange.coord) |>.getD 0
  let n3   := g.dim - 1
  let inducedMetrics := vertices.map (fun (t0, x1, x2) =>
    -- Substitute values into the spatial block
    let subs := [(timeRange.coord, t0), (spatialRange1.coord, x1), (spatialRange2.coord, x2)]
    let gCov := g.covariantMatrix
    matBuild n3 (fun i j =>
      let e := matGet gCov (i+1) (j+1)
      subs.foldl (fun e (x, v) => exprSubstExpr e x (.lit v)) e))
  -- AFP structural-completeness: proximity-based adjacency on the grid.
  -- Two vertices are adjacent iff they differ in exactly one grid dimension by one step.
  -- Since vertices are generated as (t, x1, x2) with step 1/(n-1) in each dim,
  -- we connect pairs whose Euclidean distance is at most 1.5 * grid spacing.
  let nv := vertices.size
  let gridSpacing : Rat :=
    if n ≤ 1 then 1
    else (spatialRange1.final - spatialRange1.initial) / ((n - 1 : Nat) : Rat)
  let threshold : Rat := gridSpacing * (3 / 2)  -- 1.5 × grid step
  let adjacencyList := Array.ofFn (n := nv) (fun i : Fin nv =>
    -- Find all j ≠ i whose vertex is within threshold distance
    let (ti, xi, yi) := vertices[i.val]!
    (Array.ofFn (n := nv) (fun j : Fin nv => j.val)).filter (fun j =>
      if j == i.val then false
      else
        let (tj, xj, yj) := vertices[j]!
        let dt := ti - tj; let dx := xi - xj; let dy := yi - yj
        -- Rational Euclidean distance squared ≤ threshold²
        dt*dt + dx*dx + dy*dy ≤ threshold * threshold))
  { metric := g, timeRange, spatialRange1, spatialRange2,
    vertexCount, discretizationScale, vertices,
    inducedMetrics, adjacencyList }

/-- Named dispatch. -/
def named (name : String) (vertexCount : Nat := 100) : Option DiscreteHypersurface :=
  MetricTensor.named name |>.map (fun g =>
    ofMetric g (vertexCount := vertexCount))

end DiscreteHypersurface
end Gravitas
