import CATEPTGravitasPort.Basic
import CATEPTGravitasPort.MetricTensor
import CATEPTGravitasPort.ChristoffelSymbols
import CATEPTGravitasPort.DiscreteHypersurfaceDecomposition

/-!
# Gravitas.DiscreteHypersurfaceGeodesic

Port of `Gravitas/Kernel/DiscreteHypersurfaceGeodesic.wl`.

Geodesic structure on a discrete hypersurface:

Given a `DiscreteHypersurface`, compute:
- The geodesic distance between adjacent vertices using the induced metric
- A discrete geodesic path between two vertex indices (Dijkstra on the graph)
- The discrete parallel transport matrix along a path

The WL implementation uses `FindShortestPath` + numerical integration;
here we port the algebraic/combinatorial structure.
-/

namespace Gravitas

-- ---------------------------------------------------------------------------
-- Edge length
-- ---------------------------------------------------------------------------

/-- Compute the discrete geodesic length of the edge (i, j) using the
    induced metric at vertex i (midpoint approximation). -/
def edgeLength (surf : DiscreteHypersurface) (i j : Nat) : Expr :=
  match surf.vertices[i]?, surf.vertices[j]?, surf.inducedMetrics[i]? with
  | some (t1, x1, y1), some (t2, x2, y2), some γ =>
      let dx : Array Rat := #[t2 - t1, x2 - x1, y2 - y1]
      -- ds² = γ_{ab} dx^a dx^b  (rational arithmetic, result is Expr)
      let ds2 := sumN 3 (fun a => sumN 3 (fun b =>
        simplify (.mul (.mul (matGet γ a b) (.lit (dx[a]!))) (.lit (dx[b]!)))))
      simplify (.sqrt ds2)
  | _, _, _ => .lit 0

-- ---------------------------------------------------------------------------
-- Dijkstra shortest-path on the discrete graph
-- ---------------------------------------------------------------------------

/-- Simple Dijkstra's algorithm on the adjacency list with symbolic edge weights.
    Returns the sequence of vertex indices forming the shortest path from `src` to `dst`.
    Since edge weights are `Expr` (symbolic), we minimise over vertex count
    (unweighted Dijkstra / BFS) as the symbolic lengths cannot be compared numerically. -/
def shortestPath (surf : DiscreteHypersurface) (src dst : Nat) : Array Nat :=
  let nv := surf.vertices.size
  if src >= nv || dst >= nv then #[]
  else
    -- BFS
    let visited := Array.replicate nv false
    let prev    := Array.replicate nv nv  -- nv = "no predecessor"
    let queue   := #[src]
    let visited := visited.set! src true
    let (_, _, prev) := Id.run do
      let mut q       := queue
      let mut visited := visited
      let mut prev    := prev
      let mut found   := false
      while !q.isEmpty && !found do
        let v := q[0]!
        q := q.extract 1 q.size
        if v == dst then
          found := true
        else
          for w in surf.adjacencyList[v]! do
            if !visited[w]! then
              visited := visited.set! w true
              prev    := prev.set! w v
              q := q.push w
      pure (q, visited, prev)
    -- Reconstruct path
    Id.run do
      let mut path := #[dst]
      let mut cur  := dst
      let mut ok   := true
      while ok && cur != src do
        let p := prev[cur]!
        if p == nv then
          ok := false  -- no path
        else
          path := #[p] ++ path
          cur  := p
      return if ok then path else #[]

-- ---------------------------------------------------------------------------
-- Geodesic path length (sum of edge lengths along the path)
-- ---------------------------------------------------------------------------

/-- Compute the total length of a discrete geodesic path (sequence of vertex indices). -/
def pathLength (surf : DiscreteHypersurface) (path : Array Nat) : Expr :=
  if path.size < 2 then .lit 0
  else
    (List.range (path.size - 1)).foldl (fun acc k =>
      simplify (.add acc (edgeLength surf (path[k]!) (path[k+1]!)))) (.lit 0)

-- ---------------------------------------------------------------------------
-- Discrete parallel transport
-- ---------------------------------------------------------------------------

/-- First-order local transport matrix along edge (i→j).
    Uses the Christoffel symbols of the induced metric at vertex i:
      T^a_b ≈ δ^a_b - Γ^a_{bc} Δx^c
    where Δx^c = x^c_j - x^c_i is the coordinate displacement. -/
private def edgeTransport (surf : DiscreteHypersurface) (i j : Nat) : Mat :=
  let n3 := 3
  match surf.vertices[i]?, surf.vertices[j]?, surf.inducedMetrics[i]? with
  | some (t1, x1, y1), some (t2, x2, y2), some γ =>
      let dx : Array Expr := #[.lit (t2-t1), .lit (x2-x1), .lit (y2-y1)]
      -- Build a dummy MetricTensor from the induced metric (no coords needed for Γ)
      -- Use placeholder coordinate labels for symbolic differentiation
      let coords : Array String := #["t", "x1", "x2"]
      let gInv := matInv γ |>.getD (matId n3)
      let Γ := ChristoffelSymbols.computeMixed γ gInv coords
      let getΓ := fun a b c => ChristoffelSymbols.getComp n3 Γ a b c
      -- T^a_b = δ^a_b - Σ_c Γ^a_{bc} Δx^c
      matBuild n3 (fun a b =>
        let correction := sumN n3 (fun c =>
          simplify (.mul (getΓ a b c) (dx[c]!)))
        let delta : Expr := if a == b then .lit 1 else .lit 0
        simplify (.sub delta correction))
  | _, _, _ => matId n3

/-- Discrete parallel transport matrix along a path.
    Computes the product of first-order Christoffel-corrected transport matrices
    T^a_b ≈ δ^a_b - Γ^a_{bc} Δx^c at each edge, matching the WL source's
    numerical integration approach in the symbolic/first-order limit. -/
def parallelTransport (surf : DiscreteHypersurface) (path : Array Nat) : Mat :=
  let n3 := 3
  if path.size < 2 then matId n3
  else
    (List.range (path.size - 1)).foldl (fun acc k =>
      let vi := path[k]!
      let vj := path[k+1]!
      matMul acc (edgeTransport surf vi vj)
    ) (matId n3)

end Gravitas
