/-!
# JSP-000690: a critically 3-chromatic 3-uniform hypergraph of minimum degree 7

Justin Sun Prize problem bank entry JSP-000690: *Is there a three-uniform,
three-chromatic-critical hypergraph with minimum degree at least seven?*

The problem originates with Erdős and Lovász and was resolved affirmatively
(chromatic interpretation) by **Ruiliang Li** (arXiv:2512.24850, 2025) via an
explicit construction. This file machine-checks that answer: the hypergraph
`edges` below, on 9 vertices with 22 edges, satisfies

* every edge has 3 vertices (3-uniform),
* no proper 2-colouring exists (Property B fails), while a proper
  3-colouring exists — so the chromatic number is exactly 3,
* deleting any single edge, or any single vertex, leaves a 2-colourable
  hypergraph (criticality; witness colourings appear in Appendix B of the
  paper and are re-derived here by exhaustive search),
* every vertex lies in at least 7 edges (degree 10 for vertex `1`, and 7 for
  each of the other eight vertices).

Implementation note: colourings are enumerated as the bits of `n < 2^9`
(`colOf n v` is bit `v` of `n`), and all statements are reduced to closed
`Bool` computations checked by the kernel with `decide`. **Lean core only,
no mathlib, no axioms.**

Attribution: mathematical solution — Ruiliang Li (2025); Lean formalization —
AI-assisted (GLM via the ZCode agent) directed by @aichiwuhuarou.
-/

/-- The 22 hyperedges (paper equation (5)), on vertices indexed 
(paper vertex `i ∈ {1,…,9}` is `i - 1`). -/
def edges : List (List Nat) :=
  [[0, 1, 2], [0, 1, 8], [0, 2, 7], [0, 3, 5], [0, 3, 7], [0, 3, 8],
   [0, 4, 6], [0, 4, 7], [0, 4, 8], [0, 5, 6], [1, 2, 5], [1, 2, 6],
   [1, 3, 8], [1, 4, 8], [1, 5, 6], [2, 3, 7], [2, 4, 7], [2, 5, 6],
   [3, 5, 7], [3, 5, 8], [4, 6, 7], [4, 6, 8]]



/-- Colouring number `n < 512` assigns vertex `v` the bit `v` of `n`. -/
def colOf (n : Nat) (v : Nat) : Bool := (n >>> v) % 2 == 1

/-- Monochromaticity of edge `e` (a vertex list) under colouring number `n`. -/
def monoE (n : Nat) (e : List Nat) : Bool :=
  e.all (fun v => colOf n v) || e.all (fun v => !colOf n v)

/-- Colouring number `n` is proper for the edge list `H`. -/
def properN (n : Nat) (H : List (List Nat)) : Bool :=
  H.all (fun e => !monoE n e)

/-- 3-colouring number `m < 3^9` assigns vertex `v` the base-3 digit `v` of `m`. -/
def col3Of (m v : Nat) : Nat := (m / 3 ^ v) % 3

/-- Edge `e` is monochromatic under 3-colouring number `m`. -/
def mono3 (m : Nat) (e : List Nat) : Bool :=
  e.all (fun v => col3Of m v == 0) || e.all (fun v => col3Of m v == 1)
  || e.all (fun v => col3Of m v == 2)

/-- All 512 two-colourings fail to be proper for `H`. -/
def noProper2 (H : List (List Nat)) : Bool :=
  (List.range 512).all (fun n => !properN n H)

/-- Some 3-colouring (among `3^9 = 19683`) is proper for `H`. -/
def someProper3 (H : List (List Nat)) : Bool :=
  (List.range 19683).any (fun m => H.all (fun e => !mono3 m e))

/-- Vertex `v` has degree `d` in `H`. -/
def degree (H : List (List Nat)) (v : Nat) : Nat :=
  (H.filter (fun e => e.contains v)).length

/-- All 9 vertices have degree at least 7 (vertex 1 has degree 10). -/
def degreesOK : Bool :=
  (List.range 9).all (fun v => 7 <= degree edges v)
  && degree edges 0 == 10

/-- Edge-criticality: after deleting any edge some 2-colouring works. -/
def edgeCritical : Bool :=
  edges.all (fun e =>
    (List.range 512).any (fun n =>
      (edges.filter (fun f => f != e)).all (fun f => !monoE n f)))

/-- Vertex-criticality: after deleting any vertex some 2-colouring works on
the edges avoiding that vertex. -/
def vertexCritical : Bool :=
  (List.range 9).all (fun v =>
    (List.range 512).any (fun n =>
      (edges.filter (fun e => !e.contains v)).all (fun f => !monoE n f)))

set_option maxRecDepth 512000

/-! ### Machine-checked facts -/

/-- 3-uniformity: every edge has exactly 3 vertices. -/
theorem uniform3 : edges.all (fun e => e.length = 3) = true := by decide

/-- The minimum degree is 7: every vertex lies in at least 7 edges, and
vertex `0` (paper vertex 1) lies in 10. -/
theorem degrees : degreesOK = true := by decide

theorem degrees_min : (List.range 9).all (fun v => 7 <= degree edges v) = true := by
  decide

/-- No proper 2-colouring exists (all 512 colourings fail). -/
theorem not_two_colourable : noProper2 edges = true := by decide

/-- A proper 3-colouring exists; hence the chromatic number is exactly 3. -/
theorem three_colourable : someProper3 edges = true := by decide

/-- Deleting any single edge leaves a 2-colourable hypergraph. -/
theorem edge_critical : edgeCritical = true := by decide

/-- Deleting any single vertex leaves a 2-colourable hypergraph. -/
theorem vertex_critical : vertexCritical = true := by decide

/-- **Main theorem (JSP-000690, chromatic interpretation).** There exists a
3-uniform hypergraph of minimum degree at least 7 that is critically
3-chromatic: not 2-colourable, 3-colourable, and 2-colourable again after
deleting any single edge or any single vertex. -/
theorem jsp_000690 :
    edges.all (fun e => e.length = 3) = true ∧
    noProper2 edges = true ∧
    someProper3 edges = true ∧
    edgeCritical = true ∧
    vertexCritical = true ∧
    (List.range 9).all (fun v => 7 <= degree edges v) = true :=
  ⟨uniform3, not_two_colourable, three_colourable, edge_critical,
    vertex_critical, degrees_min⟩
