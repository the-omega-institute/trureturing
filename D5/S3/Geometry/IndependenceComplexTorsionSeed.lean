/- GID: D5/S3/Geometry/IndependenceComplexTorsionSeed
   generality: I
   mirror-B: D5/B/S3/Geometry/IndependenceComplexTorsionSeed
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.Homology.ShortComplex.ModuleCat, mathlib/module/Mathlib.Combinatorics.SimpleGraph.Clique]
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Geometry/IndependenceComplexTorsionSeed.seedClass_nonzero_killed_by_two; premises=D5/S3/Geometry/IndependenceComplexTorsionSeed.d1_z,D5/S3/Geometry/IndependenceComplexTorsionSeed.d2_boundingChain,D5/S3/Geometry/IndependenceComplexTorsionSeed.detector_d2,D5/S3/Geometry/IndependenceComplexTorsionSeed.detector_z
   digest: An explicit integral one-cycle in the eleven-vertex independence complex has exact order two in its finite-chain homology. -/
import D5.S3.Geometry.FiniteGraphVertexSubstitution
import D5.S3.HomologicalAlgebra.DetectedOrderTwoHomology
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.GroupTheory.OrderOfElement

/-!
This is a necessary component of the counterexample route for Carnero Bravo,
arXiv:2505.06457v2, Question 32, not Question 35 and not a separate solved
original problem. It concerns integral finite ordered simplicial chains.

The graph H has graph6 encoding `JEhbtj{rve?`; G0 is its complement. Its
independence complex is exactly `FiniteGraphVertexSubstitution.independenceComplex
G0`. The edge and triangle enumerations below are proved bijective onto the
actual increasing independent faces. In those bases the differentials are the
usual alternating simplicial boundaries. The class lives in Mathlib's actual
`ShortComplex.homology` in `ModuleCat ℤ`.

The graph and coefficient data are explicit below. The integer chain and
mod-two cocycle supply kernel-checkable finite identities; the detector's
linearity extends the column identities to all integral boundaries.

The comparison with singular homology of the actual coordinate realization is
still a separate obligation. This module asserts neither that comparison nor
the full topological counterexample, exact H1 = Z/2, or a novelty claim.

The finite numerical premises feed `seedClass_nonzero_killed_by_two`; its
nonzero assertion also consumes the direct `z_not_boundary` proof. The intended
external consumer is the full Question 32 torsion obstruction, which is not yet
implemented here. The finite numerical premises are consumed in this module; this is not a
claim to resolve a separate published open problem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096

namespace D5.S3.Geometry.IndependenceComplexTorsionSeed

open CategoryTheory
open D5.S3.HomologicalAlgebra.DetectedOrderTwoHomology
open scoped BigOperators

abbrev Vertex := Fin 11
abbrev EdgeIndex := Fin 32
abbrev TriangleIndex := Fin 24

/-- Six-bit payload values of `Ehbtj{rve?`, after subtracting ASCII 63.
The initial `J` specifies eleven vertices. The last five padding bits are zero. -/
def graph6Bit (k : ℕ) : Bool :=
  Nat.testBit
    ((([6, 41, 35, 53, 43, 60, 51, 55, 38, 0] : List ℕ)[k / 6]?).getD 0)
    (5 - k % 6)

/-- The actual graph6 graph, reading the upper triangle in column order. -/
def H : SimpleGraph Vertex where
  Adj a b := a ≠ b ∧ graph6Bit
    (max a.val b.val * (max a.val b.val - 1) / 2 + min a.val b.val) = true
  symm := ⟨by
    intro a b h
    exact ⟨Ne.symm h.1, by simpa only [max_comm, min_comm] using h.2⟩⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩

instance : DecidableRel H.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ graph6Bit
    (max a.val b.val * (max a.val b.val - 1) / 2 + min a.val b.val) = true))

/-- The eleven-vertex seed whose independent faces are the cliques of H. -/
def G0 : SimpleGraph Vertex := Hᶜ

instance : DecidableRel G0.Adj := by
  unfold G0
  infer_instance

/-- The existing project's independence complex, without a replacement model. -/
def seedComplex : AbstractSimplicialComplex Vertex :=
  FiniteGraphVertexSubstitution.independenceComplex G0

instance (s : Finset Vertex) : Decidable (s ∈ seedComplex) :=
  inferInstanceAs (Decidable (s.Nonempty ∧ G0.IsIndepSet (s : Set Vertex)))

/-- Increasing oriented edge table, in the order of the retained certificate. -/
def edge : EdgeIndex → Vertex × Vertex := ![
  (0, 3), (0, 4), (0, 7), (0, 8), (0, 9), (0, 10),
  (1, 3), (1, 5), (1, 6), (1, 8), (1, 9), (1, 10),
  (2, 4), (2, 5), (2, 6), (2, 7), (2, 8), (2, 10),
  (3, 6), (3, 7), (3, 8), (3, 10), (4, 6), (4, 8),
  (4, 9), (5, 7), (5, 8), (5, 9), (6, 9), (6, 10),
  (7, 9), (7, 10)]

/-- Increasing oriented triangle table; (a,b,c) means [a,b,c]. -/
def triangle : TriangleIndex → Vertex × Vertex × Vertex := ![
  (0, 3, 7), (0, 3, 8), (0, 3, 10), (0, 4, 8),
  (0, 4, 9), (0, 7, 9), (0, 7, 10), (1, 3, 6),
  (1, 3, 8), (1, 3, 10), (1, 5, 8), (1, 5, 9),
  (1, 6, 9), (1, 6, 10), (2, 4, 6), (2, 4, 8),
  (2, 5, 7), (2, 5, 8), (2, 6, 10), (2, 7, 10),
  (3, 6, 10), (3, 7, 10), (4, 6, 9), (5, 7, 9)]

/-- The genuine increasing one-simplices of `seedComplex`. -/
def EdgeSimplex := {p : Vertex × Vertex //
  p.1 < p.2 ∧ ({p.1, p.2} : Finset Vertex) ∈ seedComplex}

/-- The genuine increasing two-simplices of `seedComplex`. -/
def TriangleSimplex := {p : Vertex × Vertex × Vertex //
  p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧
    ({p.1, p.2.1, p.2.2} : Finset Vertex) ∈ seedComplex}

set_option maxHeartbeats 2000000 in
-- Exhaustive kernel reduction of the fixed finite chain tables.
private theorem edge_enumeration : ∀ a b : Vertex,
    (a < b ∧ ({a, b} : Finset Vertex) ∈ seedComplex) ↔
      ∃ e : EdgeIndex, edge e = (a, b) := by
  decide

set_option maxHeartbeats 2000000 in
-- Exhaustive kernel reduction of the fixed finite chain tables.
private theorem triangle_enumeration : ∀ a b c : Vertex,
    (a < b ∧ b < c ∧ ({a, b, c} : Finset Vertex) ∈ seedComplex) ↔
      ∃ t : TriangleIndex, triangle t = (a, b, c) := by
  decide

set_option maxHeartbeats 2000000 in
-- Exhaustive kernel reduction of the fixed finite chain tables.
private theorem edge_injective : Function.Injective edge := by decide
set_option maxHeartbeats 2000000 in
-- Exhaustive kernel reduction of the fixed finite chain tables.
private theorem triangle_injective : Function.Injective triangle := by decide

/-- This equivalence certifies that every actual edge occurs, exactly once.
It is used in the boundary maps, so the chain basis is tied to the actual complex. -/
noncomputable def edgeSimplexEquiv : EdgeIndex ≃ EdgeSimplex :=
  Equiv.ofBijective
    (fun e => ⟨edge e, (edge_enumeration _ _).mpr ⟨e, rfl⟩⟩)
    ⟨fun _ _ h => edge_injective (congrArg Subtype.val h), by
      rintro ⟨⟨a, b⟩, hab⟩
      obtain ⟨e, he⟩ := (edge_enumeration a b).mp hab
      exact ⟨e, Subtype.ext he⟩⟩

/-- Likewise, all actual increasing triangles occur exactly once. -/
noncomputable def triangleSimplexEquiv : TriangleIndex ≃ TriangleSimplex :=
  Equiv.ofBijective
    (fun t => ⟨triangle t, (triangle_enumeration _ _ _).mpr ⟨t, rfl⟩⟩)
    ⟨fun _ _ h => triangle_injective (congrArg Subtype.val h), by
      rintro ⟨⟨a, b, c⟩, habc⟩
      obtain ⟨t, ht⟩ := (triangle_enumeration a b c).mp habc
      exact ⟨t, Subtype.ext ht⟩⟩

abbrev C0 := Vertex → ℤ
abbrev C1 := EdgeIndex → ℤ
abbrev C2 := TriangleIndex → ℤ

/-- The column [b] - [a] for the actual oriented edge [a,b]. -/
noncomputable def edgeBoundary (e : EdgeIndex) : C0 :=
  Pi.single (edgeSimplexEquiv e).val.2 1 -
    Pi.single (edgeSimplexEquiv e).val.1 1

/-- The actual integer simplicial differential Z^32 -> Z^11. -/
noncomputable def d1 : C1 →ₗ[ℤ] C0 :=
  Fintype.linearCombination ℤ edgeBoundary

/-- The column [b,c] - [a,c] + [a,b] for the actual triangle [a,b,c]. -/
noncomputable def triangleBoundary (t : TriangleIndex) : C1 := fun e =>
  let p := (triangleSimplexEquiv t).val
  let q := (edgeSimplexEquiv e).val
  (if q = (p.2.1, p.2.2) then 1 else 0) -
    (if q = (p.1, p.2.2) then 1 else 0) +
    (if q = (p.1, p.2.1) then 1 else 0)

/-- The actual integer simplicial differential Z^24 -> Z^32. -/
noncomputable def d2 : C2 →ₗ[ℤ] C1 :=
  Fintype.linearCombination ℤ triangleBoundary

set_option maxHeartbeats 2000000 in
-- Exhaustive kernel reduction of the fixed finite chain tables.
private theorem triangleBoundary_cycle :
    ∀ t : TriangleIndex, d1 (triangleBoundary t) = 0 := by
  decide

/-- The actual two successive finite ordered boundary maps compose to zero. -/
theorem d1_comp_d2 : d1.comp d2 = 0 := by
  apply LinearMap.ext
  intro c
  change d1 (∑ t, c t • triangleBoundary t) = 0
  simp only [map_sum, map_smul, triangleBoundary_cycle, smul_zero, Finset.sum_const_zero]

/-- Degree-one finite ordered simplicial chain homology of `seedComplex`.
The higher chain groups do not affect ker(d1)/im(d2). -/
noncomputable def seedChainComplex : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.moduleCatMk d2 d1 d1_comp_d2

/-- The displayed oriented cycle [0,3] - [0,7] - [1,3] + [1,5] + [5,7]. -/
def z : C1 := ![
  1, 0, -1, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]

/-- Retained integral triangle coefficients whose boundary is twice z. -/
def boundingChain : C2 := ![
  0, 1, 1, -1, 1, -1, -1, 0, -1, -1, 1, 1,
  -1, 1, -1, 1, 1, -1, -1, 1, 0, 0, 1, 1]

/-- The ten tree edges, with the orientations of `edge`. -/
def treeEdge : Fin 10 → EdgeIndex := ![0, 1, 2, 3, 4, 5, 6, 18, 12, 25]

/-- The complementary edges, in the certificate's non-tree order. -/
def nonTreeEdge : Fin 22 → EdgeIndex := ![
  7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 19,
  20, 21, 22, 23, 24, 26, 27, 28, 29, 30, 31]

/-- The supplied detecting cocycle, before extension to the tree edges. -/
def nonTreeCocycle : Fin 22 → ZMod 2 := ![
  1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0,
  0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0]

set_option maxHeartbeats 2000000 in
-- Exhaustive kernel reduction of the fixed finite chain tables.
/-- A full edge functional, with its zero-on-tree and retained non-tree values
included in its type. No spanning-tree theorem is needed for the detection proof. -/
def extendedCocycle : {w : EdgeIndex → ZMod 2 //
    (∀ i : Fin 10, w (treeEdge i) = 0) ∧
    (∀ i : Fin 22, w (nonTreeEdge i) = nonTreeCocycle i)} :=
  ⟨![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1,
    0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0], by decide⟩

/-- The additive mod-two detector, as a linear map of integer modules. -/
def detector : C1 →ₗ[ℤ] ZMod 2 :=
  Fintype.linearCombination ℤ extendedCocycle.val

set_option maxHeartbeats 2000000 in
-- Exhaustive kernel reduction of the fixed finite chain tables.
private theorem detector_triangleBoundary :
    ∀ t : TriangleIndex, detector (triangleBoundary t) = 0 := by
  decide

/-- The cocycle vanishes on every integral triangle boundary. -/
theorem detector_d2 (c : C2) : detector (d2 c) = 0 := by
  change detector (∑ t, c t • triangleBoundary t) = 0
  simp only [map_sum, map_smul, detector_triangleBoundary, smul_zero, Finset.sum_const_zero]

set_option maxHeartbeats 2000000 in
-- Exhaustive kernel reduction of the fixed finite chain tables.
/-- The retained edge vector is a cycle. -/
theorem d1_z : d1 z = 0 := by decide

set_option maxHeartbeats 2000000 in
-- Exhaustive kernel reduction of the fixed finite chain tables.
/-- The retained triangle chain bounds twice the cycle, with integral coefficients. -/
theorem d2_boundingChain : d2 boundingChain = (2 : ℕ) • z := by decide

set_option maxHeartbeats 2000000 in
-- Exhaustive kernel reduction of the fixed finite chain tables.
/-- The full edge cocycle takes value one on the displayed cycle. -/
theorem detector_z : detector z = 1 := by decide

/-- In particular the cycle is not an integral boundary. -/
theorem z_not_boundary : z ∉ LinearMap.range d2 := by
  rintro ⟨c, hc⟩
  have h : (1 : ZMod 2) = 0 := by
    calc
      1 = detector z := detector_z.symm
      _ = detector (d2 c) := congrArg detector hc.symm
      _ = 0 := detector_d2 c
  exact one_ne_zero h

/-- The actual categorical homology class of the retained cycle. -/
noncomputable def seedClass : seedChainComplex.homology :=
  cycleClassMap seedChainComplex ⟨z, d1_z⟩

/-- Exact additive order two; no assertion about the other homology classes. -/
theorem seedClass_addOrderOf : addOrderOf seedClass = 2 := by
  have h := detected_order_two seedChainComplex ⟨z, d1_z⟩ boundingChain
    d2_boundingChain detector detector_d2 (by
      change detector z ≠ (0 : ZMod 2)
      rw [detector_z]
      exact one_ne_zero)
  exact addOrderOf_eq_prime h.2 h.1

/-- The displayed class is nonzero and killed by two in the degree-one
finite ordered simplicial homology object of the actual seed complex. -/
theorem seedClass_nonzero_killed_by_two :
    seedClass ≠ 0 ∧ (2 : ℕ) • seedClass = 0 := by
  refine ⟨?_, (addOrderOf_eq_prime_iff.mp seedClass_addOrderOf).1⟩
  intro hzero
  obtain ⟨c, hc⟩ :=
    (cycleClassMap_eq_zero_iff seedChainComplex ⟨z, d1_z⟩).mp hzero
  exact z_not_boundary ⟨c, hc⟩

end D5.S3.Geometry.IndependenceComplexTorsionSeed
