import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9PendantCliqueExclusion
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9CubicMaskTriangle

/-! The three-closed-axis obstruction rules out every triangle of cubic
vertices in an actual contact graph. This applies at any number of masks. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9CubicTriangleExclusion

open Finset
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open Q9WeightedSaturation (defect signedBiadjacency)
open Q9IsotropicHuang (parity weightedLinear)
open Q9MinimumDistanceOperator (minimumDisplacements)
open Q9ActualMinimumDisplacements (exists_both_parity_supported_of_signed_defect_singular)
open Q9SquareMaskGraph (activeAxes maskGraph distance_two_mask_graph_constraints)
open Q9CubicMaskTriangle (triangle_closes)
open Q9PendantCliqueExclusion (no_four_axis_block_with_three_closed_axes)
open private neighbors_eq_triple from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9CubicMaskTriangle
open private mem_minimumDisplacements from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open private pair_ne from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SquareMaskGraph
open private mem_axes from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.MinimumContactDisplacementCount

open Classical in
/-- Three cubic contact axes cannot form a triangle. The square law would
close the triangle into a four-clique whose three original axes are closed,
and the fourth axis may have any additional neighbors. -/
theorem no_cubic_contact_triangle {C D : Finset (Q 9)} {b : Bool}
    (hsep : ∀ x ∈ C, ∀ y ∈ D, 2 ≤ hammingDist x y)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcC : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetC : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w C false)).det = 0)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0) :
    let F := minimumDisplacements C D b 2
    let G := maskGraph F
    ∀ a c e, G.Adj a c → G.Adj c e → G.Adj e a →
      G.degree a = 3 → G.degree c = 3 → G.degree e = 3 → False := by
  let F := minimumDisplacements C D b 2
  let G := maskGraph F
  change ∀ a c e : activeAxes F, G.Adj a c → G.Adj c e → G.Adj e a →
    G.degree a = 3 → G.degree c = 3 → G.degree e = 3 → False
  intro a c e hac hce hea ha hc he
  obtain ⟨_, hsquare⟩ := distance_two_mask_graph_constraints (b := b)
    hsep hrC hrD hcC hcD hbC hbD hdetC hdetD
  have hs : Q9TenMaskGraph.SquareCompletion G := by
    intro x y z
    exact hsquare
  obtain ⟨d, had, hcd, hed, _⟩ := triangle_closes hs hac hce hea ha hc he
  have hval {x y : activeAxes F} (h : x ≠ y) : x.val ≠ y.val := fun h' => h (Subtype.ext h')
  let A : Finset (Fin 9) := {a.val,c.val,e.val,d.val}
  have hA : A.card = 4 := by
    have h1 : a.val ∉ ({c.val,e.val,d.val} : Finset (Fin 9)) := by
      simp [hval hac.ne, hval hea.ne.symm, hval had.ne]
    have h2 : c.val ∉ ({e.val,d.val} : Finset (Fin 9)) := by
      simp [hval hce.ne, hval hcd.ne]
    rw [show A = insert a.val (insert c.val {e.val,d.val}) from rfl,
      card_insert_of_notMem h1, card_insert_of_notMem h2, card_pair (hval hed.ne)]
  have haN := neighbors_eq_triple ha hac hea.symm had hce.ne hcd.ne hed.ne
  have hcN := neighbors_eq_triple hc hac.symm hce hcd hea.ne.symm had.ne hed.ne
  have heN := neighbors_eq_triple he hea hce.symm hed hac.ne had.ne hcd.ne
  have hsize (T : Finset (Fin 9)) (hT : T ∈ F) : T.card = 2 := by
    obtain ⟨_, _, _, _, _, hdist, rfl⟩ := mem_minimumDisplacements.mp hT
    exact hdist
  have closed (k l : Fin 9) (hm : ({k,l} : Finset (Fin 9)) ∈ F) :
      k ∈ A → k ≠ d.val → l ∈ A := by
    intro hk hn
    have hl : l ∈ activeAxes F := mem_axes.mpr ⟨_, hm, by simp⟩
    let v : activeAxes F := ⟨l,hl⟩
    have hcases : k = a.val ∨ k = c.val ∨ k = e.val := by
      simpa only [A, mem_insert, mem_singleton, hn, or_false] using hk
    rcases hcases with rfl | rfl | rfl
    · have hv : G.Adj a v := ⟨fun h => pair_ne hsize hm (congrArg Subtype.val h),hm⟩
      have hmem := (G.mem_neighborFinset a v).mpr hv
      rw [haN] at hmem
      simp only [mem_insert,mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl <;> simp [A,v]
    · have hv : G.Adj c v := ⟨fun h => pair_ne hsize hm (congrArg Subtype.val h),hm⟩
      have hmem := (G.mem_neighborFinset c v).mpr hv
      rw [hcN] at hmem
      simp only [mem_insert,mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl <;> simp [A,v]
    · have hv : G.Adj e v := ⟨fun h => pair_ne hsize hm (congrArg Subtype.val h),hm⟩
      have hmem := (G.mem_neighborFinset e v).mpr hv
      rw [heN] at hmem
      simp only [mem_insert,mem_singleton] at hmem
      rcases hmem with rfl | rfl | rfl <;> simp [A,v]
  have hC (j : Fin 9) : ∃ f : Q 9 → ℝ,
      (∀ z, f z ≠ 0 ↔ z ∈ C ∧ parity z = b) ∧
      (∀ z ∉ C, weightedLinear (fun k => if k = j then 2 else 1) f z = 0) := by
    let w (k : Fin 9) : ℝ := if k = j then 2 else 1
    have hw (k : Fin 9) : 0 < w k := by dsimp only [w]; split <;> norm_num
    exact exists_both_parity_supported_of_signed_defect_singular C hrC hcC hbC w hw (hdetC w) b
  obtain ⟨g,hg,hAg⟩ := exists_both_parity_supported_of_signed_defect_singular D hrD hcD hbD
    (fun _ => 1) (fun _ => by norm_num) (hdetD fun _ => 1) b
  exact no_four_axis_block_with_three_closed_axes hA (by simp [A]) (by simp [A])
    (by simp [A]) (hval had.ne) (hval hcd.ne) hac.2
    (fun k l hm => ⟨closed k l hm, closed l k (by simpa only [Finset.pair_comm] using hm)⟩)
    hsep hrC hrD hbC hbD hC ⟨g,hg,hAg⟩

#print axioms no_cubic_contact_triangle

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9CubicTriangleExclusion
