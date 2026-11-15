/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceExclusion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceExclusion.claim; result=D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceExclusion.result; claim=D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceExclusion.claim
   digest: Actual asymmetric slice parameters force the excluded twenty-four-point graph. -/


import D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSlicePairs
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceNonEmbedding

/-! Actual degree-two/three bipartite slices with side counts13/11 and low
counts7/1, independent low vertices and girth at least eight have no induced
realization in any finite cube. Actual saturation forces a six-high core, all
eleven right labels and seven low pairs; actual degrees give an induced copy
of the previously excluded graph. Other parameter cases and Problem2 remain open.
The finite helper checks are consumed by the designated refutation result. -/


set_option linter.style.longLine false

open private rootThreeWeight root_three_paths_card root_weight_add_two root_paths_card_of_coverage root_weight_low root_weight_high root_three_paths_two_connectors saturation_count_equalities saturation_local_equality right_high_neighbor_rigidity saturation_endpoint_union high_root_endpoint_coverage low_vertex_high_neighbor_card asymmetric_right_type_counts asymmetric_left_connector_count neighbors_eq_pair complete_pairing c6_core_of_distinguished_pair from
  D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceRigidity
open private High connectors core high_left high_degree connector_right connector_degree connector_card high_neighbor_mem connector_filter_eq connector_third other_high middle_unique different_middle core_degree_two core_triangle_free low_vertex_anchor compressed_core_package high_skeleton_labels lowPair low_pair_excluded_by_common_high low_pair_excluded_by_short_paths low_pair_excluded_by_fixed_pair coverage_forces_low_pair connector_high_table ne_of_high_tables high_right_connector_labels stub_neighbor_table_three third_neighbor stub_actual_saturation stub_of_two_connectors stub_singleton_ne stub_adj_of_high_table stub_low_high_ne right_labels_assembly from
  D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceLabels
open private highIncidence allowedPair forbidden_pair_witness actual_low_pair_allowed first_four_low_pairs allowed_five allowed_seven allowed_nine two_partners_force_second low_pair_symm actual_low_pair_completion highRow IndexedLabels indexed_labels_of_parameters other_right_of_low_neighbor low_pair_partner_exists two_low_pair_partners_exists indexed_high_card_bound indexed_stub_high_card indexed_first_four all_actual_pairs from
  D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSlicePairs

/- Internal bridge from seven actual low pairs to the explicit 24-point graph.
The finite tables below specify labels and check actual edge types and degrees;
they are internal helpers for the eventual exclusion theorem. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricPairEmbedding

open SimpleGraph AsymmetricLowPairing AsymmetricLowPairAllowed
open private graph edges from
  D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceNonEmbedding

private instance : DecidableRel graph.Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ ((a, b) ∈ edges ∨ (b, a) ∈ edges)))

private abbrev Tag := Fin 11 ⊕ (Fin 7 ⊕ Fin 6)

private def leftEnd : Fin 7 → Fin 11 := ![1, 9, 2, 3, 7, 4, 5]
private def rightEnd : Fin 7 → Fin 11 := ![10, 10, 9, 8, 8, 7, 6]

private def labels : Fin 24 → Tag :=
  ![Sum.inl 7, Sum.inl 8, Sum.inl 9, Sum.inl 10,
    Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inl 4, Sum.inl 5, Sum.inl 6,
    Sum.inr (Sum.inl 0), Sum.inr (Sum.inl 1), Sum.inr (Sum.inl 2),
    Sum.inr (Sum.inl 3), Sum.inr (Sum.inl 4), Sum.inr (Sum.inl 5),
    Sum.inr (Sum.inl 6),
    Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1), Sum.inr (Sum.inr 2),
    Sum.inr (Sum.inr 3), Sum.inr (Sum.inr 4), Sum.inr (Sum.inr 5), Sum.inl 0]

private def tagDegree : Tag → ℕ :=
  Sum.elim (fun i => if i = 0 then 2 else 3)
    (Sum.elim (fun _ => 2) (fun _ => 3))

private def neighbors (a : Fin 24) : Finset (Fin 24) :=
  Finset.univ.filter (graph.Adj a)

private def edgeType (a b : Fin 24) : Prop :=
  (∃ (i : Fin 11) (p : Fin 6), labels a = Sum.inl i ∧
    labels b = Sum.inr (Sum.inr p) ∧ highIncidence i p) ∨
  ∃ k : Fin 7, labels a = Sum.inr (Sum.inl k) ∧
    (labels b = Sum.inl (leftEnd k) ∨ labels b = Sum.inl (rightEnd k))

private instance (a b : Fin 24) : Decidable (edgeType a b) := by
  unfold edgeType
  infer_instance

private theorem endpoints_distinct : ∀ k : Fin 7, leftEnd k ≠ rightEnd k := by
  decide +kernel

private theorem endpoints_identify :
    ∀ i j : Fin 7,
      (leftEnd i = leftEnd j ∨ leftEnd i = rightEnd j) →
      (rightEnd i = leftEnd j ∨ rightEnd i = rightEnd j) → i = j := by
  decide +kernel

private theorem labels_injective : Function.Injective labels := by
  decide +kernel

private theorem edges_have_type :
    edges.all (fun e => decide (edgeType e.1 e.2)) = true := by
  decide +kernel

private theorem neighbor_card :
    ∀ a : Fin 24, (neighbors a).card = tagDegree (labels a) := by
  decide +kernel

private theorem injective_sum {A B W : Type*} (f : A → W) (g : B → W)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hsep : ∀ a b, f a ≠ g b) : Function.Injective (Sum.elim f g) := by
  intro x y hxy
  cases x with
  | inl a =>
      cases y with
      | inl b => exact congrArg Sum.inl (hf hxy)
      | inr b => exact False.elim (hsep a b hxy)
  | inr a =>
      cases y with
      | inl b => exact False.elim (hsep b a hxy.symm)
      | inr b => exact congrArg Sum.inr (hg hxy)

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

private def realize (r : Fin 11 → V) (w : Fin 7 → V) (h : Fin 6 → V) : Tag → V :=
  Sum.elim r (Sum.elim w h)

omit [DecidableEq V] in
/-- An injective edge-preserving map whose vertices have exactly the source
neighbor counts is induced. -/
private theorem induced_of_saturated_degrees
    {A : Type*} (H : SimpleGraph A) (N : A → Finset A)
    (hN : ∀ a b, b ∈ N a ↔ H.Adj a b)
    (f : A → V) (hf : Function.Injective f)
    (hedge : ∀ a b, H.Adj a b → G.Adj (f a) (f b))
    (hdegree : ∀ a, G.degree (f a) = (N a).card) :
    ∀ a b, H.Adj a b ↔ G.Adj (f a) (f b) := by
  classical
  have hsat (a : A) : (N a).image f = G.neighborFinset (f a) := by
    have hsub : (N a).image f ⊆ G.neighborFinset (f a) := by
      intro y hy
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
      exact (G.mem_neighborFinset _ _).mpr (hedge a b ((hN a b).mp hb))
    apply Finset.eq_of_subset_of_card_le hsub
    apply le_of_eq
    calc
      (G.neighborFinset (f a)).card = G.degree (f a) := rfl
      _ = (N a).card := hdegree a
      _ = ((N a).image f).card := (Finset.card_image_of_injective _ hf).symm
  intro a b
  constructor
  · exact hedge a b
  · intro hab
    have hb : f b ∈ (N a).image f := by
      rw [hsat a]
      exact (G.mem_neighborFinset _ _).mpr hab
    obtain ⟨c, hc, hcb⟩ := Finset.mem_image.mp hb
    have hcb' : c = b := hf hcb
    subst c
    exact (hN a b).mp hc

variable {L R : Finset V}

omit [DecidableEq V] in
/-- Seven actual low pairs and the positive high incidences give an actual
induced copy of the explicit 24-vertex graph. -/
private theorem actual_pair_embedding
    (hpart : G.IsBipartiteWith (L : Set V) (R : Set V))
    (r : Fin 11 → V) (h : Fin 6 → V)
    (hr : Function.Injective r) (hh : Function.Injective h)
    (hrR : ∀ i, r i ∈ R) (hhL : ∀ p, h p ∈ L)
    (hh3 : ∀ p, G.degree (h p) = 3)
    (hz2 : G.degree (r 0) = 2)
    (hr3 : ∀ i : Fin 11, i ≠ 0 → G.degree (r i) = 3)
    (hinc : ∀ i p, highIncidence i p → G.Adj (r i) (h p))
    (h0 : lowPair G (r 1) (r 10))
    (h1 : lowPair G (r 9) (r 10))
    (h2 : lowPair G (r 2) (r 9))
    (h3 : lowPair G (r 3) (r 8))
    (h4 : lowPair G (r 7) (r 8))
    (h5 : lowPair G (r 4) (r 7))
    (h6 : lowPair G (r 5) (r 6)) :
    ∃ F : Fin 24 → V, Function.Injective F ∧
      ∀ a b, graph.Adj a b ↔ G.Adj (F a) (F b) := by
  classical
  have hpairs : ∀ k : Fin 7, lowPair G (r (leftEnd k)) (r (rightEnd k)) := by
    intro k
    fin_cases k
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
  have hwitness : ∀ k : Fin 7, ∃ w : V, G.degree w = 2 ∧
      G.Adj (r (leftEnd k)) w ∧ G.Adj (r (rightEnd k)) w := hpairs
  choose w hw2 hwp hwq using hwitness
  have hwL (k : Fin 7) : w k ∈ L :=
    hpart.symm.mem_of_mem_adj (hrR (leftEnd k)) (hwp k)
  have hwN (k : Fin 7) :
      G.neighborFinset (w k) = {r (leftEnd k), r (rightEnd k)} := by
    have hne : r (leftEnd k) ≠ r (rightEnd k) :=
      fun he => endpoints_distinct k (hr he)
    have hsub : ({r (leftEnd k), r (rightEnd k)} : Finset V) ⊆
        G.neighborFinset (w k) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with hx | hx
      · subst x
        exact (G.mem_neighborFinset _ _).mpr (hwp k).symm
      · have hx' := Finset.mem_singleton.mp hx
        subst x
        exact (G.mem_neighborFinset _ _).mpr (hwq k).symm
    apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
    simp [SimpleGraph.card_neighborFinset_eq_degree, hw2 k, hne]
  have hw : Function.Injective w := by
    intro i j hij
    have hpi : r (leftEnd i) ∈ G.neighborFinset (w j) := by
      apply (G.mem_neighborFinset _ _).mpr
      simpa only [hij] using (hwp i).symm
    have hqi : r (rightEnd i) ∈ G.neighborFinset (w j) := by
      apply (G.mem_neighborFinset _ _).mpr
      simpa only [hij] using (hwq i).symm
    rw [hwN j] at hpi hqi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpi hqi
    exact endpoints_identify i j
      (hpi.elim (fun he => Or.inl (hr he)) (fun he => Or.inr (hr he)))
      (hqi.elim (fun he => Or.inl (hr he)) (fun he => Or.inr (hr he)))
  have hwh : ∀ k p, w k ≠ h p := by
    intro k p he
    have hk := hw2 k
    rw [he, hh3 p] at hk
    omega
  have hleft : Function.Injective (Sum.elim w h) := injective_sum w h hw hh hwh
  have hleftL (t : Fin 7 ⊕ Fin 6) : Sum.elim w h t ∈ L := by
    cases t with
    | inl k => exact hwL k
    | inr p => exact hhL p
  have hrleft : ∀ i t, r i ≠ Sum.elim w h t := by
    intro i t he
    have hiL : r i ∈ L := by
      rw [he]
      exact hleftL t
    exact Set.disjoint_left.mp hpart.disjoint hiL (hrR i)
  have hreal : Function.Injective (realize r w h) :=
    injective_sum r (Sum.elim w h) hr hleft hrleft
  let F : Fin 24 → V := fun a => realize r w h (labels a)
  have hF : Function.Injective F := hreal.comp labels_injective
  have hedge_entry {a b : Fin 24} (hab : (a, b) ∈ edges) :
      G.Adj (F a) (F b) := by
    have ht : edgeType a b :=
      of_decide_eq_true ((List.all_eq_true.mp edges_have_type) (a, b) hab)
    change G.Adj (realize r w h (labels a)) (realize r w h (labels b))
    rcases ht with ⟨i, p, ha, hb, hip⟩ | ⟨k, ha, hb⟩
    · rw [ha, hb]
      exact hinc i p hip
    · rcases hb with hb | hb
      · rw [ha, hb]
        exact (hwp k).symm
      · rw [ha, hb]
        exact (hwq k).symm
  have hedge : ∀ a b, graph.Adj a b → G.Adj (F a) (F b) := by
    intro a b hab
    rcases hab with ⟨_, hab | hab⟩
    · exact hedge_entry hab
    · exact (hedge_entry hab).symm
  have hreal_degree (t : Tag) : G.degree (realize r w h t) = tagDegree t := by
    rcases t with i | (k | p)
    · change G.degree (r i) = if i = 0 then 2 else 3
      split_ifs with hi
      · subst i
        exact hz2
      · exact hr3 i hi
    · exact hw2 k
    · exact hh3 p
  have hdegree (a : Fin 24) : G.degree (F a) = (neighbors a).card :=
    (hreal_degree (labels a)).trans (neighbor_card a).symm
  refine ⟨F, hF, ?_⟩
  apply induced_of_saturated_degrees graph neighbors ?_ F hF hedge hdegree
  intro a b
  simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and]

end D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricPairEmbedding

end

/- The asymmetric parameter branch has no induced realization in a finite cube. -/

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceExclusion

open SimpleGraph GirthSliceCounting AsymmetricIndexedSliceLabels AsymmetricPairEmbedding
open D5.S3.Combinatorics.Graph.Hypercube
open private indexed_labels_of_parameters from D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSlicePairs
open private all_actual_pairs from D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSlicePairs

open private IndexedLabels.r IndexedLabels.h IndexedLabels.r_injective IndexedLabels.h_injective IndexedLabels.r_mem IndexedLabels.h_mem IndexedLabels.h_degree IndexedLabels.r_zero_degree IndexedLabels.r_nonzero_degree IndexedLabels.incidence from
  D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSlicePairs

/-- A genuine induced subset of a finite cube with the original slice parameters. -/
def claim : Prop :=
  ∃ (n : ℕ) (S : Finset (Fin n → Bool)),
    ∃ L R : Finset {x : Fin n → Bool // x ∈ S},
      let G := (hypercube n).induce {x | x ∈ S}
      G.IsBipartiteWith (L : Set {x : Fin n → Bool // x ∈ S})
        (R : Set {x : Fin n → Bool // x ∈ S}) ∧
      (∀ x, G.degree x = 2 ∨ G.degree x = 3) ∧
      (∀ {x y}, G.Adj x y → G.degree x = 2 → G.degree y = 2 → False) ∧
      (8 : ℕ∞) ≤ G.egirth ∧
      L.card = 13 ∧ R.card = 11 ∧
      (degreeTwo G L).card = 7 ∧ (degreeTwo G R).card = 1

/-- No finite cube contains an induced slice with parameters (13,11;7,1),
degrees two/three, independent low vertices and girth at least eight. -/
theorem result : ¬ claim := by
  rintro ⟨n, S, L, R, hpart, hdeg, hlow, hg, hL, hR, hL2, hR2⟩
  obtain ⟨s⟩ := indexed_labels_of_parameters hpart hdeg hlow hg hL hR hL2 hR2
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ :=
    all_actual_pairs hpart hdeg hlow hg hL hR hL2 hR2 s
  obtain ⟨F, hF, he⟩ := actual_pair_embedding hpart (IndexedLabels.r s) (IndexedLabels.h s)
    (IndexedLabels.r_injective s) (IndexedLabels.h_injective s) (IndexedLabels.r_mem s) (IndexedLabels.h_mem s) (IndexedLabels.h_degree s)
    (IndexedLabels.r_zero_degree s) (IndexedLabels.r_nonzero_degree s) (fun i p hip => ((IndexedLabels.incidence s) i p).mpr hip)
    p1 p7 p2 p3 p6 p4 p5
  exact AsymmetricSliceNonEmbedding.result
    ⟨n, fun a => (F a).val, Subtype.val_injective.comp hF, fun a b => he a b⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.AsymmetricSliceExclusion

end
