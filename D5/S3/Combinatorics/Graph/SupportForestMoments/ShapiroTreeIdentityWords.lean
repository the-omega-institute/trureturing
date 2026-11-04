/- GID: D5/S3/Combinatorics/Graph/SupportForestMoments/ShapiroTreeIdentityWords
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/SupportForestMoments/ShapiroTreeIdentityWords
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Leaf intervals characterize identity words on every finite tree. -/

/-
Mathematical judgement:
ShapiroProbe.edge_fixed: proof_shape: bind-only; escape_witness: none
consumers: ShapiroProbe.distinct_forest_fixed, ShapiroProbe.word_fixed
Direct frozen dependencies: D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.edgeSwap sha256:d6c9b690e033e2588f285eeefbade1f09b60432a5cd9a60126139955c331cdea
ShapiroProbe.word_fixed: proof_shape: bind-only; escape_witness: none
consumers: ShapiroMain.identity_separated, ShapiroProbe.distinct_forest_fixed
Direct frozen dependencies: D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.edgeSwap sha256:d6c9b690e033e2588f285eeefbade1f09b60432a5cd9a60126139955c331cdea
ShapiroProbe.word_reachable: proof_shape: bind-only; escape_witness: none
consumers: ShapiroProbe.distinct_forest_fixed, ShapiroProbe.once_not_identity
Direct frozen dependencies: D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.edgeSwap sha256:d6c9b690e033e2588f285eeefbade1f09b60432a5cd9a60126139955c331cdea
ShapiroProbe.distinct_forest_fixed: proof_shape: content; escape_witness: none
consumers: ShapiroMain.identity_separated
Direct frozen dependencies: D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.edgeSwap sha256:d6c9b690e033e2588f285eeefbade1f09b60432a5cd9a60126139955c331cdea
ShapiroProbe.once_not_identity: proof_shape: bind-only; escape_witness: none
consumers: ShapiroProbe.count_ne_one
Direct frozen dependencies: D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.edgeSwap sha256:d6c9b690e033e2588f285eeefbade1f09b60432a5cd9a60126139955c331cdea
ShapiroProbe.count_ne_one: proof_shape: bind-only; escape_witness: none
consumers: ShapiroProbe.multiplicity_two
Direct frozen dependencies: D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.edgeSwap sha256:d6c9b690e033e2588f285eeefbade1f09b60432a5cd9a60126139955c331cdea
ShapiroProbe.multiplicity_two: proof_shape: bind-only; escape_witness: none
consumers: result
Direct frozen dependencies: D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.edgeSwap sha256:d6c9b690e033e2588f285eeefbade1f09b60432a5cd9a60126139955c331cdea
ShapiroList.four_sublist: proof_shape: bind-only; escape_witness: none
consumers: ShapiroList.between_commute
Direct frozen dependencies: none
ShapiroList.gap_nodup: proof_shape: content; escape_witness: none
consumers: ShapiroList.interval_cancellation
Direct frozen dependencies: none
ShapiroList.good_sublist: proof_shape: bind-only; escape_witness: none
consumers: ShapiroList.interval_cancellation
Direct frozen dependencies: none
ShapiroList.double_delete: proof_shape: bind-only; escape_witness: none
consumers: ShapiroList.interval_cancellation
Direct frozen dependencies: none
ShapiroList.singles_delete: proof_shape: bind-only; escape_witness: none
consumers: ShapiroList.interval_cancellation
Direct frozen dependencies: none
ShapiroList.between_commute: proof_shape: bind-only; escape_witness: none
consumers: ShapiroList.interval_cancellation
Direct frozen dependencies: none
ShapiroList.pair_delete_product: proof_shape: bind-only; escape_witness: none
consumers: ShapiroList.interval_cancellation
Direct frozen dependencies: none
ShapiroList.interval_cancellation: proof_shape: content; escape_witness: none
consumers: ShapiroMain.identity_separated, result
Direct frozen dependencies: none
ShapiroPattern.pattern_iff: proof_shape: bind-only; escape_witness: none
consumers: ShapiroPattern.local_iff
Direct frozen dependencies: none
ShapiroPattern.local_iff: proof_shape: bind-only; escape_witness: none
consumers: result
Direct frozen dependencies: D5/S1/Words/Patterns/NoncrossingNonnestingGraphRecurrence.Crossing sha256:2dcc5e50ba675171458ace069cbd437a54d26889fc87ae881c1ef8cbf8a225dc
ShapiroPattern.swap_commute: proof_shape: bind-only; escape_witness: none
consumers: ShapiroMain.separated_good
Direct frozen dependencies: D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.edgeSwap sha256:d6c9b690e033e2588f285eeefbade1f09b60432a5cd9a60126139955c331cdea
ShapiroPattern.skip_head_prefix: proof_shape: bind-only; escape_witness: none
consumers: ShapiroPattern.pattern_interval_count
Direct frozen dependencies: none
ShapiroPattern.middle_mem_left: proof_shape: bind-only; escape_witness: none
consumers: ShapiroPattern.pattern_interval_count
Direct frozen dependencies: none
ShapiroPattern.pattern_interval_count: proof_shape: bind-only; escape_witness: none
consumers: ShapiroMain.identity_separated
Direct frozen dependencies: none
ShapiroLeaf.forest_leaf: proof_shape: bind-only; escape_witness: none
consumers: ShapiroMain.identity_separated
Direct frozen dependencies: none
ShapiroLeaf.leaf_edge_unique: proof_shape: bind-only; escape_witness: none
consumers: ShapiroMain.identity_separated, ShapiroMain.leaf_disjoint
Direct frozen dependencies: none
ShapiroLeaf.leaf_interval: proof_shape: bind-only; escape_witness: none
consumers: ShapiroMain.identity_separated
Direct frozen dependencies: none
ShapiroMain.split_two: proof_shape: bind-only; escape_witness: none
consumers: ShapiroMain.identity_separated
Direct frozen dependencies: none
ShapiroMain.singles_nodup: proof_shape: bind-only; escape_witness: none
consumers: ShapiroMain.identity_separated
Direct frozen dependencies: none
ShapiroMain.swap_involution: proof_shape: bind-only; escape_witness: none
consumers: ShapiroMain.identity_separated, result
Direct frozen dependencies: D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.edgeSwap sha256:d6c9b690e033e2588f285eeefbade1f09b60432a5cd9a60126139955c331cdea
ShapiroMain.separated_good: proof_shape: bind-only; escape_witness: none
consumers: ShapiroMain.identity_separated, result
Direct frozen dependencies: D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.edgeSwap sha256:d6c9b690e033e2588f285eeefbade1f09b60432a5cd9a60126139955c331cdea
ShapiroMain.leaf_disjoint: proof_shape: bind-only; escape_witness: none
consumers: ShapiroMain.identity_separated
Direct frozen dependencies: none
ShapiroMain.identity_separated: proof_shape: content; escape_witness: none
consumers: result
Direct frozen dependencies: D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.edgeSwap sha256:d6c9b690e033e2588f285eeefbade1f09b60432a5cd9a60126139955c331cdea
result: proof_shape: content; escape_witness: none
consumers: none
Direct frozen dependencies: D5/S1/Words/Patterns/NoncrossingNonnestingGraphRecurrence.Crossing sha256:2dcc5e50ba675171458ace069cbd437a54d26889fc87ae881c1ef8cbf8a225dc, D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.edgeSwap sha256:d6c9b690e033e2588f285eeefbade1f09b60432a5cd9a60126139955c331cdea
NoncrossingDoubleOccurrence: proof_shape: bind-only; escape_witness: none
consumers: claim, result
Direct frozen dependencies: D5/S1/Words/Patterns/NoncrossingNonnestingGraphRecurrence.Crossing sha256:2dcc5e50ba675171458ace069cbd437a54d26889fc87ae881c1ef8cbf8a225dc
claim: proof_shape: bind-only; escape_witness: none
consumers: result
Direct frozen dependencies: D5/S1/Words/Patterns/NoncrossingNonnestingGraphRecurrence.Crossing sha256:2dcc5e50ba675171458ace069cbd437a54d26889fc87ae881c1ef8cbf8a225dc, D5/S3/Combinatorics/Graph/SupportForestMoments/SupportAndEdgeWordReflection.edgeSwap sha256:d6c9b690e033e2588f285eeefbade1f09b60432a5cd9a60126139955c331cdea
ShapiroList.Double: proof_shape: bind-only; escape_witness: none
consumers: ShapiroList.between_commute, ShapiroList.double_delete, ShapiroList.interval_cancellation, ShapiroMain.identity_separated, result
Direct frozen dependencies: none
ShapiroList.Good: proof_shape: bind-only; escape_witness: none
consumers: ShapiroList.between_commute, ShapiroList.good_sublist, ShapiroList.interval_cancellation
Direct frozen dependencies: none
ShapiroList.singles: proof_shape: bind-only; escape_witness: none
consumers: ShapiroList.interval_cancellation, ShapiroList.singles_delete, ShapiroMain.identity_separated, ShapiroMain.singles_nodup, result
Direct frozen dependencies: none
ShapiroPattern.Separated: proof_shape: bind-only; escape_witness: none
consumers: ShapiroMain.identity_separated, ShapiroMain.separated_good, ShapiroPattern.local_iff, result
Direct frozen dependencies: none
The definition rows specify formulas and consumed proof organization, rather than proof-valued definitions.
The settling result uses the leaf-interval singleton-residual obstruction in ShapiroMain.identity_separated.
admission_basis: open-problem-resolution (#22558; Proved)
The claim retains the source conditions; proofs use the existing endpoint transposition and Crossing.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/24676
-/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import D5.S3.Combinatorics.Graph.SupportForestMoments.SupportAndEdgeWordReflection
import D5.S1.Words.Patterns.NoncrossingNonnestingGraphRecurrence

/-! Identity edge words are characterized by multiplicity and local noncrossing. -/

namespace D5.S3.Combinatorics.Graph.SupportForestMoments.ShapiroTreeIdentityWords

open scoped Classical
noncomputable section

open D5.S3.Combinatorics.Graph.SupportForestMoments.SupportAndEdgeWordReflection (edgeSwap)
open D5.S1.Words.Patterns.NoncrossingNonnestingGraphRecurrence (Crossing)

/-- Every occurring edge occurs twice, and no two distinct edges have alternating occurrences.
`Crossing` is the existing predicate on pairs of positions; nesting is allowed. -/
def NoncrossingDoubleOccurrence {n : ℕ} (w : List (Sym2 (Fin n))) : Prop :=
  (∀ a : Sym2 (Fin n), a ∈ w → w.count a = 2) ∧
    ∀ i j k l : Fin w.length,
      w[i] = w[j] → w[k] = w[l] → w[i] ≠ w[k] →
        ¬ Crossing (i, j) (k, l)

/-- Shapiro, arXiv:2610.14373v1, Conjecture 1(iii), for every finite simple tree.
`Fin n` relabels the source's `[n]`. All letters are edges, all edges are used, and
multiplication is the literal list product of the existing endpoint transpositions. -/
def claim : Prop :=
  ∀ (n : ℕ) (T : SimpleGraph (Fin n)) (w : List (Sym2 (Fin n))),
    T.IsTree →
    (∀ a : Sym2 (Fin n), a ∈ w → a ∈ T.edgeFinset) →
    w.length = 2 * T.edgeFinset.card →
    (∀ a : Sym2 (Fin n), a ∈ T.edgeFinset → a ∈ w) →
      ((w.map edgeSwap).prod = 1 ↔
        (∀ a : Sym2 (Fin n), a ∈ T.edgeFinset → w.count a = 2) ∧
          ∀ x : Fin n, NoncrossingDoubleOccurrence (w.filter fun a => x ∈ a))

end



namespace ShapiroProbe
open scoped Classical
noncomputable section
open D5.S3.Combinatorics.Graph.SupportForestMoments.SupportAndEdgeWordReflection (edgeSwap)

private theorem edge_fixed {n : ℕ} (a : Sym2 (Fin n)) (x : Fin n) (hx : x ∉ a) :
    edgeSwap a x = x := by
  induction a using Sym2.ind with
  | _ u v =>
    simp only [Sym2.mem_iff, not_or] at hx
    exact Equiv.swap_apply_of_ne_of_ne hx.1 hx.2

private theorem word_fixed {n : ℕ} (w : List (Sym2 (Fin n))) (x : Fin n)
    (hx : ∀ a ∈ w, x ∉ a) : ((w).map edgeSwap).prod x = x := by
  exact List.prod_induction (fun σ : Equiv.Perm (Fin n) => σ x = x)
    (fun σ τ hσ hτ => by simpa only [Equiv.Perm.mul_apply,hτ] using hσ) rfl
    (by
      intro σ hσ
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hσ
      exact edge_fixed a x (hx a ha))

private theorem word_reachable {n : ℕ} (G : SimpleGraph (Fin n))
    (w : List (Sym2 (Fin n))) (hw : ∀ a ∈ w, a ∈ G.edgeSet) (x : Fin n) :
    G.Reachable x (((w).map edgeSwap).prod x) := by
  induction w with
  | nil => exact .rfl
  | cons a w ih =>
    have hi := ih (fun b hb => hw b (by simp [hb]))
    apply hi.trans
    change G.Reachable (((w).map edgeSwap).prod x) (edgeSwap a (((w).map edgeSwap).prod x))
    induction a using Sym2.ind with
    | _ u v =>
      have ha : G.Adj u v := G.mem_edgeSet.mp (hw _ (by simp))
      change G.Reachable (((w).map edgeSwap).prod x)
        (Equiv.swap u v (((w).map edgeSwap).prod x))
      by_cases hu : ((w).map edgeSwap).prod x = u
      · simpa only [hu, Equiv.swap_apply_left] using ha.reachable
      · by_cases hv : ((w).map edgeSwap).prod x = v
        · simpa only [hv, Equiv.swap_apply_right] using ha.symm.reachable
        · simpa only [Equiv.swap_apply_of_ne_of_ne hu hv] using (SimpleGraph.Reachable.rfl (G := G)
              (u := ((w).map edgeSwap).prod x))

private theorem distinct_forest_fixed {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.IsAcyclic) (w : List (Sym2 (Fin n)))
    (hw : ∀ a ∈ w, a ∈ G.edgeSet) (hd : w.Nodup) (x : Fin n) :
    ((w).map edgeSwap).prod x = x ↔ ∀ a ∈ w, x ∉ a := by
  constructor
  · intro hf
    induction w with
    | nil => simp
    | cons a w ih =>
      have hnd := List.nodup_cons.mp hd
      have hmem : ∀ b ∈ w, b ∈ G.edgeSet := fun b hb => hw b (by simp [hb])
      have hnot : x ∉ a := by
        induction a using Sym2.ind with
        | _ u v =>
          have ha : G.Adj u v := G.mem_edgeSet.mp (hw _ (by simp))
          have hb := (SimpleGraph.isAcyclic_iff_forall_isBridge.mp hG) (hw s(u,v) (by simp))
          have hr := word_reachable (G.deleteEdges {s(u,v)}) w (by
            intro b hbw
            rw [SimpleGraph.edgeSet_deleteEdges]
            exact ⟨hmem b hbw, by
              simp only [Set.mem_singleton_iff]
              intro he
              exact hnd.1 (he ▸ hbw)⟩) x
          change Equiv.swap u v (((w).map edgeSwap).prod x) = x at hf
          intro hx
          rcases Sym2.mem_iff.mp hx with hx | hx
          · subst x
            have he : ((w).map edgeSwap).prod u = v := by
              have hh := congrArg (Equiv.swap u v) hf
              simpa using hh
            exact hb (by simpa [he] using hr)
          · subst x
            have he : ((w).map edgeSwap).prod v = u := by
              have hh := congrArg (Equiv.swap u v) hf
              simpa using hh
            exact hb (by simpa [he] using hr.symm)
      have ht : ((w).map edgeSwap).prod x = x := by
        apply (edgeSwap a).injective
        change edgeSwap a (((w).map edgeSwap).prod x) = x at hf
        exact hf.trans (edge_fixed a x hnot).symm
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hnot
      · exact ih hmem hnd.2 ht b hb
  · exact word_fixed w x


private theorem once_not_identity {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.IsAcyclic)
    (u v : Fin n) (ha : G.Adj u v) (L R : List (Sym2 (Fin n)))
    (hL : ∀ b ∈ L, b ∈ G.edgeSet) (hR : ∀ b ∈ R, b ∈ G.edgeSet)
    (haL : s(u,v) ∉ L) (haR : s(u,v) ∉ R) :
    ((L ++ s(u,v) :: R).map edgeSwap).prod ≠ 1 := by
  intro hprod
  have hbridge := (SimpleGraph.isAcyclic_iff_forall_isBridge.mp hG)
    (G.mem_edgeSet.mpr ha)
  have hLd : ∀ b ∈ L, b ∈ (G.deleteEdges {s(u,v)}).edgeSet := by
    intro b hb
    rw [SimpleGraph.edgeSet_deleteEdges]
    exact ⟨hL b hb, by simpa only [Set.mem_singleton_iff] using
      (show b ≠ s(u,v) from fun h => haL (h ▸ hb))⟩
  have hRd : ∀ b ∈ R, b ∈ (G.deleteEdges {s(u,v)}).edgeSet := by
    intro b hb
    rw [SimpleGraph.edgeSet_deleteEdges]
    exact ⟨hR b hb, by simpa only [Set.mem_singleton_iff] using
      (show b ≠ s(u,v) from fun h => haR (h ▸ hb))⟩
  let x := (((R).map edgeSwap).prod)⁻¹ u
  have hx : ((R).map edgeSwap).prod x = u := (((R).map edgeSwap).prod).apply_symm_apply u
  have hprod' : ((L).map edgeSwap).prod * edgeSwap s(u,v) * ((R).map edgeSwap).prod = 1 := by
    simpa [List.map_append,List.prod_append,mul_assoc] using hprod
  have hh := congrArg (fun σ : Equiv.Perm (Fin n) => σ x) hprod'
  have hLv : ((L).map edgeSwap).prod v = x := by
    change ((L).map edgeSwap).prod (edgeSwap s(u,v) (((R).map edgeSwap).prod x)) = x at hh
    change ((L).map edgeSwap).prod (Equiv.swap u v (((R).map edgeSwap).prod x)) = x at hh
    simpa only [hx, Equiv.swap_apply_left] using hh
  have hrL := word_reachable (G.deleteEdges {s(u,v)}) L hLd v
  have hrR := word_reachable (G.deleteEdges {s(u,v)}) R hRd x
  rw [hLv] at hrL
  rw [hx] at hrR
  exact hbridge (hrL.trans hrR).symm

private theorem count_ne_one {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.IsAcyclic)
    (w : List (Sym2 (Fin n))) (hw : ∀ b ∈ w, b ∈ G.edgeSet) (hp : ((w).map edgeSwap).prod = 1)
    (a : Sym2 (Fin n)) : w.count a ≠ 1 := by
  intro hc
  have ha : a ∈ w := List.count_pos_iff.mp (by omega)
  obtain ⟨L,R,rfl⟩ := List.mem_iff_append.mp ha
  induction a using Sym2.ind with
  | _ u v =>
    have ha := G.mem_edgeSet.mp (hw s(u,v) (by simp))
    have hL := List.count_eq_zero.mp (show L.count s(u,v) = 0 from by
      simp only [List.count_append,List.count_cons_self] at hc; omega)
    have hR := List.count_eq_zero.mp (show R.count s(u,v) = 0 from by
      simp only [List.count_append,List.count_cons_self] at hc; omega)
    exact once_not_identity G hG u v ha L R
      (fun b hb => hw b (by simp [hb])) (fun b hb => hw b (by simp [hb])) hL hR hp

private theorem multiplicity_two {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.IsAcyclic)
    (w : List (Sym2 (Fin n))) (hw : ∀ b ∈ w, b ∈ G.edgeFinset)
    (hlen : w.length = 2 * G.edgeFinset.card)
    (honto : ∀ a ∈ G.edgeFinset, a ∈ w) (hp : ((w).map edgeSwap).prod = 1) :
    ∀ a ∈ G.edgeFinset, w.count a = 2 := by
  have hset : w.toFinset = G.edgeFinset := by
    ext a; simp only [List.mem_toFinset]; exact ⟨hw a,honto a⟩
  have hsum : ∑ a ∈ G.edgeFinset, w.count a = 2 * G.edgeFinset.card := by
    rw [← hset,List.sum_toFinset_count_eq_length,hlen,hset]
  have hlo : ∀ a ∈ G.edgeFinset, 2 ≤ w.count a := by
    intro a ha
    have hpos := List.count_pos_iff.mpr (honto a ha)
    have hne := count_ne_one G hG w (fun b hb => G.mem_edgeFinset.mp (hw b hb)) hp a
    omega
  intro a ha
  have hs : ∑ b ∈ G.edgeFinset, 2 = ∑ b ∈ G.edgeFinset, w.count b := by
    simpa [Finset.sum_const,Nat.mul_comm] using hsum.symm
  exact (Finset.sum_eq_sum_iff_of_le hlo).mp hs a ha |>.symm

end
end ShapiroProbe

namespace ShapiroList
open scoped Classical List
noncomputable section
variable {α M : Type*} [DecidableEq α] [Monoid M]

private def Double (w : List α) : Prop := ∀ a, w.count a = 0 ∨ w.count a = 2

private def Good (f : α → M) (w : List α) : Prop :=
  ∀ a b, [a,b,a,b] <+ w → Commute (f a) (f b)

private def singles (w : List α) : List α := w.filter fun a => w.count a = 1

omit [DecidableEq α] in
private theorem four_sublist (a b c d : α) (p q r s t : List α) :
    [a,b,c,d] <+ p ++ a :: q ++ b :: r ++ c :: s ++ d :: t := by
  simp only [List.append_assoc,List.cons_append]
  apply List.sublist_append_of_sublist_right
  apply List.Sublist.cons_cons
  apply List.sublist_append_of_sublist_right
  apply List.Sublist.cons_cons
  apply List.sublist_append_of_sublist_right
  apply List.Sublist.cons_cons
  apply List.sublist_append_of_sublist_right
  exact (List.nil_sublist t).cons_cons d

omit [DecidableEq α] in
private theorem gap_nodup (w : List α) (hw : ¬ w.Nodup) :
    ∃ p a v z, w = p ++ a :: v ++ a :: z ∧ v.Nodup := by
  induction w with
  | nil => simp at hw
  | cons a w ih =>
    by_cases hd : w.Nodup
    · have ha : a ∈ w := by simpa [List.nodup_cons, hd] using hw
      obtain ⟨p,z,hp⟩ := List.mem_iff_append.mp ha
      refine ⟨[],a,p,z,by simp [hp], ?_⟩
      rw [hp] at hd
      exact (List.nodup_append.mp hd).1
    · obtain ⟨p,b,v,z,hp,hv⟩ := ih hd
      exact ⟨a::p,b,v,z,by simp [hp],hv⟩

omit [DecidableEq α] in
private theorem good_sublist (f : α → M) {w v : List α}
    (h : Good f w) (hv : v <+ w) : Good f v :=
  fun a b hab => h a b (hab.trans hv)

private theorem double_delete (L v R : List α) (a : α)
    (h : Double (L ++ a :: v ++ a :: R)) : Double (L ++ v ++ R) := by
  intro b
  have hb := h b
  by_cases he : b = a
  · subst b
    left
    simp only [List.count_append, List.count_cons_self] at hb ⊢
    omega
  · simpa [List.count_append, List.count_cons, he, Ne.symm he] using hb

private theorem singles_delete (L v R : List α) (a : α)
    (ha : (L ++ a :: v ++ a :: R).count a = 2) :
    singles (L ++ a :: v ++ a :: R) = singles (L ++ v ++ R) := by
  have ha0 : (L ++ v ++ R).count a = 0 := by
    simp only [List.count_append, List.count_cons_self] at ha ⊢
    omega
  have hp : (fun b => decide ((L ++ a :: v ++ a :: R).count b = 1)) =
      (fun b => decide ((L ++ v ++ R).count b = 1)) := by
    funext b
    by_cases he : b = a
    · subst b; rw [ha,ha0] <;> decide
    · simp [List.count_append, List.count_cons, he, Ne.symm he]
  unfold singles
  rw [hp]
  simp only [List.filter_append, List.filter_cons, ha0, Nat.zero_ne_one, decide_false,
    Bool.false_eq_true, ↓reduceIte]

private theorem between_commute (f : α → M) (L v R : List α) (a : α)
    (hd : Double (L ++ a :: v ++ a :: R))
    (hg : Good f (L ++ a :: v ++ a :: R)) (hn : v.Nodup) :
    ∀ b ∈ v, Commute (f a) (f b) := by
  intro b hb
  have hc : v.count b = 1 := List.count_eq_one_of_mem hn hb
  have ha2 : (L ++ a :: v ++ a :: R).count a = 2 := by
    rcases hd a with h|h
    · simp only [List.count_append, List.count_cons_self] at h; omega
    · exact h
  have hab : b ≠ a := by
    intro h; subst b
    simp only [List.count_append, List.count_cons_self] at ha2
    omega
  have hext : b ∈ L ∨ b ∈ R := by
    by_contra hh
    have hL : L.count b = 0 := List.count_eq_zero.mpr (fun h => hh (Or.inl h))
    have hR : R.count b = 0 := List.count_eq_zero.mpr (fun h => hh (Or.inr h))
    have hh := hd b
    simp [List.count_append, List.count_cons, hab, Ne.symm hab, hc, hL, hR] at hh
  obtain ⟨v₁,v₂,hv⟩ := List.mem_iff_append.mp hb
  rcases hext with hL|hR
  · obtain ⟨L₁,L₂,hL⟩ := List.mem_iff_append.mp hL
    exact (hg b a (by
      simpa [hL,hv,List.append_assoc] using
        four_sublist b a b a L₁ L₂ v₁ v₂ R)).symm
  · obtain ⟨R₁,R₂,hR⟩ := List.mem_iff_append.mp hR
    exact hg a b (by
      simpa [hR,hv,List.append_assoc] using
        four_sublist a b a b L v₁ v₂ R₁ R₂)

omit [DecidableEq α] in
private theorem pair_delete_product (f : α → M) (L v R : List α) (a : α)
    (ha : f a * f a = 1) (hc : ∀ b ∈ v, Commute (f a) (f b)) :
    ((L ++ a :: v ++ a :: R).map f).prod = ((L ++ v ++ R).map f).prod := by
  have hm : Commute (f a) (v.map f).prod := Commute.list_prod_right _ _ (by
    intro b hb
    obtain ⟨c,hc',rfl⟩ := List.mem_map.mp hb
    exact hc c hc')
  simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons]
  calc
    _ = (L.map f).prod * (((f a * (v.map f).prod) * f a) * (R.map f).prod) := by
      simp only [mul_assoc]
    _ = (L.map f).prod * ((((v.map f).prod * f a) * f a) * (R.map f).prod) := by
      rw [hm.eq]
    _ = _ := by
      rw [mul_assoc (v.map f).prod (f a) (f a),ha,mul_one]
      simp only [mul_assoc]

private theorem interval_cancellation (f : α → M) (hf : ∀ a, f a * f a = 1)
    (w : List α) (hd : Double w) (hg : Good f w) (L v R : List α)
    (hw : w = L ++ v ++ R) : (v.map f).prod = ((singles v).map f).prod := by
  suffices h : ∀ N, ∀ w : List α, w.length = N → Double w → Good f w →
      ∀ L v R, w = L ++ v ++ R → (v.map f).prod = ((singles v).map f).prod by
    exact h w.length w rfl hd hg L v R hw
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro w hlen hd hg L v R hw
    by_cases hn : v.Nodup
    · have hs : singles v = v := List.filter_eq_self.mpr (by
        intro b hb
        simpa using List.count_eq_one_of_mem hn hb)
      rw [hs]
    · obtain ⟨p,a,m,z,hv,hm⟩ := gap_nodup v hn
      have heq : w = (L ++ p) ++ a :: m ++ a :: (z ++ R) := by
        simp only [hw,hv,List.append_assoc,List.cons_append]
      have hdm : Double ((L ++ p) ++ a :: m ++ a :: (z ++ R)) := heq ▸ hd
      have hgm : Good f ((L ++ p) ++ a :: m ++ a :: (z ++ R)) := heq ▸ hg
      have hc := between_commute f (L ++ p) m (z ++ R) a hdm hgm hm
      have ha : (p ++ a :: m ++ a :: z).count a = 2 := by
        have hh := hdm a
        simp only [List.count_append, List.count_cons_self] at hh ⊢
        omega
      have hsub : (L ++ p) ++ m ++ (z ++ R) <+ w := by
        rw [heq]
        simpa only [List.append_assoc,List.cons_append] using
          (((List.Sublist.refl m).append (List.sublist_cons_self a (z ++ R))).cons a).append_left (L ++ p)
      have hslen : ((L ++ p) ++ m ++ (z ++ R)).length < N := by
        rw [← hlen,heq]
        simp only [List.length_append,List.length_cons]
        omega
      have hi := ih _ hslen ((L ++ p) ++ m ++ (z ++ R)) rfl
        (double_delete (L ++ p) m (z ++ R) a hdm) (good_sublist f hg hsub)
        L (p ++ m ++ z) R (by simp [List.append_assoc])
      rw [hv,pair_delete_product f p m z a (hf a) hc,singles_delete p m z a ha]
      exact hi

end
end ShapiroList

namespace ShapiroPattern
open scoped Classical List
noncomputable section
open D5.S3.Combinatorics.Graph.SupportForestMoments.SupportAndEdgeWordReflection (edgeSwap)
open D5.S1.Words.Patterns.NoncrossingNonnestingGraphRecurrence (Crossing)

private theorem pattern_iff {α : Type*} (w : List α) (a b : α) :
    [a,b,a,b] <+ w ↔ ∃ i j k l : Fin w.length,
      i < j ∧ j < k ∧ k < l ∧ w[i] = a ∧ w[j] = b ∧ w[k] = a ∧ w[l] = b := by
  constructor
  · intro h
    obtain ⟨f,hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp h
    refine ⟨f 0,f 1,f 2,f 3,f.strictMono (show (0 : Fin 4) < 1 from by decide),
      f.strictMono (show (1 : Fin 4) < 2 from by decide),
      f.strictMono (show (2 : Fin 4) < 3 from by decide),?_,?_,?_,?_⟩
    · simpa using (hf 0).symm
    · simpa using (hf 1).symm
    · simpa using (hf 2).symm
    · simpa using (hf 3).symm
  · rintro ⟨i,j,k,l,hij,hjk,hkl,hi,hj,hk,hl⟩
    let f : Fin 4 ↪o Fin w.length := OrderEmbedding.ofStrictMono
      (fun t => ![i,j,k,l] t) (by
        intro r s hrs
        fin_cases r <;> fin_cases s <;> simp_all <;> omega)
    apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
    refine ⟨f,?_⟩
    intro t
    fin_cases t
    · change a = w[i]; exact hi.symm
    · change b = w[j]; exact hj.symm
    · change a = w[k]; exact hk.symm
    · change b = w[l]; exact hl.symm

private def Separated {n : ℕ} (w : List (Sym2 (Fin n))) : Prop :=
  ∀ a b, a ≠ b → [a,b,a,b] <+ w → ∀ x : Fin n, x ∈ a → x ∉ b

private theorem local_iff {n : ℕ} (w : List (Sym2 (Fin n)))
    (hd : ∀ a ∈ w, w.count a = 2) :
    ((∀ x : Fin n,
      (∀ a ∈ w.filter (fun e => x ∈ e), (w.filter (fun e => x ∈ e)).count a = 2) ∧
      ∀ i j k l : Fin (w.filter (fun e => x ∈ e)).length,
        (w.filter (fun e => x ∈ e))[i] = (w.filter (fun e => x ∈ e))[j] →
        (w.filter (fun e => x ∈ e))[k] = (w.filter (fun e => x ∈ e))[l] →
        (w.filter (fun e => x ∈ e))[i] ≠ (w.filter (fun e => x ∈ e))[k] →
        ¬ Crossing (i,j) (k,l)) ↔ Separated w) := by
  constructor
  · intro h a b hab hp x hxa hxb
    have hf := hp.filter (fun e => decide (x ∈ e))
    have hpat : [a,b,a,b] <+ w.filter (fun e => x ∈ e) := by simpa [hxa,hxb] using hf
    obtain ⟨i,j,k,l,hij,hjk,hkl,hi,hj,hk,hl⟩ := (pattern_iff _ a b).mp hpat
    exact (h x).2 i k j l (hi.trans hk.symm) (hj.trans hl.symm)
      (by simpa [hi,hj] using hab) (Or.inl ⟨hij,hjk,hkl⟩)
  · intro h x
    constructor
    · intro a ha
      have ham := List.mem_filter.mp ha
      rw [List.count_filter (p := fun e => decide (x ∈ e)) (a := a) (by simpa using ham.2)]
      exact hd a ham.1
    · intro i j k l hij hkl hne hc
      let v := w.filter (fun e => x ∈ e)
      have hix : x ∈ v[i] := by simpa [v] using (List.mem_filter.mp (List.getElem_mem (l := v) i.2)).2
      have hkx : x ∈ v[k] := by simpa [v] using (List.mem_filter.mp (List.getElem_mem (l := v) k.2)).2
      rcases hc with hc|hc
      · have hp : [v[i],v[k],v[i],v[k]] <+ v := (pattern_iff v _ _).mpr
          ⟨i,k,j,l,hc.1,hc.2.1,hc.2.2,rfl,rfl,hij.symm,hkl.symm⟩
        exact h _ _ hne (hp.trans List.filter_sublist) x hix hkx
      · have hp : [v[k],v[i],v[k],v[i]] <+ v := (pattern_iff v _ _).mpr
          ⟨k,i,l,j,hc.1,hc.2.1,hc.2.2,rfl,rfl,hkl.symm,hij.symm⟩
        exact h _ _ hne.symm (hp.trans List.filter_sublist) x hkx hix

private theorem swap_commute {n : ℕ} (a b : Sym2 (Fin n))
    (h : ∀ x : Fin n, x ∈ a → x ∉ b) : Commute (edgeSwap a) (edgeSwap b) := by
  apply Equiv.Perm.Disjoint.commute
  intro x
  by_cases hx : x ∈ a
  · right
    induction b using Sym2.ind with
    | _ u v =>
      have hh := h x hx
      simp only [Sym2.mem_iff,not_or] at hh
      exact Equiv.swap_apply_of_ne_of_ne hh.1 hh.2
  · left
    induction a using Sym2.ind with
    | _ u v =>
      simp only [Sym2.mem_iff,not_or] at hx
      exact Equiv.swap_apply_of_ne_of_ne hx.1 hx.2

end
end ShapiroPattern

namespace ShapiroPattern
open scoped Classical List
noncomputable section

private theorem skip_head_prefix {α : Type*} (a : α) (s p t : List α)
    (ha : a ∉ p) (h : a :: s <+ p ++ t) : a :: s <+ t := by
  induction p with
  | nil => simpa using h
  | cons b p ih =>
    have hn : a ≠ b := fun he => ha (by simp [he])
    exact ih (fun hp => ha (by simp [hp])) (h.of_cons_of_ne hn)

private theorem middle_mem_left {α : Type*} (a b : α) (L R : List α)
    (hab : b ≠ a) (haL : a ∉ L) (haR : a ∉ R)
    (h : [b,a,b] <+ L ++ a :: R) : b ∈ L := by
  by_contra hb
  have ht : [b,a,b] <+ a :: R := h.of_sublist_append_right (by
    intro c hc
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl <;> assumption)
  have hr : [b,a,b] <+ R := ht.of_cons_of_ne hab
  exact haR (hr.subset (by simp))

private theorem pattern_interval_count {α : Type*} [DecidableEq α]
    (a b : α) (L v R : List α) (hab : b ≠ a)
    (haL : a ∉ L) (hav : a ∉ v) (haR : a ∉ R)
    (hb : (L ++ a :: v ++ a :: R).count b = 2)
    (hp : [a,b,a,b] <+ L ++ a :: v ++ a :: R) : v.count b = 1 := by
  have hp' : [a,b,a,b] <+ L ++ a :: (v ++ a :: R) := by
    simpa only [List.append_assoc,List.cons_append] using hp
  have hm : [b,a,b] <+ v ++ a :: R := List.cons_sublist_cons.mp
    (skip_head_prefix a [b,a,b] L _ haL hp')
  have hbv : b ∈ v := middle_mem_left a b v R hab hav haR hm
  have hbr : b ∈ R := by
    have hrev : [b,a,b] <+ R.reverse ++ a :: v.reverse := by
      simpa [List.reverse_append,List.reverse_cons,List.append_assoc] using hm.reverse
    have := middle_mem_left a b R.reverse v.reverse hab
      (by simpa using haR) (by simpa using hav) hrev
    simpa using this
  have hc1 := List.count_pos_iff.mpr hbv
  have hc2 := List.count_pos_iff.mpr hbr
  simp only [List.count_append,List.count_cons_of_ne hab.symm] at hb
  omega

end
end ShapiroPattern

namespace ShapiroLeaf
open scoped Classical
noncomputable section
open D5.S3.Combinatorics.Graph.SupportForestMoments.SupportAndEdgeWordReflection (edgeSwap)

private theorem forest_leaf {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.IsAcyclic)
    (he : ∃ u v, G.Adj u v) :
    ∃ l p, G.Adj l p ∧ ∀ x, G.Adj l x → x = p := by
  obtain ⟨u₀,v₀,huv⟩ := he
  letI : Nonempty (Fin n) := ⟨u₀⟩
  obtain ⟨u,v,p,hp,hmax⟩ := SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  have hpos : 0 < p.length := by
    have hle : 1 ≤ p.length := by
      simpa using hmax u₀ v₀ huv.toWalk huv.isPath_toWalk
    omega
  have hn : ¬ p.Nil := by
    intro h
    have := SimpleGraph.Walk.length_eq_zero_iff.mpr h
    omega
  refine ⟨u,p.snd,p.adj_snd hn,?_⟩
  intro w hadj
  apply hG.eq_snd_of_adj_start hp hadj
  have : ¬ (p.cons hadj.symm).IsPath := by
    intro hh
    have hle := hmax w v (p.cons hadj.symm) hh
    simp only [SimpleGraph.Walk.length_cons] at hle
    omega
  by_contra hs
  exact this (hp.cons hs)

private theorem leaf_edge_unique {n : ℕ} (G : SimpleGraph (Fin n))
    (l p : Fin n) (h : ∀ x, G.Adj l x → x = p)
    (a : Sym2 (Fin n)) (ha : a ∈ G.edgeSet) (hl : l ∈ a) : a = s(l,p) := by
  induction a using Sym2.ind with
  | _ u v =>
    have he := G.mem_edgeSet.mp ha
    rcases Sym2.mem_iff.mp hl with hl|hl
    · subst u
      rw [h v he]
    · subst v
      rw [h u he.symm,Sym2.eq_swap]

private theorem leaf_interval {n : ℕ} (l p : Fin n) (U V Z : Equiv.Perm (Fin n))
    (hU : U l = l) (hV : V l = l) (hZ : Z l = l)
    (hprod : U * Equiv.swap l p * V * Equiv.swap l p * Z = 1) :
    V p = p ∧ U * V * Z = 1 := by
  have hh := congrArg (fun f : Equiv.Perm (Fin n) => f l) hprod
  have hx : U (Equiv.swap l p (V p)) = U l := by
    simpa only [Equiv.Perm.mul_apply,hZ,Equiv.swap_apply_left,Equiv.Perm.one_apply,hU] using hh
  have hfix : V p = p := by
    have h := congrArg (Equiv.swap l p) (U.injective hx)
    simpa using h
  have hiL : V⁻¹ l = l :=
    Equiv.Perm.inv_eq_iff_eq.mpr (id (Eq.symm hV))
  have hiP : V⁻¹ p = p :=
    Equiv.Perm.inv_eq_iff_eq.mpr (id (Eq.symm hfix))
  have hc : Equiv.swap l p * V = V * Equiv.swap l p := by
    rw [Equiv.swap_mul_eq_mul_swap,hiL,hiP]
  constructor
  · exact hfix
  · calc
      U * V * Z = U * (V * (Equiv.swap l p * Equiv.swap l p)) * Z := by simp
      _ = U * (Equiv.swap l p * V * Equiv.swap l p) * Z := by rw [← mul_assoc V,← hc]
      _ = 1 := by simpa only [mul_assoc] using hprod

end
end ShapiroLeaf
namespace ShapiroMain
open scoped Classical List
noncomputable section
open D5.S3.Combinatorics.Graph.SupportForestMoments.SupportAndEdgeWordReflection (edgeSwap)
open ShapiroPattern (Separated)

private theorem split_two {α : Type*} [DecidableEq α] (a : α) (w : List α)
    (hc : w.count a = 2) :
    ∃ L v R, w = L ++ a :: v ++ a :: R ∧ a ∉ L ∧ a ∉ v ∧ a ∉ R := by
  induction w with
  | nil => simp at hc
  | cons b w ih =>
    by_cases hba : b = a
    · subst b
      have hm : a ∈ w := List.count_pos_iff.mp (by simp only [List.count_cons_self] at hc; omega)
      obtain ⟨v,R,rfl⟩ := List.mem_iff_append.mp hm
      refine ⟨[],v,R,by simp,by simp,?_,?_⟩ <;>
        apply List.count_eq_zero.mp <;>
        simp only [List.count_cons_self,List.count_append] at hc <;> omega
    · have ht : w.count a = 2 := by simpa [List.count_cons,hba] using hc
      obtain ⟨L,v,R,heq,hL,hv,hR⟩ := ih ht
      exact ⟨b::L,v,R,by simp [heq],by simp [hba,Ne.symm hba,hL],hv,hR⟩

private theorem singles_nodup {α : Type*} [DecidableEq α] (w : List α) :
    (ShapiroList.singles w).Nodup := by
  apply List.nodup_iff_count_eq_one.mpr
  intro a ha
  have hh := List.mem_filter.mp ha
  have hc : w.count a = 1 := by simpa using hh.2
  exact (List.count_filter (p := fun a => decide (w.count a = 1)) (by simp [hc])).trans hc

private theorem swap_involution {n : ℕ} (a : Sym2 (Fin n)) :
    edgeSwap a * edgeSwap a = 1 := by
  induction a using Sym2.ind with
  | _ u v => exact Equiv.swap_mul_self u v

private theorem separated_good {n : ℕ} (w : List (Sym2 (Fin n)))
    (h : Separated w) : ShapiroList.Good edgeSwap w := by
  intro a b hp
  by_cases hab : a = b
  · subst b; exact Commute.refl _
  · exact ShapiroPattern.swap_commute a b (h a b hab hp)

private theorem leaf_disjoint {n : ℕ} (G : SimpleGraph (Fin n)) (l p : Fin n)
    (hleaf : ∀ x, G.Adj l x → x = p) (b : Sym2 (Fin n))
    (hb : b ∈ G.edgeSet) (hne : b ≠ s(l,p)) (hpb : p ∉ b) :
    ∀ x : Fin n, x ∈ s(l,p) → x ∉ b := by
  intro x hx hxb
  rcases Sym2.mem_iff.mp hx with hx|hx
  · subst x
    exact hne (ShapiroLeaf.leaf_edge_unique G l p hleaf b hb hxb)
  · subst x
    exact hpb hxb

private theorem identity_separated {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.IsAcyclic)
    (w : List (Sym2 (Fin n))) (hw : ∀ a ∈ w, a ∈ G.edgeSet)
    (hused : ∀ a ∈ G.edgeSet, a ∈ w) (hd : ∀ a ∈ w, w.count a = 2)
    (hp : ((w).map edgeSwap).prod = 1) : Separated w := by
  suffices main : ∀ N, ∀ (G : SimpleGraph (Fin n)), G.IsAcyclic →
      ∀ w : List (Sym2 (Fin n)), w.length = N →
      (∀ a ∈ w, a ∈ G.edgeSet) → (∀ a ∈ G.edgeSet, a ∈ w) →
      (∀ a ∈ w, w.count a = 2) → ((w).map edgeSwap).prod = 1 → Separated w by
    exact main w.length G hG w rfl hw hused hd hp
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro G hG w hlen hw hused hd hp
    by_cases hn : w = []
    · subst w
      intro a b hab hpat
      have hh := hpat.length_le
      simp at hh
    · obtain ⟨a,ha⟩ := List.exists_mem_of_ne_nil w hn
      have he : ∃ u v, G.Adj u v := by
        induction a using Sym2.ind with
        | _ u v => exact ⟨u,v,G.mem_edgeSet.mp (hw _ ha)⟩
      obtain ⟨l,p,hlp,hleaf⟩ := ShapiroLeaf.forest_leaf G hG he
      let a := s(l,p)
      have hae : a ∈ G.edgeSet := G.mem_edgeSet.mpr hlp
      have hac : w.count a = 2 := hd a (hused a hae)
      obtain ⟨L,v,R,heq,haL,hav,haR⟩ := split_two a w hac
      have hletter : ∀ b ∈ L ++ v ++ R, b ∈ G.edgeSet ∧ b ≠ a := by
        intro b hb
        have hbw : b ∈ w := by simp only [heq,List.mem_append,List.mem_cons] at *; tauto
        refine ⟨hw b hbw,?_⟩
        intro h; subst b
        simp only [List.mem_append] at hb
        rcases hb with (hb|hb)|hb
        · exact haL hb
        · exact hav hb
        · exact haR hb
      have hfixL : ((L).map edgeSwap).prod l = l := ShapiroProbe.word_fixed L l (by
        intro b hb hbl
        exact (hletter b (by simp [hb])).2
          (ShapiroLeaf.leaf_edge_unique G l p hleaf b (hw b (by simp [heq,hb])) hbl))
      have hfixV : ((v).map edgeSwap).prod l = l := ShapiroProbe.word_fixed v l (by
        intro b hb hbl
        exact (hletter b (by simp [hb])).2
          (ShapiroLeaf.leaf_edge_unique G l p hleaf b (hw b (by simp [heq,hb])) hbl))
      have hfixR : ((R).map edgeSwap).prod l = l := ShapiroProbe.word_fixed R l (by
        intro b hb hbl
        exact (hletter b (by simp [hb])).2
          (ShapiroLeaf.leaf_edge_unique G l p hleaf b (hw b (by simp [heq,hb])) hbl))
      have hprod : ((L).map edgeSwap).prod * Equiv.swap l p * ((v).map edgeSwap).prod * Equiv.swap l p * ((R).map edgeSwap).prod = 1 := by
        simpa [edgeSwap, heq, a, List.map_append, List.prod_append, mul_assoc] using hp
      obtain ⟨hvp,hdel⟩ := ShapiroLeaf.leaf_interval l p (((L).map edgeSwap).prod) (((v).map edgeSwap).prod) (((R).map edgeSwap).prod)
        hfixL hfixV hfixR hprod
      have hp' : ((L ++ v ++ R).map edgeSwap).prod = 1 := by
        simpa [List.map_append,List.prod_append,mul_assoc] using hdel
      have hfilter : w.filter (fun b => b ≠ a) = L ++ v ++ R := by
        have hf (s : List (Sym2 (Fin n))) (hs : a ∉ s) : s.filter (fun b => b ≠ a) = s :=
          List.filter_eq_self.mpr (fun b hb => by simp only [decide_eq_true_eq]; intro h; exact hs (h ▸ hb))
        rw [heq]
        simp only [List.filter_append,List.filter_cons,ne_self_iff_false,decide_false,
          Bool.false_eq_true,↓reduceIte,hf L haL,hf v hav,hf R haR]
      have hletters' : ∀ b ∈ L ++ v ++ R, b ∈ (G.deleteEdges {a}).edgeSet := by
        intro b hb
        rw [SimpleGraph.edgeSet_deleteEdges]
        exact ⟨(hletter b hb).1, by simpa using (hletter b hb).2⟩
      have hused' : ∀ b ∈ (G.deleteEdges {a}).edgeSet, b ∈ L ++ v ++ R := by
        intro b hb
        rw [SimpleGraph.edgeSet_deleteEdges] at hb
        rw [← hfilter]
        exact List.mem_filter.mpr ⟨hused b hb.1,by simpa using hb.2⟩
      have hd' : ∀ b ∈ L ++ v ++ R, (L ++ v ++ R).count b = 2 := by
        intro b hb
        rw [← hfilter,List.count_filter (p := fun c => decide (c ≠ a)) (a := b) (by simpa using (hletter b hb).2)]
        exact hd b (by simp [heq] at *; tauto)
      have hshort : (L ++ v ++ R).length < N := by
        rw [← hlen,heq]
        simp only [List.length_append,List.length_cons]
        omega
      have hsep := ih _ hshort (G.deleteEdges {a})
        (hG.anti (G.deleteEdges_le {a})) (L ++ v ++ R) rfl hletters' hused' hd' hp'
      have hdouble : ShapiroList.Double (L ++ v ++ R) := by
        intro b
        by_cases hb : b ∈ L ++ v ++ R
        · exact Or.inr (hd' b hb)
        · exact Or.inl (List.count_eq_zero.mpr hb)
      have hinterval := ShapiroList.interval_cancellation edgeSwap swap_involution
        (L ++ v ++ R) hdouble (separated_good _ hsep) L v R rfl
      have hsfix : ((ShapiroList.singles v).map edgeSwap).prod p = p := by
        change ((ShapiroList.singles v).map edgeSwap).prod p = p
        rw [← hinterval]
        exact hvp
      have hres := (ShapiroProbe.distinct_forest_fixed G hG (ShapiroList.singles v)
        (by intro b hb; exact (hletter b (by
          have := (List.mem_filter.mp hb).1; simp [this])).1) (singles_nodup v) p).mp hsfix
      have hnew : ∀ b, b ≠ a → w.count b = 2 →
          ([a,b,a,b] <+ w ∨ [b,a,b,a] <+ w) → ∀ x : Fin n, x ∈ a → x ∉ b := by
        intro b hba hbc hpat
        have hc : v.count b = 1 := by
          rcases hpat with hab|hba'
          · exact ShapiroPattern.pattern_interval_count a b L v R hba haL hav haR
              (heq ▸ hbc) (heq ▸ hab)
          · have hrev : w.reverse = R.reverse ++ a :: v.reverse ++ a :: L.reverse := by
              simp [heq,List.reverse_append,List.reverse_cons,List.append_assoc]
            have hh := ShapiroPattern.pattern_interval_count a b R.reverse v.reverse L.reverse hba
              (by simpa using haR) (by simpa using hav) (by simpa using haL)
              (by rw [← hrev]; simpa using hbc)
              (by rw [← hrev]; simpa using hba'.reverse)
            simpa using hh
        have hbs : b ∈ ShapiroList.singles v := List.mem_filter.mpr
          ⟨List.count_pos_iff.mp (by omega),by simp [hc]⟩
        exact leaf_disjoint G l p hleaf b (hw b (by
          have hbv := (List.mem_filter.mp hbs).1
          simp [heq,hbv])) hba (hres b hbs)
      intro b c hbc hpat x hxb hxc
      by_cases hb : b = a
      · subst b
        exact hnew c hbc.symm (hd c (hpat.subset (by simp))) (Or.inl hpat) x hxb hxc
      · by_cases hc : c = a
        · subst c
          exact hnew b hb (hd b (hpat.subset (by simp))) (Or.inr hpat) x hxc hxb
        · have hh := hpat.filter (fun b => decide (b ≠ a))
          have hpat' : [b,c,b,c] <+ L ++ v ++ R := by
            rw [← hfilter]
            simpa [hb,hc] using hh
          exact hsep b c hbc hpat' x hxb hxc

end
end ShapiroMain
open scoped Classical
noncomputable section
open D5.S3.Combinatorics.Graph.SupportForestMoments.SupportAndEdgeWordReflection (edgeSwap)

theorem result : claim := by
  intro n T w hT hw hlen hused
  constructor
  · intro hp
    have hm := ShapiroProbe.multiplicity_two T hT.isAcyclic w hw hlen hused hp
    refine ⟨hm, ?_⟩
    exact (ShapiroPattern.local_iff w (fun a ha => hm a (hw a ha))).mpr
      (ShapiroMain.identity_separated T hT.isAcyclic w
        (fun a ha => T.mem_edgeFinset.mp (hw a ha))
        (fun a ha => hused a (T.mem_edgeFinset.mpr ha))
        (fun a ha => hm a (hw a ha)) hp)
  · intro h
    have hd : ∀ a ∈ w, w.count a = 2 := fun a ha => h.1 a (hw a ha)
    have hsep := (ShapiroPattern.local_iff w hd).mp h.2
    have hdouble : ShapiroList.Double w := by
      intro a
      by_cases ha : a ∈ w
      · exact Or.inr (hd a ha)
      · exact Or.inl (List.count_eq_zero.mpr ha)
    have heq := ShapiroList.interval_cancellation edgeSwap ShapiroMain.swap_involution
      w hdouble (ShapiroMain.separated_good w hsep) [] w [] (by simp)
    have hnil : ShapiroList.singles w = [] := List.filter_eq_nil_iff.mpr (by
      intro a ha
      simpa [hd a ha])
    simpa [hnil] using heq

end


end D5.S3.Combinatorics.Graph.SupportForestMoments.ShapiroTreeIdentityWords
