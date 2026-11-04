/- GID: D5/S1/Words/Sequenceability/AdaptiveMergeSignedFork
   generality: G
   mirror-B: D5/B/S1/Words/Sequenceability/AdaptiveMergeSignedFork
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Generic two-collision signed-fork obstruction and conditional adaptive repair. -/

import D5.S1.Words.Sequenceability.AdaptiveMergePrefix

set_option autoImplicit false
noncomputable section
namespace D5.S1.Words.Sequenceability.AdaptiveMergeSignedFork
open _root_.D5.S1.Words.Sequenceability.AdaptiveMergePrefix
open scoped Classical BigOperators
variable {G : Type*} [AddCommGroup G]

def ListSubset (A : Finset G) (U : List G) : Prop :=
  U.Nodup ∧ ∀ z ∈ U, z ∈ A

def ListDisjoint (U V : List G) : Prop :=
  ∀ z, z ∈ U → z ∈ V → False

private def ListMixedFork (A : Finset G) (x y : G) : Prop :=
  ∃ U V : List G,
    ListSubset (A.erase x) U ∧ ListSubset (A.erase x) V ∧
    ListDisjoint U V ∧ U ≠ [] ∧ V ≠ [] ∧ y ∈ V ∧
    U.sum = -x ∧ V.sum = x

/-- Equal-sign signed-fork data `E(x,y)`. -/
private def ListEqualFork (A : Finset G) (x y : G) : Prop :=
  ∃ U V : List G,
    ListSubset ((A.erase x).erase y) U ∧
    ListSubset ((A.erase x).erase y) V ∧
    ListDisjoint U V ∧ U ≠ [] ∧ V ≠ [] ∧
    U.sum = -x ∧ V.sum = -x

/-- Mixed signed fork, on literal coefficient-one subsets of the original alphabet. -/
def MixedFork (A : Finset G) (x y : G) : Prop :=
  ∃ U V : Finset G, U ⊆ A.erase x ∧ V ⊆ A.erase x ∧ Disjoint U V ∧
    U.Nonempty ∧ V.Nonempty ∧ y ∈ V ∧ (∑ z ∈ U, z) = -x ∧ (∑ z ∈ V, z) = x

/-- Equal-sign signed fork on subsets avoiding both merge labels. -/
def EqualFork (A : Finset G) (x y : G) : Prop :=
  ∃ U V : Finset G, U ⊆ (A.erase x).erase y ∧ V ⊆ (A.erase x).erase y ∧
    Disjoint U V ∧ U.Nonempty ∧ V.Nonempty ∧
    (∑ z ∈ U, z) = -x ∧ (∑ z ∈ V, z) = -x

/-- Static unordered fork edge, before choosing any compressed order. -/
def ForkEdge (A : Finset G) (x y : G) : Prop :=
  MixedFork A x y ∨ MixedFork A y x ∨ EqualFork A x y ∨ EqualFork A y x

private lemma mixed_from_list {A : Finset G} {x y : G}
    (h : ListMixedFork A x y) : MixedFork A x y := by
  rcases h with ⟨U,V,hU,hV,hd,hUne,hVne,hy,hUs,hVs⟩
  refine ⟨U.toFinset,V.toFinset,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro z hz; exact hU.2 z (List.mem_toFinset.mp hz)
  · intro z hz; exact hV.2 z (List.mem_toFinset.mp hz)
  · apply Finset.disjoint_left.mpr
    intro z hz hz'
    exact hd z (List.mem_toFinset.mp hz) (List.mem_toFinset.mp hz')
  · simpa using hUne
  · simpa using hVne
  · exact List.mem_toFinset.mpr hy
  · simpa using (List.sum_toFinset (fun z : G => z) hU.1).trans (by simpa using hUs)
  · simpa using (List.sum_toFinset (fun z : G => z) hV.1).trans (by simpa using hVs)

private lemma equal_from_list {A : Finset G} {x y : G}
    (h : ListEqualFork A x y) : EqualFork A x y := by
  rcases h with ⟨U,V,hU,hV,hd,hUne,hVne,hUs,hVs⟩
  refine ⟨U.toFinset,V.toFinset,?_,?_,?_,?_,?_,?_,?_⟩
  · intro z hz; exact hU.2 z (List.mem_toFinset.mp hz)
  · intro z hz; exact hV.2 z (List.mem_toFinset.mp hz)
  · apply Finset.disjoint_left.mpr
    intro z hz hz'
    exact hd z (List.mem_toFinset.mp hz) (List.mem_toFinset.mp hz')
  · simpa using hUne
  · simpa using hVne
  · simpa using (List.sum_toFinset (fun z : G => z) hU.1).trans (by simpa using hUs)
  · simpa using (List.sum_toFinset (fun z : G => z) hV.1).trans (by simpa using hVs)

private lemma listDisjoint_append_left {U V W : List G}
    (hUV : ListDisjoint U V) (hUW : ListDisjoint U W) :
    ListDisjoint U (V ++ W) := by
  intro z hzU hzVW
  rcases List.mem_append.mp hzVW with hzV | hzW
  · exact hUV z hzU hzV
  · exact hUW z hzU hzW

private lemma listSubset_append {A : Finset G} {U V : List G}
    (hU : ListSubset A U) (hV : ListSubset A V)
    (hUV : ListDisjoint U V) : ListSubset A (U ++ V) := by
  refine ⟨?_, ?_⟩
  · exact List.Nodup.append hU.1 hV.1 (by
      intro z hzU hzV
      exact hUV z hzU hzV)
  · intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact hU.2 z hz
    · exact hV.2 z hz

private lemma list_subset_of_prefix {A : Finset G} {P U : List G}
    (h : ListSubset A (P ++ U)) : ListSubset A U := by
  refine ⟨h.1.sublist (List.sublist_append_right P U), ?_⟩
  intro z hz
  exact h.2 z (by simp [hz])

private lemma suffix_nested {L S T : List G} {P Q : List G}
    (hS : L = P ++ S) (hT : L = Q ++ T) :
    (S.length ≤ T.length → ∃ W, T = W ++ S) ∧
      (T.length ≤ S.length → ∃ W, S = W ++ T) := by
  constructor
  · intro hlen
    obtain ⟨W, hW⟩ :=
      List.suffix_of_suffix_length_le ⟨P, hS.symm⟩ ⟨Q, hT.symm⟩ hlen
    exact ⟨W, hW.symm⟩
  · intro hlen
    obtain ⟨W, hW⟩ :=
      List.suffix_of_suffix_length_le ⟨Q, hT.symm⟩ ⟨P, hS.symm⟩ hlen
    exact ⟨W, hW.symm⟩

private lemma mixed_of_nested_suffixes {A : Finset G} {x y : G} {S W : List G}
    (hyA : y ∈ A) (hxy : x ≠ y)
    (hT : ListSubset ((A.erase x).erase y) (W ++ S))
    (hSne : S ≠ []) (hSsum : S.sum = -x)
    (hTsum : (W ++ S).sum = -y) : ListMixedFork A x y := by
  have hS : ListSubset (A.erase x) S := by
    refine ⟨hT.1.of_append_right, ?_⟩
    intro z hz
    exact Finset.mem_of_mem_erase (hT.2 z (by simp [hz]))
  have hW : ListSubset (A.erase x) W := by
    refine ⟨hT.1.of_append_left, ?_⟩
    intro z hz
    exact Finset.mem_of_mem_erase (hT.2 z (by simp [hz]))
  have hyS : y ∉ S := by
    intro hy
    exact (Finset.mem_erase.mp (hT.2 y (by simp [hy]))).1 rfl
  have hyW : y ∉ W := by
    intro hy
    exact (Finset.mem_erase.mp (hT.2 y (by simp [hy]))).1 rfl
  have hSW : ListDisjoint S W := by
    intro z hzS hzW
    exact (List.disjoint_of_nodup_append hT.1) hzW hzS
  have hyone : ListSubset (A.erase x) [y] := by
    refine ⟨by simp, ?_⟩
    intro z hz
    have hzy : z = y := by simpa using hz
    subst z
    exact Finset.mem_erase.mpr ⟨Ne.symm hxy, hyA⟩
  have hV : ListSubset (A.erase x) (W ++ [y]) :=
    listSubset_append hW hyone (by
      intro z hzW hzY
      have hzy : z = y := by simpa using hzY
      subst z
      exact hyW hzW)
  have hSV : ListDisjoint S (W ++ [y]) :=
    listDisjoint_append_left hSW (by
      intro z hzS hzY
      have hzy : z = y := by simpa using hzY
      subst z
      exact hyS hzS)
  have hsumV : (W ++ [y]).sum = x := by
    calc
      (W ++ [y]).sum = W.sum + y := by simp
      _ = (W.sum + S.sum) + x + y := by rw [hSsum]; abel
      _ = -y + x + y := by rw [← List.sum_append, hTsum]
      _ = x := by abel
  exact ⟨S, W ++ [y], hS, hV, hSV, hSne, by simp, by simp, hSsum, hsumV⟩

private lemma mixed_of_left_collisions {A : Finset G} {x y : G} {L : List G}
    (hxy : x ≠ y) (hxA : x ∈ A) (hyA : y ∈ A)
    (hL : ListSubset ((A.erase x).erase y) L)
    (hS : LeftCollision L x) (hT : LeftCollision L y) :
    ListMixedFork A x y ∨ ListMixedFork A y x := by
  rcases hS with ⟨P, S, hPs, hSne, hSsum⟩
  rcases hT with ⟨Q, T, hQt, hTne, hTsum⟩
  have hS0 : ListSubset ((A.erase x).erase y) S := by
    simpa [hPs] using list_subset_of_prefix (show ListSubset ((A.erase x).erase y) (P ++ S) by simpa [← hPs] using hL)
  have hT0 : ListSubset ((A.erase x).erase y) T := by
    exact list_subset_of_prefix (show ListSubset ((A.erase x).erase y) (Q ++ T) by simpa [← hQt] using hL)
  obtain ⟨hST, hTS⟩ := suffix_nested hPs hQt
  by_cases hlen : S.length ≤ T.length
  · obtain ⟨W, hWT⟩ := hST hlen
    left
    exact mixed_of_nested_suffixes (W := W) hyA hxy (by rw [← hWT]; exact hT0) hSne hSsum (by rw [← hWT]; exact hTsum)
  · obtain ⟨W, hWS⟩ := hTS (by omega)
    right
    exact mixed_of_nested_suffixes (W := W) hxA (Ne.symm hxy)
      (by rw [← hWS]; simpa only [Finset.erase_right_comm] using hS0)
      hTne hTsum (by rw [← hWS]; exact hSsum)

private lemma equal_of_left_right_collisions {A : Finset G} {x y : G}
    {L R : List G} (hLR : ListDisjoint L R)
    (hL : ListSubset ((A.erase x).erase y) L)
    (hR : ListSubset ((A.erase x).erase y) R)
    (hS : ∃ P S : List G, L = P ++ S ∧ S ≠ [] ∧ S.sum = -x)
    (hT : ∃ T Q : List G, R = T ++ Q ∧ T ≠ [] ∧ T.sum = -x) :
    ListEqualFork A x y := by
  rcases hS with ⟨P, S, hPs, hSne, hSsum⟩
  rcases hT with ⟨T, Q, hTQ, hTne, hTsum⟩
  have hSn : S.Nodup := (show S <:+ L from ⟨P, hPs.symm⟩).nodup hL.1
  have hTn : T.Nodup := (show T <+: R from ⟨Q, hTQ.symm⟩).nodup hR.1
  have hS0 : ListSubset ((A.erase x).erase y) S := by
    refine ⟨hSn, ?_⟩
    intro z hz
    exact hL.2 z (by simp [hPs, hz])
  have hT0 : ListSubset ((A.erase x).erase y) T := by
    refine ⟨hTn, ?_⟩
    intro z hz
    exact hR.2 z (by simp [hTQ, hz])
  have hST : ListDisjoint S T := by
    intro z hzS hzT
    exact hLR z (by simp [hPs, hzS]) (by simp [hTQ, hzT])
  exact ⟨S, T, hS0, hT0, hST, hSne, hTne, hSsum, hTsum⟩

private lemma listSubset_reverse {A : Finset G} {U : List G} (hU : ListSubset A U) :
    ListSubset A U.reverse := by
  refine ⟨List.nodup_reverse.mpr hU.1, ?_⟩
  intro z hz
  exact hU.2 z (List.mem_reverse.mp hz)

private lemma rightCollision_to_left {R : List G} {x : G}
    (h : RightCollision R x) : LeftCollision R.reverse x := by
  rcases h with ⟨S, Q, hSQ, hSne, hsum⟩
  refine ⟨Q.reverse, S.reverse, ?_, ?_, ?_⟩
  · simpa [hSQ, List.reverse_append]
  · simpa using hSne
  · simpa [List.sum_reverse] using hsum

theorem two_collision_fork {A : Finset G} {a b : G} {L R : List G}
    (haA : a ∈ A) (hbA : b ∈ A) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : a ≠ b)
    (hL : ListSubset ((A.erase a).erase b) L)
    (hR : ListSubset ((A.erase a).erase b) R)
    (hLR : ListDisjoint L R)
    (hgood : Good (L ++ [a + b] ++ R))
    (hbadab : ¬ Good (L ++ [a, b] ++ R))
    (hbadba : ¬ Good (L ++ [b, a] ++ R)) :
    ForkEdge A a b := by
  have hgood' : Good (L ++ [b + a] ++ R) := by simpa [add_comm] using hgood
  have hL' : ListSubset ((A.erase b).erase a) L := by simpa [Finset.erase_right_comm] using hL
  have hR' : ListSubset ((A.erase b).erase a) R := by simpa [Finset.erase_right_comm] using hR
  obtain hxa | hxb := bad_expand_implies_collision ha0 hb0 hgood hbadab
  · obtain hya | hyb := bad_expand_implies_collision hb0 ha0 hgood' hbadba
    · rcases mixed_of_left_collisions hab haA hbA hL hxa hya with hM | hM
      · exact Or.inl (mixed_from_list hM)
      · exact Or.inr (Or.inl (mixed_from_list hM))
    · exact Or.inr (Or.inr (Or.inl (equal_from_list (equal_of_left_right_collisions hLR hL hR hxa hyb))))
  · obtain hya | hyb := bad_expand_implies_collision hb0 ha0 hgood' hbadba
    · exact Or.inr (Or.inr (Or.inr (equal_from_list (equal_of_left_right_collisions hLR hL' hR' hya hxb))))
    · rcases mixed_of_left_collisions (Ne.symm hab) hbA haA (listSubset_reverse hR')
        (rightCollision_to_left hxb) (rightCollision_to_left hyb) with hM | hM
      · exact Or.inr (Or.inl (mixed_from_list hM))
      · exact Or.inl (mixed_from_list hM)



end D5.S1.Words.Sequenceability.AdaptiveMergeSignedFork
