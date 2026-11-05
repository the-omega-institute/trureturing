/- GID: D5/S1/Words/Sequenceability/AdaptiveMergeZeroCrossing
   generality: G
   mirror-B: D5/B/S1/Words/Sequenceability/AdaptiveMergeZeroCrossing
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Proper zero-sum crossings and explicit structural fork exclusions. -/

import D5.S1.Words.Sequenceability.AdaptiveMergeSignedFork

set_option autoImplicit false
noncomputable section
namespace D5.S1.Words.Sequenceability.AdaptiveMergeZeroCrossing
open _root_.D5.S1.Words.Sequenceability.AdaptiveMergeSignedFork
open scoped Classical BigOperators
variable {G : Type*} [AddCommGroup G]

/-- Three nonempty Venn regions, at least one a singleton, between proper zero sets. -/
def ProperZeroCrossing (A : Finset G) : Prop :=
  ∃ C D : Finset G,
    C ⊆ A ∧ D ⊆ A ∧ C.Nonempty ∧ D.Nonempty ∧ C ≠ A ∧ D ≠ A ∧
    (∑ z ∈ C, z) = 0 ∧ (∑ z ∈ D, z) = 0 ∧
    (C ∩ D).Nonempty ∧ (C \ D).Nonempty ∧ (D \ C).Nonempty ∧
    ((C ∩ D).card = 1 ∨ (C \ D).card = 1 ∨ (D \ C).card = 1)

def NoSingletonZeroCrossing (A : Finset G) : Prop := ¬ ProperZeroCrossing A

/-- A mixed fork has singleton difference; properness is witnessed by y and x. -/
private lemma mixed_fork_crossing {A : Finset G} {x y : G}
    (hxy : x ≠ y) (hxA : x ∈ A) (hyA : y ∈ A)
    (hM : MixedFork A x y) : ProperZeroCrossing A := by
  rcases hM with ⟨U,V,hU,hV,hUV,hUne,hVne,hyV,hUs,hVs⟩
  have hxU : x ∉ U := fun hz => (Finset.mem_erase.mp (hU hz)).1 rfl
  have hxV : x ∉ V := fun hz => (Finset.mem_erase.mp (hV hz)).1 rfl
  have hyU : y ∉ U := fun hz => Finset.disjoint_left.mp hUV hz hyV
  have hUA : U ⊆ A := fun z hz => Finset.mem_of_mem_erase (hU hz)
  have hVA : V ⊆ A := fun z hz => Finset.mem_of_mem_erase (hV hz)
  have hC : insert x U ≠ A := by
    intro heq
    have := heq ▸ hyA
    simpa [hyU, Ne.symm hxy] using this
  have hD : U ∪ V ≠ A := by
    intro heq
    have := heq ▸ hxA
    simpa [hxU,hxV] using this
  have hInt : insert x U ∩ (U ∪ V) = U := by
    ext z
    have hd : z ∈ U → z ∈ V → False :=
      fun h1 h2 => Finset.disjoint_left.mp hUV h1 h2
    by_cases hz : z = x <;> simp_all <;> tauto
  have hLeft : insert x U \ (U ∪ V) = {x} := by
    ext z
    by_cases hz : z = x <;> simp_all
  have hRight : (U ∪ V) \ insert x U = V := by
    ext z
    have hd : z ∈ U → z ∈ V → False :=
      fun h1 h2 => Finset.disjoint_left.mp hUV h1 h2
    by_cases hz : z = x <;> simp_all <;> tauto
  refine ⟨insert x U, U ∪ V, Finset.insert_subset hxA hUA,
    Finset.union_subset hUA hVA, Finset.insert_nonempty _ _,
    hUne.mono Finset.subset_union_left, hC,hD,?_,?_,?_,?_,?_,?_⟩
  · simp [Finset.sum_insert, hxU, hUs]
  · rw [Finset.sum_union hUV, hUs, hVs]; exact neg_add_cancel x
  · rwa [hInt]
  · rw [hLeft]; simp
  · rwa [hRight]
  · exact Or.inr (Or.inl (by rw [hLeft]; simp))

/-- An equal-sign fork has singleton intersection; the omitted y proves properness. -/
private lemma equal_fork_crossing {A : Finset G} {x y : G}
    (hxy : x ≠ y) (hxA : x ∈ A) (hyA : y ∈ A)
    (hE : EqualFork A x y) : ProperZeroCrossing A := by
  rcases hE with ⟨U,V,hU,hV,hUV,hUne,hVne,hUs,hVs⟩
  have hxU : x ∉ U := fun hz =>
    (Finset.mem_erase.mp (Finset.mem_of_mem_erase (hU hz))).1 rfl
  have hxV : x ∉ V := fun hz =>
    (Finset.mem_erase.mp (Finset.mem_of_mem_erase (hV hz))).1 rfl
  have hyU : y ∉ U := fun hz => (Finset.mem_erase.mp (hU hz)).1 rfl
  have hyV : y ∉ V := fun hz => (Finset.mem_erase.mp (hV hz)).1 rfl
  have hUA : U ⊆ A := fun z hz =>
    Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (hU hz))
  have hVA : V ⊆ A := fun z hz =>
    Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (hV hz))
  have hC : insert x U ≠ A := by
    intro heq
    have := heq ▸ hyA
    simpa [hyU, Ne.symm hxy] using this
  have hD : insert x V ≠ A := by
    intro heq
    have := heq ▸ hyA
    simpa [hyV, Ne.symm hxy] using this
  have hInt : insert x U ∩ insert x V = {x} := by
    ext z
    have hd : z ∈ U → z ∈ V → False :=
      fun h1 h2 => Finset.disjoint_left.mp hUV h1 h2
    by_cases hz : z = x <;> simp_all <;> tauto
  have hLeft : insert x U \ insert x V = U := by
    ext z
    have hd : z ∈ U → z ∈ V → False :=
      fun h1 h2 => Finset.disjoint_left.mp hUV h1 h2
    by_cases hz : z = x <;> simp_all <;> tauto
  have hRight : insert x V \ insert x U = V := by
    ext z
    have hd : z ∈ U → z ∈ V → False :=
      fun h1 h2 => Finset.disjoint_left.mp hUV h1 h2
    by_cases hz : z = x <;> simp_all <;> tauto
  refine ⟨insert x U,insert x V,Finset.insert_subset hxA hUA,
    Finset.insert_subset hxA hVA,Finset.insert_nonempty _ _,
    Finset.insert_nonempty _ _,hC,hD,?_,?_,?_,?_,?_,?_⟩
  · simp [Finset.sum_insert,hxU,hUs]
  · simp [Finset.sum_insert,hxV,hVs]
  · rw [hInt]; simp
  · rwa [hLeft]
  · rwa [hRight]
  · exact Or.inl (by rw [hInt]; simp)

theorem fork_edge_crossing {A : Finset G} {x y : G}
    (hxy : x ≠ y) (hxA : x ∈ A) (hyA : y ∈ A)
    (hfork : ForkEdge A x y) : ProperZeroCrossing A := by
  rcases hfork with h | h | h | h
  · exact mixed_fork_crossing hxy hxA hyA h
  · exact mixed_fork_crossing (Ne.symm hxy) hyA hxA h
  · exact equal_fork_crossing hxy hxA hyA h
  · exact equal_fork_crossing (Ne.symm hxy) hyA hxA h

theorem no_singleton_crossing_fork_empty (A : Finset G)
    (hcross : NoSingletonZeroCrossing A) :
    ∀ ⦃x y : G⦄, x ∈ A → y ∈ A → x ≠ y → ¬ ForkEdge A x y := by
  intro x y hx hy hxy hfork
  exact hcross (fork_edge_crossing hxy hx hy hfork)

/-- Laminarity is imposed only on nonempty proper zero-sum subsets. -/
def Laminar (A : Finset G) : Prop :=
  ∀ ⦃C D : Finset G⦄, C ⊆ A → D ⊆ A → C.Nonempty → D.Nonempty →
    C ≠ A → D ≠ A → (∑ z ∈ C, z) = 0 → (∑ z ∈ D, z) = 0 →
      C ⊆ D ∨ D ⊆ C ∨ Disjoint C D

theorem laminar_no_singleton_crossing (A : Finset G) (hlam : Laminar A) :
    NoSingletonZeroCrossing A := by
  rintro ⟨C,D,hCA,hDA,hCne,hDne,hCneq,hDneq,hCs,hDs,hInt,hCD,hDC,_⟩
  rcases hlam hCA hDA hCne hDne hCneq hDneq hCs hDs with hsub | hsub | hdis
  · obtain ⟨z,hz⟩ := hCD
    exact (Finset.mem_sdiff.mp hz).2 (hsub (Finset.mem_sdiff.mp hz).1)
  · obtain ⟨z,hz⟩ := hDC
    exact (Finset.mem_sdiff.mp hz).2 (hsub (Finset.mem_sdiff.mp hz).1)
  · obtain ⟨z,hz⟩ := hInt
    exact Finset.disjoint_left.mp hdis (Finset.mem_inter.mp hz).1 (Finset.mem_inter.mp hz).2

/-- An actual partition of A, all of whose blocks have size at least two. -/
def PartitionBlocks (A : Finset G) (P : Finset (Finset G)) : Prop :=
  P.biUnion id = A ∧ (∀ B ∈ P, 2 ≤ B.card) ∧
    (∀ B ∈ P, ∀ K ∈ P, B ≠ K → Disjoint B K)

/-- Every nonempty proper zero-sum subset is a union of these partition blocks. -/
def ProperZeroBlockUnions (A : Finset G) (P : Finset (Finset G)) : Prop :=
  ∀ C : Finset G, C ⊆ A → C.Nonempty → C ≠ A → (∑ z ∈ C, z) = 0 →
    ∃ Q : Finset (Finset G), Q ⊆ P ∧ C = Q.biUnion id

private def Saturated (P : Finset (Finset G)) (C : Finset G) : Prop :=
  ∀ z ∈ C, ∃ B ∈ P, z ∈ B ∧ B ⊆ C

private lemma union_saturated {P Q : Finset (Finset G)} (hQ : Q ⊆ P) :
    Saturated P (Q.biUnion id) := by
  intro z hz
  obtain ⟨B,hB,hzB⟩ := Finset.mem_biUnion.mp hz
  exact ⟨B,hQ hB,hzB,fun t ht => Finset.mem_biUnion.mpr ⟨B,hB,ht⟩⟩

private lemma saturated_region {P : Finset (Finset G)}
    (hdis : ∀ B ∈ P, ∀ K ∈ P, B ≠ K → Disjoint B K)
    {C D : Finset G} (hC : Saturated P C) (hD : Saturated P D) :
    Saturated P (C ∩ D) ∧ Saturated P (C \ D) := by
  have same : ∀ {B K : Finset G}, B ∈ P → K ∈ P →
      ∀ {z : G}, z ∈ B → z ∈ K → B = K := by
    intro B K hB hK z hzB hzK
    by_contra hne
    exact Finset.disjoint_left.mp (hdis B hB K hK hne) hzB hzK
  constructor
  · intro z hz
    obtain ⟨B,hB,hzB,hBC⟩ := hC z (Finset.mem_inter.mp hz).1
    obtain ⟨K,hK,hzK,hKD⟩ := hD z (Finset.mem_inter.mp hz).2
    have heq := same hB hK hzB hzK
    subst K
    exact ⟨B,hB,hzB,fun t ht => Finset.mem_inter.mpr ⟨hBC ht,hKD ht⟩⟩
  · intro z hz
    obtain ⟨B,hB,hzB,hBC⟩ := hC z (Finset.mem_sdiff.mp hz).1
    refine ⟨B,hB,hzB,?_⟩
    intro t ht
    refine Finset.mem_sdiff.mpr ⟨hBC ht,?_⟩
    intro htD
    obtain ⟨K,hK,htK,hKD⟩ := hD t htD
    have heq := same hB hK ht htK
    subst K
    exact (Finset.mem_sdiff.mp hz).2 (hKD hzB)

private lemma saturated_card {P : Finset (Finset G)}
    (hsize : ∀ B ∈ P, 2 ≤ B.card) {C : Finset G}
    (hC : Saturated P C) (hne : C.Nonempty) : 2 ≤ C.card := by
  obtain ⟨z,hz⟩ := hne
  obtain ⟨B,hB,_,hBC⟩ := hC z hz
  exact (hsize B hB).trans (Finset.card_le_card hBC)

/-- Block unions need not be laminar; their nonempty Venn regions cannot be singletons. -/
theorem partition_blocks_no_singleton_crossing {A : Finset G} {P : Finset (Finset G)}
    (hpart : PartitionBlocks A P) (hunions : ProperZeroBlockUnions A P) :
    NoSingletonZeroCrossing A := by
  rintro ⟨C,D,hCA,hDA,hCne,hDne,hCneq,hDneq,hCs,hDs,hInt,hCD,hDC,hsingle⟩
  obtain ⟨Q,hQ,rfl⟩ := hunions C hCA hCne hCneq hCs
  obtain ⟨T,hT,rfl⟩ := hunions D hDA hDne hDneq hDs
  have hC := union_saturated hQ
  have hD := union_saturated hT
  have hregions := saturated_region hpart.2.2 hC hD
  have hi := saturated_card hpart.2.1 hregions.1 hInt
  have hl := saturated_card hpart.2.1 hregions.2 hCD
  have hr := saturated_card hpart.2.1 (saturated_region hpart.2.2 hD hC).2 hDC
  rcases hsingle with h | h | h <;> omega

end D5.S1.Words.Sequenceability.AdaptiveMergeZeroCrossing
