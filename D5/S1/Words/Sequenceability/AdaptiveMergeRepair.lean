/- GID: D5/S1/Words/Sequenceability/AdaptiveMergeRepair
   generality: G
   mirror-B: D5/B/S1/Words/Sequenceability/AdaptiveMergeRepair
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Generic two-collision signed-fork obstruction and conditional adaptive repair. -/

import D5.S1.Words.Sequenceability.AdaptiveMergeZeroCrossing
import D5.S3.FiniteGroups.RestrictedPairSumClassification

set_option autoImplicit false
noncomputable section
namespace D5.S1.Words.Sequenceability.AdaptiveMergeRepair
open _root_.D5.S1.Words.Sequenceability.AdaptiveMergePrefix
open _root_.D5.S1.Words.Sequenceability.AdaptiveMergeSignedFork
open _root_.D5.S1.Words.Sequenceability.AdaptiveMergeZeroCrossing
open scoped Classical BigOperators
variable {G : Type*} [AddCommGroup G]

/-- Legal original-label edge; the sum lies outside A and is nonzero. -/
def LegalPair (A : Finset G) (a b : G) : Prop :=
  a ∈ A ∧ b ∈ A ∧ a ≠ b ∧ a + b ∉ insert 0 A

def compressedAlphabet (A : Finset G) (a b : G) : Finset G :=
  insert (a + b) ((A.erase a).erase b)

/-- A genuine permutation of the actual alphabet with proper intervals nonzero. -/
def GoodOrder (A : Finset G) (w : List G) : Prop :=
  w.Perm A.toList ∧ ProperIntervals w

def GoodCompression (A : Finset G) (a b : G) (L R : List G) : Prop :=
  GoodOrder (compressedAlphabet A a b) (L ++ [a + b] ++ R)

private lemma legal_nonzero {A : Finset G} {a b : G} (hab : LegalPair A a b) :
    a ≠ 0 ∧ b ≠ 0 := by
  rcases hab with ⟨haA,hbA,_,hsum⟩
  constructor
  · intro ha
    exact hsum (by simpa [ha] using
      (Finset.mem_insert.mpr (Or.inr hbA) : b ∈ insert (0:G) A))
  · intro hb
    exact hsum (by simpa [hb] using
      (Finset.mem_insert.mpr (Or.inr haA) : a ∈ insert (0:G) A))

private lemma compression_sides {A : Finset G} {a b : G} {L R : List G}
    (hp : (L ++ [a + b] ++ R).Perm (compressedAlphabet A a b).toList) :
    ListSubset ((A.erase a).erase b) L ∧
    ListSubset ((A.erase a).erase b) R ∧ ListDisjoint L R := by
  have hnd : (L ++ ((a+b) :: R)).Nodup := by
    simpa [List.append_assoc] using hp.nodup_iff.mpr (Finset.nodup_toList _)
  have hdis := List.disjoint_of_nodup_append hnd
  have htail := List.nodup_cons.mp hnd.of_append_right
  have hmem : ∀ z, z ∈ L ∨ z ∈ R → z ∈ compressedAlphabet A a b := by
    intro z hz
    apply Finset.mem_toList.mp
    apply hp.mem_iff.mp
    rcases hz with hz | hz <;> simp [hz]
  have hLmem : ∀ z ∈ L, z ∈ (A.erase a).erase b := by
    intro z hz
    have hzB := hmem z (Or.inl hz)
    rcases Finset.mem_insert.mp hzB with hzr | hzB
    · subst z
      exact (hdis hz (by simp)).elim
    · exact hzB
  have hRmem : ∀ z ∈ R, z ∈ (A.erase a).erase b := by
    intro z hz
    have hzB := hmem z (Or.inr hz)
    rcases Finset.mem_insert.mp hzB with hzr | hzB
    · subst z
      exact (htail.1 hz).elim
    · exact hzB
  refine ⟨⟨hnd.of_append_left, hLmem⟩, ⟨htail.2, hRmem⟩, ?_⟩
  intro z hzL hzR
  exact hdis hzL (by simp [hzR])

private lemma expanded_permutation {A : Finset G} {a b : G} {L R : List G}
    (hab : LegalPair A a b)
    (hp : (L ++ [a + b] ++ R).Perm (compressedAlphabet A a b).toList) :
    (L ++ [a, b] ++ R).Perm A.toList := by
  obtain ⟨hL,hR,hLR⟩ := compression_sides hp
  have haL : a ∉ L := fun hz =>
    (Finset.mem_erase.mp (Finset.mem_of_mem_erase (hL.2 a hz))).1 rfl
  have hbL : b ∉ L := fun hz => (Finset.mem_erase.mp (hL.2 b hz)).1 rfl
  have haR : a ∉ R := fun hz =>
    (Finset.mem_erase.mp (Finset.mem_of_mem_erase (hR.2 a hz))).1 rfl
  have hbR : b ∉ R := fun hz => (Finset.mem_erase.mp (hR.2 b hz)).1 rfl
  have hn : (L ++ [a, b] ++ R).Nodup := by
    rw [List.append_assoc]
    apply List.Nodup.append hL.1
    · simpa using (show (a :: b :: R).Nodup by simp [hab.2.2.1,haR,hbR,hR.1])
    · intro z hzL hzT
      simp only [List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at hzT
      rcases hzT with (rfl | rfl) | hzR
      · exact haL hzL
      · exact hbL hzL
      · exact hLR z hzL hzR
  apply (List.perm_ext_iff_of_nodup hn (Finset.nodup_toList A)).mpr
  intro z
  have hmemLR : (z ∈ L ∨ z ∈ R) ↔ z ∈ (A.erase a).erase b := by
    constructor
    · rintro (hz | hz)
      · exact hL.2 z hz
      · exact hR.2 z hz
    · intro hz
      have hzA := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz)
      have hzsum : z ≠ a+b := by
        intro heq
        subst z
        exact hab.2.2.2 (Finset.mem_insert.mpr (Or.inr hzA))
      have hzB : z ∈ (compressedAlphabet A a b).toList := by
        simpa [compressedAlphabet] using (Finset.mem_insert.mpr (Or.inr hz) :
          z ∈ insert (a+b) ((A.erase a).erase b))
      have hzW := hp.mem_iff.mpr hzB
      simpa [hzsum] using hzW
  simp only [List.mem_append,List.mem_cons,List.mem_nil_iff,or_false,Finset.mem_toList]
  have haA := hab.1
  have hbA := hab.2.1
  simp only [Finset.mem_erase] at hmemLR
  by_cases hza : z = a
  · subst z
    simp [haA]
  by_cases hzb : z = b
  · subst z
    simp [hbA]
  simpa [hza,hzb] using hmemLR

/-- Every actual Good compressed order whose two actual expansions fail has a static fork. -/
theorem failed_expansions_force_fork {A : Finset G} {a b : G} {L R : List G}
    (hab : LegalPair A a b) (hw : GoodCompression A a b L R)
    (habBad : ¬ GoodOrder A (L ++ [a, b] ++ R))
    (hbaBad : ¬ GoodOrder A (L ++ [b, a] ++ R)) : ForkEdge A a b := by
  obtain ⟨hL,hR,hLR⟩ := compression_sides hw.1
  obtain ⟨ha0,hb0⟩ := legal_nonzero hab
  have hba : LegalPair A b a := by
    exact ⟨hab.2.1,hab.1,Ne.symm hab.2.2.1,by simpa [add_comm] using hab.2.2.2⟩
  apply two_collision_fork hab.1 hab.2.1 ha0 hb0 hab.2.2.1 hL hR hLR
    ((good_iff_proper_intervals _).mpr hw.2)
  · intro hg
    exact habBad ⟨expanded_permutation hab hw.1,(good_iff_proper_intervals _).mp hg⟩
  · intro hg
    exact hbaBad ⟨expanded_permutation hba (by simpa [add_comm,
      compressedAlphabet,Finset.erase_right_comm] using hw.1),
      (good_iff_proper_intervals _).mp hg⟩

/-- A legal edge outside the static fork graph lifts EVERY actual Good compressed order. -/
theorem outside_fork_lifts_every_order {A : Finset G} {a b : G} {L R : List G}
    (hab : LegalPair A a b) (hfork : ¬ ForkEdge A a b)
    (hw : GoodCompression A a b L R) :
    GoodOrder A (L ++ [a, b] ++ R) ∨ GoodOrder A (L ++ [b, a] ++ R) := by
  by_contra hbad
  push Not at hbad
  exact hfork (failed_expansions_force_fork hab hw hbad.1 hbad.2)

private lemma compression_witness_of_order {A : Finset G} {a b : G}
    (hw : ∃ w : List G, GoodOrder (compressedAlphabet A a b) w) :
    ∃ L R : List G, GoodCompression A a b L R := by
  rcases hw with ⟨w,hp,hg⟩
  have hr : a+b ∈ w := hp.mem_iff.mpr (by simp [compressedAlphabet])
  obtain ⟨L,R,heq⟩ := List.mem_iff_append.mp hr
  have hsplit : w = L ++ [a + b] ++ R := by simpa [List.append_assoc] using heq
  exact ⟨L,R,by simpa [GoodCompression,GoodOrder,← hsplit] using (And.intro hp hg)⟩

/-- Adaptive lifting retains an actual legal compression, its Good order and actual expansion. -/
def AdaptiveLifting (A : Finset G) : Prop :=
  ∃ a b : G, ∃ L R : List G, LegalPair A a b ∧ GoodCompression A a b L R ∧
    (GoodOrder A (L ++ [a, b] ++ R) ∨ GoodOrder A (L ++ [b, a] ++ R))

/-- H is precisely existence of a Good actual order for every legal compression. -/
theorem adaptive_repair_under_H {A : Finset G}
    (H : ∀ ⦃a b : G⦄, LegalPair A a b →
      ∃ w : List G, GoodOrder (compressedAlphabet A a b) w)
    (hedge : ∃ a b : G, LegalPair A a b ∧ ¬ ForkEdge A a b) :
    AdaptiveLifting A := by
  rcases hedge with ⟨a,b,hab,hfork⟩
  obtain ⟨L,R,hw⟩ := compression_witness_of_order (H hab)
  exact ⟨a,b,L,R,hab,hw,outside_fork_lifts_every_order hab hfork hw⟩

theorem adaptive_failure_forces_fork_inclusion {A : Finset G}
    (H : ∀ ⦃a b : G⦄, LegalPair A a b →
      ∃ w : List G, GoodOrder (compressedAlphabet A a b) w)
    (hfail : ¬ AdaptiveLifting A) :
    ∀ ⦃a b : G⦄, LegalPair A a b → ForkEdge A a b := by
  intro a b hab
  by_contra hfork
  exact hfail (adaptive_repair_under_H H ⟨a,b,hab,hfork⟩)

/-- The explicit crossing exclusion repairs adaptive lifting, assuming H and a legal edge. -/
theorem adaptive_of_no_singleton_crossing {A : Finset G}
    (H : ∀ ⦃a b : G⦄, LegalPair A a b →
      ∃ w : List G, GoodOrder (compressedAlphabet A a b) w)
    (hedge : ∃ a b : G, LegalPair A a b) (hcross : NoSingletonZeroCrossing A) :
    AdaptiveLifting A := by
  obtain ⟨a,b,hab⟩ := hedge
  exact adaptive_repair_under_H H ⟨a,b,hab,
    no_singleton_crossing_fork_empty A hcross hab.1 hab.2.1 hab.2.2.1⟩

/-- Laminar proper-zero families repair adaptive lifting under exactly H and a legal edge. -/
theorem adaptive_of_laminar {A : Finset G}
    (H : ∀ ⦃a b : G⦄, LegalPair A a b →
      ∃ w : List G, GoodOrder (compressedAlphabet A a b) w)
    (hedge : ∃ a b : G, LegalPair A a b) (hlam : Laminar A) :
    AdaptiveLifting A :=
  adaptive_of_no_singleton_crossing H hedge (laminar_no_singleton_crossing A hlam)

/-- Structural classification is consumed only to supply a legal edge. -/
private lemma legal_edge_of_not_subgroup {A : Finset G} (h0 : 0 ∉ A)
    (hcard : 3 ≤ A.card)
    (hnot : ¬ ∃ K : AddSubgroup G, (K : Set G) = (↑(insert 0 A) : Set G)) :
    ∃ a b : G, LegalPair A a b := by
  by_contra hn
  apply hnot
  apply D5.S3.FiniteGroups.RestrictedPairSumClassification.restricted_pair_sum_classification
    A h0 hcard
  intro a b ha hb hab
  by_contra hsum
  exact hn ⟨a,b,ha,hb,hab,hsum⟩

/-- Laminarity is an extra hypothesis; nonsubgroup structure supplies the legal edge. -/
theorem adaptive_of_laminar_nonsubgroup {A : Finset G} (h0 : 0 ∉ A)
    (hcard : 3 ≤ A.card)
    (hnot : ¬ ∃ K : AddSubgroup G, (K : Set G) = (↑(insert 0 A) : Set G))
    (H : ∀ ⦃a b : G⦄, LegalPair A a b →
      ∃ w : List G, GoodOrder (compressedAlphabet A a b) w)
    (hlam : Laminar A) : AdaptiveLifting A :=
  adaptive_of_laminar H (legal_edge_of_not_subgroup h0 hcard hnot) hlam

/-- The independent block-union repair assumes H and nonempty legal edges explicitly. -/
theorem adaptive_of_partition_blocks {A : Finset G} {P : Finset (Finset G)}
    (H : ∀ ⦃a b : G⦄, LegalPair A a b →
      ∃ w : List G, GoodOrder (compressedAlphabet A a b) w)
    (hedge : ∃ a b : G, LegalPair A a b)
    (hpart : PartitionBlocks A P) (hunions : ProperZeroBlockUnions A P) :
    AdaptiveLifting A :=
  adaptive_of_no_singleton_crossing H hedge
    (partition_blocks_no_singleton_crossing hpart hunions)

end D5.S1.Words.Sequenceability.AdaptiveMergeRepair
