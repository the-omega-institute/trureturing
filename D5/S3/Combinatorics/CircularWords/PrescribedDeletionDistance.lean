/- GID: D5/S3/Combinatorics/CircularWords/PrescribedDeletionDistance
   generality: G
   mirror-B: D5/B/S3/Combinatorics/CircularWords/PrescribedDeletionDistance
   mirror-E: none(waiver:research-draft)
   anchors: []
   utility: none
   digest: The actual k-prescribed-deletion code has minimum distance k minus two. -/

import D5.S3.Combinatorics.CircularWords.ThreeSpecifiedDeletions

/-!
Prescribed-label deletion distance and legal-alphabet error/erasure ambiguity.
Per-declaration registration and delivery are separate from this source integration.

The new content is the arbitrary-size agreement bound and its attained distance
calculation. Three-label reconstruction and two-label collisions are imported,
not reproved. Generic decoding is an application in the accompanying Scribe;
there is no named decoding specialization here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.CircularWords.PrescribedDeletionDistance

open CircularDeletionTransport DeletionReadoutReconstruction ThreeSpecifiedDeletions

universe u
variable {α : Type u} [DecidableEq α]

/-- The exact image of the deletion at this label, rather than an enlarged
error alphabet. No global finiteness assumption on the ambient label type. -/
def ReadoutAlphabet (A : Finset α) (x : α) :=
  {R : Cycle α // ∃ C : SupportedCircle A, delete x C.1 = R}

/-- A section of the actual alphabet family. For observations only its
restriction to J outside E is used; unused coordinates impose no noise cost. -/
abbrev ReadoutSection (A : Finset α) := (x : α) → ReadoutAlphabet A x

/-- Count erroneous whole readouts outside the known erased coordinates.
Subtype-value equality is exactly same-coordinate actual-alphabet equality. -/
noncomputable def errorCount {A : Finset α} (J E : Finset α)
    (received : ReadoutSection A) (C : SupportedCircle A) : ℕ := by
  classical
  exact (J.filter fun x => x ∉ E ∧ (received x).1 ≠ delete x C.1).card

/-- Hamming distance of the dependent observation tuple: subtype equality is
equivalent to equality of the underlying cycles at each fixed label. -/
noncomputable def readoutDistance {A : Finset α} (J : Finset α)
    (C D : SupportedCircle A) : ℕ := by
  classical
  exact (J.filter fun x => delete x C.1 ≠ delete x D.1).card

-- Consumed by the lower bound and by the attaining-pair calculation below.
private theorem distance_add_agreements {A : Finset α} (J : Finset α)
    (C D : SupportedCircle A) :
    readoutDistance J C D +
      (J.filter fun x => delete x C.1 = delete x D.1).card = J.card := by
  classical
  let disagreements := J.filter fun x => delete x C.1 ≠ delete x D.1
  let agreements := J.filter fun x => delete x C.1 = delete x D.1
  have hu : disagreements ∪ agreements = J := by
    ext x
    by_cases h : delete x C.1 = delete x D.1 <;>
      simp [disagreements, agreements, h]
  have hd : Disjoint disagreements agreements := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
  change disagreements.card + agreements.card = J.card
  rw [← Finset.card_union_of_disjoint hd, hu]

-- This finite-set inference is the missing mathematical composition, not a
-- new proof of reconstruct_three. It is live in both clauses of the result.
private theorem agreements_le_two {A J : Finset α} (hA : 4 ≤ A.card)
    (hJA : J ⊆ A) (C D : SupportedCircle A) (hne : C ≠ D) :
    (J.filter fun x => delete x C.1 = delete x D.1).card ≤ 2 := by
  classical
  by_contra hn
  have ht : 2 < (J.filter fun x => delete x C.1 = delete x D.1).card := by
    omega
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp ht
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  have hc' := Finset.mem_filter.mp hc
  have he : C.1 = D.1 := reconstruct_three hA
    (hJA ha'.1) (hJA hb'.1) (hJA hc'.1) hab hac hbc
    C.2.1 D.2.1 C.2.2 D.2.2 ha'.2 hb'.2 hc'.2
  exact hne (Subtype.ext he)

/-- For any actual fixed support of size at least four and any prescribed
distinct-label family J of size at least three, every distinct pair is at
distance at least |J|-2 and some actual distinct pair attains that distance.
The witness even has exactly two agreeing prescribed labels. -/
theorem exact_prescribed_distance {A J : Finset α} (hA : 4 ≤ A.card)
    (hJA : J ⊆ A) (hJ : 3 ≤ J.card) :
    (∀ C D : SupportedCircle A, C ≠ D →
      J.card - 2 ≤ readoutDistance J C D) ∧
    (∃ C D : SupportedCircle A, C ≠ D ∧
      (J.filter fun x => delete x C.1 = delete x D.1).card = 2 ∧
      readoutDistance J C D = J.card - 2) := by
  classical
  constructor
  · intro C D hne
    have hb := agreements_le_two hA hJA C D hne
    have hp := distance_add_agreements J C D
    omega
  · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < J.card by omega)
    obtain ⟨C₀, D₀, hnC, hnD, hsC, hsD, hne₀, hda, hdb⟩ :=
      two_deletions_insufficient hA (hJA ha) (hJA hb) hab
    let C : SupportedCircle A := ⟨C₀, hnC, hsC⟩
    let D : SupportedCircle A := ⟨D₀, hnD, hsD⟩
    have hne : C ≠ D := by
      intro he
      exact hne₀ (congrArg Subtype.val he)
    have hpair : ({a, b} : Finset α) ⊆
        J.filter (fun x => delete x C.1 = delete x D.1) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨ha, hda⟩
      · exact Finset.mem_filter.mpr ⟨hb, hdb⟩
    have hl : 2 ≤ (J.filter fun x => delete x C.1 = delete x D.1).card := by
      have hh := Finset.card_le_card hpair
      simpa [hab] using hh
    have hu := agreements_le_two hA hJA C D hne
    have he : (J.filter fun x => delete x C.1 = delete x D.1).card = 2 := by
      omega
    have hp := distance_add_agreements J C D
    exact ⟨C, D, hne, he, by omega⟩

/-- When the uniform budget inequality fails, two actual distinct states have
the same legal received observation within both budgets. Every value in the
received section has an explicit same-label deletion-image witness. This is
a construction on the actual circular code, not a generic coding theorem.
Only the restriction of the section to J outside E is observed. -/
theorem ambiguity_of_failed_budget {A J : Finset α} (hA : 4 ≤ A.card)
    (hJA : J ⊆ A) (hJ : 3 ≤ J.card) (t e : ℕ)
    (hbudget : J.card - 2 ≤ 2 * t + e) :
    ∃ C D : SupportedCircle A, C ≠ D ∧
      ∃ E : Finset α, E ⊆ J ∧ E.card ≤ e ∧
        ∃ received : ReadoutSection A,
          errorCount J E received C ≤ t ∧ errorCount J E received D ≤ t := by
  classical
  obtain ⟨C, D, hne, _, hdist⟩ := (exact_prescribed_distance hA hJA hJ).2
  let delta := J.filter fun x => delete x C.1 ≠ delete x D.1
  have hdelta : delta.card = J.card - 2 := by
    change readoutDistance J C D = J.card - 2
    exact hdist
  obtain ⟨E, hEsub, hEcard⟩ := Finset.exists_subset_card_eq
    (s := delta) (n := min e delta.card) (Nat.min_le_right _ _)
  have hEJ : E ⊆ J := fun x hx => (Finset.mem_filter.mp (hEsub hx)).1
  have hEle : E.card ≤ e := by
    rw [hEcard]
    exact Nat.min_le_left _ _
  let remaining := delta \ E
  have hremcard : remaining.card = delta.card - min e delta.card := by
    change (delta \ E).card = _
    rw [Finset.card_sdiff_of_subset hEsub, hEcard]
  have hrembound : remaining.card ≤ 2 * t := by
    by_cases h : e ≤ delta.card
    · rw [hremcard, Nat.min_eq_left h]
      omega
    · rw [hremcard, Nat.min_eq_right (by omega : delta.card ≤ e)]
      omega
  obtain ⟨P, hPsub, hPcard⟩ := Finset.exists_subset_card_eq
    (s := remaining) (n := min t remaining.card) (Nat.min_le_right _ _)
  have hPle : P.card ≤ t := by
    rw [hPcard]
    exact Nat.min_le_left _ _
  have hQle : (remaining \ P).card ≤ t := by
    rw [Finset.card_sdiff_of_subset hPsub, hPcard]
    by_cases h : t ≤ remaining.card
    · rw [Nat.min_eq_left h]
      omega
    · rw [Nat.min_eq_right (by omega : remaining.card ≤ t)]
      omega
  let received : ReadoutSection A := fun x =>
    if x ∈ P then ⟨delete x D.1, ⟨D, rfl⟩⟩ else ⟨delete x C.1, ⟨C, rfl⟩⟩
  have hfirst :
      J.filter (fun x => x ∉ E ∧ (received x).1 ≠ delete x C.1) = P := by
    ext x
    constructor
    · intro hx
      have hdiff := (Finset.mem_filter.mp hx).2.2
      by_contra hn
      simp [received, hn] at hdiff
    · intro hx
      have hr := Finset.mem_sdiff.mp (hPsub hx)
      have hd := Finset.mem_filter.mp hr.1
      apply Finset.mem_filter.mpr
      refine ⟨hd.1, hr.2, ?_⟩
      simpa [received, hx] using hd.2.symm
  have hsecond :
      J.filter (fun x => x ∉ E ∧ (received x).1 ≠ delete x D.1) = remaining \ P := by
    ext x
    constructor
    · intro hx
      have hh := Finset.mem_filter.mp hx
      have hnotP : x ∉ P := by
        intro hp
        have hdiff := hh.2.2
        simp [received, hp] at hdiff
      have hdiff : delete x C.1 ≠ delete x D.1 := by
        simpa [received, hnotP] using hh.2.2
      have hdeltaMem : x ∈ delta := Finset.mem_filter.mpr ⟨hh.1, hdiff⟩
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_sdiff.mpr ⟨hdeltaMem, hh.2.1⟩, hnotP⟩
    · intro hx
      have hh := Finset.mem_sdiff.mp hx
      have hr := Finset.mem_sdiff.mp hh.1
      have hd := Finset.mem_filter.mp hr.1
      apply Finset.mem_filter.mpr
      refine ⟨hd.1, hr.2, ?_⟩
      simpa [received, hh.2] using hd.2
  refine ⟨C, D, hne, E, hEJ, hEle, received, ?_, ?_⟩
  · change (J.filter fun x => x ∉ E ∧ (received x).1 ≠ delete x C.1).card ≤ t
    rw [hfirst]
    exact hPle
  · change (J.filter fun x => x ∉ E ∧ (received x).1 ≠ delete x D.1).card ≤ t
    rw [hsecond]
    exact hQle

#check @exact_prescribed_distance
#print axioms exact_prescribed_distance
#check @ambiguity_of_failed_budget
#print axioms ambiguity_of_failed_budget
#check @distance_add_agreements
#print axioms distance_add_agreements
#check @agreements_le_two
#print axioms agreements_le_two
#check @ReadoutAlphabet
#print axioms ReadoutAlphabet
#check @ReadoutSection
#print axioms ReadoutSection
#check @errorCount
#print axioms errorCount
#check @readoutDistance
#print axioms readoutDistance
end D5.S3.Combinatorics.CircularWords.PrescribedDeletionDistance
