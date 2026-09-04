/- GID: D5/S3/PrimeGaps/PrimeGapAdmissibilityContractBridge
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equate the repository's forbidden-residue count with the direct admissibility contract used by DHL prime tuples. -/

import D5.S3.Analytic.PrimeProducts.FiniteLocalResidueBlockingCriterion
import D5.S3.PrimeGaps.PrimeGap186SourceContract

namespace D5.S3.PrimeGaps.PrimeGapAdmissibilityContractBridge

open D5.S3.Analytic.PrimeProducts.FiniteLocalResidueBlockingCriterion
open D5.S3.PrimeGaps.PrimeGap186SourceContract

/-- The direct residue classes occupied by the offsets modulo `p`. -/
def directResidueSet (H : Finset Int) (p : Nat) : Finset (ZMod p) :=
  H.image fun h : Int => (h : ZMod p)

/-- Negation sends the direct residue set bijectively onto the repository's forbidden
translation-residue set. Thus the two presentations have the same cardinality. -/
theorem directResidueSet_card_eq_localResidueCount
    (H : Finset Int) (p : Nat) :
    (directResidueSet H p).card = localResidueCount H p := by
  classical
  unfold directResidueSet localResidueCount localResidueSet
  let e : ZMod p ≃ ZMod p := Equiv.neg (ZMod p)
  have himage :
      (H.image fun h : Int => -(h : ZMod p)) =
        (H.image fun h : Int => (h : ZMod p)).image e := by
    ext x
    simp [e]
  rw [himage, Finset.card_image_of_injective _ e.injective]

/-- A finite tuple satisfies the source's direct admissibility condition modulo a positive
modulus exactly when its occupied residue set does not fill the whole residue ring. -/
theorem direct_admissibility_iff_card_lt
    (H : Finset Int) (p : Nat) (hp : 0 < p) :
    (∃ a : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ a) ↔
      (directResidueSet H p).card < p := by
  classical
  have huniv : (Finset.univ : Finset (ZMod p)).card = p := by simp
  constructor
  · rintro ⟨a, ha⟩
    have hproper : directResidueSet H p ⊂ (Finset.univ : Finset (ZMod p)) := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩
      intro heq
      have hamem : a ∈ directResidueSet H p := by simpa [heq]
      rcases Finset.mem_image.mp hamem with ⟨h, hh, hha⟩
      exact ha h hh hha
    simpa [huniv] using Finset.card_lt_card hproper
  · intro hcard
    have hcard' : (directResidueSet H p).card < (Finset.univ : Finset (ZMod p)).card := by
      simpa [huniv] using hcard
    obtain ⟨a, ha⟩ := Finset.sdiff_nonempty_of_card_lt_card hcard'
    refine ⟨a, ?_⟩
    intro h hh hha
    have hamem : a ∈ directResidueSet H p :=
      Finset.mem_image.mpr ⟨h, hh, hha⟩
    exact (Finset.mem_sdiff.mp ha).2 hamem

/-- For a positive modulus, the repository's local-residue inequality is exactly the direct
admissibility contract appearing in the upstream `DHL[40,2]` theorem. -/
theorem local_residue_count_lt_iff_direct_admissible
    (H : Finset Int) (p : Nat) (hp : 0 < p) :
    localResidueCount H p < p ↔
      ∃ a : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ a := by
  rw [← directResidueSet_card_eq_localResidueCount H p]
  exact (direct_admissibility_iff_card_lt H p hp).symm

/-- Consequently, the all-primes source admissibility predicate is equivalent to the
repository's all-primes local survivor condition. -/
theorem admissibleIntegerTuple_iff_local_residue
    (H : Finset Int) :
    AdmissibleIntegerTuple H ↔
      ∀ p : Nat, p.Prime → localResidueCount H p < p := by
  constructor
  · intro hadm p hp
    have hp0 := hp.pos
    exact (local_residue_count_lt_iff_direct_admissible H p hp0).2 (hadm p hp)
  · intro hlocal p hp
    exact (local_residue_count_lt_iff_direct_admissible H p hp.pos).1 (hlocal p hp)

#print axioms directResidueSet
#print axioms directResidueSet_card_eq_localResidueCount
#print axioms direct_admissibility_iff_card_lt
#print axioms local_residue_count_lt_iff_direct_admissible
#print axioms admissibleIntegerTuple_iff_local_residue

end D5.S3.PrimeGaps.PrimeGapAdmissibilityContractBridge
