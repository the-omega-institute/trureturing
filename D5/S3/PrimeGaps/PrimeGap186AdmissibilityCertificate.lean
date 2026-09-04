/- GID: D5/S3/PrimeGaps/PrimeGap186AdmissibilityCertificate
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Certify the explicit diameter-186 forty-tuple against every local prime obstruction. -/

import D5.S3.PrimeGaps.PrimeGap186FiniteFrontEnd
import D5.S3.PrimeGaps.PrimeGapAdmissibilityContractBridge

namespace D5.S3.PrimeGaps.PrimeGap186AdmissibilityCertificate

open D5.S3.PrimeGaps.PrimeGap186FiniteFrontEnd
open D5.S3.PrimeGaps.PrimeGapAdmissibilityContractBridge
open D5.S3.PrimeGaps.PrimeGap186SourceContract
open D5.S3.Analytic.PrimeProducts.FiniteLocalResidueBlockingCriterion

/-- An explicit omitted residue for each possible prime modulus at most forty.
Values at composite inputs are irrelevant. -/
def omittedResidue186 (p : Nat) : Nat :=
  if p = 2 then 1
  else if p = 3 then 1
  else if p = 5 then 4
  else if p = 7 then 3
  else if p = 11 then 7
  else if p = 13 then 5
  else if p = 17 then 11
  else if p = 19 then 8
  else if p = 23 then 16
  else if p = 29 then 9
  else if p = 31 then 4
  else if p = 37 then 3
  else 0

/-- For every prime no larger than forty, the displayed residue is absent from the direct
residue image of the explicit tuple. This is a finite executable certificate. -/
theorem omittedResidue186_is_missing
    (p : Nat) (hp : p.Prime) (hle : p ≤ 40) :
    ∀ h ∈ admissibleTuple186Int,
      (h : ZMod p) ≠ (omittedResidue186 p : ZMod p) := by
  interval_cases p <;>
    norm_num [omittedResidue186, admissibleTuple186Int, admissibleTuple186] at hp ⊢

/-- The explicit forty-tuple satisfies the exact direct admissibility contract used by the
upstream `DHL[40,2]` theorem. Large primes are discharged generically by cardinality; the
small-prime residue witnesses are certified above. -/
theorem admissibleTuple186_is_admissible :
    AdmissibleIntegerTuple admissibleTuple186Int := by
  rw [admissibleIntegerTuple_iff_local_residue]
  intro p hp
  by_cases hle : p ≤ 40
  · have hdirect : ∃ a : ZMod p, ∀ h ∈ admissibleTuple186Int, (h : ZMod p) ≠ a :=
      ⟨(omittedResidue186 p : ZMod p), omittedResidue186_is_missing p hp hle⟩
    exact (local_residue_count_lt_iff_direct_admissible admissibleTuple186Int p hp.pos).2 hdirect
  · have hgt : 40 < p := Nat.lt_of_not_ge hle
    have hpos := admissibleTuple186_large_modulus_survives p hgt
    have hcount : localResidueCount admissibleTuple186Int p ≤ p := by
      calc
        localResidueCount admissibleTuple186Int p =
            (admissibleTuple186Int.image fun h : Int => -(h : ZMod p)).card := rfl
        _ ≤ admissibleTuple186Int.card := Finset.card_image_le
        _ = 40 := admissibleTuple186Int_card
        _ ≤ p := hgt.le
    exact (localSurvivorCount_pos_iff admissibleTuple186Int p hcount).1 hpos

/-- The local-residue formulation is therefore closed unconditionally for the explicit tuple. -/
theorem admissibleTuple186_all_local_residue_counts :
    ∀ p : Nat, p.Prime → localResidueCount admissibleTuple186Int p < p :=
  (admissibleIntegerTuple_iff_local_residue admissibleTuple186Int).1
    admissibleTuple186_is_admissible

#print axioms omittedResidue186
#print axioms omittedResidue186_is_missing
#print axioms admissibleTuple186_is_admissible
#print axioms admissibleTuple186_all_local_residue_counts

end D5.S3.PrimeGaps.PrimeGap186AdmissibilityCertificate
