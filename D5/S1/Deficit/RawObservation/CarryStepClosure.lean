/- GID: D5/S1/Deficit/RawObservation/CarryStepClosure
   generality: G
   mirror-B: D5/B/S1/Deficit/RawObservation/CarryStepClosure
   mirror-E: none(waiver:exact-unbounded-family)
   anchors: []
   utility: none
   digest: All shift readings plus current canonicality still fail to close the
     existing deterministic carryPass; an actual unbounded family has unit next-step defect. -/

import D5.S1.Deficit.RawObservation.NormalizationResidual
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false

namespace D5.S1.Deficit.RawObservation.CarryStepClosure

open D5.S0.Carrier D5.S1.Digit D5.S1.Deficit.RawObservation

/-- Two low repeated bins, with an arbitrary high multiplicity. -/
private def low (k : Nat) : RawDigits :=
  Finsupp.single 0 2 + Finsupp.single 1 2 + Finsupp.single 4 k

/-- The same golden value concentrated in the third bin. -/
private def high (k : Nat) : RawDigits :=
  Finsupp.single 2 2 + Finsupp.single 4 k

private def lowNext (k : Nat) : RawDigits :=
  Finsupp.single 1 3 + Finsupp.single 4 k

private def highNext (k : Nat) : RawDigits :=
  Finsupp.single 0 1 + Finsupp.single 3 1 + Finsupp.single 4 k

-- Existing beta-add/single facts are private in frozen owners. These are local
-- evaluation calculations, not new public mathematical claims.
private theorem eval_add (r s : RawDigits) :
    betaDigits (r + s) = betaDigits r + betaDigits s := by
  classical
  refine Finsupp.sum_add_index' (fun i => ?_) (fun i c d => ?_)
  · simp
  · push_cast
    ring

private theorem eval_single (i c : Nat) :
    betaDigits (Finsupp.single i c) = (c : GoldenInt) * phi ^ (i + 2) := by
  classical
  rw [betaDigits, Finsupp.sum_single_index (by simp)]

private theorem common_value (k : Nat) : betaDigits (low k) = betaDigits (high k) := by
  simp only [low, high, eval_add, eval_single]
  apply GoldenInt.ext <;> norm_num [phi, pow_succ] <;> ring

private theorem next_defect (k : Nat) :
    betaDigits (lowNext k) + 1 = betaDigits (highNext k) := by
  simp only [lowNext, highNext, eval_add, eval_single]
  apply GoldenInt.ext <;> norm_num [phi, pow_succ] <;> ring

private theorem low_not_canonical (k : Nat) : ¬ CanonicalRaw (low k) := by
  intro h
  have ht := h.1 0
  norm_num [low] at ht

private theorem high_not_canonical (k : Nat) : ¬ CanonicalRaw (high k) := by
  intro h
  have ht := h.1 2
  norm_num [high] at ht

private theorem low_step (k : Nat) : carryPass (low k) = lowNext k := by
  classical
  have hex : ∃ i, 2 ≤ low k i := ⟨0, by norm_num [low]⟩
  have hfind : Nat.find hex = 0 := by
    apply Nat.find_eq_iff.mpr
    exact ⟨by norm_num [low], fun i hi => by omega⟩
  rw [carryPass, dif_pos hex, hfind]
  ext j
  by_cases h0 : j = 0
  · subst j
    norm_num [carryRepeated, low, lowNext]
  by_cases h1 : j = 1
  · subst j
    norm_num [carryRepeated, low, lowNext]
  by_cases h4 : j = 4
  · subst j
    norm_num [carryRepeated, low, lowNext]
  simp [carryRepeated, low, lowNext, h0, h1, h4]

private theorem high_step (k : Nat) : carryPass (high k) = highNext k := by
  classical
  have hex : ∃ i, 2 ≤ high k i := ⟨2, by norm_num [high]⟩
  have hfind : Nat.find hex = 2 := by
    apply Nat.find_eq_iff.mpr
    refine ⟨by norm_num [high], ?_⟩
    intro j hj
    interval_cases j <;> norm_num [high]
  rw [carryPass, dif_pos hex, hfind]
  ext j
  by_cases h0 : j = 0
  · subst j
    norm_num [carryRepeated, high, highNext]
  by_cases h2 : j = 2
  · subst j
    norm_num [carryRepeated, high, highNext]
  by_cases h3 : j = 3
  · subst j
    norm_num [carryRepeated, high, highNext]
  by_cases h4 : j = 4
  · subst j
    norm_num [carryRepeated, high, highNext]
  simp [carryRepeated, high, highNext, h0, h2, h3, h4]

/-- The witness uses the existing carryPass on both sides. Even the whole family
of shift observations, total normalization charge, and present canonicality agree.
The next golden readouts differ by exactly one rational integer. -/
theorem actual_carry_closure_failure (k : Nat) :
    ∃ r s : RawDigits,
      rawValue r = 6 + 8 * k ∧ rawValue s = 6 + 8 * k ∧
      betaDigits r = betaDigits s ∧
      (∀ j, shiftedValue j r = shiftedValue j s) ∧
      carrySignedCount r = carrySignedCount s ∧
      ¬ CanonicalRaw r ∧ ¬ CanonicalRaw s ∧
      CarryStep r (carryPass r) ∧ CarryStep s (carryPass s) ∧
      betaDigits (carryPass r) + 1 = betaDigits (carryPass s) := by
  refine ⟨low k, high k, ?_, ?_, common_value k,
    (beta_eq_iff_all_shifts _ _).mp (common_value k),
    ((beta_eq_iff_value_charge _ _).mp (common_value k)).2,
    low_not_canonical k, high_not_canonical k,
    carryPass_step (low_not_canonical k), carryPass_step (high_not_canonical k), ?_⟩
  · norm_num [low, rawValue_add, rawValue_single, D5.S0.Conventions.wValue] <;> omega
  · norm_num [high, rawValue_add, rawValue_single, D5.S0.Conventions.wValue] <;> omega
  · rw [low_step, high_step]
    exact next_defect k

/-- A Boolean canonicality flag cannot repair the failure: no deterministic
next-golden-state map exists on this augmented, infinite shift-observation datum. -/
theorem no_shift_and_canonicality_next_map :
    ¬ ∃ f : (Nat → Nat) → Bool → GoldenInt,
      ∀ r : RawDigits, ∀ h : Decidable (CanonicalRaw r),
        f (fun j => shiftedValue j r) (@decide (CanonicalRaw r) h) =
          betaDigits (carryPass r) := by
  classical
  rintro ⟨f, hf⟩
  obtain ⟨r, s, _, _, _, hs, _, hr, ht, _, _, hd⟩ :=
    actual_carry_closure_failure 0
  have heq : (fun j => shiftedValue j r) = (fun j => shiftedValue j s) := funext hs
  have hfr := hf r (inferInstance : Decidable (CanonicalRaw r))
  have hfs := hf s (inferInstance : Decidable (CanonicalRaw s))
  simp [hr, ht] at hfr hfs
  rw [heq] at hfr
  have hout : betaDigits (carryPass r) = betaDigits (carryPass s) := hfr.symm.trans hfs
  have ha := congrArg GoldenInt.a hd
  rw [hout] at ha
  simp only [a_add, a_one] at ha
  omega

#print axioms actual_carry_closure_failure
#print axioms no_shift_and_canonicality_next_map

end D5.S1.Deficit.RawObservation.CarryStepClosure
