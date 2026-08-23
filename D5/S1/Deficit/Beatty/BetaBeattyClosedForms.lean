/- GID: D5/S1/Deficit/Beatty/BetaBeattyClosedForms
   generality: I
   mirror-B: D5/B/S1/Deficit/Beatty/BetaBeattyClosedForms
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: First publicly states two closed forms previously private across frozen modules. -/

import D5.S1.Deficit.DoubleFaceLength
import D5.S1.Deficit.ZeckendorfDisplacementReading
import D5.S1.Scale.Fibonacci
import Mathlib

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'betaContraction_eq_displacement_sub_goldenRatio' D5
     Golden/Frozen/accepted` returned no matches; the analogous search for
     `betaReal_eq_displacement_sub_goldenConj` also returned no matches.
   * Searches for `betaContraction`, `betaReal`, `displacementDecode`, and the two
     target right-hand sides found exact proofs only as private theorems in
     `ZeckendorfNormSign`, `GoldenDesubstitutionClosedForms`, and
     `FixedModulusNoncongruence` (the last contains only the `betaReal` identity).
   * The proof reuses the public lemmas `betaGolden_b`,
     `betaReal_sub_betaContraction`, `Real.goldenRatio_add_goldenConj`, and
     `Real.goldenRatio_sub_goldenConj`. The missing first coordinate is reconstructed
     using Finsupp addition, the Fibonacci recurrence, and canonical Zeckendorf digits.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Deficit.BetaBeattyClosedForms

open D5.S0.Carrier
open D5.S0.Conventions
open D5.S1.Deficit
open D5.S1.Deficit.DoubleFaceLength
open D5.S1.Deficit.ZeckendorfDisplacementReading
open D5.S1.Digit
open D5.S1.Scale

local instance : IsTrans ℕ (fun a b => b + 2 ≤ a) where
  trans _ _ _ hab hbc := by omega

private theorem betaDigits_add (r s : RawDigits) :
    betaDigits (r + s) = betaDigits r + betaDigits s := by
  classical
  refine Finsupp.sum_add_index' (fun i => ?_) (fun i m₁ m₂ => ?_)
  · simp
  · push_cast
    ring

@[simp] private theorem betaDigits_single (i : ℕ) :
    betaDigits (Finsupp.single i 1) = phi ^ (i + 2) := by
  classical
  simp [betaDigits]

private theorem betaDigits_rawOfZeckendorf_a {digits : List ℕ}
    (hmin : ∀ k ∈ digits, 2 ≤ k) :
    (betaDigits (rawOfZeckendorf digits)).a =
      ((digits.map fun k => Nat.fib (k + 1)).sum : ℤ) -
        ((digits.map Nat.fib).sum : ℤ) := by
  induction digits with
  | nil => simp [rawOfZeckendorf, betaDigits]
  | cons k digits ih =>
      have hk : 2 ≤ k := hmin k (by simp)
      have htail : ∀ j ∈ digits, 2 ≤ j := by
        intro j hj
        exact hmin j (by simp [hj])
      have hraw : rawOfZeckendorf (k :: digits) =
          Finsupp.single (k - 2) 1 + rawOfZeckendorf digits := by
        rw [rawOfZeckendorf, List.map_cons]
        change Multiset.toFinsupp ({k - 2} +
          (digits.map fun j => j - 2 : Multiset ℕ)) = _
        rw [Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]
        rfl
      rw [hraw, betaDigits_add, a_add, betaDigits_single, ih htail]
      rw [show k - 2 + 2 = k by omega]
      rw [show k = (k - 1) + 1 by omega, golden_phi_pow_a_eq_fib]
      simp only [List.map_cons, List.sum_cons]
      have hk1 : k - 1 + 1 = k := by omega
      have hk2 : k - 1 + 2 = k + 1 := by omega
      simp only [hk1]
      rw [show Nat.fib (k + 1) = Nat.fib (k - 1) + Nat.fib k by
        simpa only [hk1, hk2] using Nat.fib_add_two (n := k - 1)]
      push_cast
      ring

private theorem canonical_two_le {digits : List ℕ} (h : digits.IsZeckendorfRep) :
    ∀ k ∈ digits, 2 ≤ k := by
  rw [List.IsZeckendorfRep, List.isChain_iff_pairwise] at h
  intro k hk
  exact (List.pairwise_append.mp h).2.2 k hk 0 (by simp)

private theorem betaGolden_a (v : ℕ) :
    (betaGolden v).a = (displacementDecode v : ℤ) - v := by
  rw [betaGolden, toRaw, Z, wEncoding]
  change (betaDigits (rawOfZeckendorf (wdigits v))).a = _
  rw [betaDigits_rawOfZeckendorf_a]
  · simp [displacementDecode, decode_wdigits]
  · intro k hk
    exact canonical_two_le (wdigits_isCanonical v) k hk

/-- The expanding beta reading is the integer Zeckendorf displacement minus the
golden-conjugate multiple of its input. -/
theorem betaReal_eq_displacement_sub_goldenConj (v : ℕ) :
    betaReal v = (displacementDecode v : ℝ) - (v : ℝ) * Real.goldenConj := by
  rw [betaReal, embedding_apply, betaGolden_a, betaGolden_b]
  push_cast
  rw [show Real.goldenRatio = 1 - Real.goldenConj by
    linarith [Real.goldenRatio_add_goldenConj]]
  ring

/-- The contracting beta reading is the integer Zeckendorf displacement minus the
golden-ratio multiple of its input. -/
theorem betaContraction_eq_displacement_sub_goldenRatio (v : ℕ) :
    betaContraction v = (displacementDecode v : ℝ) - (v : ℝ) * Real.goldenRatio := by
  have hspread := betaReal_sub_betaContraction v
  rw [betaReal_eq_displacement_sub_goldenConj,
    ← Real.goldenRatio_sub_goldenConj] at hspread
  linear_combination -hspread

example :
    betaContraction 5 =
      (displacementDecode 5 : ℝ) - (5 : ℝ) * Real.goldenRatio :=
  betaContraction_eq_displacement_sub_goldenRatio 5

example :
    betaReal 5 = (displacementDecode 5 : ℝ) - (5 : ℝ) * Real.goldenConj :=
  betaReal_eq_displacement_sub_goldenConj 5

#print axioms betaContraction_eq_displacement_sub_goldenRatio
#print axioms betaReal_eq_displacement_sub_goldenConj

end D5.S1.Deficit.BetaBeattyClosedForms
