/- GID: D5/S1/Deficit/RawObservation/ShiftReadout
   generality: G
   mirror-B: none(waiver:new-formal-source)
   mirror-E: none(waiver:universal-algebraic-proof)
   anchors: []
   utility: none
   digest: Actual raw-position shifts identify the golden semantic state; their
     admissible display pairs form an exact cone and two observations determine all shifts. -/

import D5.S1.Deficit.RawObservation.RealizableFiber
import D5.S1.Digit.Admissibility.LeastDigitDecomposition

set_option autoImplicit false

namespace D5.S1.Deficit.RawObservation

open D5.S0.Carrier D5.S1.Digit D5.S1.Deficit.DoubleFaceLength
open D5.S1.Digit.Admissibility.LeastDigitDecomposition

/-- The actual natural readout after moving every raw digit k slots upward.
No normalization or canonical representative is substituted before the shift. -/
noncomputable def shiftedValue (k : Nat) (r : RawDigits) : Nat :=
  rawValue (shiftDigits k r)

/- A corresponding identity is private in GoldenModelSetSelfSimilar. The proof
is repeated locally to apply it to arbitrary, not only canonical, raw inputs. -/
private theorem beta_shift (k : Nat) (r : RawDigits) :
    betaDigits (shiftDigits k r) = phi ^ k * betaDigits r := by
  classical
  rw [betaDigits, shiftDigits, Finsupp.sum_mapDomain_index]
  · rw [betaDigits, Finsupp.mul_sum]
    apply Finsupp.sum_congr
    intro i _
    rw [show k + i + 2 = k + (i + 2) by omega, pow_add]
    ring
  · intro i
    simp
  · intro i c d
    push_cast
    ring

/-- This is the commuting square linking the displayed integer to actual raw shifts. -/
theorem shiftedValue_as_coordinate (k : Nat) (r : RawDigits) :
    (shiftedValue k r : Int) = (phi ^ k * betaDigits r).b := by
  change (rawValue (shiftDigits k r) : Int) = _
  rw [← betaDigits_b (shiftDigits k r), beta_shift]

@[simp] theorem shiftedValue_zero (r : RawDigits) : shiftedValue 0 r = rawValue r := by
  have h := shiftedValue_as_coordinate 0 r
  simpa [betaDigits_b] using h

theorem shiftedValue_one (r : RawDigits) :
    (shiftedValue 1 r : Int) = (betaDigits r).a + (rawValue r : Int) := by
  rw [shiftedValue_as_coordinate]
  simp [b_mul, betaDigits_b]

/-- A display pair determines the actual golden image by an explicit inverse formula. -/
theorem reconstruct_beta (r : RawDigits) :
    betaDigits r =
      (⟨(shiftedValue 1 r : Int) - (rawValue r : Int), (rawValue r : Int)⟩ : GoldenInt) := by
  apply GoldenInt.ext
  · have h := shiftedValue_one r
    dsimp
    omega
  · exact betaDigits_b r

/-- Exact consistency of two natural readouts with one common raw input. -/
theorem display_pair_iff (n m : Nat) :
    (∃ r : RawDigits, rawValue r = n ∧ shiftedValue 1 r = m) ↔
      3 * n ≤ 2 * m ∧ m ≤ 2 * n := by
  constructor
  · rintro ⟨r, hn, hm⟩
    have hc := beta_raw_cone r
    have hf := shiftedValue_one r
    rw [betaDigits_b, hn] at hc
    rw [hn, hm] at hf
    constructor <;> omega
  · intro h
    have hb : (m : Int) - n ≤ n ∧ (n : Int) ≤ 2 * ((m : Int) - n) := by
      constructor <;> omega
    obtain ⟨r, hn, ha⟩ := (display_fiber_iff n ((m : Int) - n)).mpr hb
    refine ⟨r, hn, ?_⟩
    have hf := shiftedValue_one r
    rw [hn, ha] at hf
    have he : (shiftedValue 1 r : Int) = (m : Int) := by omega
    exact_mod_cast he

/-- Two raw inputs have the same golden semantics exactly when the current and
one-shift readouts agree. This does not assert equality of raw inputs. -/
theorem beta_eq_iff_display_pair (r s : RawDigits) :
    betaDigits r = betaDigits s ↔
      rawValue r = rawValue s ∧ shiftedValue 1 r = shiftedValue 1 s := by
  constructor
  · intro h
    constructor
    · have hb := congrArg GoldenInt.b h
      rw [betaDigits_b, betaDigits_b] at hb
      exact_mod_cast hb
    · have hb := congrArg (fun z : GoldenInt => (phi ^ 1 * z).b) h
      rw [← shiftedValue_as_coordinate, ← shiftedValue_as_coordinate] at hb
      exact_mod_cast hb
  · rintro ⟨hn, hm⟩
    rw [reconstruct_beta r, reconstruct_beta s, hn, hm]

/-- The golden semantic kernel is precisely the kernel of all raw shift readouts. -/
theorem beta_eq_iff_all_shifts (r s : RawDigits) :
    betaDigits r = betaDigits s ↔ ∀ k : Nat, shiftedValue k r = shiftedValue k s := by
  constructor
  · intro h k
    have hb := congrArg (fun z : GoldenInt => (phi ^ k * z).b) h
    rw [← shiftedValue_as_coordinate, ← shiftedValue_as_coordinate] at hb
    exact_mod_cast hb
  · intro h
    apply (beta_eq_iff_display_pair r s).mpr
    exact ⟨by simpa using h 0, h 1⟩

/-- All later shift observations satisfy the actual Fibonacci recurrence. -/
theorem shiftedValue_recurrence (r : RawDigits) (k : Nat) :
    shiftedValue (k + 2) r = shiftedValue (k + 1) r + shiftedValue k r := by
  have hp : phi ^ (k + 2) = phi ^ (k + 1) + phi ^ k := by
    rw [pow_add, phi_sq, pow_succ]
    ring
  have hb := congrArg (fun z : GoldenInt => (z * betaDigits r).b) hp
  simp only [add_mul, b_add] at hb
  rw [← shiftedValue_as_coordinate, ← shiftedValue_as_coordinate,
    ← shiftedValue_as_coordinate] at hb
  exact_mod_cast hb

/-- For every display n>=2, two legal raw inputs give different one-shift outputs. -/
theorem every_nontrivial_display_ambiguous (n : Nat) (hn : 2 ≤ n) :
    ∃ r s : RawDigits, rawValue r = n ∧ rawValue s = n ∧
      shiftedValue 1 r ≠ shiftedValue 1 s := by
  obtain ⟨r, hr, hfr⟩ := (display_pair_iff n (2 * n)).mpr (by omega)
  obtain ⟨s, hs, hfs⟩ := (display_pair_iff n (2 * n - 1)).mpr (by omega)
  refine ⟨r, s, hr, hs, ?_⟩
  rw [hfr, hfs]
  omega

/-- A scalar display identifies the golden image exactly at values zero and one. -/
theorem display_determines_beta_iff (n : Nat) :
    (∀ r s : RawDigits, rawValue r = n → rawValue s = n →
      betaDigits r = betaDigits s) ↔ n ≤ 1 := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨r, s, hr, hs, hf⟩ := every_nontrivial_display_ambiguous n (by omega)
    exact hf ((beta_eq_iff_display_pair r s).mp (h r s hr hs)).2
  · intro hn r s hr hs
    have hcr := beta_raw_cone r
    have hcs := beta_raw_cone s
    rw [betaDigits_b, hr] at hcr
    rw [betaDigits_b, hs] at hcs
    apply GoldenInt.ext
    · omega
    · rw [betaDigits_b, betaDigits_b, hr, hs]

#print axioms display_pair_iff
#print axioms beta_eq_iff_all_shifts
#print axioms shiftedValue_recurrence
#print axioms display_determines_beta_iff

end D5.S1.Deficit.RawObservation
