/- GID: D5/S1/Digit/ZumkellerBinaryGaussianEvaluationZeroMultipleOfFive
   generality: G
   mirror-B: D5/B/S1/Digit/ZumkellerBinaryGaussianEvaluationZeroMultipleOfFive
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.NumberTheory.Zsqrtd.GaussianInt, mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: none
   digest: Zumkeller's binary Gaussian evaluation zero implies divisibility by five. -/

import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Data.ZMod.Basic

namespace D5.S1.Digit.ZumkellerBinaryGaussianEvaluationZeroMultipleOfFive

open GaussianInt

/-- The binary digit polynomial evaluated at the Gaussian imaginary unit.

    `Nat.binaryRec` strips the least significant bit at each step, so this is
    exactly the digit sum `Σ d_k i^k` from OEIS A131851, with the low bit
    contributing the leading summand and the remaining digits multiplied by
    `i`.
-/
def z : ℕ → GaussianInt :=
  Nat.binaryRec 0 (fun b _ w => (if b then 1 else 0) + (⟨0, 1⟩ : GaussianInt) * w)

private theorem invariant : ∀ n : ℕ,
    (n : ZMod 5) = (z n).re + 2 * (z n).im := by
  intro n
  induction n using Nat.binaryRec with
  | zero => simp [z]
  | bit b n ih =>
      have hz : z (Nat.bit b n) =
          (if b then 1 else 0) + (⟨0, 1⟩ : GaussianInt) * z n := by
        simpa [z] using
          (Nat.binaryRec_eq (motive := fun _ => GaussianInt)
            (zero := (0 : GaussianInt))
            (bit := fun b _ w =>
              (if b then 1 else 0) + (⟨0, 1⟩ : GaussianInt) * w)
            b n (by simp))
      rw [hz]
      rw [Nat.bit_val]
      have h4 : (4 : ZMod 5) = -1 := by decide
      cases b <;> simp [ih]
      · ring_nf
        rw [h4]
        ring
      · ring_nf
        rw [h4]
        ring

/-- If the binary digit evaluation vanishes, its argument is a multiple of 5. -/
theorem zumkeller_a131853 : ∀ m : ℕ, z m = 0 → 5 ∣ m := by
  intro m hm
  have hmod : (m : ZMod 5) = 0 := by
    rw [invariant m, hm]
    simp
  exact (ZMod.natCast_eq_zero_iff m 5).mp hmod

#print axioms zumkeller_a131853

end D5.S1.Digit.ZumkellerBinaryGaussianEvaluationZeroMultipleOfFive
