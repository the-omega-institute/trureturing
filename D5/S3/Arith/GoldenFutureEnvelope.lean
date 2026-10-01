/- GID: D5/S3/Arith/GoldenFutureEnvelope
   generality: I
   mirror-B: D5/B/S3/Arith/GoldenFutureEnvelope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The attained objective on positive multiples is the least prime-step safe envelope. -/

import D5.S3.Arith.GoldenFutureExtensionMaximum
import Mathlib.Data.Nat.Factorization.Induction

namespace D5.S3.Arith.GoldenFutureEnvelope

open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenFutureExtensionMaximum

noncomputable section

/-- The maximum priced divisor benefit over all positive multiples of the base integer. -/
def goldenFutureEnvelope (lambda : ℝ) (n : ℕ) : ℝ :=
  sSup (goldenResourceObjective lambda '' {m : ℕ | n ∣ m ∧ 1 ≤ m})

/-- The future envelope majorizes the current objective, decreases under every prime step,
and is pointwise least among all functions with these two properties on positive integers. -/
theorem golden_future_envelope_least {lambda : ℝ} (hlambda : 0 < lambda) :
    (∀ n : ℕ, 1 ≤ n → goldenResourceObjective lambda n ≤ goldenFutureEnvelope lambda n) ∧
    (∀ p : ℕ, p.Prime → ∀ n : ℕ, 1 ≤ n →
      goldenFutureEnvelope lambda (p * n) ≤ goldenFutureEnvelope lambda n) ∧
    (∀ U : ℕ → ℝ,
      (∀ n : ℕ, 1 ≤ n → goldenResourceObjective lambda n ≤ U n) →
      (∀ p : ℕ, p.Prime → ∀ n : ℕ, 1 ≤ n → U (p * n) ≤ U n) →
      ∀ n : ℕ, 1 ≤ n → goldenFutureEnvelope lambda n ≤ U n) := by
  have attained (n : ℕ) (hn : 1 ≤ n) :
      ∃ m : ℕ, n ∣ m ∧ 1 ≤ m ∧
        goldenFutureEnvelope lambda n = goldenResourceObjective lambda m ∧
        ∀ k : ℕ, n ∣ k → 1 ≤ k →
          goldenResourceObjective lambda k ≤ goldenFutureEnvelope lambda n := by
    obtain ⟨m, hnm, hm, hmax⟩ := golden_future_extension_maximum_attained hlambda hn
    have hg : IsGreatest
        (goldenResourceObjective lambda '' {k : ℕ | n ∣ k ∧ 1 ≤ k})
        (goldenResourceObjective lambda m) := by
      refine ⟨⟨m, ⟨hnm, hm⟩, rfl⟩, ?_⟩
      rintro _ ⟨k, hk, rfl⟩
      exact (sub_le_sub_iff_right _).mp (hmax k hk.1 hk.2)
    have heq : goldenFutureEnvelope lambda n = goldenResourceObjective lambda m :=
      hg.csSup_eq
    exact ⟨m, hnm, hm, heq, fun k hk hpos => heq.symm ▸ hg.2 ⟨k, ⟨hk, hpos⟩, rfl⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, _, _, _, hmax⟩ := attained n hn
    exact hmax n dvd_rfl hn
  · intro p hp n hn
    obtain ⟨m, hpm, hm, heq, _⟩ := attained (p * n) (Nat.mul_pos hp.pos hn)
    obtain ⟨k, _, _, _, hmax⟩ := attained n hn
    rw [heq]
    exact hmax m ((dvd_mul_left n p).trans hpm) hm
  · intro U hmajor hstep n hn
    have factor_induction : ∀ q : ℕ, q ≠ 0 →
        ∀ a : ℕ, 1 ≤ a → U (a * q) ≤ U a := by
      intro q
      induction q using induction_on_primes with
      | zero => simp
      | one => simp
      | prime_mul p q hp ih =>
        intro hpq a ha
        have hq : q ≠ 0 := right_ne_zero_of_mul hpq
        calc
          U (a * (p * q)) = U (p * (a * q)) := by rw [mul_left_comm a p q]
          _ ≤ U (a * q) := hstep p hp (a * q) (Nat.mul_pos ha (Nat.pos_of_ne_zero hq))
          _ ≤ U a := ih hq a ha
    obtain ⟨m, hnm, hm, heq, _⟩ := attained n hn
    obtain ⟨q, rfl⟩ := hnm
    have hq : q ≠ 0 := right_ne_zero_of_mul (by omega : n * q ≠ 0)
    rw [heq]
    exact (hmajor (n * q) hm).trans (factor_induction q hq n hn)

#print axioms golden_future_envelope_least

end
end D5.S3.Arith.GoldenFutureEnvelope
