/- GID: D5/S3/Arith/SignedDirichletPositiveResponse
   generality: G
   mirror-B: D5/B/S3/Arith/SignedDirichletPositiveResponse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.NumberTheory.Divisors]
   utility: none
   digest: Positive response to monotone forcing for signed divisor convolution. -/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace D5.S3.Arith.SignedDirichletPositiveResponse

open scoped BigOperators

/-- A positive head dominating the separate negative and positive divisor-tail
budgets gives a positive response to every nonnegative monotone forcing.
Neither positivity nor a global bound on the response is assumed. -/
theorem signedDivisor_positive_response
    (b f g : ℕ → ℝ) (E P : ℝ)
    (hg : ∀ n : ℕ, 0 < n → 0 ≤ g n)
    (hmono : ∀ m n : ℕ, 0 < m → m ≤ n → g m ≤ g n)
    (hnegative : ∀ n : ℕ, (∑ d ∈ n.divisors.erase 1, max (-b d) 0) ≤ E)
    (hpositive : ∀ n : ℕ, (∑ d ∈ n.divisors.erase 1, max (b d) 0) ≤ P)
    (hgap : E + P < b 1)
    (hconvolution : ∀ n : ℕ, 0 < n →
      (∑ d ∈ n.divisors, b d * f (n / d)) = g n) :
    ∀ n : ℕ, 0 < n →
      ((b 1 - E - P) / (b 1 * (b 1 - E))) * g n ≤ f n ∧
        f n ≤ g n / (b 1 - E) := by
  have hE : 0 ≤ E := by simpa using hnegative 1
  have hP : 0 ≤ P := by simpa using hpositive 1
  have hhead : 0 < b 1 := by linarith
  have hden : 0 < b 1 - E := by linarith
  have hmargin : 0 < b 1 - E - P := by linarith
  let K : ℝ := 1 / (b 1 - E)
  let L : ℝ := (b 1 - E - P) / (b 1 * (b 1 - E))
  have hK : 0 ≤ K := (div_pos zero_lt_one hden).le
  have hL : 0 ≤ L := (div_pos hmargin (mul_pos hhead hden)).le
  have hKidentity : (b 1 - E) * K = 1 := by
    dsimp [K]
    field_simp
  have hLidentity : b 1 * L + P * K = 1 := by
    dsimp [L, K]
    field_simp
    ring
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hsplit : b 1 * f n +
        (∑ d ∈ n.divisors.erase 1, b d * f (n / d)) = g n := by
      rw [← hconvolution n hn]
      simpa using Finset.add_sum_erase n.divisors
        (fun d => b d * f (n / d)) (Nat.one_mem_divisors.mpr (ne_of_gt hn))
    have hprevious : ∀ d ∈ n.divisors.erase 1,
        0 ≤ f (n / d) ∧ f (n / d) ≤ K * g n := by
      intro d hd
      obtain ⟨hd1, hdn⟩ := Finset.mem_erase.mp hd
      have hdpos := Nat.pos_of_mem_divisors hdn
      have hdle := Nat.divisor_le hdn
      have hdlarge : 1 < d := by omega
      have hqpos : 0 < n / d := Nat.div_pos hdle hdpos
      have hqlt : n / d < n := Nat.div_lt_self hn hdlarge
      have hqle : n / d ≤ n := Nat.div_le_self n d
      obtain ⟨hlower, hupper⟩ := ih (n / d) hqlt hqpos
      constructor
      · exact (mul_nonneg hL (hg (n / d) hqpos)).trans hlower
      · have hupper' : f (n / d) ≤ K * g (n / d) := by
          simpa [K, div_eq_mul_inv, mul_comm] using hupper
        exact hupper'.trans (mul_le_mul_of_nonneg_left
          (hmono (n / d) n hqpos hqle) hK)
    have hforcing : 0 ≤ K * g n := mul_nonneg hK (hg n hn)
    have htailupper : (∑ d ∈ n.divisors.erase 1, b d * f (n / d)) ≤
        P * (K * g n) := by
      calc
        _ ≤ ∑ d ∈ n.divisors.erase 1, max (b d) 0 * (K * g n) := by
          apply Finset.sum_le_sum
          intro d hd
          obtain ⟨hf0, hfbound⟩ := hprevious d hd
          exact (mul_le_mul_of_nonneg_right (le_max_left _ _) hf0).trans
            (mul_le_mul_of_nonneg_left hfbound (le_max_right _ _))
        _ = (∑ d ∈ n.divisors.erase 1, max (b d) 0) * (K * g n) :=
          (Finset.sum_mul _ _ _).symm
        _ ≤ P * (K * g n) :=
          mul_le_mul_of_nonneg_right (hpositive n) hforcing
    have htailnegative : -(∑ d ∈ n.divisors.erase 1, b d * f (n / d)) ≤
        E * (K * g n) := by
      calc
        _ = ∑ d ∈ n.divisors.erase 1, (-b d) * f (n / d) := by
          rw [← Finset.sum_neg_distrib]
          simp only [neg_mul]
        _ ≤ ∑ d ∈ n.divisors.erase 1, max (-b d) 0 * (K * g n) := by
          apply Finset.sum_le_sum
          intro d hd
          obtain ⟨hf0, hfbound⟩ := hprevious d hd
          exact (mul_le_mul_of_nonneg_right (le_max_left _ _) hf0).trans
            (mul_le_mul_of_nonneg_left hfbound (le_max_right _ _))
        _ = (∑ d ∈ n.divisors.erase 1, max (-b d) 0) * (K * g n) :=
          (Finset.sum_mul _ _ _).symm
        _ ≤ E * (K * g n) :=
          mul_le_mul_of_nonneg_right (hnegative n) hforcing
    constructor
    · change L * g n ≤ f n
      apply (mul_le_mul_iff_right₀ hhead).mp
      nlinarith [congrArg (fun x : ℝ => x * g n) hLidentity]
    · have hupper : f n ≤ K * g n := by
        apply (mul_le_mul_iff_right₀ hhead).mp
        nlinarith [congrArg (fun x : ℝ => x * g n) hKidentity]
      simpa [K, div_eq_mul_inv, mul_comm] using hupper

end D5.S3.Arith.SignedDirichletPositiveResponse
