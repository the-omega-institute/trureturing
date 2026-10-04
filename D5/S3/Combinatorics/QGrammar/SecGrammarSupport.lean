/- GID: D5/S3/Combinatorics/QGrammar/SecGrammarSupport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/QGrammar/SecGrammarSupport
   mirror-E: none(waiver:positive-grammar-support)
   anchors: [mathlib/module/Mathlib.Algebra.Polynomial.Coeff]
   utility: none
   digest: Nonnegative polynomial coefficients prevent cancellation in the Sec grammar. -/

import D5.S3.Combinatorics.QGrammar.SecGrammarDefs
import Mathlib.Algebra.Polynomial.Coeff

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.QGrammar.SecGrammar

open Polynomial SecGrammarDefs

/-- The derivative preserves coefficient positivity, and its support consists exactly of
the normalized positional branches of support words. Colliding branches cannot cancel. -/
theorem support_reduction (n : ℕ) :
    (∀ w d, 0 ≤ ((deriv^[n] (Finsupp.single [(true, 0)] 1)) w).coeff d) ∧
    ∀ z, z ∈ (deriv^[n + 1] (Finsupp.single [(true, 0)] 1)).support ↔
      ∃ w ∈ (deriv^[n] (Finsupp.single [(true, 0)] 1)).support,
        ∃ j < w.length, ∃ t ∈ (rule (w.getD j (false, 0))).support,
          dio (w.take j ++ t ++ up (w.drop (j + 1))) = z := by
  classical
  have step (E : List Var →₀ ℤ[X]) (hE : ∀ w d, 0 ≤ (E w).coeff d) :
      (∀ w d, 0 ≤ (deriv E w).coeff d) ∧
      ∀ z, z ∈ (deriv E).support ↔
        ∃ w ∈ E.support, ∃ j < w.length,
          ∃ t ∈ (rule (w.getD j (false, 0))).support,
            dio (w.take j ++ t ++ up (w.drop (j + 1))) = z := by
    classical
    have sum_nonneg {ι : Type} (s : Finset ι) (f : ι → ℤ[X])
        (hf : ∀ i ∈ s, ∀ d, 0 ≤ (f i).coeff d) :
        ∀ d, 0 ≤ (∑ i ∈ s, f i).coeff d := by
      intro d
      rw [finsetSum_coeff]
      exact Finset.sum_nonneg fun i hi => hf i hi d
    have sum_nonzero {ι : Type} (s : Finset ι) (f : ι → ℤ[X])
        (hf : ∀ i ∈ s, ∀ d, 0 ≤ (f i).coeff d) :
        (∑ i ∈ s, f i) ≠ 0 ↔ ∃ i ∈ s, f i ≠ 0 := by
      constructor
      · exact Finset.exists_ne_zero_of_sum_ne_zero
      · rintro ⟨i, hi, hfi⟩ hzero
        apply hfi
        ext d
        have hd : (∑ k ∈ s, (f k).coeff d) = 0 := by
          rw [← finsetSum_coeff, hzero, coeff_zero]
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun k hk => hf k hk d)).mp hd i hi
    have mul_nonneg (p q : ℤ[X]) (hp : ∀ d, 0 ≤ p.coeff d)
        (hq : ∀ d, 0 ≤ q.coeff d) : ∀ d, 0 ≤ (p * q).coeff d := by
      intro d
      rw [coeff_mul]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (hp k.1) (hq k.2)
    have rule_nonneg (v : Var) : ∀ t d, 0 ≤ (rule v t).coeff d := by
      intro t d
      have hx : 0 ≤ (X ^ v.2 : ℤ[X]).coeff d := by
        rw [coeff_X_pow]
        split_ifs <;> norm_num
      unfold rule
      split_ifs
      · simp only [Finsupp.single_apply]
        split_ifs <;> simp_all
      · simp only [Finsupp.add_apply, coeff_add, Finsupp.single_apply]
        split_ifs <;> simp_all
    have single_nonneg (t z : List Var) (p : ℤ[X]) (hp : ∀ d, 0 ≤ p.coeff d) :
        ∀ d, 0 ≤ (Finsupp.single t p z).coeff d := by
      intro d
      simp only [Finsupp.single_apply]
      split_ifs
      · exact hp d
      · simp
    have word_nonneg (w : List Var) : ∀ z d, 0 ≤ (derivWord w z).coeff d := by
      intro z d
      unfold derivWord
      simp only [Finsupp.finsetSum_apply]
      apply sum_nonneg _ _ _ d
      intro j _ k
      simp only [Finsupp.sum, Finsupp.finsetSum_apply]
      apply sum_nonneg _ _ _ k
      intro t _
      exact single_nonneg _ _ _ (rule_nonneg _ t)
    have word_support (w z : List Var) : derivWord w z ≠ 0 ↔
        ∃ j < w.length, ∃ t ∈ (rule (w.getD j (false, 0))).support,
          dio (w.take j ++ t ++ up (w.drop (j + 1))) = z := by
      unfold derivWord
      simp only [Finsupp.finsetSum_apply]
      have hn (j : ℕ) : ∀ d, 0 ≤
          (((rule (w.getD j (false, 0))).sum fun t c =>
            Finsupp.single (dio (w.take j ++ t ++ up (w.drop (j + 1)))) c) z).coeff d := by
        simp only [Finsupp.sum, Finsupp.finsetSum_apply]
        apply sum_nonneg
        intro t _
        exact single_nonneg _ _ _ (rule_nonneg _ t)
      rw [sum_nonzero _ _ (fun j _ => hn j)]
      simp only [Finset.mem_range]
      apply exists_congr
      intro j
      apply and_congr_right
      intro _
      simp only [Finsupp.sum, Finsupp.finsetSum_apply]
      rw [sum_nonzero _ _ (fun t _ => single_nonneg _ _ _ (rule_nonneg _ t))]
      apply exists_congr
      intro t
      apply and_congr_right
      intro ht
      have hc := Finsupp.mem_support_iff.mp ht
      simp only [Finsupp.single_apply]
      split_ifs with he
      · exact iff_of_true hc he
      · exact iff_of_false (by simp) he
    constructor
    · intro z d
      unfold deriv
      simp only [Finsupp.sum, Finsupp.finsetSum_apply]
      apply sum_nonneg _ _ _ d
      intro w _
      simpa only [Finsupp.smul_apply, smul_eq_mul] using
        mul_nonneg (E w) (derivWord w z) (hE w) (word_nonneg w z)
    · intro z
      rw [Finsupp.mem_support_iff]
      unfold deriv
      simp only [Finsupp.sum, Finsupp.finsetSum_apply]
      have hn (w : List Var) : ∀ d, 0 ≤ ((E w • derivWord w) z).coeff d := by
        simpa only [Finsupp.smul_apply, smul_eq_mul] using
          mul_nonneg (E w) (derivWord w z) (hE w) (word_nonneg w z)
      rw [sum_nonzero _ _ (fun w _ => hn w)]
      apply exists_congr
      intro w
      apply and_congr_right
      intro hw
      rw [Finsupp.smul_apply, smul_eq_mul, mul_ne_zero_iff]
      exact (and_iff_right (Finsupp.mem_support_iff.mp hw)).trans (word_support w z)
  have positive (m : ℕ) :
      ∀ w d, 0 ≤ ((deriv^[m] (Finsupp.single [(true, 0)] 1)) w).coeff d := by
    induction m with
    | zero =>
      intro w d
      simp only [Function.iterate_zero, id_eq, Finsupp.single_apply]
      split_ifs <;> simp [coeff_one] <;> split_ifs <;> norm_num
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact (step _ ih).1
  refine ⟨positive n, ?_⟩
  rw [Function.iterate_succ_apply']
  exact (step _ (positive n)).2

end D5.S3.Combinatorics.QGrammar.SecGrammar
