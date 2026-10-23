/- GID: D5/S3/Quantum/Schatten/PowerMajorization
   generality: G
   mirror-B: D5/B/S3/Quantum/Schatten/PowerMajorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Singular value power sums and their finite Holder bound. -/

/-
Attributed source: leanprover-community/physlib, revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142.
Original module: QuantumInfo/ForMathlib/Majorization.lean.
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
Full license: docs/reports/inoutbalance/physlib-LICENSE.txt.
Retire this transplant when an equivalent consumed declaration exists in the
repository-pinned Mathlib, replacing it by direct application.
No mathematical originality is claimed for the attributed source.
-/
module

public import D5.S3.Quantum.Schatten.ProductLogMajorization

@[expose] public section

open Finset BigOperators Matrix
open scoped AllOrdered
variable {d : Type*} [Fintype d] [DecidableEq d]
noncomputable section

/-! ### Weak log-majorization implies sum of powers inequality -/

/-- Raising nonneg antitone sequences to a positive power preserves antitonicity. -/
lemma rpow_antitone_of_nonneg_antitone {n : ℕ}
    {f : Fin n → ℝ} (hf : Antitone f) (hf_nn : ∀ i, 0 ≤ f i)
    {r : ℝ} (hr : 0 < r) :
    Antitone (fun i => f i ^ r) := by
  exact fun i j hij => Real.rpow_le_rpow (hf_nn _) (hf hij) hr.le

/-- Weak log-majorization is preserved under positive powers. -/
lemma rpow_preserves_weak_log_maj {n : ℕ}
    {x y : Fin n → ℝ}
    (hx_nn : ∀ i, 0 ≤ x i) (hy_nn : ∀ i, 0 ≤ y i)
    (h_log_maj : ∀ (k : ℕ) (_ : k ≤ n),
      ∏ i : Fin k, x ⟨i.val, by omega⟩ ≤
      ∏ i : Fin k, y ⟨i.val, by omega⟩)
    {r : ℝ} (hr : 0 < r) :
    ∀ (k : ℕ) (_ : k ≤ n),
      ∏ i : Fin k, (fun j => x j ^ r) ⟨i.val, by omega⟩ ≤
      ∏ i : Fin k, (fun j => y j ^ r) ⟨i.val, by omega⟩ := by
  intro k hk
  convert Real.rpow_le_rpow _ (h_log_maj k hk) hr.le using 1 <;>
    norm_num [Real.finsetProd_rpow _ _ fun i _ => hx_nn _,
              Real.finsetProd_rpow _ _ fun i _ => hy_nn _]
  exact Finset.prod_nonneg fun _ _ => hx_nn _

/-
The Abel summation identity (a rewriting of the sum) gives:
∑_{i=0}^{n-1} x_i * d_i = x_{n-1} * D_{n-1} + ∑_{i=0}^{n-2} (x_i - x_{i+1}) * D_i
(This is essentially Finset.sum_range_by_parts with f = x and g = d.)
Each term is nonneg because:
- x_{n-1} ≥ 0 (positive) and D_{n-1} ≥ 0 (see below)
- x_i - x_{i+1} ≥ 0 (x is antitone) and D_i ≥ 0 (see below)
D_k = ∑_{j=0}^k log(y_j/x_j) = log(∏_{j=0}^k y_j/x_j) = log(∏ y_j / ∏ x_j) ≥ log(1) = 0
because ∏ y_j ≥ ∏ x_j (weak log-majorization) and both products are positive.
So ∑ x_i * d_i is a sum of nonneg terms, hence ≥ 0.
Use Finset.sum_range_by_parts from Mathlib. The key Mathlib lemma is:
Finset.sum_range_by_parts f g n = f (n-1) • ∑_{i<n} g i - ∑_{i<n-1} (f(i+1) - f(i)) • ∑_{j<i+1} g j
Here f i = x ⟨i, ...⟩ (antitone) and g i = log(y ⟨i,...⟩ / x ⟨i,...⟩).
Actually, it may be easier to prove this directly by induction on n, without using Finset.sum_range_by_parts. The induction step would split off the last term and use the IH.
For the direct induction approach on n:
- n = 0: sum is empty, 0 ≥ 0.
- n = 1: x_0 * log(y_0/x_0) ≥ 0 since x_0 > 0 and log(y_0/x_0) ≥ 0 (from ∏_{i<1} x_i ≤ ∏_{i<1} y_i, i.e., x_0 ≤ y_0, so y_0/x_0 ≥ 1, so log(y_0/x_0) ≥ 0).
- n+1 → n+2: Split ∑_{i=0}^{n+1} x_i * log(y_i/x_i) = ∑_{i=0}^{n} x_i * log(y_i/x_i) + x_{n+1} * log(y_{n+1}/x_{n+1}).
  Now ∑_{i=0}^{n} x_i * log(y_i/x_i) ≥ ∑_{i=0}^{n} x_{n+1} * log(y_i/x_i) (since x_i ≥ x_{n+1} and log(y_i/x_i) could be negative, but x_i * log(y_i/x_i) ≥ x_{n+1} * log(y_i/x_i) when log(y_i/x_i) ≥ 0).
Hmm, this doesn't work cleanly because log(y_i/x_i) can be negative for some i.
Better approach: prove it directly using the Abel summation identity and nonnegativity of each term.
-/
lemma sum_mul_log_nonneg_of_weak_log_maj {n : ℕ}
    {x y : Fin n → ℝ}
    (hx_pos : ∀ i, 0 < x i) (hy_pos : ∀ i, 0 < y i)
    (hx_anti : Antitone x)
    (h_log_maj : ∀ (k : ℕ) (_ : k ≤ n),
      ∏ i : Fin k, x ⟨i.val, by omega⟩ ≤
      ∏ i : Fin k, y ⟨i.val, by omega⟩) :
    0 ≤ ∑ i, x i * Real.log (y i / x i) := by
  by_contra h_neg
  -- Let $d_i = \log(y_i / x_i)$ and $D_k = \sum_{j=0}^{k} d_j$.
  set d : Fin n → ℝ := fun i => Real.log (y i / x i)
  set D : Fin n → ℝ := fun k => ∑ i ∈ Finset.Iic k, d i
  -- By Abel's summation formula, we have $\sum_{i=0}^{n-1} x_i d_i = x_{n-1} D_{n-1} + \sum_{i=0}^{n-2} (x_i - x_{i+1}) D_i$.
  have hn : n ≠ 0 := by rintro rfl; simp at h_neg
  have h_abel : ∑ i, x i * d i = x ⟨n - 1, by omega⟩ * D ⟨n - 1, by omega⟩ + ∑ i : Fin (n - 1),
      (x ⟨i.val, by omega⟩ - x ⟨i.val + 1, by omega⟩) * D ⟨i.val, by omega⟩ := by
    rcases n with ⟨⟩ <;> norm_num at *
    rename_i n
    have h_abel : ∀ m : Fin (n + 1), ∑ i ∈ Finset.Iic m, x i * d i = x m * D m + ∑ i ∈ Finset.Iio m, (x i - x (i + 1)) * D i := by
      intro m
      induction' m using Fin.inductionOn with m ih
      · simp +zetaDelta at *
        rw [Finset.sum_eq_single 0, Finset.sum_eq_single 0] <;> aesop
      · rw [show (Finset.Iic (Fin.succ m) : Finset (Fin (n + 1))) = Finset.Iic (Fin.castSucc m) ∪ { Fin.succ m } from ?_, Finset.sum_union] <;> norm_num [Finset.sum_singleton, Finset.sum_union, Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc)] at *
        · rw [show (Finset.Iio (Fin.succ m) : Finset (Fin (n + 1))) = Finset.Iio (Fin.castSucc m) ∪ { Fin.castSucc m } from ?_, Finset.sum_union] <;> norm_num [Finset.sum_singleton, Finset.sum_union, Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc)] at *
          · rw [ih]
            ring_nf!
            rw [show (Finset.Iic (Fin.succ m) : Finset (Fin (n + 1))) = Finset.Iic (Fin.castSucc m) ∪ { Fin.succ m } from ?_, Finset.sum_union] <;> norm_num; ring!
            ext i; simp [Finset.mem_Iic, Finset.mem_insert]
            exact ⟨fun hi => or_iff_not_imp_left.mpr fun hi' => Nat.le_of_lt_succ <| hi.lt_of_ne hi', fun hi => hi.elim (fun hi => hi.symm ▸ le_rfl) fun hi => Nat.le_trans hi (Nat.le_succ _)⟩
          · ext i; simp [Fin.lt_def, Fin.le_iff_val_le_val]
        · ext i; simp [Finset.mem_Iic, Finset.mem_insert]
          exact ⟨fun hi => or_iff_not_imp_left.mpr fun hi' => Nat.le_of_lt_succ <| hi.lt_of_ne hi', fun hi => hi.elim (fun hi => hi.symm ▸ le_rfl) fun hi => Nat.le_trans hi (Nat.le_succ _)⟩
    convert h_abel ⟨n, Nat.lt_succ_self _⟩ using 1
    · rw [show (Iic ⟨n, Nat.lt_succ_self _⟩ : Finset (Fin (n + 1))) = Finset.univ from Finset.eq_univ_of_forall fun i => Finset.mem_Iic.mpr (Nat.le_of_lt_succ i.2)]
    · refine' congr rfl (Finset.sum_bij (fun i hi => ⟨i, by omega⟩) _ _ _ _) <;> simp [Fin.add_def, Nat.mod_eq_of_lt]
      · exact fun i j h => Fin.ext h
      · exact fun i hi => ⟨⟨i, by linarith [Fin.is_lt i, show (i : ℕ) < n from hi]⟩, rfl⟩
  -- Since $D_k \geq 0$ for all $k$, we have $x_{n-1} D_{n-1} \geq 0$ and $(x_i - x_{i+1}) D_i \geq 0$ for all $i$.
  have h_nonneg : ∀ k : Fin n, 0 ≤ D k := by
    intro k
    have h_prod : ∏ i ∈ Finset.Iic k, y i ≥ ∏ i ∈ Finset.Iic k, x i := by
      specialize h_log_maj (k + 1) (by linarith [Fin.is_lt k])
      rw [show (Finset.Iic k : Finset (Fin n)) = Finset.image (fun i : Fin (k + 1) => ⟨i, by linarith [Fin.is_lt k, Fin.is_lt i]⟩) Finset.univ from ?_, Finset.prod_image] <;> norm_num
      · rwa [Finset.prod_image <| by intros i hi j hj hij; simpa [Fin.ext_iff] using hij]
      · intro i j hij
        exact Fin.ext <| by simpa using congr_arg Fin.val hij
      · ext ⟨i, hi⟩; simp [Fin.ext_iff, Fin.le_iff_val_le_val]
        exact ⟨fun hi' => ⟨⟨i, by linarith [Fin.is_lt k]⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ Nat.le_trans (Nat.le_of_lt_succ (by linarith [Fin.is_lt a, Fin.is_lt k])) (Nat.le_refl _)⟩
    simp +zetaDelta at *
    rw [← Real.log_prod fun i hi => ne_of_gt (div_pos (hy_pos i) (hx_pos i))]; exact Real.log_nonneg (by rw [Finset.prod_div_distrib]; exact by rw [le_div_iff₀ (Finset.prod_pos fun i hi => hx_pos i)]; linarith)
  exact h_neg <| h_abel.symm ▸ add_nonneg (mul_nonneg (le_of_lt (hx_pos _)) (h_nonneg _)) (Finset.sum_nonneg fun i hi => mul_nonneg (sub_nonneg.mpr (hx_anti <| Nat.le_succ _)) (h_nonneg _))

/-
PROBLEM
For positive reals a, b: b - a ≥ a · log(b/a).
Equivalently: t - 1 ≥ log(t) for t = b/a.
PROVIDED SOLUTION
We need b - a ≥ a * log(b/a) for a, b > 0. Equivalently, dividing by a > 0: b/a - 1 ≥ log(b/a). Let t = b/a > 0. Then we need t - 1 ≥ log(t), which is equivalent to log(t) ≤ t - 1. This is Real.log_le_sub_one_of_le or follows from Real.add_one_le_exp: for any x, 1 + x ≤ exp(x). Taking x = log(t): 1 + log(t) ≤ exp(log(t)) = t, so log(t) ≤ t - 1. Multiply by a > 0 to get a * log(b/a) ≤ a * (b/a - 1) = b - a.
-/
lemma sub_ge_mul_log_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    b - a ≥ a * Real.log (b / a) := by
  nlinarith [Real.log_le_sub_one_of_pos (div_pos hb ha), mul_div_cancel₀ b ha.ne']

/- Weak log-majorization of nonneg antitone sequences implies the sum inequality ∑ x_i ≤ ∑ y_i. -/
lemma weak_log_maj_sum_le {n : ℕ}
    {x y : Fin n → ℝ}
    (hx_nn : ∀ i, 0 ≤ x i) (hy_nn : ∀ i, 0 ≤ y i)
    (hx_anti : Antitone x) (hy_anti : Antitone y)
    (h_log_maj : ∀ (k : ℕ) (_ : k ≤ n),
      ∏ i : Fin k, x ⟨i.val, by omega⟩ ≤
      ∏ i : Fin k, y ⟨i.val, by omega⟩) :
    ∑ i, x i ≤ ∑ i, y i := by
  induction' n with n ih
  · norm_num +zetaDelta at *
  · by_cases h_last : x (Fin.last n) = 0
    · simp [Fin.sum_univ_castSucc, h_last]
      refine le_add_of_le_of_nonneg (ih (fun i => hx_nn _) (fun i => hy_nn _) (fun i j hij => hx_anti hij) (fun i j hij => hy_anti hij) ?_) (hy_nn _)
      intro k hk
      simp
      exact h_log_maj k (by linarith)
    · -- Since $x_{\text{last}} > 0$, we have $x_i > 0$ for all $i$.
      have hx_pos : ∀ i, 0 < x i := by
        exact fun i => lt_of_lt_of_le (lt_of_le_of_ne (hx_nn _) (Ne.symm h_last)) (hx_anti (Fin.le_last _))
      have hy_pos : ∀ i, 0 < y i := by
        intro i; specialize h_log_maj (n + 1) le_rfl; contrapose! h_log_maj; simp_all [Fin.prod_univ_castSucc]
        exact lt_of_le_of_lt (mul_nonpos_of_nonneg_of_nonpos (Finset.prod_nonneg fun _ _ => hy_nn _) (by linarith [hy_anti (show i ≤ Fin.last n from Fin.le_last i)])) (mul_pos (Finset.prod_pos fun _ _ => hx_pos _) (hx_pos _))
      have h_sum_mul_log_nonneg : 0 ≤ ∑ i, x i * Real.log (y i / x i) := by
        apply sum_mul_log_nonneg_of_weak_log_maj (fun i => hx_pos i) (fun i => hy_pos i) hx_anti (fun k hk => h_log_maj k hk)
      have h_sum_mul_log_nonneg : ∑ i, (y i - x i) ≥ ∑ i, x i * Real.log (y i / x i) := by
        exact Finset.sum_le_sum fun i _ => by have := sub_ge_mul_log_div (hx_pos i) (hy_pos i); ring_nf at *; linarith
      norm_num at *; linarith

/-- Weak log-majorization of nonneg antitone sequences implies the sum of
powers inequality. -/
lemma weak_log_maj_sum_rpow_le {n : ℕ}
    {x y : Fin n → ℝ}
    (hx_nn : ∀ i, 0 ≤ x i) (hy_nn : ∀ i, 0 ≤ y i)
    (hx_anti : Antitone x) (hy_anti : Antitone y)
    (h_log_maj : ∀ (k : ℕ) (_ : k ≤ n),
      ∏ i : Fin k, x ⟨i.val, by omega⟩ ≤
      ∏ i : Fin k, y ⟨i.val, by omega⟩)
    {r : ℝ} (hr : 0 < r) :
    ∑ i, x i ^ r ≤ ∑ i, y i ^ r := by
  apply weak_log_maj_sum_le
  · exact fun i => Real.rpow_nonneg (hx_nn i) r
  · exact fun i => Real.rpow_nonneg (hy_nn i) r
  · exact rpow_antitone_of_nonneg_antitone hx_anti hx_nn hr
  · exact rpow_antitone_of_nonneg_antitone hy_anti hy_nn hr
  · exact rpow_preserves_weak_log_maj hx_nn hy_nn h_log_maj hr

/-! ## Key singular value inequality for products -/

lemma sum_rpow_singularValues_mul_le (A B : Matrix d d ℂ) {r : ℝ} (hr : 0 < r) :
    ∑ i : Fin (Fintype.card d), singularValuesSorted (A * B) i ^ r ≤
    ∑ i : Fin (Fintype.card d),
      (singularValuesSorted A i ^ r * singularValuesSorted B i ^ r) := by
  have h_rw : ∀ i : Fin (Fintype.card d),
      singularValuesSorted A i ^ r * singularValuesSorted B i ^ r =
      (singularValuesSorted A i * singularValuesSorted B i) ^ r := by
    intro i
    rw [Real.mul_rpow (singularValuesSorted_nonneg A i) (singularValuesSorted_nonneg B i)]
  simp_rw [h_rw]
  apply weak_log_maj_sum_rpow_le
  · exact fun i => singularValuesSorted_nonneg (A * B) i
  · exact fun i => mul_nonneg (singularValuesSorted_nonneg A i) (singularValuesSorted_nonneg B i)
  · exact singularValuesSorted_antitone (A * B)
  · exact antitone_mul_of_antitone_nonneg
      (singularValuesSorted_antitone A) (singularValuesSorted_antitone B)
      (singularValuesSorted_nonneg A) (singularValuesSorted_nonneg B)
  · exact horn_weak_log_majorization A B
  · exact hr

/-! ## Hölder inequality for singular values -/

/--
The finite-sum Hölder inequality applied to sequences of r-th powers of
sorted singular values.

With conjugate exponents `p' = p/r > 1` and `q' = q/r > 1` (which satisfy
`1/p' + 1/q' = 1` when `1/r = 1/p + 1/q`), this gives:
  `∑ σ↓ᵢ(A)^r · σ↓ᵢ(B)^r ≤ (∑ σ↓ᵢ(A)^p)^{r/p} · (∑ σ↓ᵢ(B)^q)^{r/q}`

Note: The sums on the RHS don't depend on the ordering, so we can replace
sorted singular values with unsorted ones.
-/
lemma holder_step_for_singularValues (A B : Matrix d d ℂ)
    {r p q : ℝ} (hr : 0 < r) (hp : 0 < p) (hq : 0 < q)
    (hpqr : 1 / r = 1 / p + 1 / q) :
    (∑ i : Fin (Fintype.card d),
      (singularValuesSorted A i ^ r * singularValuesSorted B i ^ r)) ≤
    (∑ i : Fin (Fintype.card d), singularValuesSorted A i ^ p) ^ (r / p) *
    (∑ i : Fin (Fintype.card d), singularValuesSorted B i ^ q) ^ (r / q) := by
  have h_holder : (∑ i : Fin (Fintype.card d), (singularValuesSorted A i ^ r) * (singularValuesSorted B i ^ r)) ≤ (∑ i : Fin (Fintype.card d), (singularValuesSorted A i ^ r) ^ (p / r)) ^ (r / p) * (∑ i : Fin (Fintype.card d), (singularValuesSorted B i ^ r) ^ (q / r)) ^ (r / q) := by
    have := @Real.inner_le_Lp_mul_Lq
    convert @this (Fin (Fintype.card d)) Finset.univ (fun i => singularValuesSorted A i ^ r) (fun i => singularValuesSorted B i ^ r) (p / r) (q / r) _ using 1 <;> norm_num [hr.ne', hp.ne', hq.ne', div_eq_mul_inv]
    · simp only [abs_of_nonneg (Real.rpow_nonneg (singularValuesSorted_nonneg A _) _),
              abs_of_nonneg (Real.rpow_nonneg (singularValuesSorted_nonneg B _) _)]
    · constructor <;> norm_num [hr.ne', hp.ne', hq.ne'] at hpqr ⊢ <;> ring_nf at hpqr ⊢ <;> nlinarith [inv_pos.2 hr, inv_pos.2 hp, inv_pos.2 hq, mul_inv_cancel₀ hr.ne', mul_inv_cancel₀ hp.ne', mul_inv_cancel₀ hq.ne']
  convert h_holder using 3 <;> push_cast [← Real.rpow_mul (singularValuesSorted_nonneg _ _), mul_div_cancel₀ _ hr.ne'] <;> ring_nf

end
