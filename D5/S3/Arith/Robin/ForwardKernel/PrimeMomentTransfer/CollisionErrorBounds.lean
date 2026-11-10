/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CollisionErrorBounds
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CollisionErrorBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Repeated-shift quadratic defects give uniform weighted collision error bounds. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.QuadraticCollisionReduction
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.PrimePowerExceptions

/-! Sparse exceptions and logarithmic replacement in mixed interval moments. -/

open scoped BigOperators
open Finset
namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

private def repeatedSum {k : ℕ} (d : Fin k → ℕ) (q : ℕ → ℝ) : ℝ :=
  ∑ e ∈ (Finset.univ.image d).filter (fun e => 2 ≤ mult d e), q e

private lemma repeatedSum_nonneg {k : ℕ} (d : Fin k → ℕ) (q : ℕ → ℝ)
    (hq : ∀ e, 0 ≤ q e) : 0 ≤ repeatedSum d q := Finset.sum_nonneg (fun e _ => hq e)

private lemma repeatedSum_injective {k : ℕ} (d : Fin k → ℕ)
    (hd : Function.Injective d) (q : ℕ → ℝ) : repeatedSum d q = 0 := by
  apply Finset.sum_eq_zero
  intro e he
  obtain ⟨he, hm⟩ := Finset.mem_filter.mp he
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
  have hf : Finset.univ.filter (fun j => d j = d i) = {i} := by ext j; simp [hd.eq_iff]
  simp [mult, hf] at hm

private lemma repeatedSum_pattern_le {r k : ℕ} (P : Finset ℕ) (q : ℕ → ℝ)
    (hq : ∀ e, 0 ≤ q e) (p : Fin k → Fin r) (x : Fin r → P)
    (hx : Function.Injective x) :
    repeatedSum (fun i => (x (p i)).val) q ≤ ∑ i, q (x i).val := by
  have hv : Function.Injective (fun i => (x i).val) := Subtype.val_injective.comp hx
  rw [← Finset.sum_image hv.injOn]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp he).1
    exact Finset.mem_image.mpr ⟨p i, Finset.mem_univ _, rfl⟩
  · intro e _ _; exact hq e

private lemma pattern_repeated_bound {k r : ℕ} (P : Finset ℕ) (q : ℕ → ℝ)
    (hq : ∀ e, 0 ≤ q e) (p : Fin k → Fin r) :
    (∑ x : Fin r → P with Function.Injective x,
      repeatedSum (fun i => (x (p i)).val) q) ≤
      (r : ℝ) * (P.card : ℝ) ^ (r - 1) * ∑ e ∈ P, q e := by
  calc
    _ ≤ ∑ x : Fin r → P with Function.Injective x, ∑ i, q (x i).val :=
      Finset.sum_le_sum (fun x hx => repeatedSum_pattern_le P q hq p x (Finset.mem_filter.mp hx).2)
    _ ≤ ∑ x : Fin r → P, ∑ i, q (x i).val :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun x _ _ =>
        Finset.sum_nonneg (fun i _ => hq _))
    _ = _ := by
      rw [Finset.sum_comm]
      have hsum (i : Fin r) : (∑ x : Fin r → P, q (x i).val) =
          (P.card : ℝ) ^ (r - 1) * ∑ e ∈ P, q e := by
        have h := Fintype.sum_piFinset_apply (fun e : P => q e.val) Finset.univ i
        rw [Fintype.piFinset_univ] at h
        simpa only [Finset.univ_eq_attach, Fintype.card_coe, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Finset.sum_attach,
          Finset.card_attach] using h
      simp_rw [hsum]
      simp [mul_assoc]

private lemma sum_repeated_bound (P : Finset ℕ) (hP : 1 ≤ P.card)
    (q : ℕ → ℝ) (hq : ∀ e, 0 ≤ q e) (k : ℕ) (hk : k = 2 ∨ k = 3 ∨ k = 4) :
    (∑ d : Fin k → P, repeatedSum (fun i => (d i).val) q) ≤
      33 * (P.card : ℝ) ^ (k - 2) * ∑ e ∈ P, q e := by
  have hP' : (1 : ℝ) ≤ P.card := by exact_mod_cast hP
  have hQ : 0 ≤ ∑ e ∈ P, q e := Finset.sum_nonneg (fun e _ => hq e)
  rcases hk with rfl | rfl | rfl
  · have heq (d : Fin 2 → P) :
        repeatedSum (fun i => (d i).val) q =
          if d 0 = d 1 then q (d 0).val else 0 := by
      by_cases he : d 0 = d 1
      · have hd : (fun i : Fin 2 => (d i).val) = fun _ => (d 0).val := by
          funext i
          fin_cases i
          · rfl
          · exact congrArg Subtype.val he.symm
        rw [if_pos he, hd]
        unfold repeatedSum
        rw [Finset.image_const Finset.univ_nonempty]
        have hm : mult (fun _ : Fin 2 => (d 0).val) (d 0).val = 2 := by
          simp [mult]
        rw [Finset.filter_singleton, hm]
        norm_num
      · have hv : (d 0).val ≠ (d 1).val := fun h => he (Subtype.ext h)
        rw [if_neg he]
        apply repeatedSum_injective
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all
    simp_rw [heq]
    have hsum : (∑ d : Fin 2 → P, if d 0 = d 1 then q (d 0).val else 0) =
        ∑ e ∈ P, q e := by
      rw [← Equiv.sum_comp (finTwoArrowEquiv P).symm]
      simp [Fintype.sum_prod_type, Finset.sum_attach]
    rw [hsum]
    norm_num
    nlinarith
  · have hzero : patternSum3 (r := 3) ![0,1,2]
        (fun d : Fin 3 → P => repeatedSum (fun i => (d i).val) q) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      apply repeatedSum_injective
      have hi := Subtype.val_injective.comp (Finset.mem_filter.mp hx).2
      convert hi using 1
      funext i; fin_cases i <;> rfl
    rw [sum_fin_three_eq_pattern_sums, hzero]
    calc
      _ ≤ 0 + (2 * (P.card : ℝ) ^ 1 * ∑ e ∈ P, q e) +
          (2 * (P.card : ℝ) ^ 1 * ∑ e ∈ P, q e) +
          (2 * (P.card : ℝ) ^ 1 * ∑ e ∈ P, q e) +
          (1 * (P.card : ℝ) ^ 0 * ∑ e ∈ P, q e) := by
        gcongr <;> first
        | exact pattern_repeated_bound (k := 3) (r := 2) P q hq _
        | simpa [patternSum3, Function.comp_def] using
            (pattern_repeated_bound (k := 3) (r := 1) P q hq ![0,0,0])
      _ ≤ _ := by norm_num; nlinarith
  · have hzero : patternSum (r := 4) ![0,1,2,3]
        (fun d : Fin 4 → P => repeatedSum (fun i => (d i).val) q) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      apply repeatedSum_injective
      have hi := Subtype.val_injective.comp (Finset.mem_filter.mp hx).2
      convert hi using 1
      funext i; fin_cases i <;> rfl
    rw [sum_fin_four_eq_pattern_sums, hzero]
    calc
      _ ≤ 0 + (3 * (P.card : ℝ) ^ 2 * ∑ e ∈ P, q e) +
          (3 * (P.card : ℝ) ^ 2 * ∑ e ∈ P, q e) +
          (3 * (P.card : ℝ) ^ 2 * ∑ e ∈ P, q e) +
          (3 * (P.card : ℝ) ^ 2 * ∑ e ∈ P, q e) +
          (3 * (P.card : ℝ) ^ 2 * ∑ e ∈ P, q e) +
          (3 * (P.card : ℝ) ^ 2 * ∑ e ∈ P, q e) +
          (2 * (P.card : ℝ) ^ 1 * ∑ e ∈ P, q e) +
          (2 * (P.card : ℝ) ^ 1 * ∑ e ∈ P, q e) +
          (2 * (P.card : ℝ) ^ 1 * ∑ e ∈ P, q e) +
          (2 * (P.card : ℝ) ^ 1 * ∑ e ∈ P, q e) +
          (2 * (P.card : ℝ) ^ 1 * ∑ e ∈ P, q e) +
          (2 * (P.card : ℝ) ^ 1 * ∑ e ∈ P, q e) +
          (2 * (P.card : ℝ) ^ 1 * ∑ e ∈ P, q e) +
          (1 * (P.card : ℝ) ^ 0 * ∑ e ∈ P, q e) := by
        gcongr <;> first
        | exact pattern_repeated_bound (k := 4) (r := 3) P q hq _
        | exact pattern_repeated_bound (k := 4) (r := 2) P q hq _
        | simpa [patternSum, Function.comp_def] using
            (pattern_repeated_bound (k := 4) (r := 1) P q hq ![0,0,0,0])
      _ ≤ _ := by
        norm_num
        have hP2 : (P.card : ℝ) ≤ (P.card : ℝ) ^ 2 := by nlinarith
        nlinarith

private lemma arithmetic_size_bounds (N H M : ℝ) (n e : ℕ)
    (hN : 2 ≤ N) (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hn : N ≤ n) (hn2 : (n : ℝ) ≤ 2 * N) (he : (e : ℝ) ≤ M * H)
    (hMH : M * H ≤ N) :
    1 ≤ 4 * Real.log N ∧ |Real.log n - 2| ≤ 4 * Real.log N ∧
      |Real.log n - 1| ≤ 4 * Real.log N ∧
      |ArithmeticFunction.vonMangoldt (n + e) - 1| ≤ 4 * Real.log N ∧
      |(ArithmeticFunction.vonMangoldt (n + e) - 1) ^ 2 -
        (Real.log n - 2) * (ArithmeticFunction.vonMangoldt (n + e) - 1) -
          (Real.log n - 1)| ≤
        (if IsPrimePow (n + e) ∧ ¬Nat.Prime (n + e) then
          3 * (4 * Real.log N) ^ 2 else 0) + M * H / N * (3 * Real.log N) := by
  have hN0 : 0 < N := by linarith
  have hL : (1 / 2 : ℝ) ≤ Real.log N :=
    (by linarith [Real.log_two_gt_d9] : (1 / 2 : ℝ) ≤ Real.log 2).trans
      (Real.log_le_log (by norm_num) hN)
  have hn0 : 0 < (n : ℝ) := hN0.trans_le hn
  have hm0 : 0 < ((n + e : ℕ) : ℝ) := by push_cast; positivity
  have hm3 : ((n + e : ℕ) : ℝ) ≤ 3 * N := by push_cast; linarith
  have hl3 : Real.log (3 * N) ≤ 3 * Real.log N := by
    calc
      _ ≤ Real.log (N ^ 3) := Real.log_le_log (by positivity) (by
        have hc : 0 ≤ N ^ 2 - 3 := by nlinarith [sq_nonneg (N - 2)]
        nlinarith [mul_nonneg hN0.le hc])
      _ = _ := by rw [Real.log_pow]; norm_num
  have hlog : Real.log ((n + e : ℕ) : ℝ) ≤ 3 * Real.log N :=
    (Real.log_le_log hm0 hm3).trans hl3
  have hsn : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hs : Real.log n ≤ 3 * Real.log N :=
    (Real.log_le_log hn0 (by linarith : (n : ℝ) ≤ 3 * N)).trans hl3
  have hv0 := ArithmeticFunction.vonMangoldt_nonneg (n := n + e)
  have hv : ArithmeticFunction.vonMangoldt (n + e) ≤ 3 * Real.log N :=
    ArithmeticFunction.vonMangoldt_le_log.trans hlog
  have hy : |ArithmeticFunction.vonMangoldt (n + e) - 1| ≤ 4 * Real.log N :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have ha : |Real.log n - 2| ≤ 4 * Real.log N := abs_le.mpr ⟨by linarith, by linarith⟩
  have hb : |Real.log n - 1| ≤ 4 * Real.log N := abs_le.mpr ⟨by linarith, by linarith⟩
  refine ⟨by linarith, ha, hb, hy, ?_⟩
  split_ifs with hex
  · have hrough : |(ArithmeticFunction.vonMangoldt (n + e) - 1) ^ 2 -
        (Real.log n - 2) * (ArithmeticFunction.vonMangoldt (n + e) - 1) -
          (Real.log n - 1)| ≤ 3 * (4 * Real.log N) ^ 2 := by
      calc
        _ ≤ |ArithmeticFunction.vonMangoldt (n + e) - 1| ^ 2 +
            |Real.log n - 2| * |ArithmeticFunction.vonMangoldt (n + e) - 1| +
              |Real.log n - 1| := by
          simp only [← abs_pow, ← abs_mul]
          exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
        _ ≤ (4 * Real.log N) ^ 2 + (4 * Real.log N) * (4 * Real.log N) +
            4 * Real.log N := by gcongr
        _ ≤ _ := by nlinarith
    exact hrough.trans (le_add_of_nonneg_right (by positivity))
  · have hq := vonMangoldt_sub_one_quadratic (n + e) hex
    have hid : (ArithmeticFunction.vonMangoldt (n + e) - 1) ^ 2 -
        (Real.log n - 2) * (ArithmeticFunction.vonMangoldt (n + e) - 1) -
          (Real.log n - 1) =
        (Real.log ((n + e : ℕ) : ℝ) - Real.log n) * ArithmeticFunction.vonMangoldt (n + e) := by
      linear_combination hq
    rw [hid, abs_mul, abs_of_nonneg hv0, zero_add]
    exact mul_le_mul (log_shift_bound N H M n e hN0 hH hM hn he) hv hv0 (by positivity)

private lemma shifted_exception_count (N : ℝ) (hN : 2 ≤ N)
    (e : ℕ) (he : (e : ℝ) ≤ N) (C : ℝ)
    (hC : ∀ x : ℝ, 2 ≤ x →
      (((Finset.Ioc 0 ⌊x⌋₊).filter (fun m => IsPrimePow m ∧ ¬Nat.Prime m)).card : ℝ) ≤
        C * Real.sqrt x) :
    (((Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊).filter
      (fun n => IsPrimePow (n + e) ∧ ¬Nat.Prime (n + e))).card : ℝ) ≤ C * Real.sqrt (3 * N) := by
  apply le_trans _ (hC (3 * N) (by linarith))
  exact_mod_cast Finset.card_le_card_of_injOn (fun n => n + e) (by
    intro n hn
    obtain ⟨hn, hp⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ioc.mp hn
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, hp⟩
    · exact Nat.add_pos_left (lt_of_le_of_lt (Nat.zero_le _) hn1) e
    · apply (Nat.le_floor_iff (by linarith : (0 : ℝ) ≤ 3 * N)).mpr
      have hn2' : (n : ℝ) ≤ 2 * N := (Nat.le_floor_iff (by linarith)).mp hn2
      push_cast
      linarith) (by intro n hn m hm h; exact Nat.add_right_cancel h)

private lemma interval_error_le_defects {k : ℕ} (hk : k = 2 ∨ k = 3 ∨ k = 4)
    (N H T B : ℝ) (hT : 1 ≤ T) (a b : Fin k → ℝ) (w : ℝ → ℝ)
    (hw : ∀ t, |w t| ≤ B) (hB : 0 ≤ B)
    (P : Finset ℕ) (hP : 1 ≤ P.card) (hpoints : ∀ i, points H (a i) (b i) ⊆ P)
    (q : ℕ → ℕ → ℝ) (hq : ∀ n e, 0 ≤ q n e)
    (hlocal : ∀ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
      |Real.log n - 2| ≤ T ∧ |Real.log n - 1| ≤ T ∧
      (∀ e ∈ P, |ArithmeticFunction.vonMangoldt (n + e) - 1| ≤ T) ∧
      ∀ e ∈ P, |(ArithmeticFunction.vonMangoldt (n + e) - 1) ^ 2 -
        (Real.log n - 2) * (ArithmeticFunction.vonMangoldt (n + e) - 1) -
          (Real.log n - 1)| ≤ q n e) :
    |discreteRaw N H a b w -
      (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, w ((n : ℝ) / N) *
        ∑ d ∈ Fintype.piFinset (fun i => points H (a i) (b i)),
          reducedAt (Real.log n) n d)| ≤
      B * (8 * T) ^ (k - 2) * 33 * (P.card : ℝ) ^ (k - 2) *
        ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, ∑ e ∈ P, q n e := by
  classical
  let A := Fintype.piFinset (fun i => points H (a i) (b i))
  let U := Fintype.piFinset (fun _ : Fin k => P)
  have hAU : A ⊆ U := by
    intro d hd
    exact Fintype.mem_piFinset.mpr (fun i => hpoints i (Fintype.mem_piFinset.mp hd i))
  have hcount (n : ℕ) : (∑ d ∈ A, repeatedSum d (q n)) ≤
      33 * (P.card : ℝ) ^ (k - 2) * ∑ e ∈ P, q n e := by
    calc
      _ ≤ ∑ d ∈ U, repeatedSum d (q n) :=
        Finset.sum_le_sum_of_subset_of_nonneg hAU (fun d _ _ => repeatedSum_nonneg d _ (hq n))
      _ = ∑ d : Fin k → P, repeatedSum (fun i => (d i).val) (q n) := by
        symm
        apply Finset.sum_bij (fun d _ i => (d i).val)
        · intro d hd; exact Fintype.mem_piFinset.mpr (fun i => (d i).property)
        · intro d hd d' hd' hh; funext i; exact Subtype.ext (congrFun hh i)
        · intro d hd
          exact ⟨fun i => ⟨d i, Fintype.mem_piFinset.mp hd i⟩, Finset.mem_univ _, rfl⟩
        · intro d hd; rfl
      _ ≤ _ := sum_repeated_bound P hP (q n) (hq n) k hk
  have hinner (n : ℕ) (hn : n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊) :
      |∑ d ∈ A, ((∏ i, (ArithmeticFunction.vonMangoldt (n + d i) - 1)) -
          reducedAt (Real.log n) n d)| ≤
        (8 * T) ^ (k - 2) * (33 * (P.card : ℝ) ^ (k - 2) * ∑ e ∈ P, q n e) := by
    obtain ⟨ha, hb, hy, hδ⟩ := hlocal n hn
    calc
      _ ≤ ∑ d ∈ A, |(∏ i, (ArithmeticFunction.vonMangoldt (n + d i) - 1)) -
          reducedAt (Real.log n) n d| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ A, (8 * T) ^ (k - 2) * repeatedSum d (q n) := by
        apply Finset.sum_le_sum
        intro d hd
        have hD : Finset.univ.image d ⊆ P := by
          rintro e he
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
          exact hpoints i (Fintype.mem_piFinset.mp hd i)
        exact (product_reducedAt_error_bound (by rcases hk with rfl | rfl | rfl <;> omega)
          _ T hT ha hb n d (fun e he => hy e (hD he))).trans
            (mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum (fun e he => hδ e (hD (Finset.mem_filter.mp he).1)))
              (by positivity))
      _ = (8 * T) ^ (k - 2) * ∑ d ∈ A, repeatedSum d (q n) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcount n) (by positivity)
  have heq : discreteRaw N H a b w -
      (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, w ((n : ℝ) / N) *
        ∑ d ∈ A, reducedAt (Real.log n) n d) =
      ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, w ((n : ℝ) / N) *
        ∑ d ∈ A, ((∏ i, (ArithmeticFunction.vonMangoldt (n + d i) - 1)) -
          reducedAt (Real.log n) n d) := by
    unfold discreteRaw
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [← mul_sub, Finset.sum_sub_distrib]
    congr 2
    exact Finset.prod_univ_sum _ _
  rw [heq]
  calc
    _ ≤ ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
        |w ((n : ℝ) / N) * ∑ d ∈ A, ((∏ i, (ArithmeticFunction.vonMangoldt (n + d i) - 1)) -
          reducedAt (Real.log n) n d)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
        B * ((8 * T) ^ (k - 2) * (33 * (P.card : ℝ) ^ (k - 2) * ∑ e ∈ P, q n e)) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [abs_mul]
      exact mul_le_mul (hw _) (hinner n hn) (abs_nonneg _) hB
    _ = _ := by simp_rw [← Finset.mul_sum]; ring

/-- Replacing repeated shifted von Mangoldt factors by their quadratic reduction at log n
has a uniform error with one fewer free shift in the prime-power exception term. -/
theorem collision_error_bound (M : ℝ) (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : ℝ, 2 ≤ N → ∀ H : ℕ, 1 ≤ H → M * (H : ℝ) ≤ N →
      ∀ B : ℝ, ∀ w : ℝ → ℝ, BVBound w B →
      ∀ k : ℕ, (k = 2 ∨ k = 3 ∨ k = 4) → ∀ a b : Fin k → ℝ, admissible M a b →
        |discreteRaw N H a b w -
          (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, w ((n : ℝ) / N) *
            ∑ d ∈ Fintype.piFinset (fun i => points H (a i) (b i)),
              reducedAt (Real.log n) n d)| ≤
          C * B * (Real.sqrt N * (H : ℝ) ^ (k - 1) * (Real.log N) ^ (k + 1) +
            (H : ℝ) ^ k * (Real.log N) ^ (k - 1)) := by
  classical
  obtain ⟨C₀, hC₀, hcount⟩ := proper_prime_power_count_le_sqrt
  let K := 33 * 1024 * M ^ 3
  refine ⟨K * (192 * C₀ + 6 * M), by dsimp [K]; positivity, ?_⟩
  intro N hN H hH hMH B w hw k hk a b hab
  obtain ⟨_, _, hB, U, hU, hwU, hUB⟩ := hw
  have hwB (t : ℝ) : |w t| ≤ B := (hwU t).trans (by
    have := ENNReal.toReal_nonneg (a := eVariationOn w Set.univ)
    linarith)
  have hN0 : 0 < N := by linarith
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hM0 : 0 ≤ M := by linarith
  have hL : (1 / 2 : ℝ) ≤ Real.log N :=
    (by linarith [Real.log_two_gt_d9] : (1 / 2 : ℝ) ≤ Real.log 2).trans
      (Real.log_le_log (by norm_num) hN)
  let P : Finset ℕ := Finset.Ioc 0 ⌊M * (H : ℝ)⌋₊
  have hP : 1 ≤ P.card := by
    simp only [P, Nat.card_Ioc, Nat.sub_zero]
    exact (Nat.one_le_floor_iff _).mpr (by nlinarith)
  have hPc : (P.card : ℝ) ≤ M * H := by
    simp only [P, Nat.card_Ioc, Nat.sub_zero]
    exact Nat.floor_le (by positivity)
  have hpoints (i : Fin k) : points H (a i) (b i) ⊆ P := by
    intro e he
    obtain ⟨he1, he2⟩ := Finset.mem_Ioc.mp he
    exact Finset.mem_Ioc.mpr ⟨by omega, he2.trans (Nat.floor_mono (by
      exact mul_le_mul_of_nonneg_right (hab i).2.2 hH0))⟩
  have hecap (e : ℕ) (he : e ∈ P) : (e : ℝ) ≤ M * H :=
    (Nat.le_floor_iff (by positivity)).mp (Finset.mem_Ioc.mp he).2
  have hnbounds (n : ℕ) (hn : n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊) :
      N ≤ n ∧ (n : ℝ) ≤ 2 * N :=
    ⟨(Nat.lt_of_floor_lt (Finset.mem_Ioc.mp hn).1).le,
      (Nat.le_floor_iff (by positivity)).mp (Finset.mem_Ioc.mp hn).2⟩
  let q := fun n e : ℕ =>
    (if IsPrimePow (n + e) ∧ ¬Nat.Prime (n + e) then
      3 * (4 * Real.log N) ^ 2 else 0) + M * (H : ℝ) / N * (3 * Real.log N)
  have hq (n e : ℕ) : 0 ≤ q n e := by dsimp [q]; split_ifs <;> positivity
  have hcard : ((Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊).card : ℝ) ≤ 2 * N := by
    calc
      _ ≤ (⌊2 * N⌋₊ : ℝ) := by exact_mod_cast (show
        (Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊).card ≤ ⌊2 * N⌋₊ by simp [Nat.card_Ioc])
      _ ≤ _ := Nat.floor_le (by positivity)
  have hsqrt : Real.sqrt (3 * N) ≤ 2 * Real.sqrt N := by
    nlinarith [Real.sq_sqrt (by positivity : 0 ≤ N),
      Real.sq_sqrt (by positivity : 0 ≤ 3 * N), Real.sqrt_nonneg N, Real.sqrt_nonneg (3 * N)]
  have htotal : (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, ∑ e ∈ P, q n e) ≤
      (P.card : ℝ) * (96 * C₀ * Real.sqrt N * (Real.log N) ^ 2 +
        6 * M * H * Real.log N) := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ _e ∈ P, (96 * C₀ * Real.sqrt N * (Real.log N) ^ 2 +
          6 * M * H * Real.log N) := by
        apply Finset.sum_le_sum
        intro e he
        dsimp only [q]
        rw [Finset.sum_add_distrib]
        have hce := shifted_exception_count N hN e ((hecap e he).trans hMH) C₀ hcount
        have hexc : (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
            if IsPrimePow (n + e) ∧ ¬Nat.Prime (n + e) then
              3 * (4 * Real.log N) ^ 2 else 0) ≤
            (C₀ * (2 * Real.sqrt N)) * (3 * (4 * Real.log N) ^ 2) := by
          rw [← Finset.sum_filter]
          simp only [Finset.sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right
            (hce.trans (mul_le_mul_of_nonneg_left hsqrt hC₀)) (by positivity)
        have hconst : (∑ _n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊,
            M * (H : ℝ) / N * (3 * Real.log N)) ≤ 6 * M * H * Real.log N := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          calc
            _ ≤ (2 * N) * (M * (H : ℝ) / N * (3 * Real.log N)) :=
              mul_le_mul_of_nonneg_right hcard (by positivity)
            _ = _ := by field_simp; ring
        nlinarith
      _ = _ := by simp; ring
  have hstart := interval_error_le_defects hk N H (4 * Real.log N) B (by linarith)
    a b w hwB hB P hP hpoints q hq (by
      intro n hn
      obtain ⟨hn1, hn2⟩ := hnbounds n hn
      have hbds (e : ℕ) (he : e ∈ P) :=
        arithmetic_size_bounds N H M n e hN hH0 hM0 hn1 hn2 (hecap e he) hMH
      have hb0 := arithmetic_size_bounds N H M n 0 hN hH0 hM0 hn1 hn2
        (by simp only [Nat.cast_zero]; positivity) hMH
      exact ⟨hb0.2.1, hb0.2.2.1, fun e he => (hbds e he).2.2.2.1,
        fun e he => (hbds e he).2.2.2.2⟩)
  have hk2 : 2 ≤ k := by rcases hk with rfl | rfl | rfl <;> omega
  have hcoef : 33 * 32 ^ (k - 2) * M ^ (k - 1) ≤ K := by
    apply mul_le_mul
    · rcases hk with rfl | rfl | rfl <;> norm_num
    · exact pow_le_pow_right₀ hM (by rcases hk with rfl | rfl | rfl <;> omega)
    · positivity
    · norm_num
  have hlog : (Real.log N) ^ k ≤ 2 * (Real.log N) ^ (k + 1) := by
    rw [pow_succ]
    nlinarith [pow_nonneg (by linarith : 0 ≤ Real.log N) k]
  let A := Real.sqrt N * (H : ℝ) ^ (k - 1) * (Real.log N) ^ (k + 1)
  let D := (H : ℝ) ^ k * (Real.log N) ^ (k - 1)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  calc
    _ ≤ B * (8 * (4 * Real.log N)) ^ (k - 2) * 33 * (P.card : ℝ) ^ (k - 2) *
        ((P.card : ℝ) * (96 * C₀ * Real.sqrt N * (Real.log N) ^ 2 +
          6 * M * H * Real.log N)) :=
      hstart.trans (mul_le_mul_of_nonneg_left htotal (by positivity))
    _ = B * 33 * (32 * Real.log N) ^ (k - 2) * (P.card : ℝ) ^ (k - 1) *
        (96 * C₀ * Real.sqrt N * (Real.log N) ^ 2 + 6 * M * H * Real.log N) := by
      rcases hk with rfl | rfl | rfl <;> norm_num <;> ring
    _ ≤ B * 33 * (32 * Real.log N) ^ (k - 2) * (M * H) ^ (k - 1) *
        (96 * C₀ * Real.sqrt N * (Real.log N) ^ 2 + 6 * M * H * Real.log N) := by
      gcongr
    _ = B * (33 * 32 ^ (k - 2) * M ^ (k - 1)) *
        (96 * C₀ * Real.sqrt N * (H : ℝ) ^ (k - 1) * (Real.log N) ^ k + 6 * M * D) := by
      rcases hk with rfl | rfl | rfl <;> dsimp [D] <;> norm_num <;> ring
    _ ≤ B * K * (192 * C₀ * A + 6 * M * D) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hcoef hB
      · apply add_le_add _ le_rfl
        dsimp [A]
        calc
          _ ≤ 96 * C₀ * Real.sqrt N * (H : ℝ) ^ (k - 1) *
              (2 * (Real.log N) ^ (k + 1)) := mul_le_mul_of_nonneg_left hlog (by positivity)
          _ = _ := by ring
      · positivity
      · dsimp [K]; positivity
    _ ≤ (K * (192 * C₀ + 6 * M)) * B * (A + D) := by
      have hcross : 0 ≤ 192 * C₀ * D + 6 * M * A := by positivity
      have hBK : 0 ≤ B * K := by dsimp [K]; positivity
      nlinarith

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
