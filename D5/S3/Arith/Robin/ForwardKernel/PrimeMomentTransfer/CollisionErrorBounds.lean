/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CollisionErrorBounds
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CollisionErrorBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Repeated-shift quadratic defects give uniform weighted collision error bounds. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.QuadraticCollisionReduction
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.PrimePowerExceptions
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.TupleSubsetMultiplicity
import D5.S3.PrimeGaps.GreedyResidues

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

private lemma repeated_tuple_card_le (P : Finset ℕ) (k e : ℕ) :
    ((Fintype.piFinset (fun _ : Fin k => P)).filter (fun d => 2 ≤ mult d e)).card ≤
      k ^ 2 * P.card ^ (k - 2) := by
  classical
  let T := Fintype.piFinset (fun _ : Fin k => P)
  by_cases hk : k < 2
  · have hz : T.filter (fun d => 2 ≤ mult d e) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro d hd
      have hm := (Finset.mem_filter.mp hd).2
      have hle : mult d e ≤ k := by
        simpa [mult] using (Finset.card_filter_le (Finset.univ : Finset (Fin k))
          (fun i => d i = e))
      omega
    simp [hz, T] at *
  have hk2 : 2 ≤ k := by omega
  by_cases he : e ∈ P
  swap
  · have hz : T.filter (fun d => 2 ≤ mult d e) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro d hd
      obtain ⟨hd, hm⟩ := Finset.mem_filter.mp hd
      have hpos : 0 < (Finset.univ.filter (fun i => d i = e)).card := by
        change 2 ≤ (Finset.univ.filter (fun i => d i = e)).card at hm
        omega
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
      exact he ((Finset.mem_filter.mp hi).2 ▸ Fintype.mem_piFinset.mp hd i)
    change (T.filter _).card ≤ _
    rw [hz]
    exact Nat.zero_le _
  have hP : (0 : ℝ) < P.card := by exact_mod_cast Finset.card_pos.mpr ⟨e, he⟩
  have hP0 : (P.card : ℝ) ≠ 0 := ne_of_gt hP
  have hcollision (d : Fin k → ℕ) :
      (∃ i j, i ≠ j ∧ d i = e ∧ d j = e) ↔ 2 ≤ mult d e := by
    have htwo : 2 ≤ mult d e ↔
        1 < (Finset.univ.filter (fun i => d i = e)).card := by simp only [mult]; omega
    rw [htwo, Finset.one_lt_card]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, j, hij, hi, hj⟩
      exact ⟨i, hi, j, hj, hij⟩
    · rintro ⟨i, hi, j, hj, hij⟩
      exact ⟨i, j, hij, hi, hj⟩
  let S := (Finset.univ : Finset (Fin k → ↥P)).filter
    (fun r => 2 ≤ mult (fun i => (r i).val) e)
  have hcard : S.card = (T.filter (fun d => 2 ≤ mult d e)).card := by
    apply Finset.card_nbij (fun r i => (r i).val)
    · intro r hr
      exact Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun i => (r i).property),
        (Finset.mem_filter.mp hr).2⟩
    · intro r hr s hs hrs
      funext i
      exact Subtype.ext (congrFun hrs i)
    · intro d hd
      refine ⟨fun i => ⟨d i, Fintype.mem_piFinset.mp (Finset.mem_filter.mp hd).1 i⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hd).2⟩, rfl⟩
  have hmass : (∑ x : ↥P, (1 / (P.card : ℝ)) *
      if x.val = e then 1 else 0) = 1 / (P.card : ℝ) := by
    rw [Finset.sum_eq_single (⟨e, he⟩ : ↥P)]
    · simp
    · intro x hx hxe
      have hx : x.val ≠ e := fun hx => hxe (Subtype.ext hx)
      simp [hx]
    · simp
  have hbound := LongGapsBetweenPrimes.product_collision_bound
    (α := Unit) (Ω := ↥P) (fun _ => 1 / (P.card : ℝ))
    (fun _ => by positivity) (by simp [hP0]) (fun _ x => x.val = e) k
  have hnormalized : (S.card : ℝ) / (P.card : ℝ) ^ k ≤
      (k : ℝ) ^ 2 / (P.card : ℝ) ^ 2 := by
    simp only [Fintype.sum_unique, hmass] at hbound
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      exists_const, hcollision] at hbound
    rw [← Finset.mul_sum, Finset.sum_boole] at hbound
    simpa [S, one_div_pow, div_eq_mul_inv, mul_comm] using hbound
  have hpow : (P.card : ℝ) ^ k = (P.card : ℝ) ^ (k - 2) * (P.card : ℝ) ^ 2 := by
    rw [← pow_add, Nat.sub_add_cancel hk2]
  have hreal : (S.card : ℝ) ≤ (k : ℝ) ^ 2 * (P.card : ℝ) ^ (k - 2) := by
    apply (div_le_iff₀ (pow_pos hP k)).mp at hnormalized
    rw [hpow] at hnormalized
    convert hnormalized using 1 <;> field_simp <;> ring
  rw [hcard] at hreal
  exact_mod_cast hreal

private lemma sum_repeated_bound (P : Finset ℕ)
    (q : ℕ → ℝ) (hq : ∀ e, 0 ≤ q e) (k : ℕ) :
    (∑ d ∈ Fintype.piFinset (fun _ : Fin k => P), repeatedSum d q) ≤
      (if k = 1 then 0 else (k : ℝ) ^ 2) * (P.card : ℝ) ^ (k - 2) * ∑ e ∈ P, q e := by
  classical
  by_cases hk : k = 1
  · subst k
    simp only [ite_true, zero_mul]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro d hd
    exact repeatedSum_injective d (fun i j _ => Subsingleton.elim _ _) q
  simp only [ite_eq_right hk]
  let T := Fintype.piFinset (fun _ : Fin k => P)
  have hrep (d : Fin k → ℕ) (hd : d ∈ T) :
      repeatedSum d q = ∑ e ∈ P, if 2 ≤ mult d e then q e else 0 := by
    have heq : (Finset.univ.image d).filter (fun e => 2 ≤ mult d e) =
        P.filter (fun e => 2 ≤ mult d e) := by
      ext e
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨he, hm⟩
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
        exact ⟨Fintype.mem_piFinset.mp hd i, hm⟩
      · rintro ⟨he, hm⟩
        have hpos : 0 < (Finset.univ.filter (fun i => d i = e)).card := by
          simpa [mult] using (show 0 < mult d e by omega)
        obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
        exact ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩, hm⟩
    unfold repeatedSum
    rw [heq, Finset.sum_filter]
  calc
    _ = ∑ d ∈ T, ∑ e ∈ P, if 2 ≤ mult d e then q e else 0 :=
      Finset.sum_congr rfl hrep
    _ = ∑ e ∈ P, ∑ d ∈ T, if 2 ≤ mult d e then q e else 0 := Finset.sum_comm
    _ = ∑ e ∈ P, (((T.filter (fun d => 2 ≤ mult d e)).card : ℕ) : ℝ) * q e := by
      simp_rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ e ∈ P, ((k : ℝ) ^ 2 * (P.card : ℝ) ^ (k - 2)) * q e := by
      apply Finset.sum_le_sum
      intro e he
      apply mul_le_mul_of_nonneg_right _ (hq e)
      exact_mod_cast repeated_tuple_card_le P k e
    _ = _ := by rw [Finset.mul_sum]

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

private lemma interval_error_le_defects {k : ℕ}
    (N H T B : ℝ) (hT : 1 ≤ T) (a b : Fin k → ℝ) (w : ℝ → ℝ)
    (hw : ∀ t, |w t| ≤ B) (hB : 0 ≤ B)
    (P : Finset ℕ) (hpoints : ∀ i, points H (a i) (b i) ⊆ P)
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
      B * (8 * T) ^ (k - 2) * (if k = 1 then 0 else (k : ℝ) ^ 2) * (P.card : ℝ) ^ (k - 2) *
        ∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, ∑ e ∈ P, q n e := by
  classical
  let A := Fintype.piFinset (fun i => points H (a i) (b i))
  let U := Fintype.piFinset (fun _ : Fin k => P)
  have hAU : A ⊆ U := by
    intro d hd
    exact Fintype.mem_piFinset.mpr (fun i => hpoints i (Fintype.mem_piFinset.mp hd i))
  have hcount (n : ℕ) : (∑ d ∈ A, repeatedSum d (q n)) ≤
      (if k = 1 then 0 else (k : ℝ) ^ 2) * (P.card : ℝ) ^ (k - 2) * ∑ e ∈ P, q n e := by
    calc
      _ ≤ ∑ d ∈ U, repeatedSum d (q n) :=
        Finset.sum_le_sum_of_subset_of_nonneg hAU (fun d _ _ => repeatedSum_nonneg d _ (hq n))
      _ ≤ _ := sum_repeated_bound P (q n) (hq n) k
  have hinner (n : ℕ) (hn : n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊) :
      |∑ d ∈ A, ((∏ i, (ArithmeticFunction.vonMangoldt (n + d i) - 1)) -
          reducedAt (Real.log n) n d)| ≤
        (8 * T) ^ (k - 2) * ((if k = 1 then 0 else (k : ℝ) ^ 2) *
          (P.card : ℝ) ^ (k - 2) * ∑ e ∈ P, q n e) := by
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
        exact (product_reducedAt_error_bound
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
        B * ((8 * T) ^ (k - 2) * ((if k = 1 then 0 else (k : ℝ) ^ 2) *
          (P.card : ℝ) ^ (k - 2) * ∑ e ∈ P, q n e)) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [abs_mul]
      exact mul_le_mul (hw _) (hinner n hn) (abs_nonneg _) hB
    _ = _ := by simp_rw [← Finset.mul_sum]; ring

/-- Replacing repeated shifted von Mangoldt factors by their quadratic reduction at log n
has a uniform error with one fewer free shift in the prime-power exception term. -/
theorem collision_error_bound (qmax : ℕ) (M : ℝ) (hM : 1 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : ℝ, 2 ≤ N → ∀ H : ℕ, 1 ≤ H → M * (H : ℝ) ≤ N →
      ∀ B : ℝ, ∀ w : ℝ → ℝ, BVBound w B →
      ∀ k : ℕ, 1 ≤ k → k ≤ qmax → ∀ a b : Fin k → ℝ, admissible M a b →
        |discreteRaw N H a b w -
          (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, w ((n : ℝ) / N) *
            ∑ d ∈ Fintype.piFinset (fun i => points H (a i) (b i)),
              reducedAt (Real.log n) n d)| ≤
          C * B * (Real.sqrt N * (H : ℝ) ^ (k - 1) * (Real.log N) ^ (k + 1) +
            (H : ℝ) ^ k * (Real.log N) ^ (k - 1)) := by
  classical
  obtain ⟨C₀, hC₀, hcount⟩ := proper_prime_power_count_le_sqrt
  let K := (qmax : ℝ) ^ 2 * 32 ^ qmax * M ^ qmax
  refine ⟨K * (192 * C₀ + 6 * M), by dsimp [K]; positivity, ?_⟩
  intro N hN H hH hMH B w hw k hk1 hkmax a b hab
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
  have hstart := interval_error_le_defects N H (4 * Real.log N) B (by linarith)
    a b w hwB hB P hpoints q hq (by
      intro n hn
      obtain ⟨hn1, hn2⟩ := hnbounds n hn
      have hbds (e : ℕ) (he : e ∈ P) :=
        arithmetic_size_bounds N H M n e hN hH0 hM0 hn1 hn2 (hecap e he) hMH
      have hb0 := arithmetic_size_bounds N H M n 0 hN hH0 hM0 hn1 hn2
        (by simp only [Nat.cast_zero]; positivity) hMH
      exact ⟨hb0.2.1, hb0.2.2.1, fun e he => (hbds e he).2.2.2.1,
        fun e he => (hbds e he).2.2.2.2⟩)
  by_cases hk2 : 2 ≤ k
  swap
  · have hk : k = 1 := by omega
    have hz : |discreteRaw N H a b w -
        (∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊, w ((n : ℝ) / N) *
          ∑ d ∈ Fintype.piFinset (fun i => points H (a i) (b i)),
            reducedAt (Real.log n) n d)| ≤ 0 := by
      simpa only [ite_eq_left hk, mul_zero, zero_mul] using hstart
    exact hz.trans (by dsimp [K]; positivity)
  have hkn1 : k ≠ 1 := by omega
  simp only [ite_eq_right hkn1] at hstart
  have hcoef : (k : ℝ) ^ 2 * 32 ^ (k - 2) * M ^ (k - 1) ≤ K := by
    apply mul_le_mul
    · apply mul_le_mul
      · exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hkmax) 2
      · exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 32) (by omega)
      · positivity
      · positivity
    · exact pow_le_pow_right₀ hM (by omega)
    · positivity
    · positivity
  have hlog : (Real.log N) ^ k ≤ 2 * (Real.log N) ^ (k + 1) := by
    rw [pow_succ]
    nlinarith [pow_nonneg (by linarith : 0 ≤ Real.log N) k]
  let A := Real.sqrt N * (H : ℝ) ^ (k - 1) * (Real.log N) ^ (k + 1)
  let D := (H : ℝ) ^ k * (Real.log N) ^ (k - 1)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  calc
    _ ≤ B * (8 * (4 * Real.log N)) ^ (k - 2) * (k : ℝ) ^ 2 * (P.card : ℝ) ^ (k - 2) *
        ((P.card : ℝ) * (96 * C₀ * Real.sqrt N * (Real.log N) ^ 2 +
          6 * M * H * Real.log N)) :=
      hstart.trans (mul_le_mul_of_nonneg_left htotal (by positivity))
    _ = B * (k : ℝ) ^ 2 * (32 * Real.log N) ^ (k - 2) * (P.card : ℝ) ^ (k - 1) *
        (96 * C₀ * Real.sqrt N * (Real.log N) ^ 2 + 6 * M * H * Real.log N) := by
      have hp : (P.card : ℝ) ^ (k - 2) * P.card = (P.card : ℝ) ^ (k - 1) := by
        rw [← pow_succ, show k - 2 + 1 = k - 1 by omega]
      rw [show 8 * (4 * Real.log N) = 32 * Real.log N by ring]
      calc
        _ = B * (k : ℝ) ^ 2 * (32 * Real.log N) ^ (k - 2) *
            ((P.card : ℝ) ^ (k - 2) * P.card) *
              (96 * C₀ * Real.sqrt N * (Real.log N) ^ 2 + 6 * M * H * Real.log N) := by ring
        _ = _ := by rw [hp]
    _ ≤ B * (k : ℝ) ^ 2 * (32 * Real.log N) ^ (k - 2) * (M * H) ^ (k - 1) *
        (96 * C₀ * Real.sqrt N * (Real.log N) ^ 2 + 6 * M * H * Real.log N) := by
      gcongr
    _ = B * ((k : ℝ) ^ 2 * 32 ^ (k - 2) * M ^ (k - 1)) *
        (96 * C₀ * Real.sqrt N * (H : ℝ) ^ (k - 1) * (Real.log N) ^ k + 6 * M * D) := by
      dsimp [D]
      rw [mul_pow, mul_pow]
      have hklog : (Real.log N) ^ (k - 2) * (Real.log N) ^ 2 = (Real.log N) ^ k := by
        rw [← pow_add, show k - 2 + 2 = k by omega]
      have hklog1 : (Real.log N) ^ (k - 2) * Real.log N = (Real.log N) ^ (k - 1) := by
        rw [← pow_succ, show k - 2 + 1 = k - 1 by omega]
      have hkH : (H : ℝ) ^ (k - 1) * H = (H : ℝ) ^ k := by
        rw [← pow_succ, show k - 1 + 1 = k by omega]
      calc
        _ = B * ((k : ℝ) ^ 2 * 32 ^ (k - 2) * M ^ (k - 1)) *
            (96 * C₀ * Real.sqrt N * (H : ℝ) ^ (k - 1) *
              ((Real.log N) ^ (k - 2) * (Real.log N) ^ 2) +
                6 * M * ((H : ℝ) ^ (k - 1) * H) *
                  ((Real.log N) ^ (k - 2) * Real.log N)) := by ring
        _ = _ := by rw [hklog, hklog1, hkH]; ring
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
