/- GID: D5/S3/Combinatorics/Partitions/NiuQ15Analytic
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/NiuQ15Analytic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Group.Tannery]
   utility: none
   digest: Exact rectangle tails, normalized limiting masses and the odd-entry limit. -/

module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! Tail, point and parity laws for the rectangle in Niu's Question 15. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

@[expose] public section

open Filter
open scoped BigOperators Topology

namespace NiuQ15.Analytic

def tailCoefficient (k r : ℕ) : ℕ := (r + (k - 1)).choose (k - 1)

/-- The exact survival function supplied by the finite counting identity. -/
noncomputable def finiteTail (k n r : ℕ) : ℝ :=
  if r ≤ n then (tailCoefficient k r : ℝ) *
    ∏ j ∈ Finset.range r, ((n : ℝ) - j) / ((k : ℝ) * n - j)
  else 0

noncomputable def limitTail (k r : ℕ) : ℝ :=
  (tailCoefficient k r : ℝ) * ((k : ℝ)⁻¹) ^ r

noncomputable def limitMass (k r : ℕ) : ℝ :=
  (r : ℝ) * ((r + (k - 1)).choose (k - 2) : ℝ) / (k : ℝ) ^ (r + 1)

/-- The same summable majorant works for every row count and width. -/
noncomputable def tailBound : ℕ → ℝ
  | 0 => 1
  | r + 1 => (3 / 4 : ℝ) ^ r

private theorem cast_two_le {k : ℕ} (hk : 2 ≤ k) : (2 : ℝ) ≤ (k : ℝ) := by
  exact_mod_cast hk

private theorem tailCoefficient_succ {k : ℕ} (hk : 2 ≤ k) (r : ℕ) :
    (tailCoefficient k (r + 1) : ℝ) * ((r : ℝ) + 1) =
      (tailCoefficient k r : ℝ) * ((r : ℝ) + k) := by
  have h := Nat.choose_mul_succ_eq (r + (k - 1)) (k - 1)
  have h₁ : r + (k - 1) + 1 = r + k := by omega
  have h₂ : r + (k - 1) + 1 - (k - 1) = r + 1 := by omega
  have h₃ : r + (k - 1) + 1 = (r + 1) + (k - 1) := by omega
  have he : tailCoefficient k (r + 1) * (r + 1) = tailCoefficient k r * (r + k) := by
    unfold tailCoefficient
    rw [← h₃, ← h₂, ← h, h₁]
  exact_mod_cast he

private theorem tailCoefficient_one {k : ℕ} (hk : 2 ≤ k) : tailCoefficient k 1 = k := by
  have h₁ : 1 + (k - 1) = k := by omega
  have h₂ : k - 1 ≤ k := Nat.sub_le _ _
  have h₃ : k - (k - 1) = 1 := by omega
  rw [tailCoefficient, h₁, ← Nat.choose_symm h₂, h₃, Nat.choose_one_right]

@[simp] theorem finiteTail_zero (k n : ℕ) : finiteTail k n 0 = 1 := by
  simp [finiteTail, tailCoefficient]

@[simp] theorem finiteTail_above {k n r : ℕ} (hr : n < r) : finiteTail k n r = 0 := by
  simp [finiteTail, hr.not_ge]

@[simp] theorem finiteTail_one {k n : ℕ} (hk : 2 ≤ k) (hn : 0 < n) :
    finiteTail k n 1 = 1 := by
  have hk0 : (k : ℝ) ≠ 0 := by linarith [cast_two_le hk]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [finiteTail, show 1 ≤ n from hn, tailCoefficient_one hk]
  field_simp

@[simp] theorem limitTail_zero (k : ℕ) : limitTail k 0 = 1 := by
  simp [limitTail, tailCoefficient]

@[simp] theorem limitTail_one {k : ℕ} (hk : 2 ≤ k) : limitTail k 1 = 1 := by
  have hk0 : (k : ℝ) ≠ 0 := by linarith [cast_two_le hk]
  simp [limitTail, tailCoefficient_one hk, hk0]

theorem limitTail_nonneg (k r : ℕ) : 0 ≤ limitTail k r := by
  unfold limitTail
  positivity

private theorem factor_bounds {k n j : ℕ} (hk : 2 ≤ k) (hj : j < n) :
    0 ≤ ((n : ℝ) - j) / ((k : ℝ) * n - j) ∧
      ((n : ℝ) - j) / ((k : ℝ) * n - j) ≤ (k : ℝ)⁻¹ := by
  have hk2 := cast_two_le hk
  have hjn : (j : ℝ) < n := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hn0 : (0 : ℝ) < n := hj0.trans_lt hjn
  have hk0 : (0 : ℝ) < k := by linarith
  have hknj : (0 : ℝ) < (k : ℝ) * n - j := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (k : ℝ) - 1 by linarith) hn0.le]
  refine ⟨div_nonneg (sub_nonneg.mpr hjn.le) hknj.le, ?_⟩
  rw [← one_div, div_le_div_iff₀ hknj hk0]
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ (k : ℝ) - 1 by linarith) hj0]

theorem finiteTail_bounds {k : ℕ} (hk : 2 ≤ k) (n r : ℕ) :
    0 ≤ finiteTail k n r ∧ finiteTail k n r ≤ limitTail k r := by
  by_cases hr : r ≤ n
  · rw [finiteTail, ite_eq_left hr, limitTail]
    have h j (hj : j ∈ Finset.range r) :=
      factor_bounds hk ((Finset.mem_range.mp hj).trans_le hr)
    refine ⟨mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg fun j hj => (h j hj).1), ?_⟩
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    calc
      _ ≤ ∏ _j ∈ Finset.range r, (k : ℝ)⁻¹ :=
        Finset.prod_le_prod₀ (fun j hj => (h j hj).1) (fun j hj => (h j hj).2)
      _ = _ := by rw [Finset.prod_const, Finset.card_range]
  · simp [finiteTail, hr, limitTail_nonneg]

private theorem limitTail_succ {k : ℕ} (hk : 2 ≤ k) (r : ℕ) :
    limitTail k (r + 1) = limitTail k r *
      (((r : ℝ) + k) / ((k : ℝ) * (r + 1))) := by
  have hk0 : (k : ℝ) ≠ 0 := by linarith [cast_two_le hk]
  have hr0 : (r : ℝ) + 1 ≠ 0 := by positivity
  have hc := tailCoefficient_succ hk r
  have he := (eq_div_iff hr0).2 hc
  unfold limitTail
  rw [he, pow_succ]
  field_simp

private theorem limitTail_succ_le {k r : ℕ} (hk : 2 ≤ k) (hr : 1 ≤ r) :
    limitTail k (r + 1) ≤ limitTail k r * (3 / 4 : ℝ) := by
  have hk2 := cast_two_le hk
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hk0 : (0 : ℝ) < k := by linarith
  rw [limitTail_succ hk]
  apply mul_le_mul_of_nonneg_left _ (limitTail_nonneg k r)
  apply (div_le_iff₀ (mul_pos hk0 (by positivity))).2
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ (k : ℝ) - 2 by linarith)
    (show (0 : ℝ) ≤ (r : ℝ) - 1 by linarith)]

theorem limitTail_le_bound {k : ℕ} (hk : 2 ≤ k) (r : ℕ) :
    limitTail k r ≤ tailBound r := by
  cases r with
  | zero => simp [tailBound]
  | succ r =>
    induction r with
    | zero => simp [tailBound, limitTail_one hk]
    | succ r ih =>
      calc
        limitTail k (r + 1 + 1) ≤ limitTail k (r + 1) * (3 / 4 : ℝ) :=
          limitTail_succ_le hk (by omega)
        _ ≤ tailBound (r + 1) * (3 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right ih (by norm_num)
        _ = tailBound (r + 1 + 1) := by simp [tailBound, pow_succ]

theorem finiteTail_le_bound {k : ℕ} (hk : 2 ≤ k) (n r : ℕ) :
    ‖finiteTail k n r‖ ≤ tailBound r := by
  rw [Real.norm_of_nonneg (finiteTail_bounds hk n r).1]
  exact (finiteTail_bounds hk n r).2.trans (limitTail_le_bound hk r)

theorem summable_tailBound : Summable tailBound := by
  apply (summable_nat_add_iff 1).1
  exact summable_geometric_of_norm_lt_one (by norm_num : ‖(3 / 4 : ℝ)‖ < 1)

private theorem tendsto_factor {k : ℕ} (hk : 2 ≤ k) (j : ℕ) :
    Tendsto (fun n : ℕ => ((n : ℝ) - j) / ((k : ℝ) * n - j))
      atTop (𝓝 ((k : ℝ)⁻¹)) := by
  have hk0 : (k : ℝ) ≠ 0 := by linarith [cast_two_le hk]
  have hj := tendsto_const_div_atTop_nhds_zero_nat (j : ℝ)
  have ht := (tendsto_const_nhds (x := (1 : ℝ))).sub hj
  have hb := (tendsto_const_nhds (x := (k : ℝ))).sub hj
  have h := ht.div hb (by simpa using hk0)
  simp only [sub_zero, one_div] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  change (1 - (j : ℝ) / n) / ((k : ℝ) - (j : ℝ) / n) = _
  calc
    _ = (((n : ℝ) - j) / n) / ((((k : ℝ) * n) - j) / n) := by
      rw [sub_div (n : ℝ), sub_div ((k : ℝ) * n), div_self hn0, mul_div_cancel_right₀ _ hn0]
    _ = _ := div_div_div_cancel_right₀ hn0 _ _

theorem tendsto_finiteTail {k : ℕ} (hk : 2 ≤ k) (r : ℕ) :
    Tendsto (fun n => finiteTail k n r) atTop (𝓝 (limitTail k r)) := by
  have hp := tendsto_finsetProd (Finset.range r) (fun j _ => tendsto_factor hk j)
  have h := (tendsto_const_nhds (x := (tailCoefficient k r : ℝ))).mul hp
  simp only [Finset.prod_const, Finset.card_range] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop r] with n hn
  simp [finiteTail, hn]

/-- The product formula agrees with the descending-factorial ratio from counting. -/
theorem finiteTail_eq_descFactorial {k n r : ℕ} (hk : 2 ≤ k) (hr : r ≤ n) :
    finiteTail k n r = (tailCoefficient k r : ℝ) *
      ((n.descFactorial r : ℝ) / ((k * n).descFactorial r : ℝ)) := by
  rw [finiteTail, ite_eq_left hr, Finset.prod_div_distrib]
  congr 1
  have hnkn : n ≤ k * n := by
    calc n = 1 * n := (one_mul n).symm
         _ ≤ k * n := Nat.mul_le_mul_right n (by omega)
  rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range,
    Nat.cast_prod, Nat.cast_prod]
  congr 1
  · exact Finset.prod_congr rfl fun j hj =>
      (Nat.cast_sub ((Finset.mem_range.mp hj).le.trans hr)).symm
  · refine Finset.prod_congr rfl fun j hj => ?_
    rw [Nat.cast_sub ((Finset.mem_range.mp hj).le.trans (hr.trans hnkn)), Nat.cast_mul]


/-- The tail difference holds at the endpoint as well, where the next tail vanishes. -/
private theorem finiteTail_succ {k n r : ℕ} (hk : 2 ≤ k) (hr : r ≤ n) :
    finiteTail k n (r + 1) = finiteTail k n r *
      ((((r : ℝ) + k) / ((r : ℝ) + 1)) * (((n : ℝ) - r) / ((k : ℝ) * n - r))) := by
  by_cases h : r + 1 ≤ n
  · rw [finiteTail, ite_eq_left h, finiteTail, ite_eq_left hr, Finset.prod_range_succ]
    have hc := (eq_div_iff (show (r : ℝ) + 1 ≠ 0 by positivity)).2
      (tailCoefficient_succ hk r)
    rw [hc]
    ring
  · have he : r = n := by omega
    subst r
    simp [finiteTail, h]

theorem finiteTail_sub_succ {k n r : ℕ} (hk : 2 ≤ k) (hn : 0 < n) (hr : r ≤ n) :
    finiteTail k n r - finiteTail k n (r + 1) =
      finiteTail k n r * (((k : ℝ) - 1) * r * ((n : ℝ) + 1) /
        (((r : ℝ) + 1) * ((k : ℝ) * n - r))) := by
  have hk2 := cast_two_le hk
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hrn : (r : ℝ) ≤ n := by exact_mod_cast hr
  have hden : (0 : ℝ) < (k : ℝ) * n - r := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (k : ℝ) - 2 by linarith) hn0.le]
  rw [finiteTail_succ hk hr]
  field_simp [hden.ne', show (r : ℝ) + 1 ≠ 0 by positivity]
  ring

theorem limitTail_sub_succ {k : ℕ} (hk : 2 ≤ k) (r : ℕ) :
    limitTail k r - limitTail k (r + 1) = limitMass k r := by
  have hk0 : (k : ℝ) ≠ 0 := by linarith [cast_two_le hk]
  have hr0 : (r : ℝ) + 1 ≠ 0 := by positivity
  have hc : ((r + (k - 1)).choose (k - 2) : ℝ) * ((r : ℝ) + 1) =
      (tailCoefficient k r : ℝ) * ((k : ℝ) - 1) := by
    have h := Nat.choose_succ_right_eq (r + (k - 1)) (k - 2)
    have h₁ : k - 2 + 1 = k - 1 := by omega
    have h₂ : r + (k - 1) - (k - 2) = r + 1 := by omega
    rw [h₁, h₂] at h
    have hcast : (tailCoefficient k r : ℝ) * ((k - 1 : ℕ) : ℝ) =
        ((r + (k - 1)).choose (k - 2) : ℝ) * ((r : ℝ) + 1) := by
      exact_mod_cast h
    rw [Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_one] at hcast
    exact hcast.symm
  have he := (eq_div_iff hr0).2 hc
  rw [limitTail_succ hk, limitMass, he, limitTail, inv_pow, pow_succ]
  rw [inv_eq_one_div]
  field_simp
  ring

theorem limitMass_nonneg (k r : ℕ) : 0 ≤ limitMass k r := by
  unfold limitMass
  positivity

@[simp] theorem limitMass_zero (k : ℕ) : limitMass k 0 = 0 := by
  simp [limitMass]

private theorem summable_limitTail {k : ℕ} (hk : 2 ≤ k) : Summable (limitTail k) := by
  apply summable_tailBound.of_norm_bounded
  intro r
  rw [Real.norm_of_nonneg (limitTail_nonneg k r)]
  exact limitTail_le_bound hk r

theorem hasSum_limitMass {k : ℕ} (hk : 2 ≤ k) : HasSum (limitMass k) 1 := by
  have hsum := summable_limitTail hk
  have hzero := hsum.tendsto_atTop_zero
  have hmass : Summable (limitMass k) := by
    simpa only [limitTail_sub_succ hk] using hsum.sub ((summable_nat_add_iff 1).2 hsum)
  have ht : Tendsto (fun n => ∑ r ∈ Finset.range n, limitMass k r) atTop (𝓝 (1 : ℝ)) := by
    simpa only [← limitTail_sub_succ hk, Finset.sum_range_sub', limitTail_zero, sub_zero]
      using (tendsto_const_nhds (x := (1 : ℝ))).sub hzero
  exact (hasSum_iff_tendsto_nat_of_summable_norm
    (by simpa only [Real.norm_of_nonneg (limitMass_nonneg k _)] using hmass)).2 ht

section PointPartition

variable {k : ℕ} (hk : 2 ≤ k) {point : ℕ → ℕ → ℝ}
  (hpart : ∀ n, 0 < n → ∀ r, finiteTail k n r = point n r + finiteTail k n (r + 1))

include hpart

theorem point_eq_tail_sub {n : ℕ} (hn : 0 < n) (r : ℕ) :
    point n r = finiteTail k n r - finiteTail k n (r + 1) :=
  eq_sub_of_add_eq (hpart n hn r).symm

include hk in
theorem point_eq {n r : ℕ} (hn : 0 < n) (hr : r ≤ n) :
    point n r = finiteTail k n r * (((k : ℝ) - 1) * r * ((n : ℝ) + 1) /
      (((r : ℝ) + 1) * ((k : ℝ) * n - r))) := by
  rw [point_eq_tail_sub hpart hn, finiteTail_sub_succ hk hn hr]

include hk in
theorem point_zero {n : ℕ} (hn : 0 < n) : point n 0 = 0 := by
  rw [point_eq_tail_sub hpart hn, finiteTail_zero, finiteTail_one hk hn, sub_self]

theorem point_above {n r : ℕ} (hn : 0 < n) (hr : n < r) : point n r = 0 := by
  rw [point_eq_tail_sub hpart hn, finiteTail_above hr, finiteTail_above (by omega), sub_self]

theorem sum_point {n : ℕ} (hn : 0 < n) :
    ∑ r ∈ Finset.range (n + 1), point n r = 1 := by
  simp only [point_eq_tail_sub hpart hn, Finset.sum_range_sub', finiteTail_zero,
    finiteTail_above (Nat.lt_succ_self n), sub_zero]

include hk in
theorem tendsto_point (r : ℕ) :
    Tendsto (fun n => point n r) atTop (𝓝 (limitMass k r)) := by
  rw [← limitTail_sub_succ hk]
  refine ((tendsto_finiteTail hk r).sub (tendsto_finiteTail hk (r + 1))).congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact (point_eq_tail_sub hpart hn r).symm

end PointPartition


private theorem sum_even_differences (s : ℕ → ℝ) (m : ℕ) :
    (∑ r ∈ Finset.range (2 * m), if Even r then s r - s (r + 1) else 0) =
      ∑ r ∈ Finset.range (2 * m), (-1 : ℝ) ^ r * s r := by
  induction m with
  | zero => simp
  | succ m ih =>
    have he : Even (2 * m) := ⟨m, by omega⟩
    have ho : Odd (2 * m + 1) := ⟨m, rfl⟩
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega]
    simp only [Finset.sum_range_succ, ite_eq_left he,
      ite_eq_right (Nat.not_even_iff_odd.mpr ho), he.neg_one_pow, ho.neg_one_pow,
      one_mul, neg_one_mul, add_zero, ih]
    ring

private theorem norm_alternating (s : ℕ → ℝ) (r : ℕ) :
    ‖(-1 : ℝ) ^ r * s r‖ = ‖s r‖ := by
  simp [norm_mul, norm_pow]

private theorem hasSum_alternating_limitTail {k : ℕ} (hk : 2 ≤ k) :
    HasSum (fun r => (-1 : ℝ) ^ r * limitTail k r)
      (((k : ℝ) / ((k : ℝ) + 1)) ^ k) := by
  have hk2 := cast_two_le hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hz : ‖-((k : ℝ)⁻¹)‖ < 1 := by
    rw [norm_neg, Real.norm_of_nonneg (by positivity), ← one_div]
    exact (div_lt_iff₀ hk0).2 (by linarith)
  have hs := hasSum_choose_mul_geometric_of_norm_lt_one (k - 1) hz
  have hk1 : k - 1 + 1 = k := by omega
  have eqterm (r : ℕ) :
      ((r + (k - 1)).choose (k - 1) : ℝ) * (-((k : ℝ)⁻¹)) ^ r =
        (-1 : ℝ) ^ r * limitTail k r := by
    rw [limitTail, tailCoefficient, ← neg_one_mul, mul_pow]
    ring
  have eqsum : 1 / (1 - -((k : ℝ)⁻¹)) ^ k = ((k : ℝ) / ((k : ℝ) + 1)) ^ k := by
    rw [← one_div_pow]
    congr 1
    field_simp
    ring
  simpa only [eqterm, hk1, eqsum] using hs

theorem hasSum_even_limitMass {k : ℕ} (hk : 2 ≤ k) :
    HasSum (fun r => if Even r then limitMass k r else 0)
      (((k : ℝ) / ((k : ℝ) + 1)) ^ k) := by
  have hmajor (r : ℕ) : ‖if Even r then limitMass k r else 0‖ ≤ tailBound r := by
    by_cases h : Even r
    · rw [ite_eq_left h, Real.norm_of_nonneg (limitMass_nonneg k r), ← limitTail_sub_succ hk]
      exact (sub_le_self _ (limitTail_nonneg k (r + 1))).trans (limitTail_le_bound hk r)
    · rw [ite_eq_right h, norm_zero]
      exact (limitTail_nonneg k r).trans (limitTail_le_bound hk r)
  have hs := summable_tailBound.of_norm_bounded hmajor
  have hcofinal : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_mono (fun m => show m ≤ 2 * m by omega) tendsto_id
  have h₁ := hs.tendsto_sum_tsum_nat.comp hcofinal
  have h₂ := (hasSum_alternating_limitTail hk).tendsto_sum_nat.comp hcofinal
  have heq : (∑' r, if Even r then limitMass k r else 0) =
      ((k : ℝ) / ((k : ℝ) + 1)) ^ k := by
    apply tendsto_nhds_unique h₁
    refine h₂.congr (fun m => ?_)
    simpa only [Function.comp_apply, ← limitTail_sub_succ hk] using
      (sum_even_differences (limitTail k) m).symm
  exact heq ▸ hs.hasSum

theorem sum_even_point_eq_alternating {k : ℕ} {point : ℕ → ℕ → ℝ}
    (hpart : ∀ n, 0 < n → ∀ r, finiteTail k n r = point n r + finiteTail k n (r + 1))
    {n : ℕ} (hn : 0 < n) :
    (∑ r ∈ Finset.range (n + 1), if Even r then point n r else 0) =
      ∑' r, (-1 : ℝ) ^ r * finiteTail k n r := by
  have hc (r : ℕ) (hr : r ∉ Finset.range (n + 1)) : n < r := by
    simp only [Finset.mem_range, not_lt] at hr
    omega
  have hz (r : ℕ) (hr : r ∉ Finset.range (n + 1)) :
      (if Even r then point n r else 0) = 0 := by
    simp [point_above hpart hn (hc r hr)]
  have hcut : n + 1 ≤ 2 * (n + 1) := by omega
  calc
    _ = ∑ r ∈ Finset.range (2 * (n + 1)), if Even r then point n r else 0 :=
      Finset.sum_subset (Finset.range_mono hcut) (fun r _ hr => hz r hr)
    _ = ∑ r ∈ Finset.range (2 * (n + 1)), (-1 : ℝ) ^ r * finiteTail k n r := by
      simpa only [point_eq_tail_sub hpart hn] using sum_even_differences (finiteTail k n) (n + 1)
    _ = _ := (tsum_eq_sum fun r hr => by
      have hnr : n < r := by simp only [Finset.mem_range, not_lt] at hr; omega
      rw [finiteTail_above hnr, mul_zero]).symm

/-- The alternating series converges by Tannery's theorem with a majorant
independent of both the row count and width. -/
theorem tendsto_alternating_finiteTail {k : ℕ} (hk : 2 ≤ k) :
    Tendsto (fun n => ∑' r, (-1 : ℝ) ^ r * finiteTail k n r) atTop
      (𝓝 (((k : ℝ) / ((k : ℝ) + 1)) ^ k)) := by
  rw [← (hasSum_alternating_limitTail hk).tsum_eq]
  exact tendsto_tsum_of_dominated_convergence summable_tailBound
    (fun r => (tendsto_finiteTail hk r).const_mul ((-1 : ℝ) ^ r))
    (Eventually.of_forall fun n r => (norm_alternating (finiteTail k n) r).trans_le
      (finiteTail_le_bound hk n r))

theorem tendsto_sum_even_point {k : ℕ} (hk : 2 ≤ k) {point : ℕ → ℕ → ℝ}
    (hpart : ∀ n, 0 < n → ∀ r, finiteTail k n r = point n r + finiteTail k n (r + 1)) :
    Tendsto (fun n => ∑ r ∈ Finset.range (n + 1), if Even r then point n r else 0)
      atTop (𝓝 (((k : ℝ) / ((k : ℝ) + 1)) ^ k)) := by
  refine (tendsto_alternating_finiteTail hk).congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact (sum_even_point_eq_alternating hpart hn).symm

end NiuQ15.Analytic
