/- GID: D5/S3/Arith/Primes/GoldenCubicPadicConjugacy
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenCubicPadicConjugacy
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: The full small p-adic ball is isometrically conjugate from the cubic block update to multiplication by nine. -/

import D5.S3.Arith.Primes.GoldenCubicFormalConjugacy
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Arith.Primes.GoldenCubicPadicConjugacy

open GoldenCubicFormalConjugacy

theorem twice_factorial_depth_le_half {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) (n : ℕ) :
    2 * padicValNat p (2*n).factorial ≤ n := by
  have hy : (p-1) * (2*n).factorial.factorization p ≤ 2*n := by
    rw [Nat.sub_one_mul_factorization_factorial hp.out]
    exact Nat.sub_le _ _
  have h4 := Nat.mul_le_mul_right ((2*n).factorial.factorization p) (show 4 ≤ p - 1 by omega)
  have hs := h4.trans hy
  have hfac := Nat.factorization_def (2*n).factorial hp.out
  rw [hfac] at hs
  omega

/-- Every nonlinear coefficient term gains at least one valuation digit after
dividing a difference by its input difference on pZ_p. -/
theorem twice_factorial_depth_le_minus_two {p : ℕ} [hp : Fact p.Prime]
    (hp5 : 5 ≤ p) (n : ℕ) (hn : 2 ≤ n) :
    padicValNat p (2*n).factorial ≤ n-2 := by
  rcases eq_or_lt_of_le hn with rfl | hn
  · have hfreq : (4:ℕ).factorial.factorization p = 0 :=
      Nat.factorization_factorial_eq_zero_of_lt (by omega)
    have hfac := Nat.factorization_def (4:ℕ).factorial hp.out
    simpa only [show 2*2 = (4:ℕ) by decide, hfac, Nat.sub_self, nonpos_iff_eq_zero] using hfreq
  · have hb := twice_factorial_depth_le_half hp5 n
    omega

/-- On rational points of the unit p-ball the explicit term valuations grow
at least linearly, with rate n/2. This is an estimate, not a p-adic
evaluation/continuity theorem. -/
theorem coordinate_term_depth {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) {z : ℚ}
    (hz : z ≠ 0) (hzv : 1 ≤ padicValRat p z) (n : ℕ) :
    (n : ℤ) ≤ 2 * padicValRat p (2*z^n/((2*n).factorial : ℚ)) := by
  have hd : ¬ p ∣ 2 := fun H => by have := Nat.le_of_dvd (by decide : 0 < 2) H; omega
  have htwo : padicValRat p (2 : ℚ) = 0 := by
    change padicValRat p ((2:ℕ):ℚ) = 0
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hd, Nat.cast_zero]
  have hfac0 : ((2*n).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2*n)
  rw [padicValRat.div (mul_ne_zero (by decide) (pow_ne_zero _ hz)) hfac0,
    padicValRat.mul (by decide : (2:ℚ) ≠ 0) (pow_ne_zero _ hz),
    htwo, zero_add, padicValRat.pow, padicValRat.of_nat]
  have H : 2 * ((padicValNat p (2*n).factorial : ℕ) : ℤ) ≤ (n : ℤ) := by
    exact_mod_cast twice_factorial_depth_le_half hp5 n
  have hm : (n:ℤ) ≤ (n:ℤ) * padicValRat p z := by
    simpa using mul_le_mul_of_nonneg_left hzv (show (0:ℤ) ≤ n by exact_mod_cast Nat.zero_le n)
  omega

section Padic
open Filter
open scoped Topology NNReal

variable {p : ℕ} [hp : Fact p.Prime]

/-- Actual terms of the convergent coordinate on the small p-adic ball. -/
noncomputable def coordinateTerm (z : ℚ_[p]) (n : ℕ) : ℚ_[p] :=
  if n = 0 then 0 else (2 : ℚ_[p])*z^n/((2*n).factorial : ℚ_[p])

private theorem coordinateTerm_ne_zero {x : ℚ_[p]} (hx : x ≠ 0) {n : ℕ}
    (hn : n ≠ 0) : coordinateTerm x n ≠ 0 := by
  simp only [coordinateTerm, ite_eq_right hn]
  exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hx))
    (by exact_mod_cast Nat.factorial_ne_zero (2*n))

private theorem coordinateTerm_valuation {x : ℚ_[p]} (hx : x ≠ 0) {n : ℕ}
    (hn : n ≠ 0) (hp5 : 5 ≤ p) :
    (coordinateTerm x n).valuation = (n : ℤ) * x.valuation - padicValNat p (2*n).factorial := by
  have hno : ¬ p ∣ 2 := fun H => by have := Nat.le_of_dvd (by decide : 0 < 2) H; omega
  have ht : Padic.valuation (2 : ℚ_[p]) = 0 := by
    rw [Padic.valuation_ofNat, padicValNat.eq_zero_of_not_dvd hno, Nat.cast_zero]
  have hfac : ((2*n).factorial : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2*n)
  rw [coordinateTerm, ite_eq_right hn, div_eq_mul_inv,
    Padic.valuation_mul (mul_ne_zero (by norm_num) (pow_ne_zero _ hx)) (inv_ne_zero hfac),
    Padic.valuation_mul (by norm_num) (pow_ne_zero _ hx), ht, zero_add,
    Padic.valuation_pow, Padic.valuation_inv, Padic.valuation_natCast, sub_eq_add_neg]

/-- Geometric majorant for the actual coefficient evaluation on pZ_p. -/
theorem coordinateTerm_norm_le (hp5 : 5 ≤ p) {z : ℚ_[p]}
    (hz : z = 0 ∨ 1 ≤ z.valuation) (n : ℕ) :
    ‖coordinateTerm z n‖ ≤ ((p:ℝ)⁻¹)^(n / 2) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [coordinateTerm]
  rcases hz with rfl | hzv
  · simp only [coordinateTerm, ite_eq_right hn, zero_pow hn, mul_zero, zero_div, norm_zero]
    positivity
  have hz0 : z ≠ 0 := by intro h; simp [h] at hzv
  have hpR : 1 < (p:ℝ) := by exact_mod_cast hp.out.one_lt
  rw [Padic.norm_eq_zpow_neg_valuation (coordinateTerm_ne_zero hz0 hn), inv_pow,
    ← zpow_natCast, ← zpow_neg, zpow_le_zpow_iff_right₀ hpR, neg_le_neg_iff,
    coordinateTerm_valuation hz0 hn hp5]
  have hfac : 2 * (padicValNat p (2*n).factorial : ℤ) ≤ (n : ℤ) := by
    exact_mod_cast twice_factorial_depth_le_half hp5 n
  have hm : (n:ℤ) ≤ (n:ℤ) * z.valuation := by
    simpa using mul_le_mul_of_nonneg_left hzv (show (0:ℤ) ≤ n by exact_mod_cast Nat.zero_le n)
  have hdiv : 2*((n/2 : ℕ) : ℤ) ≤ (n : ℤ) := by
    exact_mod_cast (show 2 * (n/2) ≤ n by omega)
  omega

/-- The root-free coordinate itself exists by actual p-adic summability on the
entire small ball. Algebraic evaluation and the inverse are separate claims. -/
theorem coordinate_summable (hp5 : 5 ≤ p) {z : ℚ_[p]}
    (hz : z = 0 ∨ 1 ≤ z.valuation) : Summable (coordinateTerm z) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hpR : 1 < (p:ℝ) := by exact_mod_cast hp.out.one_lt
  have hl : Tendsto (fun n : ℕ => ((p:ℝ)⁻¹)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hpR)
  apply squeeze_zero (fun n => norm_nonneg _) (coordinateTerm_norm_le hp5 hz)
  exact hl.comp (Nat.tendsto_div_const_atTop (by decide : (2:ℕ) ≠ 0))

end Padic


section PadicIsometry
open Filter
open scoped Topology NNReal

variable {p : ℕ} [hp : Fact p.Prime]

private theorem padic_radius_lt_one : (p:ℝ)⁻¹ < 1 := by
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)

private theorem padic_radius_pos : 0 < (p:ℝ)⁻¹ :=
  inv_pos.mpr (show 0 < (p:ℝ) by exact_mod_cast hp.out.pos)

private theorem mem_small_ball_iff (x : ℚ_[p]) :
    ‖x‖ ≤ (p:ℝ)⁻¹ ↔ x = 0 ∨ 1 ≤ x.valuation := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [padic_radius_pos.le]
  rw [or_iff_right hx, Padic.norm_eq_zpow_neg_valuation hx,
    ← zpow_neg_one, zpow_le_zpow_iff_right₀ (show 1 < (p:ℝ) by exact_mod_cast hp.out.one_lt),
    neg_le]
  simp

private theorem norm_coefficient (hp5 : 5 ≤ p) (n : ℕ) :
    ‖(2 : ℚ_[p])/((2*n).factorial : ℚ_[p])‖ =
      (p:ℝ)^(padicValNat p (2*n).factorial : ℤ) := by
  have hno : ¬ p ∣ 2 := fun H => by have := Nat.le_of_dvd (by decide : 0 < 2) H; omega
  have ht : Padic.valuation (2 : ℚ_[p]) = 0 := by
    rw [Padic.valuation_ofNat, padicValNat.eq_zero_of_not_dvd hno, Nat.cast_zero]
  have hd0 : ((2*n).factorial : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2*n)
  rw [norm_div, Padic.norm_eq_zpow_neg_valuation (by norm_num : (2:ℚ_[p]) ≠ 0), ht,
    neg_zero, zpow_zero, Padic.norm_eq_zpow_neg_valuation hd0, Padic.valuation_natCast,
    one_div, zpow_neg, inv_inv]

private theorem coefficient_times_powers_le (hp5 : 5 ≤ p) (n : ℕ) (hn : 2 ≤ n) :
    (p:ℝ)^(padicValNat p (2*n).factorial : ℤ) * ((p:ℝ)⁻¹)^(n-1) ≤ (p:ℝ)⁻¹ := by
  have hpR : 1 < (p:ℝ) := by exact_mod_cast hp.out.one_lt
  have hf : (padicValNat p (2*n).factorial : ℤ) ≤ ((n-2:ℕ) : ℤ) := by
    exact_mod_cast twice_factorial_depth_le_minus_two hp5 n hn
  rw [inv_pow, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ (by positivity : (p:ℝ) ≠ 0),
    ← zpow_neg_one, zpow_le_zpow_iff_right₀ hpR]
  omega

private theorem coordinateTerm_diff_le (hp5 : 5 ≤ p) {x y : ℚ_[p]}
    (hx : ‖x‖ ≤ (p:ℝ)⁻¹) (hy : ‖y‖ ≤ (p:ℝ)⁻¹) (n : ℕ) (hn : 2 ≤ n) :
    ‖coordinateTerm x n-coordinateTerm y n‖ ≤ (p:ℝ)⁻¹ * ‖x-y‖ := by
  let w := ∑ i ∈ Finset.range n, x^i * y^(n-1-i)
  have hw : ‖w‖ ≤ ((p:ℝ)⁻¹)^(n-1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    rw [norm_mul, norm_pow, norm_pow]
    refine (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hx _)
      (pow_le_pow_left₀ (norm_nonneg _) hy _) (by positivity) (by positivity)).trans ?_
    rw [← pow_add, show i + (n-1-i) = n-1 by omega]
  have hd : coordinateTerm x n-coordinateTerm y n =
      ((2:ℚ_[p])/((2*n).factorial : ℚ_[p])) * (w * (x-y)) := by
    simp only [coordinateTerm, ite_eq_right (show n ≠ 0 by omega)]
    rw [show w * (x-y) = x^n-y^n from geom_sum₂_mul x y n]
    ring
  rw [hd, norm_mul, norm_mul, norm_coefficient hp5, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  exact (mul_le_mul_of_nonneg_left hw (by positivity)).trans
    (coefficient_times_powers_le hp5 n hn)

private noncomputable def coordinateRemainder (x : ℚ_[p]) : ℚ_[p] :=
  ∑' n : ℕ, coordinateTerm x (n+2)

private theorem coordinateRemainder_zero : coordinateRemainder (0 : ℚ_[p]) = 0 := by
  simp [coordinateRemainder, coordinateTerm]

private theorem coordinateRemainder_diff_le (hp5 : 5 ≤ p) {x y : ℚ_[p]}
    (hx : ‖x‖ ≤ (p:ℝ)⁻¹) (hy : ‖y‖ ≤ (p:ℝ)⁻¹) :
    ‖coordinateRemainder x-coordinateRemainder y‖ ≤ (p:ℝ)⁻¹ * ‖x-y‖ := by
  have hsum (z : ℚ_[p]) (hz : ‖z‖ ≤ (p:ℝ)⁻¹) :
      Summable (fun n => coordinateTerm z (n+2)) :=
    (summable_nat_add_iff 2).mpr (coordinate_summable hp5 ((mem_small_ball_iff z).mp hz))
  rw [coordinateRemainder, coordinateRemainder, ← (hsum x hx).tsum_sub (hsum y hy)]
  exact IsUltrametricDist.norm_tsum_le_of_forall_le
    (fun n => coordinateTerm_diff_le hp5 hx hy (n+2) (by omega))

/-- The literal evaluated coordinate is identity plus a strict contraction. -/
noncomputable def evaluateCoordinate (x : ℚ_[p]) : ℚ_[p] := x+coordinateRemainder x

theorem evaluateCoordinate_eq_tsum (hp5 : 5 ≤ p) {x : ℚ_[p]} (hx : ‖x‖ ≤ (p:ℝ)⁻¹) :
    evaluateCoordinate x = ∑' n, coordinateTerm x n := by
  have h := (coordinate_summable hp5 ((mem_small_ball_iff x).mp hx)).sum_add_tsum_nat_add 2
  simpa [evaluateCoordinate, coordinateRemainder, coordinateTerm, Finset.sum_range_succ,
    Nat.factorial] using h

theorem evaluateCoordinate_isometry (hp5 : 5 ≤ p) {x y : ℚ_[p]}
    (hx : ‖x‖ ≤ (p:ℝ)⁻¹) (hy : ‖y‖ ≤ (p:ℝ)⁻¹) :
    ‖evaluateCoordinate x-evaluateCoordinate y‖ = ‖x-y‖ := by
  by_cases he : x = y
  · simp [he]
  have hlt : ‖coordinateRemainder x-coordinateRemainder y‖ < ‖x-y‖ := by
    refine (coordinateRemainder_diff_le hp5 hx hy).trans_lt ?_
    exact mul_lt_of_lt_one_left (norm_pos_iff.mpr (sub_ne_zero.mpr he)) (padic_radius_lt_one (p := p))
  rw [show evaluateCoordinate x-evaluateCoordinate y =
      (x-y)+(coordinateRemainder x-coordinateRemainder y) by unfold evaluateCoordinate; ring,
    IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hlt), max_eq_left hlt.le]

theorem evaluateCoordinate_mapsTo (hp5 : 5 ≤ p) :
    Set.MapsTo (evaluateCoordinate : ℚ_[p] → ℚ_[p])
      (Metric.closedBall 0 ((p:ℝ)⁻¹)) (Metric.closedBall 0 ((p:ℝ)⁻¹)) := by
  intro x hx
  rw [mem_closedBall_zero_iff] at hx ⊢
  have hr := evaluateCoordinate_isometry hp5 hx (show ‖(0:ℚ_[p])‖ ≤ (p:ℝ)⁻¹ by
    simp [padic_radius_pos.le])
  simp only [evaluateCoordinate, coordinateRemainder_zero, add_zero, sub_zero] at hr
  have he : ‖evaluateCoordinate x‖ = ‖x‖ := by simpa only [evaluateCoordinate] using hr
  exact he.le.trans hx

theorem evaluateCoordinate_surjectiveOn (hp5 : 5 ≤ p) :
    Set.SurjOn (evaluateCoordinate : ℚ_[p] → ℚ_[p])
      (Metric.closedBall 0 ((p:ℝ)⁻¹)) (Metric.closedBall 0 ((p:ℝ)⁻¹)) := by
  intro y hy
  let f (x : ℚ_[p]) := y-coordinateRemainder x
  let s := Metric.closedBall (0:ℚ_[p]) ((p:ℝ)⁻¹)
  let K : ℝ≥0 := ⟨(p:ℝ)⁻¹, padic_radius_pos.le⟩
  have hsc : IsComplete s := Metric.isClosed_closedBall.isComplete
  have hzero : (0:ℚ_[p]) ∈ s := Metric.mem_closedBall_self padic_radius_pos.le
  have hmaps : Set.MapsTo f s s := by
    intro x hx
    simp only [s, mem_closedBall_zero_iff] at hx ⊢
    rw [mem_closedBall_zero_iff] at hy
    dsimp [f]
    have hr := coordinateRemainder_diff_le hp5 hx
      (show ‖(0:ℚ_[p])‖ ≤ (p:ℝ)⁻¹ by simp [padic_radius_pos.le])
    rw [coordinateRemainder_zero, sub_zero, sub_zero] at hr
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy ?_)
    rw [norm_neg]
    exact hr.trans ((mul_le_of_le_one_left (norm_nonneg _) (padic_radius_lt_one (p := p)).le).trans hx)
  have hcontract : ContractingWith K (hmaps.restrict f s s) := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul ?_⟩
    · exact_mod_cast (padic_radius_lt_one (p := p))
    · intro x z
      change dist (f x) (f z) ≤ (p:ℝ)⁻¹ * dist (x:ℚ_[p]) z
      rw [dist_eq_norm, dist_eq_norm,
        show f x-f z = -(coordinateRemainder x-coordinateRemainder z) by dsimp [f]; ring,
        norm_neg]
      exact coordinateRemainder_diff_le hp5
        (by simpa only [s, mem_closedBall_zero_iff] using x.property)
        (by simpa only [s, mem_closedBall_zero_iff] using z.property)
  obtain ⟨x, hx, hfix, _, _⟩ := hcontract.exists_fixedPoint' hsc hmaps hzero (edist_ne_top (x:=0) (y:=f 0))
  refine ⟨x, hx, ?_⟩
  change y-coordinateRemainder x = x at hfix
  unfold evaluateCoordinate
  linear_combination -hfix

end PadicIsometry



section PadicEvaluation

open PowerSeries

variable {p : ℕ} [hp : Fact p.Prime]

private local instance : NonarchimedeanRing ℚ_[p] where
  is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean

/-- The coefficient term of a rational formal series at one p-adic point.
The evaluation lemmas explicitly require summability of the operands. -/
private noncomputable def evalTerm (z : ℚ_[p]) (f : PowerSeries ℚ) (n : ℕ) : ℚ_[p] :=
  (coeff n f : ℚ)*z^n

private noncomputable def evalSeries (z : ℚ_[p]) (f : PowerSeries ℚ) : ℚ_[p] :=
  ∑' n, evalTerm z f n

private theorem evalTerm_add (z : ℚ_[p]) (f g : PowerSeries ℚ) :
    evalTerm z (f+g) = fun n => evalTerm z f n + evalTerm z g n := by
  funext n
  simp [evalTerm, add_mul]

private theorem evalSeries_add (z : ℚ_[p]) {f g : PowerSeries ℚ}
    (hf : Summable (evalTerm z f)) (hg : Summable (evalTerm z g)) :
    Summable (evalTerm z (f+g)) ∧ evalSeries z (f+g) = evalSeries z f+evalSeries z g := by
  simp only [evalSeries, evalTerm_add]
  exact ⟨hf.add hg, hf.tsum_add hg⟩

private theorem evalTerm_mul (z : ℚ_[p]) (f g : PowerSeries ℚ) :
    evalTerm z (f*g) = fun n =>
      ∑ kl ∈ Finset.antidiagonal n, evalTerm z f kl.1 * evalTerm z g kl.2 := by
  funext n
  simp only [evalTerm, coeff_mul, Rat.cast_sum, Rat.cast_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro kl hk
  rw [← Finset.mem_antidiagonal.mp hk, pow_add]
  ring

private theorem evalSeries_mul (z : ℚ_[p]) {f g : PowerSeries ℚ}
    (hf : Summable (evalTerm z f)) (hg : Summable (evalTerm z g)) :
    Summable (evalTerm z (f*g)) ∧ evalSeries z (f*g) = evalSeries z f*evalSeries z g := by
  simp only [evalTerm_mul, evalSeries]
  have hfg := hf.mul_of_nonarchimedean hg
  exact ⟨summable_sum_mul_antidiagonal_of_summable_mul hfg,
    (hf.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg hfg).symm⟩

private theorem evalSeries_natMul (z : ℚ_[p]) (a : ℕ) {f : PowerSeries ℚ}
    (hf : Summable (evalTerm z f)) :
    Summable (evalTerm z (a*f)) ∧ evalSeries z (a*f) = a*evalSeries z f := by
  have he : evalTerm z (a*f) = fun n => a*evalTerm z f n := by
    funext n
    rw [← nsmul_eq_mul]
    simp [evalTerm, nsmul_eq_mul, mul_assoc]
  simp only [evalSeries, he]
  exact ⟨hf.mul_left _, tsum_mul_left⟩

private theorem evalTerm_rescale (z : ℚ_[p]) (a : ℚ) (f : PowerSeries ℚ) :
    evalTerm z (rescale a f) = evalTerm ((a:ℚ_[p])*z) f := by
  funext n
  simp only [evalTerm, coeff_rescale, Rat.cast_mul, Rat.cast_pow, mul_pow]
  ring

private theorem evalTerm_coordinate (z : ℚ_[p]) : evalTerm z coordinate = coordinateTerm z := by
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [evalTerm, coordinateTerm]
  simp only [evalTerm, coeff_coordinate, coordinateTerm, ite_eq_right hn,
    Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast]
  ring

private theorem nine_preserves_small_ball {z : ℚ_[p]} (hz : ‖z‖ ≤ (p:ℝ)⁻¹) :
    ‖9*z‖ ≤ (p:ℝ)⁻¹ := by
  have hn : ‖(9 : ℚ_[p])‖ ≤ 1 := by
    rw [Padic.norm_le_one_iff_val_nonneg, Padic.valuation_ofNat]
    positivity
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hn).trans hz

/-- The coordinate relation survives analytic evaluation at every point of
the small p-adic ball, with no root restriction on the point. -/
theorem evaluateCoordinate_cubic (hp5 : 5 ≤ p) {z : ℚ_[p]} (hz : ‖z‖ ≤ (p:ℝ)⁻¹) :
    (evaluateCoordinate z)^3 + 6*(evaluateCoordinate z)^2 + 9*evaluateCoordinate z =
      evaluateCoordinate (9*z) := by
  have hG : Summable (evalTerm z coordinate) := by
    rw [evalTerm_coordinate]
    exact coordinate_summable hp5 ((mem_small_ball_iff z).mp hz)
  have hG2 := evalSeries_mul z hG hG
  have hG3 := evalSeries_mul z hG2.1 hG
  have h6 := evalSeries_natMul z 6 hG2.1
  have h9 := evalSeries_natMul z 9 hG
  have hA := evalSeries_add z hG3.1 h6.1
  have hB := evalSeries_add z hA.1 h9.1
  have hres : evalSeries z (rescale (9:ℚ) coordinate) = evalSeries (9*z) coordinate := by
    rw [evalSeries, evalTerm_rescale]
    rfl
  have he (x : ℚ_[p]) (hx : ‖x‖ ≤ (p:ℝ)⁻¹) : evalSeries x coordinate = evaluateCoordinate x := by
    rw [evalSeries, evalTerm_coordinate, evaluateCoordinate_eq_tsum hp5 hx]
  have h := congrArg (evalSeries z) formal_conjugacy
  simp only [pow_succ, pow_zero, one_mul] at h
  norm_num only [Nat.cast_ofNat] at h6 h9 hA hB
  rw [hB.2, hA.2, hG3.2, h6.2, h9.2, hG2.2, hres, he z hz,
    he (9*z) (nine_preserves_small_ball hz)] at h
  simpa only [pow_succ, pow_zero, one_mul] using h

/-- The root-free evaluated series bijects the entire small p-adic ball and
conjugates multiplication by nine to the cubic update there. -/
theorem cubic_isometrically_linearized (hp5 : 5 ≤ p) :
    Set.BijOn (evaluateCoordinate : ℚ_[p] → ℚ_[p])
      (Metric.closedBall 0 ((p:ℝ)⁻¹)) (Metric.closedBall 0 ((p:ℝ)⁻¹)) ∧
    (∀ x : ℚ_[p], ‖x‖ ≤ (p:ℝ)⁻¹ →
      (evaluateCoordinate x)^3 + 6*(evaluateCoordinate x)^2 + 9*evaluateCoordinate x =
        evaluateCoordinate (9*x)) ∧
    (∀ x y : ℚ_[p], ‖x‖ ≤ (p:ℝ)⁻¹ → ‖y‖ ≤ (p:ℝ)⁻¹ →
      ‖evaluateCoordinate x-evaluateCoordinate y‖ = ‖x-y‖) := by
  refine ⟨Set.BijOn.mk (evaluateCoordinate_mapsTo hp5) ?_
    (evaluateCoordinate_surjectiveOn hp5), fun x hx => evaluateCoordinate_cubic hp5 hx,
    fun x y hx hy => evaluateCoordinate_isometry hp5 hx hy⟩
  intro x hx y hy h
  rw [mem_closedBall_zero_iff] at hx hy
  have hs := evaluateCoordinate_isometry hp5 hx hy
  rw [h, sub_self, norm_zero, eq_comm, norm_eq_zero, sub_eq_zero] at hs
  exact hs

end PadicEvaluation

section Equivalence

variable {p : ℕ} [hp : Fact p.Prime]

/-- The small closed ball (p\mathbf Z_p), carrying its inherited metric. -/
abbrev SmallBall (p : ℕ) [Fact p.Prime] :=
  ↥(Metric.closedBall (0 : ℚ_[p]) ((p : ℝ)⁻¹))

noncomputable def ballTimesNine (x : SmallBall p) : SmallBall p :=
  ⟨9*x.val, by rw [mem_closedBall_zero_iff]
               exact nine_preserves_small_ball ((mem_closedBall_zero_iff).mp x.property)⟩

noncomputable def ballCubic (hp5 : 5 ≤ p) (y : SmallBall p) : SmallBall p :=
  ⟨y.val^3 + 6*y.val^2 + 9*y.val, by
    obtain ⟨z, hz, he⟩ := evaluateCoordinate_surjectiveOn hp5 y.property
    rw [← he, evaluateCoordinate_cubic hp5 ((mem_closedBall_zero_iff).mp hz)]
    exact evaluateCoordinate_mapsTo hp5 (ballTimesNine ⟨z,hz⟩).property⟩

/-- The full-ball coordinate and its inverse as a bundled isometry. -/
noncomputable def linearizingIsometry (hp5 : 5 ≤ p) : SmallBall p ≃ᵢ SmallBall p where
  toEquiv := Equiv.ofBijective
    ((evaluateCoordinate_mapsTo hp5).restrict evaluateCoordinate _ _)
    (cubic_isometrically_linearized hp5).1.bijective
  isometry_toFun := Isometry.of_dist_eq fun x y => by
    change dist (evaluateCoordinate x.val) (evaluateCoordinate y.val) = dist x.val y.val
    rw [dist_eq_norm, dist_eq_norm]
    exact evaluateCoordinate_isometry hp5
      ((mem_closedBall_zero_iff).mp x.property) ((mem_closedBall_zero_iff).mp y.property)

/-- The cubic update on the entire small p-adic ball is isometrically
conjugate to multiplying the linear coordinate by nine. -/
theorem linearizingIsometry_conj (hp5 : 5 ≤ p) (z : SmallBall p) :
    linearizingIsometry hp5 (ballTimesNine z) =
      ballCubic hp5 (linearizingIsometry hp5 z) := by
  apply Subtype.ext
  exact (evaluateCoordinate_cubic hp5 ((mem_closedBall_zero_iff).mp z.property)).symm

end Equivalence

end D5.S3.Arith.Primes.GoldenCubicPadicConjugacy
