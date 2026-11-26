/- GID: D5/S1/Words/Patterns/Separable/EndpointQuadraticMarginal
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/EndpointQuadraticMarginal
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Actual marked-cycle prefix discrepancies have uniformly tight quadratic marginals. -/

import D5.S1.Words.Patterns.Separable.EndpointFirstCycleHitLimit
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

namespace D5.S1.Words.Patterns.Separable.EndpointQuadraticMarginal
open CutFactorization MinimumCutKernel OccupiedComparison ActualCycleLaw ActualCycles
open scoped ENNReal
open scoped BigOperators

private noncomputable def scaledWeight (s : ℝ) (n : ℕ) : ℝ :=
  (rho * s) ^ (n + 1) * (Nat.card (Avoider (n + 1)) : ℝ)

private noncomputable def shapePGF (s : ℝ) : ℝ := ∑' n, scaledWeight s n

private theorem scaledWeight_eq (s : ℝ) (n : ℕ) :
    scaledWeight s n = shapeWeight n * s ^ (n + 1) := by
  unfold scaledWeight shapeWeight
  rw [mul_pow]
  ring

private theorem shapePGF_equation (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ shapePGF s ∧ shapePGF s ≤ b ∧
    shapePGF s = rho * s + rho * s * shapePGF s + shapePGF s ^ 2 := by
  let w := scaledWeight s
  have rnon : 0 ≤ rho := by unfold rho; positivity
  have hnon (n : ℕ) : 0 ≤ w n := by dsimp [w, scaledWeight]; positivity
  have hbound (n : ℕ) : w n ≤ shapeWeight n := by
    rw [show w n = scaledWeight s n from rfl, scaledWeight_eq]
    exact mul_le_of_le_one_right (by unfold shapeWeight rho; positivity)
      (pow_le_one₀ hs hs1)
  have hsum : Summable w := Summable.of_nonneg_of_le hnon hbound critical_shape_masses.1
  obtain ⟨_, actualCounts, _, _, _, _, _, _, _, _⟩ :=
    D5.S1.Words.Patterns.Separable.ActualCardinality.actual_schroder_cardinality
  have weightCount (n : ℕ) : w n = (rho * s) ^ (n + 1) * (Nat.largeSchroder n : ℝ) := by
    simp only [w, scaledWeight, actualCounts (n + 1) (by omega), Nat.add_sub_cancel]
  have weightZero : w 0 = rho * s := by simp [weightCount]
  have recurrence (n : ℕ) : w (n + 1) = (rho * s) * w n +
      ∑ pair ∈ Finset.antidiagonal n, w pair.1 * w pair.2 := by
    have counts : (Nat.largeSchroder (n + 1) : ℝ) = (Nat.largeSchroder n : ℝ) +
        ∑ pair ∈ Finset.antidiagonal n,
          (Nat.largeSchroder pair.1 : ℝ) * (Nat.largeSchroder pair.2 : ℝ) := by
      have natural := Nat.largeSchroder_succ n
      rw [← Nat.range_succ_eq_Iic] at natural
      rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => Nat.largeSchroder i * Nat.largeSchroder j)] at natural
      exact_mod_cast natural
    rw [weightCount, counts, mul_add, Finset.mul_sum, weightCount]
    congr 1
    · rw [pow_succ]
      ring
    · apply Finset.sum_congr rfl
      intro pair member
      rw [weightCount, weightCount]
      have indices := Finset.mem_antidiagonal.mp member
      have exponents : n + 1 + 1 = (pair.1 + 1) + (pair.2 + 1) := by omega
      rw [exponents, pow_add]
      ring
  have productSum : Summable (fun pair : ℕ × ℕ =>
      w pair.1 * w pair.2) := hsum.mul_of_nonneg hsum hnon hnon
  have convolutionSum := summable_sum_mul_antidiagonal_of_summable_mul productSum
  have cauchy := hsum.tsum_mul_tsum_eq_tsum_sum_antidiagonal hsum productSum
  have totalEquation : (∑' n, w n) = (rho * s) + (rho * s) * (∑' n, w n) +
      (∑' n, w n) ^ 2 := by
    calc
      (∑' n, w n) = (rho * s) + ∑' n, w (n + 1) := by
        rw [hsum.tsum_eq_zero_add, weightZero]
      _ = (rho * s) + ∑' n, ((rho * s) * w n +
          ∑ pair ∈ Finset.antidiagonal n, w pair.1 * w pair.2) := by
        congr 1
        exact tsum_congr recurrence
      _ = (rho * s) + (rho * s) * (∑' n, w n) + (∑' n, w n) ^ 2 := by
        rw [((hsum.mul_left (rho * s)).tsum_add convolutionSum), tsum_mul_left, ← cauchy]
        ring

  refine ⟨tsum_nonneg hnon, ?_, totalEquation⟩
  exact (hsum.tsum_le_tsum hbound critical_shape_masses.1).trans_eq critical_shape_masses.2.1

private theorem shapePGF_deficit_sq (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    (b - shapePGF s) ^ 2 = rho * (1 - s) * (1 + shapePGF s) := by
  have root := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hr : rho + 2 * b = 1 := by unfold rho b; nlinarith
  have hb : b ^ 2 = rho := rfl
  nlinarith [shapePGF_equation s hs hs1 |>.2.2, congrArg (· * shapePGF s) hr]


private theorem weight_nonneg (s : ℝ) (hs : 0 ≤ s) (n : ℕ) : 0 ≤ scaledWeight s n := by
  unfold scaledWeight rho
  positivity

private theorem weight_summable (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    Summable (scaledWeight s) :=
  Summable.of_nonneg_of_le (weight_nonneg s hs)
    (fun n => by
      rw [scaledWeight_eq]
      exact mul_le_of_le_one_right (by unfold shapeWeight rho; positivity)
        (pow_le_one₀ hs hs1))
    critical_shape_masses.1

private noncomputable def terminalPGF (s : ℝ) : ℝ := (shapePGF s + rho * s) / 2

section
variable (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
include hs
private theorem nonnegative_rhos : 0 ≤ rho * s :=
  mul_nonneg (by unfold rho; positivity) hs
include hs1
private theorem scaled_removal_mass :
    (∑' c : Removal, ENNReal.ofReal ((rho * s) ^ (c.1 + 1))) = ENNReal.ofReal (shapePGF s) := by
  classical
  rw [ENNReal.tsum_sigma']
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card]
  have cast (n : ℕ) : (Nat.card (Avoider (n + 1)) : ℝ≥0∞) *
      ENNReal.ofReal ((rho * s) ^ (n + 1)) = ENNReal.ofReal (scaledWeight s n) := by
    rw [scaledWeight, ENNReal.ofReal_mul (pow_nonneg (nonnegative_rhos s hs) _)]
    simp only [ENNReal.ofReal_natCast, mul_comm]
  simp_rw [cast]
  rw [← ENNReal.ofReal_tsum_of_nonneg (weight_nonneg s hs) (weight_summable s hs hs1)]
  rfl
private theorem scaled_terminal_mass (sign : Bool) :
    (∑' c : Σ n : ℕ, Indecomposable sign (n + 1),
      ENNReal.ofReal ((rho * s) ^ (c.1 + 1))) = ENNReal.ofReal (terminalPGF s) := by
  classical
  rw [ENNReal.tsum_sigma']
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card]
  have counts := D5.S1.Words.Patterns.Separable.ActualCardinality.actual_schroder_cardinality.2.2.1
  simp_rw [counts sign, ← counts false]
  have cast (n : ℕ) : (Nat.card (Indecomposable false (n + 1)) : ℝ≥0∞) *
      ENNReal.ofReal ((rho * s) ^ (n + 1)) = ENNReal.ofReal
        ((rho * s) ^ (n + 1) * (Nat.card (Indecomposable false (n + 1)) : ℝ)) := by
    rw [ENNReal.ofReal_mul (pow_nonneg (nonnegative_rhos s hs) _)]
    simp only [ENNReal.ofReal_natCast, mul_comm]
  simp_rw [cast]

  have point (n : ℕ) :
      (rho * s) ^ (n + 1) * (Nat.card (Indecomposable false (n + 1)) : ℝ) =
        (scaledWeight s n + (if n = 0 then rho * s else 0)) / 2 := by
    have h := critical_shape_masses.2.2.2.2.2.2 n
    unfold kernelWeight at h
    rw [mul_pow, scaledWeight_eq]
    have heq : rho ^ (n + 1) * s ^ (n + 1) *
          (Nat.card (Indecomposable false (n + 1)) : ℝ) =
        (rho ^ (n + 1) * (Nat.card (Indecomposable false (n + 1)) : ℝ)) *
          s ^ (n + 1) := by ring
    rw [heq, h]
    by_cases hn : n = 0
    · subst n
      simp
      ring
    · simp [hn]
      ring
  simp_rw [point]
  have summableDelta : Summable (fun n : ℕ => if n = 0 then rho * s else 0) :=
    summable_of_ne_finset_zero (s := {0}) (by intro n hn; exact ite_eq_right (by simpa using hn))
  have summableSum := (weight_summable s hs hs1).add summableDelta
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun n => div_nonneg (add_nonneg (weight_nonneg s hs n)
      (by split_ifs <;> first | exact nonnegative_rhos s hs | exact le_rfl)) (by norm_num))
    (summableSum.div_const _), tsum_div_const,
    (weight_summable s hs hs1).tsum_add summableDelta, tsum_ite_eq]
  rfl
private theorem scaled_fixed_mass (sign : Bool) (r : ℕ) :
    (∑' c : Fixed sign r, ENNReal.ofReal ((rho * s) ^ c.size)) =
      ENNReal.ofReal (terminalPGF s * shapePGF s ^ r) := by
  induction r generalizing sign with
  | zero =>
    change (∑' c : Σ n : ℕ, Indecomposable sign (n + 1),
      ENNReal.ofReal ((rho * s) ^ (c.1 + 1))) = _
    simpa only [pow_zero, mul_one] using scaled_terminal_mass s hs hs1 sign
  | succ r ih =>
    change (∑' c : Removal × Fixed (!sign) r,
      ENNReal.ofReal ((rho * s) ^ (c.1.1 + 1 + c.2.size))) = _
    have split (c : Removal × Fixed (!sign) r) :
        ENNReal.ofReal ((rho * s) ^ (c.1.1 + 1 + c.2.size)) =
          ENNReal.ofReal ((rho * s) ^ (c.1.1 + 1)) * ENNReal.ofReal ((rho * s) ^ c.2.size) := by
      rw [pow_add, ENNReal.ofReal_mul (pow_nonneg (nonnegative_rhos s hs) _)]
    simp_rw [split]
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left, ih]
    rw [ENNReal.tsum_mul_right, scaled_removal_mass s hs hs1,
      ← ENNReal.ofReal_mul (shapePGF_equation s hs hs1).1]
    congr 1
    ring

private theorem scaled_signed_mass (sign : Bool) :
    (∑' c : UnboundedCycle sign, ENNReal.ofReal ((rho * s) ^ c.size)) =
      ENNReal.ofReal (terminalPGF s * (1 - shapePGF s)⁻¹) := by
  rw [← (enumeration sign).symm.tsum_eq]
  simp only [enumeration, Equiv.coe_fn_symm_mk, Fixed.decode_size]
  rw [ENNReal.tsum_sigma']
  simp_rw [scaled_fixed_mass s hs hs1]

  have hb : b < 1 := by unfold b; have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num); nlinarith
  have hB := shapePGF_equation s hs hs1
  have hT : 0 ≤ terminalPGF s :=
    div_nonneg (add_nonneg hB.1 (nonnegative_rhos s hs)) (by norm_num)
  have summable : Summable (fun r : ℕ => terminalPGF s * shapePGF s ^ r) :=
    (summable_geometric_of_lt_one hB.1 (hB.2.1.trans_lt hb)).mul_left _
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun r => mul_nonneg hT (pow_nonneg hB.1 r)) summable,
    tsum_mul_left, tsum_geometric_of_lt_one hB.1 (hB.2.1.trans_lt hb)]

end

private theorem cyclePGF (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    (∑' c : MarkedCycle, cyclePMF c * ENNReal.ofReal (s ^ c.2.size)) =
      ENNReal.ofReal ((shapePGF s + rho * s) / (1 - shapePGF s)) := by
  have hr : 0 ≤ rho := by unfold rho; positivity
  have scaled (c : MarkedCycle) :
      cyclePMF c * ENNReal.ofReal (s ^ c.2.size) =
        ENNReal.ofReal ((rho * s) ^ c.2.size) := by
    change ENNReal.ofReal (rho ^ c.2.size) * _ = _
    rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg hr _)]
  simp_rw [scaled]
  rw [ENNReal.tsum_sigma']
  simp_rw [scaled_signed_mass s hs hs1]
  simp only [tsum_fintype, Fintype.sum_bool]
  have hB := shapePGF_equation s hs hs1
  have hb : b < 1 := by
    unfold b
    have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith
  have hT : 0 ≤ terminalPGF s :=
    div_nonneg (add_nonneg hB.1 (mul_nonneg hr hs)) (by norm_num)
  have hp : 0 ≤ terminalPGF s * (1 - shapePGF s)⁻¹ :=
    mul_nonneg hT (inv_nonneg.mpr (sub_nonneg.mpr (hB.2.1.trans hb.le)))
  rw [← ENNReal.ofReal_add hp hp]
  congr 1
  unfold terminalPGF
  ring

open EndpointCanonicalCycle
open MeasureTheory

private theorem abs_discrepancyDelta_le_size {sign : Bool} (c : UnboundedCycle sign) :
    |discrepancyDelta c| ≤ (c.size : ℤ) := by
  induction c with
  | @terminal sg n shape =>
    cases sg <;> simp only [discrepancyDelta, UnboundedCycle.size, Bool.false_eq_true,
      ite_false, ite_true, Nat.cast_add, Nat.cast_one] <;>
      exact abs_le.mpr ⟨by omega, by omega⟩
  | @discard sign n shape c ih =>
    rw [discrepancyDelta, UnboundedCycle.size]
    push_cast
    calc
      _ ≤ |if sign then (n : ℤ) + 1 else 0| + |discrepancyDelta c| := abs_add_le _ _
      _ ≤ _ := by
        have h : |if sign then (n : ℤ) + 1 else 0| ≤ (n : ℤ) + 1 := by
          split <;> exact abs_le.mpr ⟨by omega, by omega⟩
        omega

private theorem half_laplace_of_large (x : ℝ) (hx : 1 ≤ x) (n : ℕ) (hn : x < n) :
    (x / (1 + x)) ^ n ≤ (1 / 2 : ℝ) := by
  have hxpos : 0 < x := by linarith
  have hx' : 0 ≤ 1 / x := by positivity
  have bern := one_add_mul_le_pow (a := 1 / x) (by linarith) n
  have hq : 1 ≤ (n : ℝ) * (1 / x) := by
    rw [mul_one_div, le_div_iff₀ hxpos]
    simpa using hn.le
  have ht : (2 : ℝ) ≤ (1 + 1 / x) ^ n := by linarith
  have hrecip : x / (1 + x) = (1 + 1 / x)⁻¹ := by
    have hz : x + 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [hrecip, inv_pow, inv_le_iff_one_le_mul₀ (by positivity)]
  linarith

private theorem pgf_deficit_le (x : ℝ) (hx : 1 ≤ x) :
    let s := x / (1 + x)
    1 - (shapePGF s + rho * s) / (1 - shapePGF s) ≤ 10 / Real.sqrt (1 + x) := by
  let s := x / (1 + x)
  change 1 - (shapePGF s + rho * s) / (1 - shapePGF s) ≤ _
  have hxpos : 0 < 1 + x := by linarith
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hs1 : s ≤ 1 := (div_le_one hxpos).2 (by linarith)
  have hb : b ≤ 1 / 2 := by
    unfold b
    have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith [sq_nonneg (Real.sqrt 2 - 3/2)]
  have hr : 0 ≤ rho ∧ rho ≤ 1 := by
    unfold rho
    have h : 0 ≤ b := by
      unfold b
      have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      nlinarith [Real.sqrt_nonneg 2]
    exact ⟨sq_nonneg _, by nlinarith⟩
  obtain ⟨hB, hBb, _⟩ := shapePGF_equation s hs hs1
  have hd : 0 < 1 - shapePGF s := by linarith
  have hg : 1 - s = (1 + x)⁻¹ := by dsimp [s]; field_simp; ring
  have hsq := shapePGF_deficit_sq s hs hs1
  rw [hg] at hsq
  have ht : 0 < Real.sqrt (1 + x) := Real.sqrt_pos.2 hxpos
  have htsq := Real.sq_sqrt hxpos.le
  have ht1 : 1 ≤ Real.sqrt (1 + x) := by nlinarith
  have hquad : ((b - shapePGF s) * Real.sqrt (1 + x)) ^ 2 ≤ 4 := by
    rw [mul_pow, hsq, htsq]
    field_simp
    nlinarith [mul_le_mul_of_nonneg_right hr.2 (show 0 ≤ 1 + shapePGF s by linarith)]
  have hgap : b - shapePGF s ≤ 2 / Real.sqrt (1 + x) := by
    apply (le_div_iff₀ ht).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hBb) ht.le]
  have hsmall : rho * (1 - s) ≤ 1 / Real.sqrt (1 + x) := by
    rw [hg]
    apply (le_div_iff₀ ht).2
    rw [mul_right_comm]
    apply (mul_inv_le_iff₀ hxpos).2
    calc
      rho * Real.sqrt (1 + x) ≤ 1 * Real.sqrt (1 + x) := mul_le_mul_of_nonneg_right hr.2 ht.le
      _ ≤ 1 * (1 + x) := by nlinarith only [htsq, ht1, mul_nonneg (sub_nonneg.mpr ht1) ht.le]
  have hrb : 2 * b + rho = 1 := by
    unfold rho b
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have heq : 1 - (shapePGF s + rho * s) / (1 - shapePGF s) =
      (2 * (b - shapePGF s) + rho * (1 - s)) / (1 - shapePGF s) := by
    field_simp
    linarith
  rw [heq, div_le_iff₀ hd]
  have hscale := mul_le_mul_of_nonneg_left (show (1/2 : ℝ) ≤ 1 - shapePGF s by linarith)
      (show 0 ≤ 10 / Real.sqrt (1 + x) by positivity)
  simp only [div_eq_mul_inv] at hscale hgap hsmall ⊢
  linarith

open EndpointFirstCycleHitLimit

private theorem one_sub_pow_sum_le (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    {ι : Type*} (a : ι → ℕ) (S : Finset ι) :
    1 - s ^ (∑ i ∈ S, a i) ≤ ∑ i ∈ S, (1 - s ^ a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, pow_add]
    have h := mul_nonneg (sub_nonneg.mpr (pow_le_one₀ hs hs1 (n := a i)))
      (sub_nonneg.mpr (pow_le_one₀ hs hs1 (n := ∑ j ∈ S, a j)))
    linarith only [ih, h]

private theorem lintegral_deficit_coordinate (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (i : ℕ) :
    (∫⁻ ω : Stream, ENNReal.ofReal (1 - s ^ (ω i).2.size) ∂streamMeasure) =
      ENNReal.ofReal (1 - (shapePGF s + rho * s) / (1 - shapePGF s)) := by
  let f : MarkedCycle → ℝ≥0∞ := fun c => ENNReal.ofReal (1 - s ^ c.2.size)
  have hm := measurable_of_countable f
  have coord : MeasurePreserving (fun ω : Stream => ω i) streamMeasure cyclePMF.toMeasure :=
    measurePreserving_eval_infinitePi (fun _ : ℕ => cyclePMF.toMeasure) i
  have hint := coord.lintegral_comp hm
  change (∫⁻ ω : Stream, f (ω i) ∂streamMeasure) = _ at hint
  rw [hint, lintegral_countable']
  simp_rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  let P := (shapePGF s + rho * s) / (1 - shapePGF s)
  let A : ℝ≥0∞ := ∑' c : MarkedCycle, f c * cyclePMF c
  change A = ENNReal.ofReal (1 - P)
  have hsum : A + ENNReal.ofReal P = 1 := by
    rw [← cyclePGF s hs hs1]
    change (∑' c : MarkedCycle, f c * cyclePMF c) + _ = _
    rw [← ENNReal.tsum_add]
    calc
      _ = ∑' c : MarkedCycle, cyclePMF c := by
        apply tsum_congr
        intro c
        dsimp [f]
        rw [mul_comm (cyclePMF c), ← add_mul,
          ← ENNReal.ofReal_add (sub_nonneg.mpr (pow_le_one₀ hs hs1)) (pow_nonneg hs _),
          sub_add_cancel, ENNReal.ofReal_one, one_mul]
      _ = 1 := PMF.tsum_coe _
  have hp : 0 ≤ P := by
    obtain ⟨hB, hBb, _⟩ := shapePGF_equation s hs hs1
    have hb : b < 1 := by
      unfold b
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    exact div_nonneg (add_nonneg hB (by unfold rho; positivity)) (by linarith)
  have hA : A ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans le_self_add hsum.le)
  have hreal := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add hA ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp,
    ENNReal.toReal_one] at hreal
  have heq : A.toReal = 1 - P := by linarith
  rw [← heq, ENNReal.ofReal_toReal hA]

private theorem stream_size_tail (j : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    streamMeasure {ω : Stream | x < ((∑ i : Fin j, (ω i.val).2.size : ℕ) : ℝ)} ≤
      ENNReal.ofReal (20 * j / Real.sqrt (1 + x)) := by
  let s := x / (1 + x)
  have hxpos : 0 < 1 + x := by linarith
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hs1 : s ≤ 1 := (div_le_one hxpos).2 (by linarith)
  let A : Set Stream := {ω | x < ((∑ i : Fin j, (ω i.val).2.size : ℕ) : ℝ)}
  let f (i : Fin j) (ω : Stream) := ENNReal.ofReal (1 - s ^ (ω i.val).2.size)
  have hf (i : Fin j) : Measurable (f i) :=
    (measurable_of_countable (fun c : MarkedCycle => ENNReal.ofReal (1 - s ^ c.2.size))).comp
      (measurable_pi_apply i.val)
  have hA : MeasurableSet A := by
    let g (ω : Stream) (i : Fin j) := ω i.val
    let T : Set (Fin j → MarkedCycle) := {w | x < ((∑ i : Fin j, (w i).2.size : ℕ) : ℝ)}
    change MeasurableSet (g ⁻¹' T)
    exact T.to_countable.measurableSet.preimage (measurable_pi_iff.2 fun i => measurable_pi_apply i.val)
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_one]
    norm_num
  have hpoint (ω : Stream) : A.indicator (fun _ => (1/2 : ℝ≥0∞)) ω ≤ ∑ i : Fin j, f i ω := by
    by_cases hw : ω ∈ A
    · rw [Set.indicator_of_mem hw, ← hhalf]
      have hlow := half_laplace_of_large x hx (∑ i : Fin j, (ω i.val).2.size) hw
      have hpow := one_sub_pow_sum_le s hs hs1 (fun i : Fin j => (ω i.val).2.size) Finset.univ
      have hnon (i : Fin j) : 0 ≤ 1 - s ^ (ω i.val).2.size :=
        sub_nonneg.mpr (pow_le_one₀ hs hs1)
      have he := ENNReal.ofReal_le_ofReal (show (1/2 : ℝ) ≤ ∑ i : Fin j, (1 - s ^ (ω i.val).2.size) by
        change s ^ (∑ i : Fin j, (ω i.val).2.size) ≤ (1/2 : ℝ) at hlow
        linarith only [hlow, hpow])
      rwa [ENNReal.ofReal_sum_of_nonneg (fun i _ => hnon i)] at he
    · simp [Set.indicator_of_notMem hw]
  have hint := lintegral_mono (μ := streamMeasure) hpoint
  rw [lintegral_indicator_const hA, lintegral_finsetSum _ (fun i _ => hf i)] at hint
  simp_rw [f, lintegral_deficit_coordinate s hs hs1] at hint
  have hbound (i : Fin j) : ENNReal.ofReal (1 - (shapePGF s + rho * s) / (1 - shapePGF s)) ≤
      ENNReal.ofReal (10 / Real.sqrt (1 + x)) :=
    ENNReal.ofReal_le_ofReal (pgf_deficit_le x hx)
  have hh := hint.trans (Finset.sum_le_sum fun i _ => hbound i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  have hh' := ENNReal.toReal_mono (by finiteness) hh
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hh'
  rw [← hhalf, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 10 / Real.sqrt (1 + x))] at hh'
  change streamMeasure A ≤ _
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (by positivity)]
  convert (show (streamMeasure A).toReal ≤ 2 * (j * (10 / Real.sqrt (1 + x))) by linarith) using 1
  ring

/-- Absolute prefix discrepancy from an initial integer offset. -/
def shiftedMagnitude (e : ℤ) (j : ℕ) (ω : Stream) : ℝ :=
  |((e + streamDiscrepancy j ω : ℤ) : ℝ)|

/-- A uniform quadratic scale for the actual marked-cycle stream, with an explicit constant. -/
theorem actual_uniform_quadratic_marginal (e : ℤ) (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    streamMeasure {ω : Stream | (|(e : ℝ)| + (max 1 (20 / δ))^2) *
        ((j : ℝ) + 1)^2 < shiftedMagnitude e j ω} ≤ ENNReal.ofReal δ := by
  let L : ℝ := max 1 (20 / δ)
  have hL : 1 ≤ L := le_max_left _ _
  have hδL : (20 : ℝ) / δ ≤ L := le_max_right _ _
  let x : ℝ := (L * ((j : ℝ) + 1))^2
  have gj : 1 ≤ (j : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
  have U : 1 ≤ L * ((j : ℝ) + 1) := by nlinarith only [mul_le_mul_of_nonneg_right hL (by positivity : 0 ≤ (j : ℝ)+1), gj]
  have hx : 1 ≤ x := by dsimp [x]; nlinarith
  apply (measure_mono ?_).trans ((stream_size_tail j x hx).trans (ENNReal.ofReal_le_ofReal ?_))
  · intro ω hω
    change (|(e : ℝ)| + L^2) * ((j : ℝ) + 1)^2 <
      |((e + streamDiscrepancy j ω : ℤ) : ℝ)| at hω
    change x < ((∑ i : Fin j, (ω i.val).2.size : ℕ) : ℝ)
    have hdisc : |streamDiscrepancy j ω| ≤ (∑ i : Fin j, ((ω i.val).2.size : ℤ)) := by
      unfold streamDiscrepancy
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun _ _ => abs_discrepancyDelta_le_size _)
    have hcast : (|streamDiscrepancy j ω| : ℝ) ≤ ((∑ i : Fin j, (ω i.val).2.size : ℕ) : ℝ) := by
      push_cast
      exact_mod_cast hdisc
    have htotal := abs_add_le (e : ℝ) ((streamDiscrepancy j ω : ℤ) : ℝ)
    push_cast at hω hcast ⊢
    have he := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ ((j : ℝ)+1)^2 by nlinarith) (abs_nonneg (e : ℝ))
    dsimp [x]
    nlinarith only [htotal, hω, hcast, he]
  · apply (div_le_iff₀ (Real.sqrt_pos.2 (by linarith))).2
    have hroot : L * ((j : ℝ) + 1) ≤ Real.sqrt (1+x) := by
      have hsq := Real.sq_sqrt (show 0 ≤ 1+x by linarith)
      dsimp [x] at hsq
      nlinarith [Real.sqrt_nonneg (1+x)]
    have h20 : 20 ≤ δ * L := by
      have h := (div_le_iff₀ hδ).1 hδL
      linarith only [h]
    have h0 : 20 * ((j : ℝ)+1) ≤ δ * (L * ((j : ℝ)+1)) := by
      calc
        _ ≤ (δ * L) * ((j : ℝ)+1) := mul_le_mul_of_nonneg_right h20 (by positivity)
        _ = _ := by ring
    exact (le_trans (by linarith only [h0] : 20 * (j : ℝ) ≤ _) (mul_le_mul_of_nonneg_left hroot hδ.le))

#print axioms actual_uniform_quadratic_marginal

end D5.S1.Words.Patterns.Separable.EndpointQuadraticMarginal
