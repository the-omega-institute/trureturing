/- GID: D5/S1/Words/Patterns/Separable/ActualCountRatios
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/ActualCountRatios
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Schroder]
   utility: none
   digest: Critical actual-shape masses and full-sequence fixed-shift count ratio limits. -/

import D5.S1.Words.Patterns.Separable.ActualCardinality
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.RingTheory.PowerSeries.Schroder
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic

namespace D5.S1.Words.Patterns.Separable.OccupiedComparison

open D5.S1.Words.Patterns.Separable.CutFactorization
open D5.S1.Words.Patterns.Separable.MinimumCutKernel
open scoped BigOperators

noncomputable def b : ℝ := Real.sqrt 2 - 1
noncomputable def rho : ℝ := b ^ 2
noncomputable def a : ℝ := 1 - b
noncomputable def h : ℝ := (1 + b) / 2
noncomputable def ceiling : ℝ := a / 2
noncomputable def shapeWeight (n : ℕ) : ℝ := rho ^ (n + 1) * (Nat.card (Avoider (n + 1)) : ℝ)
/-- The correction at index zero is the genuine length-one correction. -/
noncomputable def kernelWeight (n : ℕ) : ℝ := shapeWeight n + if n = 0 then rho / 2 else 0
theorem critical_shape_masses : Summable shapeWeight ∧
    (∑' n, shapeWeight n) = b ∧ Summable kernelWeight ∧
    (∑' n, kernelWeight n) = (1 / 2 : ℝ) ∧
    Summable (fun n : ℕ => rho ^ (n + 1) *
      (Nat.card (Indecomposable false (n + 1)) : ℝ)) ∧
    (∑' n : ℕ, rho ^ (n + 1) *
      (Nat.card (Indecomposable false (n + 1)) : ℝ)) = ceiling ∧
    (∀ n : ℕ, rho ^ (n + 1) * (Nat.card (Indecomposable false (n + 1)) : ℝ) =
      (kernelWeight n + (if n = 0 then rho / 2 else 0)) / 2) := by
  classical
  have sqrtSq : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have sqrtPos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have sqrtBounds : 1 < Real.sqrt (2 : ℝ) ∧ Real.sqrt (2 : ℝ) < 2 := by
    constructor <;> nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hp : 0 < h := by dsimp [h, b]; linarith
  have hc : 0 < ceiling := by dsimp [ceiling, a, b]; linarith [sqrtBounds.2]
  have hsumc : h + ceiling = 1 := by dsimp [h, ceiling, a, b]; ring
  have hsq : h ^ 2 = (1 / 2 : ℝ) := by dsimp [h, b]; nlinarith
  have rhop : 0 < rho := by exact pow_pos (sub_pos.mpr sqrtBounds.1) 2
  have tn (n : ℕ) : 0 ≤ shapeWeight n := by
    unfold shapeWeight
    positivity
  obtain ⟨_, actualCounts, _, _, _, _, _, _, _, _⟩ :=
    D5.S1.Words.Patterns.Separable.ActualCardinality.actual_schroder_cardinality
  have weightCount (n : ℕ) : shapeWeight n = rho ^ (n + 1) * (Nat.largeSchroder n : ℝ) := by
    simp only [shapeWeight, actualCounts (n + 1) (by omega), Nat.add_sub_cancel]
  have weightZero : shapeWeight 0 = rho := by simp [weightCount]
  have recurrence (n : ℕ) : shapeWeight (n + 1) = rho * shapeWeight n +
      ∑ pair ∈ Finset.antidiagonal n, shapeWeight pair.1 * shapeWeight pair.2 := by
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
  have bp : 0 < b := sub_pos.mpr sqrtBounds.1
  have bquadratic : b ^ 2 + 2 * b = 1 := by dsimp [b]; nlinarith
  have rhoValue : rho = 1 - 2 * b := by dsimp [rho]; nlinarith
  have critical : rho + rho * b + b ^ 2 = b := by rw [rhoValue]; nlinarith
  have triangleBound (n : ℕ) : (∑ k ∈ Finset.range n,
        ∑ pair ∈ Finset.antidiagonal k, shapeWeight pair.1 * shapeWeight pair.2) ≤
      (∑ k ∈ Finset.range n, shapeWeight k) ^ 2 := by
    have disjoint : Set.PairwiseDisjoint (Finset.range n : Set ℕ) Finset.antidiagonal := by
      intro i _ j _ different
      apply Finset.disjoint_left.mpr
      intro pair hi hj
      exact different ((Finset.mem_antidiagonal.mp hi).symm.trans (Finset.mem_antidiagonal.mp hj))
    rw [← Finset.sum_biUnion disjoint]
    calc
      (∑ pair ∈ (Finset.range n).biUnion Finset.antidiagonal,
          shapeWeight pair.1 * shapeWeight pair.2) ≤
          ∑ pair ∈ (Finset.range n) ×ˢ (Finset.range n),
            shapeWeight pair.1 * shapeWeight pair.2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro pair member
          obtain ⟨k, hk, hpair⟩ := Finset.mem_biUnion.mp member
          have indices := Finset.mem_antidiagonal.mp hpair
          simp only [Finset.mem_product, Finset.mem_range]
          have := Finset.mem_range.mp hk
          omega
        · intro pair _ _
          exact mul_nonneg (tn _) (tn _)
      _ = (∑ k ∈ Finset.range n, shapeWeight k) ^ 2 := by
        rw [Finset.sum_product, ← Finset.sum_mul_sum, pow_two]
  have partialBound (n : ℕ) : (∑ k ∈ Finset.range n, shapeWeight k) ≤ b := by
    induction n with
    | zero => simpa using bp.le
    | succ n ih =>
      rw [Finset.sum_range_succ', weightZero]
      simp_rw [recurrence]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      have nonneg : 0 ≤ ∑ k ∈ Finset.range n, shapeWeight k := Finset.sum_nonneg (fun k _ => tn k)
      have squareBound : (∑ k ∈ Finset.range n, shapeWeight k) ^ 2 ≤ b ^ 2 := by nlinarith
      have linearBound := mul_le_mul_of_nonneg_left ih rhop.le
      have quadraticBound := triangleBound n
      linarith [critical]
  have hsum : Summable shapeWeight := summable_of_sum_range_le tn partialBound
  have productSum : Summable (fun pair : ℕ × ℕ =>
      shapeWeight pair.1 * shapeWeight pair.2) := hsum.mul_of_nonneg hsum tn tn
  have convolutionSum := summable_sum_mul_antidiagonal_of_summable_mul productSum
  have cauchy := hsum.tsum_mul_tsum_eq_tsum_sum_antidiagonal hsum productSum
  have totalEquation : (∑' n, shapeWeight n) = rho + rho * (∑' n, shapeWeight n) +
      (∑' n, shapeWeight n) ^ 2 := by
    calc
      (∑' n, shapeWeight n) = rho + ∑' n, shapeWeight (n + 1) := by
        rw [hsum.tsum_eq_zero_add, weightZero]
      _ = rho + ∑' n, (rho * shapeWeight n +
          ∑ pair ∈ Finset.antidiagonal n, shapeWeight pair.1 * shapeWeight pair.2) := by
        congr 1
        exact tsum_congr recurrence
      _ = rho + rho * (∑' n, shapeWeight n) + (∑' n, shapeWeight n) ^ 2 := by
        rw [((hsum.mul_left rho).tsum_add convolutionSum), tsum_mul_left, ← cauchy]
        ring
  have shapeTotal : (∑' n, shapeWeight n) = b := by
    rw [rhoValue] at totalEquation
    have zero : ((∑' n, shapeWeight n) - b) ^ 2 = 0 := by nlinarith [bquadratic]
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp zero)
  have kn (n : ℕ) : 0 ≤ kernelWeight n := by
    unfold kernelWeight
    have := tn n
    split_ifs <;> positivity
  have deltaSum : Summable (fun n : ℕ => if n = 0 then rho / 2 else 0) :=
    summable_of_ne_finset_zero (s := {0}) (by
      intro n hn
      simp only [Finset.mem_singleton] at hn
      exact if_neg hn)
  have ksum : Summable kernelWeight := hsum.add deltaSum
  have hmass : ∑' n : ℕ, kernelWeight n = (1 / 2 : ℝ) := by
    change tsum (fun n : ℕ => shapeWeight n + if n = 0 then rho / 2 else 0) = _
    rw [hsum.tsum_add deltaSum, shapeTotal]
    simp only [tsum_ite_eq]
    rw [rhoValue]
    ring
  obtain ⟨_, _, _, halfCounts, _, _, singletonCount, tinyCounts, _, _⟩ :=
    D5.S1.Words.Patterns.Separable.ActualCardinality.actual_schroder_cardinality
  let indecomposableWeight (n : ℕ) : ℝ :=
    rho ^ (n + 1) * (Nat.card (Indecomposable false (n + 1)) : ℝ)
  have indecomposableIdentity (n : ℕ) : indecomposableWeight n =
      (kernelWeight n + (if n = 0 then rho / 2 else 0)) / 2 := by
    by_cases nz : n = 0
    · subst n
      have singletonIndecomposable := (tinyCounts false).2
      simp only [indecomposableWeight, kernelWeight, shapeWeight,
        singletonIndecomposable, singletonCount, Nat.cast_one, zero_add,
        pow_one, ite_true]
      ring
    · have large : 2 ≤ n + 1 := by omega
      have halfReal : (2 : ℝ) * (Nat.card (Indecomposable false (n + 1)) : ℝ) =
          (Nat.card (Avoider (n + 1)) : ℝ) := by
        exact_mod_cast halfCounts false (n + 1) large
      dsimp [indecomposableWeight, kernelWeight, shapeWeight]
      simp only [nz, ite_false, add_zero]
      rw [← halfReal]
      ring
  have indecomposableSummable : Summable indecomposableWeight := by
    apply Summable.congr ((ksum.add deltaSum).div_const 2)
    intro n
    exact (indecomposableIdentity n).symm
  have indecomposableTotal : (∑' n, indecomposableWeight n) = ceiling := by
    calc
      (∑' n, indecomposableWeight n) =
          (∑' n, (kernelWeight n + (if n = 0 then rho / 2 else 0)) / 2) :=
        tsum_congr indecomposableIdentity
      _ = ((∑' n, kernelWeight n) + rho / 2) / 2 := by
        rw [tsum_div_const, ksum.tsum_add deltaSum]
        simp
      _ = ceiling := by
        rw [hmass]
        dsimp [ceiling, a, rho, b]
        nlinarith
  exact ⟨hsum, shapeTotal, ksum, hmass, indecomposableSummable, indecomposableTotal,
    indecomposableIdentity⟩

#print axioms critical_shape_masses

end D5.S1.Words.Patterns.Separable.OccupiedComparison

namespace D5.S1.Words.Patterns.Separable.ActualCountRatios

open D5.S1.Words.Patterns.Separable.MinimumCutKernel
open D5.S1.Words.Patterns.Separable.CutFactorization
open D5.S1.Words.Patterns.Separable.ActualCardinality
open Filter Topology PowerSeries
open scoped BigOperators

private noncomputable def series : PowerSeries ℝ :=
  PowerSeries.largeSchroderSeries.map (Nat.castRingHom ℝ)

private theorem series_equation : series = 1 + PowerSeries.X * series +
    PowerSeries.X * series ^ 2 := by
  have h := congrArg (PowerSeries.map (Nat.castRingHom ℝ))
    largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul_largeSchroderSeries_sq
  simpa only [map_add, map_one, map_mul, PowerSeries.map_X, map_pow, series] using h

private theorem schroder_recurrence (n : ℕ) :
    ((n : ℝ) + 3) * (Nat.largeSchroder (n + 2) : ℝ) =
      (6 * n + 9) * (Nat.largeSchroder (n + 1) : ℝ) -
        n * (Nat.largeSchroder n : ℝ) := by
  let x : PowerSeries ℝ := PowerSeries.X
  let f := series
  have eq : (1 - x) * f - x * f ^ 2 - 1 = 0 := by
    dsimp [x, f]
    linear_combination series_equation
  have deq : (1 - x - 2 * x * f) * PowerSeries.derivative (R := ℝ) f - f - f ^ 2 = 0 := by
    have h := congrArg (PowerSeries.derivative (R := ℝ)) eq
    dsimp [x] at h ⊢
    simp only [map_sub, Derivation.leibniz, PowerSeries.derivative_one,
      PowerSeries.derivative_X, PowerSeries.derivative_pow, map_zero,
      smul_eq_mul, Nat.cast_ofNat, sub_zero] at h
    linear_combination h
  have differential : x * ((1 - 6 * x + x ^ 2) * PowerSeries.derivative (R := ℝ) f) +
      f - 3 * (x * f) = 1 + x := by
    linear_combination
      x * (1 - x - 2 * x * f) * deq +
        (1 + x + 2 * x * f + 4 * x ^ 2 * PowerSeries.derivative (R := ℝ) f) * eq
  have expanded : x * PowerSeries.derivative (R := ℝ) f -
      PowerSeries.C 6 * (x * (x * PowerSeries.derivative (R := ℝ) f)) +
      x * (x * (x * PowerSeries.derivative (R := ℝ) f)) + f -
        PowerSeries.C 3 * (x * f) = 1 + x := by
    change _ - (6 : PowerSeries ℝ) * _ + _ + _ - (3 : PowerSeries ℝ) * _ = _
    linear_combination differential
  have xd (k : ℕ) : PowerSeries.coeff k (PowerSeries.X * PowerSeries.derivative (R := ℝ) f) =
      (k : ℝ) * PowerSeries.coeff k f := by
    cases k with
    | zero => simp
    | succ k =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
      push_cast
      ring
  have coeff (k : ℕ) : PowerSeries.coeff k f = (Nat.largeSchroder k : ℝ) := by
    simp [f, series]
  have h := congrArg (PowerSeries.coeff (n + 2)) expanded
  dsimp only [x] at h
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul,
    xd, PowerSeries.coeff_succ_X_mul, coeff, PowerSeries.coeff_one, PowerSeries.coeff_X,
    show n + 2 ≠ 0 by omega, show n + 2 ≠ 1 by omega, ite_false, zero_add,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at h
  linear_combination h

private theorem schroder_positive (n : ℕ) : 0 < (Nat.largeSchroder n : ℝ) := by
  have natural : 0 < Nat.largeSchroder n := by
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.largeSchroder_succ]; omega
  exact_mod_cast natural

private noncomputable def ratio (n : ℕ) : ℝ :=
  (Nat.largeSchroder (n + 1) : ℝ) / Nat.largeSchroder n

private theorem ratio_recurrence (n : ℕ) :
    ratio (n + 1) = (6 * n + 9) / (n + 3) -
      (n : ℝ) / ((n + 3) * ratio n) := by
  have h := schroder_recurrence n
  have hn := (schroder_positive n).ne'
  have hn' := (schroder_positive (n + 1)).ne'
  have nn : (n : ℝ) + 3 ≠ 0 := by positivity
  dsimp [ratio]
  field_simp
  nlinarith

private noncomputable def growth : ℝ := 3 + 2 * Real.sqrt 2

private theorem growth_bounds : 5 < growth ∧ growth < 6 ∧
    growth ^ 2 - 6 * growth + 1 = 0 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  dsimp [growth]
  constructor
  · nlinarith
  constructor <;> nlinarith

private noncomputable def advance (n : ℕ) (x : ℝ) : ℝ :=
  (6 * n + 9) / (n + 3) - (n : ℝ) / ((n + 3) * x)

private theorem advance_lower (n : ℕ) {x : ℝ} (hx : 2 ≤ x) : 2 ≤ advance n x := by
  have hp : 0 < x := by linarith
  have hn : 0 < (n : ℝ) + 3 := by positivity
  have eq : advance n x = ((6 * n + 9) * x - n) / (((n : ℝ) + 3) * x) := by
    dsimp [advance]
    field_simp
  rw [eq, le_div_iff₀ (mul_pos hn hp)]
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sub_nonneg.mpr hx)]

private theorem advance_upper (n : ℕ) {x : ℝ} (hx : 2 ≤ x)
    (hu : x ≤ growth) : advance n x ≤ growth := by
  have hp : 0 < x := by linarith
  have hn : 0 < (n : ℝ) + 3 := by positivity
  have hg := growth_bounds
  have hprod : (6 - growth) * x ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hg.2.1.le) (sub_nonneg.mpr hu)]
  have hneg : 9 - 3 * growth < 0 := by linarith
  have first := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg (α := ℝ) n)
    (sub_nonpos.mpr hprod)
  have last := mul_nonpos_of_nonpos_of_nonneg hneg.le hp.le
  have eq : advance n x = ((6 * n + 9) * x - n) / (((n : ℝ) + 3) * x) := by
    dsimp [advance]
    field_simp
  rw [eq, div_le_iff₀ (mul_pos hn hp)]
  nlinarith

private theorem advance_mono (n : ℕ) {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) :
    advance n x ≤ advance n y := by
  have hn : 0 < (n : ℝ) + 3 := by positivity
  exact sub_le_sub_left
    (div_le_div_of_nonneg_left (Nat.cast_nonneg n) (mul_pos hn (by linarith))
      (mul_le_mul_of_nonneg_left hxy hn.le)) _

private theorem advance_step (n : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    advance n x ≤ advance (n + 1) x := by
  have hp : 0 < x := by linarith
  have hn : 0 < (n : ℝ) + 3 := by positivity
  have hn' : 0 < (n : ℝ) + 4 := by positivity
  have difference : advance (n + 1) x - advance n x =
      (9 * x - 3) / (((n : ℝ) + 3) * (n + 4) * x) := by
    dsimp [advance]
    push_cast
    field_simp
    ring
  have : 0 ≤ advance (n + 1) x - advance n x := by
    rw [difference]
    exact div_nonneg (by linarith) (by positivity)
  linarith

private theorem ratio_bounds (n : ℕ) :
    2 ≤ ratio n ∧ ratio n ≤ growth ∧ ratio n ≤ ratio (n + 1) := by
  induction n with
  | zero =>
    refine ⟨by norm_num [ratio], ?_, by norm_num [ratio]⟩
    have := growth_bounds.1
    norm_num [ratio]
    linarith
  | succ n ih =>
    have eq : ratio (n + 1) = advance n (ratio n) := ratio_recurrence n
    refine ⟨?_, ?_, ?_⟩
    · rw [eq]
      exact advance_lower n ih.1
    · rw [eq]
      exact advance_upper n ih.1 ih.2.1
    · rw [ratio_recurrence (n + 1)]
      change ratio (n + 1) ≤ advance (n + 1) (ratio (n + 1))
      calc
        ratio (n + 1) = advance n (ratio n) := eq
        _ ≤ advance (n + 1) (ratio n) := advance_step n ih.1
        _ ≤ advance (n + 1) (ratio (n + 1)) := advance_mono _ ih.1 ih.2.2

private theorem ratio_limit : Tendsto ratio atTop (𝓝 growth) := by
  have mono : Monotone ratio := monotone_nat_of_le_succ (fun n => (ratio_bounds n).2.2)
  have bounded : BddAbove (Set.range ratio) := ⟨growth, by
    rintro _ ⟨n, rfl⟩
    exact (ratio_bounds n).2.1⟩
  let l : ℝ := ⨆ n, ratio n
  have limit : Tendsto ratio atTop (𝓝 l) := tendsto_atTop_ciSup mono bounded
  have hl : 2 ≤ l := by
    simpa [ratio] using (le_ciSup bounded 0 : ratio 0 ≤ l)
  have lnz : l ≠ 0 := by linarith
  have shifted := (tendsto_add_atTop_iff_nat 1).2 limit
  have linear : Tendsto (fun n : ℕ => (6 * (n : ℝ) + 9) / (n + 3))
      atTop (𝓝 6) := by
    simpa [add_comm, mul_comm] using
      (tendsto_add_mul_div_add_mul_atTop_nhds (9 : ℝ) 3 6 (d := 1) one_ne_zero)
  have fraction := (tendsto_natCast_div_add_atTop (3 : ℝ)).div limit lnz
  have equation : l = 6 - 1 / l := by
    apply tendsto_nhds_unique shifted
    apply (linear.sub fraction).congr'
    exact Filter.Eventually.of_forall (fun n => by
      dsimp only
      rw [ratio_recurrence]
      simp only [Pi.div_apply, div_mul_eq_div_div])
  have polynomial : l ^ 2 - 6 * l + 1 = 0 := by
    field_simp at equation
    nlinarith
  have hg := growth_bounds
  have same : l = growth := by
    have factors : (l - growth) * (l - (6 - growth)) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp factors with first | last
    · linarith
    · linarith
  simpa only [same] using limit

private theorem forward_limit (shift : ℕ) :
    Tendsto (fun n : ℕ => (Nat.largeSchroder (n + shift) : ℝ) /
      Nat.largeSchroder n) atTop (𝓝 (growth ^ shift)) := by
  induction shift with
  | zero =>
    simpa only [Nat.add_zero, div_self (schroder_positive _).ne', pow_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  | succ shift ih =>
    have shifted := ratio_limit.comp (tendsto_add_atTop_nat shift)
    have product := ih.mul shifted
    apply product.congr'
    exact Filter.Eventually.of_forall (fun n => by
      dsimp [ratio]
      rw [← Nat.add_assoc]
      field_simp [(schroder_positive (n + shift)).ne'])

/-- Removing any fixed number of labels has the full-sequence critical count ratio. -/
theorem actual_fixed_shift_ratio (shift : ℕ) :
    Tendsto (fun n : ℕ => (Nat.card (Avoider (n - shift)) : ℝ) /
      Nat.card (Avoider n)) atTop
        (𝓝 (OccupiedComparison.rho ^ shift)) := by
  have growthPositive : 0 < growth := lt_trans (by norm_num) growth_bounds.1
  have inverse := (forward_limit shift).inv₀ (pow_ne_zero _ growthPositive.ne')
  have radius : growth⁻¹ = OccupiedComparison.rho := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    apply inv_eq_of_mul_eq_one_right
    dsimp [growth, OccupiedComparison.rho, OccupiedComparison.b]
    nlinarith
  have shifted : Tendsto (fun n : ℕ =>
      (Nat.card (Avoider (n + shift + 1 - shift)) : ℝ) /
        Nat.card (Avoider (n + shift + 1))) atTop
          (𝓝 (OccupiedComparison.rho ^ shift)) := by
    convert inverse using 1
    · funext n
      have one : n + shift + 1 - shift = n + 1 := by omega
      rw [one, actual_schroder_cardinality.2.1 (n + 1) (by omega),
        actual_schroder_cardinality.2.1 (n + shift + 1) (by omega)]
      simp only [Nat.add_sub_cancel, inv_div]
    · rw [← radius, inv_pow]
  exact (tendsto_add_atTop_iff_nat (shift + 1)).mp (by
    simpa only [Nat.add_assoc] using shifted)

#print axioms actual_fixed_shift_ratio

end D5.S1.Words.Patterns.Separable.ActualCountRatios
