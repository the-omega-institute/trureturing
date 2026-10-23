/- GID: D5/S3/Analytic/SeriesInequalities/GurlandLogRemainder
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/GurlandLogRemainder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original Gurland logarithmic remainder converges for every positive real pair. -/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.PSeries
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# The original Gurland logarithmic remainder

The real Euler limit identifies the Gamma logarithm with a nonnegative logarithmic
series. Its absolutely summable logarithmic power series gives the original
positive-shift Hurwitz expansion for every positive pair.
-/

public section

namespace D5.S3.Analytic.SeriesInequalities.GurlandLogRemainder

open Filter Finset
open scoped Topology BigOperators

noncomputable section

/-- The source real Hurwitz series, with its actual positive shift. -/
def sourceHurwitz (s : ℕ) (b : ℝ) : ℝ :=
  ∑' j : ℕ, 1 / ((j : ℝ) + b) ^ s

/-- The modified Gamma ratio in the original question. -/
def gammaRatio (x y : ℝ) : ℝ :=
  Real.Gamma (1 + x) * Real.Gamma (1 + y) /
    Real.Gamma (1 + (x + y) / 2) ^ 2

/-- The finite source expansion, with precisely the indices 1 through m-1. -/
def partialExpansion (x y : ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ Ico 1 m, ((x - y) / 2) ^ (2 * k) *
    sourceHurwitz (2 * k) (1 + (x + y) / 2) / (k : ℝ)

/-- Equation (4) determines the original remainder as this difference. -/
def remainder (x y : ℝ) (m : ℕ) : ℝ :=
  Real.log (gammaRatio x y) - partialExpansion x y m

/-- Open Problem 1, including the diagonal and positive integer arguments. -/
def claim : Prop :=
  ∀ x y : ℝ, 0 < x → 0 < y →
    Tendsto (remainder x y) atTop (𝓝 0)

private def c (x y : ℝ) (n : ℕ) : ℝ :=
  ((x - y) / 2) ^ 2 / ((n : ℝ) + 1 + (x + y) / 2) ^ 2

private theorem c_bounds {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (n : ℕ) :
    0 ≤ c x y n ∧ c x y n < 1 := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hb : 0 < (n : ℝ) + 1 + (x + y) / 2 := by positivity
  constructor
  · exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  · apply (div_lt_one (sq_pos_of_pos hb)).2
    nlinarith [mul_pos hx hy, sq_nonneg ((n : ℝ) + 1)]

private theorem log_term {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (n : ℕ) :
    -Real.log (1 - c x y n) =
      2 * Real.log (1 + (x + y) / 2 + n) -
        Real.log (1 + x + n) - Real.log (1 + y + n) := by
  have hb : 0 < (n : ℝ) + 1 + (x + y) / 2 := by positivity
  have hX : 0 < 1 + x + (n : ℝ) := by positivity
  have hY : 0 < 1 + y + (n : ℝ) := by positivity
  have hA : 0 < 1 + (x + y) / 2 + (n : ℝ) := by positivity
  have heq : 1 - c x y n =
      ((1 + x + n) * (1 + y + n)) / (1 + (x + y) / 2 + n) ^ 2 := by
    unfold c
    field_simp
    ring
  rw [heq, Real.log_div (mul_ne_zero hX.ne' hY.ne') (pow_ne_zero _ hA.ne'),
    Real.log_mul hX.ne' hY.ne', Real.log_pow]
  ring

private theorem log_ratio {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log (gammaRatio x y) = Real.log (Real.Gamma (1 + x)) +
      Real.log (Real.Gamma (1 + y)) -
        2 * Real.log (Real.Gamma (1 + (x + y) / 2)) := by
  have hX := Real.Gamma_pos_of_pos (show 0 < 1 + x by positivity)
  have hY := Real.Gamma_pos_of_pos (show 0 < 1 + y by positivity)
  have hA := Real.Gamma_pos_of_pos (show 0 < 1 + (x + y) / 2 by positivity)
  rw [gammaRatio, Real.log_div (mul_ne_zero hX.ne' hY.ne') (pow_ne_zero _ hA.ne'),
    Real.log_mul hX.ne' hY.ne', Real.log_pow]
  norm_num

private theorem finite_euler {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (N : ℕ) :
    (∑ n ∈ range (N + 1), -Real.log (1 - c x y n)) =
      Real.BohrMollerup.logGammaSeq (1 + x) N +
      Real.BohrMollerup.logGammaSeq (1 + y) N -
      2 * Real.BohrMollerup.logGammaSeq (1 + (x + y) / 2) N := by
  simp_rw [log_term hx hy]
  simp only [sum_sub_distrib, ← mul_sum, Real.BohrMollerup.logGammaSeq]
  ring

private theorem hasSum_log {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    HasSum (fun n : ℕ => -Real.log (1 - c x y n)) (Real.log (gammaRatio x y)) := by
  have hnonneg : ∀ n : ℕ, 0 ≤ -Real.log (1 - c x y n) := by
    intro n
    exact neg_nonneg.mpr (Real.log_nonpos (by linarith [(c_bounds hx hy n).2])
      (sub_le_self _ (c_bounds hx hy n).1))
  apply (hasSum_iff_tendsto_nat_of_nonneg hnonneg _).2
  rw [log_ratio hx hy]
  apply (tendsto_add_atTop_iff_nat 1).1
  have h := ((Real.BohrMollerup.tendsto_log_gamma (show 0 < 1 + x by positivity)).add
    (Real.BohrMollerup.tendsto_log_gamma (show 0 < 1 + y by positivity))).sub
    ((Real.BohrMollerup.tendsto_log_gamma
      (show 0 < 1 + (x + y) / 2 by positivity)).const_mul 2)
  simpa only [← finite_euler hx hy] using h

private theorem hurwitz_summable {b : ℝ} (hb : 1 ≤ b) {s : ℕ} (hs : 2 ≤ s) :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + b) ^ s) := by
  have hbase : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ s) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by omega : 1 < s))
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hbase
  intro n
  gcongr

private theorem power_term (x y : ℝ) (n k : ℕ) :
    c x y n ^ k = ((x - y) / 2) ^ (2 * k) /
      ((n : ℝ) + 1 + (x + y) / 2) ^ (2 * k) := by
  unfold c
  rw [div_pow, ← pow_mul, ← pow_mul]

private theorem coefficient_eq (x y : ℝ) (k : ℕ) :
    (∑' n : ℕ, c x y n ^ (k + 1) / ((k : ℝ) + 1)) =
      ((x - y) / 2) ^ (2 * (k + 1)) *
        sourceHurwitz (2 * (k + 1)) (1 + (x + y) / 2) / (k + 1) := by
  simp_rw [power_term]
  rw [tsum_div_const, sourceHurwitz, ← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro n
  rw [show (n : ℝ) + 1 + (x + y) / 2 = (n : ℝ) + (1 + (x + y) / 2) by ring]
  ring

private theorem column_summable {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (k : ℕ) :
    Summable (fun n : ℕ => c x y n ^ (k + 1) / ((k : ℝ) + 1)) := by
  have hs := hurwitz_summable (show 1 ≤ 1 + (x + y) / 2 by linarith)
    (show 2 ≤ 2 * (k + 1) by omega)
  convert (hs.mul_left (((x - y) / 2) ^ (2 * (k + 1)))).div_const (k + 1 : ℝ) using 1
  ext n
  rw [power_term]
  rw [show (n : ℝ) + 1 + (x + y) / 2 = (n : ℝ) + (1 + (x + y) / 2) by ring]
  ring

private theorem finite_interchange {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (m : ℕ) :
    (∑' n : ℕ, ∑ k ∈ range m, c x y n ^ (k + 1) / ((k : ℝ) + 1)) =
      ∑ k ∈ range m, ((x - y) / 2) ^ (2 * (k + 1)) *
        sourceHurwitz (2 * (k + 1)) (1 + (x + y) / 2) / (k + 1) := by
  rw [Summable.tsum_finsetSum (fun k _ => column_summable hx hy k)]
  simp_rw [coefficient_eq]

private theorem diagonal {x : ℝ} (hx : 0 < x) (m : ℕ) : remainder x x m = 0 := by
  have hG := Real.Gamma_pos_of_pos (show 0 < 1 + x by positivity)
  have hratio : gammaRatio x x = 1 := by
    unfold gammaRatio
    rw [show (x + x) / 2 = x by ring, ← pow_two, div_self (pow_ne_zero 2 hG.ne')]
  have hpartial : partialExpansion x x m = 0 := by
    apply sum_eq_zero
    intro k hk
    have hkpos : 0 < 2 * k := by have := (mem_Ico.mp hk).1; omega
    simp only [sub_self, zero_div, zero_pow (Nat.ne_of_gt hkpos), zero_mul]
  rw [remainder, hratio, Real.log_one, hpartial, sub_self]

private theorem hasSum_coefficients {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    HasSum (fun k : ℕ => ((x - y) / 2) ^ (2 * (k + 1)) *
      sourceHurwitz (2 * (k + 1)) (1 + (x + y) / 2) / (k + 1))
        (Real.log (gammaRatio x y)) := by
  let f : ℕ → ℕ → ℝ := fun n k => c x y n ^ (k + 1) / (k + 1)
  have hrow : ∀ n, HasSum (f n) (-Real.log (1 - c x y n)) := by
    intro n
    exact Real.hasSum_pow_div_log_of_abs_lt_one
      (by rw [abs_of_nonneg (c_bounds hx hy n).1]; exact (c_bounds hx hy n).2)
  have hnonneg : ∀ n k, 0 ≤ f n k := by
    intro n k
    exact div_nonneg (pow_nonneg (c_bounds hx hy n).1 _) (by positivity)
  have hprod : Summable (Function.uncurry f) := by
    apply (summable_prod_of_nonneg (fun p => hnonneg p.1 p.2)).2
    refine ⟨fun n => (hrow n).summable, ?_⟩
    simpa only [(hrow _).tsum_eq] using (hasSum_log hx hy).summable
  have hcolumn : ∀ k, Summable (fun n => f n k) := fun k => column_summable hx hy k
  have hswap : HasSum (fun k => ∑' n, f n k) (Real.log (gammaRatio x y)) := by
    have heq : (∑' k, ∑' n, f n k) = Real.log (gammaRatio x y) := by
      rw [hprod.tsum_comm' (fun n => (hrow n).summable) hcolumn]
      simpa only [(hrow _).tsum_eq] using (hasSum_log hx hy).tsum_eq
    rw [← heq]
    exact hprod.prod_symm.prod.hasSum
  simpa only [f, coefficient_eq] using hswap

/-- The full original positive-real Gurland remainder tends to zero. -/
theorem result : claim := by
  intro x y hx hy
  by_cases hxy : x = y
  · subst y
    change Tendsto (remainder x x) atTop (𝓝 0)
    have heq : remainder x x = fun _ => 0 := funext (diagonal hx)
    rw [heq]
    exact tendsto_const_nhds
  · have h := (hasSum_coefficients hx hy).tendsto_sum_nat
    have hshift := h.comp (tendsto_sub_atTop_nat 1)
    let p : ℕ → ℝ := fun m => ∑' n : ℕ,
      ∑ k ∈ range (m - 1), c x y n ^ (k + 1) / ((k : ℝ) + 1)
    have hp : Tendsto p atTop (𝓝 (Real.log (gammaRatio x y))) := by
      have heq : p = fun m => ∑ k ∈ range (m - 1), ((x - y) / 2) ^ (2 * (k + 1)) *
          sourceHurwitz (2 * (k + 1)) (1 + (x + y) / 2) / (k + 1) :=
        funext (fun m => finite_interchange hx hy (m - 1))
      rw [heq]
      simpa only [Function.comp_def] using hshift
    have heq : remainder x y = fun m => Real.log (gammaRatio x y) - p m := by
      funext m
      unfold remainder partialExpansion p
      rw [finite_interchange hx hy, sum_Ico_eq_sum_range]
      simp only [Nat.add_comm, Nat.cast_add, Nat.cast_one]
    change Tendsto (remainder x y) atTop (𝓝 0)
    rw [heq]
    simpa only [sub_self] using
      (tendsto_const_nhds (x := Real.log (gammaRatio x y))).sub hp

end
end D5.S3.Analytic.SeriesInequalities.GurlandLogRemainder
