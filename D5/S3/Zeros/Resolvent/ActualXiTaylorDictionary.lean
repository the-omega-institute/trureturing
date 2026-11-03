/- GID: D5/S3/Zeros/Resolvent/ActualXiTaylorDictionary
   generality: I
   mirror-B: D5/B/S3/Zeros/Resolvent/ActualXiTaylorDictionary
   mirror-E: none(waiver:actual-analytic-zero-source)
   anchors: []
   utility: none
   digest: The actual xi folded resolvent has its full derivative-identified moment series. -/

import D5.S3.Zeros.Resolvent.ActualXiFoldedResolvent
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic

/-!
All sums are over distinct actual positive-height zeros with analytic multiplicity
in the weights. The full Taylor identification is for the independently defined
xiOdd, not a function defined by the series. The complex square in the subsequent
Hankel identity is not a modulus square. No ordinary novelty is claimed.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Zeros.Resolvent.ActualXiTaylorDictionary
open Complex Filter Finset
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Zeros.Resolvent.ActualXiFoldedSpectrum
open D5.S3.Zeros.Resolvent.ActualXiFoldedResolvent
open scoped Topology ComplexConjugate

def totalWeight : ℝ := ∑' n : PositiveZero, ‖weight n‖

def radius : ℝ := sSup (insert 0 (Set.range (fun n : PositiveZero => ‖node n‖)))

private theorem radius_bdd : BddAbove (insert 0 (Set.range (fun n : PositiveZero => ‖node n‖))) := by
  refine ⟨1, ?_⟩
  rintro x (rfl | ⟨n, rfl⟩)
  · norm_num
  · exact (node_norm_lt_one n).le

theorem radius_bounds : 0 ≤ radius ∧ radius ≤ 1 := by
  constructor
  · exact le_csSup radius_bdd (Set.mem_insert 0 _)
  · apply csSup_le (Set.insert_nonempty _ _)
    rintro x (rfl | ⟨n, rfl⟩)
    · norm_num
    · exact (node_norm_lt_one n).le

theorem node_norm_le_radius (n : PositiveZero) : ‖node n‖ ≤ radius :=
  le_csSup radius_bdd (Set.mem_insert_of_mem _ ⟨n, rfl⟩)

def moment (j : ℕ) : ℂ := ∑' n : PositiveZero, weight n * node n ^ j

theorem moment_summable (j : ℕ) : Summable (fun n : PositiveZero => weight n * node n ^ j) := by
  apply (weight_norm_summable.mul_right (radius ^ j)).of_norm_bounded
  intro n
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (node_norm_le_radius n) _)
    (norm_nonneg _)

theorem moment_bound (j : ℕ) : ‖moment j‖ ≤ totalWeight * radius ^ j := by
  apply tsum_of_norm_bounded ((weight_norm_summable.hasSum).mul_right (radius ^ j))
  intro n
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (node_norm_le_radius n) _)
    (norm_nonneg _)

theorem moment_real (j : ℕ) : (moment j).im = 0 := by
  have hc : conj (moment j) = moment j := by
    rw [moment, Complex.conj_tsum]
    calc
      (∑' n : PositiveZero, conj (weight n * node n ^ j)) =
          ∑' n : PositiveZero, weight (conjugation n) * node (conjugation n) ^ j := by
        apply tsum_congr
        intro n
        simp [weight_conjugation, node_conjugation]
      _ = moment j := by
        simpa only [moment] using
          conjugation.tsum_eq (fun n : PositiveZero => weight n * node n ^ j)
  have hi := congrArg Complex.im hc
  simp only [Complex.conj_im] at hi
  linarith

private theorem moment_bound_mass (j : ℕ) : ‖moment j‖ ≤ totalWeight := by
  calc
    ‖moment j‖ ≤ totalWeight * radius ^ j := moment_bound j
    _ ≤ totalWeight * 1 := mul_le_mul_of_nonneg_left
      (pow_le_one₀ radius_bounds.1 radius_bounds.2) (tsum_nonneg (fun _ => norm_nonneg _))
    _ = totalWeight := mul_one _

private theorem double_summable (w : ℂ) (hw : ‖w‖ < 1) :
    Summable (fun p : PositiveZero × ℕ => weight p.1 * node p.1 ^ p.2 * w ^ (2 * p.2 + 1)) := by
  have hq : ‖w‖ ^ 2 < 1 := by nlinarith [norm_nonneg w]
  have hs := (weight_norm_summable.mul_right ‖w‖).mul_of_nonneg
    (hasSum_geometric_of_lt_one (sq_nonneg ‖w‖) hq).summable
    (fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _)) (fun j => pow_nonneg (sq_nonneg _) j)
  apply hs.of_norm_bounded
  intro p
  simp only [norm_mul, norm_pow]
  have hn : ‖node p.1‖ ^ p.2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (node_norm_lt_one _).le
  calc
    ‖weight p.1‖ * ‖node p.1‖ ^ p.2 * ‖w‖ ^ (2 * p.2 + 1) ≤
        ‖weight p.1‖ * 1 * ‖w‖ ^ (2 * p.2 + 1) := by gcongr
    _ = (‖weight p.1‖ * ‖w‖) * (‖w‖ ^ 2) ^ p.2 := by rw [pow_add, pow_mul]; ring

/-- Full odd-power expansion, with absolute double summability justifying the exchange. -/
theorem actual_xi_moment_hasSum (w : ℂ) (hw : ‖w‖ < 1 / 4) :
    HasSum (fun j : ℕ => moment j * w ^ (2 * j + 1)) (xiOdd w) := by
  have hp := double_summable w (by linarith)
  have hrow (n : PositiveZero) : HasSum
      (fun j : ℕ => weight n * node n ^ j * w ^ (2 * j + 1))
      (w * weight n / (1 - node n * w ^ 2)) := by
    have hnorm : ‖node n * w ^ 2‖ < 1 := by
      rw [norm_mul, norm_pow]
      exact (mul_le_mul_of_nonneg_right (node_norm_lt_one n).le (sq_nonneg ‖w‖)).trans_lt
        (by nlinarith [norm_nonneg w])
    convert (hasSum_geometric_of_norm_lt_one hnorm).mul_left (w * weight n) using 1
    · funext j
      rw [mul_pow, pow_add, pow_mul]
      ring
    · simp [div_eq_mul_inv]
  have he : (∑' j : ℕ, moment j * w ^ (2 * j + 1)) = xiOdd w := by
    simp_rw [moment, ← tsum_mul_right]
    rw [Summable.tsum_comm (f := fun (n : PositiveZero) (j : ℕ) =>
      weight n * node n ^ j * w ^ (2 * j + 1)) hp]
    simp_rw [(hrow _).tsum_eq]
    exact (actual_xi_folded_hasSum w hw).tsum_eq
  rw [← he]
  apply Summable.hasSum
  convert hp.prod_symm.prod using 1
  funext j
  exact (tsum_mul_right).symm

/-- All even coefficients are zero; odd coefficients are the convergent actual moments. -/
def coefficient (k : ℕ) : ℂ := if k % 2 = 1 then moment (k / 2) else 0

private theorem coefficient_odd (j : ℕ) : coefficient (2 * j + 1) = moment j := by
  simp [coefficient, show (2 * j + 1) / 2 = j by omega]

private theorem coefficient_even (j : ℕ) : coefficient (2 * j) = 0 := by
  simp [coefficient]

private theorem coefficient_bound (k : ℕ) : ‖coefficient k‖ ≤ totalWeight := by
  unfold coefficient
  split_ifs
  · exact moment_bound_mass _
  · simpa only [norm_zero, totalWeight] using
      (tsum_nonneg (fun n : PositiveZero => norm_nonneg (weight n)))

/-- The genuine xi expression has this full scalar power series on the specified disk. -/
theorem actual_xi_powerSeries : HasFPowerSeriesOnBall xiOdd
    (FormalMultilinearSeries.ofScalars ℂ coefficient) 0 (ENNReal.ofReal (1 / 4)) := by
  constructor
  · apply le_trans (show ENNReal.ofReal (1 / 4) ≤ (1 : ENNReal) by norm_num)
    apply FormalMultilinearSeries.le_radius_of_bound _ totalWeight (r := 1)
    intro k
    simpa only [FormalMultilinearSeries.ofScalars_norm, NNReal.coe_one, one_pow, mul_one]
      using coefficient_bound k
  · norm_num
  · intro w hw
    have hnorm : ‖w‖ < 1 / 4 := by
      simpa only [Metric.mem_eball, edist_dist, dist_zero_right,
        ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1 / 4)] using hw
    have hi : Function.Injective (fun j : ℕ => 2 * j + 1) := by
      intro a b h
      dsimp at h
      omega
    have hout : ∀ k : ℕ, k ∉ Set.range (fun j : ℕ => 2 * j + 1) →
        coefficient k * w ^ k = 0 := by
      intro k hk
      have hmod : k % 2 ≠ 1 := by
        intro h
        apply hk
        refine ⟨k / 2, ?_⟩
        dsimp
        omega
      simp [coefficient, hmod]
    have h := (hi.hasSum_iff hout).mp
      ((actual_xi_moment_hasSum w hnorm).congr_fun (fun j => by
        simp only [Function.comp_apply, coefficient_odd]))
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] using h

/-- The analytic Taylor coefficient is identified with the actual moment, at every order. -/
theorem actual_xi_coefficient_derivative (k : ℕ) :
    coefficient k = iteratedDeriv k xiOdd 0 / (k.factorial : ℂ) := by
  have h := actual_xi_powerSeries.factorial_smul (1 : ℂ) k
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, one_pow, smul_eq_mul, mul_one,
    nsmul_eq_mul, ← iteratedDeriv_eq_iteratedFDeriv] at h
  apply (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero k)).mpr
  simpa [mul_comm] using h

theorem actual_xi_taylor_moment (j : ℕ) :
    iteratedDeriv (2 * j + 1) xiOdd 0 / ((2 * j + 1).factorial : ℂ) = moment j := by
  rw [← actual_xi_coefficient_derivative, coefficient_odd]

theorem actual_xi_even_derivative (j : ℕ) : iteratedDeriv (2 * j) xiOdd 0 = 0 := by
  have h := actual_xi_coefficient_derivative (2 * j)
  rw [coefficient_even, eq_comm, div_eq_zero_iff] at h
  exact h.resolve_right (by exact_mod_cast Nat.factorial_ne_zero (2 * j))

theorem actual_xi_analytic (w : ℂ) (hw : ‖w‖ < 1 / 4) : AnalyticAt ℂ xiOdd w := by
  apply actual_xi_powerSeries.analyticAt_of_mem
  simpa only [Metric.mem_eball, edist_dist, dist_zero_right,
    ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1 / 4)] using hw

end D5.S3.Zeros.Resolvent.ActualXiTaylorDictionary
