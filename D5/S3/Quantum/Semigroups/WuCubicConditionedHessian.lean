import D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy
import D5.S3.Quantum.Semigroups.WuCubicOccupationTaylor
import D5.S3.Quantum.Semigroups.WuCubicHotInnerPartialTrace
import Mathlib.Analysis.Matrix.Order
import D5.S3.Weil.ZetaLinear.RankTrace
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen

/-! Analytic estimates for the Hessian of the conditioned equal-cap Wu cubic deficit. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Set Filter
open scoped BigOperators ComplexOrder ComplexConjugate MatrixOrder Kronecker Matrix.Norms.L2Operator Topology

namespace D5.S3.Quantum.Semigroups.WuCubicConditionedHessian

open WuCubicOperatorBridge (Mat Occupation G GInv generator)
open WuCubicThermalBasis (a b)
open WuRepeatedMiddleCubic (alpha)
open TwistedTwoModeOUComparison (modeJump)
open private gibbsLow gibbsHigh gibbsOccupation jump_zero jump_one from
  D5.S3.Quantum.Semigroups.WuRepeatedMiddleCubic

open WuCubicThermalBasis (Index coefficient degree basis basis_repr)
open WuCubicTranslationEnergy (vPairing vWeight)
open private coefficient_generator vPairing_re_of_coeff vWeight_nonneg from
  D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy

/-- The generator centered at degree three contracts the same Gibbs weighted
quadratic form as the original translation proof, on degrees two through four. -/
theorem degree_contraction {r : ℝ} (hr : 1 ≤ r) (H : Mat)
    (hdegree : ∀ k : Index, degree k < 2 → coefficient r H k = 0) :
    (vPairing r (generator r H - (3 : ℂ) • H)
        (generator r H - (3 : ℂ) • H)).re ≤ (vPairing r H H).re := by
  let R := generator r H - (3 : ℂ) • H
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  have hR (k : Index) : coefficient r R k =
      ((degree k : ℂ) - 3) * coefficient r H k := by
    rw [← basis_repr hr0]
    dsimp only [R]
    rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply,
      basis_repr hr0, basis_repr hr0, coefficient_generator hr0]
    simp only [smul_eq_mul, sub_mul]
  have hRw (k : Index) : vWeight r R k = ((degree k : ℝ) - 3) ^ 2 * vWeight r H k := by
    unfold vWeight
    rw [hR, Complex.normSq_mul, show (degree k : ℂ) - 3 =
      (((degree k : ℝ) - 3 : ℝ) : ℂ) by push_cast; rfl, Complex.normSq_ofReal]
    ring
  have hV (X : Mat) : (vPairing r X X).re = ∑ k : Index, vWeight r X k := by
    simpa only [one_mul] using vPairing_re_of_coeff hr X X (fun _ => 1) (by simp)
  change (vPairing r R R).re ≤ (vPairing r H H).re
  rw [hV, hV]
  apply Finset.sum_le_sum
  intro k _
  rw [hRw]
  by_cases hk : degree k < 2
  · simp [vWeight, hdegree k hk]
  have hfour : degree k ≤ 4 := by
    obtain ⟨i,j⟩ := k
    fin_cases i <;> fin_cases j <;> decide
  have hlow : (2 : ℝ) ≤ degree k := by exact_mod_cast (show 2 ≤ degree k by omega)
  have hhigh : (degree k : ℝ) ≤ 4 := by exact_mod_cast hfour
  have hd : ((degree k : ℝ) - 3) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hlow) (sub_nonneg.mpr hhigh)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hd (vWeight_nonneg hr H k)

/-- The normalized scalar envelope after combining the three entropy terms with
the degree-two energy estimate and the jump-map bound. -/
def p (x : ℝ) : ℝ :=
  x * (4851 / 400 - 9 / 2 - 3 * Real.log (39 * x ^ 3 / 17)) - 1620 / 341

private theorem log_endpoint_upper : Real.log (39 / 17) ≤ 7 / 8 := by
  have h := abs_le.mp (Real.sum_range_sub_log_div_le (x := (11 / 28 : ℝ))
    (by norm_num) 3)
  have hh : (1 + (11 / 28 : ℝ)) / (1 - 11 / 28) = 39 / 17 := by norm_num
  rw [hh] at h
  norm_num [Finset.sum_range_succ] at h
  linarith [h.2]

private theorem p_concave : ConcaveOn ℝ (Icc (5 / 9 : ℝ) 1) p := by
  have hlin := (concaveOn_id (𝕜 := ℝ) (convex_Icc (5 / 9 : ℝ) 1)).smul
    (c := 4851 / 400 - 9 / 2 - 3 * Real.log (39 / 17))
    (by linarith [log_endpoint_upper])
  have hlog := (Real.convexOn_mul_log.subset (fun x hx => show 0 ≤ x from
    le_trans (by norm_num) hx.1) (convex_Icc (5 / 9 : ℝ) 1)).smul (c := 9) (by norm_num)
  have hc := (hlin.sub hlog).sub (convexOn_const (c := (1620 / 341 : ℝ))
    (convex_Icc (5 / 9 : ℝ) 1))
  apply hc.congr
  intro x hx
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx.1
  have harg : 39 * x ^ 3 / 17 = (39 / 17) * x ^ 3 := by ring
  simp only [p, Pi.sub_apply, id_eq, smul_eq_mul, harg,
    Real.log_mul (by norm_num : (39 / 17 : ℝ) ≠ 0) (pow_ne_zero _ hxpos.ne'),
    Real.log_pow]
  ring

/-- The uniform scalar lower bound on the normalized conditioned spectral band. -/
theorem p_ge {x : ℝ} (hx : x ∈ Icc (5 / 9 : ℝ) 1) : 1 / 5 ≤ p x := by
  have hlo : 1 / 5 ≤ p (5 / 9) := by
    unfold p
    have h := Real.log_le_sub_one_of_pos
      (show 0 < (39 : ℝ) * (5 / 9) ^ 3 / 17 by norm_num)
    linarith only [h]
  have hhi : 1 / 5 ≤ p 1 := by
    unfold p
    norm_num only [one_pow, mul_one]
    linarith only [log_endpoint_upper]
  exact (le_min hlo hhi).trans (p_concave.min_le_of_mem_Icc
    (by norm_num) (by norm_num) hx)

/-- The coefficient of the occupation imbalance after canceling the
anticommutator part of the Gibbs logarithm with the dissipator. -/
def theta (r : ℝ) : ℝ := 6 * alpha r * Real.log r - (9 / 4) * (b r - a r)

private theorem theta_factor {r : ℝ} (hr : 1 ≤ r) :
    let u := r - 1
    theta r = -(9 / 4) * u * (1 - u - u ^ 2) * (1 + 3 * u + u ^ 2) /
      ((2 + u) * (1 + u + u ^ 2) * (3 + 3 * u + u ^ 2)) := by
  dsimp
  rcases eq_or_lt_of_le hr with h | h
  · rw [← h]
    norm_num [theta, alpha, a, b]
  have hp : 0 < r := by linarith
  have hl : Real.log r ≠ 0 := (Real.log_pos h).ne'
  have hd : 1 + r ^ 3 ≠ 0 := by positivity
  have hq : r ^ 2 + r + 1 ≠ 0 := by positivity
  have hr1 : r ≠ 1 := ne_of_gt h
  unfold theta alpha b a
  rw [ite_eq_right hr1]
  field_simp [hl, hd, hq]
  ring

/-- Uniform bound on the residual thermal imbalance. -/
theorem abs_theta_le {r : ℝ} (hr : 1 ≤ r) (hhi : r ≤ 6 / 5) :
    |theta r| ≤ 3 / 40 := by
  rw [theta_factor hr]
  let u := r - 1
  change |-(9 / 4 : ℝ) * u * (1 - u - u ^ 2) * (1 + 3 * u + u ^ 2) /
      ((2 + u) * (1 + u + u ^ 2) * (3 + 3 * u + u ^ 2))| ≤ _
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have huhi : u ≤ 1 / 5 := by dsimp [u]; linarith
  have hu2 : u ^ 2 ≤ 1 / 25 := by nlinarith [sq_nonneg (u - 1 / 5)]
  have hn : 0 ≤ 1 - u - u ^ 2 := by linarith
  have hd : 0 < (2 + u) * (1 + u + u ^ 2) * (3 + 3 * u + u ^ 2) := by positivity
  have hnum : (1 - u - u ^ 2) * (1 + 3 * u + u ^ 2) ≤ 1 + 2 * u := by
    nlinarith [sq_nonneg u, pow_nonneg hu 3, pow_nonneg hu 4]
  have hden : 6 * (1 + 2 * u) ≤
      (2 + u) * (1 + u + u ^ 2) * (3 + 3 * u + u ^ 2) := by
    nlinarith [pow_nonneg hu 2, pow_nonneg hu 3, pow_nonneg hu 4, pow_nonneg hu 5]
  rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by
    have : 0 ≤ u * (1 - u - u ^ 2) * (1 + 3 * u + u ^ 2) := by positivity
    nlinarith) hd.le), ← neg_div, div_le_iff₀ hd]
  have hmul := mul_le_mul_of_nonneg_left hnum hu
  have hmul' := mul_le_mul_of_nonneg_right huhi (show 0 ≤ 1 + 2 * u by positivity)
  nlinarith only [hmul, hmul', hden]

private theorem gain_rate_bound {r : ℝ} (hr : 1 ≤ r) (hhi : r ≤ 6 / 5) :
    b r / r ≤ 180 / 341 := by
  have hp : 0 < r := by linarith
  have hd : 0 < 1 + r ^ 3 := by positivity
  have hr2 : r ^ 2 ≤ (6 / 5 : ℝ) ^ 2 := by gcongr
  have hh : 0 ≤ -36 * r ^ 2 + 25 * r + 30 := by linarith
  have h := mul_nonneg (show 0 ≤ 6 - 5 * r by linarith) hh
  have he : b r / r = r ^ 2 / (1 + r ^ 3) := by
    unfold b a
    field_simp
  rw [he, div_le_iff₀ hd]
  nlinarith only [h]

/-- The positive gain map in the actual embedded generator. -/
def gain (r : ℝ) (M : Mat) : Mat :=
  ∑ k : Fin 2, (((2 * a r * r : ℝ) : ℂ) • ((modeJump k)ᴴ * M * modeJump k) +
    ((2 * b r / r : ℝ) : ℂ) • (modeJump k * M * (modeJump k)ᴴ))

/-- Occupation number minus identity, in the physical occupation order. -/
def imbalance : Mat :=
  diagonal fun i => ((i.1.val : ℂ) + (i.2.val : ℂ) - 1)

def loss (r : ℝ) : Mat := 1 - ((b r - a r : ℝ) : ℂ) • imbalance

private theorem gain_sub (r : ℝ) (M N : Mat) :
    gain r (M - N) = gain r M - gain r N := by
  simp only [gain, sub_mul, mul_sub, smul_sub, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  abel

theorem gain_posSemidef {r : ℝ} (hr : 1 ≤ r) {M : Mat} (hM : M.PosSemidef) :
    (gain r M).PosSemidef := by
  have hp : 0 < r := by linarith
  have ha : 0 ≤ a r := by unfold a; positivity
  have hb : 0 ≤ b r := by unfold b; positivity
  refine Matrix.posSemidef_sum _ (fun k _ => ?_)
  exact ((hM.conjTranspose_mul_mul_same (modeJump k)).smul
    (by exact_mod_cast (show 0 ≤ 2 * a r * r by positivity))).add
    ((hM.mul_mul_conjTranspose_same (modeJump k)).smul
      (by exact_mod_cast (show 0 ≤ 2 * b r / r by positivity)))

private theorem gain_one_diagonal (r : ℝ) :
    gain r 1 = diagonal (fun i : Occupation =>
      ((2 * a r * r * ((i.1.val : ℝ) + (i.2.val : ℝ)) +
        2 * b r / r * (2 - (i.1.val : ℝ) - (i.2.val : ℝ)) : ℝ) : ℂ)) := by
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [gain, Fin.sum_univ_two, jump_zero, jump_one, Matrix.mul_apply,
      Matrix.one_apply, Matrix.diagonal_apply, Matrix.kroneckerMap_apply,
      Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Fintype.sum_prod_type, Complex.ofReal_div] <;> ring

/-- The signed gain term admits a Loewner upper bound uniform in the band. -/
theorem gain_le {r : ℝ} (hr : 1 ≤ r) (hhi : r ≤ 6 / 5) {M : Mat}
    (hM : M ≤ 1) : gain r M ≤ ((720 / 341 : ℝ) : ℂ) • (1 : Mat) := by
  have hp : 0 < r := by linarith
  have ha : 0 ≤ a r := by unfold a; positivity
  have hab : a r * r ≤ b r / r := by
    have he : b r / r = r ^ 2 * a r := by unfold b; field_simp
    rw [he]
    nlinarith [mul_nonneg ha (show 0 ≤ r ^ 2 - r by nlinarith)]
  have hrate := gain_rate_bound hr hhi
  have hfirst : gain r M ≤ gain r 1 := by
    rw [Matrix.le_iff, ← gain_sub]
    exact gain_posSemidef hr (Matrix.le_iff.mp hM)
  apply hfirst.trans
  rw [gain_one_diagonal, Matrix.le_iff, ← Matrix.diagonal_one, ← Matrix.diagonal_smul,
    Matrix.diagonal_sub]
  rw [Matrix.posSemidef_diagonal_iff]
  intro ⟨i,j⟩
  simp only [Pi.smul_apply, smul_eq_mul, mul_one]
  change 0 ≤ ((720 / 341 : ℝ) : ℂ) -
    ((2 * a r * r * ((i.val : ℝ) + (j.val : ℝ)) +
        2 * b r / r * (2 - (i.val : ℝ) - (j.val : ℝ)) : ℝ) : ℂ)
  rw [← Complex.ofReal_sub]
  simp only [Complex.nonneg_iff, Complex.ofReal_re, Complex.ofReal_im, and_true]
  fin_cases i <;> fin_cases j <;> norm_num <;> (try simp only [mul_div_assoc]) <;> linarith only [hab, hrate]


private theorem loss_eq_sum {r : ℝ} (hr : 1 ≤ r) :
    loss r = ∑ k : Fin 2, ((a r : ℂ) • ((modeJump k)ᴴ * modeJump k) +
      (b r : ℂ) • (modeJump k * (modeJump k)ᴴ)) := by
  have hab : (a r : ℂ) + (b r : ℂ) = 1 := by
    exact_mod_cast WuCubicThermalBasis.a_add_b (zero_le_one.trans hr)
  ext ⟨i,j⟩ ⟨k,l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [loss, imbalance, Fin.sum_univ_two, jump_zero, jump_one, Matrix.mul_apply,
      Matrix.one_apply, Matrix.diagonal_apply, Matrix.kroneckerMap_apply,
      Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, Fintype.sum_prod_type, Complex.ofReal_sub] <;>
    linear_combination -hab

/-- Decompose the embedded generator into the occupation anticommutator and the
signed positive gain map, using the existing modular transport identity. -/
theorem embedded_generator_eq {r : ℝ} (hr : 1 ≤ r) (M : Mat) :
    G r * generator r (GInv r * M * GInv r) * G r =
      loss r * M + M * loss r - gain r M := by
  rw [WuCubicOperatorBridge.operator_trace_modular_identity hr, loss_eq_sum hr, gain]
  simp only [Finset.sum_mul, Finset.mul_sum, add_mul, mul_add, smul_mul_assoc,
    mul_smul_comm, Finset.sum_add_distrib, Finset.sum_sub_distrib, Complex.ofReal_mul,
    Complex.ofReal_inv, Complex.ofReal_ofNat, smul_add, show gibbsLow r = a r from rfl,
    show gibbsHigh r = b r from rfl, div_eq_mul_inv]
  abel

/-- The physical jump contribution to the normalized energy curvature. -/
theorem neg_gain_trace_ge {r : ℝ} (hr : 1 ≤ r) (hhi : r ≤ 6 / 5)
    {M W : Mat} (hM : M ≤ 1) (hW : W.IsHermitian) :
    -(1620 / 341 : ℝ) * (W ^ 2).trace.re ≤
      -(9 / 4 : ℝ) * (W ^ 2 * gain r M).trace.re := by
  have hsq : (W ^ 2).PosSemidef := by
    simpa only [pow_two, hW.eq] using Matrix.posSemidef_conjTranspose_mul_self W
  have hh := RHLinalg.trace_mul_nonneg_of_posSemidef hsq
    (Matrix.le_iff.mp (gain_le hr hhi hM))
  change 0 ≤ (W ^ 2 * (((720 / 341 : ℝ) : ℂ) • (1 : Mat) - gain r M)).trace.re at hh
  simp only [mul_sub, mul_smul_comm, mul_one, Matrix.trace_sub, Complex.sub_re,
    Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul] at hh
  linarith

/-- The nonconstant part of the logarithmic Gibbs reference. -/
def logImbalance (r : ℝ) : Mat := (Real.log r : ℂ) • imbalance

theorem combined_loss_log (r : ℝ) :
    ((9 / 4 : ℝ) : ℂ) • loss r + ((6 * alpha r : ℝ) : ℂ) • logImbalance r =
      ((9 / 4 : ℝ) : ℂ) • (1 : Mat) + (theta r : ℂ) • imbalance := by
  simp only [loss, logImbalance, theta, Complex.ofReal_mul, Complex.ofReal_sub,
    smul_sub, smul_smul]
  module

/-- Constant part of the logarithm of the cubic-root Gibbs reference. -/
def logCenter (r : ℝ) : ℝ := Real.log r - (2 / 3) * Real.log (1 + r ^ 3)

private theorem thermal_ratio_le {r : ℝ} (hr : 1 ≤ r) (hhi : r ≤ 6 / 5) :
    (1 + r ^ 3) ^ 2 / r ^ 3 ≤ 13 / 3 := by
  have hp : 0 < r := by linarith
  have hlo : 1 ≤ r ^ 3 := by simpa using pow_le_pow_left₀ (by norm_num : 0 ≤ (1 : ℝ)) hr 3
  have hhi' : r ^ 3 ≤ 7 / 4 := by
    calc
      _ ≤ (6 / 5 : ℝ) ^ 3 := by gcongr
      _ ≤ _ := by norm_num
  have h := mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi')
  rw [div_le_iff₀ (by positivity)]
  nlinarith only [h, hhi']

private theorem log_entropy_argument_pos {x : ℝ} (hx : 5 / 9 ≤ x) :
    0 ≤ 9 + 6 * Real.log (39 * x ^ 3 / 17) := by
  have hbase : Real.exp (-1) < 3 / 8 := by
    rw [Real.exp_neg, inv_eq_one_div, div_lt_iff₀ (Real.exp_pos 1)]
    linarith [Real.exp_one_gt_d9]
  have harg : (3 / 8 : ℝ) ≤ 39 * x ^ 3 / 17 := by
    calc
      _ ≤ 39 * (5 / 9 : ℝ) ^ 3 / 17 := by norm_num
      _ ≤ _ := by gcongr
  have h := Real.log_le_log (Real.exp_pos (-1)) (hbase.le.trans harg)
  rw [Real.log_exp] at h
  linarith

/-- The three scalar entropy-curvature coefficients combine after using the mass bound
and the Gibbs logarithmic center. The coefficient is evaluated at the actual eigenvalue. -/
theorem entropy_coefficient_ge {r x T : ℝ} (hr : 1 ≤ r) (hhi : r ≤ 6 / 5)
    (hx : 5 / 9 ≤ x) (hT : 17 / 9 ≤ T) :
    -(x * (9 / 2 + 3 * Real.log (39 * x ^ 3 / 17))) ≤
      -(alpha r * (15 * x + 18 * x * Real.log x)) +
        alpha r * (6 * (1 + Real.log T) * x + 18 * logCenter r * x) := by
  have hp : 0 < r := by linarith
  have hxpos : 0 < x := by linarith
  have hTpos : 0 < T := by linarith
  have hd : 0 < 1 + r ^ 3 := by positivity
  have hratio : 0 < (1 + r ^ 3) ^ 2 / r ^ 3 := by positivity
  have hh : (1 + r ^ 3) ^ 2 / r ^ 3 * x ^ 3 / T ≤ 39 * x ^ 3 / 17 := by
    calc
      _ ≤ (13 / 3 : ℝ) * x ^ 3 / T := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (thermal_ratio_le hr hhi) (by positivity)) hTpos.le
      _ ≤ (13 / 3 : ℝ) * x ^ 3 / (17 / 9) :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hT
      _ = _ := by ring
  have hlog := Real.log_le_log (show 0 < (1 + r ^ 3) ^ 2 / r ^ 3 * x ^ 3 / T by positivity) hh
  rw [Real.log_div (by positivity : (1 + r ^ 3) ^ 2 / r ^ 3 * x ^ 3 ≠ 0) hTpos.ne',
    Real.log_mul hratio.ne' (pow_ne_zero _ hxpos.ne'),
    Real.log_div (pow_ne_zero _ hd.ne') (pow_ne_zero _ hp.ne'),
    Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  have ha := WuCubicOccupationTaylor.alpha_bounds_of_one_le hr
  have hpos := log_entropy_argument_pos hx
  have hc : 9 + 18 * Real.log x - 6 * Real.log T - 18 * logCenter r ≤
      9 + 6 * Real.log (39 * x ^ 3 / 17) := by
    unfold logCenter
    norm_num at hlog
    linarith only [hlog]
  have hmul := mul_le_mul_of_nonneg_left hc ha.1
  have hmul' := mul_le_mul_of_nonneg_right ha.2 hpos
  have hxmul := mul_le_mul_of_nonneg_right (hmul.trans hmul') hxpos.le
  nlinarith only [hxmul]

private theorem imbalance_hermitian : imbalance.IsHermitian := by
  unfold imbalance Matrix.IsHermitian
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  ext ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> norm_num

private theorem imbalance_add_one_psd : (imbalance + (1 : Mat)).PosSemidef := by
  rw [imbalance, ← Matrix.diagonal_one, Matrix.diagonal_add,
    Matrix.posSemidef_diagonal_iff]
  intro ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> norm_num [Complex.nonneg_iff]

private theorem imbalance_sq_le : imbalance ^ 2 ≤ (1 : Mat) := by
  rw [pow_two, imbalance, Matrix.diagonal_mul_diagonal, Matrix.le_iff,
    ← Matrix.diagonal_one, Matrix.diagonal_sub, Matrix.posSemidef_diagonal_iff]
  intro ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> norm_num [Complex.nonneg_iff]

private theorem reTrace_nonneg {M : Mat} (hM : M.PosSemidef) : 0 ≤ M.trace.re :=
  (Complex.nonneg_iff.mp hM.trace_nonneg).1

private theorem square_psd {W : Mat} (hW : W.IsHermitian) : (W ^ 2).PosSemidef := by
  simpa only [pow_two, hW.eq] using Matrix.posSemidef_conjTranspose_mul_self W

/-- The logarithmic middle term has the required lower bound for the actual
Hermitian direction, since the occupation imbalance is bounded below by minus identity. -/
theorem log_middle_ge {r : ℝ} (hr : 1 ≤ r) (hhi : r ≤ 6 / 5)
    {M W : Mat} (hM : M.PosSemidef) (hW : W.IsHermitian) :
    -(3 / 5 : ℝ) * (M * W ^ 2).trace.re ≤
      6 * alpha r * (W * M * W * logImbalance r).trace.re := by
  have hwmw : (W * M * W).PosSemidef := by
    simpa only [hW.eq] using hM.conjTranspose_mul_mul_same W
  have hq : 0 ≤ (M * W ^ 2).trace.re :=
    RHLinalg.trace_mul_nonneg_of_posSemidef hM (square_psd hW)
  have hcycle : (W * M * W).trace = (M * W ^ 2).trace := by
    rw [Matrix.trace_mul_comm (W * M) W, ← Matrix.mul_assoc, ← pow_two,
      Matrix.trace_mul_comm]
  have hh := RHLinalg.trace_mul_nonneg_of_posSemidef hwmw imbalance_add_one_psd
  change 0 ≤ (W * M * W * (imbalance + 1)).trace.re at hh
  rw [mul_add, mul_one, Matrix.trace_add, Complex.add_re, hcycle] at hh
  have hlog0 := Real.log_nonneg hr
  have hlog := Real.log_le_sub_one_of_pos (show 0 < r by linarith)
  have ha := WuCubicOccupationTaylor.alpha_bounds_of_one_le hr
  have hcoeff : 6 * alpha r * Real.log r ≤ 3 / 5 := by
    have h := mul_le_mul_of_nonneg_right ha.2 hlog0
    linarith
  unfold logImbalance
  simp only [mul_smul_comm, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  have hlow := mul_le_mul_of_nonneg_left (show -(M * W ^ 2).trace.re ≤
    (W * M * W * imbalance).trace.re by linarith) (mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (6 : ℝ)) ha.1) hlog0)
  have hlow' := mul_le_mul_of_nonneg_right hcoeff hq
  nlinarith only [hlow, hlow']

/-- The trace of the physical imbalance anticommutator is bounded by the
condition-number estimate on the normalized spectral band. -/
theorem imbalance_anticommutator_bound {M W : Mat} (hM : M.PosSemidef)
    (hlo : ((5 / 9 : ℝ) : ℂ) • (1 : Mat) ≤ M) (hhi : M ≤ 1) (hW : W.IsHermitian) :
    |((M * W ^ 2 + W ^ 2 * M) * imbalance).trace.re| ≤
      (14 / 5 : ℝ) * (M * W ^ 2).trace.re := by
  let K := imbalance
  let q := (M * W ^ 2).trace.re
  let n := (W ^ 2).trace.re
  have hq : 0 ≤ q := RHLinalg.trace_mul_nonneg_of_posSemidef hM (square_psd hW)
  have hn : 0 ≤ n := reTrace_nonneg (square_psd hW)
  have hnq : 5 / 9 * n ≤ q := by
    have h := RHLinalg.trace_mul_nonneg_of_posSemidef (Matrix.le_iff.mp hlo) (square_psd hW)
    change 0 ≤ ((M - ((5 / 9 : ℝ) : ℂ) • (1 : Mat)) * W ^ 2).trace.re at h
    simp only [sub_mul, smul_mul_assoc, one_mul, Matrix.trace_sub, Complex.sub_re,
      Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul] at h
    linarith
  have hK : Kᴴ = K := imbalance_hermitian.eq
  have hW' : Wᴴ = W := hW.eq
  have hB : ((W * K) * M * (W * K)ᴴ).trace.re ≤ n := by
    have h1 := reTrace_nonneg
      ((Matrix.le_iff.mp hhi).conjTranspose_mul_mul_same (K * W))
    have h2 := reTrace_nonneg
      ((Matrix.le_iff.mp imbalance_sq_le).conjTranspose_mul_mul_same W)
    change 0 ≤ ((K * W)ᴴ * (1 - M) * (K * W)).trace.re at h1
    change 0 ≤ (Wᴴ * (1 - K ^ 2) * W).trace.re at h2
    simp only [Matrix.conjTranspose_mul, hK, hW', mul_sub, sub_mul, mul_one,
      Matrix.trace_sub, Complex.sub_re] at h1 h2
    rw [show W * K * (K * W) = W * K ^ 2 * W by rw [pow_two]; noncomm_ring] at h1
    rw [← pow_two] at h2
    simp only [Matrix.conjTranspose_mul, hK, hW']
    linarith only [h1, h2]
  have hcycle : (W * M * W).trace = (M * W ^ 2).trace := by
    rw [Matrix.trace_mul_comm (W * M) W, ← Matrix.mul_assoc, ← pow_two,
      Matrix.trace_mul_comm]
  let : _ := M.toMatrixSeminormedAddCommGroup hM
  let : _ := M.toMatrixInnerProductSpace hM
  have hs (A B : Mat) : inner ℂ A B = (B * M * Aᴴ).trace := rfl
  have hc := pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ) W (W * K)) 2
  rw [hs, hW', mul_pow, norm_sq_eq_re_inner (𝕜 := ℂ) W,
    norm_sq_eq_re_inner (𝕜 := ℂ) (W * K), hs, hs, hW', hcycle] at hc
  have hpair : (W * K * M * W).trace = (M * W ^ 2 * K).trace := by
    rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm (W * (W * K)) M]
    simp [pow_two, Matrix.mul_assoc]
  rw [hpair] at hc
  change ‖(M * W ^ 2 * K).trace‖ ^ 2 ≤ q * ((W * K) * M * (W * K)ᴴ).trace.re at hc
  have hbound : |(M * W ^ 2 * K).trace.re| ≤ (7 / 5 : ℝ) * q := by
    have hnorm := pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm
      (M * W ^ 2 * K).trace) 2
    have hqn := mul_le_mul_of_nonneg_left hB hq
    have hnq' := mul_le_mul_of_nonneg_left hnq hq
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    nlinarith only [hc, hnorm, hqn, hnq', sq_nonneg q]
  have hrev : (W ^ 2 * M * K).trace.re = (M * W ^ 2 * K).trace.re := by
    have h := congrArg Complex.re (Matrix.trace_conjTranspose (M * W ^ 2 * K))
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_pow, hM.isHermitian.eq,
      hW', hK] at h
    rw [Matrix.trace_mul_comm K (W ^ 2 * M)] at h
    change (W ^ 2 * M * K).trace.re = (star (M * W ^ 2 * K).trace).re at h
    exact h
  rw [add_mul, Matrix.trace_add, Complex.add_re, hrev]
  change |(M * W ^ 2 * K).trace.re + (M * W ^ 2 * K).trace.re| ≤ _
  rw [← two_mul, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
  linarith

/-- Combining the anticommutator terms yields the uniform physical loss estimate. -/
theorem combined_loss_trace_ge {r : ℝ} (hr : 1 ≤ r) (hhi : r ≤ 6 / 5)
    {M W : Mat} (hM : M.PosSemidef)
    (hlo : ((5 / 9 : ℝ) : ℂ) • (1 : Mat) ≤ M) (hMhi : M ≤ 1) (hW : W.IsHermitian) :
    (9 / 2 - 21 / 100 : ℝ) * (M * W ^ 2).trace.re ≤
      (9 / 4 : ℝ) * ((M * W ^ 2 + W ^ 2 * M) * loss r).trace.re +
      6 * alpha r * ((M * W ^ 2 + W ^ 2 * M) * logImbalance r).trace.re := by
  let A := M * W ^ 2 + W ^ 2 * M
  let q := (M * W ^ 2).trace.re
  have hq : 0 ≤ q := RHLinalg.trace_mul_nonneg_of_posSemidef hM (square_psd hW)
  have ha : A.trace.re = 2 * q := by
    dsimp [A, q]
    rw [Matrix.trace_add, Complex.add_re, Matrix.trace_mul_comm (W ^ 2) M]
    ring
  have hcombine := congrArg (fun X : Mat => (A * X).trace.re) (combined_loss_log r)
  simp only [mul_add, mul_smul_comm, mul_one, Matrix.trace_add, Complex.add_re,
    Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul, ha] at hcombine
  have hb := imbalance_anticommutator_bound hM hlo hMhi hW
  change |(A * imbalance).trace.re| ≤ (14 / 5 : ℝ) * q at hb
  have htheta := abs_theta_le hr hhi
  have hprod := mul_le_mul htheta hb (abs_nonneg _) (by norm_num : 0 ≤ (3 / 40 : ℝ))
  rw [← abs_mul] at hprod
  have hlow := (neg_abs_le (theta r * (A * imbalance).trace.re)).trans'
    (neg_le_neg hprod)
  change _ ≤ (9 / 4 : ℝ) * (A * loss r).trace.re +
      6 * alpha r * (A * logImbalance r).trace.re
  linarith only [hcombine, hlow]

/-- Algebraic endpoint of the physical normalized curvature estimate, in the spectral
measure of the actual squared direction. The two remaining analytic estimates enter
as the mixed-energy and trace-function bounds. -/
theorem normalized_curvature_ge {r T : ℝ} (hr : 1 ≤ r) (hhi : r ≤ 6 / 5)
    (hT : 17 / 9 ≤ T) (m w : Occupation → ℝ)
    (hm : ∀ i, m i ∈ Icc (5 / 9 : ℝ) 1) (hw : ∀ i, 0 ≤ w i)
    (mixedEnergy gainTerm combinedLoss logRemainder traceCurvature massCurvature : ℝ)
    (hMixed : 135 / 16 * (∑ i, m i * w i) ≤ mixedEnergy)
    (hGain : -(1620 / 341) * (∑ i, w i) ≤ gainTerm)
    (hLoss : (9 / 2 - 21 / 100) * (∑ i, m i * w i) ≤ combinedLoss)
    (hLog : -(3 / 5) * (∑ i, m i * w i) ≤ logRemainder)
    (hTrace : traceCurvature ≤ ∑ i, w i * (15 * m i + 18 * m i * Real.log (m i)))
    (hMass : 6 * (1 + Real.log T) * (∑ i, m i * w i) ≤ massCurvature) :
    (1 / 5 : ℝ) * (∑ i, w i) ≤
      mixedEnergy + gainTerm + combinedLoss + logRemainder -
        alpha r * traceCurvature + alpha r * massCurvature +
        18 * alpha r * logCenter r * (∑ i, m i * w i) := by
  have ha := (WuCubicOccupationTaylor.alpha_bounds_of_one_le hr).1
  have hpoint (i : Occupation) : (1 / 5 : ℝ) * w i ≤
      (135 / 16 + (9 / 2 - 21 / 100) - 3 / 5) * (m i * w i) -
      1620 / 341 * w i -
      alpha r * (w i * (15 * m i + 18 * m i * Real.log (m i))) +
      alpha r * (6 * (1 + Real.log T) * (m i * w i)) +
      18 * alpha r * logCenter r * (m i * w i) := by
    have hp := mul_le_mul_of_nonneg_right (p_ge (hm i)) (hw i)
    have he := mul_le_mul_of_nonneg_right
      (entropy_coefficient_ge hr hhi (hm i).1 hT) (hw i)
    unfold p at hp
    nlinarith only [hp, he]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  have htrace := mul_le_mul_of_nonneg_left hTrace ha
  have hmass := mul_le_mul_of_nonneg_left hMass ha
  linarith only [hsum, hMixed, hGain, hLoss, hLog, htrace, hmass]

/-- The Gibbs reference in the original operator deficit has precisely the
constant and imbalance parts used by the curvature cancellation. -/
theorem log_density_eq {r : ℝ} (hr : 1 ≤ r) :
    cfc Real.log (WuCubicOperatorBridge.D r) =
      ((3 * logCenter r : ℝ) : ℂ) • (1 : Mat) + (3 : ℂ) • logImbalance r := by
  have hp : 0 < r := by linarith
  have hd : 0 < 1 + r ^ 3 := by positivity
  have ha : 0 < gibbsLow r := by unfold gibbsLow; positivity
  have hb : 0 < gibbsHigh r := by unfold gibbsHigh; positivity
  have hdiag : cfc Real.log (WuCubicOperatorBridge.D r) =
      diagonal (fun i : Occupation => (Real.log (gibbsOccupation r i.1 * gibbsOccupation r i.2) : ℂ)) := by
    simpa only [WuCubicOperatorBridge.D, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
      Matrix.cfc_diagonal_real (𝕜 := ℂ)
        (fun i : Occupation => gibbsOccupation r i.1 * gibbsOccupation r i.2) Real.log
  have hg (i : Fin 2) : 0 < gibbsOccupation r i := by
    fin_cases i
    · exact ha
    · exact hb
  have hlow : Real.log (gibbsLow r) = -Real.log (1 + r ^ 3) := by
    unfold gibbsLow
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hd.ne', Real.log_one, zero_sub]
  have hhigh : Real.log (gibbsHigh r) = 3 * Real.log r - Real.log (1 + r ^ 3) := by
    unfold gibbsHigh
    rw [Real.log_mul (pow_ne_zero 3 hp.ne') ha.ne', Real.log_pow, hlow]
    ring
  rw [hdiag]
  ext i j
  by_cases hij : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq, Real.log_mul (hg i.1).ne' (hg i.2).ne']
    obtain ⟨i,j⟩ := i
    fin_cases i <;> fin_cases j <;>
      norm_num [logCenter, logImbalance, imbalance, gibbsOccupation, hlow, hhigh,
        Matrix.smul_apply, smul_eq_mul, Complex.ofReal_add, Complex.ofReal_mul,
        Complex.ofReal_sub] <;> ring
  · simp [logImbalance, imbalance, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

private theorem trace_weighted_cfc (M W : Mat) (hM : M.IsHermitian)
    (f : ℝ → ℝ) :
    (W ^ 2 * cfc f M).trace.re = ∑ i : Occupation,
      ((hM.eigenvectorUnitary.valᴴ * W ^ 2 * hM.eigenvectorUnitary.val) i i).re *
        f (hM.eigenvalues i) := by
  let U : Mat := hM.eigenvectorUnitary
  have hcol : Uᴴ * U = 1 := Unitary.coe_star_mul_self hM.eigenvectorUnitary
  have hc : cfc f M = U * diagonal (fun i => (f (hM.eigenvalues i) : ℂ)) * Uᴴ := by
    rw [hM.cfc_eq f]
    rfl
  rw [hc]
  have htrace : (W ^ 2 * (U * diagonal (fun i => (f (hM.eigenvalues i) : ℂ)) * Uᴴ)).trace =
      (Uᴴ * W ^ 2 * U * diagonal (fun i => (f (hM.eigenvalues i) : ℂ))).trace := by
    rw [← mul_assoc (W ^ 2) (U * Matrix.diagonal _), Matrix.trace_mul_comm _ Uᴴ]
    congr 1
    noncomm_ring
  rw [htrace]
  simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum, Matrix.mul_diagonal,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, U]

/-- The physical curvature expression in the embedded variables. The two input
inequalities are the mixed-generator term and the second entropy-trace variation.
The mass curvature is displayed with its nonnegative square term. -/
theorem physical_curvature_ge {r : ℝ} (hr : 1 ≤ r) (hhi : r ≤ 6 / 5)
    (M W : Mat) (hM : M.PosDef) (hW : W.IsHermitian)
    (hlo : ((5 / 9 : ℝ) : ℂ) • (1 : Mat) ≤ M) (hMhi : M ≤ 1)
    (hm : ∀ i, hM.isHermitian.eigenvalues i ∈ Icc (5 / 9 : ℝ) 1)
    (hT : 17 / 9 ≤ (M ^ 3).trace.re)
    (traceCurvature : ℝ)
    (hTrace : traceCurvature ≤
      (W ^ 2 * cfc (fun x : ℝ => 15 * x + 18 * x * Real.log x) M).trace.re)
    (hMixed : (15 / 4 : ℝ) * (M * W ^ 2).trace.re ≤
      ((M * W + W * M) * (G r * generator r (GInv r * W * GInv r) * G r)).trace.re) :
    (1 / 5 : ℝ) * (W ^ 2).trace.re ≤
      (9 / 4 : ℝ) * (W ^ 2 * (G r * generator r (GInv r * M * GInv r) * G r) +
        (M * W + W * M) * (G r * generator r (GInv r * W * GInv r) * G r)).trace.re -
      alpha r * traceCurvature +
      2 * alpha r * ((M * W ^ 2 + W * M * W + W ^ 2 * M) *
        cfc Real.log (WuCubicOperatorBridge.D r)).trace.re +
      alpha r * (6 * (1 + Real.log (M ^ 3).trace.re) * (M * W ^ 2).trace.re +
        9 * ((M ^ 2 * W).trace.re) ^ 2 / (M ^ 3).trace.re) := by
  let U : Mat := hM.isHermitian.eigenvectorUnitary
  let m : Occupation → ℝ := hM.isHermitian.eigenvalues
  let w : Occupation → ℝ := fun i => ((Uᴴ * W ^ 2 * U) i i).re
  let q := (M * W ^ 2).trace.re
  let v := (W ^ 2).trace.re
  let T := (M ^ 3).trace.re
  let A := M * W ^ 2 + W ^ 2 * M
  let L := G r * generator r (GInv r * W * GInv r) * G r
  have hw (i : Occupation) : 0 ≤ w i :=
    (Complex.nonneg_iff.mp ((square_psd hW).conjTranspose_mul_mul_same U).diag_nonneg).1
  have hU : U * Uᴴ = 1 := Unitary.coe_mul_star_self hM.isHermitian.eigenvectorUnitary
  have hv : ∑ i, w i = v := by
    change (Uᴴ * W ^ 2 * U).trace.re = (W ^ 2).trace.re
    rw [Matrix.trace_mul_cycle, hU, one_mul]
  have hq : ∑ i, m i * w i = q := by
    have h := trace_weighted_cfc M W hM.isHermitian id
    have hId : cfc (id : ℝ → ℝ) M = M := by
      rw [hM.isHermitian.cfc_eq]
      conv_rhs => rw [hM.isHermitian.spectral_theorem]
      rfl
    rw [hId, Matrix.trace_mul_comm] at h
    simpa only [m, w, U, id_eq, mul_comm] using h.symm
  have ht : traceCurvature ≤ ∑ i, w i * (15 * m i + 18 * m i * Real.log (m i)) := by
    rw [trace_weighted_cfc M W hM.isHermitian] at hTrace
    exact hTrace
  have hmass : 6 * (1 + Real.log T) * (∑ i, m i * w i) ≤
      6 * (1 + Real.log T) * q + 9 * (M ^ 2 * W).trace.re ^ 2 / T := by
    rw [hq]
    have hTp : 0 < T := by dsimp [T]; linarith
    exact le_add_of_nonneg_right (div_nonneg (by positivity) hTp.le)
  have hmixed' : 135 / 16 * (∑ i, m i * w i) ≤
      (9 / 4 : ℝ) * ((M * W + W * M) * L).trace.re := by
    rw [hq]
    linarith only [hMixed]
  have he := normalized_curvature_ge hr hhi hT m w hm hw
    ((9 / 4) * ((M * W + W * M) * L).trace.re)
    (-(9 / 4) * (W ^ 2 * gain r M).trace.re)
    ((9 / 4) * (A * loss r).trace.re + 6 * alpha r * (A * logImbalance r).trace.re)
    (6 * alpha r * (W * M * W * logImbalance r).trace.re)
    traceCurvature (6 * (1 + Real.log T) * q + 9 * (M ^ 2 * W).trace.re ^ 2 / T)
    hmixed' (by rw [hv]; exact neg_gain_trace_ge hr hhi hMhi hW)
    (by rw [hq]; exact combined_loss_trace_ge hr hhi hM.posSemidef hlo hMhi hW)
    (by rw [hq]; exact log_middle_ge hr hhi hM.posSemidef hW) ht hmass
  rw [hv, hq] at he
  have henergy : (W ^ 2 * (loss r * M + M * loss r - gain r M)).trace.re =
      (A * loss r).trace.re - (W ^ 2 * gain r M).trace.re := by
    simp only [mul_sub, mul_add, Matrix.trace_sub, Matrix.trace_add, Complex.sub_re,
      Complex.add_re, A, add_mul]
    rw [Matrix.trace_mul_cycle' (W ^ 2) (loss r) M]
    simp only [Matrix.mul_assoc]
  have hc : (M * W ^ 2 + W * M * W + W ^ 2 * M).trace.re = 3 * q := by
    have hcycle : (W * M * W).trace = (M * W ^ 2).trace := by
      rw [Matrix.trace_mul_comm (W * M) W, ← Matrix.mul_assoc, ← pow_two, Matrix.trace_mul_comm]
    rw [Matrix.trace_add, Matrix.trace_add, Complex.add_re, Complex.add_re, hcycle,
      Matrix.trace_mul_comm (W ^ 2) M]
    ring
  have href : ((M * W ^ 2 + W * M * W + W ^ 2 * M) *
      cfc Real.log (WuCubicOperatorBridge.D r)).trace.re =
      9 * logCenter r * q + 3 * (A * logImbalance r).trace.re +
        3 * (W * M * W * logImbalance r).trace.re := by
    rw [log_density_eq hr, mul_add, mul_smul_comm, mul_one, mul_smul_comm,
      Matrix.trace_add, Complex.add_re, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul,
      show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num, Matrix.trace_smul, smul_eq_mul,
      Complex.re_ofReal_mul, hc]
    simp only [A, add_mul, Matrix.trace_add, Complex.add_re]
    ring
  rw [embedded_generator_eq hr M, Matrix.trace_add, Complex.add_re, henergy, href]
  dsimp only [A, L, q, T, v] at he ⊢
  linarith only [he]

open private generator_affine cubeVariation trace_cubeVariation from
  D5.S3.Quantum.Semigroups.WuCubicHotInnerPartialTrace

private theorem affine_hasDerivAt (M W : Mat) (t : ℝ) :
    HasDerivAt (fun s : ℝ => M + s • W) W t := by
  simpa using ((hasDerivAt_id t).smul_const W).const_add M

private theorem reTrace_hasDerivAt {F : ℝ → Mat} {V : Mat} {t : ℝ}
    (hF : HasDerivAt F V t) : HasDerivAt (fun s => (F s).trace.re) V.trace.re t := by
  let T : Mat →L[ℝ] ℝ :=
    Complex.reCLM.comp (Matrix.traceLinearMap Occupation ℝ ℂ).toContinuousLinearMap
  exact T.hasFDerivAt.comp_hasDerivAt t hF

def embeddedGenerator (r : ℝ) (M : Mat) : Mat :=
  G r * generator r (GInv r * M * GInv r) * G r

private theorem embedded_generator_affine (r : ℝ) (M W : Mat) (t : ℝ) :
    embeddedGenerator r (M + t • W) =
      embeddedGenerator r M + t • embeddedGenerator r W := by
  simp only [embeddedGenerator, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    generator_affine]

private theorem embedded_energy_hasDerivAt (r : ℝ) (M W : Mat) (t : ℝ) :
    let A := M + t • W
    let C := embeddedGenerator r W
    HasDerivAt (fun s : ℝ => (9 / 8 : ℝ) *
      ((M + s • W) ^ 2 * embeddedGenerator r (M + s • W)).trace.re)
      ((9 / 8 : ℝ) * (((W * A + A * W) * embeddedGenerator r A + A ^ 2 * C).trace.re)) t := by
  dsimp only
  have hA := affine_hasDerivAt M W t
  have hC := affine_hasDerivAt (embeddedGenerator r M) (embeddedGenerator r W) t
  have h := (reTrace_hasDerivAt ((hA.fun_mul hA).fun_mul hC)).const_mul (9 / 8 : ℝ)
  simpa only [embedded_generator_affine, pow_two] using h

/-- Exact second derivative of the embedded physical energy along a Hermitian affine
line. This part of the curvature is purely polynomial. -/
theorem energy_second_hasDerivAt (r : ℝ) (M W : Mat) :
    HasDerivAt (deriv (fun s : ℝ => (9 / 8 : ℝ) *
      ((M + s • W) ^ 2 * embeddedGenerator r (M + s • W)).trace.re))
      ((9 / 4 : ℝ) * (W ^ 2 * embeddedGenerator r M +
        (M * W + W * M) * embeddedGenerator r W).trace.re) 0 := by
  let A := fun s : ℝ => M + s • W
  let C := embeddedGenerator r W
  let N := embeddedGenerator r M
  let B := fun s : ℝ => N + s • C
  have hA := affine_hasDerivAt M W 0
  have hB := affine_hasDerivAt N C 0
  have hfirst (s : ℝ) : deriv (fun s : ℝ => (9 / 8 : ℝ) *
      ((M + s • W) ^ 2 * embeddedGenerator r (M + s • W)).trace.re) s =
      (9 / 8 : ℝ) * (((W * A s + A s * W) * B s + A s ^ 2 * C).trace.re) := by
    rw [(embedded_energy_hasDerivAt r M W s).deriv, embedded_generator_affine]
  have h := (reTrace_hasDerivAt (((hA.const_mul W).add (hA.mul_const W)).fun_mul hB |>.add
    ((hA.fun_mul hA).mul_const C))).const_mul (9 / 8 : ℝ)
  have hh : (W * W + W * W) * N + (W * M + M * W) * C + (W * M + M * W) * C =
      (2 : ℝ) • (W ^ 2 * N + (M * W + W * M) * C) := by
    rw [two_smul]
    noncomm_ring
  simp only [Pi.add_apply, zero_smul, add_zero, hh, Matrix.trace_smul,
    Complex.smul_re, smul_eq_mul] at h
  apply (h.congr_deriv (by ring)).congr_of_eventuallyEq
  exact Eventually.of_forall fun s => by simpa only [A, B, pow_two] using hfirst s

private theorem cubic_mass_hasDerivAt (M W : Mat) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ((M + s • W) ^ 3).trace.re)
      (3 * (((M + t • W) ^ 2 * W).trace.re)) t := by
  let A := M + t • W
  have hA := affine_hasDerivAt M W t
  have h := reTrace_hasDerivAt ((hA.fun_mul hA).fun_mul hA)
  have htrace : (((W * A + A * W) * A + A * A * W).trace.re) =
      3 * (A ^ 2 * W).trace.re := by
    rw [show ((W * A + A * W) * A + A * A * W) = cubeVariation A W by
      rw [cubeVariation, pow_two], show (3 : ℝ) * (A ^ 2 * W).trace.re =
        (3 : ℝ) * (W * A ^ 2).trace.re by rw [Matrix.trace_mul_comm]]
    rw [show (cubeVariation A W).trace =
        (W * (A ^ 2 + A * A + A ^ 2)).trace by
      simpa only [mul_one, one_mul] using (trace_cubeVariation A W (1 : Mat))]
    simp only [mul_add, Matrix.trace_add, Complex.add_re, ← pow_two]
    ring
  simpa only [A, pow_succ, pow_zero, one_mul, htrace] using h

/-- Exact second variation of the cubic mass, obtained by differentiating the trace
polynomial and using cyclicity. -/
theorem mass_second_hasDerivAt (M W : Mat) :
    HasDerivAt (deriv (fun s : ℝ => ((M + s • W) ^ 3).trace.re))
      (6 * (M * W ^ 2).trace.re) 0 := by
  have hA := affine_hasDerivAt M W 0
  have h := (reTrace_hasDerivAt ((hA.fun_mul hA).mul_const W)).const_mul 3
  have htrace : (((W * M + M * W) * W).trace.re) = 2 * (M * W ^ 2).trace.re := by
    rw [add_mul, Matrix.trace_add, Complex.add_re,
      Matrix.trace_mul_comm (W * M) W, ← mul_assoc, ← pow_two, Matrix.trace_mul_comm (W ^ 2) M,
      mul_assoc, ← pow_two]
    ring
  simp only [zero_smul, add_zero, htrace] at h
  apply (h.congr_deriv (by ring)).congr_of_eventuallyEq
  exact Eventually.of_forall fun s => by simpa only [pow_two] using (cubic_mass_hasDerivAt M W s).deriv

/-- For a positive mass the logarithmic normalization contributes the claimed
second derivative, including the nonnegative square of its first variation. -/
theorem mass_log_second_hasDerivAt (M W : Mat) (hT : 0 < (M ^ 3).trace.re) :
    HasDerivAt (deriv (fun s : ℝ => ((M + s • W) ^ 3).trace.re *
      Real.log ((M + s • W) ^ 3).trace.re))
      (6 * (1 + Real.log (M ^ 3).trace.re) * (M * W ^ 2).trace.re +
        9 * (M ^ 2 * W).trace.re ^ 2 / (M ^ 3).trace.re) 0 := by
  let T := fun s : ℝ => ((M + s • W) ^ 3).trace.re
  let dT := fun s : ℝ => 3 * ((M + s • W) ^ 2 * W).trace.re
  have hT0 : 0 < T 0 := by simpa [T] using hT
  have hT' : HasDerivAt T (dT 0) 0 := cubic_mass_hasDerivAt M W 0
  have hdT' : HasDerivAt dT (6 * (M * W ^ 2).trace.re) 0 := by
    apply (mass_second_hasDerivAt M W).congr_of_eventuallyEq
    exact Eventually.of_forall (fun s => (cubic_mass_hasDerivAt M W s).deriv.symm)
  have hlog := (Real.hasDerivAt_log hT0.ne').comp 0 hT'
  have h := ((hlog.const_add 1).fun_mul hdT')
  have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < T s :=
    hT'.continuousAt.eventually (lt_mem_nhds hT0)
  have hfirst : deriv (fun s => T s * Real.log (T s)) =ᶠ[𝓝 0]
      fun s => (1 + Real.log (T s)) * dT s := by
    filter_upwards [hnear] with s hs
    have hd : HasDerivAt T (dT s) s := cubic_mass_hasDerivAt M W s
    have hh := hd.fun_mul ((Real.hasDerivAt_log hs.ne').comp s hd)
    have hh' : HasDerivAt (fun s => T s * Real.log (T s))
        (dT s * Real.log (T s) + T s * ((T s)⁻¹ * dT s)) s := hh
    rw [hh'.deriv]
    change dT s * Real.log (T s) + T s * ((T s)⁻¹ * dT s) = _
    rw [← mul_assoc (T s), mul_inv_cancel₀ hs.ne', one_mul]
    ring
  have he : (T 0)⁻¹ * dT 0 * dT 0 + (1 + Real.log (T 0)) *
      (6 * (M * W ^ 2).trace.re) =
      6 * (1 + Real.log (M ^ 3).trace.re) * (M * W ^ 2).trace.re +
        9 * (M ^ 2 * W).trace.re ^ 2 / (M ^ 3).trace.re := by
    simp only [T, dT, zero_smul, add_zero, div_eq_mul_inv]
    ring
  have h' := h.congr_deriv he
  exact h'.congr_of_eventuallyEq hfirst

private theorem reference_hasDerivAt (M W K : Mat) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ((M + s • W) ^ 3 * K).trace.re)
      (cubeVariation (M + t • W) W * K).trace.re t := by
  have hA := affine_hasDerivAt M W t
  have h := reTrace_hasDerivAt (((hA.fun_mul hA).fun_mul hA).mul_const K)
  simpa only [cubeVariation, pow_succ, pow_zero, one_mul] using h

/-- Exact second derivative of the cubic reference term with the fixed Gibbs logarithm. -/
theorem reference_second_hasDerivAt (M W K : Mat) :
    HasDerivAt (deriv (fun s : ℝ => ((M + s • W) ^ 3 * K).trace.re))
      (2 * ((M * W ^ 2 + W * M * W + W ^ 2 * M) * K).trace.re) 0 := by
  have hA := affine_hasDerivAt M W 0
  have hV := (((hA.const_mul W).add (hA.mul_const W)).fun_mul hA).add
    ((hA.fun_mul hA).mul_const W)
  have h := reTrace_hasDerivAt (hV.mul_const K)
  simp only [Pi.add_apply, zero_smul, add_zero] at h
  have he : ((W * W + W * W) * M + (W * M + M * W) * W +
      (W * M + M * W) * W) * K =
      (2 : ℝ) • ((M * W ^ 2 + W * M * W + W ^ 2 * M) * K) := by
    rw [two_smul]
    noncomm_ring
  rw [he, Matrix.trace_smul, Complex.smul_re, smul_eq_mul] at h
  apply h.congr_of_eventuallyEq
  exact Eventually.of_forall fun s => by
    simpa only [cubeVariation, pow_two] using (reference_hasDerivAt M W K s).deriv

/-- The normalized trace constraint implies the cubic mass floor used in the
scalar entropy coefficient. Jensen's tangent inequality is exact at two thirds. -/
theorem cubic_mass_ge {M : Mat} (hM : M.PosDef)
    (htrace : 3 ≤ M.trace.re)
    (hmax : ∃ i, hM.isHermitian.eigenvalues i = 1) :
    17 / 9 ≤ (M ^ 3).trace.re := by
  let m := hM.isHermitian.eigenvalues
  have htr : 3 ≤ ∑ i : Occupation, m i := by
    have ht := RHLinalg.rtrace_eq_sum_eigenvalues hM.isHermitian
    change M.trace.re = ∑ i : Occupation, m i at ht
    rw [← ht]
    exact htrace
  have hpow : (M ^ 3).trace.re = ∑ i : Occupation, (m i) ^ 3 := by
    conv_lhs => rw [hM.isHermitian.spectral_theorem]
    rw [← map_pow, Unitary.conjStarAlgAut_apply,
      Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul,
      Matrix.diagonal_pow, Matrix.trace_diagonal, Complex.re_sum]
    simp [m, ← Complex.ofReal_pow]
  rw [hpow]
  have hjensen (i : Occupation) : 4 / 3 * m i - 16 / 27 ≤ (m i) ^ 3 := by
    have hm : 0 ≤ m i := hM.posSemidef.eigenvalues_nonneg i
    nlinarith [mul_nonneg (sq_nonneg (m i - 2 / 3)) (show 0 ≤ m i + 4 / 3 by linarith)]
  obtain ⟨⟨j,k⟩, hj⟩ := hmax
  change m (j,k) = 1 at hj
  norm_num [Fintype.sum_prod_type, Fin.sum_univ_two] at htr ⊢
  fin_cases j <;> fin_cases k
  · change m (0,0) = 1 at hj
    rw [hj] at htr ⊢
    norm_num at htr ⊢
    linarith only [htr, hjensen (0,1), hjensen (1,0), hjensen (1,1)]
  · change m (0,1) = 1 at hj
    rw [hj] at htr ⊢
    norm_num at htr ⊢
    linarith only [htr, hjensen (0,0), hjensen (1,0), hjensen (1,1)]
  · change m (1,0) = 1 at hj
    rw [hj] at htr ⊢
    norm_num at htr ⊢
    linarith only [htr, hjensen (0,0), hjensen (0,1), hjensen (1,1)]
  · change m (1,1) = 1 at hj
    rw [hj] at htr ⊢
    norm_num at htr ⊢
    linarith only [htr, hjensen (0,0), hjensen (0,1), hjensen (1,0)]

open WuCubicOperatorNormalization (operatorDeficit)
open private G_mul_GInv GInv_mul_G from D5.S3.Quantum.Semigroups.WuCubicOperatorBridge
open private eventually_posDef from D5.S3.Quantum.Divergence.TraceEntropyCalculus

/-- The actual normalized Wu operator deficit along an embedded affine line has
the lower second derivative once the mixed-generator inequality and the
noncommuting trace-entropy second variation are supplied. -/
theorem operatorDeficit_second_of_traceCurvature {r : ℝ} (hr : 1 ≤ r) (hhi : r ≤ 6 / 5)
    (M W : Mat) (hM : M.PosDef) (hW : W.IsHermitian)
    (hlo : ((5 / 9 : ℝ) : ℂ) • (1 : Mat) ≤ M) (hMhi : M ≤ 1)
    (hm : ∀ i, hM.isHermitian.eigenvalues i ∈ Icc (5 / 9 : ℝ) 1)
    (htrace : 3 ≤ M.trace.re) (hmax : ∃ i, hM.isHermitian.eigenvalues i = 1)
    (traceCurvature : ℝ)
    (hTraceD : HasDerivAt (deriv (fun s : ℝ =>
      ((M + s • W) ^ 3 * cfc Real.log ((M + s • W) ^ 3)).trace.re)) traceCurvature 0)
    (hTrace : traceCurvature ≤
      (W ^ 2 * cfc (fun x : ℝ => 15 * x + 18 * x * Real.log x) M).trace.re)
    (hMixed : (15 / 4 : ℝ) * (M * W ^ 2).trace.re ≤
      ((M * W + W * M) * embeddedGenerator r W).trace.re) :
    ∃ c : ℝ, (1 / 5 : ℝ) * (W ^ 2).trace.re ≤ c ∧
      HasDerivAt (deriv (fun s : ℝ => operatorDeficit r (GInv r * (M + s • W) * GInv r))) c 0 := by
  let A := fun s : ℝ => M + s • W
  let E := fun s : ℝ => (9 / 8 : ℝ) * ((A s) ^ 2 * embeddedGenerator r (A s)).trace.re
  let F := fun s : ℝ => ((A s) ^ 3 * cfc Real.log ((A s) ^ 3)).trace.re
  let R := fun s : ℝ => ((A s) ^ 3 * cfc Real.log (WuCubicOperatorBridge.D r)).trace.re
  let T := fun s : ℝ => ((A s) ^ 3).trace.re
  let Z := fun s : ℝ => T s * Real.log (T s)
  have hA0 : A 0 = M := by simp [A]
  have hAherm (s : ℝ) : (A s).IsHermitian := hM.isHermitian.add (hW.smul (star_trivial s))
  have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), (A s).PosDef :=
    eventually_posDef (affine_hasDerivAt M W 0).continuousAt
      (Eventually.of_forall hAherm) (hA0 ▸ hM)
  have hG (s : ℝ) : G r * (GInv r * A s * GInv r) * G r = A s := by
    rw [show G r * (GInv r * A s * GInv r) * G r =
      (G r * GInv r) * A s * (GInv r * G r) by noncomm_ring,
      G_mul_GInv hr, GInv_mul_G hr, one_mul, mul_one]
  have hsource (s : ℝ) : operatorDeficit r (GInv r * A s * GInv r) =
      E s - alpha r * F s + alpha r * R s + alpha r * Z s := by
    unfold operatorDeficit
    dsimp only
    rw [hG s]
    simp only [E, F, R, Z, T, embeddedGenerator, mul_sub, Matrix.trace_sub, Complex.sub_re]
    ring
  have hTbound := cubic_mass_ge hM htrace hmax
  have hTpos : 0 < (M ^ 3).trace.re := by linarith
  have hE := energy_second_hasDerivAt r M W
  have hR := reference_second_hasDerivAt M W (cfc Real.log (WuCubicOperatorBridge.D r))
  have hZ := mass_log_second_hasDerivAt M W hTpos
  have hD := ((hE.sub (hTraceD.const_mul (alpha r))).add (hR.const_mul (alpha r))).add
    (hZ.const_mul (alpha r))
  refine ⟨_, physical_curvature_ge hr hhi M W hM hW hlo hMhi hm hTbound
    traceCurvature hTrace hMixed, ?_⟩
  apply (hD.congr_deriv (by unfold embeddedGenerator; ring)).congr_of_eventuallyEq
  filter_upwards [hnear] with s hs
  have hc : ((A s) ^ 3).PosDef :=
    (((hs.posSemidef.pow 3).posDef_iff_isUnit).mpr (hs.isUnit.pow 3))
  have hP := (affine_hasDerivAt M W s)
  have hPow : HasDerivAt (fun s => A s ^ 3) (cubeVariation (A s) W) s := by
    simpa only [A, cubeVariation, pow_succ, pow_zero, one_mul] using (hP.fun_mul hP).fun_mul hP
  have hF := D5.S3.Quantum.Divergence.TraceEntropyCalculus.hasDerivAt_trace_mul_log
    (fun s => (A s) ^ 3) (cubeVariation (A s) W) s hPow
    (Eventually.of_forall fun s => (hAherm s).pow 3) hc
  have hEd : DifferentiableAt ℝ E s := (embedded_energy_hasDerivAt r M W s).differentiableAt
  have hFd : DifferentiableAt ℝ F s := hF.differentiableAt
  have hRd : DifferentiableAt ℝ R s :=
    (reference_hasDerivAt M W (cfc Real.log (WuCubicOperatorBridge.D r)) s).differentiableAt
  have hTd : DifferentiableAt ℝ T s := (cubic_mass_hasDerivAt M W s).differentiableAt
  have hmasspos : 0 < T s := (Complex.lt_def.mp hc.trace_pos).1
  have hZd : DifferentiableAt ℝ Z s :=
    hTd.mul ((Real.differentiableAt_log hmasspos.ne').comp s hTd)
  have heq : (fun s => operatorDeficit r (GInv r * A s * GInv r)) =
      fun s => E s - alpha r * F s + alpha r * R s + alpha r * Z s := funext hsource
  have h1 := hEd.sub (hFd.const_mul (alpha r))
  have h2 := h1.add (hRd.const_mul (alpha r))
  change deriv (fun s => operatorDeficit r (GInv r * A s * GInv r)) s =
    deriv E s - alpha r * deriv F s + alpha r * deriv R s + alpha r * deriv Z s
  rw [heq]
  change deriv (((E - fun y => alpha r * F y) + fun y => alpha r * R y) +
      fun y => alpha r * Z y) s = _
  rw [deriv_add h2 (hZd.const_mul (alpha r))]
  change deriv ((E - fun y => alpha r * F y) + fun y => alpha r * R y) s +
      deriv (fun y => alpha r * Z y) s = _
  rw [deriv_add h1 (hRd.const_mul (alpha r))]
  change deriv (E - fun y => alpha r * F y) s + deriv (fun y => alpha r * R y) s +
      deriv (fun y => alpha r * Z y) s = _
  rw [deriv_sub hEd (hFd.const_mul (alpha r))]
  simp only [deriv_const_mul_field]

open WuCubicTranslationEnergy (sandwich pairWeight baseEntry)
open private baseEntry_pos vPairing_entries from
  D5.S3.Quantum.Semigroups.WuCubicTranslationEnergy

private theorem pairWeight_pos {r : ℝ} (hr : 1 ≤ r) (i j : Occupation) :
    0 < pairWeight r i j := by
  unfold pairWeight
  have hi := baseEntry_pos hr i
  have hj := baseEntry_pos hr j
  positivity

private theorem vPairing_cauchy {r : ℝ} (hr : 1 ≤ r) (X Y : Mat) :
    (vPairing r X Y).re ^ 2 ≤ (vPairing r X X).re * (vPairing r Y Y).re := by
  let V (A : Mat) : EuclideanSpace ℂ (Occupation × Occupation) :=
    WithLp.toLp 2 (fun ij => (Real.sqrt (pairWeight r ij.1 ij.2) : ℂ) * A ij.1 ij.2)
  have hpair (A B : Mat) : inner ℂ (V A) (V B) = vPairing r A B := by
    rw [vPairing_entries, PiLp.inner_apply, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [V, RCLike.inner_apply, map_mul,
      Complex.conj_ofReal]
    have h := Real.sq_sqrt (pairWeight_pos hr i j).le
    have hh : (Real.sqrt (pairWeight r i j) : ℂ) ^ 2 = (pairWeight r i j : ℂ) := by
      exact_mod_cast h
    calc
      _ = (Real.sqrt (pairWeight r i j) : ℂ) ^ 2 * (conj (A i j) * B i j) := by ring
      _ = _ := by rw [hh]
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ) (V X) (V Y)) 2
  rw [hpair X Y, mul_pow, norm_sq_eq_re_inner (𝕜 := ℂ) (V X),
    norm_sq_eq_re_inner (𝕜 := ℂ) (V Y), hpair X X, hpair Y Y] at h
  have hh := pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm (vPairing r X Y)) 2
  rw [sq_abs] at hh
  exact hh.trans h

/-- The direction representing the physical anticommutator functional in the
existing Gibbs-weighted variance pairing. -/
def mixedDual (r : ℝ) (M H : Mat) : Mat :=
  let W := sandwich r H
  let A := G r * (M * W + W * M) * G r
  fun i j => conj (A j i) / ((2 * pairWeight r i j : ℝ) : ℂ)

theorem mixedDual_pairing {r : ℝ} (hr : 1 ≤ r) (M H Y : Mat) :
    vPairing r (mixedDual r M H) Y =
      (1 / 2 : ℂ) * ((M * sandwich r H + sandwich r H * M) * sandwich r Y).trace := by
  let W := sandwich r H
  let Q := G r * (M * W + W * M) * G r
  have htrace : (Q * Y).trace = ((M * W + W * M) * sandwich r Y).trace := by
    dsimp only [Q, sandwich]
    rw [show G r * (M * W + W * M) * G r * Y =
      G r * ((M * W + W * M) * G r * Y) by noncomm_ring,
      Matrix.trace_mul_comm (G r)]
    congr 1
    noncomm_ring
  rw [← htrace, vPairing_entries, Matrix.trace_mul_comm Q Y]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  change (pairWeight r i j : ℂ) *
      (conj (conj (Q j i) / ((2 * pairWeight r i j : ℝ) : ℂ)) * Y i j) =
      (1 / 2 : ℂ) * (Y i j * Q j i)
  simp only [map_div₀, Complex.conj_conj, Complex.ofReal_mul,
    Complex.ofReal_ofNat, map_mul, Complex.conj_ofReal, map_ofNat]
  have hn : (pairWeight r i j : ℂ) ≠ 0 := by exact_mod_cast (pairWeight_pos hr i j).ne'
  field_simp [hn]

/-- The degree-two contraction proves the mixed-generator estimate once the
relative Kantorovich moment bound for the physical dual direction is available. -/
theorem mixed_energy_ge_of_dual_moment {r : ℝ} (hr : 1 ≤ r)
    (M H : Mat) (hM : M.PosSemidef) (hW : (sandwich r H).IsHermitian)
    (hdeg : ∀ k : Index, degree k < 2 → coefficient r H k = 0)
    (hMoment : (vPairing r (mixedDual r M H) (mixedDual r M H)).re *
      (vPairing r H H).re ≤ ((9 / 8 : ℝ) * (M * (sandwich r H) ^ 2).trace.re) ^ 2) :
    (15 / 4 : ℝ) * (M * (sandwich r H) ^ 2).trace.re ≤
      ((M * sandwich r H + sandwich r H * M) *
        embeddedGenerator r (sandwich r H)).trace.re := by
  let W := sandwich r H
  let U := mixedDual r M H
  let Z := generator r H - (3 : ℂ) • H
  let q := (M * W ^ 2).trace.re
  have hq : 0 ≤ q := RHLinalg.trace_mul_nonneg_of_posSemidef hM (square_psd hW)
  have hU : 0 ≤ (vPairing r U U).re := by
    rw [show (vPairing r U U).re = ∑ k : Index, vWeight r U k by
      simpa only [one_mul] using vPairing_re_of_coeff hr U U (fun _ => 1) (by simp)]
    exact Finset.sum_nonneg fun k _ => vWeight_nonneg hr U k
  have hc := (vPairing_cauchy hr U Z).trans
    ((mul_le_mul_of_nonneg_left (degree_contraction hr H hdeg) hU).trans hMoment)
  have habs : |(vPairing r U Z).re| ≤ (9 / 8 : ℝ) * q := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    simpa only [sq_abs] using hc
  have hlow := (abs_le.mp habs).1
  have hL : embeddedGenerator r W = sandwich r (generator r H) := by
    have he : GInv r * W * GInv r = H := by
      dsimp only [W, sandwich]
      rw [show GInv r * (G r * H * G r) * GInv r =
        (GInv r * G r) * H * (G r * GInv r) by noncomm_ring,
        GInv_mul_G hr, G_mul_GInv hr, one_mul, mul_one]
    rw [embeddedGenerator, he]
    rfl
  have hz : sandwich r Z = embeddedGenerator r W - (3 : ℂ) • W := by
    simp only [Z, sandwich, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
    rw [hL]
    rfl
  have hpair := mixedDual_pairing hr M H Z
  change vPairing r U Z = (1 / 2 : ℂ) * ((M * W + W * M) * sandwich r Z).trace at hpair
  rw [hz] at hpair
  have hhalf := congrArg Complex.re hpair
  have htrace : ((M * W + W * M) * W).trace.re = 2 * q := by
    rw [add_mul, Matrix.trace_add, Complex.add_re, Matrix.trace_mul_comm (W * M) W,
      ← mul_assoc, ← pow_two, Matrix.trace_mul_comm (W ^ 2) M, mul_assoc, ← pow_two]
    ring
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul,
    mul_sub, mul_smul_comm, Matrix.trace_sub, Complex.sub_re, Matrix.trace_smul,
    show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num, smul_eq_mul, Complex.re_ofReal_mul,
    htrace] at hhalf
  change (15 / 4 : ℝ) * q ≤ ((M * W + W * M) * embeddedGenerator r W).trace.re
  linarith only [hlow, hhalf]

end D5.S3.Quantum.Semigroups.WuCubicConditionedHessian
