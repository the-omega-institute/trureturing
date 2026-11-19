/- GID: D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorEndpointSigns
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/OpenBoundaryMPSInteriorEndpointSigns
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.Analysis.Normed.Module.FiniteDimension]
   utility: none
   digest: Operator norm endpoint limits give native annular residual signs. -/

import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorRootRealization
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! Native complex-linear operator limits and strict real residual endpoint signs. -/

set_option autoImplicit false
noncomputable section
namespace D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorEndpointSigns

open scoped BigOperators Matrix ComplexOrder _root_.Topology Matrix.Norms.Elementwise
open Matrix Filter Bornology
open PeriodicMPSParentIntersection
open OpenBoundaryMPSInteriorRootRealization

local instance : NormedAddCommGroup Bond := Matrix.normedAddCommGroup
local instance : NormedSpace ℂ Bond := Matrix.normedSpace

local instance : IsNormableSpace ℂ Bond :=
  inferInstanceAs (IsNormableSpace ℂ (Fin 2 → Fin 2 → ℂ))
local instance : ContinuousMul (Bond →L[ℂ] Bond) :=
  inferInstanceAs (ContinuousMul ((Fin 2 → Fin 2 → ℂ) →L[ℂ] (Fin 2 → Fin 2 → ℂ)))

private lemma complex_conj_mul (z : ℂ) : (starRingEnd ℂ) z * z = (Complex.normSq z : ℂ) := by
  rw [mul_comm]
  exact Complex.mul_conj z

private def U (s : Sector) : Bond := !![beta s, -1; 0, 0]
private def V (s : Sector) : Bond := !![0, 0; -alpha s, 1]

/-- The two rank-one inputs after the native diagonal Schur inverse. -/
def Mzero (s : Sector) : Bond :=
  diagonalStarInverse s (vecMulVec (star (![-alpha s, 1] : Fin 2 → ℂ)) ![-alpha s, 1])

def Minf (s : Sector) : Bond :=
  diagonalStarInverse s (vecMulVec (star (![beta s, -1] : Fin 2 → ℂ)) ![beta s, -1])

private def sandwich (s : Sector) (A B : Bond) : Bond →L[ℂ] Bond :=
  LinearMap.toContinuousLinearMap {
    toFun := fun X => diagonalStarInverse s (A * X * B)
    map_add' := by
      intro X Y
      ext i j
      simp [Matrix.mul_add, Matrix.add_mul, diagonalStarInverse, add_div]
    map_smul' := by
      intro t X
      ext i j
      simp [Matrix.mul_smul, Matrix.smul_mul, diagonalStarInverse, mul_div_assoc] }

/-- Complex-linear bundling of exactly the native algebraic inverse dual transfer. -/
def inverseDualOperator (s : Sector) (z : ℂ) : Bond →L[ℂ] Bond :=
  sandwich s ((G s z)⁻¹)ᴴ (G s z)⁻¹

theorem inverse_dual_operator_apply (s : Sector) (z : ℂ) (X : Bond) :
    inverseDualOperator s z X = inverseDualTransfer s z X := rfl

@[simp] private lemma sandwich_apply (s : Sector) (A B X : Bond) :
    sandwich s A B X = diagonalStarInverse s (A * X * B) := rfl

private def atInfinity (s : Sector) (w : ℂ) : Bond →L[ℂ] Bond :=
  ((Complex.normSq (delta s) : ℂ)⁻¹) •
    sandwich s (U s + w • V s)ᴴ (U s + w • V s)

private def atZero (s : Sector) (z : ℂ) : Bond →L[ℂ] Bond :=
  ((Complex.normSq (delta s) : ℂ)⁻¹) •
    (((‖z‖ ^ 2 : ℝ) : ℂ) • sandwich s (U s)ᴴ (U s) +
      star z • sandwich s (U s)ᴴ (V s) +
      z • sandwich s (V s)ᴴ (U s) + sandwich s (V s)ᴴ (V s))

private lemma continuous_atInfinity (s : Sector) : Continuous (atInfinity s) := by
  refine (continuous_clm_apply (𝕜 := ℂ) (E := Bond) (F := Bond)
    (f := atInfinity s)).mpr ?_
  intro X
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  change Continuous (fun w : ℂ => (Complex.normSq (delta s) : ℂ)⁻¹ *
    (((U s + w • V s)ᴴ * X * (U s + w • V s)) i j /
      (1 + star ((![s.lambda, s.mu] : Fin 2 → ℂ) i) *
        (![s.lambda, s.mu] : Fin 2 → ℂ) j)))
  simp only [Matrix.mul_apply, Fin.sum_univ_two, conjTranspose_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  fun_prop

private lemma continuous_atZero (s : Sector) : Continuous (atZero s) := by
  unfold atZero
  fun_prop

private lemma inverse_G {s : Sector} (hs : Regular s) {z : ℂ} (hz : z ≠ 0) :
    (G s z)⁻¹ = (delta s)⁻¹ • (U s + z⁻¹ • V s) := by
  have hd : delta s ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hs.1).1).1
  have hdet : (G s z).det = delta s * z := by
    simp [G, delta, alpha, beta, det_fin_two]
    ring
  rw [Matrix.inv_def, hdet, Ring.inverse_eq_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [G, U, V, adjugate_fin_two, alpha, beta, delta] <;>
    field_simp <;> ring

private lemma native_infinity {s : Sector} (hs : Regular s) {z : ℂ} (hz : z ≠ 0) :
    inverseDualOperator s z = atInfinity s z⁻¹ := by
  ext X i j
  rw [inverse_dual_operator_apply]
  simp only [inverseDualTransfer, sandwich_apply, inverse_G hs hz, atInfinity,
    _root_.smul_apply, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    diagonalStarInverse, Matrix.smul_apply, smul_eq_mul]
  have he : (delta s)⁻¹ * star ((delta s)⁻¹) = (Complex.normSq (delta s) : ℂ)⁻¹ := by
    rw [star_inv₀, ← mul_inv]
    congr 1
    exact Complex.mul_conj _
  calc
    _ = ((delta s)⁻¹ * star ((delta s)⁻¹)) *
        (((U s + z⁻¹ • V s)ᴴ * X * (U s + z⁻¹ • V s)) i j /
          (1 + star ((![s.lambda, s.mu] : Fin 2 → ℂ) i) *
            (![s.lambda, s.mu] : Fin 2 → ℂ) j)) := by ring
    _ = _ := by rw [he]

private lemma native_zero {s : Sector} (hs : Regular s) {z : ℂ} (hz : z ≠ 0) :
    ((‖z‖ ^ 2 : ℝ) : ℂ) • inverseDualOperator s z = atZero s z := by
  rw [native_infinity hs hz]
  ext X i j
  simp only [atInfinity, atZero, _root_.smul_apply, _root_.add_apply, sandwich_apply, diagonalStarInverse,
    conjTranspose_add, conjTranspose_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  have hn : ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := by
    simpa [RCLike.star_def] using (Complex.conj_mul' z).symm
  rw [hn, star_inv₀]
  have hc : star z ≠ 0 := star_ne_zero.mpr hz
  field_simp
  <;> ring

private def entryOperator (s : Sector) (i : Fin 2) (M : Bond) : Bond →L[ℂ] Bond :=
  LinearMap.toContinuousLinearMap {
    toFun := fun X => (X i i * (Complex.normSq (delta s) : ℂ)⁻¹) • M
    map_add' := by intros; simp [add_mul, add_smul]
    map_smul' := by intros; simp [mul_assoc, smul_smul] }

/-- The complex-linear limiting map at punctured zero. -/
def zeroLimitOperator (s : Sector) : Bond →L[ℂ] Bond := entryOperator s 1 (Mzero s)

/-- The complex-linear limiting map at infinity. -/
def infinityLimitOperator (s : Sector) : Bond →L[ℂ] Bond := entryOperator s 0 (Minf s)

@[simp] private lemma entryOperator_apply (s : Sector) (i : Fin 2) (M X : Bond) :
    entryOperator s i M X = (X i i * (Complex.normSq (delta s) : ℂ)⁻¹) • M := rfl

private lemma zero_value (s : Sector) : atZero s 0 = zeroLimitOperator s := by
  ext X i j
  fin_cases i <;> fin_cases j <;>
    simp [atZero, zeroLimitOperator, entryOperator_apply, sandwich_apply, Mzero,
    V, diagonalStarInverse, Matrix.mul_apply, Fin.sum_univ_two, vecMulVec_apply,
    conjTranspose_apply, mul_div_assoc]
  <;> ring

private lemma infinity_value (s : Sector) : atInfinity s 0 = infinityLimitOperator s := by
  ext X i j
  fin_cases i <;> fin_cases j <;>
    simp [atInfinity, infinityLimitOperator, entryOperator_apply, sandwich_apply, Minf,
    U, diagonalStarInverse, Matrix.mul_apply, Fin.sum_univ_two, vecMulVec_apply,
    conjTranspose_apply, mul_div_assoc]
  <;> ring


theorem inverse_dual_operator_zero (s : Sector) (hs : Regular s) :
    Tendsto (fun z : ℂ => ((‖z‖ ^ 2 : ℝ) : ℂ) • inverseDualOperator s z)
      (𝓝[≠] 0) (𝓝 (zeroLimitOperator s)) := by
  rw [← zero_value]
  apply (continuous_atZero s).continuousAt.tendsto.mono_left inf_le_left |>.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (native_zero hs hz).symm

theorem inverse_dual_operator_infinity (s : Sector) (hs : Regular s) :
    Tendsto (inverseDualOperator s) (cobounded ℂ) (𝓝 (infinityLimitOperator s)) := by
  rw [← infinity_value]
  apply ((continuous_atInfinity s).continuousAt.tendsto.comp
    (tendsto_inv₀_cobounded : Tendsto (fun z : ℂ => z⁻¹) (cobounded ℂ) (𝓝 0))).congr'
  filter_upwards [(isBounded_singleton : IsBounded ({0} : Set ℂ))] with z hz
  exact (native_infinity hs (by simpa using hz)).symm

private lemma Mzero_corner (s : Sector) :
    Mzero s 1 1 = ((1 + Complex.normSq s.mu : ℝ) : ℂ)⁻¹ := by
  simp [Mzero, diagonalStarInverse, complex_conj_mul]

private lemma Minf_corner (s : Sector) :
    Minf s 0 0 = (Complex.normSq (beta s) : ℂ) /
      ((1 + Complex.normSq s.lambda : ℝ) : ℂ) := by
  simp [Minf, diagonalStarInverse, complex_conj_mul]

private lemma entryOperator_pow (s : Sector) (i : Fin 2) (M P : Bond) (k : ℕ) :
    (entryOperator s i M ^ (k + 1)) P =
      (P i i * (Complex.normSq (delta s) : ℂ)⁻¹ ^ (k + 1) * (M i i) ^ k) • M := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, entryOperator_apply]
    simp only [Matrix.smul_apply, smul_eq_mul, smul_smul]
    congr 1
    simp only [pow_succ]
    ring

private lemma scaled_native_power (s : Sector) (z t : ℂ) (p : ℕ) (P : Bond) :
    ((t • inverseDualOperator s z) ^ p) P = t ^ p • trialLeft s p P z := by
  rw [smul_pow, _root_.smul_apply]
  congr 1
  rw [FunLike.coe_pow_eq_iterate]
  have he : (inverseDualOperator s z : Bond → Bond) = inverseDualTransfer s z := by
    funext X
    exact inverse_dual_operator_apply s z X
  rw [he]
  rfl

private lemma operator_zero_power (s : Sector) (hs : Regular s) (p : ℕ) :
    Tendsto (fun z : ℂ => (((‖z‖ ^ 2 : ℝ) : ℂ) • inverseDualOperator s z) ^ p)
      (𝓝[≠] 0) (𝓝 (zeroLimitOperator s ^ p)) :=
  (inverse_dual_operator_zero s hs).pow p

private lemma operator_infinity_power (s : Sector) (hs : Regular s) (p : ℕ) :
    Tendsto (fun z : ℂ => inverseDualOperator s z ^ p)
      (cobounded ℂ) (𝓝 (infinityLimitOperator s ^ p)) :=
  (inverse_dual_operator_infinity s hs).pow p

/-- Fixed native left iterates, scaled at punctured zero. -/
theorem trial_left_zero (s : Sector) (hs : Regular s) (p : ℕ) (hp : 1 ≤ p) (P : Bond) :
    Tendsto (fun z : ℂ => ((‖z‖ ^ (2 * p) : ℝ) : ℂ) • trialLeft s p P z)
      (𝓝[≠] 0) (𝓝 ((P 1 1 * (Complex.normSq (delta s) : ℂ)⁻¹ ^ p *
        (((1 + Complex.normSq s.mu : ℝ) : ℂ)⁻¹) ^ (p - 1)) • Mzero s)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  have h := (ContinuousLinearMap.apply ℂ Bond P).continuous.continuousAt.tendsto.comp
    (operator_zero_power s hs (k + 1))
  simp only [Function.comp_def, ContinuousLinearMap.apply_apply, zeroLimitOperator,
    entryOperator_pow, Mzero_corner] at h
  convert h using 1
  · funext z
    rw [scaled_native_power]
    simp only [← Complex.ofReal_pow, ← pow_mul]
  · simp only [Nat.succ_sub_one]

/-- Fixed native left iterates at infinity, with no growth claim. -/
theorem trial_left_infinity (s : Sector) (hs : Regular s) (p : ℕ) (hp : 1 ≤ p) (P : Bond) :
    Tendsto (trialLeft s p P) (cobounded ℂ)
      (𝓝 ((P 0 0 * (Complex.normSq (delta s) : ℂ)⁻¹ ^ p *
        ((Complex.normSq (beta s) : ℂ) / ((1 + Complex.normSq s.lambda : ℝ) : ℂ)) ^
          (p - 1)) • Minf s)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  have h := (ContinuousLinearMap.apply ℂ Bond P).continuous.continuousAt.tendsto.comp
    (operator_infinity_power s hs (k + 1))
  simp only [Function.comp_def, ContinuousLinearMap.apply_apply, infinityLimitOperator,
    entryOperator_pow, Minf_corner] at h
  convert h using 1
  · funext z
    simpa using (scaled_native_power s z 1 (k + 1) P).symm
  · simp only [Nat.succ_sub_one]

private lemma rank_schur_det (s : Sector) (x y : ℂ) :
    (diagonalStarInverse s (vecMulVec (star (![x, y] : Fin 2 → ℂ)) ![x, y])).det =
      ((Complex.normSq x * Complex.normSq y *
        (1 / ((1 + Complex.normSq s.lambda) * (1 + Complex.normSq s.mu)) -
          1 / Complex.normSq (1 + star s.lambda * s.mu)) : ℝ) : ℂ) := by
  have hcross : (1 + star s.lambda * s.mu) * (1 + star s.mu * s.lambda) =
      (Complex.normSq (1 + star s.lambda * s.mu) : ℂ) := by
    rw [← Complex.mul_conj]
    congr 1
    simp [RCLike.star_def, mul_comm]
  calc
    _ = (star x * x) * (star y * y) *
        ((1 + star s.lambda * s.lambda)⁻¹ * (1 + star s.mu * s.mu)⁻¹ -
          (1 + star s.lambda * s.mu)⁻¹ * (1 + star s.mu * s.lambda)⁻¹) := by
      simp [diagonalStarInverse, det_fin_two, vecMulVec_apply, div_eq_mul_inv]
      <;> ring
    _ = _ := by
      rw [← mul_inv, ← mul_inv, hcross]
      simp [complex_conj_mul, Complex.ofReal_add,
        Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_div]

private lemma det_Mzero (s : Sector) :
    (Mzero s).det = ((Complex.normSq (alpha s) *
      (1 / ((1 + Complex.normSq s.lambda) * (1 + Complex.normSq s.mu)) -
        1 / Complex.normSq (1 + star s.lambda * s.mu)) : ℝ) : ℂ) := by
  simpa [Mzero] using rank_schur_det s (-alpha s) 1

private lemma det_Minf (s : Sector) :
    (Minf s).det = ((Complex.normSq (beta s) *
      (1 / ((1 + Complex.normSq s.lambda) * (1 + Complex.normSq s.mu)) -
        1 / Complex.normSq (1 + star s.lambda * s.mu)) : ℝ) : ℂ) := by
  simpa [Minf] using rank_schur_det s (beta s) (-1)

private lemma gram_gap (s : Sector) :
    Complex.normSq (1 + star s.lambda * s.mu) =
      (1 + Complex.normSq s.lambda) * (1 + Complex.normSq s.mu) -
        Complex.normSq (delta s) := by
  simp [Complex.normSq_apply, delta, RCLike.star_def]
  ring

private lemma det_endpoints_negative (s : Sector) (hs : Regular s) :
    (Mzero s).det.re < 0 ∧ (Minf s).det.re < 0 := by
  have hf := mul_ne_zero_iff.mp hs.1
  have hab := mul_ne_zero_iff.mp hf.1
  have hd := Complex.normSq_pos.mpr hab.1
  have ha := Complex.normSq_pos.mpr hab.2
  have hb := Complex.normSq_pos.mpr hf.2
  have hc : Complex.normSq (1 + star s.lambda * s.mu) <
      (1 + Complex.normSq s.lambda) * (1 + Complex.normSq s.mu) := by
    rw [gram_gap]
    linarith
  have hgap := sub_neg.mpr (one_div_lt_one_div_of_lt hs.2 hc)
  rw [det_Mzero, det_Minf]
  simpa only [Complex.ofReal_re] using
    And.intro (mul_neg_of_pos_of_neg ha hgap) (mul_neg_of_pos_of_neg hb hgap)

private lemma positive_diagonal {P : Bond} (hP : P.PosDef) (i : Fin 2) :
    0 < (P i i).re ∧ P i i = ((P i i).re : ℂ) := by
  have h := Complex.pos_iff.mp (hP.diag_pos (i := i))
  refine ⟨h.1, ?_⟩
  apply Complex.ext
  · rfl
  · simpa using h.2.symm

private lemma negative_scaled_det {M : Bond} (hM : M.det.re < 0) {t : ℝ} (ht : 0 < t) :
    (((t : ℂ) • M).det).re < 0 := by
  rw [Matrix.det_smul]
  simpa only [Fintype.card_fin, ← Complex.ofReal_pow, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
      mul_neg_of_pos_of_neg (sq_pos_of_pos ht) hM

private lemma limit_determinants_negative (s : Sector) (hs : Regular s)
    (p : ℕ) (P : Bond) (hP : P.PosDef) :
    (((P 1 1 * (Complex.normSq (delta s) : ℂ)⁻¹ ^ p *
        (((1 + Complex.normSq s.mu : ℝ) : ℂ)⁻¹) ^ (p - 1)) • Mzero s).det).re < 0 ∧
    (((P 0 0 * (Complex.normSq (delta s) : ℂ)⁻¹ ^ p *
        ((Complex.normSq (beta s) : ℂ) / ((1 + Complex.normSq s.lambda : ℝ) : ℂ)) ^
          (p - 1)) • Minf s).det).re < 0 := by
  have hf := mul_ne_zero_iff.mp hs.1
  have hd : 0 < Complex.normSq (delta s) :=
    Complex.normSq_pos.mpr (mul_ne_zero_iff.mp hf.1).1
  have hb : 0 < Complex.normSq (beta s) := Complex.normSq_pos.mpr hf.2
  have ha0 : 0 < 1 + Complex.normSq s.lambda := by
    linarith [Complex.normSq_nonneg s.lambda]
  have ha1 : 0 < 1 + Complex.normSq s.mu := by
    linarith [Complex.normSq_nonneg s.mu]
  have h00 := positive_diagonal hP 0
  have h11 := positive_diagonal hP 1
  rw [h00.2, h11.2]
  constructor
  · convert negative_scaled_det (det_endpoints_negative s hs).1
      (mul_pos (mul_pos h11.1 (pow_pos (inv_pos.mpr hd) p))
        (pow_pos (inv_pos.mpr ha1) (p - 1))) using 1 <;> push_cast <;> rfl
  · convert negative_scaled_det (det_endpoints_negative s hs).2
      (mul_pos (mul_pos h00.1 (pow_pos (inv_pos.mpr hd) p))
        (pow_pos (div_pos hb ha0) (p - 1))) using 1 <;> push_cast <;> rfl

private lemma eventually_zero_negative (s : Sector) (hs : Regular s)
    (p : ℕ) (hp : 1 ≤ p) (P : Bond) (hP : P.PosDef) :
    ∀ᶠ z : ℂ in 𝓝[≠] 0, (trialLeft s p P z).det.re < 0 := by
  have hc : Continuous (fun X : Bond => X.det.re) := by fun_prop
  have h := (hc.continuousAt.tendsto.comp (trial_left_zero s hs p hp P)).eventually
    (gt_mem_nhds (limit_determinants_negative s hs p P hP).1)
  filter_upwards [h, self_mem_nhdsWithin] with z hz hnz
  have hpos : 0 < ‖z‖ ^ (2 * p) := pow_pos (norm_pos_iff.mpr hnz) _
  change (((((‖z‖ ^ (2 * p) : ℝ) : ℂ) • trialLeft s p P z).det).re < 0) at hz
  rw [Matrix.det_smul] at hz
  have he : ((↑(‖z‖ ^ (2 * p)) ^ Fintype.card (Fin 2) *
      (trialLeft s p P z).det) : ℂ).re =
        (‖z‖ ^ (2 * p)) ^ 2 * (trialLeft s p P z).det.re := by
    simp only [Fintype.card_fin, ← Complex.ofReal_pow, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [he] at hz
  by_contra hn
  have := mul_nonneg (sq_pos_of_pos hpos).le (le_of_not_gt hn)
  linarith

private lemma eventually_infinity_negative (s : Sector) (hs : Regular s)
    (p : ℕ) (hp : 1 ≤ p) (P : Bond) (hP : P.PosDef) :
    ∀ᶠ z : ℂ in cobounded ℂ, (trialLeft s p P z).det.re < 0 := by
  have hc : Continuous (fun X : Bond => X.det.re) := by fun_prop
  exact (hc.continuousAt.tendsto.comp (trial_left_infinity s hs p hp P)).eventually
    (gt_mem_nhds (limit_determinants_negative s hs p P hP).2)

/-- Both entire circles have a strictly negative native real residual component;
q and H are arbitrary and the two radii enclose the prescribed nonzero point. -/
theorem annular_residual_negative (s : Sector) (hs : Regular s) (p : ℕ) (hp : 1 ≤ p)
    (P : Bond) (hP : P.PosDef) (z₀ : ℂ) (hz₀ : z₀ ≠ 0) :
    ∃ ε R : ℝ, 0 < ε ∧ ε < ‖z₀‖ ∧ ‖z₀‖ < R ∧
      ∀ (q : ℕ) (H : Bond) (z : ℂ), ‖z‖ = ε ∨ ‖z‖ = R →
        (residual s p q P H z).re < 0 := by
  obtain ⟨r, hr, hsmall⟩ := Metric.mem_nhdsWithin_iff.mp
    (eventually_zero_negative s hs p hp P hP)
  obtain ⟨b, _, hlarge⟩ := (Metric.hasBasis_cobounded_compl_closedBall (0 : ℂ)).mem_iff.mp
    (eventually_infinity_negative s hs p hp P hP)
  have hzpos := norm_pos_iff.mpr hz₀
  let ε := min (r / 2) (‖z₀‖ / 2)
  let R := max (b + 1) (‖z₀‖ + 1)
  have hepos : 0 < ε := lt_min (by linarith) (by linarith)
  have her : ε < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hez : ε < ‖z₀‖ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hRz : ‖z₀‖ < R := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hRb : b < R := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  refine ⟨ε, R, hepos, hez, hRz, ?_⟩
  intro q H z hz
  have hdet : (trialLeft s p P z).det.re < 0 := by
    rcases hz with hz | hz
    · apply hsmall
      constructor
      · simpa [Metric.mem_ball, hz] using her
      · change z ≠ 0
        intro he
        rw [he, norm_zero] at hz
        linarith
    · apply hlarge
      simpa [Metric.mem_closedBall, hz, not_le] using hRb
  simpa [OpenBoundaryMPSInteriorRootRealization.residual] using hdet

#print axioms inverse_dual_operator_apply
#print axioms inverse_dual_operator_zero
#print axioms inverse_dual_operator_infinity
#print axioms trial_left_zero
#print axioms trial_left_infinity
#print axioms annular_residual_negative

end D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorEndpointSigns
