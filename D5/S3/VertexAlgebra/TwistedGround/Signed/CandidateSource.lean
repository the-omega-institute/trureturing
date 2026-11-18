/- GID: D5/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Signed/CandidateSource
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed Gaussian sources, normalized roots and spatial T equation. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalAnalyticCandidate
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalEquations
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology
namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalSignedCandidate
open OriginalGaussianExternalGenerators OriginalGaussianExternalGeneratedSource
open OriginalGaussianExternalModeSums OriginalGaussianExternalJetSums
open D5.S3.Analytic.OriginalHalfBinomialPeriod

open OriginalGaussianExternalAnalyticCandidate (b ell correction)

def h (e : Bool) (u r : ℂ) : ℂ :=
  if e then 1 - (1 - r) * u else 1 - r - u

def W (e : Bool) (u r : ℂ) : ℂ := h e u r * sourceMode e u r

def rho (e f : Bool) (u v : ℂ) : ℂ :=
  if e = f then u + v else -(1 + u * v)

-- E=d-r*K is exactly the four-entry table; no inverted source chart occurs.
def K (e f : Bool) (u v : ℂ) : ℂ :=
  if e then (if f then u * v else -u) else (if f then -v else 1)
def E (e f : Bool) (u v r : ℂ) : ℂ := b u * b v - r * K e f u v
def N (e f : Bool) (u v r : ℂ) : ℂ :=
  if e then (if f then 1 + (1 - r) * u * v else -((1 - r) * u + v))
  else (if f then -(u + (1 - r) * v) else 1 - r + u * v)

def rationalT (e f : Bool) (u v r : ℂ) : ℂ :=
  r * N e f u v r / (2 * E e f u v r) + r ^ 2 * u * v / E e f u v r ^ 2

def candidateT (e f : Bool) (u v r : ℂ) : ℂ :=
  sourceMode e u r * sourceMode f v r * (rationalT e f u v r - correction r)

def candidateJ (e f : Bool) (u v r : ℂ) : ℂ :=
  sourceMode e u r * sourceMode f v r *
    (r / 4 - correction r +
      r ^ 2 * rho e f u v / (4 * b u * b v * (W e u r + W f v r) ^ 2))

-- Exactly the coefficient in firstModeDerivative/secondModeDerivative.
def beta (e : Bool) (u : ℂ) : ℂ :=
  if e then (1 - 3 * u) / 2 else -(u + 1) / 2

def L (e : Bool) (F : ℂ → ℂ) (u : ℂ) : ℂ :=
  u * b u * deriv F u + beta e u * F u

-- The signed logarithmic derivative is calculated from the original mode sums.
def slope (e : Bool) (r : ℂ) : ℂ := if e then 1 - r else 1
def mLog (e : Bool) (u r : ℂ) : ℂ :=
  1 / (2 * b u) + slope e r / (2 * h e u r)
def modeD (e : Bool) (u r : ℂ) : ℂ :=
  if e then -r * u / h e u r else r * u / h e u r

lemma h_ne_zero (e : Bool) {u r : ℂ} (hu : ‖u‖ + ‖r‖ < 1) : h e u r ≠ 0 := by
  have hf := mode_factors_ne_zero hu
  cases e
  · exact hf.2.2
  · exact hf.2.1

lemma source_u (e : Bool) {u r : ℂ} (hu : ‖u‖ + ‖r‖ < 1) :
    HasDerivAt (fun w => sourceMode e w r) (mLog e u r * sourceMode e u r) u := by
  have hd := (mode_derivative e hu).2.hasDerivAt
  rw [mode_derivative_explicit e hu] at hd
  cases e <;> simpa only [mLog, slope, h, b, Bool.false_eq_true, ite_false, ite_true,
    one_mul, mul_one, mul_comm] using hd

lemma source_frequency (e : Bool) {u r : ℂ}
    (hb : b u ≠ 0) (hh : h e u r ≠ 0) :
    u * b u * mLog e u r + beta e u = modeA e u r := by
  cases e <;> simp only [mLog, slope, h, beta, modeA, Bool.false_eq_true,
    ite_false, ite_true] at hh ⊢ <;>
    generalize hD : (1 - (1-r)*u : ℂ) = d at hh ⊢ <;>
    field_simp [hb, hh] <;> (try rw [← hD]) <;> unfold b <;> ring

private lemma source_square (e : Bool) {u r : ℂ} (hu : ‖u‖ + ‖r‖ < 1) :
    sourceMode e u r ^ 2 = 1 / (b u * h e u r) := by
  cases e
  · exact (sourceMode_square hu).2
  · exact (sourceMode_square hu).1

lemma W_square (e : Bool) {u r : ℂ} (hu : ‖u‖ + ‖r‖ < 1) :
    W e u r ^ 2 = h e u r / b u := by
  have hb : b u ≠ 0 := (mode_factors_ne_zero hu).1
  have hh := h_ne_zero e hu
  unfold W
  rw [mul_pow, source_square e hu]
  field_simp [hb, hh] <;> ring

lemma source_W_normalization (e : Bool) {u r : ℂ} (hu : ‖u‖ + ‖r‖ < 1) :
    sourceMode e u r * b u * W e u r = 1 := by
  have hb : b u ≠ 0 := (mode_factors_ne_zero hu).1
  have hh := h_ne_zero e hu
  calc
    _ = sourceMode e u r ^ 2 * (b u * h e u r) := by unfold W; ring
    _ = 1 := by rw [source_square e hu]; exact one_div_mul_cancel (mul_ne_zero hb hh)

/- The branch proof uses a SINGLE base in cpow_add. It never uses cpow of a
product and never changes variables to 1/u. -/
def normalizedArgument (e : Bool) (u r : ℂ) : ℂ :=
  if e then 1 + r * u / b u else 1 - r / b u

private lemma source_closed (e : Bool) {u r : ℂ} (hu : ‖u‖ + ‖r‖ < 1) :
    sourceMode e u r = (1 / b u) * normalizedArgument e u r ^ (-1 / 2 : ℂ) := by
  cases e
  · exact (sourceAmplitude_generators hu).2.tsum_eq
  · exact (sourceAmplitude_generators hu).1.tsum_eq

private lemma normalizedArgument_re_pos (e : Bool) {u r : ℂ} (hu : ‖u‖ + ‖r‖ < 1) :
    0 < (normalizedArgument e u r).re := by
  have hu1 : ‖u‖ < 1 := by linarith [norm_nonneg r]
  have hb : 1 - ‖u‖ ≤ ‖b u‖ := by
    simpa only [b, norm_one] using norm_sub_norm_le (1 : ℂ) u
  have hb0 : 0 < ‖b u‖ := by linarith
  have hn : ‖r / b u‖ < 1 := by
    rw [norm_div]
    exact (div_lt_one hb0).mpr (by linarith)
  have hp : ‖r * u / b u‖ < 1 := by
    rw [norm_div, norm_mul]
    apply (div_lt_one hb0).mpr
    calc
      ‖r‖ * ‖u‖ ≤ ‖r‖ := mul_le_of_le_one_right (norm_nonneg r) hu1.le
      _ < ‖b u‖ := by linarith
  cases e
  · have ht := Complex.re_le_norm (r / b u)
    simp only [normalizedArgument, Bool.false_eq_true, ite_false, Complex.sub_re,
      Complex.one_re]
    linarith
  · have ht := neg_abs_le (r * u / b u).re
    have ha := Complex.abs_re_le_norm (r * u / b u)
    simp only [normalizedArgument, ite_true, Complex.add_re, Complex.one_re]
    linarith

private lemma W_eq_normalized_root (e : Bool) {u r : ℂ} (hu : ‖u‖ + ‖r‖ < 1) :
    W e u r = normalizedArgument e u r ^ (1 / 2 : ℂ) := by
  have hb : b u ≠ 0 := (mode_factors_ne_zero hu).1
  have hz : normalizedArgument e u r ≠ 0 := by
    intro hz
    have hh := normalizedArgument_re_pos e hu
    rw [hz, Complex.zero_re] at hh
    exact (lt_irrefl 0) hh
  have hratio : h e u r / b u = normalizedArgument e u r := by
    cases e <;> simp only [h, normalizedArgument, Bool.false_eq_true, ite_false,
      ite_true] <;> field_simp [hb] <;> unfold b <;> ring
  calc
    W e u r = (h e u r / b u) * normalizedArgument e u r ^ (-1 / 2 : ℂ) := by
      unfold W
      rw [source_closed e hu]
      ring
    _ = normalizedArgument e u r ^ (1 : ℂ) * normalizedArgument e u r ^ (-1 / 2 : ℂ) := by
      rw [hratio, Complex.cpow_one]
    _ = normalizedArgument e u r ^ ((1 : ℂ) + (-1 / 2 : ℂ)) :=
      (Complex.cpow_add _ _ hz).symm
    _ = normalizedArgument e u r ^ (1 / 2 : ℂ) := by norm_num

private lemma W_re_pos (e : Bool) {u r : ℂ} (hu : ‖u‖ + ‖r‖ < 1) :
    0 < (W e u r).re := by
  rw [W_eq_normalized_root e hu, show (1 / 2 : ℂ) = 2⁻¹ by norm_num,
    Complex.cpow_inv_two_re]
  apply Real.sqrt_pos.2
  have hp := normalizedArgument_re_pos e hu
  have hn := norm_nonneg (normalizedArgument e u r)
  linarith

lemma W_sum_ne_zero (e f : Bool) {u v r : ℂ}
    (hu : ‖u‖ + ‖r‖ < 1) (hv : ‖v‖ + ‖r‖ < 1) :
    W e u r + W f v r ≠ 0 := by
  intro hz
  have hp := W_re_pos e hu
  have hq := W_re_pos f hv
  have hh := congrArg Complex.re hz
  simp only [Complex.add_re, Complex.zero_re] at hh
  linarith

private lemma source_analytic (e : Bool) {u r : ℂ} (hu : ‖u‖ + ‖r‖ < 1) :
    AnalyticAt ℂ (fun w => sourceMode e w r) u := by
  have hon : DifferentiableOn ℂ (fun w => sourceMode e w r) (Metric.ball 0 (1 - ‖r‖)) := by
    intro w hw
    exact (source_u e (show ‖w‖ + ‖r‖ < 1 by
      have hh : ‖w‖ < 1 - ‖r‖ := by simpa using hw
      linarith)).differentiableAt.differentiableWithinAt
  exact hon.analyticOnNhd Metric.isOpen_ball u (by
    change dist u 0 < 1 - ‖r‖
    simpa only [dist_zero_right] using (show ‖u‖ < 1 - ‖r‖ by linarith))

lemma ell_eq_source {r : ℂ} (hr : ‖r‖ < 1) :
    ell r = OriginalGaussianAllIndexResolvent.shiftedCentralDerivative r 0 / period r := by
  have hd := OriginalGaussianAllIndexResolvent.central_hasDerivAt hr 0
  have hf : (fun w => OriginalGaussianAllIndexResolvent.shiftedCentralSeries w 0) = period :=
    funext (fun w => (OriginalGaussianAllIndexResolvent.period_eq_central w).symm)
  rw [hf] at hd
  exact congrArg (fun x => x / period r) hd.deriv

private lemma E_comm (e f : Bool) (u v r : ℂ) : E e f u v r = E f e v u r := by
  cases e <;> cases f <;> simp only [E, K, Bool.false_eq_true, ite_false, ite_true] <;> ring
private lemma N_comm (e f : Bool) (u v r : ℂ) : N e f u v r = N f e v u r := by
  cases e <;> cases f <;> simp only [N, Bool.false_eq_true, ite_false, ite_true] <;> ring
private lemma rationalT_comm (e f : Bool) (u v r : ℂ) :
    rationalT e f u v r = rationalT f e v u r := by
  unfold rationalT
  rw [E_comm e f u v r, N_comm e f u v r]
  ring

-- Only derivatives of the four explicit polynomials; no general rational PDE framework.
def Ku (e f : Bool) (v : ℂ) : ℂ := if e then (if f then v else -1) else 0
def Nu (e f : Bool) (v r : ℂ) : ℂ :=
  if e then (if f then (1 - r) * v else -(1 - r)) else (if f then -1 else v)
def Eu (e f : Bool) (v r : ℂ) : ℂ := -b v - r * Ku e f v

def tU (e f : Bool) (u v r : ℂ) : ℂ :=
  r * (Nu e f v r * E e f u v r - N e f u v r * Eu e f v r) / (2 * E e f u v r ^ 2) +
    r ^ 2 * v / E e f u v r ^ 2 - 2 * r ^ 2 * u * v * Eu e f v r / E e f u v r ^ 3

private lemma K_u (e f : Bool) (u v : ℂ) :
    HasDerivAt (fun w => K e f w v) (Ku e f v) u := by
  cases e
  · cases f <;> exact hasDerivAt_const u _
  · cases f
    · convert (hasDerivAt_id u).neg using 1 <;> (try funext w) <;> simp [K, Ku]
    · simpa only [K, Ku, ite_true, one_mul, id_eq] using (hasDerivAt_id u).mul_const v

private lemma E_u (e f : Bool) (u v r : ℂ) :
    HasDerivAt (fun w => E e f w v r) (Eu e f v r) u := by
  convert (((hasDerivAt_id u).const_sub 1).mul_const (b v)).sub
    ((K_u e f u v).const_mul r) using 1 <;>
    (try (apply funext; intro w)) <;>
    simp only [E, Eu, b, Pi.sub_apply, Pi.mul_apply, id_eq] <;> ring

private lemma N_u (e f : Bool) (u v r : ℂ) :
    HasDerivAt (fun w => N e f w v r) (Nu e f v r) u := by
  cases e
  · cases f
    · simpa only [N, Nu, Bool.false_eq_true, ite_false, one_mul, id_eq] using
        ((hasDerivAt_id u).mul_const v).const_add (1 - r)
    · convert ((hasDerivAt_id u).add_const ((1 - r) * v)).neg using 1 <;>
        (try funext w) <;> simp [N, Nu]
  · cases f
    · convert (((hasDerivAt_id u).const_mul (1 - r)).add_const v).neg using 1 <;>
        (try funext w) <;> simp only [N, Nu, Bool.false_eq_true, ite_false, ite_true, mul_one, Pi.neg_apply, id_eq] <;> ring
    · convert ((((hasDerivAt_id u).const_mul (1 - r)).mul_const v).const_add 1) using 1 <;>
        (try funext w) <;> simp only [N, Nu, ite_true, mul_one, id_eq] <;> ring

private lemma rationalT_u (e f : Bool) {u v r : ℂ} (he : E e f u v r ≠ 0) :
    HasDerivAt (fun w => rationalT e f w v r) (tU e f u v r) u := by
  have hE := E_u e f u v r
  have hQ := ((N_u e f u v r).const_mul r).div (hE.const_mul 2)
    (mul_ne_zero (by norm_num) he)
  have hS := (((hasDerivAt_id u).const_mul (r ^ 2)).mul_const v).div
    (hE.pow 2) (pow_ne_zero _ he)
  convert hQ.add hS using 1
  · funext w
    rfl
  · simp only [tU, Pi.pow_apply, Pi.mul_apply, id_eq, Nat.cast_ofNat,
      Nat.reduceSub, pow_one]
    field_simp [he]
    ring

private lemma rationalT_v (e f : Bool) {u v r : ℂ} (he : E e f u v r ≠ 0) :
    HasDerivAt (fun w => rationalT e f u w r) (tU f e v u r) v := by
  simpa only [rationalT_comm e f u] using
    (rationalT_u f e (u := v) (v := u) (r := r)
      (by simpa only [E_comm e f u] using he))

-- Tdop(P) certificate from the terminal result. field_simp is licensed by
-- actual h factors and E, including the difficult -- denominator d-r.
set_option maxHeartbeats 1600000 in
private lemma rationalT_spatial (e f : Bool) {u v r : ℂ}
    (hau : h e u r ≠ 0) (hav : h f v r ≠ 0) (he : E e f u v r ≠ 0) :
    modeScale f v * u * b u * tU e f u v r -
        modeScale e u * v * b v * tU f e v u r +
      (modeScale f v * modeA e u r - modeScale e u * modeA f v r) * rationalT e f u v r =
        (1 - r) * (modeA e u r * modeD f v r - modeD e u r * modeA f v r) / 2 := by
  simp only [tU, rationalT, E_comm f e v u r]
  cases e <;> cases f <;>
    simp only [modeScale, modeA, modeD, h, Eu, Ku, Nu, N,
      Bool.false_eq_true, ite_false, ite_true] at hau hav ⊢ <;>
    generalize hD : (1 - (1-r)*u : ℂ) = d at hau ⊢ <;>
    generalize hF : (1 - (1-r)*v : ℂ) = a at hav ⊢ <;>
    field_simp [hau, hav, he] <;> (try rw [← hD]) <;> (try rw [← hF]) <;> unfold E K b <;>
    simp only [Bool.false_eq_true, ite_false, ite_true] <;> ring

private lemma candidateT_u (e f : Bool) {u v r : ℂ} (hu : ‖u‖ + ‖r‖ < 1)
    (he : E e f u v r ≠ 0) :
    HasDerivAt (fun w => candidateT e f w v r)
      (sourceMode e u r * sourceMode f v r *
        (tU e f u v r + mLog e u r * (rationalT e f u v r - correction r))) u := by
  apply (((source_u e hu).mul_const (sourceMode f v r)).mul
    ((rationalT_u e f he).sub_const (correction r))).congr_deriv
  try simp only [Pi.mul_apply, Pi.sub_apply, id_eq]
  ring

private lemma candidateT_v (e f : Bool) {u v r : ℂ} (hv : ‖v‖ + ‖r‖ < 1)
    (he : E e f u v r ≠ 0) :
    HasDerivAt (fun w => candidateT e f u w r)
      (sourceMode e u r * sourceMode f v r *
        (tU f e v u r + mLog f v r * (rationalT e f u v r - correction r))) v := by
  apply (((source_u f hv).const_mul (sourceMode e u r)).mul
    ((rationalT_v e f he).sub_const (correction r))).congr_deriv
  try simp only [Pi.mul_apply, Pi.sub_apply, id_eq]
  ring

-- Actual source-mode spatial T equation. No parameter derivative or PF is used.
set_option maxHeartbeats 1600000 in
private theorem candidateT_displacement (e f : Bool) {u v r : ℂ}
    (hu : ‖u‖ + ‖r‖ < 1) (hv : ‖v‖ + ‖r‖ < 1) (he : E e f u v r ≠ 0) :
    let lam := OriginalGaussianAllIndexResolvent.shiftedCentralDerivative r 0 / period r
    modeScale f v * L e (fun w => candidateT e f w v r) u -
      modeScale e u * L f (fun w => candidateT e f u w r) v =
      (1 - r) * sourceMode e u r * sourceMode f v r *
        (modeA e u r * modeH f v r lam - modeH e u r lam * modeA f v r) / 2 := by
  have hr : ‖r‖ < 1 := by linarith [norm_nonneg u]
  dsimp only
  rw [← ell_eq_source hr]
  have hbu : b u ≠ 0 := (mode_factors_ne_zero hu).1
  have hbv : b v ≠ 0 := (mode_factors_ne_zero hv).1
  have hau := h_ne_zero e hu
  have hav := h_ne_zero f hv
  have hLu : L e (fun w => candidateT e f w v r) u =
      sourceMode e u r * sourceMode f v r *
        (u * b u * tU e f u v r + modeA e u r * (rationalT e f u v r - correction r)) := by
    unfold L
    rw [(candidateT_u e f hu he).deriv]
    dsimp only [candidateT]
    linear_combination sourceMode e u r * sourceMode f v r *
      (rationalT e f u v r - correction r) * source_frequency e hbu hau
  have hLv : L f (fun w => candidateT e f u w r) v =
      sourceMode e u r * sourceMode f v r *
        (v * b v * tU f e v u r + modeA f v r * (rationalT e f u v r - correction r)) := by
    unfold L
    rw [(candidateT_v e f hv he).deriv]
    dsimp only [candidateT]
    linear_combination sourceMode e u r * sourceMode f v r *
      (rationalT e f u v r - correction r) * source_frequency f hbv hav
  rw [hLu, hLv]
  have hc := rationalT_spatial e f hau hav he
  have halg :
      (1 - r) * (modeA e u r * modeD f v r - modeD e u r * modeA f v r) / 2 -
        (modeScale f v * modeA e u r - modeScale e u * modeA f v r) * correction r =
      (1 - r) * (modeA e u r * modeH f v r (ell r) -
        modeH e u r (ell r) * modeA f v r) / 2 := by
    cases e <;> cases f <;>
      simp only [modeH, modeA, modeScale, modeD, h, correction,
        Bool.false_eq_true, ite_false, ite_true] at hau hav ⊢ <;>
      field_simp [hau, hav] <;> ring
  linear_combination sourceMode e u r * sourceMode f v r * hc +
    sourceMode e u r * sourceMode f v r * halg

private lemma K_norm_le_one (e f : Bool) {u v : ℂ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖K e f u v‖ ≤ 1 := by
  cases e <;> cases f
  · simp [K]
  · simpa only [K, Bool.false_eq_true, ite_false, ite_true, norm_neg] using hv
  · simpa only [K, Bool.false_eq_true, ite_false, ite_true, norm_neg] using hu
  · simpa only [K, ite_true, norm_mul] using mul_le_one₀ hu (norm_nonneg v) hv

-- Uniform proof for all FOUR table entries, using |K| <= 1.
lemma E_ne_zero (e f : Bool) {u v r : ℂ}
    (hu : ‖u‖ + Real.sqrt ‖r‖ < 1) (hv : ‖v‖ + Real.sqrt ‖r‖ < 1) :
    E e f u v r ≠ 0 := by
  have ht : 0 ≤ Real.sqrt ‖r‖ := Real.sqrt_nonneg _
  have hsq : (Real.sqrt ‖r‖) ^ 2 = ‖r‖ := Real.sq_sqrt (norm_nonneg r)
  have hbound (w : ℂ) (hw : ‖w‖ + Real.sqrt ‖r‖ < 1) :
      Real.sqrt ‖r‖ < ‖b w‖ := by
    have hn : 1 - ‖w‖ ≤ ‖b w‖ := by
      simpa only [norm_one, b] using norm_sub_norm_le (1 : ℂ) w
    linarith
  have hu' := hbound u hu
  have hv' := hbound v hv
  have hbu : 0 < ‖b u‖ := lt_of_le_of_lt ht hu'
  have hk := K_norm_le_one e f (u := u) (v := v) (by linarith) (by linarith)
  have hp : ‖r * K e f u v‖ < ‖b u * b v‖ := by
    rw [norm_mul, norm_mul]
    calc
      ‖r‖ * ‖K e f u v‖ ≤ ‖r‖ := mul_le_of_le_one_right (norm_nonneg r) hk
      _ = Real.sqrt ‖r‖ * Real.sqrt ‖r‖ := by nlinarith [hsq]
      _ ≤ ‖b u‖ * Real.sqrt ‖r‖ := mul_le_mul_of_nonneg_right hu'.le ht
      _ < ‖b u‖ * ‖b v‖ := mul_lt_mul_of_pos_left hv' hbu
  intro he
  have hh : b u * b v = r * K e f u v := sub_eq_zero.mp he
  exact (ne_of_lt hp) (congrArg norm hh).symm

lemma original_small {w : ℂ} {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hw : ‖w‖ + Real.sqrt r < 1) : ‖w‖ + ‖(r : ℂ)‖ < 1 := by
  have hnr : ‖(r : ℂ)‖ = r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  have hrs : r ≤ Real.sqrt r := Real.le_sqrt_self_iff.mpr hr1.le
  rw [hnr]
  linarith

/-- exact signed T displacement PDE, with all denominator premises
proved from the original domain. Axes and same-sign diagonals are included. -/
theorem candidateT_original_displacement (e f : Bool) {u v : ℂ} {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1)
    (hu : ‖u‖ + Real.sqrt r < 1) (hv : ‖v‖ + Real.sqrt r < 1) :
    let x : ℂ := r
    let lam := OriginalGaussianAllIndexResolvent.shiftedCentralDerivative x 0 / period x
    modeScale f v * L e (fun w => candidateT e f w v x) u -
      modeScale e u * L f (fun w => candidateT e f u w x) v =
      (1 - x) * sourceMode e u x * sourceMode f v x *
        (modeA e u x * modeH f v x lam - modeH e u x lam * modeA f v x) / 2 := by
  have hnr : ‖(r : ℂ)‖ = r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  exact candidateT_displacement e f (original_small hr.le hr1 hu)
    (original_small hr.le hr1 hv)
    (E_ne_zero e f (by simpa only [hnr] using hu) (by simpa only [hnr] using hv))


private lemma candidateT_joint_analytic (e f : Bool) {u v r : ℂ}
    (hu : ‖u‖ + ‖r‖ < 1) (hv : ‖v‖ + ‖r‖ < 1) (he : E e f u v r ≠ 0) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => candidateT e f p.1 p.2 r) (u, v) := by
  have hMu : AnalyticAt ℂ (fun p : ℂ × ℂ => sourceMode e p.1 r) (u, v) :=
    AnalyticAt.comp (source_analytic e hu) analyticAt_fst
  have hMv : AnalyticAt ℂ (fun p : ℂ × ℂ => sourceMode f p.2 r) (u, v) :=
    AnalyticAt.comp (source_analytic f hv) analyticAt_snd
  have hK : AnalyticAt ℂ (fun p : ℂ × ℂ => K e f p.1 p.2) (u, v) := by
    cases e <;> cases f
    · exact analyticAt_const
    · exact analyticAt_snd.neg
    · exact analyticAt_fst.neg
    · exact analyticAt_fst.mul analyticAt_snd
  have hN : AnalyticAt ℂ (fun p : ℂ × ℂ => N e f p.1 p.2 r) (u, v) := by
    cases e <;> cases f
    · exact analyticAt_const.add (analyticAt_fst.mul analyticAt_snd)
    · exact (analyticAt_fst.add (analyticAt_const.mul analyticAt_snd)).neg
    · exact ((analyticAt_const.mul analyticAt_fst).add analyticAt_snd).neg
    · exact analyticAt_const.add ((analyticAt_const.mul analyticAt_fst).mul analyticAt_snd)
  have hE : AnalyticAt ℂ (fun p : ℂ × ℂ => E e f p.1 p.2 r) (u, v) :=
    ((analyticAt_const.sub analyticAt_fst).mul (analyticAt_const.sub analyticAt_snd)).sub
      (analyticAt_const.mul hK)
  unfold candidateT rationalT
  apply (hMu.mul hMv).mul
  apply AnalyticAt.sub _ analyticAt_const
  exact ((analyticAt_const.mul hN).div (analyticAt_const.mul hE)
    (mul_ne_zero (by norm_num) he)).add
      (((analyticAt_const.mul analyticAt_fst).mul analyticAt_snd).div (hE.pow 2) (pow_ne_zero _ he))

lemma candidateJ_joint_analytic (e f : Bool) {u v r : ℂ}
    (hu : ‖u‖ + ‖r‖ < 1) (hv : ‖v‖ + ‖r‖ < 1) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => candidateJ e f p.1 p.2 r) (u, v) := by
  have hMu : AnalyticAt ℂ (fun p : ℂ × ℂ => sourceMode e p.1 r) (u, v) :=
    AnalyticAt.comp (source_analytic e hu) analyticAt_fst
  have hMv : AnalyticAt ℂ (fun p : ℂ × ℂ => sourceMode f p.2 r) (u, v) :=
    AnalyticAt.comp (source_analytic f hv) analyticAt_snd
  have hWu : AnalyticAt ℂ (fun p : ℂ × ℂ => W e p.1 r) (u, v) := by
    cases e
    · exact (analyticAt_const.sub analyticAt_fst).mul hMu
    · exact (analyticAt_const.sub (analyticAt_const.mul analyticAt_fst)).mul hMu
  have hWv : AnalyticAt ℂ (fun p : ℂ × ℂ => W f p.2 r) (u, v) := by
    cases f
    · exact (analyticAt_const.sub analyticAt_snd).mul hMv
    · exact (analyticAt_const.sub (analyticAt_const.mul analyticAt_snd)).mul hMv
  have hRho : AnalyticAt ℂ (fun p : ℂ × ℂ => rho e f p.1 p.2) (u, v) := by
    by_cases hef : e = f
    · convert (analyticAt_fst.add analyticAt_snd : AnalyticAt ℂ _ (u, v)) using 1
      funext p
      simp [rho, hef]
    · have hOne : AnalyticAt ℂ (fun _ : ℂ × ℂ => (1 : ℂ)) (u,v) := analyticAt_const
      convert (hOne.add (analyticAt_fst.mul analyticAt_snd)).neg using 1
      funext p
      simp [rho, hef]
  have hbu : b u ≠ 0 := (mode_factors_ne_zero hu).1
  have hbv : b v ≠ 0 := (mode_factors_ne_zero hv).1
  have hs := W_sum_ne_zero e f hu hv
  unfold candidateJ
  apply (hMu.mul hMv).mul
  apply analyticAt_const.add
  apply AnalyticAt.div
  · exact analyticAt_const.mul hRho
  · exact ((analyticAt_const.mul (analyticAt_const.sub analyticAt_fst)).mul
      (analyticAt_const.sub analyticAt_snd)).mul ((hWu.add hWv).pow 2)
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hbu) hbv) (pow_ne_zero _ hs)

/-- genuine JOINT complex differentiability in (u,v), on the full
original source bidisk, with no branch/nonzero premises passed to the consumer. -/
theorem candidates_original_joint_differentiable (e f : Bool) {u v : ℂ} {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1)
    (hu : ‖u‖ + Real.sqrt r < 1) (hv : ‖v‖ + Real.sqrt r < 1) :
    DifferentiableAt ℂ (fun p : ℂ × ℂ => candidateJ e f p.1 p.2 (r : ℂ)) (u, v) ∧
    DifferentiableAt ℂ (fun p : ℂ × ℂ => candidateT e f p.1 p.2 (r : ℂ)) (u, v) := by
  have hnr : ‖(r : ℂ)‖ = r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hu' := original_small hr.le hr1 hu
  have hv' := original_small hr.le hr1 hv
  exact ⟨(candidateJ_joint_analytic e f hu' hv').differentiableAt,
    (candidateT_joint_analytic e f hu' hv' (E_ne_zero e f
      (by simpa only [hnr] using hu) (by simpa only [hnr] using hv))).differentiableAt⟩

/-- the direct inverse-square definition retains the same-sign
removable diagonal, including u=0. This is evaluation of the regular formula. -/
lemma candidateJ_diagonal (e : Bool) {u r : ℂ} (hu : ‖u‖ + ‖r‖ < 1) :
    candidateJ e e u u r =
      (r / 4 - correction r) / (b u * h e u r) +
        r ^ 2 * u / (8 * (b u * h e u r) ^ 2) := by
  have hb : b u ≠ 0 := (mode_factors_ne_zero hu).1
  have hh := h_ne_zero e hu
  have hS : sourceMode e u r * sourceMode e u r = 1 / (b u * h e u r) := by
    simpa only [pow_two] using source_square e hu
  unfold candidateJ
  rw [hS]
  simp only [rho, ite_true]
  rw [show W e u r + W e u r = 2 * W e u r by ring, mul_pow, W_square e hu]
  field_simp [hb, hh]
  ring

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalSignedCandidate
