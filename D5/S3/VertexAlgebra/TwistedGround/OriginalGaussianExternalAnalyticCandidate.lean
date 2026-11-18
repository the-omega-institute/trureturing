/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive Gaussian kernel equations and actual positive J identification. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalCandidateCore
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPeriodIdentity
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.MeanValue

/-! The square-root branch is the existing literal sourceMode, never a new root.
The rational formulas and certificates are due to the supplied Pro construction;
their analytic verification uses the original source derivatives and period. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology
namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalAnalyticCandidate
open OriginalGaussianExternalGenerators OriginalGaussianExternalGeneratedSource
open OriginalGaussianExternalModeSums OriginalGaussianExternalJetSums
open D5.S3.Analytic.OriginalHalfBinomialPeriod

def a (u r : ℂ) : ℂ := 1 - (1 - r) * u
def b (u : ℂ) : ℂ := 1 - u
def E (u v r : ℂ) : ℂ := 1 - u - v + (1 - r) * u * v
def W (u r : ℂ) : ℂ := a u r * sourceMode true u r
def ell (r : ℂ) : ℂ := deriv period r / period r
def correction (r : ℂ) : ℂ := r * (1 - r) * ell r

def rationalT (u v r : ℂ) : ℂ :=
  r * (1 + (1 - r) * u * v) / (2 * E u v r) + r ^ 2 * u * v / E u v r ^ 2

def candidateT (u v r : ℂ) : ℂ :=
  sourceMode true u r * sourceMode true v r * (rationalT u v r - correction r)

/-- This expression includes u=v and either zero coordinate without a chart inverse. -/
def candidateJ (u v r : ℂ) : ℂ :=
  sourceMode true u r * sourceMode true v r *
    (r / 4 - correction r +
      r ^ 2 * (u + v) / (4 * b u * b v * (W u r + W v r) ^ 2))

def rationalJ (u v r : ℂ) : ℂ :=
  (u * b v * a u r + v * b u * a v r) / (2 * (u - v) ^ 2)
def cauchy (u v : ℂ) : ℂ := (u + v) / (2 * (u - v) ^ 2)
private def D (u r : ℂ) : ℂ := -r * u / a u r
private def mLog (u r : ℂ) : ℂ := 1 / (2 * b u) + (1 - r) / (2 * a u r)
private def tU (u v r : ℂ) : ℂ :=
  r * ((1 - r) * v * E u v r + (1 + (1 - r) * u * v) * a v r) /
      (2 * E u v r ^ 2) + r ^ 2 * v / E u v r ^ 2 +
    2 * r ^ 2 * u * v * a v r / E u v r ^ 3
private def tR (u v r : ℂ) : ℂ :=
  ((1 + (1 - 2 * r) * u * v) * E u v r +
      r * (1 + (1 - r) * u * v) * u * v) / (2 * E u v r ^ 2) +
    2 * r * u * v / E u v r ^ 2 + 2 * r ^ 2 * u ^ 2 * v ^ 2 / E u v r ^ 3

private lemma a_formula (u r : ℂ) : a u r = 1 - (1 - r) * u := rfl
private lemma E_comm (u v r : ℂ) : E u v r = E v u r := by unfold E; ring
private lemma rationalT_comm (u v r : ℂ) : rationalT u v r = rationalT v u r := by
  unfold rationalT
  rw [E_comm u v r]
  ring

private lemma source_u {u r : ℂ} (h : ‖u‖ + ‖r‖ < 1) :
    HasDerivAt (fun w => sourceMode true w r) (mLog u r * sourceMode true u r) u := by
  have hd := (mode_derivative true h).2.hasDerivAt
  rw [mode_derivative_explicit true h] at hd
  simpa only [mLog, a, b, ite_true, mul_comm] using hd

private lemma source_r {u r : ℂ} (h : ‖u‖ + ‖r‖ < 1) :
    HasDerivAt (fun w => sourceMode true u w)
      (-u * sourceMode true u r / (2 * a u r)) r := by
  have hd := (amplitude_derivative_mode true h).2.1.hasDerivAt
  rw [diagonal_derivative_explicit true h] at hd
  convert hd using 1 <;> simp only [ite_true, a] <;> congr 1 <;> ring

lemma correction_hasDerivAt {r : ℂ} (hr : ‖r‖ < 1) :
    HasDerivAt correction (1 / 4 - r * (1 - r) * ell r ^ 2) r := by
  have hp := picard_fuchs hr
  have hn := OriginalGaussianPeriodIdentity.period_ne_zero hr
  have hd := (((hasDerivAt_id r).mul ((hasDerivAt_id r).const_sub 1)).mul
    (hp.2.1.hasDerivAt.div hp.1.hasDerivAt hn))
  apply hd.congr_deriv
  dsimp only [correction, ell, id_eq, Pi.mul_apply, Pi.div_apply]
  field_simp [hn]
  linear_combination 4 * period r * hp.2.2

private lemma rationalT_u {u v r : ℂ} (he : E u v r ≠ 0) :
    HasDerivAt (fun w => rationalT w v r) (tU u v r) u := by
  have hE : HasDerivAt (fun w => E w v r) (-a v r) u := by
    convert (((hasDerivAt_const u (1 : ℂ)).sub (hasDerivAt_id u)).sub_const v).add
      (((hasDerivAt_id u).const_mul (1 - r)).mul_const v) using 1 <;>
      (try (apply funext; intro w)) <;>
      simp only [E, a, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, id_eq] <;> ring
  have hN : HasDerivAt (fun w => r * (1 + (1 - r) * w * v))
      (r * (1 - r) * v) u := by
    convert (((((hasDerivAt_id u).const_mul (1 - r)).mul_const v).const_add 1).const_mul r)
      using 1 <;> (try (apply funext; intro w)) <;>
      (try simp only [Pi.mul_apply, id_eq]) <;> ring
  have hQ := hN.div (hE.const_mul 2) (mul_ne_zero (by norm_num) he)
  have hS := (((hasDerivAt_id u).const_mul (r ^ 2)).mul_const v).div
    (hE.pow 2) (pow_ne_zero _ he)
  convert hQ.add hS using 1
  · funext w
    rfl
  · simp only [tU, Pi.pow_apply, Pi.mul_apply, id_eq, Nat.cast_ofNat,
      Nat.reduceSub, pow_one]
    field_simp [he]
    ring

private lemma rationalT_v {u v r : ℂ} (he : E u v r ≠ 0) :
    HasDerivAt (fun w => rationalT u w r) (tU v u r) v := by
  simpa only [rationalT_comm u, E_comm u] using
    (rationalT_u (u := v) (v := u) (r := r) (by simpa only [E_comm u] using he))

private lemma rationalT_r {u v r : ℂ} (he : E u v r ≠ 0) :
    HasDerivAt (fun w => rationalT u v w) (tR u v r) r := by
  have hE : HasDerivAt (fun w => E u v w) (-u * v) r := by
    convert ((((hasDerivAt_id r).const_sub 1).mul_const u).mul_const v).const_add
      (1 - u - v) using 1 <;> (try (apply funext; intro w)) <;>
      (try simp only [E, id_eq]) <;> ring
  have hN := (hasDerivAt_id r).mul
    (((((hasDerivAt_id r).const_sub 1).mul_const u).mul_const v).const_add 1)
  have hS := (((hasDerivAt_pow 2 r).mul_const u).mul_const v).div
    (hE.pow 2) (pow_ne_zero _ he)
  convert (hN.div (hE.const_mul 2) (mul_ne_zero (by norm_num) he)).add hS using 1
  · funext w
    rfl
  · simp only [tR, Pi.pow_apply, Pi.mul_apply, id_eq, Nat.cast_ofNat,
      Nat.reduceSub, pow_one]
    field_simp [he]
    ring

private lemma rationalT_spatial {u v r : ℂ}
    (ha : a u r ≠ 0) (hb : a v r ≠ 0) (he : E u v r ≠ 0) :
    u * b u * tU u v r - v * b v * tU v u r +
      (modeA true u r - modeA true v r) * rationalT u v r =
        (1 - r) * (b u * D v r - D u r * b v) / 4 := by
  unfold tU rationalT D
  simp only [modeA, ite_true, ← a_formula, E_comm v u r]
  field_simp [ha, hb, he]
  unfold a b E
  ring

private lemma rationalT_radial {u v r : ℂ}
    (ha : a u r ≠ 0) (hb : a v r ≠ 0) (he : E u v r ≠ 0) :
    2 * r * tR u v r - u * b u * tU u v r - v * b v * tU v u r +
      (D u r + D v r - modeA true u r - modeA true v r) * rationalT u v r =
        r / 2 - (1 - r) * (D u r * b v + b u * D v r) / 4 := by
  unfold tR tU rationalT D
  simp only [modeA, ite_true, ← a_formula, E_comm v u r]
  field_simp [ha, hb, he]
  unfold a b E
  ring

private lemma ell_source {r : ℂ} (hr : ‖r‖ < 1) :
    ell r = OriginalGaussianAllIndexResolvent.shiftedCentralDerivative r 0 / period r := by
  have hd := OriginalGaussianAllIndexResolvent.central_hasDerivAt hr 0
  have hf : (fun w => OriginalGaussianAllIndexResolvent.shiftedCentralSeries w 0) = period :=
    funext (fun w => (OriginalGaussianAllIndexResolvent.period_eq_central w).symm)
  rw [hf] at hd
  exact congrArg (fun x => x / period r) hd.deriv

private lemma source_frequency {u r : ℂ} (hu : b u ≠ 0) (ha : a u r ≠ 0) :
    u * b u * mLog u r + (1 - 3 * u) / 2 = modeA true u r := by
  simp only [mLog, modeA, ite_true, ← a_formula]
  field_simp [hu, ha]
  unfold a b
  ring

private lemma candidateT_u {u v r : ℂ} (hu : ‖u‖ + ‖r‖ < 1)
    (he : E u v r ≠ 0) :
    HasDerivAt (fun w => candidateT w v r)
      (sourceMode true u r * sourceMode true v r *
        (tU u v r + mLog u r * (rationalT u v r - correction r))) u := by
  apply (((source_u hu).mul_const (sourceMode true v r)).mul
    ((rationalT_u he).sub_const (correction r))).congr_deriv
  try simp only [Pi.mul_apply, Pi.sub_apply, id_eq]
  ring

private lemma candidateT_v {u v r : ℂ} (hv : ‖v‖ + ‖r‖ < 1)
    (he : E u v r ≠ 0) :
    HasDerivAt (fun w => candidateT u w r)
      (sourceMode true u r * sourceMode true v r *
        (tU v u r + mLog v r * (rationalT u v r - correction r))) v := by
  apply (((source_u hv).const_mul (sourceMode true u r)).mul
    ((rationalT_v he).sub_const (correction r))).congr_deriv
  try simp only [Pi.mul_apply, Pi.sub_apply, id_eq]
  ring

private lemma candidateT_r {u v r : ℂ} (hu : ‖u‖ + ‖r‖ < 1)
    (hv : ‖v‖ + ‖r‖ < 1) (he : E u v r ≠ 0) :
    HasDerivAt (fun w => candidateT u v w)
      (sourceMode true u r * sourceMode true v r *
        (tR u v r - (1 / 4 - r * (1 - r) * ell r ^ 2) +
          (-u / (2 * a u r) - v / (2 * a v r)) *
            (rationalT u v r - correction r))) r := by
  have hr : ‖r‖ < 1 := by linarith [norm_nonneg u]
  apply (((source_r hu).mul (source_r hv)).mul
    ((rationalT_r he).sub (correction_hasDerivAt hr))).congr_deriv
  try simp only [Pi.mul_apply, Pi.sub_apply, id_eq]
  ring

/-- The positive frequency operator, in the same normalization as the literal equations. -/
def L (f : ℂ → ℂ) (u : ℂ) : ℂ :=
  u * b u * deriv f u + (1 - 3 * u) / 2 * f u

/-- Both T equations hold for the actual normalized source factors and period.
No nonzero-coordinate or off-diagonal hypothesis occurs. -/
theorem candidateT_differential {u v r : ℂ}
    (hu : ‖u‖ + ‖r‖ < 1) (hv : ‖v‖ + ‖r‖ < 1) (he : E u v r ≠ 0) :
    let lam := OriginalGaussianAllIndexResolvent.shiftedCentralDerivative r 0 / period r
    (L (fun w => candidateT w v r) u - L (fun w => candidateT u w r) v =
      (1 - r) * sourceMode true u r * sourceMode true v r *
        (modeA true u r * modeH true v r lam - modeH true u r lam * modeA true v r) / 2) ∧
    (2 * r * deriv (fun w => candidateT u v w) r -
        L (fun w => candidateT w v r) u - L (fun w => candidateT u w r) v =
      (1 - r) * sourceMode true u r * sourceMode true v r *
        (modeH true u r lam * modeH true v r lam - modeA true u r * modeA true v r) / 2) := by
  have hr : ‖r‖ < 1 := by linarith [norm_nonneg u]
  dsimp only
  rw [← ell_source hr]
  have hfu := mode_factors_ne_zero hu
  have hfv := mode_factors_ne_zero hv
  have hbu : b u ≠ 0 := hfu.1
  have hbv : b v ≠ 0 := hfv.1
  have hau : a u r ≠ 0 := hfu.2.1
  have hav : a v r ≠ 0 := hfv.2.1
  have hLu : L (fun w => candidateT w v r) u =
      sourceMode true u r * sourceMode true v r *
        (u * b u * tU u v r + modeA true u r * (rationalT u v r - correction r)) := by
    unfold L
    rw [(candidateT_u hu he).deriv]
    dsimp only [candidateT]
    linear_combination sourceMode true u r * sourceMode true v r *
      (rationalT u v r - correction r) * source_frequency hbu hau
  have hLv : L (fun w => candidateT u w r) v =
      sourceMode true u r * sourceMode true v r *
        (v * b v * tU v u r + modeA true v r * (rationalT u v r - correction r)) := by
    unfold L
    rw [(candidateT_v hv he).deriv]
    dsimp only [candidateT]
    linear_combination sourceMode true u r * sourceMode true v r *
      (rationalT u v r - correction r) * source_frequency hbv hav
  rw [hLu, hLv]
  constructor
  · have hc := rationalT_spatial hau hav he
    have halg :
        (1 - r) * (b u * D v r - D u r * b v) / 4 -
          (modeA true u r - modeA true v r) * correction r =
        (1 - r) *
          (modeA true u r * modeH true v r (ell r) -
            modeH true u r (ell r) * modeA true v r) / 2 := by
      simp only [modeH, modeA, modeScale, ite_true, correction, D, ← a_formula]
      field_simp [hau, hav]
      unfold a b
      ring
    linear_combination sourceMode true u r * sourceMode true v r * hc +
      sourceMode true u r * sourceMode true v r * halg
  · rw [(candidateT_r hu hv he).deriv]
    have hc := rationalT_radial hau hav he
    have halg :
        r / 2 - (1 - r) * (D u r * b v + b u * D v r) / 4 -
          2 * r * (1 / 4 - r * (1 - r) * ell r ^ 2) -
          (D u r + D v r - modeA true u r - modeA true v r) * correction r =
        (1 - r) *
          (modeH true u r (ell r) * modeH true v r (ell r) -
            modeA true u r * modeA true v r) / 2 := by
      simp only [modeH, modeA, modeScale, ite_true, correction, D, ← a_formula]
      field_simp [hau, hav]
      unfold a b
      ring
    have hD (w : ℂ) : 2 * r * (-w / (2 * a w r)) = D w r := by
      simp only [D, div_eq_mul_inv, mul_inv_rev]
      ring
    linear_combination sourceMode true u r * sourceMode true v r * hc +
      sourceMode true u r * sourceMode true v r * halg +
      sourceMode true u r * sourceMode true v r * (rationalT u v r - correction r) *
        hD u +
      sourceMode true u r * sourceMode true v r * (rationalT u v r - correction r) *
        hD v

private lemma W_square {u r : ℂ} (hu : ‖u‖ + ‖r‖ < 1) :
    W u r ^ 2 * b u = a u r := by
  have hbu : b u ≠ 0 := (mode_factors_ne_zero hu).1
  have hau : a u r ≠ 0 := (mode_factors_ne_zero hu).2.1
  unfold W
  rw [mul_pow, (sourceMode_square hu).1]
  change a u r ^ 2 * (1 / (b u * a u r)) * b u = a u r
  field_simp [hbu, hau]

private lemma W_zero {u : ℂ} (hu : ‖u‖ < 1) : W u 0 = 1 := by
  have hs := (sourceAmplitude_generators (u := u) (x := 0) (by simpa using hu)).1.tsum_eq
  change sourceMode true u 0 = _ at hs
  have hbu : 1 - u ≠ 0 := (mode_factors_ne_zero (x := 0) (by simpa using hu)).1
  unfold W a
  rw [hs]
  simp only [sub_zero, zero_mul, zero_div, add_zero, Complex.one_cpow, mul_one, one_mul]
  exact mul_one_div_cancel hbu

private lemma W_sum_ne_zero {u v r : ℂ}
    (hu : ‖u‖ + ‖r‖ < 1) (hv : ‖v‖ + ‖r‖ < 1) :
    W u r + W v r ≠ 0 := by
  by_cases hr : r = 0
  · subst r
    rw [W_zero (by simpa using hu), W_zero (by simpa using hv)]
    norm_num
  intro hs
  have hsq : W u r ^ 2 = W v r ^ 2 := by
    rw [eq_neg_of_add_eq_zero_left hs]
    ring
  have hU := W_square hu
  have hV := W_square hv
  have hprod : r * (u - v) = 0 := by
    calc
      r * (u - v) = b v * a u r - b u * a v r := by unfold a b; ring
      _ = 0 := by rw [← hU, ← hV, hsq]; ring
  have huv : u = v := sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hr)
  subst v
  have hwu : W u r ≠ 0 := by
    intro hz
    simp only [hz, zero_pow (by decide : 2 ≠ 0), zero_mul] at hU
    exact (mode_factors_ne_zero hu).2.1 hU.symm
  apply hwu
  linear_combination (1 / 2 : ℂ) * hs

private lemma candidateJ_chart {u v r : ℂ}
    (hu : ‖u‖ + ‖r‖ < 1) (hv : ‖v‖ + ‖r‖ < 1)
    (hs : W u r + W v r ≠ 0) (hd : u - v ≠ 0) :
    candidateJ u v r = sourceMode true u r * sourceMode true v r *
      (rationalJ u v r - correction r) - cauchy u v := by
  have hbu : b u ≠ 0 := (mode_factors_ne_zero hu).1
  have hbv : b v ≠ 0 := (mode_factors_ne_zero hv).1
  have hau : a u r ≠ 0 := (mode_factors_ne_zero hu).2.1
  have hav : a v r ≠ 0 := (mode_factors_ne_zero hv).2.1
  have hU := W_square hu
  have hV := W_square hv
  have hwu : W u r ≠ 0 := by intro hz; simp [hz] at hU; exact hau hU.symm
  have hwv : W v r ≠ 0 := by intro hz; simp [hz] at hV; exact hav hV.symm
  have hNu : sourceMode true u r * b u * W u r = 1 := by
    calc
      _ = sourceMode true u r ^ 2 * (b u * a u r) := by unfold W; ring
      _ = 1 := by rw [(sourceMode_square hu).1]; exact one_div_mul_cancel (mul_ne_zero hbu hau)
  have hNv : sourceMode true v r * b v * W v r = 1 := by
    calc
      _ = sourceMode true v r ^ 2 * (b v * a v r) := by unfold W; ring
      _ = 1 := by rw [(sourceMode_square hv).1]; exact one_div_mul_cancel (mul_ne_zero hbv hav)
  have hB : sourceMode true u r * sourceMode true v r =
      1 / (b u * b v * W u r * W v r) := by
    apply (eq_div_iff (by aesop : b u * b v * W u r * W v r ≠ 0)).2
    calc
      _ = (sourceMode true u r * b u * W u r) *
        (sourceMode true v r * b v * W v r) := by ring
      _ = 1 := by rw [hNu, hNv, one_mul]
  have hdiff : W u r - W v r = r * (u - v) / (b u * b v * (W u r + W v r)) := by
    apply (eq_div_iff (mul_ne_zero (mul_ne_zero hbu hbv) hs)).2
    have hpoly : b v * a u r - b u * a v r = r * (u - v) := by unfold a b; ring
    linear_combination b v * hU - b u * hV + hpoly
  have hchart : sourceMode true u r * sourceMode true v r * rationalJ u v r - cauchy u v =
      (W u r - W v r) * (u * W u r - v * W v r) /
        (2 * (u - v) ^ 2 * W u r * W v r) := by
    rw [hB]
    unfold rationalJ cauchy
    rw [← hU, ← hV]
    field_simp [hbu, hbv, hwu, hwv, hd]
    ring
  have hlin : u * W u r - v * W v r =
      ((u - v) * (W u r + W v r) + (u + v) * (W u r - W v r)) / 2 := by ring
  have hregular : sourceMode true u r * sourceMode true v r * rationalJ u v r - cauchy u v =
      sourceMode true u r * sourceMode true v r *
        (r / 4 + r ^ 2 * (u + v) / (4 * b u * b v * (W u r + W v r) ^ 2)) := by
    rw [hchart, hlin, hdiff, hB]
    field_simp [hbu, hbv, hwu, hwv, hs, hd]
    ring
  unfold candidateJ
  linear_combination -hregular

private lemma W_continuous {u r : ℂ} (hu : ‖u‖ + ‖r‖ < 1) :
    ContinuousAt (fun w => W w r) u := by
  exact (show ContinuousAt (fun w => a w r) u by unfold a; fun_prop).mul
    (source_u hu).continuousAt

/-- The regular candidate is holomorphic in either external coordinate even on the diagonal.
Its off-diagonal value is the Cauchy-subtracted source expression. -/
theorem candidateJ_regular {u v r : ℂ}
    (hu : ‖u‖ + ‖r‖ < 1) (hv : ‖v‖ + ‖r‖ < 1) :
    DifferentiableAt ℂ (fun w => candidateJ w v r) u ∧
    DifferentiableAt ℂ (fun w => candidateJ u w r) v ∧
    (u - v ≠ 0 → candidateJ u v r =
      sourceMode true u r * sourceMode true v r * (rationalJ u v r - correction r) -
        cauchy u v) := by
  have hs := W_sum_ne_zero hu hv
  have hbu : b u ≠ 0 := (mode_factors_ne_zero hu).1
  have hbv : b v ≠ 0 := (mode_factors_ne_zero hv).1
  have hWu : DifferentiableAt ℂ (fun w => W w r) u :=
    (show DifferentiableAt ℂ (fun w => a w r) u by unfold a; fun_prop).mul
      (source_u hu).differentiableAt
  have hWv : DifferentiableAt ℂ (fun w => W w r) v :=
    (show DifferentiableAt ℂ (fun w => a w r) v by unfold a; fun_prop).mul
      (source_u hv).differentiableAt
  have hden : 4 * b u * b v * (W u r + W v r) ^ 2 ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hbu) hbv)
      (pow_ne_zero _ hs)
  refine ⟨?_, ?_, candidateJ_chart hu hv hs⟩
  · unfold candidateJ
    apply ((source_u hu).differentiableAt.mul_const _).mul
    apply DifferentiableAt.const_add
    apply DifferentiableAt.div
    · fun_prop
    · exact (((show DifferentiableAt ℂ (fun w => b w) u by unfold b; fun_prop).const_mul
        4).mul_const (b v)).mul ((hWu.add_const (W v r)).pow 2)
    · exact hden
  · unfold candidateJ
    apply ((source_u hv).differentiableAt.const_mul _).mul
    apply DifferentiableAt.const_add
    apply DifferentiableAt.div
    · fun_prop
    · exact ((show DifferentiableAt ℂ (fun w => b w) v by unfold b; fun_prop).const_mul
        (4 * b u)).mul ((hWv.const_add (W u r)).pow 2)
    · exact hden

private def jU (u v r : ℂ) : ℂ :=
  ((b v * (1 - 2 * (1 - r) * u) - v * a v r) * (u - v) -
    2 * (u * b v * a u r + v * b u * a v r)) / (2 * (u - v) ^ 3)
private def cU (u v : ℂ) : ℂ := 1 / (2 * (u - v) ^ 2) - (u + v) / (u - v) ^ 3
private def chartJ (u v r : ℂ) : ℂ :=
  sourceMode true u r * sourceMode true v r * (rationalJ u v r - correction r) - cauchy u v

private lemma rationalJ_comm (u v r : ℂ) : rationalJ u v r = rationalJ v u r := by
  unfold rationalJ
  congr 1 <;> ring
private lemma cauchy_comm (u v : ℂ) : cauchy u v = cauchy v u := by
  unfold cauchy
  congr 1 <;> ring

private lemma rationalJ_u {u v r : ℂ} (hd : u - v ≠ 0) :
    HasDerivAt (fun w => rationalJ w v r) (jU u v r) u := by
  have hA : HasDerivAt (fun w => a w r) (-(1 - r)) u := by
    convert ((hasDerivAt_id u).const_mul (1 - r)).const_sub 1 using 1 <;>
      (try (apply funext; intro w)) <;> (try simp only [a, id_eq]) <;> ring
  have hB : HasDerivAt b (-1) u := (hasDerivAt_id u).const_sub 1
  have hN := (((hasDerivAt_id u).mul_const (b v)).mul hA).add
    ((hB.const_mul v).mul_const (a v r))
  have hden := (((hasDerivAt_id u).sub_const v).pow 2).const_mul 2
  apply (hN.div hden (mul_ne_zero (by norm_num) (pow_ne_zero _ hd))).congr_deriv
  simp only [jU, Pi.pow_apply, Pi.mul_apply, Pi.add_apply, id_eq,
    Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp [hd]
  unfold a b
  ring

private lemma rationalJ_v {u v r : ℂ} (hd : u - v ≠ 0) :
    HasDerivAt (fun w => rationalJ u w r) (jU v u r) v := by
  simpa only [rationalJ_comm u] using
    (rationalJ_u (u := v) (v := u) (r := r) (sub_ne_zero.mpr (sub_ne_zero.mp hd).symm))

private lemma cauchy_u {u v : ℂ} (hd : u - v ≠ 0) :
    HasDerivAt (fun w => cauchy w v) (cU u v) u := by
  apply (((hasDerivAt_id u).add_const v).div
    ((((hasDerivAt_id u).sub_const v).pow 2).const_mul 2)
      (mul_ne_zero (by norm_num) (pow_ne_zero _ hd))).congr_deriv
  simp only [cU, Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp [hd] <;> ring

private lemma cauchy_v {u v : ℂ} (hd : u - v ≠ 0) :
    HasDerivAt (fun w => cauchy u w) (cU v u) v := by
  simpa only [cauchy_comm u] using
    (cauchy_u (u := v) (v := u) (sub_ne_zero.mpr (sub_ne_zero.mp hd).symm))

private lemma rationalJ_spatial {u v r : ℂ}
    (ha : a u r ≠ 0) (hb : a v r ≠ 0) (hd : u - v ≠ 0) :
    u * b u * jU u v r + v * b v * jU v u r +
      (modeA true u r + modeA true v r) * rationalJ u v r =
        (1 - r) * (D u r * D v r - b u * b v) / 4 := by
  have hd' : v - u ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp hd).symm
  unfold jU rationalJ D
  simp only [modeA, ite_true, ← a_formula]
  field_simp [ha, hb, hd, hd']
  unfold a b
  ring

private lemma cauchy_spatial {u v : ℂ} (hd : u - v ≠ 0) :
    u * b u * cU u v + v * b v * cU v u +
      ((1 - 3 * u) / 2 + (1 - 3 * v) / 2) * cauchy u v = -(1 / 4 : ℂ) := by
  have hd' : v - u ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp hd).symm
  unfold cU cauchy
  field_simp [hd, hd']
  unfold b
  ring

private lemma candidateJ_u {u v r : ℂ}
    (hu : ‖u‖ + ‖r‖ < 1) (hv : ‖v‖ + ‖r‖ < 1)
    (hs : W u r + W v r ≠ 0) (hd : u - v ≠ 0) :
    HasDerivAt (fun w => candidateJ w v r)
      (sourceMode true u r * sourceMode true v r *
        (jU u v r + mLog u r * (rationalJ u v r - correction r)) - cU u v) u := by
  have hc : HasDerivAt (fun w => chartJ w v r) _ u :=
    (((source_u hu).mul_const (sourceMode true v r)).mul
      ((rationalJ_u hd).sub_const (correction r))).sub (cauchy_u hd)
  have heq : (fun w => candidateJ w v r) =ᶠ[nhds u] (fun w => chartJ w v r) := by
    have hn : ∀ᶠ w : ℂ in nhds u, ‖w‖ + ‖r‖ < 1 :=
      (continuous_norm.continuousAt.add continuousAt_const).eventually (gt_mem_nhds hu)
    have hsn := ((W_continuous hu).add continuousAt_const).eventually_ne hs
    have hdn := (continuousAt_id.sub continuousAt_const).eventually_ne hd
    filter_upwards [hn, hsn, hdn] with w hw hsw hdw
    exact candidateJ_chart hw hv hsw hdw
  apply (hc.congr_of_eventuallyEq heq).congr_deriv
  try simp only [Pi.mul_apply, Pi.sub_apply, id_eq]
  ring

private lemma candidateJ_v {u v r : ℂ}
    (hu : ‖u‖ + ‖r‖ < 1) (hv : ‖v‖ + ‖r‖ < 1)
    (hs : W u r + W v r ≠ 0) (hd : u - v ≠ 0) :
    HasDerivAt (fun w => candidateJ u w r)
      (sourceMode true u r * sourceMode true v r *
        (jU v u r + mLog v r * (rationalJ u v r - correction r)) - cU v u) v := by
  have hc : HasDerivAt (fun w => chartJ u w r) _ v :=
    (((source_u hv).const_mul (sourceMode true u r)).mul
      ((rationalJ_v hd).sub_const (correction r))).sub (cauchy_v hd)
  have heq : (fun w => candidateJ u w r) =ᶠ[nhds v] (fun w => chartJ u w r) := by
    have hn : ∀ᶠ w : ℂ in nhds v, ‖w‖ + ‖r‖ < 1 :=
      (continuous_norm.continuousAt.add continuousAt_const).eventually (gt_mem_nhds hv)
    have hsn := ((W_continuous hv).const_add (W u r)).eventually_ne hs
    have hdn := (continuousAt_const.sub continuousAt_id).eventually_ne hd
    filter_upwards [hn, hsn, hdn] with w hw hsw hdw
    exact candidateJ_chart hu hw hsw hdw
  apply (hc.congr_of_eventuallyEq heq).congr_deriv
  try simp only [Pi.mul_apply, Pi.sub_apply, id_eq]
  ring

/-- The regular J candidate satisfies the original positive spatial equation off the diagonal. -/
private theorem candidateJ_off_diagonal {u v r : ℂ}
    (hu : ‖u‖ + ‖r‖ < 1) (hv : ‖v‖ + ‖r‖ < 1)
    (hs : W u r + W v r ≠ 0) (hd : u - v ≠ 0) :
    let lam := OriginalGaussianAllIndexResolvent.shiftedCentralDerivative r 0 / period r
    L (fun w => candidateJ w v r) u + L (fun w => candidateJ u w r) v =
      (1 - r) * sourceMode true u r * sourceMode true v r *
        (modeA true u r * modeH true v r lam + modeH true u r lam * modeA true v r) / 2 +
          1 / 4 := by
  have hr : ‖r‖ < 1 := by linarith [norm_nonneg u]
  dsimp only
  rw [← ell_source hr]
  unfold L
  rw [(candidateJ_u hu hv hs hd).deriv, (candidateJ_v hu hv hs hd).deriv]
  dsimp only
  rw [candidateJ_chart hu hv hs hd]
  have hbu : b u ≠ 0 := (mode_factors_ne_zero hu).1
  have hbv : b v ≠ 0 := (mode_factors_ne_zero hv).1
  have hau : a u r ≠ 0 := (mode_factors_ne_zero hu).2.1
  have hav : a v r ≠ 0 := (mode_factors_ne_zero hv).2.1
  have hc := rationalJ_spatial hau hav hd
  have hC := cauchy_spatial hd
  have halg : (1 - r) * (D u r * D v r - b u * b v) / 4 -
      (modeA true u r + modeA true v r) * correction r =
      (1 - r) * (modeA true u r * modeH true v r (ell r) +
        modeH true u r (ell r) * modeA true v r) / 2 := by
    simp only [modeH, modeA, modeScale, ite_true, correction, D, ← a_formula]
    field_simp [hau, hav]
    unfold a b
    ring
  linear_combination sourceMode true u r * sourceMode true v r * hc +
    sourceMode true u r * sourceMode true v r * halg - hC +
    sourceMode true u r * sourceMode true v r * (rationalJ u v r - correction r) *
      source_frequency hbu hau +
    sourceMode true u r * sourceMode true v r * (rationalJ u v r - correction r) *
      source_frequency hbv hav

private lemma source_analytic {u r : ℂ} (hu : ‖u‖ + ‖r‖ < 1) :
    AnalyticAt ℂ (fun w => sourceMode true w r) u := by
  have hon : DifferentiableOn ℂ (fun w => sourceMode true w r)
      (Metric.ball 0 (1 - ‖r‖)) := by
    intro w hw
    exact (source_u (show ‖w‖ + ‖r‖ < 1 by
      have hh : ‖w‖ < 1 - ‖r‖ := by simpa using hw
      linarith)).differentiableAt.differentiableWithinAt
  exact hon.analyticOnNhd Metric.isOpen_ball u (by
    change dist u 0 < 1 - ‖r‖
    simpa only [dist_zero_right] using (show ‖u‖ < 1 - ‖r‖ by linarith))

private lemma candidateJ_joint_analytic {u v r : ℂ}
    (hu : ‖u‖ + ‖r‖ < 1) (hv : ‖v‖ + ‖r‖ < 1)
    (hs : W u r + W v r ≠ 0) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => candidateJ p.1 p.2 r) (u, v) := by
  have hMu : AnalyticAt ℂ (fun p : ℂ × ℂ => sourceMode true p.1 r) (u, v) :=
    AnalyticAt.comp (f := fun p : ℂ × ℂ => p.1) (x := (u, v))
      (source_analytic hu) analyticAt_fst
  have hMv : AnalyticAt ℂ (fun p : ℂ × ℂ => sourceMode true p.2 r) (u, v) :=
    AnalyticAt.comp (f := fun p : ℂ × ℂ => p.2) (x := (u, v))
      (source_analytic hv) analyticAt_snd
  have hWu : AnalyticAt ℂ (fun p : ℂ × ℂ => W p.1 r) (u, v) :=
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_fst)).mul hMu
  have hWv : AnalyticAt ℂ (fun p : ℂ × ℂ => W p.2 r) (u, v) :=
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_snd)).mul hMv
  have hbu : b u ≠ 0 := (mode_factors_ne_zero hu).1
  have hbv : b v ≠ 0 := (mode_factors_ne_zero hv).1
  unfold candidateJ
  apply (hMu.mul hMv).mul
  apply analyticAt_const.add
  apply AnalyticAt.div
  · exact analyticAt_const.mul (analyticAt_fst.add analyticAt_snd)
  · exact ((analyticAt_const.mul (analyticAt_const.sub analyticAt_fst)).mul
      (analyticAt_const.sub analyticAt_snd)).mul
        ((hWu.add hWv).pow 2)
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hbu) hbv)
      (pow_ne_zero _ hs)

private lemma candidateJ_partials {u v r : ℂ}
    (hu : ‖u‖ + ‖r‖ < 1) (hv : ‖v‖ + ‖r‖ < 1)
    (hs : W u r + W v r ≠ 0) :
    deriv (fun w => candidateJ w v r) u =
        fderiv ℂ (fun p : ℂ × ℂ => candidateJ p.1 p.2 r) (u, v) (1, 0) ∧
    deriv (fun w => candidateJ u w r) v =
        fderiv ℂ (fun p : ℂ × ℂ => candidateJ p.1 p.2 r) (u, v) (0, 1) := by
  have hf := (candidateJ_joint_analytic hu hv hs).differentiableAt.hasFDerivAt
  constructor
  · exact (hf.comp_hasDerivAt u ((hasDerivAt_id u).prodMk (hasDerivAt_const u v))).deriv
  · exact (hf.comp_hasDerivAt v ((hasDerivAt_const v u).prodMk (hasDerivAt_id v))).deriv

/-- The original positive spatial equation also holds on the removable diagonal. -/
theorem candidateJ_differential {u v r : ℂ}
    (hu : ‖u‖ + ‖r‖ < 1) (hv : ‖v‖ + ‖r‖ < 1) :
    let lam := OriginalGaussianAllIndexResolvent.shiftedCentralDerivative r 0 / period r
    L (fun w => candidateJ w v r) u + L (fun w => candidateJ u w r) v =
      (1 - r) * sourceMode true u r * sourceMode true v r *
        (modeA true u r * modeH true v r lam + modeH true u r lam * modeA true v r) / 2 +
          1 / 4 := by
  have hs := W_sum_ne_zero hu hv
  by_cases hd : u - v ≠ 0
  · exact candidateJ_off_diagonal hu hv hs hd
  have huv : v = u := (sub_eq_zero.mp (not_ne_iff.mp hd)).symm
  subst v
  let F : ℂ × ℂ → ℂ := fun p => candidateJ p.1 p.2 r
  let lam := OriginalGaussianAllIndexResolvent.shiftedCentralDerivative r 0 / period r
  let R : ℂ → ℂ := fun w =>
    w * b w * fderiv ℂ F (w, u) (1, 0) + (1 - 3 * w) / 2 * F (w, u) +
    (u * b u * fderiv ℂ F (w, u) (0, 1) + (1 - 3 * u) / 2 * F (w, u)) -
    ((1 - r) * sourceMode true w r * sourceMode true u r *
      (modeA true w r * modeH true u r lam + modeH true w r lam * modeA true u r) / 2 + 1 / 4)
  have hf : AnalyticAt ℂ F (u, u) := candidateJ_joint_analytic hu hu hs
  have hp : ContinuousAt (fun w : ℂ => (w, u)) u := continuousAt_id.prodMk continuousAt_const
  have hcD : ContinuousAt (fun w => fderiv ℂ F (w, u)) u :=
    ContinuousAt.comp (g := fderiv ℂ F) (f := fun w : ℂ => (w, u))
      hf.fderiv.continuousAt hp
  have hD₁ : ContinuousAt (fun w => fderiv ℂ F (w, u) (1, 0)) u :=
    hcD.clm_apply continuousAt_const
  have hD₂ : ContinuousAt (fun w => fderiv ℂ F (w, u) (0, 1)) u :=
    hcD.clm_apply continuousAt_const
  have hF : ContinuousAt (fun w => F (w, u)) u :=
    ContinuousAt.comp (g := F) (f := fun w : ℂ => (w, u)) hf.continuousAt hp
  have hM := (source_u hu).continuousAt
  have ha : 1 - (1 - r) * u ≠ 0 := (mode_factors_ne_zero hu).2.1
  have hA : ContinuousAt (fun w => modeA true w r) u := by
    simp only [modeA, ite_true]
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact mul_ne_zero (by norm_num) ha
  have hH : ContinuousAt (fun w => modeH true w r lam) u := by
    simp only [modeH, modeScale, ite_true]
    have hn : ContinuousAt (fun w : ℂ => -r * w) u :=
      continuousAt_const.mul continuousAt_id
    have hd : ContinuousAt (fun w : ℂ => 1 - (1 - r) * w) u :=
      continuousAt_const.sub (continuousAt_const.mul continuousAt_id)
    exact ((hn.div hd ha).sub hA).sub continuousAt_const
  have hR : ContinuousAt R u := by
    dsimp only [R]
    have hb : Continuous b := by unfold b; fun_prop
    fun_prop
  have heq : R =ᶠ[nhdsWithin u {u}ᶜ] (fun _ => 0) := by
    have hn : ∀ᶠ w : ℂ in nhds u, ‖w‖ + ‖r‖ < 1 :=
      (continuous_norm.continuousAt.add continuousAt_const).eventually (gt_mem_nhds hu)
    have hsn := ((W_continuous hu).add continuousAt_const).eventually_ne hs
    filter_upwards [hn.filter_mono nhdsWithin_le_nhds,
      hsn.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw hsw hdw
    have hder := candidateJ_partials hw hu hsw
    have he := candidateJ_off_diagonal hw hu hsw (sub_ne_zero.mpr hdw)
    dsimp only at he
    unfold L at he
    dsimp only at he
    rw [hder.1, hder.2] at he
    exact sub_eq_zero.mpr he
  have hz : R u = 0 := tendsto_nhds_unique
    (hR.tendsto.mono_left nhdsWithin_le_nhds)
    (tendsto_const_nhds.congr' heq.symm)
  have hder := candidateJ_partials hu hu hs
  dsimp only [R, F, lam] at hz
  dsimp only
  unfold L
  dsimp only
  rw [hder.1, hder.2]
  exact sub_eq_zero.mp hz

private lemma E_ne_zero {u v r : ℂ}
    (hu : ‖u‖ + Real.sqrt ‖r‖ < 1) (hv : ‖v‖ + Real.sqrt ‖r‖ < 1) :
    E u v r ≠ 0 := by
  have ht : 0 ≤ Real.sqrt ‖r‖ := Real.sqrt_nonneg _
  have hsq : (Real.sqrt ‖r‖) ^ 2 = ‖r‖ := Real.sq_sqrt (norm_nonneg r)
  have hbound (w : ℂ) (hw : ‖w‖ + Real.sqrt ‖r‖ < 1) :
      Real.sqrt ‖r‖ * ‖w‖ < ‖b w‖ := by
    have hw1 : ‖w‖ ≤ 1 := by linarith
    have hm := mul_le_of_le_one_right ht hw1
    have hn : 1 - ‖w‖ ≤ ‖b w‖ := by
      simpa only [norm_one, b] using norm_sub_norm_le (1 : ℂ) w
    linarith
  have hu' := hbound u hu
  have hv' := hbound v hv
  have hp : ‖r * u * v‖ < ‖b u * b v‖ := by
    rw [norm_mul, norm_mul, norm_mul]
    calc
      ‖r‖ * ‖u‖ * ‖v‖ =
          (Real.sqrt ‖r‖) ^ 2 * ‖u‖ * ‖v‖ := by rw [hsq]
      _ = (Real.sqrt ‖r‖ * ‖u‖) * (Real.sqrt ‖r‖ * ‖v‖) := by ring
      _ ≤ ‖b u‖ * (Real.sqrt ‖r‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_right hu'.le (mul_nonneg ht (norm_nonneg v))
      _ < ‖b u‖ * ‖b v‖ := mul_lt_mul_of_pos_left hv'
        (lt_of_le_of_lt (mul_nonneg ht (norm_nonneg u)) hu')
  intro he
  have heq : b u * b v = r * u * v := by
    unfold E at he
    unfold b
    linear_combination he
  exact (ne_of_lt hp) (congrArg norm heq).symm

/-- The original convergence bidiscs suffice for both candidate T equations;
no chart denominator, nonzero coordinate or off-diagonal premise is needed. -/
theorem candidateT_original_differential {u v : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1)
    (hu : ‖u‖ + Real.sqrt r < 1) (hv : ‖v‖ + Real.sqrt r < 1) :
    let x : ℂ := r
    let lam := OriginalGaussianAllIndexResolvent.shiftedCentralDerivative x 0 / period x
    (L (fun w => candidateT w v x) u - L (fun w => candidateT u w x) v =
      (1 - x) * sourceMode true u x * sourceMode true v x *
        (modeA true u x * modeH true v x lam - modeH true u x lam * modeA true v x) / 2) ∧
    (2 * x * deriv (fun t : ℝ => candidateT u v (t : ℂ)) r -
        L (fun w => candidateT w v x) u - L (fun w => candidateT u w x) v =
      (1 - x) * sourceMode true u x * sourceMode true v x *
        (modeH true u x lam * modeH true v x lam - modeA true u x * modeA true v x) / 2) := by
  have hnr : ‖(r : ℂ)‖ = r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  have hrs : r ≤ Real.sqrt r := by
    have hsq := Real.sq_sqrt hr
    have hn := Real.sqrt_nonneg r
    have hl : Real.sqrt r ≤ 1 := (Real.sqrt_le_one).mpr hr1.le
    nlinarith
  have hu' : ‖u‖ + ‖(r : ℂ)‖ < 1 := by rw [hnr]; linarith
  have hv' : ‖v‖ + ‖(r : ℂ)‖ < 1 := by rw [hnr]; linarith
  have he : E u v (r : ℂ) ≠ 0 :=
    E_ne_zero (by simpa only [hnr] using hu) (by simpa only [hnr] using hv)
  have hd := candidateT_r hu' hv' he
  have hreal : deriv (fun t : ℝ => candidateT u v (t : ℂ)) r =
      deriv (fun w : ℂ => candidateT u v w) (r : ℂ) :=
    hd.comp_ofReal.deriv.trans hd.deriv.symm
  dsimp only
  rw [hreal]
  exact candidateT_differential hu' hv' he

open scoped BigOperators ENNReal
open Filter Set
open OriginalGaussianResolvent OriginalGaussianExternalResolvent
open OriginalGaussianDifferentiation OriginalGaussianAllIndexResolvent
open OriginalGaussianBilinearTranspose OriginalGaussianExternalNormal
open OriginalGaussianExternalEquations

-- Continuous bilinear source pairing for the actual vector mode sums.
private def pairing : H →L[ℂ] H →L[ℂ] ℂ :=
  ({ toFun := sourceBilinearFunctional
     map_add' := by
       intro x y
       ext w
       rw [sourceBilinearFunctional_comm (x + y) w, map_add]
       simp only [add_apply]
       rw [sourceBilinearFunctional_comm w x, sourceBilinearFunctional_comm w y]
     map_smul' := by
       intro a x
       ext w
       simp only [RingHom.id_apply, smul_apply, smul_eq_mul]
       exact sourceBilinearFunctional_smul_left a x w } : H →ₗ[ℂ] H →L[ℂ] ℂ).mkContinuous
    1 (by
      intro x
      change ‖sourceBilinearFunctional x‖ ≤ 1 * ‖x‖
      simp only [sourceBilinearFunctional, innerSL_apply_norm, norm_star, one_mul, le_refl])

private def modeVector (out : Bool) (u z : ℂ) : H :=
  ∑' p : ℕ, u ^ p • externalVector out p z

-- Banach-valued holomorphy follows from local normal convergence.
private lemma modeVector_differentiable (out : Bool) {u z : ℂ}
    (hu : ‖u‖ + ‖z‖ < 1) : DifferentiableAt ℂ (fun w => modeVector out w z) u := by
  obtain ⟨R, huR, hR⟩ := exists_between (show ‖u‖ < 1 - ‖z‖ by linarith)
  have hR0 : 0 < R := lt_of_le_of_lt (norm_nonneg u) huR
  have hs := externalVector_mode_summable out (u := (R : ℂ)) (z := z)
    (by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0] using
      (show R + ‖z‖ < 1 by linarith))
  have hd (p : ℕ) : DifferentiableOn ℂ
      (fun w : ℂ => w ^ p • externalVector out p z) (Metric.ball 0 R) := by
    intro w _
    exact ((hasDerivAt_pow p w).smul_const _).differentiableAt.differentiableWithinAt
  have hb (p : ℕ) (w : ℂ) (hw : w ∈ Metric.ball 0 R) :
      ‖w ^ p • externalVector out p z‖ ≤ ‖(R : ℂ) ^ p • externalVector out p z‖ := by
    simp only [norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0]
    gcongr
    exact (show ‖w‖ < R by simpa using hw).le
  exact (Complex.differentiableOn_tsum_of_summable_norm hs hd Metric.isOpen_ball hb)
    |>.differentiableAt (Metric.isOpen_ball.mem_nhds (by simpa using huR))

-- Two map_tsum applications factor the actual original kernel.
private lemma kernelMode_pairing (square out out' : Bool) {u v z : ℂ}
    (hu : ‖u‖ + ‖z‖ < 1) (hv : ‖v‖ + ‖z‖ < 1) :
    kernelMode square out out' u v z =
      pairing (modeVector out u z)
        ((if square then squareResolvent z else oddResolvent z) (modeVector out' v z)) := by
  let A : H →L[ℂ] H := if square then squareResolvent z else oddResolvent z
  let c : ℕ × ℕ → ℂ := fun pq =>
    if square then externalT out pq.1 out' pq.2 z else externalJ out pq.1 out' pq.2 z
  have hz : ‖z‖ < 1 := by linarith [norm_nonneg u]
  have hp := (externalVector_mode_summable out hu).of_norm
  have hq := (externalVector_mode_summable out' hv).of_norm
  have hc : Summable (fun pq : ℕ × ℕ => c pq * u ^ pq.1 * v ^ pq.2) := by
    have h := external_kernel_mode_summable out out' hu hv
    cases square
    · simpa only [c, Bool.false_eq_true, ite_false, norm_mul, mul_comm,
        mul_left_comm, mul_assoc] using h.1.of_norm
    · simpa only [c, ite_true, norm_mul, mul_comm, mul_left_comm, mul_assoc] using h.2.of_norm
  have he (p q : ℕ) :
      pairing (externalVector out p z) (A (externalVector out' q z)) = c (p, q) := by
    change sourceBilinearFunctional (externalVector out p z) (A (externalVector out' q z)) = _
    cases square
    · exact (external_contractions_explicit out p out' q hz).2.2.1
    · exact (external_contractions_explicit out p out' q hz).2.2.2.1
  symm
  calc
    _ = ∑' p : ℕ, pairing (u ^ p • externalVector out p z) (A (modeVector out' v z)) :=
      (pairing.flip (A (modeVector out' v z))).map_tsum hp
    _ = ∑' p : ℕ, ∑' q : ℕ,
        pairing (u ^ p • externalVector out p z) (A (v ^ q • externalVector out' q z)) := by
      apply tsum_congr
      intro p
      exact ((pairing (u ^ p • externalVector out p z)).comp A).map_tsum hq
    _ = ∑' p : ℕ, ∑' q : ℕ, c (p, q) * u ^ p * v ^ q := by
      apply tsum_congr
      intro p
      apply tsum_congr
      intro q
      simp only [map_smul, smul_apply, smul_eq_mul]
      rw [he]
      ring
    _ = _ := hc.tsum_prod.symm

-- The original kernel regularity follows from its actual vector mode sums.
private theorem kernelMode_joint_differentiable (square out out' : Bool) {u v z : ℂ}
    (hu : ‖u‖ + ‖z‖ < 1) (hv : ‖v‖ + ‖z‖ < 1) :
    DifferentiableAt ℂ (fun p : ℂ × ℂ => kernelMode square out out' p.1 p.2 z) (u, v) := by
  let A : H →L[ℂ] H := if square then squareResolvent z else oddResolvent z
  have hfst : DifferentiableAt ℂ (fun p : ℂ × ℂ => p.1) (u, v) :=
    differentiableAt_fst
  have hsnd : DifferentiableAt ℂ (fun p : ℂ × ℂ => p.2) (u, v) :=
    differentiableAt_snd
  have hX := (modeVector_differentiable out hu).comp (u, v) hfst
  have hY := A.differentiableAt.comp (u, v)
    ((modeVector_differentiable out' hv).comp (u, v) hsnd)
  have h := (pairing.hasFDerivAt_of_bilinear hX.hasFDerivAt hY.hasFDerivAt).differentiableAt
  apply h.congr_of_eventuallyEq
  have hnu : ∀ᶠ p : ℂ × ℂ in 𝓝 (u, v), ‖p.1‖ + ‖z‖ < 1 :=
    (continuous_fst.norm.add continuous_const).continuousAt.eventually (gt_mem_nhds hu)
  have hnv : ∀ᶠ p : ℂ × ℂ in 𝓝 (u, v), ‖p.2‖ + ‖z‖ < 1 :=
    (continuous_snd.norm.add continuous_const).continuousAt.eventually (gt_mem_nhds hv)
  filter_upwards [hnu, hnv] with p hp hq
  exact kernelMode_pairing square out out' hp hq

private lemma joint_partials {F : ℂ × ℂ → ℂ} {u v : ℂ}
    (hf : DifferentiableAt ℂ F (u, v)) :
    deriv (fun w => F (w, v)) u = fderiv ℂ F (u, v) (1, 0) ∧
    deriv (fun w => F (u, w)) v = fderiv ℂ F (u, v) (0, 1) := by
  constructor
  · exact (hf.hasFDerivAt.comp_hasDerivAt u
      ((hasDerivAt_id u).prodMk (hasDerivAt_const u v))).deriv
  · exact (hf.hasFDerivAt.comp_hasDerivAt v
      ((hasDerivAt_const v u).prodMk (hasDerivAt_id v))).deriv

private def characteristicDenominator (u t : ℂ) : ℂ := 1 - u + t * u
private def characteristicPath (u t : ℂ) : ℂ := t * u / characteristicDenominator u t

private lemma path_control {u : ℂ} (hu : ‖u‖ < 1) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    characteristicDenominator u (t : ℂ) ≠ 0 ∧ ‖characteristicPath u (t : ℂ)‖ ≤ ‖u‖ := by
  have hb : 1 - (1 - t) * ‖u‖ ≤ ‖characteristicDenominator u (t : ℂ)‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (((1 - t : ℝ) : ℂ) * u)
    have he : (1 : ℂ) - (((1 - t : ℝ) : ℂ) * u) = characteristicDenominator u (t : ℂ) := by
      push_cast
      unfold characteristicDenominator
      ring
    rw [he] at h
    simpa only [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ht.2)] using h
  have hpos : 0 < ‖characteristicDenominator u (t : ℂ)‖ := by
    nlinarith [norm_nonneg u, mul_nonneg ht.1 (norm_nonneg u)]
  refine ⟨norm_ne_zero_iff.mp hpos.ne', ?_⟩
  rw [characteristicPath, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
  apply (div_le_iff₀ hpos).mpr
  have htD : t ≤ ‖characteristicDenominator u (t : ℂ)‖ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hu.le)]
  nlinarith [mul_nonneg (norm_nonneg u) (sub_nonneg.mpr htD)]

private lemma phi_hasDerivAt (u t : ℂ) (hd : characteristicDenominator u t ≠ 0) :
    HasDerivAt (characteristicPath u) (u * (1 - u) / characteristicDenominator u t ^ 2) t := by
  have hD : HasDerivAt (characteristicDenominator u) u t := by
    convert ((hasDerivAt_id t).mul_const u).const_add (1 - u) using 1 <;>
      (try funext w) <;> (try simp only [characteristicDenominator, id_eq]) <;> ring
  apply (((hasDerivAt_id t).mul_const u).div hD hd).congr_deriv
  dsimp only [characteristicDenominator, id_eq]
  ring

-- The squared characteristic invariant is consumed by the actual J identification.
private theorem positive_spatial_zero {R : ℝ} (hR : R ≤ 1) (F : ℂ × ℂ → ℂ)
    (hreg : ∀ a b : ℂ, ‖a‖ < R → ‖b‖ < R → DifferentiableAt ℂ F (a, b))
    (hpde : ∀ a b : ℂ, ‖a‖ < R → ‖b‖ < R →
      a * (1 - a) * deriv (fun w => F (w, b)) a +
      b * (1 - b) * deriv (fun w => F (a, w)) b +
      (1 - 3 * (a + b) / 2) * F (a, b) = 0)
    {u v : ℂ} (hu : ‖u‖ < R) (hv : ‖v‖ < R) : F (u, v) = 0 := by
  let g : ℂ → ℂ := fun t =>
    t ^ 2 * F (characteristicPath u t, characteristicPath v t) ^ 2 / (characteristicDenominator u t ^ 3 * characteristicDenominator v t ^ 3)
  have hder (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun s : ℝ => g (s : ℂ)) 0 t := by
    have hcu := path_control (hu.trans_le hR) ht
    have hcv := path_control (hv.trans_le hR) ht
    have hpu : ‖characteristicPath u (t : ℂ)‖ < R := hcu.2.trans_lt hu
    have hpv : ‖characteristicPath v (t : ℂ)‖ < R := hcv.2.trans_lt hv
    have hf := hreg _ _ hpu hpv
    let d := fderiv ℂ F (characteristicPath u (t : ℂ), characteristicPath v (t : ℂ))
    have hpart := joint_partials hf
    have hlin (a b : ℂ) : d (a, b) = a * d (1, 0) + b * d (0, 1) := by
      have he : (a, b) = a • ((1, 0) : ℂ × ℂ) + b • ((0, 1) : ℂ × ℂ) := by
        ext <;> simp
      rw [he, map_add, map_smul, map_smul]
      rfl
    have hpath : HasDerivAt (fun s : ℂ => F (characteristicPath u s, characteristicPath v s))
        (u * (1 - u) / characteristicDenominator u (t : ℂ) ^ 2 * d (1, 0) +
          v * (1 - v) / characteristicDenominator v (t : ℂ) ^ 2 * d (0, 1)) (t : ℂ) := by
      exact (hf.hasFDerivAt.comp_hasDerivAt (t : ℂ)
        ((phi_hasDerivAt u (t : ℂ) hcu.1).prodMk
          (phi_hasDerivAt v (t : ℂ) hcv.1))).congr_deriv (hlin _ _)
    have hDu : HasDerivAt (characteristicDenominator u) u (t : ℂ) := by
      convert ((hasDerivAt_id (t : ℂ)).mul_const u).const_add (1 - u) using 1 <;>
        (try funext s) <;> (try simp only [characteristicDenominator, id_eq]) <;> ring
    have hDv : HasDerivAt (characteristicDenominator v) v (t : ℂ) := by
      convert ((hasDerivAt_id (t : ℂ)).mul_const v).const_add (1 - v) using 1 <;>
        (try funext s) <;> (try simp only [characteristicDenominator, id_eq]) <;> ring
    have he := hpde _ _ hpu hpv
    rw [hpart.1, hpart.2] at he
    have hg : HasDerivAt g 0 (t : ℂ) := by
      apply (((hasDerivAt_pow 2 (t : ℂ)).mul (hpath.pow 2)).div
        ((hDu.pow 3).mul (hDv.pow 3))
        (mul_ne_zero (pow_ne_zero _ hcu.1) (pow_ne_zero _ hcv.1))).congr_deriv
      dsimp only [Pi.mul_apply, Pi.pow_apply, id_eq]
      norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
      calc
        _ = (2 * (t : ℂ) * F (characteristicPath u (t : ℂ), characteristicPath v (t : ℂ)) /
            (characteristicDenominator u (t : ℂ) ^ 3 * characteristicDenominator v (t : ℂ) ^ 3)) *
            (characteristicPath u (t : ℂ) * (1 - characteristicPath u (t : ℂ)) * d (1, 0) +
             characteristicPath v (t : ℂ) * (1 - characteristicPath v (t : ℂ)) * d (0, 1) +
             (1 - 3 * (characteristicPath u (t : ℂ) + characteristicPath v (t : ℂ)) / 2) *
               F (characteristicPath u (t : ℂ), characteristicPath v (t : ℂ))) := by
          have hdu := hcu.1
          have hdv := hcv.1
          dsimp only [characteristicPath, characteristicDenominator] at hdu hdv ⊢
          field_simp [hdu, hdv]
          ring
        _ = 0 := by change _ * _ = 0; rw [he]; ring
    exact hg.comp_ofReal
  have hc : ContinuousOn (fun t : ℝ => g (t : ℂ)) (Icc (0 : ℝ) 1) :=
    fun t ht => (hder t ht).continuousAt.continuousWithinAt
  have hz := constant_of_has_deriv_right_zero hc
    (fun t ht => (hder t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    1 (by constructor <;> norm_num)
  have hs : F (u, v) ^ 2 = 0 := by simpa [g, characteristicPath, characteristicDenominator] using hz
  exact eq_zero_of_pow_eq_zero hs

/-- The actual positive J generator equals its analytic candidate on the full source bidisk. -/
theorem positiveJ_eq_candidateJ {u v : ℂ} {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hu : ‖u‖ + Real.sqrt r < 1) (hv : ‖v‖ + Real.sqrt r < 1) :
    kernelMode false true true u v (Real.sqrt r : ℂ) = candidateJ u v (r : ℂ) := by
  let R := 1 - Real.sqrt r
  let K : ℂ × ℂ → ℂ := fun p => kernelMode false true true p.1 p.2 (Real.sqrt r : ℂ)
  let C : ℂ × ℂ → ℂ := fun p => candidateJ p.1 p.2 (r : ℂ)
  let F : ℂ × ℂ → ℂ := K - C
  have hk (a b : ℂ) (ha : ‖a‖ < R) (hb : ‖b‖ < R) : DifferentiableAt ℂ K (a, b) := by
    apply kernelMode_joint_differentiable false true true
    · simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg r)] using
          (show ‖a‖ + Real.sqrt r < 1 by dsimp [R] at ha; linarith)
    · simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg r)] using
          (show ‖b‖ + Real.sqrt r < 1 by dsimp [R] at hb; linarith)
  have hrS : r ≤ Real.sqrt r := Real.le_sqrt_self_iff.mpr hr1.le
  have hc (a b : ℂ) (ha : ‖a‖ < R) (hb : ‖b‖ < R) : DifferentiableAt ℂ C (a, b) := by
    have har : ‖a‖ + ‖(r : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      dsimp [R] at ha
      linarith
    have hbr : ‖b‖ + ‖(r : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      dsimp [R] at hb
      linarith
    exact (candidateJ_joint_analytic har hbr (W_sum_ne_zero har hbr)).differentiableAt
  have hreg (a b : ℂ) (ha : ‖a‖ < R) (hb : ‖b‖ < R) : DifferentiableAt ℂ F (a, b) :=
    (hk a b ha hb).sub (hc a b ha hb)
  have hpde (a b : ℂ) (ha : ‖a‖ < R) (hb : ‖b‖ < R) :
      a * (1 - a) * deriv (fun w => F (w, b)) a +
      b * (1 - b) * deriv (fun w => F (a, w)) b +
      (1 - 3 * (a + b) / 2) * F (a, b) = 0 := by
    have haS : ‖a‖ + Real.sqrt r < 1 := by dsimp [R] at ha; linarith
    have hbS : ‖b‖ + Real.sqrt r < 1 := by dsimp [R] at hb; linarith
    have har : ‖a‖ + ‖(r : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]; linarith
    have hbr : ‖b‖ + ‖(r : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]; linarith
    have hK := (displacement_differential true true hr hr1 haS hbS).1
    have hC := candidateJ_differential har hbr
    have hKu := ((hk a b ha hb).hasFDerivAt.comp_hasDerivAt a
      ((hasDerivAt_id a).prodMk (hasDerivAt_const a b))).differentiableAt
    have hKv := ((hk a b ha hb).hasFDerivAt.comp_hasDerivAt b
      ((hasDerivAt_const b a).prodMk (hasDerivAt_id b))).differentiableAt
    have hCu := ((hc a b ha hb).hasFDerivAt.comp_hasDerivAt a
      ((hasDerivAt_id a).prodMk (hasDerivAt_const a b))).differentiableAt
    have hCv := ((hc a b ha hb).hasFDerivAt.comp_hasDerivAt b
      ((hasDerivAt_const b a).prodMk (hasDerivAt_id b))).differentiableAt
    change a * (1 - a) * deriv ((fun w => K (w, b)) - (fun w => C (w, b))) a +
      b * (1 - b) * deriv ((fun w => K (a, w)) - (fun w => C (a, w))) b +
      (1 - 3 * (a + b) / 2) * (K (a, b) - C (a, b)) = 0
    change DifferentiableAt ℂ (fun w => K (w, b)) a at hKu
    change DifferentiableAt ℂ (fun w => K (a, w)) b at hKv
    change DifferentiableAt ℂ (fun w => C (w, b)) a at hCu
    change DifferentiableAt ℂ (fun w => C (a, w)) b at hCv
    rw [deriv_sub hKu hCu, deriv_sub hKv hCv]
    dsimp only at hK hC
    simp only [modeScale, modeB, firstModeDerivative, secondModeDerivative,
      L, OriginalGaussianExternalAnalyticCandidate.b, ite_true, one_mul] at hK hC
    dsimp only [K, C]
    linear_combination hK - hC
  have hz := positive_spatial_zero (R := R)
    (by dsimp [R]; linarith [Real.sqrt_nonneg r]) F hreg hpde
    (u := u) (v := v) (by dsimp [R]; linarith) (by dsimp [R]; linarith)
  exact sub_eq_zero.mp hz


end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalAnalyticCandidate
