/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalAnalyticCandidate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Normalized positive Gaussian kernel candidates and their differential equations. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalCandidateCore
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianPeriodIdentity

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

private lemma correction_hasDerivAt {r : ℂ} (hr : ‖r‖ < 1) :
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

private lemma candidateJ_chart {u v r : ℂ}
    (hu : ‖u‖ + ‖r‖ < 1) (hv : ‖v‖ + ‖r‖ < 1)
    (hs : W u r + W v r ≠ 0) (hd : u - v ≠ 0) :
    candidateJ u v r = sourceMode true u r * sourceMode true v r *
      (rationalJ u v r - correction r) - cauchy u v := by
  have hbu : b u ≠ 0 := (mode_factors_ne_zero hu).1
  have hbv : b v ≠ 0 := (mode_factors_ne_zero hv).1
  have hau : a u r ≠ 0 := (mode_factors_ne_zero hu).2.1
  have hav : a v r ≠ 0 := (mode_factors_ne_zero hv).2.1
  have hU : W u r ^ 2 * b u = a u r := by
    unfold W
    rw [mul_pow, (sourceMode_square hu).1]
    change a u r ^ 2 * (1 / (b u * a u r)) * b u = a u r
    field_simp [hbu, hau]
  have hV : W v r ^ 2 * b v = a v r := by
    unfold W
    rw [mul_pow, (sourceMode_square hv).1]
    change a v r ^ 2 * (1 / (b v * a v r)) * b v = a v r
    field_simp [hbv, hav]
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
    (hu : ‖u‖ + ‖r‖ < 1) (hv : ‖v‖ + ‖r‖ < 1)
    (hs : W u r + W v r ≠ 0) :
    DifferentiableAt ℂ (fun w => candidateJ w v r) u ∧
    DifferentiableAt ℂ (fun w => candidateJ u w r) v ∧
    (u - v ≠ 0 → candidateJ u v r =
      sourceMode true u r * sourceMode true v r * (rationalJ u v r - correction r) -
        cauchy u v) := by
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
theorem candidateJ_differential {u v r : ℂ}
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

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalAnalyticCandidate
