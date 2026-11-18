/- GID: D5/S3/VertexAlgebra/TwistedGround/Signed/JSpatial
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Signed/JSpatial
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed Gaussian regularization and spatial J equation. -/

import D5.S3.VertexAlgebra.TwistedGround.Signed.CandidateSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology
namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalSignedCandidate
open OriginalGaussianExternalGenerators OriginalGaussianExternalGeneratedSource
open OriginalGaussianExternalModeSums OriginalGaussianExternalJetSums
open OriginalGaussianExternalAnalyticCandidate (b ell correction)
open D5.S3.Analytic.OriginalHalfBinomialPeriod

def G (e f : Bool) (u v : ℂ) : ℂ := if e = f then u - v else 1 - u * v
def Gu (e f : Bool) (v : ℂ) : ℂ := if e = f then 1 else -v
def Qconstant (e f : Bool) (r : ℂ) : ℂ := if e && f then 0 else r / 2

def jN (e f : Bool) (u v r : ℂ) : ℂ :=
  if e = f then u * h e u r * b v + v * b u * h f v r
  else if e then -(h e u r * b v + u * v * b u * h f v r)
  else -(u * v * h e u r * b v + b u * h f v r)

def jNu (e f : Bool) (u v r : ℂ) : ℂ :=
  if e = f then (h e u r - u * slope e r) * b v - v * h f v r
  else if e then slope e r * b v - v * (1 - 2 * u) * h f v r
  else -v * (h e u r - u * slope e r) * b v + h f v r

def rationalJ (e f : Bool) (u v r : ℂ) : ℂ :=
  Qconstant e f r + jN e f u v r / (2 * G e f u v ^ 2)
def cauchy (e f : Bool) (u v : ℂ) : ℂ := rho e f u v / (2 * G e f u v ^ 2)
def jU (e f : Bool) (u v r : ℂ) : ℂ :=
  jNu e f u v r / (2 * G e f u v ^ 2) - jN e f u v r * Gu e f v / G e f u v ^ 3
def cU (e f : Bool) (u v : ℂ) : ℂ :=
  Gu e f v / (2 * G e f u v ^ 2) - rho e f u v * Gu e f v / G e f u v ^ 3

def chartJ (e f : Bool) (u v r : ℂ) : ℂ :=
  sourceMode e u r * sourceMode f v r * (rationalJ e f u v r - correction r) - cauchy e f u v

private lemma G_ne_zero_swap (e f : Bool) {u v : ℂ} (hg : G e f u v ≠ 0) : G f e v u ≠ 0 := by
  cases e <;> cases f <;> simp only [G, Bool.false_eq_true, Bool.true_eq_false,
    ite_true, ite_false] at hg ⊢
  · exact sub_ne_zero.mpr (sub_ne_zero.mp hg).symm
  · simpa only [mul_comm] using hg
  · simpa only [mul_comm] using hg
  · exact sub_ne_zero.mpr (sub_ne_zero.mp hg).symm

private lemma Qconstant_comm (e f : Bool) (r : ℂ) : Qconstant e f r = Qconstant f e r := by
  cases e <;> cases f <;> rfl
private lemma jN_comm (e f : Bool) (u v r : ℂ) : jN e f u v r = jN f e v u r := by
  cases e <;> cases f <;> simp only [jN, Bool.false_eq_true, Bool.true_eq_false,
    ite_true, ite_false, ite_true, ite_false] <;> ring
private lemma rho_comm (e f : Bool) (u v : ℂ) : rho e f u v = rho f e v u := by
  cases e <;> cases f <;> simp only [rho, Bool.false_eq_true, Bool.true_eq_false,
    ite_true, ite_false] <;> ring
private lemma G_sq_comm (e f : Bool) (u v : ℂ) : G e f u v ^ 2 = G f e v u ^ 2 := by
  cases e <;> cases f <;> simp only [G, Bool.false_eq_true, Bool.true_eq_false,
    ite_true, ite_false] <;> ring
private lemma rationalJ_comm (e f : Bool) (u v r : ℂ) :
    rationalJ e f u v r = rationalJ f e v u r := by
  unfold rationalJ
  rw [Qconstant_comm e f r, jN_comm e f u v r, G_sq_comm e f u v]
private lemma cauchy_comm (e f : Bool) (u v : ℂ) : cauchy e f u v = cauchy f e v u := by
  unfold cauchy
  rw [rho_comm e f u v, G_sq_comm e f u v]

private lemma h_u (e : Bool) (u r : ℂ) : HasDerivAt (fun w => h e w r) (-slope e r) u := by
  cases e
  · simpa only [h, slope, Bool.false_eq_true, ite_false, id_eq] using
      (hasDerivAt_id u).const_sub (1 - r)
  · simpa only [h, slope, ite_true, mul_one, id_eq] using
      ((hasDerivAt_id u).const_mul (1 - r)).const_sub 1

private lemma G_u (e f : Bool) (u v : ℂ) : HasDerivAt (fun w => G e f w v) (Gu e f v) u := by
  by_cases hef : e = f
  · simpa only [G, Gu, if_pos hef, id_eq] using (hasDerivAt_id u).sub_const v
  · simpa only [G, Gu, if_neg hef, mul_one, one_mul, id_eq] using
      ((hasDerivAt_id u).mul_const v).const_sub 1

private lemma rho_u (e f : Bool) (u v : ℂ) : HasDerivAt (fun w => rho e f w v) (Gu e f v) u := by
  by_cases hef : e = f
  · simpa only [rho, Gu, if_pos hef, id_eq] using (hasDerivAt_id u).add_const v
  · convert (((hasDerivAt_id u).mul_const v).const_add 1).neg using 1 <;>
      (try funext w) <;> simp [rho, Gu, hef, id_eq]

private lemma jN_u (e f : Bool) (u v r : ℂ) :
    HasDerivAt (fun w => jN e f w v r) (jNu e f u v r) u := by
  have hB : HasDerivAt b (-1) u := (hasDerivAt_id u).const_sub 1
  have hA := h_u e u r
  by_cases hef : e = f
  · convert ((((hasDerivAt_id u).mul hA).mul_const (b v)).add
      ((hB.const_mul v).mul_const (h f v r))) using 1 <;>
      (try (apply funext; intro w)) <;>
      simp only [jN, jNu, if_pos hef, Pi.add_apply, Pi.mul_apply, id_eq] <;> ring
  · cases e
    · convert (((((hasDerivAt_id u).mul_const v).mul hA).mul_const (b v)).add
        (hB.mul_const (h f v r))).neg using 1 <;>
        (try (apply funext; intro w)) <;>
        simp only [jN, jNu, if_neg hef, Bool.false_eq_true, ite_false,
          Pi.neg_apply, Pi.add_apply, Pi.mul_apply, id_eq] <;> ring
    · convert (((hA.mul_const (b v)).add
        ((((hasDerivAt_id u).mul_const v).mul hB).mul_const (h f v r)))).neg using 1 <;>
        (try (apply funext; intro w)) <;>
        simp only [jN, jNu, if_neg hef, ite_true,
          Pi.neg_apply, Pi.add_apply, Pi.mul_apply, id_eq, b] <;> ring

private lemma rationalJ_u (e f : Bool) {u v r : ℂ} (hg : G e f u v ≠ 0) :
    HasDerivAt (fun w => rationalJ e f w v r) (jU e f u v r) u := by
  have hd := ((G_u e f u v).pow 2).const_mul 2
  apply (((jN_u e f u v r).div hd
    (mul_ne_zero (by norm_num) (pow_ne_zero _ hg))).const_add (Qconstant e f r)).congr_deriv
  simp only [jU, Pi.pow_apply, Pi.mul_apply, id_eq, Nat.cast_ofNat,
    Nat.reduceSub, pow_one]
  field_simp [hg] <;> ring

private lemma rationalJ_v (e f : Bool) {u v r : ℂ} (hg : G e f u v ≠ 0) :
    HasDerivAt (fun w => rationalJ e f u w r) (jU f e v u r) v := by
  simpa only [rationalJ_comm e f u] using
    (rationalJ_u f e (u := v) (v := u) (r := r) (G_ne_zero_swap e f hg))

private lemma cauchy_u (e f : Bool) {u v : ℂ} (hg : G e f u v ≠ 0) :
    HasDerivAt (fun w => cauchy e f w v) (cU e f u v) u := by
  apply ((rho_u e f u v).div (((G_u e f u v).pow 2).const_mul 2)
    (mul_ne_zero (by norm_num) (pow_ne_zero _ hg))).congr_deriv
  simp only [cU, Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp [hg] <;> ring
private lemma cauchy_v (e f : Bool) {u v : ℂ} (hg : G e f u v ≠ 0) :
    HasDerivAt (fun w => cauchy e f u w) (cU f e v u) v := by
  simpa only [cauchy_comm e f u] using
    (cauchy_u f e (u := v) (v := u) (G_ne_zero_swap e f hg))

-- Clearing the four signed rational charts produces high degree polynomial identities.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
private lemma rationalJ_spatial (e f : Bool) {u v r : ℂ}
    (hau : h e u r ≠ 0) (hav : h f v r ≠ 0) (hg : G e f u v ≠ 0) :
    modeScale f v * u * b u * jU e f u v r +
      modeScale e u * v * b v * jU f e v u r +
      (modeScale f v * modeA e u r + modeScale e u * modeA f v r) * rationalJ e f u v r =
      (1 - r) * (modeA e u r * modeD f v r + modeD e u r * modeA f v r -
        2 * modeA e u r * modeA f v r) / 2 := by
  have hg' := G_ne_zero_swap e f hg
  cases e <;> cases f <;>
    simp only [jU, rationalJ, jNu, jN, Gu, Qconstant, modeScale, modeA, modeD, h,
      Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false, ite_true, ite_false,
      Bool.and_false, Bool.and_true] at hau hav ⊢ <;>
    generalize hDu : 1 - (1 - r) * u = du at hau ⊢ <;>
    generalize hDv : 1 - (1 - r) * v = dv at hav ⊢ <;>
    field_simp [hau, hav, hg, hg'] <;>
    (try rw [← hDu]) <;> (try rw [← hDv]) <;>
    unfold G slope b <;>
    simp only [Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false] <;> ring

-- This is the actual inhomogeneous constant, with no sign guessed or discarded.
set_option maxHeartbeats 1600000 in
private lemma cauchy_spatial (e f : Bool) {u v : ℂ} (hg : G e f u v ≠ 0) :
    modeScale f v * u * b u * cU e f u v + modeScale e u * v * b v * cU f e v u +
      (modeScale f v * beta e u + modeScale e u * beta f v) * cauchy e f u v =
        -(modeB e * modeB f) := by
  have hg' := G_ne_zero_swap e f hg
  cases e <;> cases f <;>
    simp only [cU, cauchy, rho, Gu, modeScale, beta, modeB,
      Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false, ite_true, ite_false] <;>
    field_simp [hg, hg'] <;> unfold G b <;>
    simp only [Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false] <;> ring

-- Regularization, directly in the actual normalized source roots.
def chartSign (e f : Bool) : ℂ := if e && !f then -1 else 1
def chartLinear (e f : Bool) (u v U V : ℂ) : ℂ :=
  if e = f then u * U - v * V else if e then U - u * v * V else V - u * v * U

private lemma candidateJ_chart (e f : Bool) {u v r : ℂ}
    (hu : ‖u‖ + ‖r‖ < 1) (hv : ‖v‖ + ‖r‖ < 1) (hg : G e f u v ≠ 0) :
    candidateJ e f u v r = chartJ e f u v r := by
  have hbu : b u ≠ 0 := (mode_factors_ne_zero hu).1
  have hbv : b v ≠ 0 := (mode_factors_ne_zero hv).1
  have hs := W_sum_ne_zero e f hu hv
  have hU : W e u r ^ 2 * b u = h e u r := by rw [W_square e hu]; field_simp [hbu] <;> ring
  have hV : W f v r ^ 2 * b v = h f v r := by rw [W_square f hv]; field_simp [hbv] <;> ring
  have hwu : W e u r ≠ 0 := by
    intro hz
    have hh := h_ne_zero e hu
    rw [hz, zero_pow (by decide), zero_mul] at hU
    exact hh hU.symm
  have hwv : W f v r ≠ 0 := by
    intro hz
    have hh := h_ne_zero f hv
    rw [hz, zero_pow (by decide), zero_mul] at hV
    exact hh hV.symm
  have hB : sourceMode e u r * sourceMode f v r = 1 / (b u * b v * W e u r * W f v r) := by
    apply (eq_div_iff (by aesop : b u * b v * W e u r * W f v r ≠ 0)).2
    calc
      _ = (sourceMode e u r * b u * W e u r) * (sourceMode f v r * b v * W f v r) := by ring
      _ = 1 := by rw [source_W_normalization e hu, source_W_normalization f hv, one_mul]
  have hpoly : b v * h e u r - b u * h f v r =
      (if e then r else -r) * G e f u v := by
    cases e <;> cases f <;> simp only [h, G, b, Bool.false_eq_true, Bool.true_eq_false,
      ite_true, ite_false, ite_true, ite_false] <;> ring
  have hdiff : W e u r - W f v r =
      (if e then r else -r) * G e f u v / (b u * b v * (W e u r + W f v r)) := by
    apply (eq_div_iff (mul_ne_zero (mul_ne_zero hbu hbv) hs)).2
    linear_combination b v * hU - b u * hV + hpoly
  have hchart : sourceMode e u r * sourceMode f v r * rationalJ e f u v r - cauchy e f u v =
      sourceMode e u r * sourceMode f v r * Qconstant e f r +
      chartSign e f * (W e u r - W f v r) * chartLinear e f u v (W e u r) (W f v r) /
        (2 * G e f u v ^ 2 * W e u r * W f v r) := by
    rw [hB]
    unfold rationalJ cauchy jN
    -- Treat h_e, h_f as their PROVED quadratic expressions, then ring only.
    rw [← hU, ← hV]
    cases e <;> cases f <;>
      simp only [chartSign, chartLinear, rho, Bool.false_eq_true, Bool.true_eq_false,
        ite_true, ite_false, ite_true, ite_false, Bool.and_false, Bool.and_true,
        Bool.not_false, Bool.not_true] <;>
      field_simp [hbu, hbv, hwu, hwv, hg] <;> ring
  have hlin : chartLinear e f u v (W e u r) (W f v r) =
      if e = f then
        ((u - v) * (W e u r + W f v r) + (u + v) * (W e u r - W f v r)) / 2
      else if e then
        ((1 - u * v) * (W e u r + W f v r) + (1 + u * v) * (W e u r - W f v r)) / 2
      else
        ((1 - u * v) * (W e u r + W f v r) - (1 + u * v) * (W e u r - W f v r)) / 2 := by
    cases e <;> cases f <;>
      simp only [chartLinear, Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false,
        ite_true, ite_false] <;> ring
  have hregular : sourceMode e u r * sourceMode f v r * rationalJ e f u v r - cauchy e f u v =
      sourceMode e u r * sourceMode f v r *
        (r / 4 + r ^ 2 * rho e f u v / (4 * b u * b v * (W e u r + W f v r) ^ 2)) := by
    rw [hchart, hlin, hdiff, hB]
    cases e <;> cases f <;>
      simp only [chartSign, Qconstant, rho, Bool.false_eq_true, Bool.true_eq_false,
        ite_true, ite_false, ite_true, ite_false, Bool.and_false, Bool.and_true,
        Bool.not_false, Bool.not_true] <;>
      field_simp [hbu, hbv, hwu, hwv, hs, hg] <;> unfold G <;>
      simp only [Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false] <;> ring
  unfold candidateJ chartJ
  linear_combination -hregular

/-- The literal signed J candidate satisfies its polynomial identity also on
same-sign diagonals. The source square fixes that diagonal algebraically. -/
lemma candidateJ_cleared (e f : Bool) {u v r : ℂ}
    (hu : ‖u‖ + ‖r‖ < 1) (hv : ‖v‖ + ‖r‖ < 1) :
    2 * G e f u v ^ 2 *
      (candidateJ e f u v r - (Qconstant e f r - correction r) *
        sourceMode e u r * sourceMode f v r) =
      jN e f u v r * sourceMode e u r * sourceMode f v r - rho e f u v := by
  by_cases hg : G e f u v = 0
  · have hef : e = f := by
      by_contra hef
      have hprod : u * v = 1 := by
        have he : 1 - u * v = 0 := by simpa [G, hef] using hg
        exact (sub_eq_zero.mp he).symm
      have hu1 : ‖u‖ < 1 := by linarith [norm_nonneg r]
      have hv1 : ‖v‖ < 1 := by linarith [norm_nonneg r]
      have hn : ‖u‖ * ‖v‖ < 1 := by nlinarith [mul_nonneg (norm_nonneg u) (sub_nonneg.mpr hv1.le)]
      rw [← norm_mul, hprod, norm_one] at hn
      exact (lt_irrefl 1) hn
    subst f
    have huv : u = v := sub_eq_zero.mp (by simpa [G] using hg)
    subst v
    have hb := (mode_factors_ne_zero hu).1
    have hb' : b u ≠ 0 := hb
    have hh := h_ne_zero e hu
    have hs : sourceMode e u r ^ 2 = 1 / (b u * h e u r) := by
      cases e
      · exact (sourceMode_square hu).2
      · exact (sourceMode_square hu).1
    rw [hg, zero_pow (by decide), mul_zero, zero_mul]
    have hd : jN e e u u r * sourceMode e u r * sourceMode e u r = rho e e u u := by
      calc
        _ = (2 * u * h e u r * b u) * sourceMode e u r ^ 2 := by simp only [jN, ite_true]; ring
        _ = rho e e u u := by rw [hs]; unfold rho; simp only [ite_true]; field_simp [hb', hh]; ring
    rw [hd, sub_self]
  · rw [candidateJ_chart e f hu hv hg]
    unfold chartJ rationalJ cauchy
    field_simp [hg]
    <;> ring

private lemma candidateJ_u (e f : Bool) {u v r : ℂ}
    (hu : ‖u‖ + ‖r‖ < 1) (hv : ‖v‖ + ‖r‖ < 1) (hg : G e f u v ≠ 0) :
    HasDerivAt (fun w => candidateJ e f w v r)
      (sourceMode e u r * sourceMode f v r *
        (jU e f u v r + mLog e u r * (rationalJ e f u v r - correction r)) - cU e f u v) u := by
  have hc : HasDerivAt (fun w => chartJ e f w v r) _ u :=
    (((source_u e hu).mul_const (sourceMode f v r)).mul
      ((rationalJ_u e f hg).sub_const (correction r))).sub (cauchy_u e f hg)
  have heq : (fun w => candidateJ e f w v r) =ᶠ[nhds u] (fun w => chartJ e f w v r) := by
    have hn : ∀ᶠ w : ℂ in nhds u, ‖w‖ + ‖r‖ < 1 :=
      (continuous_norm.continuousAt.add continuousAt_const).eventually (gt_mem_nhds hu)
    have hgn := ((G_u e f u v).continuousAt).eventually_ne hg
    filter_upwards [hn, hgn] with w hw hgw
    exact candidateJ_chart e f hw hv hgw
  apply (hc.congr_of_eventuallyEq heq).congr_deriv
  try simp only [Pi.mul_apply, Pi.sub_apply, id_eq]
  ring

private lemma candidateJ_v (e f : Bool) {u v r : ℂ}
    (hu : ‖u‖ + ‖r‖ < 1) (hv : ‖v‖ + ‖r‖ < 1) (hg : G e f u v ≠ 0) :
    HasDerivAt (fun w => candidateJ e f u w r)
      (sourceMode e u r * sourceMode f v r *
        (jU f e v u r + mLog f v r * (rationalJ e f u v r - correction r)) - cU f e v u) v := by
  have hc : HasDerivAt (fun w => chartJ e f u w r) _ v :=
    (((source_u f hv).const_mul (sourceMode e u r)).mul
      ((rationalJ_v e f hg).sub_const (correction r))).sub (cauchy_v e f hg)
  have heq : (fun w => candidateJ e f u w r) =ᶠ[nhds v] (fun w => chartJ e f u w r) := by
    have hn : ∀ᶠ w : ℂ in nhds v, ‖w‖ + ‖r‖ < 1 :=
      (continuous_norm.continuousAt.add continuousAt_const).eventually (gt_mem_nhds hv)
    have hgn : ∀ᶠ w : ℂ in nhds v, G e f u w ≠ 0 :=
      (show ContinuousAt (fun w => G e f u w) v by cases e <;> cases f <;> simp only [G, Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false] <;> fun_prop).eventually_ne hg
    filter_upwards [hn, hgn] with w hw hgw
    exact candidateJ_chart e f hu hw hgw
  apply (hc.congr_of_eventuallyEq heq).congr_deriv
  try simp only [Pi.mul_apply, Pi.sub_apply, id_eq]
  ring

set_option maxHeartbeats 1600000 in
private lemma candidateJ_off_chart_poles (e f : Bool) {u v r : ℂ}
    (hu : ‖u‖ + ‖r‖ < 1) (hv : ‖v‖ + ‖r‖ < 1) (hg : G e f u v ≠ 0) :
    let lam := OriginalGaussianAllIndexResolvent.shiftedCentralDerivative r 0 / period r
    modeScale f v * L e (fun w => candidateJ e f w v r) u +
      modeScale e u * L f (fun w => candidateJ e f u w r) v =
      (1 - r) * sourceMode e u r * sourceMode f v r *
        (modeA e u r * modeH f v r lam + modeH e u r lam * modeA f v r) / 2 +
          modeB e * modeB f := by
  have hr : ‖r‖ < 1 := by linarith [norm_nonneg u]
  dsimp only
  rw [← ell_eq_source hr]
  unfold L
  rw [(candidateJ_u e f hu hv hg).deriv, (candidateJ_v e f hu hv hg).deriv]
  dsimp only
  rw [candidateJ_chart e f hu hv hg]
  unfold chartJ
  have hbu : b u ≠ 0 := (mode_factors_ne_zero hu).1
  have hbv : b v ≠ 0 := (mode_factors_ne_zero hv).1
  have hau := h_ne_zero e hu
  have hav := h_ne_zero f hv
  have hc := rationalJ_spatial e f hau hav hg
  have hC := cauchy_spatial e f hg
  have halg :
      (1 - r) * (modeA e u r * modeD f v r + modeD e u r * modeA f v r -
        2 * modeA e u r * modeA f v r) / 2 -
        (modeScale f v * modeA e u r + modeScale e u * modeA f v r) * correction r =
      (1 - r) * (modeA e u r * modeH f v r (ell r) +
        modeH e u r (ell r) * modeA f v r) / 2 := by
    cases e <;> cases f <;>
      simp only [modeH, modeA, modeScale, modeD, h, correction,
        Bool.false_eq_true, ite_false, ite_true] at hau hav ⊢ <;>
      field_simp [hau, hav] <;> ring
  linear_combination sourceMode e u r * sourceMode f v r * hc +
    sourceMode e u r * sourceMode f v r * halg - hC +
    modeScale f v * sourceMode e u r * sourceMode f v r *
      (rationalJ e f u v r - correction r) * source_frequency e hbu hau +
    modeScale e u * sourceMode e u r * sourceMode f v r *
      (rationalJ e f u v r - correction r) * source_frequency f hbv hav


private lemma candidateJ_partials (e f : Bool) {u v r : ℂ}
    (hu : ‖u‖ + ‖r‖ < 1) (hv : ‖v‖ + ‖r‖ < 1) :
    deriv (fun w => candidateJ e f w v r) u =
      fderiv ℂ (fun p : ℂ × ℂ => candidateJ e f p.1 p.2 r) (u, v) (1, 0) ∧
    deriv (fun w => candidateJ e f u w r) v =
      fderiv ℂ (fun p : ℂ × ℂ => candidateJ e f p.1 p.2 r) (u, v) (0, 1) := by
  have hf := (candidateJ_joint_analytic e f hu hv).differentiableAt.hasFDerivAt
  constructor
  · exact (hf.comp_hasDerivAt u ((hasDerivAt_id u).prodMk (hasDerivAt_const u v))).deriv
  · exact (hf.comp_hasDerivAt v ((hasDerivAt_const v u).prodMk (hasDerivAt_id v))).deriv

private lemma modeA_continuous (e : Bool) {u r : ℂ} (hu : ‖u‖ + ‖r‖ < 1) :
    ContinuousAt (fun w => modeA e w r) u := by
  cases e
  · simp only [modeA, Bool.false_eq_true, ite_false]
    apply ContinuousAt.sub _ continuousAt_const
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact mul_ne_zero (by norm_num) (h_ne_zero false hu)
  · simp only [modeA, ite_true]
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact mul_ne_zero (by norm_num) (h_ne_zero true hu)

private lemma modeH_continuous (e : Bool) {u r : ℂ} (hu : ‖u‖ + ‖r‖ < 1) (lam : ℂ) :
    ContinuousAt (fun w => modeH e w r lam) u := by
  have hA := modeA_continuous e hu
  have hD : ContinuousAt (fun w => modeD e w r) u := by
    cases e <;> simp only [modeD, h, Bool.false_eq_true, ite_false, ite_true]
    · apply ContinuousAt.div
      · fun_prop
      · fun_prop
      · exact h_ne_zero false hu
    · apply ContinuousAt.div
      · fun_prop
      · fun_prop
      · exact h_ne_zero true hu
  have hscale : ContinuousAt (fun w => 2 * r * modeScale e w * lam) u := by
    cases e <;> simp only [modeScale, Bool.false_eq_true, ite_false, ite_true] <;> fun_prop
  have hh := (hD.sub hA).sub hscale
  convert hh using 1
  funext w
  cases e <;> rfl

-- The diagonal is filled by continuity of the derivative of the JOINT analytic
-- regular candidate, not by defining a derivative on the punctured chart.
private lemma candidateJ_same_sign (e : Bool) {u v r : ℂ}
    (hu : ‖u‖ + ‖r‖ < 1) (hv : ‖v‖ + ‖r‖ < 1) :
    let lam := OriginalGaussianAllIndexResolvent.shiftedCentralDerivative r 0 / period r
    modeScale e v * L e (fun w => candidateJ e e w v r) u +
      modeScale e u * L e (fun w => candidateJ e e u w r) v =
      (1 - r) * sourceMode e u r * sourceMode e v r *
        (modeA e u r * modeH e v r lam + modeH e u r lam * modeA e v r) / 2 +
          modeB e * modeB e := by
  by_cases hd : u - v ≠ 0
  · exact candidateJ_off_chart_poles e e hu hv (by simpa only [G, ite_true] using hd)
  have huv : v = u := (sub_eq_zero.mp (not_ne_iff.mp hd)).symm
  subst v
  let F : ℂ × ℂ → ℂ := fun p => candidateJ e e p.1 p.2 r
  let lam := OriginalGaussianAllIndexResolvent.shiftedCentralDerivative r 0 / period r
  let R : ℂ → ℂ := fun w =>
    modeScale e u * (w * b w * fderiv ℂ F (w, u) (1, 0) + beta e w * F (w, u)) +
      modeScale e w * (u * b u * fderiv ℂ F (w, u) (0, 1) + beta e u * F (w, u)) -
      ((1 - r) * sourceMode e w r * sourceMode e u r *
        (modeA e w r * modeH e u r lam + modeH e w r lam * modeA e u r) / 2 +
          modeB e * modeB e)
  have hf : AnalyticAt ℂ F (u, u) := candidateJ_joint_analytic e e hu hu
  have hp : ContinuousAt (fun w : ℂ => (w, u)) u := continuousAt_id.prodMk continuousAt_const
  have hcD : ContinuousAt (fun w => fderiv ℂ F (w, u)) u :=
    ContinuousAt.comp (g := fderiv ℂ F) (f := fun w : ℂ => (w, u)) hf.fderiv.continuousAt hp
  have hD₁ : ContinuousAt (fun w => fderiv ℂ F (w, u) (1, 0)) u := hcD.clm_apply continuousAt_const
  have hD₂ : ContinuousAt (fun w => fderiv ℂ F (w, u) (0, 1)) u := hcD.clm_apply continuousAt_const
  have hF : ContinuousAt (fun w => F (w, u)) u :=
    ContinuousAt.comp (g := F) (f := fun w : ℂ => (w, u)) hf.continuousAt hp
  have hM := (source_u e hu).continuousAt
  have hA := modeA_continuous e hu
  have hH := modeH_continuous e hu lam
  have hb : Continuous b := by unfold b; fun_prop
  have hbeta : Continuous (beta e) := by
    cases e
    · change Continuous (fun w : ℂ => -(w + 1) / 2)
      fun_prop
    · change Continuous (fun w : ℂ => (1 - 3 * w) / 2)
      fun_prop
  have hscale : Continuous (modeScale e) := by
    cases e
    · change Continuous (fun w : ℂ => w)
      fun_prop
    · change Continuous (fun _ : ℂ => (1 : ℂ))
      fun_prop
  have hR : ContinuousAt R u := by
    dsimp only [R]
    fun_prop
  have heq : R =ᶠ[nhdsWithin u {u}ᶜ] (fun _ => 0) := by
    have hn : ∀ᶠ w : ℂ in nhds u, ‖w‖ + ‖r‖ < 1 :=
      (continuous_norm.continuousAt.add continuousAt_const).eventually (gt_mem_nhds hu)
    filter_upwards [hn.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw hdw
    have hder := candidateJ_partials e e hw hu
    have he := candidateJ_off_chart_poles e e hw hu
      (by simpa only [G, ite_true] using (sub_ne_zero.mpr hdw : w - u ≠ 0))
    dsimp only at he
    unfold L at he
    dsimp only at he
    rw [hder.1, hder.2] at he
    exact sub_eq_zero.mpr he
  have hz : R u = 0 := tendsto_nhds_unique
    (hR.tendsto.mono_left nhdsWithin_le_nhds) (tendsto_const_nhds.congr' heq.symm)
  have hder := candidateJ_partials e e hu hu
  dsimp only [R, F, lam] at hz
  dsimp only
  unfold L
  dsimp only
  rw [hder.1, hder.2]
  exact sub_eq_zero.mp hz

private lemma G_ne_zero_mixed (e f : Bool) {u v : ℂ} (hef : e ≠ f)
    (hu : ‖u‖ < 1) (hv : ‖v‖ < 1) : G e f u v ≠ 0 := by
  rw [G, if_neg hef]
  intro hz
  have hn : ‖u * v‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg v) hu.le) hv
  have hh := congrArg norm (sub_eq_zero.mp hz)
  simp only [norm_one] at hh
  linarith

/-- the signed REGULAR J candidate satisfies the literal spatial
PDE on the whole actual source disk. The inhomogeneous constant is retained. -/
private theorem candidateJ_displacement (e f : Bool) {u v r : ℂ}
    (hu : ‖u‖ + ‖r‖ < 1) (hv : ‖v‖ + ‖r‖ < 1) :
    let lam := OriginalGaussianAllIndexResolvent.shiftedCentralDerivative r 0 / period r
    modeScale f v * L e (fun w => candidateJ e f w v r) u +
      modeScale e u * L f (fun w => candidateJ e f u w r) v =
      (1 - r) * sourceMode e u r * sourceMode f v r *
        (modeA e u r * modeH f v r lam + modeH e u r lam * modeA f v r) / 2 +
          modeB e * modeB f := by
  by_cases hef : e = f
  · subst f
    exact candidateJ_same_sign e hu hv
  · exact candidateJ_off_chart_poles e f hu hv
      (G_ne_zero_mixed e f hef (by linarith [norm_nonneg r]) (by linarith [norm_nonneg r]))

/-- actual-domain J supplier, directly consumable by the separate
signed uniqueness theorem on the original source bidisk. -/
theorem candidateJ_original_displacement (e f : Bool) {u v : ℂ} {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1)
    (hu : ‖u‖ + Real.sqrt r < 1) (hv : ‖v‖ + Real.sqrt r < 1) :
    let x : ℂ := r
    let lam := OriginalGaussianAllIndexResolvent.shiftedCentralDerivative x 0 / period x
    modeScale f v * L e (fun w => candidateJ e f w v x) u +
      modeScale e u * L f (fun w => candidateJ e f u w x) v =
      (1 - x) * sourceMode e u x * sourceMode f v x *
        (modeA e u x * modeH f v x lam + modeH e u x lam * modeA f v x) / 2 +
          modeB e * modeB f := by
  exact candidateJ_displacement e f (original_small hr.le hr1 hu) (original_small hr.le hr1 hv)

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalSignedCandidate
