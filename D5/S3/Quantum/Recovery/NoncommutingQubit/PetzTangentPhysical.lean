/- GID: D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentPhysical
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentPhysical
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Qubit Petz tangent entries for partial trace and the square-root sandwich. -/

import D5.S3.Quantum.Recovery.NoncommutingQubit.PetzTangentArcsine
import D5.S3.Quantum.Recovery.NoncommutingQubit.PetzTangentReciprocalGram
import D5.S3.Quantum.Divergence.UmegakiConditionalBKM
import D5.S3.Quantum.Recovery.BKMFlagRefinementPetz
/-! The parity estimate applied to both coherences of the physical marginal. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Recovery.PetzTangentPhysical

open PetzTangentReciprocalGram

open PetzTangentArcsine

private lemma affine_pos {b z : ℝ} (hb : b ^ 2 < 1) (hz : z ∈ Icc (-1 : ℝ) 1) :
    0 < 1 - b * z := by
  have hL : 0 ≤ 1 + z := by linarith [hz.1]
  have hR : 0 ≤ 1 - z := sub_nonneg.mpr hz.2
  have hz2 : z ^ 2 ≤ 1 := by nlinarith [mul_nonneg hR hL]
  have hbz : (b*z)^2 < 1 := by
    rw [mul_pow]
    exact (mul_le_of_le_one_right (sq_nonneg b) hz2).trans_lt hb
  nlinarith

private lemma arc_congr_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f h : ℝ → E}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) (hh : ContinuousOn h (Icc (-1 : ℝ) 1))
    (hs : ∀ z ∈ Ioo (0 : ℝ) 1, f z + f (-z) = h z + h (-z)) :
    arcIntegral f = arcIntegral h := by
  unfold arcIntegral
  rw [fold_integral (arc_integrable hf), fold_integral (arc_integrable hh)]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro z hz
  have hd : arcsineDensity (-z) = arcsineDensity z := by simp [arcsineDensity]
  simp only [hd, ← smul_add, hs z hz]

private lemma arc_add {f h : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) (hh : ContinuousOn h (Icc (-1 : ℝ) 1)) :
    arcIntegral (fun z => f z + h z) = arcIntegral f + arcIntegral h := by
  simp only [arcIntegral, smul_add]
  exact integral_add (arc_integrable hf) (arc_integrable hh)

private lemma arc_sub {f h : ℝ → ℂ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) (hh : ContinuousOn h (Icc (-1 : ℝ) 1)) :
    arcIntegral (fun z => f z - h z) = arcIntegral f - arcIntegral h := by
  simp only [arcIntegral, smul_sub]
  exact integral_sub (arc_integrable hf) (arc_integrable hh)

private lemma arc_cmul (a : ℂ) (f : ℝ → ℂ) :
    arcIntegral (fun z => a * f z) = a * arcIntegral f := by
  change (∫ z in Ioo (-1 : ℝ) 1, (arcsineDensity z : ℂ) * (a * f z)) =
    a * ∫ z in Ioo (-1 : ℝ) 1, (arcsineDensity z : ℂ) * f z
  simp_rw [mul_left_comm (arcsineDensity _ : ℂ) a]
  apply integral_const_mul

private lemma arc_cmul_ofReal (a : ℂ) (f : ℝ → ℝ) :
    arcIntegral (fun z => a * (f z : ℂ)) = a * ((arcIntegral (E := ℝ) f : ℝ) : ℂ) := by
  rw [arc_cmul]
  congr 1
  change (∫ z in Ioo (-1 : ℝ) 1, (arcsineDensity z : ℂ) * (f z : ℂ)) =
    ((∫ z in Ioo (-1 : ℝ) 1, arcsineDensity z * f z : ℝ) : ℂ)
  simp only [← Complex.ofReal_mul, integral_complex_ofReal]

private def profile (δ : ℝ) (v₁ vδ : ℂ) (z : ℝ) : ℂ :=
  v₁ * (kernel 1 z : ℂ) + vδ * (kernel δ z : ℂ)

private lemma continuousOn_profile {δ : ℝ} (hδ : 0 < δ) (v₁ vδ : ℂ) :
    ContinuousOn (profile δ v₁ vδ) (Icc (-1 : ℝ) 1) :=
  (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_kernel one_pos))).add
  (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_kernel hδ)))

private lemma profile_even (δ : ℝ) (v₁ vδ : ℂ) (z : ℝ) :
    profile δ v₁ vδ (-z) = profile δ v₁ vδ z := by simp [profile, kernel]

private lemma arc_even_profile {δ : ℝ} (hδ : 0 < δ) (e₁ eδ : ℂ) :
    arcIntegral (profile δ e₁ eδ) = e₁ + eδ / (δ : ℂ) := by
  have hc (x : ℝ) (hx : 0 < x) (v : ℂ) :
      ContinuousOn (fun z => v * (kernel x z : ℂ)) (Icc (-1 : ℝ) 1) :=
    continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn (continuousOn_kernel hx))
  unfold profile
  rw [arc_add (hc 1 one_pos e₁) (hc δ hδ eδ), arc_cmul_ofReal, arc_cmul_ofReal,
    arcsine_even_moment 1 one_pos, arcsine_even_moment δ hδ]
  simp [div_eq_mul_inv]

private lemma arc_odd_profile {δ g : ℝ} (hδ : 0 < δ) (hg : 0 < g) (w₁ wδ : ℂ) :
    (g : ℂ) * arcIntegral (fun z => ((z^2 * kernel g z : ℝ) : ℂ) * profile δ w₁ wδ z) =
      w₁ / (1+(g : ℂ)) + wδ / ((δ : ℂ)*((δ : ℂ)+(g : ℂ))) := by
  let f := fun (x z : ℝ) => z^2 * kernel x z * kernel g z
  have hc (x : ℝ) (hx : 0 < x) :
      ContinuousOn (f x) (Icc (-1 : ℝ) 1) :=
    ((continuous_id.pow 2).continuousOn.mul (continuousOn_kernel hx)).mul
      (continuousOn_kernel hg)
  have hfun (z : ℝ) :
      ((z^2 * kernel g z : ℝ) : ℂ) * profile δ w₁ wδ z =
        w₁ * (f 1 z : ℂ) + wδ * (f δ z : ℂ) := by
    simp only [profile, f, Complex.ofReal_mul]
    ring
  simp_rw [hfun]
  have hm (x : ℝ) (hx : 0 < x) (v : ℂ) :
      ContinuousOn (fun z => v * (f x z : ℂ)) (Icc (-1 : ℝ) 1) :=
    continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn (hc x hx))
  rw [arc_add (hm 1 one_pos w₁) (hm δ hδ wδ),
    arc_cmul_ofReal, arc_cmul_ofReal, mul_add]
  rw [mul_left_comm (g : ℂ) w₁, mul_left_comm (g : ℂ) wδ, ← Complex.ofReal_mul,
    ← Complex.ofReal_mul, arcsine_odd_node_moment 1 g one_pos hg,
    arcsine_odd_node_moment δ g hδ hg]
  push_cast
  simp [div_eq_mul_inv]

private def affine (a b z : ℝ) : ℝ := (1-(z+1)/2)*a + ((z+1)/2)*b

private lemma affine_ab_pos {a b z : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hz : z ∈ Icc (-1 : ℝ) 1) : 0 < affine a b z := by
  have hs₀ : 0 ≤ (z+1)/2 := by linarith [hz.1]
  have hs₁ : (z+1)/2 ≤ 1 := by linarith [hz.2]
  rcases lt_or_eq_of_le hs₁ with h | h
  · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr h) ha) (mul_nonneg hs₀ hb.le)
  · simp [affine, h, hb]

private lemma continuousOn_affine_inv {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ContinuousOn (fun z => (affine a b z)⁻¹) (Icc (-1 : ℝ) 1) := by
  have hc : Continuous (affine a b) := by unfold affine; fun_prop
  exact hc.continuousOn.inv₀ (fun _ hz => (affine_ab_pos ha hb hz).ne')

private lemma arcsine_affine_moment (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    arcIntegral (fun z => (affine a b z)⁻¹) = (Real.sqrt (a*b))⁻¹ := by
  let k := 2 * Real.sqrt (a*b) / (a+b)
  have hs : 0 < Real.sqrt (a*b) := Real.sqrt_pos.2 (mul_pos ha hb)
  have hk : 0 < k := by dsimp [k]; positivity
  have hs2 := Real.sq_sqrt (mul_nonneg ha.le hb.le)
  have hid : (a+b)^2 * (1-k^2) = (a-b)^2 := by
    dsimp [k]
    field_simp [(add_pos ha hb).ne']
    nlinarith
  have he : arcIntegral (fun z => (affine a b z)⁻¹) =
      arcIntegral (fun z => (2/(a+b)) * kernel k z) := by
    apply arc_congr_symm (continuousOn_affine_inv ha hb)
      (continuousOn_const.mul (continuousOn_kernel hk))
    intro z hz
    have hz' : z ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hz.1], hz.2.le⟩
    have hn : -z ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hz.2], by linarith [hz.1]⟩
    have hprod : 4 * (affine a b z * affine a b (-z)) =
        (a+b)^2 * (1-(1-k^2)*z^2) := by
      unfold affine
      linear_combination z^2 * hid
    have hsum : affine a b z + affine a b (-z) = a+b := by unfold affine; ring
    let D := 1-(1-k^2)*z^2
    have hden : D ≠ 0 := (kernelDen_pos hk hz').ne'
    have hL := (affine_ab_pos ha hb hz').ne'
    have hR := (affine_ab_pos ha hb hn).ne'
    change (affine a b z)⁻¹ + (affine a b (-z))⁻¹ =
      2/(a+b)*kernel k z + 2/(a+b)*kernel k (-z)
    rw [show kernel k (-z) = kernel k z by simp [kernel]]
    change (affine a b z)⁻¹ + (affine a b (-z))⁻¹ =
      2/(a+b)*D⁻¹ + 2/(a+b)*D⁻¹
    calc
      _ = (affine a b z + affine a b (-z))/(affine a b z * affine a b (-z)) := by
        field_simp [hL, hR] <;> ring
      _ = _ := by
        rw [hsum, show affine a b z * affine a b (-z) = (a+b)^2 * D / 4 by
          change 4 * (affine a b z * affine a b (-z)) = (a+b)^2 * D at hprod
          linarith only [hprod]]
        field_simp [(add_pos ha hb).ne', hden] <;> ring
  rw [he]
  change (∫ z in Ioo (-1 : ℝ) 1, arcsineDensity z * (2/(a+b) * kernel k z)) = _
  simp_rw [mul_left_comm (arcsineDensity _) (2/(a+b))]
  rw [integral_const_mul]
  change 2/(a+b) * arcIntegral (kernel k) = _
  rw [arcsine_even_moment k hk]
  dsimp [k]
  field_simp [hs.ne', (add_pos ha hb).ne'] <;> ring

private def response (p q : ℝ) (c₀₀ c₁₁ c₀₁ c₁₀ : ℂ) (z : ℝ) : ℂ :=
  c₀₀ * ((affine p p z)⁻¹ : ℝ) + c₁₁ * ((affine q q z)⁻¹ : ℝ) +
    c₀₁ * ((affine p q z)⁻¹ : ℝ) + c₁₀ * ((affine q p z)⁻¹ : ℝ)

private lemma response_continuous {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (c₀₀ c₁₁ c₀₁ c₁₀ : ℂ) :
    ContinuousOn (response p q c₀₀ c₁₁ c₀₁ c₁₀) (Icc (-1 : ℝ) 1) := by
  have hc (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (c : ℂ) :
      ContinuousOn (fun z => c * ((affine a b z)⁻¹ : ℝ)) (Icc (-1 : ℝ) 1) :=
    continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_affine_inv ha hb))
  exact (((hc p p hp hp c₀₀).add (hc q q hq hq c₁₁)).add (hc p q hp hq c₀₁)).add
    (hc q p hq hp c₁₀)

private lemma arc_response {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (c₀₀ c₁₁ c₀₁ c₁₀ : ℂ) :
    arcIntegral (response p q c₀₀ c₁₁ c₀₁ c₁₀) =
      c₀₀ * ((Real.sqrt (p*p))⁻¹ : ℝ) + c₁₁ * ((Real.sqrt (q*q))⁻¹ : ℝ) +
      c₀₁ * ((Real.sqrt (p*q))⁻¹ : ℝ) + c₁₀ * ((Real.sqrt (q*p))⁻¹ : ℝ) := by
  have hc (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (c : ℂ) :
      ContinuousOn (fun z => c * ((affine a b z)⁻¹ : ℝ)) (Icc (-1 : ℝ) 1) :=
    continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_affine_inv ha hb))
  let f := fun a b : ℝ => fun c : ℂ => fun z : ℝ => c * ((affine a b z)⁻¹ : ℝ)
  have h₀ : ContinuousOn (fun z => f p p c₀₀ z + f q q c₁₁ z) (Icc (-1 : ℝ) 1) :=
    (hc p p hp hp c₀₀).add (hc q q hq hq c₁₁)
  have h₁ : ContinuousOn (fun z => f p p c₀₀ z + f q q c₁₁ z + f p q c₀₁ z)
      (Icc (-1 : ℝ) 1) := h₀.add (hc p q hp hq c₀₁)
  unfold response
  rw [arc_add h₁ (hc q p hq hp c₁₀), arc_add h₀ (hc p q hp hq c₀₁),
    arc_add (hc p p hp hp c₀₀) (hc q q hq hq c₁₁)]
  simp_rw [arc_cmul_ofReal, arcsine_affine_moment _ _ hp hp, arcsine_affine_moment _ _ hq hq,
    arcsine_affine_moment _ _ hp hq, arcsine_affine_moment _ _ hq hp]

private def pairResidual (p q u β : ℝ) (X c₀₀ c₁₁ c₀₁ c₁₀ : ℂ) (z : ℝ) : ℂ :=
  X - ((u * (1-β*z) : ℝ) : ℂ) * response p q c₀₀ c₁₁ c₀₁ c₁₀ z

private def pairPetzResidual (p q u g : ℝ) (X c₀₀ c₁₁ c₀₁ c₁₀ : ℂ) : ℂ :=
  X - ((u*g : ℝ) : ℂ) * (c₀₀ * ((Real.sqrt (p*p))⁻¹ : ℝ) +
    c₁₁ * ((Real.sqrt (q*q))⁻¹ : ℝ) + c₀₁ * ((Real.sqrt (p*q))⁻¹ : ℝ) +
    c₁₀ * ((Real.sqrt (q*p))⁻¹ : ℝ))

/-- Equation (4) at a pair of supported eigenvalues. The two coherences remain complex. -/
private theorem pair_petz_arcsine (p q u g β : ℝ) (X c₀₀ c₁₁ c₀₁ c₁₀ : ℂ)
    (hp : 0 < p) (hq : 0 < q) (hg : 0 < g) (hgb : g^2+β^2=1) :
    pairPetzResidual p q u g X c₀₀ c₁₁ c₀₁ c₁₀ =
      (g : ℂ) * arcIntegral (fun z =>
        pairResidual p q u β X c₀₀ c₁₁ c₀₁ c₁₀ z / ((1-β*z : ℝ) : ℂ)) := by
  let l := (1+β)/2
  let r := (1-β)/2
  have hβ : β^2 < 1 := by nlinarith [sq_pos_of_pos hg]
  have hb2 : β^2 < (1 : ℝ)^2 := by simpa using hβ
  have hb : -1 < β ∧ β < 1 := abs_lt.mp (by simpa using (sq_lt_sq.mp hb2))
  have hl : 0 < l := by dsimp [l]; linarith [hb.1]
  have hr : 0 < r := by dsimp [r]; linarith [hb.2]
  have ha (z : ℝ) : 2 * affine l r z = 1-β*z := by dsimp [affine, l, r]; ring
  have hs : Real.sqrt (l*r) = g/2 := by
    have he : l*r = (g/2)^2 := by dsimp [l, r]; nlinarith
    rw [he, Real.sqrt_sq (by positivity)]
  have hC : ContinuousOn (fun z : ℝ => (1-β*z)⁻¹) (Icc (-1 : ℝ) 1) :=
    (continuous_const.sub (continuous_const.mul continuous_id)).continuousOn.inv₀
      (fun z hz => (affine_pos hβ hz).ne')
  have hM : arcIntegral (fun z : ℝ => (1-β*z)⁻¹) = g⁻¹ := by
    have he (z : ℝ) : (1-β*z)⁻¹ = 2⁻¹ * (affine l r z)⁻¹ := by rw [← ha, mul_inv]
    simp_rw [he]
    change (∫ z in Ioo (-1 : ℝ) 1, arcsineDensity z * (2⁻¹ * (affine l r z)⁻¹)) = _
    simp_rw [mul_left_comm (arcsineDensity _) (2⁻¹ : ℝ)]
    rw [integral_const_mul]
    change 2⁻¹ * arcIntegral (fun z => (affine l r z)⁻¹) = _
    rw [arcsine_affine_moment l r hl hr, hs]
    field_simp [hg.ne']
  have hpoint : EqOn (fun z => pairResidual p q u β X c₀₀ c₁₁ c₀₁ c₁₀ z /
      ((1-β*z : ℝ) : ℂ))
      (fun z => X * ((1-β*z)⁻¹ : ℝ) - (u : ℂ) * response p q c₀₀ c₁₁ c₀₁ c₁₀ z)
      (Ioo (-1 : ℝ) 1) := by
    intro z hz
    have hn : ((1-β*z : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (affine_pos hβ (Ioo_subset_Icc_self hz)).ne'
    simp only [pairResidual, Complex.ofReal_mul, Complex.ofReal_inv]
    field_simp [hn] <;> ring
  rw [show arcIntegral (fun z => pairResidual p q u β X c₀₀ c₁₁ c₀₁ c₁₀ z /
        ((1-β*z : ℝ) : ℂ)) =
      arcIntegral (fun z => X * ((1-β*z)⁻¹ : ℝ) -
        (u : ℂ) * response p q c₀₀ c₁₁ c₀₁ c₁₀ z) by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro z hz
    exact congrArg (arcsineDensity z • ·) (hpoint hz)]
  have hL : ContinuousOn (fun z => X * ((1-β*z)⁻¹ : ℝ)) (Icc (-1 : ℝ) 1) :=
    continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hC)
  have hR : ContinuousOn (fun z => (u : ℂ) * response p q c₀₀ c₁₁ c₀₁ c₁₀ z)
      (Icc (-1 : ℝ) 1) := continuousOn_const.mul (response_continuous hp hq _ _ _ _)
  rw [arc_sub hL hR,
    arc_cmul_ofReal, hM, arc_cmul, arc_response hp hq]
  have hgc : (g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
  simp only [pairPetzResidual, Complex.ofReal_mul, Complex.ofReal_inv]
  field_simp [hgc] <;> ring

/-- Equations (5) and (6) consumed by the pinned paired parity bound. -/
private theorem paired_profile_bound (g β δ : ℝ) (e₁ eδ w₁ wδ : ℂ)
    (hg : 0 < g) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hgb : g^2+β^2=1) :
    let F := fun z : ℝ => ((1-β*z : ℝ) : ℂ) * profile δ e₁ eδ z +
      (z : ℂ) * profile δ w₁ wδ z
    Complex.normSq ((g : ℂ) * arcIntegral (fun z => F z / ((1-β*z : ℝ) : ℂ))) ≤
      parityMultiplier δ * (∫ z in Ioo (-1 : ℝ) 1,
        Complex.normSq (F z) / (1-β*z) / 2) := by
  dsimp only
  let e := profile δ e₁ eδ
  let w := profile δ w₁ wδ
  let a := e₁
  let b := eδ / (δ : ℂ)
  let c := w₁ / (1+(g : ℂ))
  let d := wδ / ((δ : ℂ)*((δ : ℂ)+(g : ℂ)))
  let F := fun z : ℝ => ((1-β*z : ℝ) : ℂ) * e z + (z : ℂ) * w z
  change Complex.normSq ((g : ℂ) * arcIntegral (fun z => F z / ((1-β*z : ℝ) : ℂ))) ≤ _
  have hβ : β^2 < 1 := by nlinarith [sq_pos_of_pos hg]
  have he := continuousOn_profile hδ e₁ eδ
  have hw := continuousOn_profile hδ w₁ wδ
  have hge : 1-g^2 = β^2 := by linarith
  have hA : Continuous (fun z : ℝ => ((1-β*z : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_const.sub (continuous_const.mul continuous_id))
  have hF : ContinuousOn F (Icc (-1 : ℝ) 1) :=
    (hA.continuousOn.mul he).add (Complex.continuous_ofReal.continuousOn.mul hw)
  have hAne (z : ℝ) (hz : z ∈ Icc (-1 : ℝ) 1) : ((1-β*z : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (affine_pos hβ hz).ne'
  let B := fun z : ℝ => ((z^2 * kernel g z : ℝ) : ℂ) * w z
  have hB : ContinuousOn B (Icc (-1 : ℝ) 1) :=
    (Complex.continuous_ofReal.comp_continuousOn
      ((continuous_id.pow 2).continuousOn.mul (continuousOn_kernel hg))).mul hw
  have hfun : (g : ℂ) * arcIntegral (fun z => F z / ((1-β*z : ℝ) : ℂ)) =
      (g : ℂ)*(a+b) + (β : ℂ)*(c+d) := by
    have hs : arcIntegral (fun z => F z / ((1-β*z : ℝ) : ℂ)) =
        arcIntegral (fun z => e z + (β : ℂ)*B z) := by
      apply arc_congr_symm (hF.div hA.continuousOn hAne)
        (he.add (continuousOn_const.mul hB))
      intro z hz
      have hz' : z ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hz.1], hz.2.le⟩
      have hn : -z ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hz.2], by linarith [hz.1]⟩
      have hKn : ((1-β^2*z^2 : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (by simpa only [hge] using (kernelDen_pos hg hz').ne')
      dsimp [F, B, e, w]
      rw [profile_even δ e₁ eδ z, profile_even δ w₁ wδ z]
      simp only [kernel, hge, neg_sq, Complex.ofReal_mul, Complex.ofReal_inv]
      push_cast
      simp only [mul_neg, sub_neg_eq_add]
      have hL : 1 - (β : ℂ) * (z : ℂ) ≠ 0 := by simpa using hAne z hz'
      have hR : 1 + (β : ℂ) * (z : ℂ) ≠ 0 := by simpa using hAne (-z) hn
      push_cast at hKn
      field_simp [hL, hR, hKn] <;> ring
    have hc : ContinuousOn (fun z => (β : ℂ) * B z) (Icc (-1 : ℝ) 1) :=
      continuousOn_const.mul hB
    rw [hs, arc_add (f := e) he hc, arc_cmul, mul_add,
      arc_even_profile hδ e₁ eδ, mul_left_comm (g : ℂ) (β : ℂ),
      arc_odd_profile hδ hg w₁ wδ]
  let en := fun z : ℝ => Complex.normSq (e z)
  let od := fun z : ℝ => z^2 * kernel g z * Complex.normSq (w z)
  have hen : ContinuousOn en (Icc (-1 : ℝ) 1) :=
    Complex.continuous_normSq.comp_continuousOn he
  have hod : ContinuousOn od (Icc (-1 : ℝ) 1) :=
    ((continuous_id.pow 2).continuousOn.mul (continuousOn_kernel hg)).mul
      (Complex.continuous_normSq.comp_continuousOn hw)
  have henergy : (∫ z in Ioo (-1 : ℝ) 1, Complex.normSq (F z) / (1-β*z) / 2) =
      (∫ t in Ioi (0 : ℝ), Real.sqrt (1+t)*evenComplexEnergy δ a b t) +
      (∫ t in Ioi (0 : ℝ), Real.sqrt (1+t)*oddComplexEnergy g δ c d t) := by
    have hi : IntegrableOn (fun z => Complex.normSq (F z) / (1-β*z) / 2)
        (Ioo (-1 : ℝ) 1) := by
      refine (((Complex.continuous_normSq.comp_continuousOn hF).div
        (continuous_const.sub (continuous_const.mul continuous_id)).continuousOn
        (fun z hz => (affine_pos hβ hz).ne')).div_const 2 |>.integrableOn_compact
          isCompact_Icc).mono_set Ioo_subset_Icc_self
    rw [fold_integral hi]
    have hp : EqOn (fun z => Complex.normSq (F z) / (1-β*z) / 2 +
        Complex.normSq (F (-z)) / (1-β*(-z)) / 2)
        (fun z => en z + od z) (Ioo (0 : ℝ) 1) := by
      intro z hz
      have hz' : z ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hz.1], hz.2.le⟩
      have hn : -z ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hz.2], by linarith [hz.1]⟩
      have hKn : 1-β^2*z^2 ≠ 0 := by simpa only [hge] using (kernelDen_pos hg hz').ne'
      dsimp [F, en, od, e, w]
      rw [profile_even δ e₁ eδ z, profile_even δ w₁ wδ z]
      simp only [kernel, hge, Complex.normSq_apply, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, zero_mul, sub_zero, zero_add]
      simp only [mul_neg, sub_neg_eq_add]
      have hR : 1 + β * z ≠ 0 := by simpa using (affine_pos hβ hn).ne'
      field_simp [(affine_pos hβ hz').ne', hR, hKn] <;> ring
    rw [setIntegral_congr_fun measurableSet_Ioo hp,
      integral_add ((hen.integrableOn_compact isCompact_Icc).mono_set
        (show Ioo (0 : ℝ) 1 ⊆ Icc (-1 : ℝ) 1 from fun z hz => ⟨by linarith [hz.1], hz.2.le⟩))
        ((hod.integrableOn_compact isCompact_Icc).mono_set
        (show Ioo (0 : ℝ) 1 ⊆ Icc (-1 : ℝ) 1 from fun z hz => ⟨by linarith [hz.1], hz.2.le⟩))]
    rw [reciprocal_change en, reciprocal_change od]
    have hroot (t : ℝ) (ht : 0 < t) :
        jacobian t * ((1+t)*(1+t)) = Real.sqrt (1+t)/2 := by
      unfold jacobian
      have hS := Real.sq_sqrt (show 0 ≤ 1+t by positivity)
      have hne : Real.sqrt (1+t) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
      generalize Real.sqrt (1+t) = v at hS hne ⊢
      rw [← hS]
      field_simp [hne] <;> ring
    have hp₁ (t : ℝ) (ht : 0 < t) :
        e (reciprocal t) =
          ((1+t : ℝ) : ℂ) * (a * ((1/(1+t) : ℝ) : ℂ) +
            b * ((δ/(δ^2+t) : ℝ) : ℂ)) := by
      dsimp [e, profile, a, b]
      rw [kernel_reciprocal one_pos ht, kernel_reciprocal hδ ht]
      push_cast
      have hδc : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
      have hn : ((1+t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (show 1+t ≠ 0 by positivity)
      have hdn : ((δ^2+t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast
        (show δ^2+t ≠ 0 by positivity)
      push_cast at hn hdn
      norm_num
      field_simp [hδc, hn, hdn] <;> ring
    have hp₂ (t : ℝ) (ht : 0 < t) :
        w (reciprocal t) =
          ((1+t : ℝ) : ℂ) * (c * (((g+1)/(1+t) : ℝ) : ℂ) +
            d * ((δ*(g+δ)/(δ^2+t) : ℝ) : ℂ)) := by
      dsimp [w, profile, c, d]
      rw [kernel_reciprocal one_pos ht, kernel_reciprocal hδ ht]
      have hne {x : ℝ} (hx : 0 < x) : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
      have h₁ := hne (show 0 < 1+t by positivity)
      have h₂ := hne (show 0 < δ^2+t by positivity)
      have h₃ := hne (add_pos one_pos hg)
      have h₄ := hne (add_pos hδ hg)
      push_cast at h₁ h₂ h₃ h₄ ⊢
      norm_num
      field_simp [h₁, h₂, h₃, h₄, hne hδ] <;> ring
    congr 1
    · apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have ht0 : 0 < t := ht
      simp only [smul_eq_mul, en, hp₁ t ht0, Complex.normSq_mul, Complex.normSq_ofReal,
        evenComplexEnergy]
      rw [← mul_assoc, hroot t ht0]
      ring
    · apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have ht0 : 0 < t := ht
      have hq : reciprocal t ^ 2 * kernel g (reciprocal t) = (g^2+t)⁻¹ := by
        rw [reciprocal_sq ht0, kernel_reciprocal hg ht0]
        field_simp [show 1+t ≠ 0 by positivity, show g^2+t ≠ 0 by positivity]
      simp only [smul_eq_mul, od, hq, hp₂ t ht0, Complex.normSq_mul, Complex.normSq_ofReal,
        oddComplexEnergy]
      rw [show ∀ v : ℝ, jacobian t * ((g^2+t)⁻¹ * (((1+t)*(1+t)) * v)) =
        (jacobian t * ((1+t)*(1+t))) * ((g^2+t)⁻¹ * v) by intro v; ring, hroot t ht0]
      simp only [div_eq_mul_inv, mul_inv]
      ring
  change Complex.normSq ((g : ℂ) * arcIntegral (fun z => F z / ((1-β*z : ℝ) : ℂ))) ≤
    parityMultiplier δ * (∫ z in Ioo (-1 : ℝ) 1, Complex.normSq (F z) / (1-β*z) / 2)
  rw [hfun, henergy]
  exact paired_parity_bound g β δ a b c d hg hδ hδ₁ hgb.le

private lemma pair_profiles (p q u β : ℝ) (X c₀₀ c₁₁ c₀₁ c₁₀ : ℂ)
    (hp : 0 < p) (hq : 0 < q) (hpq : p+q=1) :
    ∃ e₁ eδ w₁ wδ : ℂ, ∀ z ∈ Ioo (-1 : ℝ) 1,
      pairResidual p q u β X c₀₀ c₁₁ c₀₁ c₁₀ z =
        ((1-β*z : ℝ) : ℂ) * profile (2*Real.sqrt (p*q)) e₁ eδ z +
          (z : ℂ) * profile (2*Real.sqrt (p*q)) w₁ wδ z := by
  let α := p-q
  let δ := 2*Real.sqrt (p*q)
  let C₀ := c₀₀/(p : ℂ)+c₁₁/(q : ℂ)
  let C₁ := 2*(c₀₁+c₁₀)
  let C₂ := ((2*α : ℝ) : ℂ)*(c₀₁-c₁₀)
  let V := C₂ / ((α^2 : ℝ) : ℂ)
  let e₁ := X - (u : ℂ)*C₀ - ((u*β : ℝ) : ℂ)*V
  let eδ := -(u : ℂ)*C₁ + ((u*β : ℝ) : ℂ)*V
  let w₁ := ((u*β : ℝ) : ℂ)*C₀ + (β : ℂ)*e₁
  let wδ := -(u : ℂ)*(C₂-(β : ℂ)*C₁) + (β : ℂ)*eδ
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hα : 1-δ^2 = α^2 := by
    dsimp [δ, α]
    nlinarith [Real.sq_sqrt (mul_nonneg hp.le hq.le),
      congrArg (fun y : ℝ => y^2) hpq]
  refine ⟨e₁, eδ, w₁, wδ, ?_⟩
  intro z hz
  have hz' := Ioo_subset_Icc_self hz
  have hresponse : response p q c₀₀ c₁₁ c₀₁ c₁₀ z =
      C₀ + (C₁ + C₂*(z : ℂ))*(kernel δ z : ℂ) := by
    have hpp : affine p p z = p := by unfold affine; ring
    have hqq : affine q q z = q := by unfold affine; ring
    have hpq' : 2*affine p q z = 1-α*z := by dsimp [affine, α]; linarith
    have hqp' : 2*affine q p z = 1+α*z := by dsimp [affine, α]; linarith
    have hc {x : ℝ} (hx : 0 < x) : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    have hL : ((1-α*z : ℝ) : ℂ) ≠ 0 := by
      rw [← hpq', Complex.ofReal_mul]
      exact mul_ne_zero (by norm_num) (hc (affine_ab_pos hp hq hz'))
    have hR : ((1+α*z : ℝ) : ℂ) ≠ 0 := by
      rw [← hqp', Complex.ofReal_mul]
      exact mul_ne_zero (by norm_num) (hc (affine_ab_pos hq hp hz'))
    have hK := hc (kernelDen_pos hδ hz')
    rw [hα] at hK
    have hS : (affine p q z)⁻¹ = 2/(1-α*z) := by
      rw [← hpq']
      field_simp [(affine_ab_pos hp hq hz').ne']
    have hT : (affine q p z)⁻¹ = 2/(1+α*z) := by
      rw [← hqp']
      field_simp [(affine_ab_pos hq hp hz').ne']
    unfold response
    rw [hpp, hqq, hS, hT]
    simp only [kernel, hα, C₀, C₁, C₂]
    push_cast at hL hR hK ⊢
    field_simp [hc hp, hc hq, hL, hR, hK] <;> ring
  have hV : V*((kernel δ z : ℂ)-1) = C₂*(z : ℂ)^2*(kernel δ z : ℂ) := by
    by_cases h : α = 0
    · simp [V, C₂, h]
    · have hc : (α : ℂ) ≠ 0 := by exact_mod_cast h
      have hk : ((1-α^2*z^2 : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (by simpa only [hα] using (kernelDen_pos hδ hz').ne')
      simp only [V, kernel, hα]
      push_cast at hk ⊢
      field_simp [hc, hk] <;> ring
  change pairResidual p q u β X c₀₀ c₁₁ c₀₁ c₁₀ z = _
  rw [pairResidual, hresponse]
  simp only [profile, show kernel 1 z = 1 by simp [kernel], Complex.ofReal_one,
    mul_one, e₁, eδ, w₁, wδ]
  push_cast
  linear_combination -(u : ℂ)*(β : ℂ)*hV

/-- Physical scalar entry inequality following from the two moments. -/
private theorem pair_bound (p q u g β : ℝ) (X c₀₀ c₁₁ c₀₁ c₁₀ : ℂ)
    (hp : 0 < p) (hq : 0 < q) (hpq : p+q=1) (hg : 0 < g) (hgb : g^2+β^2=1) :
    Complex.normSq (pairPetzResidual p q u g X c₀₀ c₁₁ c₀₁ c₁₀) ≤
      parityMultiplier (2*Real.sqrt (p*q)) * (∫ z in Ioo (-1 : ℝ) 1,
        Complex.normSq (pairResidual p q u β X c₀₀ c₁₁ c₀₁ c₁₀ z) / (1-β*z) / 2) := by
  have hs := Real.sq_sqrt (mul_nonneg hp.le hq.le)
  have hδ : 0 < 2*Real.sqrt (p*q) := by positivity
  have hδ₁ : 2*Real.sqrt (p*q) ≤ 1 := by
    nlinarith [sq_nonneg (p-q), congrArg (fun x : ℝ => x^2) hpq]
  obtain ⟨e₁, eδ, w₁, wδ, hprofile⟩ := pair_profiles p q u β X c₀₀ c₁₁ c₀₁ c₁₀ hp hq hpq
  let δ := 2*Real.sqrt (p*q)
  let F := pairResidual p q u β X c₀₀ c₁₁ c₀₁ c₁₀
  let F' := fun z : ℝ => ((1-β*z : ℝ) : ℂ)*profile δ e₁ eδ z +
    (z : ℂ)*profile δ w₁ wδ z
  have hArc : arcIntegral (fun z => F z / ((1-β*z : ℝ) : ℂ)) =
      arcIntegral (fun z => F' z / ((1-β*z : ℝ) : ℂ)) := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro z hz
    change arcsineDensity z • (F z / ((1-β*z : ℝ) : ℂ)) =
      arcsineDensity z • (F' z / ((1-β*z : ℝ) : ℂ))
    rw [show F z = F' z from hprofile z hz]
  have hEnergy : (∫ z in Ioo (-1 : ℝ) 1, Complex.normSq (F z) / (1-β*z) / 2) =
      ∫ z in Ioo (-1 : ℝ) 1, Complex.normSq (F' z) / (1-β*z) / 2 := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro z hz
    dsimp only
    rw [show F z = F' z from hprofile z hz]
  rw [pair_petz_arcsine p q u g β X c₀₀ c₁₁ c₀₁ c₁₀ hp hq hg hgb]
  change Complex.normSq ((g : ℂ) * arcIntegral (fun z => F z / ((1-β*z : ℝ) : ℂ))) ≤
    parityMultiplier δ * (∫ z in Ioo (-1 : ℝ) 1, Complex.normSq (F z) / (1-β*z) / 2)
  rw [hArc, hEnergy]
  exact paired_profile_bound g β δ e₁ eδ w₁ wδ hg hδ hδ₁ hgb

section PhysicalEntries

open D5.S3.Quantum.Divergence.UmegakiConditionalKernel
  (arithmetic inverseMatrix arithmetic_inverseMatrix)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open D5.S3.Quantum.Matrix.SpectralPower (mpow)
open BKMFlagRefinement (partialTracePetz lift)

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {E : Type} [Fintype E] [DecidableEq E]

private abbrev coordinates (U : Matrix.unitaryGroup n ℂ) (A : Matrix n n ℂ) :=
  U.valᴴ * A * U.val

private lemma coordinates_mul (U : Matrix.unitaryGroup n ℂ) (A B : Matrix n n ℂ) :
    coordinates U (A*B) = coordinates U A * coordinates U B := by
  have hU : U.val * U.valᴴ = 1 := Unitary.coe_mul_star_self U
  change U.valᴴ*(A*B)*U.val = (U.valᴴ*A*U.val)*(U.valᴴ*B*U.val)
  calc
    _ = U.valᴴ*A*(U.val*U.valᴴ)*B*U.val := by rw [hU]; simp [Matrix.mul_assoc]
    _ = _ := by noncomm_ring

private lemma coordinates_sub (U : Matrix.unitaryGroup n ℂ) (A B : Matrix n n ℂ) :
    coordinates U (A-B) = coordinates U A - coordinates U B := by
  simp only [coordinates, Matrix.mul_sub, Matrix.sub_mul]

private lemma coordinates_spectral (U : Matrix.unitaryGroup n ℂ) (D : Matrix n n ℂ) :
    coordinates U (U.val*D*U.valᴴ) = D := by
  have hU : U.valᴴ * U.val = 1 := Unitary.coe_star_mul_self U
  change U.valᴴ*(U.val*D*U.valᴴ)*U.val = D
  calc
    _ = (U.valᴴ*U.val)*D*(U.valᴴ*U.val) := by noncomm_ring
    _ = _ := by simp [hU]

private lemma from_coordinates (U : Matrix.unitaryGroup n ℂ) (A : Matrix n n ℂ) :
    U.val * coordinates U A * U.valᴴ = A := by
  have hU : U.val * U.valᴴ = 1 := Unitary.coe_mul_star_self U
  change U.val*(U.valᴴ*A*U.val)*U.valᴴ = A
  calc
    _ = (U.val*U.valᴴ)*A*(U.val*U.valᴴ) := by noncomm_ring
    _ = _ := by simp [hU]

private abbrev diagReal (d : n → ℝ) : Matrix n n ℂ :=
  Matrix.diagonal (fun i => (d i : ℂ))

private lemma arithmetic_entry (U : Matrix.unitaryGroup n ℂ)
    {A : Matrix n n ℂ} {d : n → ℝ} (hA : A = U.val*diagReal d*U.valᴴ)
    (B : Matrix n n ℂ) (s : ℝ) (i j : n) :
    coordinates U (arithmetic A B s) i j =
      (((1-s)*d i+s*d j : ℝ) : ℂ) * coordinates U B i j := by
  have hDiag : coordinates U A = diagReal d := by rw [hA, coordinates_spectral]
  unfold arithmetic
  have hExpand :
      coordinates U ((1-s) • (A*B) + s • (B*A)) =
        (1-s) • coordinates U (A*B) + s • coordinates U (B*A) := by
    simp only [coordinates, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hExpand]
  rw [coordinates_mul, coordinates_mul, hDiag]
  simp only [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, Matrix.diagonal_mul,
    Matrix.mul_diagonal]
  push_cast
  ring

private lemma mpow_spectral (U : Matrix.unitaryGroup n ℂ) {A : Matrix n n ℂ}
    {d : n → ℝ} (hA : A.IsHermitian) (hD : A = U.val*diagReal d*U.valᴴ) (r : ℝ) :
    mpow A r = U.val * diagReal (fun i => d i ^ r) * U.valᴴ := by
  rw [mpow, hA.cfc_eq]
  exact hA.cfc_eq_any_unitary (U := U) (D := d) hD (fun x : ℝ => x ^ r)

private lemma embed_entries (U : Matrix.unitaryGroup (Fin 2 × E) ℂ)
    (V : Matrix.unitaryGroup (Fin 2) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ)
    (i j : Fin 2 × E) :
    coordinates U ((V.val*B*V.valᴴ) ⊗ₖ (1 : Matrix E E ℂ)) i j =
      ∑ a : Fin 2, ∑ b : Fin 2, B a b *
        coordinates U ((V.val*Matrix.single a b (1 : ℂ)*V.valᴴ) ⊗ₖ (1 : Matrix E E ℂ))
          i j := by
  classical
  have hb : B = ∑ a : Fin 2, ∑ b : Fin 2, B a b • Matrix.single a b (1 : ℂ) := by
    calc
      B = ∑ a : Fin 2, ∑ b : Fin 2, Matrix.single a b (B a b) := matrix_eq_sum_single B
      _ = _ := by simp [Matrix.smul_single]
  conv_lhs => rw [hb]
  simp only [Fin.sum_univ_two, coordinates, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.add_kronecker, Matrix.smul_kronecker,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

/-- The same two matrix entries in the joint spectral basis, with the physical
Petz sandwich and the native BKM residual. The retained eigenbasis is arbitrary. -/
private theorem pair_entry_representations
    (Z H : Matrix (Fin 2 × E) (Fin 2 × E) ℂ) (hZ : Z.IsHermitian)
    (hP : (partialTraceRight Z).PosDef)
    (U : Matrix.unitaryGroup (Fin 2 × E) ℂ) (V : Matrix.unitaryGroup (Fin 2) ℂ)
    (eigenvalues : Fin 2 × E → ℝ) (p : Fin 2 → ℝ)
    (hZD : Z = U.val * diagReal eigenvalues * U.valᴴ)
    (hPD : partialTraceRight Z = V.val * diagReal p * V.valᴴ)
    (hp : ∀ a, 0 < p a) (i j : Fin 2 × E) (hi : 0 < eigenvalues i) (hj : 0 < eigenvalues j) :
    let u := (eigenvalues i + eigenvalues j)/2
    let β := (eigenvalues i - eigenvalues j)/(eigenvalues i + eigenvalues j)
    let g := Real.sqrt (eigenvalues i * eigenvalues j) / u
    let X := coordinates U H i j
    let C := fun a b : Fin 2 => coordinates V (partialTraceRight H) a b *
      coordinates U ((V.val * Matrix.single a b (1 : ℂ) * V.valᴴ) ⊗ₖ (1 : Matrix E E ℂ)) i j
    (∀ z ∈ Icc (-1 : ℝ) 1,
      coordinates U (D5.S3.Quantum.Divergence.UmegakiConditionalBKM.residual Z H ((z+1)/2)) i j =
        pairResidual (p 0) (p 1) u β X (C 0 0) (C 1 1) (C 0 1) (C 1 0) z) ∧
      coordinates U (H - BKMFlagRefinement.partialTracePetz Z (partialTraceRight H)) i j =
        pairPetzResidual (p 0) (p 1) u g X (C 0 0) (C 1 1) (C 0 1) (C 1 0) := by
  dsimp only
  let M := partialTraceRight H
  let P := partialTraceRight Z
  constructor
  · intro z hz
    let s := (z+1)/2
    have hs : s ∈ Icc (0 : ℝ) 1 := ⟨by dsimp [s]; linarith [hz.1],
      by dsimp [s]; linarith [hz.2]⟩
    let R := inverseMatrix P M s
    have hR (a b : Fin 2) : coordinates V R a b =
        coordinates V M a b * (((affine (p a) (p b) z)⁻¹ : ℝ) : ℂ) := by
      have h := congrArg (fun A => coordinates V A a b) (arithmetic_inverseMatrix P M s hP hs)
      rw [arithmetic_entry V hPD] at h
      change ((affine (p a) (p b) z : ℝ) : ℂ) * coordinates V R a b =
        coordinates V M a b at h
      have hn : ((affine (p a) (p b) z : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (affine_ab_pos (hp a) (hp b) hz).ne'
      rw [Complex.ofReal_inv, ← h]
      field_simp [hn] <;> ring
    have hEmbed : coordinates U (R ⊗ₖ (1 : Matrix E E ℂ)) i j =
        ∑ a : Fin 2, ∑ b : Fin 2, coordinates V R a b *
          coordinates U ((V.val*Matrix.single a b (1 : ℂ)*V.valᴴ) ⊗ₖ
            (1 : Matrix E E ℂ)) i j := by
      exact (congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ =>
        coordinates U (A ⊗ₖ (1 : Matrix E E ℂ)) i j) (from_coordinates V R).symm).trans
        (embed_entries U V (coordinates V R) i j)
    have hscale : (1-s)*eigenvalues i+s*eigenvalues j =
        (eigenvalues i+eigenvalues j)/2 * (1-((eigenvalues i-eigenvalues j)/(eigenvalues i+eigenvalues j))*z) := by
      dsimp [s]
      field_simp [(add_pos hi hj).ne'] <;> ring
    unfold D5.S3.Quantum.Divergence.UmegakiConditionalBKM.residual pairResidual response
    simp only [coordinates_sub, Matrix.sub_apply]
    change coordinates U H i j -
      coordinates U (arithmetic Z (R ⊗ₖ (1 : Matrix E E ℂ)) s) i j = _
    rw [arithmetic_entry U hZD, hEmbed, hscale]
    simp only [hR, Fin.sum_univ_two]
    ring
  · let S := mpow Z (1/2)
    let T := mpow P (-(1/2))
    have hS : coordinates U S = diagReal (fun k => Real.sqrt (eigenvalues k)) := by
      simp only [S, mpow_spectral U hZ hZD, ← Real.sqrt_eq_rpow, coordinates_spectral]
    have hT : coordinates V T = diagReal (fun a => (Real.sqrt (p a))⁻¹) := by
      dsimp only [T]
      rw [mpow_spectral V hP.isHermitian hPD, coordinates_spectral]
      congr 1
      funext a
      rw [Real.rpow_neg (hp a).le, ← Real.sqrt_eq_rpow]
    let B := coordinates V (T*M*T)
    have hB (a b : Fin 2) : B a b =
        coordinates V M a b * (((Real.sqrt (p a*p b))⁻¹ : ℝ) : ℂ) := by
      simp only [B, coordinates_mul, hT, Matrix.mul_diagonal, Matrix.diagonal_mul,
        Real.sqrt_mul (hp a).le, mul_inv, Complex.ofReal_mul]
      ring
    have hEmbed : coordinates U ((T*M*T) ⊗ₖ (1 : Matrix E E ℂ)) i j =
        ∑ a : Fin 2, ∑ b : Fin 2, B a b *
          coordinates U ((V.val*Matrix.single a b (1 : ℂ)*V.valᴴ) ⊗ₖ
            (1 : Matrix E E ℂ)) i j := by
      exact (congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ =>
        coordinates U (A ⊗ₖ (1 : Matrix E E ℂ)) i j)
        (from_coordinates V (T*M*T)).symm).trans (embed_entries U V B i j)
    have hu : 0 < (eigenvalues i+eigenvalues j)/2 := by positivity
    have hscale : (eigenvalues i+eigenvalues j)/2 * (Real.sqrt (eigenvalues i*eigenvalues j) / ((eigenvalues i+eigenvalues j)/2)) =
        Real.sqrt (eigenvalues i) * Real.sqrt (eigenvalues j) := by
      rw [mul_div_cancel₀ _ hu.ne', Real.sqrt_mul hi.le]
    unfold partialTracePetz lift pairPetzResidual
    simp only [coordinates_sub, Matrix.sub_apply]
    change coordinates U H i j -
      coordinates U (S*((T*M*T) ⊗ₖ (1 : Matrix E E ℂ))*S) i j = _
    rw [coordinates_mul, coordinates_mul, hS, hscale]
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, hEmbed, hB, Fin.sum_univ_two,
      Complex.ofReal_mul]
    ring

/-- Equation (4) and the bound from (5)–(6) for actual matrix
entries. Only the two selected joint eigenvalues need to be positive. -/
theorem physical_entry_arcsine_and_bound
    (Z H : Matrix (Fin 2 × E) (Fin 2 × E) ℂ) (hZ : Z.IsHermitian)
    (hP : (partialTraceRight Z).PosDef)
    (U : Matrix.unitaryGroup (Fin 2 × E) ℂ) (V : Matrix.unitaryGroup (Fin 2) ℂ)
    (eigenvalues : Fin 2 × E → ℝ) (p : Fin 2 → ℝ)
    (hZD : Z = U.val * Matrix.diagonal (fun k => (eigenvalues k : ℂ)) * U.valᴴ)
    (hPD : partialTraceRight Z = V.val * Matrix.diagonal (fun a => (p a : ℂ)) * V.valᴴ)
    (hp : ∀ a, 0 < p a) (hpq : p 0 + p 1 = 1)
    (i j : Fin 2 × E) (hi : 0 < eigenvalues i) (hj : 0 < eigenvalues j) :
    let u := (eigenvalues i + eigenvalues j)/2
    let β := (eigenvalues i - eigenvalues j)/(eigenvalues i + eigenvalues j)
    let g := Real.sqrt (eigenvalues i * eigenvalues j) / u
    let F := fun z : ℝ => (U.valᴴ * D5.S3.Quantum.Divergence.UmegakiConditionalBKM.residual Z H ((z+1)/2) * U.val) i j
    let Y := (U.valᴴ * (H - BKMFlagRefinement.partialTracePetz Z (partialTraceRight H)) * U.val) i j
    Y = (g : ℂ) * arcIntegral (fun z => F z / ((1-β*z : ℝ) : ℂ)) ∧
      Complex.normSq Y ≤ parityMultiplier (2*Real.sqrt (p 0 * p 1)) *
        (∫ z in Ioo (-1 : ℝ) 1, Complex.normSq (F z) / (1-β*z) / 2) := by
  let u := (eigenvalues i+eigenvalues j)/2
  let β := (eigenvalues i-eigenvalues j)/(eigenvalues i+eigenvalues j)
  let g := Real.sqrt (eigenvalues i * eigenvalues j) / u
  let X := coordinates U H i j
  let C := fun a b : Fin 2 => coordinates V (partialTraceRight H) a b *
    coordinates U ((V.val * Matrix.single a b (1 : ℂ) * V.valᴴ) ⊗ₖ (1 : Matrix E E ℂ)) i j
  let F := fun z : ℝ => coordinates U (D5.S3.Quantum.Divergence.UmegakiConditionalBKM.residual Z H ((z+1)/2)) i j
  let Y := coordinates U (H-partialTracePetz Z (partialTraceRight H)) i j
  change Y = (g : ℂ) * arcIntegral (fun z => F z / ((1-β*z : ℝ) : ℂ)) ∧
    Complex.normSq Y ≤ parityMultiplier (2*Real.sqrt (p 0*p 1)) *
      (∫ z in Ioo (-1 : ℝ) 1, Complex.normSq (F z)/(1-β*z)/2)
  have hg : 0 < g := by dsimp [g, u]; positivity
  have hgb : g^2+β^2=1 := by
    dsimp [g, u, β]
    rw [div_pow, Real.sq_sqrt (mul_nonneg hi.le hj.le)]
    field_simp [(add_pos hi hj).ne'] <;> ring
  obtain ⟨hF,hY⟩ := pair_entry_representations Z H hZ hP U V eigenvalues p hZD hPD hp i j hi hj
  change Y = pairPetzResidual (p 0) (p 1) u g X (C 0 0) (C 1 1) (C 0 1) (C 1 0) at hY
  change EqOn F (pairResidual (p 0) (p 1) u β X (C 0 0) (C 1 1) (C 0 1) (C 1 0))
    (Icc (-1 : ℝ) 1) at hF
  let F' := pairResidual (p 0) (p 1) u β X (C 0 0) (C 1 1) (C 0 1) (C 1 0)
  have hArc : arcIntegral (fun z => F z / ((1-β*z : ℝ) : ℂ)) =
      arcIntegral (fun z => F' z / ((1-β*z : ℝ) : ℂ)) := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro z hz
    change arcsineDensity z • (F z / ((1-β*z : ℝ) : ℂ)) =
      arcsineDensity z • (F' z / ((1-β*z : ℝ) : ℂ))
    rw [show F z = F' z from hF (Ioo_subset_Icc_self hz)]
  have hEnergy : (∫ z in Ioo (-1 : ℝ) 1, Complex.normSq (F z) / (1-β*z) / 2) =
      ∫ z in Ioo (-1 : ℝ) 1, Complex.normSq (F' z) / (1-β*z) / 2 := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro z hz
    dsimp only
    rw [show F z = F' z from hF (Ioo_subset_Icc_self hz)]
  rw [hY, hArc, hEnergy]
  exact ⟨pair_petz_arcsine _ _ u g β _ _ _ _ _ (hp 0) (hp 1) hg hgb,
    pair_bound _ _ u g β _ _ _ _ _ (hp 0) (hp 1) hpq hg hgb⟩

#print axioms physical_entry_arcsine_and_bound


open D5.S3.Quantum.Divergence.UmegakiConditionalBKM (arithmetic_inverse_pairing_intervalIntegrable)
open D5.S3.Quantum.Divergence.UmegakiConditionalKernel (q)
open D5.S3.Quantum.Divergence.UmegakiReferenceTransport (partialTraceRight_posDef)
open D5.S3.Quantum.Divergence.UmegakiArithmeticBKM
  (hs_pair_spectral arithmetic_inverse_pairing_eq_logDeriv matrixHS)
open D5.S3.Divergence.LogDerivTrace (logDeriv)

private lemma interval_recenter (f : ℝ → ℝ) :
    (∫ z in Ioo (-1 : ℝ) 1, f ((z+1)/2) / 2) = ∫ s in (0 : ℝ)..1, f s := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num)]
  simp_rw [div_eq_mul_inv]
  rw [intervalIntegral.integral_mul_const]
  have h : (∫ z in (-1 : ℝ)..1, f ((1/2)*z+1/2)) =
      2 * ∫ s in (0 : ℝ)..1, f s := by
    convert intervalIntegral.integral_comp_mul_add (f := f) (a := (-1 : ℝ)) (b := 1)
      (c := (1/2 : ℝ)) (by norm_num) (1/2) using 1 <;> norm_num [smul_eq_mul]
  have he (z : ℝ) : (z+1) * 2⁻¹ = 2⁻¹ * z + 2⁻¹ := by ring
  simp_rw [he]
  simp only [one_div] at h
  rw [h]
  ring

/-- On a faithful joint reference, the weighted sum of the squared physical
Petz residual entries is bounded by the joint-minus-marginal BKM form. -/
theorem faithful_weighted_tangent [Nonempty E]
    (Z H : Matrix (Fin 2 × E) (Fin 2 × E) ℂ) (hZ : Z.PosDef)
    (htrace : (partialTraceRight Z).trace.re = 1) :
    let P := partialTraceRight Z
    let M := partialTraceRight H
    let U := hZ.isHermitian.eigenvectorUnitary
    let lam := hZ.isHermitian.eigenvalues
    let p := (partialTraceRight_posDef Z hZ).isHermitian.eigenvalues
    let Y := coordinates U (H - partialTracePetz Z M)
    ∑ i, ∑ j, Complex.normSq (Y i j) / ((lam i + lam j)/2) ≤
      parityMultiplier (2*Real.sqrt (p 0*p 1)) *
        ((Hᴴ * logDeriv Z H).trace.re - (Mᴴ * logDeriv P M).trace.re) := by
  let P := partialTraceRight Z
  let M := partialTraceRight H
  let hP : P.PosDef := partialTraceRight_posDef Z hZ
  let U := hZ.isHermitian.eigenvectorUnitary
  let V := hP.isHermitian.eigenvectorUnitary
  let lam := hZ.isHermitian.eigenvalues
  let p := hP.isHermitian.eigenvalues
  let Y := coordinates U (H - partialTracePetz Z M)
  let K := parityMultiplier (2*Real.sqrt (p 0*p 1))
  change ∑ i, ∑ j, Complex.normSq (Y i j) / ((lam i + lam j)/2) ≤
    K * ((Hᴴ * logDeriv Z H).trace.re - (Mᴴ * logDeriv P M).trace.re)
  have hZD : Z = U.val * diagReal lam * U.valᴴ := hZ.isHermitian.spectral_theorem
  have hPD : P = V.val * diagReal p * V.valᴴ := hP.isHermitian.spectral_theorem
  have hp (a : Fin 2) : 0 < p a := hP.eigenvalues_pos a
  have hpq : p 0 + p 1 = 1 := by
    have ht : P.trace = (diagReal p).trace := by
      conv_lhs => rw [hPD]
      have hV : V.valᴴ * V.val = 1 := Unitary.coe_star_mul_self V
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hV, one_mul]
    change P.trace.re = 1 at htrace
    simpa [ht, Matrix.trace_diagonal, Fin.sum_univ_two] using htrace
  let B := fun (i j : Fin 2 × E) (s : ℝ) => (1-s)*lam i+s*lam j
  let f := fun (i j : Fin 2 × E) (s : ℝ) =>
    Complex.normSq (coordinates U (D5.S3.Quantum.Divergence.UmegakiConditionalBKM.residual Z H s) i j) / B i j s
  have hscale (i j : Fin 2 × E) (z : ℝ) :
      B i j ((z+1)/2) = (lam i+lam j)/2 * (1-(lam i-lam j)/(lam i+lam j)*z) := by
    dsimp [B]
    have hn : lam i + lam j ≠ 0 := (add_pos (hZ.eigenvalues_pos i) (hZ.eigenvalues_pos j)).ne'
    field_simp [hn] <;> ring
  have hentry (i j : Fin 2 × E) :
      Complex.normSq (Y i j) / ((lam i+lam j)/2) ≤ K * ∫ s in (0 : ℝ)..1, f i j s := by
    have hu : 0 < (lam i+lam j)/2 := by
      have := hZ.eigenvalues_pos i
      have := hZ.eigenvalues_pos j
      positivity
    have he := (physical_entry_arcsine_and_bound Z H hZ.isHermitian hP U V lam p
      hZD hPD hp hpq i j (hZ.eigenvalues_pos i) (hZ.eigenvalues_pos j)).2
    dsimp only at he
    have hint :
        (∫ z in Ioo (-1 : ℝ) 1, Complex.normSq
          (coordinates U (D5.S3.Quantum.Divergence.UmegakiConditionalBKM.residual Z H ((z+1)/2)) i j) /
          (1-(lam i-lam j)/(lam i+lam j)*z) / 2) =
        (∫ s in (0 : ℝ)..1, f i j s) * ((lam i+lam j)/2) := by
      rw [← interval_recenter, ← integral_mul_const]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro z hz
      change _ = f i j ((z+1)/2) / 2 * ((lam i+lam j)/2)
      unfold f
      rw [hscale]
      simp only [div_div]
      have hβ : ((lam i-lam j)/(lam i+lam j))^2 < 1 := by
        have hi := hZ.eigenvalues_pos i
        have hj := hZ.eigenvalues_pos j
        rw [div_pow, div_lt_iff₀ (sq_pos_of_pos (add_pos hi hj))]
        nlinarith [mul_pos hi hj]
      have hn : 1-(lam i-lam j)/(lam i+lam j)*z ≠ 0 :=
        (affine_pos hβ (Ioo_subset_Icc_self hz)).ne'
      generalize hr : 1-(lam i-lam j)/(lam i+lam j)*z = r at hn ⊢
      generalize hv : (lam i+lam j)/2 = v at hu ⊢
      field_simp [hu.ne', hn]
    rw [hint, ← mul_assoc] at he
    exact (div_le_iff₀ hu).2 he
  have hq (A : Matrix (Fin 2 × E) (Fin 2 × E) ℂ) (s : ℝ)
      (hs : s ∈ Icc (0 : ℝ) 1) :
      q Z A s = ∑ i, ∑ j, Complex.normSq (coordinates U A i j) / B i j s := by
    rw [show q Z A s = _ from hs_pair_spectral Z A hZ s hs]
    simp only [B, div_eq_mul_inv]
    rfl
  have hpair {n : Type} [Fintype n] [DecidableEq n]
      (A X : Matrix n n ℂ) (hA : A.PosDef) :
      (Xᴴ * logDeriv A X).trace.re = ∫ s in (0 : ℝ)..1, q A X s :=
    arithmetic_inverse_pairing_eq_logDeriv A X hA
  have hf (i j : Fin 2 × E) : IntervalIntegrable (f i j) volume 0 1 := by
    let β := (lam i-lam j)/(lam i+lam j)
    let u := (lam i+lam j)/2
    let C := fun a b : Fin 2 => coordinates V M a b *
      coordinates U ((V.val * Matrix.single a b (1 : ℂ) * V.valᴴ) ⊗ₖ (1 : Matrix E E ℂ)) i j
    let F := pairResidual (p 0) (p 1) u β (coordinates U H i j)
      (C 0 0) (C 1 1) (C 0 1) (C 1 0)
    have hF : ContinuousOn F (Icc (-1 : ℝ) 1) := by
      unfold F pairResidual
      exact continuousOn_const.sub ((by fun_prop : Continuous
        (fun z : ℝ => ((u * (1-β*z) : ℝ) : ℂ))).continuousOn.mul
        (response_continuous (hp 0) (hp 1) _ _ _ _))
    have hEquiv := (pair_entry_representations Z H hZ.isHermitian hP U V lam p
      hZD hPD hp i j (hZ.eigenvalues_pos i) (hZ.eigenvalues_pos j)).1
    have hmap : MapsTo (fun s : ℝ => 2*s-1) (Icc (0 : ℝ) 1) (Icc (-1 : ℝ) 1) := by
      intro s hs
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hden : Continuous (B i j) := by unfold B; fun_prop
    have hn (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : B i j s ≠ 0 := by
      have hh := affine_ab_pos (hZ.eigenvalues_pos i) (hZ.eigenvalues_pos j) (hmap hs)
      convert hh.ne' using 1
      unfold B affine
      ring
    have hcont : ContinuousOn (fun s => Complex.normSq (F (2*s-1)) / B i j s)
        (Icc (0 : ℝ) 1) :=
      (Complex.continuous_normSq.comp_continuousOn (hF.comp (by fun_prop) hmap)).div
        hden.continuousOn hn
    apply (hcont.intervalIntegrable_of_Icc (μ := volume) zero_le_one).congr
    rw [uIoc_of_le zero_le_one]
    intro s hs
    have hh := hEquiv (2*s-1) (hmap (Ioc_subset_Icc_self hs))
    rw [show (2*s-1+1)/2 = s by ring] at hh
    change coordinates U (D5.S3.Quantum.Divergence.UmegakiConditionalBKM.residual Z H s) i j = F (2*s-1) at hh
    simp [f, hh]
  have hsum :
      (∑ i, ∑ j, ∫ s in (0 : ℝ)..1, f i j s) =
        (Hᴴ * logDeriv Z H).trace.re - (Mᴴ * logDeriv P M).trace.re := by
    rw [hpair Z H hZ, hpair P M hP, ← intervalIntegral.integral_sub
      (arithmetic_inverse_pairing_intervalIntegrable Z H hZ)
      (arithmetic_inverse_pairing_intervalIntegrable P M hP)]
    have hs (i : Fin 2 × E) :
        (∫ s in (0 : ℝ)..1, ∑ j, f i j s) = ∑ j, ∫ s in (0 : ℝ)..1, f i j s :=
      intervalIntegral.integral_finsetSum (fun j _ => hf i j)
    have hi' (i : Fin 2 × E) : IntervalIntegrable (fun s => ∑ j, f i j s) volume 0 1 := by
      simpa only [Finset.sum_fn] using (IntervalIntegrable.sum Finset.univ (fun j _ => hf i j))
    simp_rw [← hs]
    rw [← intervalIntegral.integral_finsetSum (fun i _ => hi' i)]
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le zero_le_one]
    intro s hs
    change (∑ i, ∑ j, f i j s) = q Z H s - q (partialTraceRight Z) (partialTraceRight H) s
    rw [D5.S3.Quantum.Divergence.UmegakiConditionalBKM.quadratic_difference_eq_residual Z H s hZ hs, hq _ _ hs]
  rw [← hsum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => hentry i j

#print axioms faithful_weighted_tangent

end PhysicalEntries

end D5.S3.Quantum.Recovery.PetzTangentPhysical
