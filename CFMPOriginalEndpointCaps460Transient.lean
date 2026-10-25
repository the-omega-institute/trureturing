import CFMPOriginalForward427
import Mathlib.Analysis.SpecialFunctions.Arsinh

/- Transient, uncompiled candidate. Canonical admission is a separate task. -/
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open D5.S3.Geometry.Hyperideal.TwoLengthAngleSum (rawCos)
open CFMPOriginalForward390 (angle angleD)

namespace CFMPOriginalEndpointCaps444Transient

private theorem determinant_factor (θ a b : ℝ) :
    angleD (Real.cos θ) (Real.cos a) (Real.cos b) =
      (Real.cos θ + Real.cos (a+b)) * (Real.cos θ + Real.cos (a-b)) := by
  have ha : Real.sin a ^ 2 = 1 - Real.cos a ^ 2 := by
    nlinarith only [Real.sin_sq_add_cos_sq a]
  have hb : Real.sin b ^ 2 = 1 - Real.cos b ^ 2 := by
    nlinarith only [Real.sin_sq_add_cos_sq b]
  calc
    _ = (Real.cos θ + Real.cos a * Real.cos b)^2 -
        (Real.sin a * Real.sin b)^2 := by
      rw [mul_pow, ha, hb]
      dsimp only [angleD]
      ring
    _ = _ := by rw [Real.cos_add, Real.cos_sub]; ring

private theorem cap_ratio (θ a b σ : ℝ)
    (hθ : 0 < θ) (ha : 0 < a) (hb : 0 < b)
    (hcap : θ+a+b ≤ σ) (hσ : σ ≤ Real.pi/2) :
    Real.sin θ / Real.sqrt (angleD (Real.cos θ) (Real.cos a) (Real.cos b)) <
      Real.tan (σ/2) := by
  have hπ := Real.pi_pos
  have hθσ : θ < σ := by linarith
  have hσ0 : 0 < σ := lt_trans hθ hθσ
  have hθπ : θ < Real.pi := by linarith
  have haπ : a < Real.pi := by linarith
  have hbπ : b < Real.pi := by linarith
  have hsθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ hθπ
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha haπ
  have hsb : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb hbπ
  have hsc : 0 < Real.sin (σ-θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hcθ : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcσθ : 0 < Real.cos (σ-θ) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hch : 0 < Real.cos (σ/2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have ht : 0 < Real.tan (σ/2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith)
  let d := Real.cos θ + Real.cos (σ-θ)
  let f := Real.cos θ + Real.cos (a+b)
  let g := Real.cos θ + Real.cos (a-b)
  let D := angleD (Real.cos θ) (Real.cos a) (Real.cos b)
  have hd : 0 < d := add_pos hcθ hcσθ
  have hcos : Real.cos (σ-θ) ≤ Real.cos (a+b) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
  have hdf : d ≤ f := by dsimp only [d, f]; linarith only [hcos]
  have hf : 0 < f := lt_of_lt_of_le hd hdf
  have hfg : f ≤ g := by
    dsimp only [f, g]
    rw [Real.cos_add, Real.cos_sub]
    nlinarith only [mul_pos hsa hsb]
  have hfactor : D = f*g := determinant_factor θ a b
  have hdD : d^2 ≤ D := by
    calc
      d^2 ≤ f^2 := by
        have hp := mul_nonneg (sub_nonneg.mpr hdf)
          (show 0 ≤ f+d by linarith only [hf, hd])
        nlinarith only [hp]
      _ = f*f := sq f
      _ ≤ f*g := mul_le_mul_of_nonneg_left hfg hf.le
      _ = D := hfactor.symm
  have hD : 0 < D := lt_of_lt_of_le (sq_pos_of_ne_zero hd.ne') hdD
  have hroot : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD
  have hdr : d ≤ Real.sqrt D := Real.le_sqrt_of_sq_le hdD
  have hcos_sum : Real.cos θ + Real.cos (σ-θ) =
      2 * Real.cos (σ/2) * Real.cos (θ-σ/2) := by
    calc
      _ = Real.cos ((θ-σ/2)+σ/2) + Real.cos (σ/2-(θ-σ/2)) := by
        congr 1 <;> congr 1 <;> ring
      _ = _ := by
        rw [Real.cos_add (θ-σ/2) (σ/2), Real.cos_sub (σ/2) (θ-σ/2)]
        ring
  have hsin_sum : Real.sin θ + Real.sin (σ-θ) =
      2 * Real.sin (σ/2) * Real.cos (θ-σ/2) := by
    calc
      _ = Real.sin ((θ-σ/2)+σ/2) + Real.sin (σ/2-(θ-σ/2)) := by
        congr 1 <;> congr 1 <;> ring
      _ = _ := by
        rw [Real.sin_add (θ-σ/2) (σ/2), Real.sin_sub (σ/2) (θ-σ/2)]
        ring
  have htrig : Real.tan (σ/2)*d = Real.sin θ + Real.sin (σ-θ) := by
    dsimp only [d]
    rw [hcos_sum, hsin_sum, Real.tan_eq_sin_div_cos]
    field_simp [hch.ne'] <;> ring
  have hstrict : Real.sin θ < Real.tan (σ/2)*d := by
    linarith only [htrig, hsc]
  apply (div_lt_iff₀ hroot).mpr
  exact lt_of_lt_of_le hstrict (mul_le_mul_of_nonneg_left hdr ht.le)

private theorem quotient_length_bound (X s z p q r t k : ℝ)
    (hX : 1 < X) (hs : 0 < s) (hsz : s^2+z^2=1)
    (hD1 : 0 < angleD z p q) (hD2 : 0 < angleD z t r) (hk : k < 1)
    (hquot : X = (s^2*k+p*r+q*t+z*(p*t+q*r)) /
      Real.sqrt (angleD z p q * angleD z t r)) :
    Real.arcosh X <
      Real.arsinh (s / Real.sqrt (angleD z p q)) +
      Real.arsinh (s / Real.sqrt (angleD z t r)) := by
  let D1 := angleD z p q
  let D2 := angleD z t r
  let C := p*r+q*t+z*(p*t+q*r)
  have hs2 : s^2 = 1-z^2 := by linarith only [hsz]
  have hresidual : (D1+s^2)*(D2+s^2)-C^2 = s^2*(p*t-q*r)^2 := by
    dsimp only [D1, D2, C, angleD]
    rw [hs2]
    ring
  have hC : C ≤ Real.sqrt ((D1+s^2)*(D2+s^2)) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith only [hresidual, mul_nonneg (sq_nonneg s) (sq_nonneg (p*t-q*r))]
  have hNum : s^2*k+C < s^2+Real.sqrt ((D1+s^2)*(D2+s^2)) := by
    have hp := mul_pos (sq_pos_of_ne_zero hs.ne') (sub_pos.mpr hk)
    nlinarith only [hp, hC]
  have hS1 : 0 < Real.sqrt D1 := Real.sqrt_pos.mpr hD1
  have hS2 : 0 < Real.sqrt D2 := Real.sqrt_pos.mpr hD2
  have hE : 0 < Real.sqrt (D1*D2) := Real.sqrt_pos.mpr (mul_pos hD1 hD2)
  have hA : 0 ≤ D1+s^2 := add_nonneg hD1.le (sq_nonneg s)
  have hB : 0 ≤ D2+s^2 := add_nonneg hD2.le (sq_nonneg s)
  have hquot' : X = (s^2*k+C)/Real.sqrt (D1*D2) := by
    rw [hquot]
    dsimp only [C, D1, D2]
    congr 1
    ring
  have hupper : X < (s^2+Real.sqrt ((D1+s^2)*(D2+s^2))) /
      Real.sqrt (D1*D2) := by
    rw [hquot']
    exact div_lt_div_of_pos_right hNum hE
  have hr1 : 1+(s/Real.sqrt D1)^2 = (D1+s^2)/D1 := by
    rw [div_pow, Real.sq_sqrt hD1.le]
    rw [add_div, div_self (show D1 ≠ 0 from hD1.ne')]
  have hr2 : 1+(s/Real.sqrt D2)^2 = (D2+s^2)/D2 := by
    rw [div_pow, Real.sq_sqrt hD2.le]
    rw [add_div, div_self (show D2 ≠ 0 from hD2.ne')]
  have he1 : Real.sqrt (1+(s/Real.sqrt D1)^2) =
      Real.sqrt (D1+s^2)/Real.sqrt D1 := by
    rw [hr1, Real.sqrt_div hA D1]
  have he2 : Real.sqrt (1+(s/Real.sqrt D2)^2) =
      Real.sqrt (D2+s^2)/Real.sqrt D2 := by
    rw [hr2, Real.sqrt_div hB D2]
  have hcosh : Real.cosh (Real.arsinh (s/Real.sqrt D1) +
      Real.arsinh (s/Real.sqrt D2)) =
      (s^2+Real.sqrt ((D1+s^2)*(D2+s^2)))/Real.sqrt (D1*D2) := by
    rw [Real.cosh_add, Real.cosh_arsinh, Real.cosh_arsinh,
      Real.sinh_arsinh, Real.sinh_arsinh, he1, he2]
    rw [Real.sqrt_mul hD1.le D2, Real.sqrt_mul hA (D2+s^2)]
    field_simp [hS1.ne', hS2.ne'] <;> ring
  have hsum : 0 < Real.arsinh (s/Real.sqrt D1) +
      Real.arsinh (s/Real.sqrt D2) :=
    add_pos (Real.arsinh_pos_iff.mpr (div_pos hs hS1))
      (Real.arsinh_pos_iff.mpr (div_pos hs hS2))
  have hh : Real.cosh (Real.arcosh X) <
      Real.cosh (Real.arsinh (s/Real.sqrt D1)+Real.arsinh (s/Real.sqrt D2)) := by
    rw [Real.cosh_arcosh hX.le, hcosh]
    exact hupper
  have habs := Real.cosh_lt_cosh.mp hh
  simpa only [abs_of_pos (Real.arcosh_pos hX), abs_of_pos hsum] using habs

/-- The unequal endpoint caps, for the six original slots of the supplied x. -/
theorem original_endpoint_caps (x : Fin 6 → ℝ)
    (hx : ∀ q, 1 < x q) (hc : ∀ q, -1 < rawCos x q ∧ rawCos x q < 1)
    (σ1 σ2 : ℝ)
    (hcap1 : Real.arccos (rawCos x 0)+Real.arccos (rawCos x 1)+
      Real.arccos (rawCos x 2) ≤ σ1)
    (hcap2 : Real.arccos (rawCos x 0)+Real.arccos (rawCos x 4)+
      Real.arccos (rawCos x 5) ≤ σ2)
    (hσ1 : σ1 ≤ Real.pi/2) (hσ2 : σ2 ≤ Real.pi/2) :
    Real.arcosh (x 0) <
      Real.arsinh (Real.tan (σ1/2)) + Real.arsinh (Real.tan (σ2/2)) := by
  let α := angle x
  have hα (q : Fin 6) : 0 < α q := Real.arccos_pos.mpr (hc q).2
  have hαπ : α 0 < Real.pi := Real.arccos_lt_pi.mpr (hc 0).1
  have hs : 0 < Real.sin (α 0) := Real.sin_pos_of_pos_of_lt_pi (hα 0) hαπ
  have hk : Real.cos (α 3) < 1 := by
    have he : Real.cos (α 3) = rawCos x 3 :=
      Real.cos_arccos (hc 3).1.le (hc 3).2.le
    rw [he]
    exact (hc 3).2
  obtain ⟨_, _, _, _, hD1, hD2, hquot⟩ := CFMPOriginalForward390.forward x hx hc
  have hlength := quotient_length_bound (x 0) (Real.sin (α 0)) (Real.cos (α 0))
    (Real.cos (α 1)) (Real.cos (α 2)) (Real.cos (α 5)) (Real.cos (α 4))
    (Real.cos (α 3)) (hx 0) hs (Real.sin_sq_add_cos_sq (α 0)) hD1 hD2 hk hquot
  change α 0+α 1+α 2 ≤ σ1 at hcap1
  change α 0+α 4+α 5 ≤ σ2 at hcap2
  have hratio1 := cap_ratio (α 0) (α 1) (α 2) σ1
    (hα 0) (hα 1) (hα 2) hcap1 hσ1
  have hratio2 := cap_ratio (α 0) (α 4) (α 5) σ2
    (hα 0) (hα 4) (hα 5) hcap2 hσ2
  exact lt_trans hlength
    (add_lt_add (Real.arsinh_strictMono hratio1) (Real.arsinh_strictMono hratio2))

private theorem tan_half_sq (σ : ℝ) (hσ0 : 0 < σ) (hσ : σ ≤ Real.pi/2) :
    (Real.tan (σ/2))^2 = (1-Real.cos σ)/(1+Real.cos σ) := by
  have hπ := Real.pi_pos
  have hch : 0 < Real.cos (σ/2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcσ : 0 ≤ Real.cos σ := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hσ⟩
  have hden : 0 < 1+Real.cos σ := by linarith only [hcσ]
  have he : Real.cos σ = 2*Real.cos (σ/2)^2-1 := by
    calc
      _ = Real.cos (2*(σ/2)) := by congr 1; ring
      _ = _ := Real.cos_two_mul (σ/2)
  have hs : Real.sin (σ/2)^2 = 1-Real.cos (σ/2)^2 := by
    nlinarith only [Real.sin_sq_add_cos_sq (σ/2)]
  rw [Real.tan_eq_sin_div_cos, div_pow]
  apply (div_eq_div_iff (pow_ne_zero 2 hch.ne') hden.ne').mpr
  rw [hs, he]
  ring

private theorem cosh_double_arsinh (t : ℝ) :
    Real.cosh (Real.arsinh t + Real.arsinh t) = 1+2*t^2 := by
  calc
    _ = Real.cosh (2*Real.arsinh t) := by congr 1; ring
    _ = Real.cosh (Real.arsinh t)^2+Real.sinh (Real.arsinh t)^2 :=
      Real.cosh_two_mul (Real.arsinh t)
    _ = _ := by
      rw [Real.cosh_arsinh, Real.sinh_arsinh,
        Real.sq_sqrt (show 0 ≤ 1+t^2 by positivity)]
      ring

/-- Equal caps give both the length bound and its rational original-x form. -/
theorem original_equal_endpoint_caps (x : Fin 6 → ℝ)
    (hx : ∀ q, 1 < x q) (hc : ∀ q, -1 < rawCos x q ∧ rawCos x q < 1)
    (σ : ℝ)
    (hcap1 : Real.arccos (rawCos x 0)+Real.arccos (rawCos x 1)+
      Real.arccos (rawCos x 2) ≤ σ)
    (hcap2 : Real.arccos (rawCos x 0)+Real.arccos (rawCos x 4)+
      Real.arccos (rawCos x 5) ≤ σ)
    (hσ : σ ≤ Real.pi/2) :
    Real.arcosh (x 0) < 2*Real.arsinh (Real.tan (σ/2)) ∧
      x 0 < (3-Real.cos σ)/(1+Real.cos σ) := by
  have hlength := original_endpoint_caps x hx hc σ σ hcap1 hcap2 hσ hσ
  have hσ0 : 0 < σ := by
    have ha0 := Real.arccos_pos.mpr (hc 0).2
    have ha1 := Real.arccos_pos.mpr (hc 1).2
    have ha2 := Real.arccos_pos.mpr (hc 2).2
    linarith only [hcap1, ha0, ha1, ha2]
  have ht : 0 < Real.tan (σ/2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith [Real.pi_pos])
  have ha : 0 < Real.arsinh (Real.tan (σ/2)) := Real.arsinh_pos_iff.mpr ht
  have hcσ : 0 ≤ Real.cos σ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hσ⟩
  have hden : 0 < 1+Real.cos σ := by linarith only [hcσ]
  have hclosed : Real.cosh (Real.arsinh (Real.tan (σ/2))+
      Real.arsinh (Real.tan (σ/2))) = (3-Real.cos σ)/(1+Real.cos σ) := by
    rw [cosh_double_arsinh, tan_half_sq σ hσ0 hσ]
    field_simp [hden.ne'] <;> ring
  have hh : Real.cosh (Real.arcosh (x 0)) <
      Real.cosh (Real.arsinh (Real.tan (σ/2))+Real.arsinh (Real.tan (σ/2))) := by
    apply Real.cosh_lt_cosh.mpr
    simpa only [abs_of_pos (Real.arcosh_pos (hx 0)), abs_of_pos (add_pos ha ha)]
      using hlength
  refine ⟨?_, ?_⟩
  · simpa only [two_mul] using hlength
  · rw [Real.cosh_arcosh (hx 0).le, hclosed] at hh
    exact hh

end CFMPOriginalEndpointCaps444Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPOriginalEndpointCaps444Transient.original_endpoint_caps,
      ``CFMPOriginalEndpointCaps444Transient.original_equal_endpoint_caps] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP460 missing declaration {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP460 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP460 CHECKED {name} axioms={axioms}"
