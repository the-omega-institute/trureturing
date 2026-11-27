import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Fourier.ThetaDerivativeBounds

open D5.S3.Fourier.PlanarTheta
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.Support.ThetaFourierBounds
noncomputable section

abbrev fourierSignature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def sineActual : Realization fourierSignature :=
  realize fourierSignature (fun _ s b => thetaSine s b) (fun e => nomatch e)

def sineRejected : Realization fourierSignature :=
  realize fourierSignature (fun _ _ _ => 1) (fun e => nomatch e)

def derivativeActual : Realization fourierSignature :=
  realize fourierSignature (fun _ s b => deriv (thetaFourier s) b) (fun e => nomatch e)

def derivativeRejected : Realization fourierSignature :=
  realize fourierSignature (fun _ _ _ => 0) (fun e => nomatch e)

def derivativeArena : Arena where
  signature := fourierSignature
  Law R := ∀ {s : ℝ}, 0 < s → ∀ b : ℝ,
    HasDerivAt (thetaFourier s) (-4 * Real.pi * R.readout () s b) b

def firstModeArena : Arena where
  signature := fourierSignature
  Law R := ∀ {s : ℝ}, 0 < s → ∀ b : ℝ,
    |R.readout () s b - Real.exp (-Real.pi * s) * Real.sin (2 * Real.pi * b)| ≤
      Real.exp (-Real.pi * s) * |Real.sin (2 * Real.pi * b)| * gaussianTail s

def boundsArena : Arena where
  signature := fourierSignature
  Law R := ∀ {s : ℝ}, 0 < s → ∀ b : ℝ,
    |R.readout () s b| ≤
      4 * Real.pi * Real.exp (-Real.pi * s) * |Real.sin (2 * Real.pi * b)| *
        (1 + gaussianTail s) ∧
    (0 ≤ b → b ≤ 1 / 2 →
      4 * Real.pi * Real.exp (-Real.pi * s) * Real.sin (2 * Real.pi * b) *
        (1 - gaussianTail s) ≤ -R.readout () s b)

private theorem derivative_bridge : (type_of% (@hasDerivAt_thetaFourier)) ↔
    derivativeArena.Law sineActual := Iff.rfl

private theorem firstMode_bridge : (type_of% (@thetaSine_first_mode)) ↔
    firstModeArena.Law sineActual := Iff.rfl

private theorem bounds_bridge : (type_of% (@thetaFourier_derivative_bounds)) ↔
    boundsArena.Law derivativeActual := Iff.rfl

private theorem sine_zero (s : ℝ) : thetaSine s 0 = 0 := by
  simp [thetaSine]

private theorem sine_quarter_pos : 0 < thetaSine 1 (1 / 4) := by
  have h := thetaSine_first_mode (s := 1) (by norm_num) (1 / 4)
  have he : Real.sin (2 * Real.pi * (1 / 4)) = 1 := by
    rw [show 2 * Real.pi * (1 / 4) = Real.pi / 2 by ring, Real.sin_pi_div_two]
  rw [he, abs_one, mul_one, mul_one] at h
  have ht := (gaussian_tail_bound (v := 1) (by norm_num)).2.2
  have hp := Real.exp_pos (-Real.pi * 1)
  have hh := mul_lt_mul_of_pos_left ht hp
  simp only [mul_one] at hp hh
  have hh' := (abs_le.mp h).1
  nlinarith

private theorem sine_dependence : ObservationalDependence fourierSignature sineActual := by
  intro i
  refine ⟨1, 0, 1 / 4, ?_⟩
  change thetaSine 1 0 ≠ thetaSine 1 (1 / 4)
  rw [sine_zero]
  exact ne_of_lt sine_quarter_pos

theorem derivative_dependence :
    ObservationalDependence fourierSignature derivativeActual := by
  intro i
  refine ⟨1, 0, 1 / 4, ?_⟩
  change deriv (thetaFourier 1) 0 ≠ deriv (thetaFourier 1) (1 / 4)
  rw [(hasDerivAt_thetaFourier (by norm_num : (0 : ℝ) < 1) 0).deriv,
    (hasDerivAt_thetaFourier (by norm_num : (0 : ℝ) < 1) (1 / 4)).deriv, sine_zero]
  have hp := mul_pos Real.pi_pos sine_quarter_pos
  nlinarith

private theorem derivative_rejected : ¬ derivativeArena.Law sineRejected := by
  intro h
  have h1 := h (s := 1) (by norm_num) 0
  have h0 := hasDerivAt_thetaFourier (by norm_num : (0 : ℝ) < 1) 0
  have he := h1.unique h0
  simp only [sineRejected, realize, mul_one, sine_zero, mul_zero] at he
  linarith [Real.pi_pos]

private theorem firstMode_rejected : ¬ firstModeArena.Law sineRejected := by
  intro h
  have h1 := h (s := 1) (by norm_num) 0
  norm_num [sineRejected, realize] at h1

private theorem bounds_rejected : ¬ boundsArena.Law derivativeRejected := by
  intro h
  have h1 := (h (s := 1) (by norm_num) (1 / 4)).2 (by norm_num) (by norm_num)
  have he : Real.sin (2 * Real.pi * (1 / 4)) = 1 := by
    rw [show 2 * Real.pi * (1 / 4) = Real.pi / 2 by ring, Real.sin_pi_div_two]
  simp only [derivativeRejected, realize, neg_zero, he, mul_one] at h1
  have hp : 0 < 4 * Real.pi * Real.exp (-Real.pi * 1) := by positivity
  have ht := (gaussian_tail_bound (v := 1) (by norm_num)).2.2
  have hh := mul_pos hp (show 0 < 1 - gaussianTail 1 by linarith)
  norm_num only [mul_one] at hh
  linarith

def derivativeRegistration : Registration derivativeArena
    (type_of% (@hasDerivAt_thetaFourier)) where
  actual := sineActual
  bridge := derivative_bridge
  variation := ⟨@hasDerivAt_thetaFourier, sineRejected, derivative_rejected⟩
  sensitivity := ⟨fun i => ⟨sineRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, derivative_rejected⟩, fun e => nomatch e⟩
  dependence := sine_dependence

def firstModeRegistration : Registration firstModeArena
    (type_of% (@thetaSine_first_mode)) where
  actual := sineActual
  bridge := firstMode_bridge
  variation := ⟨@thetaSine_first_mode, sineRejected, firstMode_rejected⟩
  sensitivity := ⟨fun i => ⟨sineRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, firstMode_rejected⟩, fun e => nomatch e⟩
  dependence := sine_dependence

def boundsRegistration : Registration boundsArena
    (type_of% (@thetaFourier_derivative_bounds)) where
  actual := derivativeActual
  bridge := bounds_bridge
  variation := ⟨@thetaFourier_derivative_bounds, derivativeRejected, bounds_rejected⟩
  sensitivity := ⟨fun i => ⟨derivativeRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, bounds_rejected⟩, fun e => nomatch e⟩
  dependence := derivative_dependence

def controlArena : Arena where
  signature := fourierSignature
  Law R := ∀ {s : ℝ}, 0 < s → ∀ b : ℝ,
    |R.readout () s b| ≤
      (4 * Real.exp (-1) / s) * (thetaFourier (s / 2) 0 - 1) * |Real.sin (2 * Real.pi * b)|

def controlRejected : Realization fourierSignature :=
  realize fourierSignature
    (fun _ s b => (4 * Real.exp (-1) / s) * (thetaFourier (s / 2) 0 - 1) *
      |Real.sin (2 * Real.pi * b)| + 1) (fun e => nomatch e)

private theorem control_bridge : (type_of% (@thetaFourier_derivative_control)) ↔
    controlArena.Law derivativeActual := Iff.rfl

private theorem control_rejected : ¬ controlArena.Law controlRejected := by
  intro h
  have h0 := h (s := 1) (by norm_num) 0
  norm_num [controlRejected, realize] at h0

def controlRegistration : Registration controlArena
    (type_of% (@thetaFourier_derivative_control)) where
  actual := derivativeActual
  bridge := control_bridge
  variation := ⟨@thetaFourier_derivative_control, controlRejected, control_rejected⟩
  sensitivity := ⟨fun i => ⟨controlRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, control_rejected⟩, fun e => nomatch e⟩
  dependence := derivative_dependence

abbrev momentSignature : Signature where
  Params := Σ _ : ℝ, ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def momentActual : Realization momentSignature :=
  realize momentSignature (fun _ p k => ((k : ℝ) + 1) ^ p.2 *
    Real.exp (-Real.pi * p.1 * ((k : ℝ) + 1) ^ 2)) (fun e => nomatch e)

def momentRejected : Realization momentSignature :=
  realize momentSignature (fun _ _ _ => 1) (fun e => nomatch e)

def momentArena : Arena where
  signature := momentSignature
  Law R := ∀ {s : ℝ}, 0 < s → ∀ j : ℕ,
    Summable (fun k : ℕ => R.readout () ⟨s, j⟩ k)

private theorem moment_bridge : (type_of% (@gaussian_moment)) ↔
    momentArena.Law momentActual := Iff.rfl

private theorem moment_dependence :
    ObservationalDependence momentSignature momentActual := by
  intro i
  refine ⟨⟨1, 0⟩, 0, 1, ?_⟩
  norm_num only [momentActual, realize, momentSignature, pow_zero, one_mul,
    Nat.cast_zero, Nat.cast_one, zero_add, mul_one, one_pow]
  apply ne_of_gt
  apply Real.exp_lt_exp.mpr
  nlinarith [Real.pi_pos]

private theorem moment_rejected : ¬ momentArena.Law momentRejected := by
  intro h
  have hh := h (s := 1) (by norm_num) 0
  simp [momentRejected, realize, summable_const_iff] at hh

def momentRegistration : Registration momentArena (type_of% (@gaussian_moment)) where
  actual := momentActual
  bridge := moment_bridge
  variation := ⟨@gaussian_moment, momentRejected, moment_rejected⟩
  sensitivity := ⟨fun i => ⟨momentRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, moment_rejected⟩, fun e => nomatch e⟩
  dependence := moment_dependence

abbrev cosineSignature : Signature where
  Params := Σ _ : ℝ, ℝ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def cosineActual : Realization cosineSignature :=
  realize cosineSignature (fun _ p k =>
    Real.exp (-Real.pi * p.1 * ((k : ℝ) + 1) ^ 2) *
      Real.cos (2 * Real.pi * ((k : ℝ) + 1) * p.2)) (fun e => nomatch e)

def cosineRejected : Realization cosineSignature :=
  realize cosineSignature (fun _ _ _ => 1) (fun e => nomatch e)

def cosineArena : Arena where
  signature := cosineSignature
  Law R := ∀ {s : ℝ}, 0 < s → ∀ b : ℝ,
    Summable (fun k : ℕ => R.readout () ⟨s, b⟩ k)

private theorem cosine_bridge : (type_of% (@cos_summable)) ↔
    cosineArena.Law cosineActual := Iff.rfl

private theorem cosine_dependence :
    ObservationalDependence cosineSignature cosineActual := by
  intro i
  refine ⟨⟨1, 0⟩, 0, 1, ?_⟩
  simp only [cosineActual, realize, mul_zero, Real.cos_zero, mul_one]
  apply ne_of_gt
  apply Real.exp_lt_exp.mpr
  norm_num only [Nat.cast_zero, Nat.cast_one, zero_add, one_add_one_eq_two, one_pow]
  nlinarith [Real.pi_pos]

private theorem cosine_rejected : ¬ cosineArena.Law cosineRejected := by
  intro h
  have hh := h (s := 1) (by norm_num) 0
  simp [cosineRejected, realize, summable_const_iff] at hh

def cosineRegistration : Registration cosineArena (type_of% (@cos_summable)) where
  actual := cosineActual
  bridge := cosine_bridge
  variation := ⟨@cos_summable, cosineRejected, cosine_rejected⟩
  sensitivity := ⟨fun i => ⟨cosineRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, cosine_rejected⟩, fun e => nomatch e⟩
  dependence := cosine_dependence

end
end Reg.Support.ThetaFourierBounds

open D5.S3.Fourier.PlanarTheta
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

namespace Reg.Support.ThetaPoisson
noncomputable section

abbrev valueSignature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def valueActual : Realization valueSignature :=
  realize valueSignature (fun _ b s => thetaFourier s b) (fun e => nomatch e)

def valueRejected : Realization valueSignature :=
  realize valueSignature (fun _ b s => thetaFourier s b + 1) (fun e => nomatch e)

abbrev zeroSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def zeroActual : Realization zeroSignature :=
  realize zeroSignature (fun _ _ s => thetaFourier s 0) (fun e => nomatch e)

def zeroRejected : Realization zeroSignature :=
  realize zeroSignature (fun _ _ s => thetaFourier s 0 + 1) (fun e => nomatch e)

def valueArena : Arena where
  signature := valueSignature
  Law R := ∀ {s : ℝ}, 0 < s → ∀ b : ℝ,
    R.readout () b s = (Real.sqrt s)⁻¹ *
      ∑' n : ℤ, Real.exp (-Real.pi / s * ((n : ℝ) - b) ^ 2)

def zeroArena : Arena where
  signature := zeroSignature
  Law R := ∀ {s : ℝ}, 0 < s →
    R.readout () () s = (Real.sqrt s)⁻¹ * thetaFourier s⁻¹ 0

private theorem value_bridge : (type_of% (@thetaFourier_poisson)) ↔
    valueArena.Law valueActual := Iff.rfl

private theorem zero_bridge : (type_of% (@thetaFourier_zero_duality)) ↔
    zeroArena.Law zeroActual := Iff.rfl

private theorem zero_strict : thetaFourier 2 0 < thetaFourier 1 0 := by
  have hs (s : ℝ) (hs : 0 < s) :
      Summable (fun k : ℕ => Real.exp (-Real.pi * s * ((k : ℝ) + 1) ^ 2)) := by
    simpa only [pow_zero, one_mul] using gaussian_moment hs 0
  have hlt : (∑' k : ℕ, Real.exp (-Real.pi * 2 * ((k : ℝ) + 1) ^ 2)) <
      ∑' k : ℕ, Real.exp (-Real.pi * 1 * ((k : ℝ) + 1) ^ 2) := by
    apply Summable.tsum_lt_tsum (i := 0)
    · intro k
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg Real.pi_pos.le (sq_nonneg ((k : ℝ) + 1))]
    · apply Real.exp_lt_exp.mpr
      norm_num only [Nat.cast_zero, zero_add, one_pow, mul_one]
      linarith [Real.pi_pos]
    · exact hs 2 (by norm_num)
    · exact hs 1 (by norm_num)
  simp only [mul_one] at hlt
  simp only [thetaFourier, mul_zero, Real.cos_zero, mul_one]
  linarith

private theorem value_dependence : ObservationalDependence valueSignature valueActual := by
  intro i
  exact ⟨0, 2, 1, ne_of_lt zero_strict⟩

private theorem zero_dependence : ObservationalDependence zeroSignature zeroActual := by
  intro i
  exact ⟨(), 2, 1, ne_of_lt zero_strict⟩

private theorem value_rejected : ¬ valueArena.Law valueRejected := by
  intro h
  have h1 := h (s := 1) (by norm_num) 0
  have h0 := thetaFourier_poisson (by norm_num : (0 : ℝ) < 1) 0
  change thetaFourier 1 0 + 1 = _ at h1
  linarith

private theorem zero_rejected : ¬ zeroArena.Law zeroRejected := by
  intro h
  have h1 := h (s := 1) (by norm_num)
  have h0 := thetaFourier_zero_duality (by norm_num : (0 : ℝ) < 1)
  change thetaFourier 1 0 + 1 = _ at h1
  linarith

def valueRegistration : Registration valueArena (type_of% (@thetaFourier_poisson)) where
  actual := valueActual
  bridge := value_bridge
  variation := ⟨@thetaFourier_poisson, valueRejected, value_rejected⟩
  sensitivity := ⟨fun i => ⟨valueRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, value_rejected⟩, fun e => nomatch e⟩
  dependence := value_dependence

def zeroRegistration : Registration zeroArena (type_of% (@thetaFourier_zero_duality)) where
  actual := zeroActual
  bridge := zero_bridge
  variation := ⟨@thetaFourier_zero_duality, zeroRejected, zero_rejected⟩
  sensitivity := ⟨fun i => ⟨zeroRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, zero_rejected⟩, fun e => nomatch e⟩
  dependence := zero_dependence

abbrev translateSignature : Signature where
  Params := Σ _ : ℝ, ℝ
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def translateTerm (p : Σ _ : ℝ, ℝ) (n : ℤ) : ℝ :=
  (-2 * p.1 * (p.2 - n)) * Real.exp (-p.1 * (p.2 - n) ^ 2)

def translateActual : Realization translateSignature :=
  realize translateSignature (fun _ p n => translateTerm p n) (fun e => nomatch e)

def translateRejected : Realization translateSignature :=
  realize translateSignature
    (fun _ p n => if n = 0 then (∑' k, translateTerm p k) + 1 else 0)
    (fun e => nomatch e)

def translateArena : Arena where
  signature := translateSignature
  Law R := ∀ {a : ℝ}, 0 < a → ∀ b : ℝ,
    HasDerivAt (fun z => ∑' n : ℤ, Real.exp (-a * (z - n) ^ 2))
      (∑' n : ℤ, R.readout () ⟨a, b⟩ n) b

private theorem translate_bridge : (type_of% (@hasDerivAt_gaussianTranslate)) ↔
    translateArena.Law translateActual := Iff.rfl

private theorem translate_dependence :
    ObservationalDependence translateSignature translateActual := by
  intro i
  refine ⟨⟨1, 0⟩, 0, 1, ?_⟩
  simp [translateActual, realize, translateTerm]

private theorem translate_rejected : ¬ translateArena.Law translateRejected := by
  intro h
  have h1 := h (a := 1) (by norm_num) 0
  have h0 := hasDerivAt_gaussianTranslate (by norm_num : (0 : ℝ) < 1) 0
  have hh := h1.unique h0
  simp only [translateRejected, realize, tsum_ite_eq] at hh
  change (∑' n, translateTerm ⟨1, 0⟩ n) + 1 =
    ∑' n, translateTerm ⟨1, 0⟩ n at hh
  linarith

def translateRegistration : Registration translateArena
    (type_of% (@hasDerivAt_gaussianTranslate)) where
  actual := translateActual
  bridge := translate_bridge
  variation := ⟨@hasDerivAt_gaussianTranslate, translateRejected, translate_rejected⟩
  sensitivity := ⟨fun i => ⟨translateRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, translate_rejected⟩, fun e => nomatch e⟩
  dependence := translate_dependence

open Reg.Support.ThetaFourierBounds

def forceRejected : Realization fourierSignature :=
  realize fourierSignature (fun _ s b => deriv (thetaFourier s) b + 1)
    (fun e => nomatch e)

def forceArena : Arena where
  signature := fourierSignature
  Law R := ∀ {s : ℝ}, 0 < s → ∀ b : ℝ,
    R.readout () s b = -(2 * Real.pi / (s * Real.sqrt s)) *
      ∑' n : ℤ, (b - n) * Real.exp (-Real.pi / s * (b - n) ^ 2)

private theorem force_bridge : (type_of% (@thetaFourier_derivative_gaussian)) ↔
    forceArena.Law derivativeActual := Iff.rfl

private theorem force_rejected : ¬ forceArena.Law forceRejected := by
  intro h
  have h1 := h (s := 1) (by norm_num) 0
  have h0 := thetaFourier_derivative_gaussian (by norm_num : (0 : ℝ) < 1) 0
  change deriv (thetaFourier 1) 0 + 1 = _ at h1
  linarith

def forceRegistration : Registration forceArena
    (type_of% (@thetaFourier_derivative_gaussian)) where
  actual := derivativeActual
  bridge := force_bridge
  variation := ⟨@thetaFourier_derivative_gaussian, forceRejected, force_rejected⟩
  sensitivity := ⟨fun i => ⟨forceRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, force_rejected⟩, fun e => nomatch e⟩
  dependence := derivative_dependence

def integerFourierArena : Arena where
  signature := valueSignature
  Law R := ∀ {s : ℝ}, 0 < s → ∀ b : ℝ,
    (∑' n : ℤ, Real.exp (-Real.pi * s * (n : ℝ) ^ 2) *
      Real.cos (2 * Real.pi * (n : ℝ) * b)) = R.readout () b s

private theorem integerFourier_bridge : (type_of% (@real_fourier_int)) ↔
    integerFourierArena.Law valueActual := Iff.rfl

private theorem integerFourier_rejected : ¬ integerFourierArena.Law valueRejected := by
  intro h
  have hh := h (s := 1) (by norm_num) 0
  have he := real_fourier_int (by norm_num : (0 : ℝ) < 1) 0
  change _ = thetaFourier 1 0 + 1 at hh
  linarith

def integerFourierRegistration : Registration integerFourierArena
    (type_of% (@real_fourier_int)) where
  actual := valueActual
  bridge := integerFourier_bridge
  variation := ⟨@real_fourier_int, valueRejected, integerFourier_rejected⟩
  sensitivity := ⟨fun i => ⟨valueRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, integerFourier_rejected⟩, fun e => nomatch e⟩
  dependence := value_dependence

end
end Reg.Support.ThetaPoisson

open D5.S3.Fourier.PlanarTheta
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.Support.ThetaDerivativeBounds
noncomputable section

abbrev derivativeSignature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def derivativeActual : Realization derivativeSignature :=
  realize derivativeSignature (fun _ s b => deriv (thetaFourier s) b) (fun e => nomatch e)

def derivativeRejected : Realization derivativeSignature :=
  realize derivativeSignature (fun _ _ _ => 0) (fun e => nomatch e)

def smallArena : Arena where
  signature := derivativeSignature
  Law R := ∀ {s : ℝ}, 0 < s → s ≤ Real.pi / 6 → ∀ b : ℝ,
    |R.readout () s b| ≤ 6 / (s * Real.sqrt s) * |Real.sin (2 * Real.pi * b)| ∧
    (0 ≤ b → b ≤ 1 / 2 →
      (3 / (10 * s * Real.sqrt s)) * Real.exp (-Real.pi / (4 * s)) *
        Real.sin (2 * Real.pi * b) ≤ -R.readout () s b)

private theorem small_bridge : (type_of% (@thetaFourier_small_derivative_bounds)) ↔
    smallArena.Law derivativeActual := Iff.rfl

private theorem derivative_zero : deriv (thetaFourier (1 / 2)) 0 = 0 := by
  rw [(hasDerivAt_thetaFourier (by norm_num : (0 : ℝ) < 1 / 2) 0).deriv]
  simp [thetaSine]

private theorem derivative_quarter_neg : deriv (thetaFourier (1 / 2)) (1 / 4) < 0 := by
  have h := (thetaFourier_small_derivative_bounds (s := 1 / 2)
    (by norm_num) (by linarith [Real.pi_gt_three]) (1 / 4)).2 (by norm_num) (by norm_num)
  have he : Real.sin (2 * Real.pi * (1 / 4)) = 1 := by
    rw [show 2 * Real.pi * (1 / 4) = Real.pi / 2 by ring, Real.sin_pi_div_two]
  rw [he, mul_one] at h
  have hp : 0 < (3 / (10 * (1 / 2) * Real.sqrt (1 / 2))) *
      Real.exp (-Real.pi / (4 * (1 / 2))) := by positivity
  linarith

private theorem derivative_dependence :
    ObservationalDependence derivativeSignature derivativeActual := by
  intro i
  refine ⟨1 / 2, 0, 1 / 4, ?_⟩
  change deriv (thetaFourier (1 / 2)) 0 ≠ deriv (thetaFourier (1 / 2)) (1 / 4)
  rw [derivative_zero]
  exact ne_of_gt derivative_quarter_neg

private theorem small_rejected : ¬ smallArena.Law derivativeRejected := by
  intro h
  have hh := (h (s := 1 / 2) (by norm_num) (by linarith [Real.pi_gt_three]) (1 / 4)).2
    (by norm_num) (by norm_num)
  have he : Real.sin (2 * Real.pi * (1 / 4)) = 1 := by
    rw [show 2 * Real.pi * (1 / 4) = Real.pi / 2 by ring, Real.sin_pi_div_two]
  simp only [derivativeRejected, realize, neg_zero, he, mul_one] at hh
  have hp : 0 < (3 / (10 * (1 / 2) * Real.sqrt (1 / 2))) *
      Real.exp (-Real.pi / (4 * (1 / 2))) := by positivity
  linarith

def smallRegistration : Registration smallArena
    (type_of% (@thetaFourier_small_derivative_bounds)) where
  actual := derivativeActual
  bridge := small_bridge
  variation := ⟨@thetaFourier_small_derivative_bounds, derivativeRejected, small_rejected⟩
  sensitivity := ⟨fun i => ⟨derivativeRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, small_rejected⟩, fun e => nomatch e⟩
  dependence := derivative_dependence

end
end Reg.Support.ThetaDerivativeBounds
