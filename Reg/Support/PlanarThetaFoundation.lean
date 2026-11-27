import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Fourier.PlanarThetaFoundation
import Mathlib.Analysis.Real.Pi.Bounds

/-! Gaussian observation families and their whole-family interventions. -/

open D5.S3.Fourier.PlanarTheta
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

namespace Reg.Support.PlanarThetaFoundation
noncomputable section

abbrev formSignature : Signature where
  Params := Σ _ : ℝ, ℝ
  State _ := ℤ × ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def formActual : Realization formSignature :=
  realize formSignature (fun _ p v => Q p.1 p.2 v) (fun e => nomatch e)

abbrev gaussianSignature : Signature where
  Params := Σ _ : ℝ, Σ _ : ℝ, ℝ
  State _ := ℤ × ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def gaussianActual : Realization gaussianSignature :=
  realize gaussianSignature
    (fun _ p v => Real.exp (-Real.pi * p.1 * Q p.2.1 p.2.2 v)) (fun e => nomatch e)

abbrev thetaSignature : Signature where
  Params := Σ _ : ℝ, ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def thetaActual : Realization thetaSignature :=
  realize thetaSignature (fun _ p v => F v p.1 p.2) (fun e => nomatch e)

abbrev basisSignature : Signature where
  Params := Σ _ : ℂ, ℂ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def basisActual : Realization basisSignature :=
  realize basisSignature (fun _ p v => basisTheta v p.1 p.2) (fun e => nomatch e)

private theorem form_dependence : ObservationalDependence formSignature formActual := by
  intro i
  refine ⟨⟨0, 1⟩, (0, 0), (1, 0), ?_⟩
  norm_num [formActual, realize, Q]

private theorem gaussian_dependence :
    ObservationalDependence gaussianSignature gaussianActual := by
  intro i
  refine ⟨⟨1, 0, 1⟩, (0, 0), (1, 0), ?_⟩
  simp only [gaussianActual, realize, Q]
  norm_num only [Int.cast_zero, Int.cast_one, zero_mul, zero_add, add_zero,
    zero_pow, one_pow, zero_div, div_one, mul_zero, mul_one, neg_mul, Real.exp_zero]
  exact ne_of_gt (by simpa using Real.exp_lt_exp.mpr (neg_lt_zero.mpr Real.pi_pos))

private theorem theta_strict : F 2 0 1 < F 1 0 1 := by
  unfold F
  apply Summable.tsum_lt_tsum (i := (1, 0))
    (f := fun v : ℤ × ℤ => Real.exp (-Real.pi * 2 * Q 0 1 v))
    (g := fun v : ℤ × ℤ => Real.exp (-Real.pi * 1 * Q 0 1 v))
  · intro v
    apply Real.exp_le_exp.mpr
    have hq : 0 ≤ Q 0 1 v := by unfold Q; positivity
    nlinarith [mul_nonneg Real.pi_pos.le hq]
  · apply Real.exp_lt_exp.mpr
    norm_num [Q]
    linarith [Real.pi_pos]
  · exact summable 2 0 (by norm_num) (by norm_num)
  · exact summable 1 0 (by norm_num) (by norm_num)

theorem theta_dependence : ObservationalDependence thetaSignature thetaActual := by
  intro i
  exact ⟨⟨0, 1⟩, 2, 1, ne_of_lt theta_strict⟩

theorem basis_dependence : ObservationalDependence basisSignature basisActual := by
  have h (t : ℝ) : basisTheta t 1 Complex.I = F t 0 1 := by
    unfold basisTheta F
    apply tsum_congr
    intro v
    congr 2
    simp [Q, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, pow_two]
  intro i
  refine ⟨⟨1, Complex.I⟩, 2, 1, ?_⟩
  simpa only [basisActual, realize, h] using ne_of_lt theta_strict

def shearDerivativeTerm (p : Σ _ : ℝ, Σ _ : ℝ, ℝ) (v : ℤ × ℤ) : ℝ :=
  (-Real.pi * p.1 *
    (2 * (v.2 : ℝ) * ((v.1 : ℝ) + v.2 * p.2.1) / p.2.2)) *
      Real.exp (-Real.pi * p.1 * Q p.2.1 p.2.2 v)

def shearDerivativeActual : Realization gaussianSignature :=
  realize gaussianSignature (fun _ p v => shearDerivativeTerm p v) (fun e => nomatch e)

def shearDerivativeRejected : Realization gaussianSignature :=
  realize gaussianSignature
    (fun _ p v => if v = (0, 0) then (∑' w, shearDerivativeTerm p w) + 1 else 0)
    (fun e => nomatch e)

def heightDerivativeTerm (p : Σ _ : ℝ, Σ _ : ℝ, ℝ) (v : ℤ × ℤ) : ℝ :=
  (-Real.pi * p.1 *
    ((v.2 : ℝ) ^ 2 - ((v.1 : ℝ) + v.2 * p.2.1) ^ 2 / p.2.2 ^ 2)) *
      Real.exp (-Real.pi * p.1 * Q p.2.1 p.2.2 v)

def heightDerivativeActual : Realization gaussianSignature :=
  realize gaussianSignature (fun _ p v => heightDerivativeTerm p v) (fun e => nomatch e)

def heightDerivativeRejected : Realization gaussianSignature :=
  realize gaussianSignature
    (fun _ p v => if v = (0, 0) then (∑' w, heightDerivativeTerm p w) + 1 else 0)
    (fun e => nomatch e)

def heightSecondTerm (p : Σ _ : ℝ, Σ _ : ℝ, ℝ) (v : ℤ × ℤ) : ℝ :=
  ((Real.pi * p.1) ^ 2 *
    ((v.2 : ℝ) ^ 2 - ((v.1 : ℝ) + v.2 * p.2.1) ^ 2 / p.2.2 ^ 2) ^ 2 -
    Real.pi * p.1 * (2 * ((v.1 : ℝ) + v.2 * p.2.1) ^ 2 / p.2.2 ^ 3)) *
      Real.exp (-Real.pi * p.1 * Q p.2.1 p.2.2 v)

def heightSecondActual : Realization gaussianSignature :=
  realize gaussianSignature (fun _ p v => heightSecondTerm p v) (fun e => nomatch e)

def heightSecondRejected : Realization gaussianSignature :=
  realize gaussianSignature
    (fun _ p v => if v = (0, 0) then (∑' w, heightSecondTerm p w) + 1 else 0)
    (fun e => nomatch e)

def controlArena : Arena where
  signature := formSignature
  Law R := ∀ {M l u x y : ℝ}, 0 < l → |x| ≤ M → l ≤ y → y ≤ u →
    ∀ v : ℤ × ℤ, (v.1 : ℝ) ^ 2 + (v.2 : ℝ) ^ 2 ≤
      max (2 * u) ((2 * M ^ 2 + 1) / l) * R.readout () ⟨x, y⟩ v

private theorem control_bridge : (type_of% (@quadratic_control)) ↔
    controlArena.Law formActual := Iff.rfl

def summableArena : Arena where
  signature := gaussianSignature
  Law R := ∀ (t x : ℝ) {y : ℝ}, 0 < t → 0 < y →
    Summable (fun v : ℤ × ℤ => R.readout () ⟨t, x, y⟩ v)

private theorem summable_bridge : (type_of% (@summable)) ↔
    summableArena.Law gaussianActual := Iff.rfl

def dualityArena : Arena where
  signature := thetaSignature
  Law R := ∀ (t x : ℝ) {y : ℝ}, 0 < t → 0 < y →
    R.readout () ⟨x, y⟩ t = t⁻¹ * F t⁻¹ x y

private theorem duality_bridge : (type_of% (@temperature_duality)) ↔
    dualityArena.Law thetaActual := Iff.rfl

def shearDerivativeArena : Arena where
  signature := gaussianSignature
  Law R := ∀ (t x : ℝ) {y : ℝ}, 0 < t → 0 < y →
    HasDerivAt (fun a => F t a y) (∑' v, R.readout () ⟨t, x, y⟩ v) x

private theorem shearDerivative_bridge : (type_of% (@hasDerivAt_shear)) ↔
    shearDerivativeArena.Law shearDerivativeActual := Iff.rfl

def heightDerivativeArena : Arena where
  signature := gaussianSignature
  Law R := ∀ (t x : ℝ) {y : ℝ}, 0 < t → 0 < y →
    HasDerivAt (fun b => F t x b) (∑' v, R.readout () ⟨t, x, y⟩ v) y

private theorem heightDerivative_bridge : (type_of% (@hasDerivAt_height)) ↔
    heightDerivativeArena.Law heightDerivativeActual := Iff.rfl

def heightSecondArena : Arena where
  signature := gaussianSignature
  Law R := ∀ (t x : ℝ) {y : ℝ}, 0 < t → 0 < y →
    HasDerivAt (fun b => deriv (fun z => F t x z) b)
      (∑' v, R.readout () ⟨t, x, y⟩ v) y

private theorem heightSecond_bridge : (type_of% (@hasDerivAt_height_deriv)) ↔
    heightSecondArena.Law heightSecondActual := Iff.rfl

def geometryArena : Arena where
  signature := formSignature
  Law R := ∀ (x : ℝ) {y : ℝ}, 0 < y →
    Function.Injective (latticePoint x y) ∧
      ∀ v : ℤ × ℤ, Complex.normSq (latticePoint x y v) = R.readout () ⟨x, y⟩ v

private theorem geometry_bridge : (type_of% (@lattice_geometry)) ↔
    geometryArena.Law formActual := Iff.rfl

def formRejected : Realization formSignature :=
  realize formSignature (fun _ _ _ => 0) (fun e => nomatch e)

def gaussianRejected : Realization gaussianSignature :=
  realize gaussianSignature (fun _ _ _ => 1) (fun e => nomatch e)

def thetaRejected : Realization thetaSignature :=
  realize thetaSignature (fun _ p t => F t p.1 p.2 + 1) (fun e => nomatch e)

private theorem control_rejected : ¬ controlArena.Law formRejected := by
  intro h
  have hh := h (M := 0) (l := 1) (u := 1) (x := 0) (y := 1)
    (by norm_num) (by norm_num) le_rfl le_rfl (1, 0)
  norm_num [formRejected, realize] at hh

private theorem summable_rejected : ¬ summableArena.Law gaussianRejected := by
  intro h
  have hh := h 1 0 (y := 1) (by norm_num) (by norm_num)
  simp [gaussianRejected, realize, summable_const_iff] at hh

private theorem duality_rejected : ¬ dualityArena.Law thetaRejected := by
  intro h
  have hh := h 1 0 (y := 1) (by norm_num) (by norm_num)
  simp only [thetaRejected, realize, inv_one, one_mul] at hh
  linarith

private theorem geometry_rejected : ¬ geometryArena.Law formRejected := by
  intro h
  have hh := (h 0 (y := 1) (by norm_num)).2 (1, 0)
  norm_num [formRejected, realize, latticePoint, Complex.normSq_mk] at hh

private theorem shearDerivative_rejected :
    ¬ shearDerivativeArena.Law shearDerivativeRejected := by
  intro h
  have hh := h 1 0 (y := 1) (by norm_num) (by norm_num)
  have he := hasDerivAt_shear 1 0 (y := 1) (by norm_num) (by norm_num)
  have hu := hh.unique he
  simp only [shearDerivativeRejected, realize] at hu
  simp only [tsum_ite_eq] at hu
  change (∑' v, shearDerivativeTerm ⟨1, 0, 1⟩ v) + 1 =
    ∑' v, shearDerivativeTerm ⟨1, 0, 1⟩ v at hu
  linarith

private theorem heightDerivative_rejected :
    ¬ heightDerivativeArena.Law heightDerivativeRejected := by
  intro h
  have hh := h 1 0 (y := 1) (by norm_num) (by norm_num)
  have he := hasDerivAt_height 1 0 (y := 1) (by norm_num) (by norm_num)
  have hu := hh.unique he
  simp only [heightDerivativeRejected, realize] at hu
  simp only [tsum_ite_eq] at hu
  change (∑' v, heightDerivativeTerm ⟨1, 0, 1⟩ v) + 1 =
    ∑' v, heightDerivativeTerm ⟨1, 0, 1⟩ v at hu
  linarith

private theorem heightSecond_rejected :
    ¬ heightSecondArena.Law heightSecondRejected := by
  intro h
  have hh := h 1 0 (y := 1) (by norm_num) (by norm_num)
  have he := hasDerivAt_height_deriv 1 0 (y := 1) (by norm_num) (by norm_num)
  have hu := hh.unique he
  simp only [heightSecondRejected, realize] at hu
  simp only [tsum_ite_eq] at hu
  change (∑' v, heightSecondTerm ⟨1, 0, 1⟩ v) + 1 =
    ∑' v, heightSecondTerm ⟨1, 0, 1⟩ v at hu
  linarith

private theorem shearDerivative_dependence :
    ObservationalDependence gaussianSignature shearDerivativeActual := by
  intro i
  refine ⟨⟨1, 1, 1⟩, (0, 0),
    (0, 1), ?_⟩
  simp [shearDerivativeActual, realize, shearDerivativeTerm, Q]

private theorem heightDerivative_dependence :
    ObservationalDependence gaussianSignature heightDerivativeActual := by
  intro i
  refine ⟨⟨1, 0, 1⟩, (0, 0),
    (1, 0), ?_⟩
  simp [heightDerivativeActual, realize, heightDerivativeTerm, Q]

private theorem heightSecond_dependence :
    ObservationalDependence gaussianSignature heightSecondActual := by
  intro i
  refine ⟨⟨1, 0, 1⟩, (0, 0),
    (1, 0), ?_⟩
  simp [heightSecondActual, realize, heightSecondTerm, Q]
  have hp := Real.pi_gt_three
  nlinarith [Real.exp_pos (-Real.pi), sq_nonneg (Real.pi - 3)]

def controlRegistration : Registration controlArena (type_of% (@quadratic_control)) where
  actual := formActual
  bridge := control_bridge
  variation := ⟨@quadratic_control, formRejected, control_rejected⟩
  sensitivity := ⟨fun i => ⟨formRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim, rfl, control_rejected⟩,
    fun e => nomatch e⟩
  dependence := form_dependence

def summableRegistration : Registration summableArena (type_of% (@summable)) where
  actual := gaussianActual
  bridge := summable_bridge
  variation := ⟨@summable, gaussianRejected, summable_rejected⟩
  sensitivity := ⟨fun i => ⟨gaussianRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim, rfl, summable_rejected⟩,
    fun e => nomatch e⟩
  dependence := gaussian_dependence

def dualityRegistration : Registration dualityArena (type_of% (@temperature_duality)) where
  actual := thetaActual
  bridge := duality_bridge
  variation := ⟨@temperature_duality, thetaRejected, duality_rejected⟩
  sensitivity := ⟨fun i => ⟨thetaRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim, rfl, duality_rejected⟩,
    fun e => nomatch e⟩
  dependence := theta_dependence

def shearDerivativeRegistration :
    Registration shearDerivativeArena (type_of% (@hasDerivAt_shear)) where
  actual := shearDerivativeActual
  bridge := shearDerivative_bridge
  variation := ⟨@hasDerivAt_shear, shearDerivativeRejected, shearDerivative_rejected⟩
  sensitivity := ⟨fun i => ⟨shearDerivativeRejected,
    fun j h =>
      (h (show j = i from @Subsingleton.elim Unit _ j i)).elim, rfl, shearDerivative_rejected⟩,
    fun e => nomatch e⟩
  dependence := shearDerivative_dependence

def heightDerivativeRegistration :
    Registration heightDerivativeArena (type_of% (@hasDerivAt_height)) where
  actual := heightDerivativeActual
  bridge := heightDerivative_bridge
  variation := ⟨@hasDerivAt_height, heightDerivativeRejected, heightDerivative_rejected⟩
  sensitivity := ⟨fun i => ⟨heightDerivativeRejected,
    fun j h =>
      (h (show j = i from @Subsingleton.elim Unit _ j i)).elim, rfl, heightDerivative_rejected⟩,
    fun e => nomatch e⟩
  dependence := heightDerivative_dependence

def heightSecondRegistration :
    Registration heightSecondArena (type_of% (@hasDerivAt_height_deriv)) where
  actual := heightSecondActual
  bridge := heightSecond_bridge
  variation := ⟨@hasDerivAt_height_deriv, heightSecondRejected, heightSecond_rejected⟩
  sensitivity := ⟨fun i => ⟨heightSecondRejected,
    fun j h =>
      (h (show j = i from @Subsingleton.elim Unit _ j i)).elim, rfl, heightSecond_rejected⟩,
    fun e => nomatch e⟩
  dependence := heightSecond_dependence

def geometryRegistration : Registration geometryArena (type_of% (@lattice_geometry)) where
  actual := formActual
  bridge := geometry_bridge
  variation := ⟨@lattice_geometry, formRejected, geometry_rejected⟩
  sensitivity := ⟨fun i => ⟨formRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim, rfl, geometry_rejected⟩,
    fun e => nomatch e⟩
  dependence := form_dependence

abbrev basisFormSignature : Signature where
  Params := Σ _ : ℂ, ℂ
  State _ := ℤ × ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def basisFormActual : Realization basisFormSignature :=
  realize basisFormSignature (fun _ p v =>
    Complex.normSq ((v.1 : ℂ) * p.1 + (v.2 : ℂ) * p.2)) (fun e => nomatch e)

def basisFormRejected : Realization basisFormSignature :=
  realize basisFormSignature (fun _ _ _ => 0) (fun e => nomatch e)

def basisGeometryArena : Arena where
  signature := basisFormSignature
  Law R := ∀ a b : ℂ, |a.re * b.im - a.im * b.re| = 1 →
    ∃ x y : ℝ, 0 ≤ x ∧ x ≤ 1 / 2 ∧ 0 < y ∧ 1 ≤ x ^ 2 + y ^ 2 ∧
      Real.sqrt 3 / 2 ≤ y ∧ ∃ e : (ℤ × ℤ) ≃+ (ℤ × ℤ), ∀ v,
        R.readout () ⟨a, b⟩ v = Q x y (e v)

private theorem basisGeometry_bridge : (type_of% (@basis_reduction_geometry)) ↔
    basisGeometryArena.Law basisFormActual := Iff.rfl

private theorem basisForm_dependence :
    ObservationalDependence basisFormSignature basisFormActual := by
  intro i
  refine ⟨⟨1, Complex.I⟩, (0, 0), (1, 0), ?_⟩
  norm_num [basisFormActual, realize]

private theorem basisGeometry_rejected : ¬ basisGeometryArena.Law basisFormRejected := by
  intro h
  obtain ⟨x, y, hx, hx', hy, hnorm, hc, e, he⟩ := h 1 Complex.I (by norm_num)
  have hh := he (e.symm ((1, 0) : ℤ × ℤ))
  change (0 : ℝ) = Q x y (e (e.symm (1, 0))) at hh
  rw [e.apply_symm_apply] at hh
  norm_num [Q] at hh
  have hp : 0 < (1 : ℝ) / y := by positivity
  linarith

def basisGeometryRegistration :
    Registration basisGeometryArena (type_of% (@basis_reduction_geometry)) where
  actual := basisFormActual
  bridge := basisGeometry_bridge
  variation := ⟨@basis_reduction_geometry, basisFormRejected, basisGeometry_rejected⟩
  sensitivity := ⟨fun i => ⟨basisFormRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, basisGeometry_rejected⟩, fun e => nomatch e⟩
  dependence := basisForm_dependence

end
end Reg.Support.PlanarThetaFoundation

open D5.S3.Fourier.PlanarTheta
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.Support.ThetaLatticeIsometry
noncomputable section

abbrev pointSignature : Signature where
  Params := Σ _ : ℝ, ℝ
  State _ := ℤ × ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def pointActual : Realization pointSignature :=
  realize pointSignature (fun _ p v => latticePoint p.1 p.2 v) (fun e => nomatch e)

def pointRejected : Realization pointSignature :=
  realize pointSignature (fun _ _ _ => (1 : ℂ)) (fun e => nomatch e)

def isometryArena : Arena where
  signature := pointSignature
  Law R := ∀ {a b : ℂ} {x y : ℝ},
    ∀ e : (ℤ × ℤ) ≃+ (ℤ × ℤ),
    (∀ v : ℤ × ℤ,
      Complex.normSq ((v.1 : ℂ) * a + (v.2 : ℂ) * b) = Q x y (e v)) →
    ∃ U : ℂ ≃ₗᵢ[ℝ] ℂ, ∀ v : ℤ × ℤ,
      U ((v.1 : ℂ) * a + (v.2 : ℂ) * b) = R.readout () ⟨x, y⟩ (e v)

private theorem isometry_bridge : (type_of% (@basis_isometry_of_quadratic_reindex)) ↔
    isometryArena.Law pointActual := Iff.rfl

private theorem point_dependence : ObservationalDependence pointSignature pointActual := by
  intro i
  refine ⟨⟨0, 1⟩, (0, 0), (1, 0), ?_⟩
  norm_num [pointActual, realize, latticePoint]
  intro he
  have h := congrArg Complex.re he
  norm_num at h

private theorem isometry_rejected : ¬ isometryArena.Law pointRejected := by
  intro h
  have hQ (v : ℤ × ℤ) :
      Complex.normSq ((v.1 : ℂ) * (1 : ℂ) + (v.2 : ℂ) * Complex.I) =
        Q 0 1 ((AddEquiv.refl (ℤ × ℤ)) v) := by
    simp [Q, Complex.normSq_apply] <;> ring
  obtain ⟨U, hU⟩ := h (a := 1) (b := Complex.I) (x := 0) (y := 1)
    (AddEquiv.refl _) hQ
  have hh := hU (0, 0)
  norm_num [pointRejected, realize] at hh

def isometryRegistration : Registration isometryArena
    (type_of% (@basis_isometry_of_quadratic_reindex)) where
  actual := pointActual
  bridge := isometry_bridge
  variation := ⟨@basis_isometry_of_quadratic_reindex, pointRejected, isometry_rejected⟩
  sensitivity := ⟨fun i => ⟨pointRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, isometry_rejected⟩, fun e => nomatch e⟩
  dependence := point_dependence

end
end Reg.Support.ThetaLatticeIsometry
