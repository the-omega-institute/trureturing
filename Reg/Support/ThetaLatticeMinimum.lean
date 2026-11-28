import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.PlanarThetaFoundation
import D5.S3.Fourier.ThetaLatticeMinimum

open D5.S3.Fourier.PlanarTheta
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Reg.Support.PlanarThetaFoundation

namespace Reg.Support.ThetaLatticeMinimum
noncomputable section

def minimumArena : Arena where
  signature := basisSignature
  Law R := ∀ a b : ℂ, ∀ {A t : ℝ}, 0 < A →
    |a.re * b.im - a.im * b.re| = A → 0 < t →
    F (A * t) (1 / 2) (Real.sqrt 3 / 2) ≤ R.readout () ⟨a, b⟩ t ∧
      (R.readout () ⟨a, b⟩ t = F (A * t) (1 / 2) (Real.sqrt 3 / 2) ↔
        IsHexagonalBasis (((Real.sqrt A)⁻¹ : ℝ) • a) (((Real.sqrt A)⁻¹ : ℝ) • b))

private theorem minimum_bridge : (type_of% (@basis_theta_minimum_isometry)) ↔
    minimumArena.Law basisActual := Iff.rfl

def basisRejected : Realization basisSignature :=
  realize basisSignature (fun _ _ _ => -1) (fun e => nomatch e)

private theorem minimum_rejected : ¬ minimumArena.Law basisRejected := by
  intro h
  have h0 := (h 1 Complex.I (A := 1) (t := 1) (by norm_num) (by norm_num) (by norm_num)).1
  have hp : 0 ≤ F 1 (1 / 2) (Real.sqrt 3 / 2) :=
    tsum_nonneg (fun _ => (Real.exp_pos _).le)
  simp only [one_mul] at h0
  change F 1 (1 / 2) (Real.sqrt 3 / 2) ≤ -1 at h0
  linarith

def minimumRegistration : Registration minimumArena
    (type_of% (@basis_theta_minimum_isometry)) where
  actual := basisActual
  bridge := minimum_bridge
  variation := ⟨@basis_theta_minimum_isometry, basisRejected, minimum_rejected⟩
  sensitivity := ⟨fun i => ⟨basisRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, minimum_rejected⟩, fun e => nomatch e⟩
  dependence := basis_dependence

end
end Reg.Support.ThetaLatticeMinimum


namespace Reg.Support.ThetaLatticeMinimum
noncomputable section

abbrev normScaleSignature : Signature where
  Params := Σ _ : ℝ, Σ _ : ℂ, ℂ
  State _ := ℤ × ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def normScaleActual : Realization normScaleSignature :=
  realize normScaleSignature (fun _ p v =>
    Complex.normSq ((v.1 : ℂ) * (p.1 • p.2.1) + (v.2 : ℂ) * (p.1 • p.2.2)))
    (fun e => nomatch e)

def normScaleRejected : Realization normScaleSignature :=
  realize normScaleSignature (fun _ p v => p.1 ^ 2 *
    Complex.normSq ((v.1 : ℂ) * p.2.1 + (v.2 : ℂ) * p.2.2) + 1)
    (fun e => nomatch e)

def normScaleArena : Arena where
  signature := normScaleSignature
  Law R := ∀ (r : ℝ) (a b : ℂ) (v : ℤ × ℤ),
    R.readout () ⟨r, a, b⟩ v =
      r ^ 2 * Complex.normSq ((v.1 : ℂ) * a + (v.2 : ℂ) * b)

private theorem normScale_bridge : (type_of% (@basis_normSq_scale)) ↔
    normScaleArena.Law normScaleActual := Iff.rfl

private theorem normScale_rejected : ¬ normScaleArena.Law normScaleRejected := by
  intro h
  have h0 := h 1 1 Complex.I (0, 0)
  norm_num [normScaleRejected, realize] at h0

private theorem normScale_dependence :
    ObservationalDependence normScaleSignature normScaleActual := by
  intro i
  refine ⟨⟨1, 1, Complex.I⟩, (0, 0), (1, 0), ?_⟩
  norm_num [normScaleActual, realize]

def normScaleRegistration : Registration normScaleArena (type_of% (@basis_normSq_scale)) where
  actual := normScaleActual
  bridge := normScale_bridge
  variation := ⟨@basis_normSq_scale, normScaleRejected, normScale_rejected⟩
  sensitivity := ⟨fun i => ⟨normScaleRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, normScale_rejected⟩, fun e => nomatch e⟩
  dependence := normScale_dependence

abbrev thetaScaleSignature : Signature where
  Params := Σ _ : ℝ, Σ _ : ℂ, ℂ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def thetaScaleActual : Realization thetaScaleSignature :=
  realize thetaScaleSignature (fun _ p t => basisTheta t (p.1 • p.2.1) (p.1 • p.2.2))
    (fun e => nomatch e)

def thetaScaleRejected : Realization thetaScaleSignature :=
  realize thetaScaleSignature (fun _ p t => basisTheta (t * p.1 ^ 2) p.2.1 p.2.2 + 1)
    (fun e => nomatch e)

def thetaScaleArena : Arena where
  signature := thetaScaleSignature
  Law R := ∀ (r : ℝ) (a b : ℂ) (t : ℝ),
    R.readout () ⟨r, a, b⟩ t = basisTheta (t * r ^ 2) a b

private theorem thetaScale_bridge : (type_of% (@basisTheta_scale)) ↔
    thetaScaleArena.Law thetaScaleActual := Iff.rfl

private theorem thetaScale_rejected : ¬ thetaScaleArena.Law thetaScaleRejected := by
  intro h
  have h0 := h 1 1 Complex.I 1
  change basisTheta (1 * 1 ^ 2) 1 Complex.I + 1 = basisTheta (1 * 1 ^ 2) 1 Complex.I at h0
  linarith

private theorem thetaScale_dependence :
    ObservationalDependence thetaScaleSignature thetaScaleActual := by
  intro i
  obtain ⟨p, x, y, h⟩ := basis_dependence ()
  refine ⟨⟨1, p⟩, x, y, ?_⟩
  simpa only [thetaScaleActual, basisActual, realize, one_smul] using h

def thetaScaleRegistration : Registration thetaScaleArena (type_of% (@basisTheta_scale)) where
  actual := thetaScaleActual
  bridge := thetaScale_bridge
  variation := ⟨@basisTheta_scale, thetaScaleRejected, thetaScale_rejected⟩
  sensitivity := ⟨fun i => ⟨thetaScaleRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, thetaScale_rejected⟩, fun e => nomatch e⟩
  dependence := thetaScale_dependence

abbrev areaSignature : Signature where
  Params := Σ _ : ℂ, ℂ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def areaActual : Realization areaSignature :=
  realize areaSignature (fun _ p A =>
    |(((Real.sqrt A)⁻¹ : ℝ) • p.1).re * (((Real.sqrt A)⁻¹ : ℝ) • p.2).im -
      (((Real.sqrt A)⁻¹ : ℝ) • p.1).im * (((Real.sqrt A)⁻¹ : ℝ) • p.2).re|) (fun e => nomatch e)

def areaRejected : Realization areaSignature :=
  realize areaSignature (fun _ _ _ => 0) (fun e => nomatch e)

def areaArena : Arena where
  signature := areaSignature
  Law R := ∀ (a b : ℂ) {A : ℝ}, 0 < A →
    |a.re * b.im - a.im * b.re| = A → R.readout () ⟨a, b⟩ A = 1

private theorem area_bridge : (type_of% (@basis_normalized_area)) ↔
    areaArena.Law areaActual := Iff.rfl

private theorem area_rejected : ¬ areaArena.Law areaRejected := by
  intro h
  have h0 := h 1 Complex.I (A := 1) (by norm_num) (by norm_num)
  norm_num [areaRejected, realize] at h0

private theorem area_dependence : ObservationalDependence areaSignature areaActual := by
  intro i
  refine ⟨⟨1, Complex.I⟩, 0, 1, ?_⟩
  norm_num [areaActual, realize]

def areaRegistration : Registration areaArena (type_of% (@basis_normalized_area)) where
  actual := areaActual
  bridge := area_bridge
  variation := ⟨@basis_normalized_area, areaRejected, area_rejected⟩
  sensitivity := ⟨fun i => ⟨areaRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, area_rejected⟩, fun e => nomatch e⟩
  dependence := area_dependence

end
end Reg.Support.ThetaLatticeMinimum
