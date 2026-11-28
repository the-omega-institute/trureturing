import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Fourier.ThetaShearMonotonicity

open D5.S3.Fourier.PlanarTheta
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.Support.ThetaShearMonotonicity
noncomputable section

abbrev shearSignature : Signature where
  Params := Σ _ : ℝ, ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def shearActual : Realization shearSignature :=
  realize shearSignature (fun _ p x => deriv (fun z => F p.1 z p.2) x)
    (fun e => nomatch e)

def shearRejected : Realization shearSignature :=
  realize shearSignature (fun _ _ _ => 0) (fun e => nomatch e)

def shearArena : Arena where
  signature := shearSignature
  Law R := ∀ {t y x : ℝ}, 0 < t → Real.sqrt 3 / 2 ≤ y →
    0 < x → x < 1 / 2 → R.readout () ⟨t, y⟩ x < 0

private theorem shear_bridge : (type_of% (@shear_derivative_neg)) ↔
    shearArena.Law shearActual := Iff.rfl

private theorem shear_zero : deriv (fun z => F 1 z 1) 0 = 0 := by
  have hd : HasDerivAt (fun z => F 1 z 1) (deriv (fun z => F 1 z 1) 0) 0 :=
    (hasDerivAt_shear 1 0 (by norm_num) (by norm_num)).differentiableAt.hasDerivAt
  have hn : HasDerivAt (fun z => F 1 z 1) (-deriv (fun z => F 1 z 1) 0) 0 := by
    have hd' : HasDerivAt (fun z => F 1 z 1)
        (deriv (fun z => F 1 z 1) 0) (-(0 : ℝ)) := by simpa using hd
    convert hd'.comp 0 ((hasDerivAt_id (0 : ℝ)).neg) using 1
    · funext z
      unfold F
      let e := Equiv.prodCongr (Equiv.neg ℤ) (Equiv.refl ℤ)
      calc
        _ = ∑' v : ℤ × ℤ, Real.exp (-Real.pi * 1 * Q z 1 (e v)) :=
          (e.tsum_eq (fun v => Real.exp (-Real.pi * 1 * Q z 1 v))).symm
        _ = _ := by
          apply tsum_congr
          intro v
          congr 1 <;> simp [Q, e] <;> ring
    · ring
  have h := hd.unique hn
  linarith

private theorem height_one : Real.sqrt 3 / 2 ≤ (1 : ℝ) := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  nlinarith [Real.sqrt_nonneg (3 : ℝ)]

private theorem shear_dependence : ObservationalDependence shearSignature shearActual := by
  intro i
  refine ⟨⟨1, 1⟩, 0, 1 / 4, ?_⟩
  change deriv (fun z => F 1 z 1) 0 ≠ deriv (fun z => F 1 z 1) (1 / 4)
  rw [shear_zero]
  exact ne_of_gt (shear_derivative_neg (t := 1) (y := 1) (x := 1 / 4)
    (by norm_num) height_one (by norm_num) (by norm_num))

private theorem shear_rejected : ¬ shearArena.Law shearRejected := by
  intro h
  have h1 := h (t := 1) (y := 1) (x := 1 / 4) (by norm_num) height_one
    (by norm_num) (by norm_num)
  norm_num [shearRejected, realize] at h1

def shearRegistration : Registration shearArena
    (type_of% (@shear_derivative_neg)) where
  actual := shearActual
  bridge := shear_bridge
  variation := ⟨@shear_derivative_neg, shearRejected, shear_rejected⟩
  sensitivity := ⟨fun i => ⟨shearRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, shear_rejected⟩, fun e => nomatch e⟩
  dependence := shear_dependence

def valueActual : Realization shearSignature :=
  realize shearSignature (fun _ p x => F p.1 x p.2) (fun e => nomatch e)

def valueRejected : Realization shearSignature :=
  realize shearSignature (fun _ p _ => F p.1 (1 / 2) p.2 + 1) (fun e => nomatch e)

def minimumArena : Arena where
  signature := shearSignature
  Law R := ∀ {t y x : ℝ}, 0 < t → Real.sqrt 3 / 2 ≤ y → 0 ≤ x → x ≤ 1 / 2 →
    F t (1 / 2) y ≤ R.readout () ⟨t, y⟩ x ∧
      (R.readout () ⟨t, y⟩ x = F t (1 / 2) y ↔ x = 1 / 2)

private theorem minimum_bridge : (type_of% (@shear_minimum)) ↔
    minimumArena.Law valueActual := Iff.rfl

private theorem value_dependence : ObservationalDependence shearSignature valueActual := by
  intro i
  refine ⟨⟨1, 1⟩, 0, 1 / 2, ?_⟩
  change F 1 0 1 ≠ F 1 (1 / 2) 1
  intro he
  have h := (shear_minimum (t := 1) (y := 1) (x := 0)
    (by norm_num) height_one (by norm_num) (by norm_num)).2.mp he
  norm_num at h

private theorem minimum_rejected : ¬ minimumArena.Law valueRejected := by
  intro h
  have h1 := (h (t := 1) (y := 1) (x := 1 / 2) (by norm_num) height_one
    (by norm_num) (by norm_num)).2.mpr rfl
  change F 1 (1 / 2) 1 + 1 = F 1 (1 / 2) 1 at h1
  linarith

def minimumRegistration : Registration minimumArena (type_of% (@shear_minimum)) where
  actual := valueActual
  bridge := minimum_bridge
  variation := ⟨@shear_minimum, valueRejected, minimum_rejected⟩
  sensitivity := ⟨fun i => ⟨valueRejected,
    fun j h => (h (show j = i from @Subsingleton.elim Unit _ j i)).elim,
    rfl, minimum_rejected⟩, fun e => nomatch e⟩
  dependence := value_dependence

end
end Reg.Support.ThetaShearMonotonicity
