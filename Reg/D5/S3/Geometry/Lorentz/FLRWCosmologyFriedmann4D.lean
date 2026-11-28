import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Lorentz.FLRWCosmologyFriedmann4D
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Lorentz.FLRWCosmologyFriedmann4D
open LeanInformationAudit

namespace Reg.D5.S3.Geometry.Lorentz.FLRWCosmologyFriedmann4D

set_option autoImplicit false

noncomputable section

abbrev hubbleSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)

def hubbleActual : Realization hubbleSignature :=
  realize hubbleSignature
    (fun _ p t => hubble (flatScaleFactor p.1 (flatExponent p.2)) t)
    (fun e => nomatch e)

def hubbleErased : Realization hubbleSignature :=
  realize hubbleSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev hubbleArena : Arena where
  signature := hubbleSignature
  Law R := ∀ {a₁ w t : ℝ}, 0 < a₁ → 0 < t →
    R.readout () ⟨a₁, w⟩ t * t = 2 / (3 * (1 + w))

private theorem hubble_erased_fails : ¬ hubbleArena.Law hubbleErased := by
  intro h
  have he := h (a₁ := 1) (w := 0) (t := 1) (by norm_num) (by norm_num)
  change (0 : ℝ) * 1 = 2 / (3 * (1 + 0)) at he
  norm_num at he

def hubbleFamily : Registration hubbleArena (type_of% (@flat_power_law_hubble_age)) where
  actual := hubbleActual
  bridge := Iff.rfl
  variation := ⟨@flat_power_law_hubble_age, hubbleErased, hubble_erased_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    hubbleArena.Law hubbleActual hubbleErased hubble_erased_fails
  dependence := by
    intro _
    refine ⟨⟨1, 0⟩, 1, 2, ?_⟩
    change hubble (flatScaleFactor 1 (flatExponent 0)) 1 ≠
      hubble (flatScaleFactor 1 (flatExponent 0)) 2
    intro he
    have h₁ := flat_power_law_hubble_age (a₁ := 1) (w := 0) (t := 1) (by norm_num) (by norm_num)
    have h₂ := flat_power_law_hubble_age (a₁ := 1) (w := 0) (t := 2) (by norm_num) (by norm_num)
    rw [he] at h₁
    norm_num at h₁ h₂
    linarith

def hubbleRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@flat_power_law_hubble_age) (Realization hubbleSignature) Unit Unit where
  unitName := `D5.S3.Geometry.Lorentz.FLRWCosmologyFriedmann4D.flat_power_law_hubble_age.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Lorentz.FLRWCosmologyFriedmann4D.hubbleFamily
  realizationSource := none
  generated := false
  arena := .source ⟨hubbleArena⟩
  objectArena := .source ⟨hubbleArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source hubbleArena ⟨hubbleFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize hubbleSignature
    (fun _ p t => hubble (flatScaleFactor p.1 (flatExponent p.2)) t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.FLRWCosmologyFriedmann4D
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Geometry.Lorentz.FLRWCosmologyFriedmann4D
