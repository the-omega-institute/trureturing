import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaBridge.OriginalSignedFourierRegularity
import Reg.Support.DependentFamily

/-! Faithful dependent-family audit of the literal two-boundary translation energy. -/

namespace Reg.D5.S3.Weil.ZetaBridge.OriginalSignedFourierRegularity

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.OriginalSignedFourierRegularity _root_.OriginalSignedCompressedFourier

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := ℝ × ℤ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p h => translationSquaredNorm p.1 p.2 h) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (L : ℝ) (_hL : 0 < L) (n : ℤ) (h : ℝ) (_hh : 0 ≤ h) (_hcap : h ≤ L),
    R.readout () ⟨L, n⟩ h =
      2 * h / L + 2 * (1 - h / L) * (1 - Real.cos (frequency L n * h))

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h 1 (by norm_num) 0 1 (by norm_num) (by norm_num)
  norm_num [rejected, realize] at hz

private lemma actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨⟨1, 0⟩, 0, 1, ?_⟩
  change translationSquaredNorm 1 0 0 ≠ translationSquaredNorm 1 0 1
  rw [translation_squared_norm 1 (by norm_num) 0 0 (by norm_num) (by norm_num),
    translation_squared_norm 1 (by norm_num) 0 1 (by norm_num) (by norm_num)]
  norm_num [frequency]

def family : Registration arena
    (type_of% (@_root_.OriginalSignedFourierRegularity.translation_squared_norm)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨translation_squared_norm, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (show (j : Unit) = (i : Unit) from Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.OriginalSignedFourierRegularity.translation_squared_norm)
    (type_of% (realize signature
      (fun _ p h => translationSquaredNorm p.1 p.2 h) (fun e => nomatch e))) Type Unit where
  unitName := `OriginalSignedFourierRegularity.translation_squared_norm.audit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.OriginalSignedFourierRegularity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p h => translationSquaredNorm p.1 p.2 h) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.OriginalSignedFourierRegularity
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Weil.ZetaBridge.OriginalSignedFourierRegularity
