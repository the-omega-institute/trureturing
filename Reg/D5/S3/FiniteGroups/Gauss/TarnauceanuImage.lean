import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.Gauss.TarnauceanuImage
import Reg.Support.DependentFamily

namespace Reg.D5.S3.FiniteGroups.Gauss.TarnauceanuImage

open _root_.D5.S3.FiniteGroups.Gauss.TarnauceanuImage
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

/-- State is the source exponent. The sole readout is the Gauss value at that
exponent, before any substitution using the closed formula. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => gauss (Family n)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (n : ℕ), 1 ≤ n → r.readout () () n = 3 - (2 : ℝ) ^ (-(n : ℤ))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h 1 (by decide)
  change (0 : ℝ) = 3 - 2 ^ (-(1 : ℤ)) at hz
  norm_num at hz

def source_registration : Registration arena (type_of% @gauss_family) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨gauss_family, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    change gauss (Family 1) ≠ gauss (Family 2)
    rw [gauss_family 1 (by decide), gauss_family 2 (by decide)]
    norm_num

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@gauss_family) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.FiniteGroups.Gauss.TarnauceanuImage.unit
  realizationName := `Reg.D5.S3.FiniteGroups.Gauss.TarnauceanuImage.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => gauss (Family n)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.Gauss.TarnauceanuImage
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.FiniteGroups.Gauss.TarnauceanuImage
