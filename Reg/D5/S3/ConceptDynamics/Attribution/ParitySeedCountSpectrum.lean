import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum
import Reg.Support.DependentFamily

/-! Budget sensitivity of the zero fixed-count condition. -/

set_option autoImplicit false

namespace Reg.D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedOptimization
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ n k => decide (Odd (n + 2) ∨ Even k)) (fun e => nomatch e)

def alwaysFalse : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n k, RealizableSeedCounts n k (fun _ => 0) ↔ R.readout () n k = true

private theorem always_false_fails : ¬ arena.Law alwaysFalse := by
  intro law
  have existsZero := (zero_coordinate_counts_iff 0 2).2 (Or.inr ⟨1, rfl⟩)
  exact Bool.false_ne_true ((law 0 2).1 existsZero)

def family : Registration arena (type_of% zero_coordinate_counts_iff) where
  actual := actual
  bridge := by simp [arena, actual, realize]
  variation := ⟨by simpa [arena, actual, realize] using zero_coordinate_counts_iff,
    alwaysFalse, always_false_fails⟩
  sensitivity := by
    constructor
    · intro role
      exact ⟨alwaysFalse, fun other h => (h (Subsingleton.elim other role)).elim,
        rfl, always_false_fails⟩
    · intro e
      exact nomatch e
  dependence := by
    intro role
    cases role
    refine ⟨0, 1, 2, ?_⟩
    decide

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    zero_coordinate_counts_iff (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum.zeroCondition
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n k => decide (Odd (n + 2) ∨ Even k))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Attribution.ParitySeedCountSpectrum
