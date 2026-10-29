import D5.S3.ConceptDynamics.Coding.PrimitiveLifts.IndependentRootCoherenceSeparation
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! The complete separation law with its original positive-degree multiplication readout. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.ConceptDynamics.Coding.PrimitiveLifts.IndependentRootCoherenceSeparation

open _root_.D5.S3.ConceptDynamics.Coding.PrimitiveLifts.IndependentRootCoherenceSeparation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

private abbrev signature : Signature where
  Params := ℕ
  State _ := G
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := G
  Anchor := Empty
  finiteAnchor := inferInstance

private abbrev actual : Realization signature :=
  realize signature (fun _ n b => n • b) (fun e => nomatch e)

private abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := c ≠ 0 ∧ (2 : ℕ) • c = 0 ∧
    (∀ n : ℕ, 0 < n → ∃ b : G, R.readout () n b = c) ∧
    (∀ f : ℚ →+ G, f = 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨b, hb⟩ := h.2.2.1 1 (by decide)
  exact h.1 hb.symm

private def family : Registration arena
    (type_of% independent_roots_without_rational_coherence) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨independent_roots_without_rational_coherence, rejected, rejected_law⟩
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
    refine ⟨1, 0, c, ?_⟩
    change (1 : ℕ) • (0 : G) ≠ (1 : ℕ) • c
    simpa using independent_roots_without_rational_coherence.1.symm

def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    independent_roots_without_rational_coherence (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.PrimitiveLifts.IndependentRootCoherenceSeparation.unit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n b => n • b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.PrimitiveLifts.IndependentRootCoherenceSeparation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["arg", "arg", "fn", "arg", "body", "body", "arg", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.ConceptDynamics.Coding.PrimitiveLifts.IndependentRootCoherenceSeparation
