import D5.S3.ConceptDynamics.Coding.PrimitiveLifts.IndependentRootCoherenceSeparation
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! The full degree-quantified root-fiber law with its actual multiplication readout. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.ConceptDynamics.Coding.PrimitiveLifts.IndependentRootInfiniteFibers

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
  realize signature (fun _ m x => m • x) (fun e => nomatch e)

private abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ m : ℕ, 1 < m → Infinite {x : G // R.readout () m x = c}

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  letI : IsEmpty {x : G // rejected.readout () 2 x = c} :=
    ⟨fun x => independent_roots_without_rational_coherence.1 x.property.symm⟩
  letI := h 2 (by decide)
  exact not_finite {x : G // rejected.readout () 2 x = c}

private def family : Registration arena (type_of% infinite_root_fiber) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨infinite_root_fiber, rejected, rejected_law⟩
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
    obtain ⟨b, hb⟩ := independent_roots_without_rational_coherence.2.2.1 2 (by decide)
    refine ⟨2, 0, b, ?_⟩
    change (2 : ℕ) • (0 : G) ≠ (2 : ℕ) • b
    rw [nsmul_zero, hb]
    exact independent_roots_without_rational_coherence.1.symm

def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    infinite_root_fiber (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.PrimitiveLifts.IndependentRootInfiniteFibers.unit
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
  readout := some (realize signature (fun _ m x => m • x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.PrimitiveLifts.IndependentRootCoherenceSeparation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.ConceptDynamics.Coding.PrimitiveLifts.IndependentRootInfiniteFibers
