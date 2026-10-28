import D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FiniteCoprimeRootObstruction
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! The sixth-power readout and its constant-h intervention. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FiniteCoprimeRootObstruction

open _root_.D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FiniteCoprimeRootObstruction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

private abbrev signature : Signature where
  Params := Unit
  State _ := H
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := H
  Anchor := Empty
  finiteAnchor := inferInstance

private abbrev actual : Realization signature :=
  realize signature (fun _ _ x => x ^ 6) (fun e => nomatch e)

private abbrev bad : Realization signature :=
  realize signature (fun _ _ _ => h) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law r :=
    Nat.card H = 72 ∧ orderOf h = 6 ∧
    (⟨QuaternionGroup.a 1, Multiplicative.ofAdd 6⟩ : H) ^ 2 = h ∧
    (⟨QuaternionGroup.a 2, Multiplicative.ofAdd 1⟩ : H) ^ 3 = h ∧
    (∀ x : H, r.readout () () x ≠ h) ∧
    (∃ x y : H, x * y ≠ y * x)

private theorem bad_law : ¬ arena.Law bad := by
  intro hb
  exact hb.2.2.2.2.1 1 rfl

private theorem sixth_readout_nonconstant :
    (1 : H) ^ 6 ≠ (⟨QuaternionGroup.a 2, Multiplicative.ofAdd 1⟩ : H) ^ 6 := by
  decide

private def evidence : Registration arena (type_of% finite72_obstruction) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finite72_obstruction, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    exact ⟨(), 1, (⟨QuaternionGroup.a 2, Multiplicative.ofAdd 1⟩ : H),
      sixth_readout_nonconstant⟩

def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    finite72_obstruction (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FiniteCoprimeRootObstruction.unit
  realizationName := ``evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x ^ 6) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FiniteCoprimeRootObstruction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "arg", "arg", "fn", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FiniteCoprimeRootObstruction

namespace Reg.D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FiniteCoprimeRootObstruction.Spectrum

open _root_.D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FiniteCoprimeRootObstruction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

private abbrev signature : Signature where
  Params := ℕ
  State _ := H
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := H
  Anchor := Empty
  finiteAnchor := inferInstance

private abbrev actual : Realization signature :=
  realize signature (fun _ q x => x ^ q) (fun e => nomatch e)

private abbrev bad : Realization signature :=
  realize signature (fun _ _ _ => h) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law r := ∀ q : ℕ,
    (∃ x : H, r.readout () q x = h) ↔
      Nat.gcd q 36 = 1 ∨ Nat.gcd q 36 = 2 ∨ Nat.gcd q 36 = 3

private theorem bad_law : ¬ arena.Law bad := by
  intro hb
  have impossible := (hb 0).mp ⟨1, rfl⟩
  norm_num at impossible

private def evidence : Registration arena (type_of% root_degree_spectrum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨root_degree_spectrum, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    exact ⟨1, 1, h, by change (1 : H) ≠ h; decide⟩

def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    root_degree_spectrum (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FiniteCoprimeRootObstruction.Spectrum.unit
  realizationName := ``evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q x => x ^ q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FiniteCoprimeRootObstruction
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms evidence
#print axioms registration

end Reg.D5.S3.ConceptDynamics.Coding.PrimitiveLifts.FiniteCoprimeRootObstruction.Spectrum
