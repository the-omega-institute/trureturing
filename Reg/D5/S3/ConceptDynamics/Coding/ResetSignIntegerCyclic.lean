import D5.S3.ConceptDynamics.Coding.ResetNativeUnitNormalForm
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic

set_option maxHeartbeats 800000
open Polynomial
open _root_.D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic
open _root_.D5.S3.ConceptDynamics.Coding.ResetNumberedHistories (resetLabel)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic
noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State _ := ℤ[X]
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ[X]
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature :=
  realize signature (fun _ _ p => p) (fun e => nomatch e)

abbrev bad : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev presentationArena : Arena where
  signature := signature
  Law r := ∀ q : ℕ,
    (forward q).comp (backward q) = RingHom.id (QF q) ∧
    (backward q).comp (forward q) = RingHom.id (QP q) ∧
    (∀ p : ℤ[X], ringEquiv q (pp q (inclusion p)) = fp q (r.readout () q p)) ∧
    (∀ p : ℤ[X], (ringEquiv q).symm (fp q p) = pp q (inclusion p)) ∧
    ringEquiv q (pp q X) = fp q X ∧
    ringEquiv q (pp q (C resetLabel)) = fp q (W q) ∧
    (∀ z : ℤ, ringEquiv q (pp q (C (algebraMap ℤ R z))) = fp q (C z)) ∧
    ringEquiv q 1 = 1 ∧
    (q = 1 → ringEquiv q (pp q (C resetLabel)) = fp q X)

private def evaluateAtOne : QF 1 →+* ℤ :=
  Ideal.Quotient.lift _ (Polynomial.evalRingHom 1) (by
    intro p hp
    rcases Ideal.mem_span_singleton'.mp hp with ⟨a, rfl⟩
    rw [map_mul]
    have hf : Polynomial.evalRingHom (1 : ℤ) (F 1) = 0 := by
      simp [F, S, Polynomial.evalRingHom]
    rw [hf, mul_zero])

private theorem bad_presentation : ¬ presentationArena.Law bad := by
  intro h
  have hh := (h 1).2.2.1 (1 : ℤ[X])
  have hz : (1 : QF 1) = 0 := by
    simpa [bad, realize] using hh
  have hi := congrArg evaluateAtOne hz
  norm_num at hi

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  simp [actual, realize]

def presentationEvidence : Registration presentationArena (∀ q : ℕ,
    (forward q).comp (backward q) = RingHom.id (QF q) ∧
    (backward q).comp (forward q) = RingHom.id (QP q) ∧
    (∀ p : ℤ[X], ringEquiv q (pp q (inclusion p)) = fp q p) ∧
    (∀ p : ℤ[X], (ringEquiv q).symm (fp q p) = pp q (inclusion p)) ∧
    ringEquiv q (pp q X) = fp q X ∧
    ringEquiv q (pp q (C resetLabel)) = fp q (W q) ∧
    (∀ z : ℤ, ringEquiv q (pp q (C (algebraMap ℤ R z))) = fp q (C z)) ∧
    ringEquiv q 1 = 1 ∧
    (q = 1 → ringEquiv q (pp q (C resetLabel)) = fp q X) ) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨literal_presentation, bad, bad_presentation⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_presentation⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def literal_presentation_registration :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (_root_.D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic.literal_presentation)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic.presentation_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic.presentationEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨presentationArena⟩
  objectArena := .source ⟨presentationArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source presentationArena ⟨presentationEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "arg", "arg", "fn", "arg", "body", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic

namespace Reg.D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic.geometricAudit
open Polynomial
open _root_.D5.S3.ConceptDynamics.Coding
open _root_.D5.S3.ConceptDynamics.Coding.ResetStandardBeamGeometry
open _root_.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect
open _root_.D5.S3.ConceptDynamics.Coding.StandardBeamHomeomorphisms
open _root_.D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic
open _root_.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing
open _root_.D5.S3.ConceptDynamics.Coding.ResetIntegralUnits
open _root_.D5.S3.ConceptDynamics.Coding.ResetNativeIntegerChart
open _root_.D5.S3.ConceptDynamics.Coding.ResetHistoryKernel
open _root_.D5.S3.ConceptDynamics.Coding.ResetNativeUnitNormalForm
open _root_.D5.S3.ConceptDynamics.Coding.ResetFullStandardBeamRepresentation
open _root_.D5.S3.ConceptDynamics.Coding.ResetNumberedHistories
open _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinCohnReductionCore
open _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open _root_.D5.S0.Carrier
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped QuadraticAlgebra
noncomputable section
local instance nativeIntModule (q : ℕ) : Module ℤ (Native q) := AddCommGroup.toIntModule _
abbrev signature : Signature where
  Params := Unit
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ℤ[X]
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature := realize signature (fun _ _ q => S q) (fun e => nomatch e)
abbrev bad : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (q : ℕ),
    X ^ q - (X - 1) * r.readout () () q = 1
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have he := congrArg (fun p : ℤ[X] => p.coeff 1) (h 1)
  norm_num [bad, realize, Polynomial.coeff_one] at he
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrArg (fun p : ℤ[X] => p.coeff 0) h
  norm_num [actual, realize, S, Finset.sum_range_succ] at he
def evidence : Registration arena (∀ (q : ℕ),
    X ^ q - (X - 1) * S q = 1) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic.geometric, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (_root_.D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic.geometric) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic.geometricAudit.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic.geometricAudit.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ q => S q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end
end Reg.D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic.geometricAudit

namespace Reg.D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic.sign_squareAudit
open Polynomial
open _root_.D5.S3.ConceptDynamics.Coding
open _root_.D5.S3.ConceptDynamics.Coding.ResetStandardBeamGeometry
open _root_.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect
open _root_.D5.S3.ConceptDynamics.Coding.StandardBeamHomeomorphisms
open _root_.D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic
open _root_.D5.S3.ConceptDynamics.Coding.ResetIntegralGluing
open _root_.D5.S3.ConceptDynamics.Coding.ResetIntegralUnits
open _root_.D5.S3.ConceptDynamics.Coding.ResetNativeIntegerChart
open _root_.D5.S3.ConceptDynamics.Coding.ResetHistoryKernel
open _root_.D5.S3.ConceptDynamics.Coding.ResetNativeUnitNormalForm
open _root_.D5.S3.ConceptDynamics.Coding.ResetFullStandardBeamRepresentation
open _root_.D5.S3.ConceptDynamics.Coding.ResetNumberedHistories
open _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinCohnReductionCore
open _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open _root_.D5.S0.Carrier
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped QuadraticAlgebra
noncomputable section
local instance nativeIntModule (q : ℕ) : Module ℤ (Native q) := AddCommGroup.toIntModule _
abbrev signature : Signature where
  Params := Unit
  State p := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ℤ[X]
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization signature := realize signature (fun _ _ q => W q) (fun e => nomatch e)
abbrev bad : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (q : ℕ),
    fp q (r.readout () () q) * fp q (r.readout () () q) = 1
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have he : (0 : QF 2) = 1 := by simpa [bad, realize] using h 2
  have hg := congrArg goldenComponent he
  have ha := congrArg GoldenInt.a hg
  norm_num at ha
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrArg (fun p : ℤ[X] => p.coeff 1) h
  norm_num [actual, realize, W, S, Finset.sum_range_succ, Polynomial.coeff_one] at he
def evidence : Registration arena (∀ (q : ℕ),
    fp q (W q) * fp q (W q) = 1) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic.sign_square, bad, bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (_root_.D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic.sign_square) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic.sign_squareAudit.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic.sign_squareAudit.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ q => W q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end
end Reg.D5.S3.ConceptDynamics.Coding.ResetSignIntegerCyclic.sign_squareAudit
