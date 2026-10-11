import D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.ExactOriginal203
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ z => compose C z) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => c0 + 1) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (j : Side) (model : Model) (execution : List Return),
      LegalWord .G0 .G0 (sourcePrefix j model execution) ∧
      (∀ p, source j model execution ((observedPrefix j model execution).length + p) =
        address (tailPrefix j) p) ∧
      (∀ p, coordinate (sourcePrefix j model execution)
          ((observedPrefix j model execution).length + p) = coordinate (tailPrefix j) p) ∧
      coordinate (externalWord j execution ++ anchor j model ++ tailPrefix j) 0 =
        c0 + sign j * execute j execution (initial j model) ∧
      (observedPrefix j model execution).length = observationOffset model + listWeight execution ∧
      (history model execution).length = observationOffset model + listWeight execution ∧
      (∀ D, r.readout () () (c0 + sign j * D) = c0 + sign j * (chi * D)) ∧
      (∀ D, compose (block j) (c0 + sign j * D) =
        c0 + sign j * (aSide j + rho * D)) ∧
      (∀ (a : Return) D, compose (returnWord j a) (c0 + sign j * D) =
        c0 + sign j * returnMap j a D) ∧
      (∀ (xs : List Return) D, compose (externalWord j xs) (c0 + sign j * D) =
        c0 + sign j * execute j xs D) ∧
      compose (tailPrefix j) 0 = c0 + sign j * xSide j

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := (h .high .original []).2.2.2.2.2.2.1 0
  norm_num [rejected, realize] at impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.paired_source_reconstruction) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.paired_source_reconstruction, rejected, rejected_law⟩
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
    refine ⟨(), c0, c0 + 1, ?_⟩
    have hc := (paired_source_reconstruction .high .original []).2.2.2.2.2.2.1
    have hc0 := hc 0
    have hc1 := hc 1
    simp only [sign, mul_zero, add_zero, one_mul, mul_one] at hc0 hc1
    have gp : 0 < g := by
      have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
      dsimp [g, t]
      nlinarith [Real.sqrt_nonneg (5 : ℝ)]
    have cp : 0 < chi := pow_pos gp 20
    change compose C c0 ≠ compose C (c0 + 1)
    rw [hc0, hc1]
    exact ne_of_lt (lt_add_of_pos_right c0 cp)

def paired_source_reconstruction_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.paired_source_reconstruction)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ z => compose C z) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.ExactOriginal203.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.ExactOriginal203.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ z => compose C z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms paired_source_reconstruction_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource.ExactOriginal203
