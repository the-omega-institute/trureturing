import Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary
import Reg.Support.SingleDependentReadout


open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open Bilateral ResetFactors ResetCodebook MemoryGraph SpectralBoundary InteriorRoot WordWeightRegrouping
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter Topology
open scoped ENNReal NNReal

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.ExactOriginal148
noncomputable section

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => Set (ℤ → CuLetter)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature := realize.{0,0,0,0,0} observationSignature (fun _ _ X => weightedFactorRate X) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize observationSignature (fun _ _ _ => -1) (fun e => nomatch e)
abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (side : MemorySide) (d : ℝ) (high : oneStepCeiling < d), (MemoryLanguage side 1 1 d = {fun _ : ℤ => CuLetter.u}) ∧ (∀ z : ℝ, 0 ≤ z → weightedRadius side 1 1 d z = ENNReal.ofReal (z^6)) ∧ (∀ z : ℝ, 0 ≤ z → (weightedRadius side 1 1 d z = 1 ↔ z = 1)) ∧ r.readout () () (MemoryLanguage side 1 1 d) = 0

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  have impossible := (h .lower (oneStepCeiling + 1) (lt_add_one _)).2.2.2
  norm_num [rejected, realize] at impossible

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.original_closed_root_boundary) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.original_closed_root_boundary, rejected, rejected_law⟩
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
    refine ⟨(), MemoryLanguage .lower 1 1 (oneStepCeiling + 1),
      MemoryLanguage .lower 0 2 0, ?_⟩
    exact Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ResetFactors.RateWitness.actual_rate_separation

def original_closed_root_boundary_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.original_closed_root_boundary)
      (type_of% (realize.{0,0,0,0,0} observationSignature (fun _ _ X => weightedFactorRate X) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.ExactOriginal148.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.ExactOriginal148.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature (fun _ _ X => weightedFactorRate X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_closed_root_boundary_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.SpectralBoundary.ExactOriginal148
