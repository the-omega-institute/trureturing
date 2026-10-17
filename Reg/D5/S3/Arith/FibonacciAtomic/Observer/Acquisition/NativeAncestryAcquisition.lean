import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeAncestryAcquisition
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeAncestryAcquisition
open _root_.D5.S3.Arith.FibonacciAtomic
open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply readout)
open Geometry.NativeAncestryDefectCube (positions variant defectB defectD fill)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeAncestryAcquisition
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped symmDiff
noncomputable section
namespace Support

def signature : Signature where
  Params := Address
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Reply
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ q t => readout q t) (fun e => nomatch e)
def bad : Realization signature :=
  realize signature (fun _ _ t => readout [false] t) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law F := ∀ (t : Source) (A B : Finset Address), A ⊆ positions t → B ⊆ positions t →
    ∀ (q : Address), (∀ p ∈ A ∆ B, q ∉ support p) →
    F.readout () q (variant t A) = F.readout () q (variant t B)

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have eq := h defectB ∅ {[]} (by decide) (by decide) [] (by simp [support])
  change Reply.branch = Reply.beta at eq
  cases eq

def evidence : Registration arena (type_of% (@outside_support_invariance)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨outside_support_invariance,bad,bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual bad bad_law
  dependence := by
    intro i
    refine ⟨[],.of true,.of false,?_⟩
    change Reply.alpha ≠ Reply.beta
    decide

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@outside_support_invariance) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeAncestryAcquisition.outside_support_invariance.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeAncestryAcquisition.Support.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q t => readout q t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeAncestryAcquisition
    definition := none
    coordinates := #[5]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms evidence
#print axioms registration
end Support
end
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeAncestryAcquisition
