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

open Geometry.AncestorAreaInstability (T)
open ActualTreeReadoutAcquisition (paid)
open _root_.D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Hist)

namespace RecordFace
abbrev signature := Reg.Support.SingleDependentReadout.signature Nat
  (fun _ => Hist (fun _ : Address => Reply)) (fun _ => Nat)
def actual : Realization signature :=
  realize signature (fun _ n h => (compatible (T n) h).card) (fun e => nomatch e)
def bad : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law F := ∀ (n : ℕ) (hn : 3 ≤ n) (A : Finset Address)
    (hA : A ⊆ positions (T n)) (h : Hist (fun _ : Address => Reply))
    (truth : Consistent (T n) A h),
    (∀ B ⊆ positions (T n), Consistent (T n) B h ↔
      B ∩ hit (T n) h = A ∩ hit (T n) h) ∧
    F.readout () n h = 2 ^ (Nat.fib (n-2) - (hit (T n) h).card) ∧
    (compatibleSources (T n) h).card = 2 ^ (Nat.fib (n-2) - (hit (T n) h).card) ∧
    posterior (T n) h = (fun _ => ((compatible (T n) h).card : ℝ)⁻¹) ∧
    D5.S3.Entropy.MaxEntropy.shannonEntropy (posterior (T n) h) / Real.log 2 =
      (Nat.fib (n-2) - (hit (T n) h).card : ℕ)

private theorem bad_law : ¬ arena.Law bad := by
  intro law
  have eq := (law 3 (by decide) ∅ (by simp) [] (by simp [Consistent])).2.1
  change 0 = 2 ^ (Nat.fib (3-2) - (hit (T 3) []).card) at eq
  simpa [hit] using eq

def evidence : Registration arena (type_of% (@native_record_face)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨native_record_face,bad,bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual bad bad_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    have source : T 3 = defectB := by decide
    have empty := (native_record_face 3 (by decide) ∅ (by simp) []
      (by simp [Consistent])).2.1
    have truth : Consistent (T 3) ∅ [⟨[false],Reply.branch⟩] := by
      rw [source]
      simp [Consistent, variant, fill, defectB, readout]
    have queried := (native_record_face 3 (by decide) ∅ (by simp)
      [⟨[false],Reply.branch⟩] truth).2.1
    refine ⟨3, [], [⟨[false],Reply.branch⟩], ?_⟩
    change (compatible (T 3) []).card ≠
      (compatible (T 3) [⟨[false],Reply.branch⟩]).card
    rw [empty,queried,source]
    have pos : positions defectB = {[]} := by decide
    norm_num [hit,pos,Finset.filter_singleton,support]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_record_face) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeAncestryAcquisition.native_record_face.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeAncestryAcquisition.RecordFace.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n h => (compatible (T n) h).card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeAncestryAcquisition
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","body","arg","fn","arg","fn","arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms evidence
#print axioms registration
end RecordFace

namespace CanonicalQueries
abbrev signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => Nat) (fun _ => Nat)
def actual : Realization signature :=
  realize signature (fun _ _ n => Nat.fib (n-2)) (fun e => nomatch e)
def bad : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law F := ∀ (n : ℕ) (hn : 3 ≤ n),
    (∀ R : CubeRun (T n), Correct (T n) R →
      F.readout () () n ≤ (paid (R.trace ∅)).card) ∧
    ∃ R : CubeRun (T n), Correct (T n) R ∧
      Function.FactorsThrough R.policy ActualCoarseReadoutHistory.kappa_hist ∧
      (∀ A ⊆ positions (T n), (paid (R.trace A)).card ≤ Nat.fib (n-2)) ∧
      (paid (R.trace ∅)).card = Nat.fib (n-2)

private theorem bad_law : ¬ arena.Law bad := by
  intro law
  obtain ⟨R,correct,_,_,cost⟩ := (law 3 (by decide)).2
  have lower := (law 3 (by decide)).1 R correct
  change 2 ≤ (paid (R.trace ∅)).card at lower
  norm_num at cost
  omega

def evidence : Registration arena (type_of% (@optimal_canonical_queries)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨optimal_canonical_queries,bad,bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual bad bad_law
  dependence := by
    change ObservationalDependence signature actual
    intro ⟨⟩
    refine ⟨(),3,5,?_⟩
    change Nat.fib (3-2) ≠ Nat.fib (5-2)
    decide

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@optimal_canonical_queries) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeAncestryAcquisition.optimal_canonical_queries.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeAncestryAcquisition.CanonicalQueries.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => Nat.fib (n-2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeAncestryAcquisition
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","fn","arg","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms evidence
#print axioms registration
end CanonicalQueries

namespace SingleDefectSuccess
abbrev signature := Reg.Support.SingleDependentReadout.signature Nat
  (fun _ => Nat) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ q n => 1/2 + (q : ℝ)/(2*Nat.fib (n-2))) (fun e => nomatch e)
def bad : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law F := ∀ (n : ℕ) (hn : 3 ≤ n) (q : ℕ)
    (hq : q ≤ Nat.fib (n-2)),
    (∀ R : CubeRun (T n),
      (∀ A ⊆ positions (T n), (hit (T n) (R.trace A)).card ≤ q) →
      success (T n) R ≤ F.readout () q n) ∧
    (∃ R : CubeRun (T n),
      (∀ A ⊆ positions (T n), (hit (T n) (R.trace A)).card ≤ q) ∧
      success (T n) R = 1/2 + (q : ℝ)/(2*Nat.fib (n-2))) ∧
    (∀ (Ω : Type) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
      [MeasureTheory.IsProbabilityMeasure μ] (R : Ω → CubeRun (T n)),
      Measurable (fun ω => success (T n) (R ω)) →
      (∀ ω A, A ⊆ positions (T n) → (hit (T n) ((R ω).trace A)).card ≤ q) →
      ∫ ω, success (T n) (R ω) ∂μ ≤ 1/2 + (q : ℝ)/(2*Nat.fib (n-2))) ∧
    (∀ (Ω : Type) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
      [MeasureTheory.IsProbabilityMeasure μ] (R : Ω → CubeRun (T n)) (δ : ℝ), δ < 1/2 →
      (∀ A ⊆ positions (T n), Measurable (fun ω => (R ω).answer A)) →
      (∀ ω A, A ⊆ positions (T n) → (hit (T n) ((R ω).trace A)).card ≤ q) →
      (∀ A ⊆ positions (T n), 1-δ ≤ ∫ ω, reward (R ω) A ∂μ) →
      (1-2*δ)*(Nat.fib (n-2) : ℝ) ≤ q)

private theorem bad_law : ¬ arena.Law bad := by
  intro law
  obtain ⟨R,budget,score⟩ := (law 3 (by decide) 0 (by decide)).2.1
  have bound := (law 3 (by decide) 0 (by decide)).1 R budget
  change success (T 3) R ≤ 0 at bound
  norm_num at score
  linarith

def evidence : Registration arena (type_of% (@optimal_single_defect_success)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨optimal_single_defect_success,bad,bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual bad bad_law
  dependence := by
    change ObservationalDependence signature actual
    intro ⟨⟩
    refine ⟨1,3,5,?_⟩
    norm_num [actual,realize]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@optimal_single_defect_success) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeAncestryAcquisition.optimal_single_defect_success.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeAncestryAcquisition.SingleDefectSuccess.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q n => 1/2 + (q : ℝ)/(2*Nat.fib (n-2))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeAncestryAcquisition
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body","body","body","body","fn","arg","body","body","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms evidence
#print axioms registration
end SingleDefectSuccess

end
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeAncestryAcquisition
