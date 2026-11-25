import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.LocalWiring.AttainedPrefixAcquisitionSharpness
import Reg.Support.DependentFamily

/-! Source-equivalent registration of the actual native readout. -/

namespace Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.AttainedPrefixAcquisitionSharpness

open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring.AttainedPrefixAcquisitionSharpness
open _root_.D5.S3.Arith.FibonacciAtomic.LocalWiring
open LocalTwoStepRecognizer KnownSeedCurrentFibers PhysicalBirthClock OrderedBirthPrefix
open PublicRowSeedReadiness LawfulSourceReadiness NativePastAcquisitionBarrier
open AttainedPrefixAcquisition
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Σ _ : Nat, Address
  State _ := OutputStream × OutputStream
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p w => nextDisagreement p.1 p.2 w) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun a => nomatch a)

def arena : Arena where
  signature := signature
  Law F := ∀ (P : Promise) (_hP : P.Valid) (_hm : 0 < P.target),
    ∃ s, P.Legal s ∧
    (∀ n, 2 ≤ n → n < deadline P.target → ∃ t, P.Legal t ∧
      matureWord n s = matureWord n t ∧
      physicalTree n s ≠ physicalTree n t ∧
      (∃ p, F.readout () ⟨n,p⟩ (s,t) = true) ∧
      future n s ≠ future n t) ∧
    ∀ {Public Tape Local : Type} (F : Filter Tape) [Filter.NeBot F]
      (A : Observer Public Tape Local) (u : Public)
      (outLabels : Public → Tape → Record Local → Option Labelled)
      (outNext : Public → Tape → Record Local → Option (Address → Bool))
      (outFuture : Public → Tape → Record Local → Option FutureBehavior),
      (AllSourcesMatureSuccess F A u P outLabels physicalTree →
        ∀ᶠ tape in F, ∀ k, (run A u tape s k).stopped = true →
          deadline P.target ≤ (run A u tape s k).cut) ∧
      (AllSourcesMatureSuccess F A u P outNext (fun n w p => queryNext n p w) →
        ∀ᶠ tape in F, ∀ k, (run A u tape s k).stopped = true →
          deadline P.target ≤ (run A u tape s k).cut) ∧
      (AllSourcesMatureSuccess F A u P outFuture future →
        ∀ᶠ tape in F, ∀ k, (run A u tape s k).stopped = true →
          deadline P.target ≤ (run A u tape s k).cut)

private def rowOne : Promise := .row 1 (fun _ => false)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hpos : 0 < rowOne.target := by decide
  have hcut : 2 < deadline rowOne.target := (deadline_pos rowOne.target hpos).1
  obtain ⟨s,_,he,_⟩ := h rowOne trivial hpos
  obtain ⟨t,_,_,_,⟨p,hbad⟩,_⟩ := he 2 (by decide) hcut
  change false = true at hbad
  cases hbad

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨⟨2, [false,false]⟩, (fun _ => false, fun _ => false),
    (fun _ => false, fun _ => true), ?_⟩
  change nextDisagreement 2 [false,false] (fun _ => false, fun _ => false) ≠
    nextDisagreement 2 [false,false] (fun _ => false, fun _ => true)
  decide

def family : Registration arena (type_of% single_adaptive_hard_source) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨single_adaptive_hard_source, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@single_adaptive_hard_source) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.AttainedPrefixAcquisitionSharpness.unit
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.AttainedPrefixAcquisitionSharpness.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.LocalWiring.AttainedPrefixAcquisitionSharpness
    definition := none
    coordinates := #[4, 8]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "fn", "arg", "body",
        "body", "body", "arg", "body", "arg", "arg", "arg", "fn", "arg", "arg",
        "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S3.Arith.FibonacciAtomic.LocalWiring.AttainedPrefixAcquisitionSharpness
