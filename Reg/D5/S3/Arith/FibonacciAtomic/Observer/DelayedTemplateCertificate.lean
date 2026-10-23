import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.DelayedTemplateCertificate
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.DelayedTemplateCertificate
open _root_.D5.S3.Arith.FibonacciAtomic
open GenealogicalFiberTransport (Source substitution composition)
open ActualTreeReadoutAcquisition (Address Reply readout leaves)
open ActualLeafHistoryRigidity (subtree)
open Observer.DelayedOriginalReadout
open Observer.DelayedTemplateCertificate
open _root_.D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open _root_.D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Hist execute)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev reflectionSignature := Reg.Support.SingleDependentReadout.signature
  (Σ _ : Nat, Σ _ : Source, Address) (fun _ => Source) (fun _ => Reply)
def reflectionActual : Realization reflectionSignature :=
  realize reflectionSignature (fun _ p u => readout p.2.2 u) (fun e => nomatch e)
def reflectionBad : Realization reflectionSignature :=
  realize reflectionSignature (fun _ _ _ => .absent) (fun e => nomatch e)
abbrev reflectionArena : Arena where
  signature := reflectionSignature
  Law R := ∀ (N : Nat) (g u : Source) (h : DelayedMatches N g u),
    ∀ p ∈ leaves g, R.readout () ⟨N,g,p⟩ u = readout p g
private theorem reflection_bad : ¬ reflectionArena.Law reflectionBad := by
  intro h
  have he := h 0 (.of true) (.of true)
    ((delayed_template_certificate 0 (.of true) (.of true)).mpr rfl) [] (by simp [leaves])
  change Reply.absent = .alpha at he
  cases he
private theorem reflection_dependence : ObservationalDependence reflectionSignature reflectionActual := by
  intro i
  refine ⟨⟨0,.of true,[]⟩, .of true, .of false, ?_⟩
  change Reply.alpha ≠ .beta
  decide
def reflectionFamily : Registration reflectionArena (type_of% (@delayed_leaf_reflection)) where
  actual := reflectionActual
  bridge := Iff.rfl
  variation := ⟨@delayed_leaf_reflection, reflectionBad, reflection_bad⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ reflection_bad
  dependence := reflection_dependence
def delayed_leaf_reflection_registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@delayed_leaf_reflection) (Realization reflectionSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.DelayedTemplateCertificate.delayed_leaf_reflection.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.DelayedTemplateCertificate.reflectionFamily
  realizationSource := none
  generated := false
  arena := .source ⟨reflectionArena⟩
  objectArena := .source ⟨reflectionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source reflectionArena ⟨reflectionFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize reflectionSignature reflectionActual.readout reflectionActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.DelayedTemplateCertificate
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev certificateSignature := Reg.Support.SingleDependentReadout.signature
  (Σ _ : Nat, Source) (fun _ => Source) (fun _ => Source)
def certificateActual : Realization certificateSignature :=
  realize certificateSignature (fun _ _ u => u) (fun e => nomatch e)
def certificateBad : Realization certificateSignature :=
  realize certificateSignature (fun _ _ _ => .of true) (fun e => nomatch e)
abbrev certificateArena : Arena where
  signature := certificateSignature
  Law R := ∀ (N : Nat) (g u : Source), DelayedMatches N g u ↔ R.readout () ⟨N,g⟩ u = g
private theorem certificate_bad : ¬ certificateArena.Law certificateBad := by
  intro h
  have he := (h 0 (.of false) (.of false)).mp
    ((delayed_template_certificate 0 (.of false) (.of false)).mpr rfl)
  change FreeMagma.of true = FreeMagma.of false at he
  cases he
private theorem certificate_dependence : ObservationalDependence certificateSignature certificateActual := by
  intro i
  refine ⟨⟨0,.of true⟩, .of true, .of false, ?_⟩
  change FreeMagma.of true ≠ FreeMagma.of false
  intro he
  cases he
def certificateFamily : Registration certificateArena (type_of% (@delayed_template_certificate)) where
  actual := certificateActual
  bridge := Iff.rfl
  variation := ⟨@delayed_template_certificate, certificateBad, certificate_bad⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ certificate_bad
  dependence := certificate_dependence
def delayed_template_certificate_registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@delayed_template_certificate) (Realization certificateSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.DelayedTemplateCertificate.delayed_template_certificate.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.DelayedTemplateCertificate.certificateFamily
  realizationSource := none
  generated := false
  arena := .source ⟨certificateArena⟩
  objectArena := .source ⟨certificateArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source certificateArena ⟨certificateFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize certificateSignature certificateActual.readout certificateActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.DelayedTemplateCertificate
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev resourcesSignature := Reg.Support.SingleDependentReadout.signature
  (Nat) (fun _ => Source) (fun _ => List Address)
def resourcesActual : Realization resourcesSignature :=
  realize resourcesSignature (fun _ p u => templateQueries p u) (fun e => nomatch e)
def resourcesBad : Realization resourcesSignature :=
  realize resourcesSignature (fun _ _ _ => [[],[]]) (fun e => nomatch e)
abbrev resourcesArena : Arena where
  signature := resourcesSignature
  Law R := ∀ (N : Nat) (g : Source),
    (R.readout () N g).Nodup ∧
    (templateQueries N g).length = g.length ∧
    ((templateQueries N g).map List.length).sum =
      leafAddressSum g + (N/2)*g.length + (N%2)*(composition g).2 ∧
    ((templateQueries N g).map List.length).foldr max 0 = delayedRadius N g
private theorem resources_bad : ¬ resourcesArena.Law resourcesBad := by
  intro h
  have he := (h 0 (.of true)).1
  change ([[],[]] : List Address).Nodup at he
  simp at he
private theorem resources_dependence : ObservationalDependence resourcesSignature resourcesActual := by
  intro i
  refine ⟨0, .of true, .mul (.of true) (.of true), ?_⟩
  change ([[]] : List Address) ≠ [[false],[true]]
  decide
def resourcesFamily : Registration resourcesArena (type_of% (@delayed_template_resources)) where
  actual := resourcesActual
  bridge := Iff.rfl
  variation := ⟨@delayed_template_resources, resourcesBad, resources_bad⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ resources_bad
  dependence := resources_dependence
def delayed_template_resources_registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@delayed_template_resources) (Realization resourcesSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.DelayedTemplateCertificate.delayed_template_resources.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.DelayedTemplateCertificate.resourcesFamily
  realizationSource := none
  generated := false
  arena := .source ⟨resourcesArena⟩
  objectArena := .source ⟨resourcesArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source resourcesArena ⟨resourcesFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize resourcesSignature resourcesActual.readout resourcesActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.DelayedTemplateCertificate
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev serviceSignature := Reg.Support.SingleDependentReadout.signature
  (Σ _ : Nat, Source) (fun _ => Source) (fun _ => Option (Hist (fun _ : Address => Reply) × Bool))
def serviceActual : Realization serviceSignature :=
  realize serviceSignature (fun _ p u => execute readout (listController (templateQueries p.1 p.2)
    (fun h => templateCheck p.1 p.2 (h.map Sigma.snd)))
    ((templateQueries p.1 p.2).length+1) [] (substitution^[p.1] u)) (fun e => nomatch e)
def serviceBad : Realization serviceSignature :=
  realize serviceSignature (fun _ _ _ => none) (fun e => nomatch e)
abbrev serviceArena : Arena where
  signature := serviceSignature
  Law R := ∀ (N : Nat) (g u : Source),
    let qs := templateQueries N g
    let finish := fun h : Hist (fun _ : Address => Reply) => templateCheck N g (h.map Sigma.snd)
    R.readout () ⟨N,g⟩ u = some (listTrace qs (substitution^[N] u),
      templateCheck N g (qs.map (fun q => readout q (substitution^[N] u)))) ∧
    (templateCheck N g (qs.map (fun q => readout q (substitution^[N] u))) = true ↔ u = g) ∧
    (listTrace qs (substitution^[N] u)).length = g.length ∧
    (((listTrace qs (substitution^[N] u)).map (fun a => a.1.length)).sum =
      leafAddressSum g + (N/2)*g.length + (N%2)*(composition g).2) ∧
    (((listTrace qs (substitution^[N] u)).map (fun a => a.1.length)).foldr max 0 = delayedRadius N g)
private theorem service_bad : ¬ serviceArena.Law serviceBad := by
  intro h
  have he := (h 0 (.of true) (.of true)).1
  change none = some _ at he
  cases he
private theorem service_dependence : ObservationalDependence serviceSignature serviceActual := by
  intro i
  refine ⟨⟨0,.of true⟩, .of true, .of false, ?_⟩
  intro he
  have hr := congrArg (Option.map (fun z : Hist (fun _ : Address => Reply) × Bool => z.2)) he
  change some true = some false at hr
  cases hr
def serviceFamily : Registration serviceArena (type_of% (@delayed_template_service)) where
  actual := serviceActual
  bridge := Iff.rfl
  variation := ⟨@delayed_template_service, serviceBad, service_bad⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ service_bad
  dependence := service_dependence
def delayed_template_service_registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@delayed_template_service) (Realization serviceSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.DelayedTemplateCertificate.delayed_template_service.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.DelayedTemplateCertificate.serviceFamily
  realizationSource := none
  generated := false
  arena := .source ⟨serviceArena⟩
  objectArena := .source ⟨serviceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source serviceArena ⟨serviceFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize serviceSignature serviceActual.readout serviceActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.DelayedTemplateCertificate
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms serviceFamily
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.DelayedTemplateCertificate
