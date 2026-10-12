import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout
open _root_.D5.S3.Arith.FibonacciAtomic
open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open ActualLeafHistoryRigidity (subtree)
open Observer.DelayedOriginalReadout
open _root_.D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open _root_.D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Hist execute)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev clockSignature := Reg.Support.SingleDependentReadout.signature
  (Nat) (fun _ => Source) (fun _ => Nat)
def clockActual : Realization clockSignature :=
  realize clockSignature (fun _ p u => rightClock (substitution^[p] u)) (fun e => nomatch e)
def clockBad : Realization clockSignature :=
  realize clockSignature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev clockArena : Arena where
  signature := clockSignature
  Law R := ∀ (N : Nat) (u : Source), R.readout () N u = rightClock u + N
private theorem clock_bad : ¬ clockArena.Law clockBad := by
  intro h
  have he := h 0 (.of true)
  change 1 = 0 at he
  cases he
private theorem clock_dependence : ObservationalDependence clockSignature clockActual := by
  intro i
  refine ⟨0, .of true, .of false, ?_⟩
  change (0 : Nat) ≠ 1
  decide
def clockFamily : Registration clockArena (type_of% (@right_clock_iterate)) where
  actual := clockActual
  bridge := Iff.rfl
  variation := ⟨@right_clock_iterate, clockBad, clock_bad⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ clock_bad
  dependence := clock_dependence
def right_clock_iterate_registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@right_clock_iterate) (Realization clockSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout.right_clock_iterate.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout.clockFamily
  realizationSource := none
  generated := false
  arena := .source ⟨clockArena⟩
  objectArena := .source ⟨clockArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source clockArena ⟨clockFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize clockSignature clockActual.readout clockActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev spineSignature := Reg.Support.SingleDependentReadout.signature
  (Nat) (fun _ => Source) (fun _ => Reply)
def spineActual : Realization spineSignature :=
  realize spineSignature (fun _ p u => readout (rights p) u) (fun e => nomatch e)
def spineBad : Realization spineSignature :=
  realize spineSignature (fun _ _ _ => .alpha) (fun e => nomatch e)
abbrev spineArena : Arena where
  signature := spineSignature
  Law R := ∀ (s : Nat) (u : Source),
    (R.readout () s u = .absent ↔ rightClock u < 2*s) ∧
    (readout (rights s) u = .alpha ↔ rightClock u = 2*s) ∧
    (readout (rights s) u = .beta ↔ rightClock u = 2*s+1) ∧
    (readout (rights s) u = .branch ↔ 2*s+2 ≤ rightClock u)
private theorem spine_bad : ¬ spineArena.Law spineBad := by
  intro h
  have he := (h 1 (.of true)).1.mpr (by decide)
  change Reply.alpha = .absent at he
  cases he
private theorem spine_dependence : ObservationalDependence spineSignature spineActual := by
  intro i
  refine ⟨0, .of true, .of false, ?_⟩
  change Reply.alpha ≠ .beta
  decide
def spineFamily : Registration spineArena (type_of% (@right_clock_readout)) where
  actual := spineActual
  bridge := Iff.rfl
  variation := ⟨@right_clock_readout, spineBad, spine_bad⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ spine_bad
  dependence := spine_dependence
def right_clock_readout_registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@right_clock_readout) (Realization spineSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout.right_clock_readout.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout.spineFamily
  realizationSource := none
  generated := false
  arena := .source ⟨spineArena⟩
  objectArena := .source ⟨spineArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source spineArena ⟨spineFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize spineSignature spineActual.readout spineActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev addressSignature := Reg.Support.SingleDependentReadout.signature
  (Σ _ : Nat, Address) (fun _ => Source) (fun _ => Option Source)
def addressActual : Realization addressSignature :=
  realize addressSignature (fun _ p u => subtree p.2 (substitution^[p.1] u)) (fun e => nomatch e)
def addressBad : Realization addressSignature :=
  realize addressSignature (fun _ _ _ => none) (fun e => nomatch e)
abbrev addressArena : Arena where
  signature := addressSignature
  Law R := ∀ (N : Nat) (p : Address) (u : Source),
    (∀ x, subtree p u = some x → ∃ y,
      R.readout () ⟨N,p⟩ u = some y ∧ rightClock y = rightClock x + N) ∧
    (subtree p u = none → ∀ y, subtree p (substitution^[N] u) = some y → rightClock y ≤ N)
private theorem address_bad : ¬ addressArena.Law addressBad := by
  intro h
  obtain ⟨y, hy, _⟩ := (h 0 [] (.of true)).1 (.of true) rfl
  change none = some y at hy
  cases hy
private theorem address_dependence : ObservationalDependence addressSignature addressActual := by
  intro i
  refine ⟨⟨0,[]⟩, .of true, .of false, ?_⟩
  change some (FreeMagma.of true) ≠ some (FreeMagma.of false)
  intro he
  cases he
def addressFamily : Registration addressArena (type_of% (@address_clock_bounds)) where
  actual := addressActual
  bridge := Iff.rfl
  variation := ⟨@address_clock_bounds, addressBad, address_bad⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ address_bad
  dependence := address_dependence
def address_clock_bounds_registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@address_clock_bounds) (Realization addressSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout.address_clock_bounds.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout.addressFamily
  realizationSource := none
  generated := false
  arena := .source ⟨addressArena⟩
  objectArena := .source ⟨addressArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source addressArena ⟨addressFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize addressSignature addressActual.readout addressActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "body", "body", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev guardSignature := Reg.Support.SingleDependentReadout.signature
  (Σ _ : Nat, Σ _ : Address, Bool) (fun _ => Source) (fun _ => Reply)
def guardActual : Realization guardSignature :=
  realize guardSignature (fun _ p u => readout (p.2.1 ++ rights (p.1/2+1)) (substitution^[p.1] u)) (fun e => nomatch e)
def guardBad : Realization guardSignature :=
  realize guardSignature (fun _ _ _ => .alpha) (fun e => nomatch e)
abbrev guardArena : Arena where
  signature := guardSignature
  Law R := ∀ (N : Nat) (a : Address) (d : Bool) (u : Source),
    guardAccept N (R.readout () ⟨N,a,d⟩ u) = true ↔ readout (a ++ [d]) u ≠ .absent
private theorem guard_bad : ¬ guardArena.Law guardBad := by
  intro h
  have he := (h 0 [] false (.of true)).mp rfl
  exact he rfl
private theorem guard_dependence : ObservationalDependence guardSignature guardActual := by
  intro i
  refine ⟨⟨0,[],false⟩, .of true, .mul (.of true) (.of true), ?_⟩
  change Reply.absent ≠ .alpha
  decide
def guardFamily : Registration guardArena (type_of% (@original_presence_guard)) where
  actual := guardActual
  bridge := Iff.rfl
  variation := ⟨@original_presence_guard, guardBad, guard_bad⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ guard_bad
  dependence := guard_dependence
def original_presence_guard_registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_presence_guard) (Realization guardSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout.original_presence_guard.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout.guardFamily
  realizationSource := none
  generated := false
  arena := .source ⟨guardArena⟩
  objectArena := .source ⟨guardArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source guardArena ⟨guardFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize guardSignature guardActual.readout guardActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev decoderSignature := Reg.Support.SingleDependentReadout.signature
  (Σ _ : Nat, Address) (fun _ => Source) (fun _ => Reply)
def decoderActual : Realization decoderSignature :=
  realize decoderSignature (fun _ p u => originalDecode p.1 p.2 ((originalQueries p.1 p.2).map (fun q => readout q (substitution^[p.1] u)))) (fun e => nomatch e)
def decoderBad : Realization decoderSignature :=
  realize decoderSignature (fun _ _ _ => .absent) (fun e => nomatch e)
abbrev decoderArena : Arena where
  signature := decoderSignature
  Law R := ∀ (N : Nat) (p : Address) (u : Source), R.readout () ⟨N,p⟩ u = readout p u
private theorem decoder_bad : ¬ decoderArena.Law decoderBad := by
  intro h
  have he := h 0 [] (.of true)
  change Reply.absent = .alpha at he
  cases he
private theorem decoder_dependence : ObservationalDependence decoderSignature decoderActual := by
  intro i
  refine ⟨⟨0,[]⟩, .of true, .of false, ?_⟩
  change Reply.alpha ≠ .beta
  decide
def decoderFamily : Registration decoderArena (type_of% (@original_decoder_correct)) where
  actual := decoderActual
  bridge := Iff.rfl
  variation := ⟨@original_decoder_correct, decoderBad, decoder_bad⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ decoder_bad
  dependence := decoder_dependence
def original_decoder_correct_registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_decoder_correct) (Realization decoderSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout.original_decoder_correct.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout.decoderFamily
  realizationSource := none
  generated := false
  arena := .source ⟨decoderArena⟩
  objectArena := .source ⟨decoderArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source decoderArena ⟨decoderFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize decoderSignature decoderActual.readout decoderActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev chainSignature := Reg.Support.SingleDependentReadout.signature
  (List Address) (fun _ => Source) (fun _ => Hist (fun _ : Address => Reply))
def chainActual : Realization chainSignature :=
  realize chainSignature (fun _ p u => listTrace p u) (fun e => nomatch e)
def chainBad : Realization chainSignature :=
  realize chainSignature (fun _ _ _ => []) (fun e => nomatch e)
abbrev chainArena : Arena where
  signature := chainSignature
  Law R := ∀ {L : Type} (qs : List Address) (finish : Hist (fun _ : Address => Reply) → L) (u : Source),
    runPassiveProtocol readout (queryChain qs) u = R.readout () qs u ∧
    execute readout (listController qs finish) (qs.length+1) [] u =
      some (listTrace qs u, finish (listTrace qs u)) ∧
    (listTrace qs u).map Sigma.fst = qs ∧ (listTrace qs u).length = qs.length
private theorem chain_bad : ¬ chainArena.Law chainBad := by
  intro h
  have he := (h (L := Bool) [[]] (fun _ => false) (.of true)).1
  change [(⟨[], Reply.alpha⟩ : Sigma (fun _ : Address => Reply))] = [] at he
  cases he
private theorem chain_dependence : ObservationalDependence chainSignature chainActual := by
  intro i
  refine ⟨[[]], .of true, .of false, ?_⟩
  intro he
  have hr := congrArg (fun h : Hist (fun _ : Address => Reply) => h.map Sigma.snd) he
  change [Reply.alpha] = [Reply.beta] at hr
  cases hr
def chainFamily : Registration chainArena (type_of% (@fixed_list_execution)) where
  actual := chainActual
  bridge := Iff.rfl
  variation := ⟨@fixed_list_execution, chainBad, chain_bad⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ chain_bad
  dependence := chain_dependence
def fixed_list_execution_registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@fixed_list_execution) (Realization chainSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout.fixed_list_execution.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout.chainFamily
  realizationSource := none
  generated := false
  arena := .source ⟨chainArena⟩
  objectArena := .source ⟨chainArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source chainArena ⟨chainFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize chainSignature chainActual.readout chainActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev serviceSignature := Reg.Support.SingleDependentReadout.signature
  (Σ _ : Nat, Address) (fun _ => Source) (fun _ => Option (Hist (fun _ : Address => Reply) × Reply))
def serviceActual : Realization serviceSignature :=
  realize serviceSignature (fun _ p u => execute readout (listController (originalQueries p.1 p.2) (fun h => originalDecode p.1 p.2 (h.map Sigma.snd))) ((originalQueries p.1 p.2).length+1) [] (substitution^[p.1] u)) (fun e => nomatch e)
def serviceBad : Realization serviceSignature :=
  realize serviceSignature (fun _ _ _ => none) (fun e => nomatch e)
abbrev serviceArena : Arena where
  signature := serviceSignature
  Law R := ∀ (N : Nat) (p : Address) (u : Source),
    let qs := originalQueries N p
    let finish := fun h : Hist (fun _ : Address => Reply) => originalDecode N p (h.map Sigma.snd)
    R.readout () ⟨N,p⟩ u = some (listTrace qs (substitution^[N] u), readout p u) ∧
    (listTrace qs (substitution^[N] u)).length ≤ 2 ∧
    (∀ q ∈ qs, q.length ≤ p.length + halfCeil N) ∧
    ((N = 0 ∨ p = []) → qs.length = 1)
private theorem service_bad : ¬ serviceArena.Law serviceBad := by
  intro h
  have he := (h 0 [] (.of true)).1
  change none = some _ at he
  cases he
private theorem service_dependence : ObservationalDependence serviceSignature serviceActual := by
  intro i
  refine ⟨⟨0,[]⟩, .of true, .of false, ?_⟩
  intro he
  have hr := congrArg (Option.map (fun z : Hist (fun _ : Address => Reply) × Reply => z.2)) he
  change some Reply.alpha = some Reply.beta at hr
  cases hr
def serviceFamily : Registration serviceArena (type_of% (@original_decoder_service)) where
  actual := serviceActual
  bridge := Iff.rfl
  variation := ⟨@original_decoder_service, serviceBad, service_bad⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ service_bad
  dependence := service_dependence
def original_decoder_service_registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_decoder_service) (Realization serviceSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout.original_decoder_service.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout.serviceFamily
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
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout
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
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout
