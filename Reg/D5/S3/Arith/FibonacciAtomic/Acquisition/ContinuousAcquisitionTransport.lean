import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Acquisition.ContinuousAcquisitionTransport
import Reg.Support.DependentFamily

/-! Full original-family registration of continuous operational transport. -/

set_option autoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.Acquisition.ContinuousAcquisitionTransport
open _root_.D5.S3.Arith.FibonacciAtomic.TerminalGcdAcquisitionCost
open _root_.D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.Acquisition.ContinuousAcquisitionTransport
universe u v

abbrev TransportParameters :=
  Σ S : Type u, Σ L : Type v, Σ _P : Controller S L, Σ _H : ℕ, List Event

abbrev transportSignature : Signature where
  Params := TransportParameters.{u,v}
  State _ := ℕ × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Option (Hist (fun _ : List Bool => ℕ) × p.2.1)
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def transportActual : Realization transportSignature.{u,v} :=
  realize transportSignature (fun _ p x =>
    execute (terminalGcd p.2.2.2.1) (selector p.2.2.1) (paidReads p.2.2.2.2 + 1) [] x)
    (fun e => nomatch e)

def transportRejected : Realization transportSignature.{u,v} :=
  realize transportSignature (fun _ _ _ => none) (fun e => nomatch e)

abbrev transportArena : Arena where
  signature := transportSignature.{u,v}
  Law R := ∀ {S : Type u} {L : Type v} (P : Controller S L) (H : ℕ)
    (es : List Event) (v : ℕ × ℕ) (t : S) (y : ℕ × ℕ) (l : L),
    Run P H P.initial v es t y l →
    R.readout () ⟨S, L, P, H, es⟩ v = some (records [] es, l) ∧
    normalize P (replay P (records [] es)) = (t, finalWord [] es) ∧
    y = runWord (finalWord [] es) v ∧
    (records [] es).length = paidReads es ∧
    PublicRun P (P.initial, []) es (t, finalWord [] es) l

private def stopped : Controller (ULift.{u} Unit) (ULift.{v} ℕ) where
  code _ := .halt ⟨0⟩
  initial := ⟨()⟩
  fallback := ⟨0⟩

private theorem transport_rejected_law : ¬ transportArena.{u,v}.Law transportRejected := by
  intro h
  have bad := (h stopped 1 [] (0, 0) ⟨()⟩ (0, 0) ⟨0⟩ (.halt rfl)).1
  change (none : Option (Hist (fun _ : List Bool => ℕ) × ULift.{v} ℕ)) =
    some ([], ⟨0⟩) at bad
  cases bad

private def oneRead : Controller (ULift.{u} (Option ℕ)) (ULift.{v} ℕ) where
  code s := match s.down with
    | none => .read (fun g => ⟨some g⟩)
    | some g => .halt ⟨g⟩
  initial := ⟨none⟩
  fallback := ⟨0⟩

private theorem transport_dependence :
    ObservationalDependence transportSignature.{u,v} transportActual := by
  intro i
  let P := oneRead.{u,v}
  let p : TransportParameters.{u,v} :=
    ⟨ULift (Option ℕ), ULift ℕ, P, 2, [.reply 2]⟩
  refine ⟨p, (0, 0), (1, 1), ?_⟩
  have h0 : Run P 2 P.initial (0, 0) [.reply 2] ⟨some 2⟩ (0, 0) ⟨2⟩ :=
    .read rfl (.halt rfl)
  have h1 : Run P 2 P.initial (1, 1) [.reply 1] ⟨some 1⟩ (1, 1) ⟨1⟩ :=
    .read rfl (.halt rfl)
  have e0 := (continuous_transport P 2 _ (0, 0) _ _ _ h0).1
  have e1 := (continuous_transport P 2 _ (1, 1) _ _ _ h1).1
  change execute (terminalGcd 2) (selector P) 2 [] (0, 0) ≠
    execute (terminalGcd 2) (selector P) 2 [] (1, 1)
  change execute (terminalGcd 2) (selector P) 2 [] (0, 0) = _ at e0
  change execute (terminalGcd 2) (selector P) 2 [] (1, 1) = _ at e1
  rw [e0, e1]
  intro h
  have hh := congrArg (fun z => z.map (fun a => a.2.down)) h
  norm_num at hh

noncomputable def transportEvidence :
    Registration transportArena.{u,v} (type_of% (@continuous_transport.{u,v})) where
  actual := transportActual
  bridge := Iff.rfl
  variation := ⟨continuous_transport, transportRejected, transport_rejected_law⟩
  sensitivity := ⟨fun i => ⟨transportRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, transport_rejected_law⟩,
    fun i => nomatch i⟩
  dependence := transport_dependence

noncomputable def transportRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@continuous_transport.{u,v}) (Realization transportSignature.{u,v}) Type Unit where
  unitName := `continuousTransport
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Acquisition.ContinuousAcquisitionTransport.transportEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨transportArena⟩
  objectArena := .source ⟨transportArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source transportArena ⟨transportEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize transportSignature (fun _ p x =>
    execute (terminalGcd p.2.2.2.1) (selector p.2.2.1) (paidReads p.2.2.2.2 + 1) [] x)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Acquisition.ContinuousAcquisitionTransport
    definition := none
    coordinates := #[0, 1, 2, 3, 4]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev lowerSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def lowerActual : Realization lowerSignature :=
  realize lowerSignature (fun _ _ H => if H = 1 then 0 else 2 * costBound H)
    (fun e => nomatch e)

def lowerRejected : Realization lowerSignature :=
  realize lowerSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev lowerArena : Arena where
  signature := lowerSignature
  Law R := ∀ {S : Type u} (H : ℕ) (hH : 1 ≤ H)
    (P : Controller S (ZMod H × ZMod H)) (J : ℕ),
    (∀ v : ℕ × ℕ, ∃ es t y,
      Run P H P.initial v es t y (residueSource H v) ∧ paidReads es ≤ J) →
    R.readout () () H ≤ J

private theorem lower_rejected_law : ¬ lowerArena.{u}.Law lowerRejected := by
  intro h
  let P : Controller (ULift.{u} Unit) (ZMod 1 × ZMod 1) :=
    ⟨fun _ => .halt 0, ⟨()⟩, 0⟩
  have success : ∀ v : ℕ × ℕ, ∃ es t y,
      Run P 1 P.initial v es t y (residueSource 1 v) ∧ paidReads es ≤ 0 := by
    intro v
    refine ⟨[], ⟨()⟩, v, ?_, by decide⟩
    have hz : residueSource 1 v = 0 := Subsingleton.elim _ _
    rw [hz]
    exact .halt rfl
  have bad := h 1 (by decide) P 0 success
  change 1 ≤ 0 at bad
  exact Nat.not_succ_le_zero 0 bad

noncomputable def lowerEvidence :
    Registration lowerArena.{u} (type_of% (@continuous_acquisition_lower_bound.{u})) where
  actual := lowerActual
  bridge := Iff.rfl
  variation := ⟨continuous_acquisition_lower_bound, lowerRejected, lower_rejected_law⟩
  sensitivity := ⟨fun i => ⟨lowerRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, lower_rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    have hb : costBound 2 = 1 := by
      simp only [costBound, Nat.prime_two.primeFactors, Finset.sup_singleton,
        Nat.prime_two.factorization_self]
    change (if (1 : ℕ) = 1 then 0 else 2 * costBound 1) ≠
      (if (2 : ℕ) = 1 then 0 else 2 * costBound 2)
    simp [hb]

noncomputable def lowerRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@continuous_acquisition_lower_bound.{u}) (Realization lowerSignature) Type Unit where
  unitName := `continuousAcquisitionLowerBound
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Acquisition.ContinuousAcquisitionTransport.lowerEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨lowerArena⟩
  objectArena := .source ⟨lowerArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source lowerArena ⟨lowerEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize lowerSignature
    (fun _ _ H => if H = 1 then 0 else 2 * costBound H) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Acquisition.ContinuousAcquisitionTransport
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms transportEvidence
#print axioms lowerEvidence

end Reg.D5.S3.Arith.FibonacciAtomic.Acquisition.ContinuousAcquisitionTransport
