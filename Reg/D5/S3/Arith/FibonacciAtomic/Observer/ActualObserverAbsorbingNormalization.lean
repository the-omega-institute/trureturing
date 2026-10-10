import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization
open D5.S3.Arith.FibonacciAtomic.ActualFiniteObserverAbsentElimination
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address)
open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization
universe u
abbrev membershipSignature : Signature where
  Params := Nat
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def membershipActual : Realization membershipSignature :=
  realize membershipSignature (fun _ N U => U ∈ allowedSources N) (fun e => nomatch e)

abbrev membershipArena : Arena where
  signature := membershipSignature
  Law R := ∀ (N : Nat) (U : Source), R.readout () N U ↔ Allowed N U

abbrev sourceSetSignature : Signature where
  Params := Unit
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Finset Source
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def sourceSetActual : Realization sourceSetSignature :=
  realize sourceSetSignature (fun _ _ N => allowedSources N) (fun e => nomatch e)

abbrev sourceSetArena : Arena where
  signature := sourceSetSignature
  Law R := ∀ (N : Nat), 1 ≤ N → (R.readout () () N).Nonempty

structure FeeContext where
  Carrier : Type u
  finite : Fintype Carrier
  observer : @Observer Carrier finite
  tau : Address → ℝ

abbrev feeSignature : Signature where
  Params := FeeContext.{u}
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def feeActual : Realization feeSignature.{u} :=
  realize feeSignature (fun _ p U => @Fee p.Carrier p.finite p.observer p.tau U)
    (fun e => nomatch e)

abbrev feeArena : Arena where
  signature := feeSignature.{u}
  Law R := ∀ {E : Type u} [Fintype E] (M : Observer E) (tau : Address → ℝ) (U : Source)
    {t : RawHistory} {f : E} {b : Bool}, Run M U M.e0 t f b →
      R.readout () ⟨E, inferInstance, M, tau⟩ U = charge tau t

abbrev maximumArena : Arena where
  signature := feeSignature.{u}
  Law R := ∀ {E : Type u} [Fintype E] (N : Nat) (positive : 1 ≤ N)
    (M : Observer E) (tau : Address → ℝ),
    (∀ U, Allowed N U → R.readout () ⟨E, inferInstance, M, tau⟩ U ≤ maxFee N M tau) ∧
    ∃ U, Allowed N U ∧ maxFee N M tau = R.readout () ⟨E, inferInstance, M, tau⟩ U

theorem membership_bridge : (type_of% (@allowedSources_exact)) ↔ membershipArena.Law membershipActual := Iff.rfl
theorem sourceSet_bridge : (type_of% (@allowedSources_nonempty)) ↔ sourceSetArena.Law sourceSetActual := Iff.rfl
theorem fee_bridge : (type_of% (@fee_run.{u})) ↔ feeArena.{u}.Law feeActual.{u} := Iff.rfl
theorem maximum_bridge : (type_of% (@maximum_exact.{u})) ↔ maximumArena.{u}.Law feeActual.{u} := Iff.rfl

theorem membership_actual_law : membershipArena.Law membershipActual := allowedSources_exact
theorem sourceSet_actual_law : sourceSetArena.Law sourceSetActual := allowedSources_nonempty
theorem fee_actual_law : feeArena.{u}.Law feeActual.{u} := @fee_run.{u}
theorem maximum_actual_law : maximumArena.{u}.Law feeActual.{u} := @maximum_exact.{u}

#print axioms membership_bridge
#print axioms sourceSet_bridge
#print axioms fee_bridge
#print axioms maximum_bridge

def membershipRejected : Realization membershipSignature :=
  realize membershipSignature (fun _ _ _ => False) (fun e => nomatch e)

theorem membership_rejected_law : ¬ membershipArena.Law membershipRejected := by
  intro h
  exact (h 1 (.of true)).mpr (by exact Nat.le_refl 1)

noncomputable def membershipProof : Registration membershipArena (type_of% (@allowedSources_exact)) where
  actual := membershipActual
  bridge := membership_bridge
  variation := ⟨membership_actual_law, membershipRejected, membership_rejected_law⟩
  sensitivity := ⟨fun i => ⟨membershipRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, membership_rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨1, .of true, .mul (.of true) (.of true), ?_⟩
    intro equal
    change ((.of true : Source) ∈ allowedSources 1) =
      ((.mul (.of true) (.of true) : Source) ∈ allowedSources 1) at equal
    have yes : (.of true : Source) ∈ allowedSources 1 :=
      (allowedSources_exact 1 _).mpr (by exact Nat.le_refl 1)
    have no : ¬ Allowed 1 (.mul (.of true) (.of true)) := by
      change ¬ (2 ≤ 1)
      omega
    exact no ((allowedSources_exact 1 _).mp (equal ▸ yes))

def sourceSetRejected : Realization sourceSetSignature :=
  realize sourceSetSignature (fun _ _ _ => ∅) (fun e => nomatch e)

theorem sourceSet_rejected_law : ¬ sourceSetArena.Law sourceSetRejected := by
  intro h
  exact Finset.not_nonempty_empty (h 1 (by omega))

noncomputable def sourceSetProof : Registration sourceSetArena (type_of% (@allowedSources_nonempty)) where
  actual := sourceSetActual
  bridge := sourceSet_bridge
  variation := ⟨sourceSet_actual_law, sourceSetRejected, sourceSet_rejected_law⟩
  sensitivity := ⟨fun i => ⟨sourceSetRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, sourceSet_rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro equal
    change allowedSources 0 = allowedSources 1 at equal
    have yes : (.of true : Source) ∈ allowedSources 1 :=
      (allowedSources_exact 1 _).mpr (by exact Nat.le_refl 1)
    have impossible : Allowed 0 (.of true) :=
      (allowedSources_exact 0 _).mp (equal.symm ▸ yes)
    exact (show ¬ Allowed 0 (.of true) by change ¬ (1 ≤ 0); omega) impossible

abbrev feeWitness : @Observer (ULift.{u} (Fin 3)) inferInstance where
  e0 := ⟨0⟩
  action e := if e.down = 0 then .inl [] else if e.down = 1 then .inl [false] else .inr false
  transition e y := if e.down = 0 then
    if y = .alpha then ⟨2⟩ else ⟨1⟩ else ⟨2⟩
  decoder _ := []
  decoded_nodup _ := List.nodup_nil

theorem feeWitness_short : Run feeWitness.{u} (.of true) feeWitness.e0
    [⟨[], .alpha⟩] ⟨2⟩ false := by
  exact Run.query (by rfl) (Run.halt (by decide))

theorem feeWitness_long : Run feeWitness.{u} (.of false) feeWitness.e0
    [⟨[], .beta⟩, ⟨[false], .absent⟩] ⟨2⟩ false := by
  exact Run.query (by rfl) (Run.query (by decide) (Run.halt (by decide)))

theorem fee_dependence : ObservationalDependence feeSignature.{u} feeActual.{u} := by
  intro i
  refine ⟨⟨ULift.{u} (Fin 3), inferInstance, feeWitness, fun _ => 1⟩,
    .of true, .of false, ?_⟩
  change Fee feeWitness (fun _ => 1) (.of true) ≠ Fee feeWitness (fun _ => 1) (.of false)
  rw [fee_run _ _ _ feeWitness_short, fee_run _ _ _ feeWitness_long]
  norm_num [charge, D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition.paid]

noncomputable def feeRejected : Realization feeSignature.{u} :=
  realize feeSignature (fun i p U => feeActual.readout i p U + 1) (fun e => nomatch e)

theorem fee_rejected_law : ¬ feeArena.{u}.Law feeRejected.{u} := by
  intro h
  have bad := h feeWitness (fun _ => 1) (.of true) feeWitness_short
  change Fee feeWitness (fun _ => 1) (.of true) + 1 = _ at bad
  rw [fee_run _ _ _ feeWitness_short] at bad
  linarith

theorem maximum_rejected_law : ¬ maximumArena.{u}.Law feeRejected.{u} := by
  intro h
  obtain ⟨U, allowed, attained⟩ := (maximum_exact 1 (by omega) feeWitness.{u} (fun _ => 1)).2
  have bad := (h 1 (by omega) feeWitness (fun _ => 1)).1 U allowed
  change Fee feeWitness (fun _ => 1) U + 1 ≤ _ at bad
  rw [attained] at bad
  linarith

noncomputable def feeProof : Registration feeArena.{u} (type_of% (@fee_run.{u})) where
  actual := feeActual
  bridge := fee_bridge
  variation := ⟨fee_actual_law, feeRejected, fee_rejected_law⟩
  sensitivity := ⟨fun i => ⟨feeRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, fee_rejected_law⟩,
    fun i => nomatch i⟩
  dependence := fee_dependence

noncomputable def maximumProof : Registration maximumArena.{u} (type_of% (@maximum_exact.{u})) where
  actual := feeActual
  bridge := maximum_bridge
  variation := ⟨maximum_actual_law, feeRejected, maximum_rejected_law⟩
  sensitivity := ⟨fun i => ⟨feeRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, maximum_rejected_law⟩,
    fun i => nomatch i⟩
  dependence := fee_dependence

#print axioms membershipProof
#print axioms sourceSetProof
#print axioms feeProof
#print axioms maximumProof


abbrev observedMembershipSignature : Signature where
  Params := Nat
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def observedMembershipActual : Realization observedMembershipSignature := by
  classical
  exact realize observedMembershipSignature (fun _ N U => decide (U ∈ allowedSources N))
    (fun e => nomatch e)

abbrev observedMembershipArena : Arena where
  signature := observedMembershipSignature
  Law R := ∀ (N : Nat) (U : Source), R.readout () N U = true ↔ Allowed N U

def observedMembershipRejected : Realization observedMembershipSignature :=
  realize observedMembershipSignature (fun _ _ _ => false) (fun e => nomatch e)

theorem observedMembership_bridge : (type_of% (@allowedSources_exact)) ↔
    observedMembershipArena.Law observedMembershipActual := by
  classical
  constructor
  · intro h N U
    constructor
    · intro yes; exact (h N U).mp (of_decide_eq_true yes)
    · intro yes; exact decide_eq_true ((h N U).mpr yes)
  · intro h N U
    constructor
    · intro yes; exact (h N U).mp (decide_eq_true yes)
    · intro yes; exact of_decide_eq_true ((h N U).mpr yes)

theorem observedMembership_rejected : ¬ observedMembershipArena.Law observedMembershipRejected := by
  intro h
  have bad := (h 1 (.of true)).mpr (show Allowed 1 (.of true) from Nat.le_refl 1)
  cases bad

noncomputable def observedMembershipProof : Registration observedMembershipArena
    (type_of% (@allowedSources_exact)) where
  actual := observedMembershipActual
  bridge := observedMembership_bridge
  variation := ⟨observedMembership_bridge.mp allowedSources_exact,
    observedMembershipRejected, observedMembership_rejected⟩
  sensitivity := ⟨fun i => ⟨observedMembershipRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, observedMembership_rejected⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨1, .of true, .mul (.of true) (.of true), ?_⟩
    intro equal
    have law := observedMembership_bridge.mp allowedSources_exact
    have yes := (law 1 (.of true)).mpr (show Allowed 1 (.of true) from Nat.le_refl 1)
    have impossible := (law 1 (.mul (.of true) (.of true))).mp (equal ▸ yes)
    change 2 ≤ 1 at impossible
    omega

#print axioms observedMembershipProof


abbrev chargeSignature : Signature where
  Params := Address → ℝ
  State _ := RawHistory
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def chargeActual : Realization chargeSignature :=
  realize chargeSignature (fun _ tau t => charge tau t) (fun e => nomatch e)

abbrev chargeArena : Arena where
  signature := chargeSignature
  Law R := ∀ {E : Type u} [Fintype E] (M : Observer E) (tau : Address → ℝ) (U : Source)
    {t : RawHistory} {f : E} {b : Bool}, Run M U M.e0 t f b →
      Fee M tau U = R.readout () tau t

noncomputable def chargeRejected : Realization chargeSignature :=
  realize chargeSignature (fun _ tau t => charge tau t + 1) (fun e => nomatch e)

theorem charge_rejected : ¬ chargeArena.{u}.Law chargeRejected := by
  intro h
  have bad := h feeWitness.{u} (fun _ => 1) (.of true) feeWitness_short
  rw [fee_run _ _ _ feeWitness_short] at bad
  change charge (fun _ => 1) [⟨[], .alpha⟩] = charge (fun _ => 1) [⟨[], .alpha⟩] + 1 at bad
  linarith

noncomputable def chargeProof : Registration chargeArena.{u} (type_of% (@fee_run.{u})) where
  actual := chargeActual
  bridge := Iff.rfl
  variation := ⟨@fee_run.{u}, chargeRejected, charge_rejected⟩
  sensitivity := ⟨fun i => ⟨chargeRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, charge_rejected⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨fun _ => 1, [], [⟨[], .alpha⟩], ?_⟩
    change charge (fun _ => 1) [] ≠ charge (fun _ => 1) [⟨[], .alpha⟩]
    norm_num [charge, D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition.paid]

#print axioms chargeProof









noncomputable def allowedSources_exact_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization.allowedSources_exact) (Realization observedMembershipArena.signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization.allowedSources_exact
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization.observedMembershipProof
  realizationSource := none
  generated := false
  arena := .source ⟨observedMembershipArena⟩
  objectArena := .source ⟨observedMembershipArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source observedMembershipArena ⟨observedMembershipProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize observedMembershipArena.signature observedMembershipActual.readout observedMembershipActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms allowedSources_exact_registration


noncomputable def allowedSources_nonempty_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization.allowedSources_nonempty) (Realization sourceSetArena.signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization.allowedSources_nonempty
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization.sourceSetProof
  realizationSource := none
  generated := false
  arena := .source ⟨sourceSetArena⟩
  objectArena := .source ⟨sourceSetArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceSetArena ⟨sourceSetProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sourceSetArena.signature sourceSetActual.readout sourceSetActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms allowedSources_nonempty_registration


noncomputable def fee_run_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization.fee_run.{u}) (Realization chargeArena.{u}.signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization.fee_run
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization.chargeProof
  realizationSource := none
  generated := false
  arena := .source ⟨chargeArena.{u}⟩
  objectArena := .source ⟨chargeArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source chargeArena.{u} ⟨chargeProof.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize chargeArena.{u}.signature chargeActual.readout chargeActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization
    definition := none
    coordinates := #[3]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms fee_run_registration


noncomputable def maximum_exact_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization.maximum_exact.{u}) (Realization maximumArena.{u}.signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization.maximum_exact
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization.maximumProof
  realizationSource := none
  generated := false
  arena := .source ⟨maximumArena⟩
  objectArena := .source ⟨maximumArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source maximumArena ⟨maximumProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize maximumArena.signature feeActual.readout feeActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization
    definition := none
    coordinates := #[0, 1, 4, 5]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "body", "body", "fn", "arg"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms maximum_exact_registration

#print axioms _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization.allowedSources_exact
#print axioms _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization.allowedSources_nonempty
#print axioms _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization.fee_run
#print axioms _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization.maximum_exact

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization.Exports
universe u
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.ActualFiniteObserverAbsentElimination
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source composition)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev compositionSignature : Signature where
  Params := Unit
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat × Nat
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev compositionActual : Realization compositionSignature :=
  realize compositionSignature (fun _ _ U => composition U) (fun e => nomatch e)

abbrev compositionArena : Arena where
  signature := compositionSignature
  Law R := ∀ T : Source, (R.readout () () T).1 + (R.readout () () T).2 = T.length

theorem compositionBridge : (type_of% (@composition_total)) ↔ compositionArena.Law compositionActual := Iff.rfl
theorem compositionLaw : compositionArena.Law compositionActual := @composition_total

structure StepContext where
  Carrier : Type u
  finite : Fintype Carrier
  observer : @Observer Carrier finite
  source : Source

abbrev stepSignature : Signature where
  Params := StepContext.{u}
  State p := p.Carrier
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.Carrier
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev stepActual : Realization stepSignature.{u} :=
  realize stepSignature (fun _ p e => @sourceStep p.Carrier p.finite p.observer p.source e)
    (fun e => nomatch e)

abbrev orbitArena : Arena where
  signature := stepSignature.{u}
  Law R := ∀ {E : Type u} [Fintype E] (M : Observer E) (U : Source)
    {e f : E} {t : RawHistory} {b : Bool}, Run M U e t f b →
      (R.readout () ⟨E, inferInstance, M, U⟩)^[t.length] e = f ∧
      M.action f = .inr b ∧
      ∀ i < t.length, ∃ q, M.action
        ((R.readout () ⟨E, inferInstance, M, U⟩)^[i] e) = .inl q

theorem orbitBridge : (type_of% (@run_orbit.{u})) ↔ orbitArena.{u}.Law stepActual.{u} := Iff.rfl
theorem orbitLaw : orbitArena.{u}.Law stepActual.{u} := @run_orbit.{u}

structure ObserverContext where
  Carrier : Type u
  finite : Fintype Carrier

abbrev observerSignature : Signature where
  Params := ObserverContext.{u}
  State p := @Observer p.Carrier p.finite
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := @Observer p.Carrier p.finite
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev observerActual : Realization observerSignature.{u} :=
  realize observerSignature (fun _ _ M => M) (fun e => nomatch e)

abbrev lengthArena : Arena where
  signature := observerSignature.{u}
  Law R := ∀ {E : Type u} [Fintype E] (M : Observer E) (U : Source)
    {e f : E} {t : RawHistory} {b : Bool},
    Run (R.readout () ⟨E, inferInstance⟩ M) U e t f b → t.length < Fintype.card E

theorem lengthBridge : (type_of% (@run_length_bound.{u})) ↔ lengthArena.{u}.Law observerActual.{u} := Iff.rfl
theorem lengthLaw : lengthArena.{u}.Law observerActual.{u} := @run_length_bound.{u}


end Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization.Exports
