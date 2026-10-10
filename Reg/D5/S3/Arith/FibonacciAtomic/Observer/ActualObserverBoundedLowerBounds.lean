import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverBoundedLowerBounds
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverBoundedLowerBounds

universe u
open _root_.D5.S3.Arith.FibonacciAtomic
open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply paid leaves Positive)
open ActualFiniteObserverAbsentElimination
open Observer.ActualObserverAbsorbingNormalization (Fee)
open Observer.ActualObserverBoundedLowerBounds
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

structure Context where
  Carrier : Type u
  finite : Fintype Carrier
  observer : @Observer Carrier finite

abbrev signature : Signature where
  Params := Context.{u}
  State _ := RawHistory
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Finset RawHistory
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature.{u} :=
  realize signature (fun _ p t => @cachedVisits p.Carrier p.finite p.observer t)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {E : Type u} [Fintype E] (N : Nat) (M : Observer E), Admissible N M →
    (∀ U : Source, Allowed N U → Positive U →
      ∀ {t : RawHistory} {f : E} {b : Bool}, Run M U M.e0 t f b →
        (leaves U).toFinset ⊆ paid t ∧ U.length + 1 ≤ Fintype.card E ∧
        ∀ tau : Address → ℝ, (∀ q, 0 ≤ tau q) →
          (∑ q ∈ (leaves U).toFinset, tau q) ≤ Fee M tau U) ∧
    (∀ U : Source, Allowed N U →
      ∀ {t : RawHistory} {f : E} {b : Bool}, Run M U M.e0 t f b →
        paid (M.decoder f) = paid t ∧
        (R.readout () ⟨E, inferInstance, M⟩ t).card = (paid t).card + 1 ∧
        ∀ i ≤ t.length, ActualPrefix M U (historyState M (t.take i)) (t.take i)) ∧
    (0 < (positiveSources N).card → (positiveSources N).card + 2 ≤ Fintype.card E)

theorem bridge : (type_of% (@bounded_cache_control_lower_bounds.{u})) ↔
    arena.{u}.Law actual.{u} := Iff.rfl

theorem actual_law : arena.{u}.Law actual.{u} := @bounded_cache_control_lower_bounds.{u}

private def negativeObserver : Observer (ULift.{u} Unit) where
  e0 := ⟨()⟩
  action _ := .inr false
  transition e _ := e
  decoder _ := []
  decoded_nodup _ := by simp

private theorem negative_admissible : Admissible 1 negativeObserver.{u} := by
  refine ⟨le_rfl, ?_, ?_, ?_⟩
  · intro U _
    refine ⟨rfl, ?_⟩
    intro e h _
    refine ⟨by simp [CacheTruth, negativeObserver], ?_⟩
    intro q row
    cases row
  · intro U allowed
    refine ⟨[], ⟨()⟩, false, Run.halt rfl, ?_⟩
    have neg : ¬ Positive U := by
      intro h
      obtain ⟨s, hs⟩ := h
      have bound := ActualImageSevenLeafSeparation.minimum s
      change 3 ≤ (GenealogicalFiberTransport.substitution^[3] s).length at bound
      rw [hs] at bound
      change U.length ≤ 1 at allowed
      omega
    simp only [Bool.false_eq_true, false_iff]
    exact neg
  · intro h k _
    rfl

noncomputable def bad : Realization signature.{u} :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

theorem bad_law : ¬ arena.{u}.Law bad.{u} := by
  intro law
  have allowed : Allowed 1 (.of false) := le_rfl
  have run : Run negativeObserver (.of false) negativeObserver.e0 [] negativeObserver.e0 false :=
    Run.halt rfl
  have count := (law 1 negativeObserver negative_admissible).2.1 (.of false) allowed run
  simpa [bad, realize, paid] using count.2.1

theorem variation : Variation arena.{u} actual.{u} := ⟨actual_law, bad, bad_law⟩

theorem sensitivity : Sensitivity arena.{u} actual.{u} := by
  constructor
  · intro i
    refine ⟨bad, ?_, ?_, bad_law⟩
    · intro j different
      exact (different (Subsingleton.elim j i)).elim
    · funext e
      cases e
  · intro e
    cases e

private def varyingObserver : Observer (ULift.{u} Bool) where
  e0 := ⟨false⟩
  action _ := .inl []
  transition _ _ := ⟨true⟩
  decoder e := if e.down then [⟨[], Reply.alpha⟩] else []
  decoded_nodup e := by cases e with | up b => cases b <;> simp

theorem dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro i
  refine ⟨⟨ULift.{u} Bool, inferInstance, varyingObserver⟩, [], [⟨[], Reply.alpha⟩], ?_⟩
  intro same
  change cachedVisits varyingObserver [] =
    cachedVisits varyingObserver [⟨[], Reply.alpha⟩] at same
  have member : ([⟨[], Reply.alpha⟩] : RawHistory) ∈
      cachedVisits varyingObserver [⟨[], Reply.alpha⟩] := by
    apply Finset.mem_image.mpr
    refine ⟨1, by simp, ?_⟩
    rfl
  have missing : ([⟨[], Reply.alpha⟩] : RawHistory) ∉ cachedVisits varyingObserver [] := by
    simp [cachedVisits, historyState, responseState, varyingObserver]
  exact missing (same.symm ▸ member)

noncomputable def family : Registration arena.{u}
    (type_of% (@bounded_cache_control_lower_bounds.{u})) where
  actual := actual
  bridge := bridge
  variation := variation
  sensitivity := sensitivity
  dependence := dependence

noncomputable def registration : Contract.Registration.{_, _, _, 0, 0, 0, u+1, 0, 0, 0, 0, 0}
    (@bounded_cache_control_lower_bounds.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverBoundedLowerBounds.unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverBoundedLowerBounds.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(True.intro : True)⟩ True.intro
  readout := some (realize signature actual.readout actual.anchor)
  variation := .evidence ⟨(True.intro : True)⟩ True.intro
  sensitivity := .evidence ⟨(True.intro : True)⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverBoundedLowerBounds
    definition := none
    coordinates := #[0, 1, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := some ⟨arena, ⟨family⟩⟩
  options := #[] }

#print axioms family
#print axioms registration

abbrev spectrumArena : Arena where
  signature := signature.{u}
  Law R := ∀ {E : Type u} [Fintype E] (M : Observer E) (U : Source), Legal M U →
    ∀ {e : E} {h : RawHistory}, ActualPrefix M U e h →
      paid (M.decoder e) = paid h ∧
      (R.readout () ⟨E, inferInstance, M⟩ h).card = (paid h).card + 1 ∧
      ∀ c ∈ R.readout () ⟨E, inferInstance, M⟩ h, paid c ⊆ paid h

theorem spectrum_bridge : (type_of% (@prefix_cache_spectrum.{u})) ↔
    spectrumArena.{u}.Law actual.{u} := Iff.rfl

theorem spectrum_law : spectrumArena.{u}.Law actual.{u} := @prefix_cache_spectrum.{u}

theorem spectrum_bad : ¬ spectrumArena.{u}.Law bad.{u} := by
  intro law
  have count := law negativeObserver (.of false)
    (negative_admissible.legal (.of false) le_rfl) ActualPrefix.initial
  simpa [bad, realize, paid] using count.2.1

theorem spectrum_variation : Variation spectrumArena.{u} actual.{u} :=
  ⟨spectrum_law, bad, spectrum_bad⟩

theorem spectrum_sensitivity : Sensitivity spectrumArena.{u} actual.{u} := by
  constructor
  · intro i
    refine ⟨bad, ?_, ?_, spectrum_bad⟩
    · intro j different
      exact (different (Subsingleton.elim j i)).elim
    · funext e
      cases e
  · intro e
    cases e

noncomputable def spectrumFamily : Registration spectrumArena.{u}
    (type_of% (@prefix_cache_spectrum.{u})) where
  actual := actual
  bridge := spectrum_bridge
  variation := spectrum_variation
  sensitivity := spectrum_sensitivity
  dependence := dependence

#print axioms spectrum_bridge
#print axioms spectrum_law
#print axioms spectrumFamily

noncomputable def spectrumRegistration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, u+1, 0, 0, 0, 0, 0}
    (@prefix_cache_spectrum.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverBoundedLowerBounds.spectrumUnit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverBoundedLowerBounds.spectrumFamily
  realizationSource := none
  generated := false
  arena := .source ⟨spectrumArena.{u}⟩
  objectArena := .source ⟨spectrumArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source spectrumArena.{u} ⟨spectrumFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(True.intro : True)⟩ True.intro
  readout := some (realize signature.{u} actual.{u}.readout actual.{u}.anchor)
  variation := .evidence ⟨(True.intro : True)⟩ True.intro
  sensitivity := .evidence ⟨(True.intro : True)⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverBoundedLowerBounds
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms spectrumRegistration

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverBoundedLowerBounds
