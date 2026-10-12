import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.ActualExactMarkedTables
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualExactMarkedTables

universe u
open _root_.D5.S3.Arith.FibonacciAtomic
open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply Strategy terminal)
open ActualCoarseReadoutHistory (kappa_hist)
open ActualFiniteObserverAbsentElimination
open Observer.ActualExactMarkedTables
open Observer.ActualExactTraceCompiler
open Observer.ActualExactSupportPruning
open Observer.ActualCompletionPhaseReplay
open Observer.ActualObserverFiniteTable
open Observer.ActualObserverAbsorbingNormalization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound (PassiveProtocol)

abbrev markSignature : Signature where
  Params := Nat
  State m := PhaseLabel m
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ m := PhaseLabel m
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def markActual : Realization markSignature :=
  realize markSignature (fun _ _ label => label) (fun e => nomatch e)

structure CertificateContext where
  Carrier : Type u
  finite : Fintype Carrier
  budget : Nat
  strategy : Strategy

abbrev certificateSignature : Signature where
  Params := CertificateContext.{u}
  State p := @Observer p.Carrier p.finite
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def certificateActual : Realization certificateSignature.{u} :=
  realize certificateSignature
    (fun _ p M => @ExactCertificate p.Carrier p.finite p.budget p.strategy M)
    (fun e => nomatch e)

structure PoolContext where
  budget : Nat
  strategy : Strategy
  count : Nat
  positive : 0 < count

abbrev poolSignature : Signature where
  Params := PoolContext
  State p := Finset (NativeTable (supportWidth (prescribedSupport p.budget p.strategy)) p.count)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Finset (NativeTable (supportWidth (prescribedSupport p.budget p.strategy)) p.count)
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def poolActual : Realization poolSignature :=
  realize poolSignature (fun _ _ pool => pool) (fun e => nomatch e)

abbrev tableSignature : Signature where
  Params := PoolContext
  State p := NativeTable (supportWidth (prescribedSupport p.budget p.strategy)) p.count
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Observer (Fin p.count)
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def tableActual : Realization tableSignature :=
  realize tableSignature (fun _ p T => tableObserver p.positive T) (fun e => nomatch e)

abbrev countSignature : Signature where
  Params := Unit
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def countActual : Realization countSignature :=
  realize countSignature (fun _ _ k => k) (fun e => nomatch e)

abbrev markingArena : Arena where
  signature := markSignature
  Law R := ∀ {E : Type u} [Fintype E] {m : Nat} (F : Fin m → Source)
    (decode : CoarseHistory → Option (Fin m))
    (p : PassiveProtocol Address (fun _ => Option Bool)) (N : Nat) (π : Strategy)
    (M : Observer E) (admissible : Admissible N M) (exact : ExactTraces N π M),
    ∃ mark : E → PhaseMark F decode p N π,
      ∀ U, Allowed N U → ∀ e h, ActualPrefix M U e h →
        R.readout () m (mark e).val = (routePhase F decode p [] (kappa_hist h)).1

theorem marking_bridge : (type_of% (@same_carrier_original_marking.{u})) ↔
    markingArena.{u}.Law markActual := Iff.rfl

theorem marking_law : markingArena.{u}.Law markActual := @same_carrier_original_marking.{u}

#print axioms marking_bridge
#print axioms marking_law

abbrev certificateArena : Arena where
  signature := certificateSignature.{u}
  Law R := ∀ {E : Type u} [Fintype E] (N : Nat) (π : Strategy) (M : Observer E),
    R.readout () ⟨E, inferInstance, N, π⟩ M ↔ Admissible N M ∧ ExactTraces N π M

theorem certificate_bridge : (type_of% (@prescribed_prefix_certificate_iff.{u})) ↔
    certificateArena.{u}.Law certificateActual.{u} := Iff.rfl

theorem certificate_law : certificateArena.{u}.Law certificateActual.{u} := @prescribed_prefix_certificate_iff.{u}

#print axioms certificate_bridge
#print axioms certificate_law

abbrev poolArena : Arena where
  signature := poolSignature
  Law R := ∀ {m : Nat} (F : Fin m → Source)
    (decode : CoarseHistory → Option (Fin m))
    (p : PassiveProtocol Address (fun _ => Option Bool)) (N : Nat) (π : Strategy)
    (n : Nat) (positive : 0 < n)
    (T : NativeTable (supportWidth (prescribedSupport N π)) n),
    T ∈ R.readout () ⟨N, π, n, positive⟩ (rawPool N π n positive) ↔ ∃ mark, (T, mark) ∈ markedPool F decode p N π n positive

theorem pool_bridge : (type_of% (@raw_mem_iff_marked)) ↔
    poolArena.Law poolActual := Iff.rfl

theorem pool_law : poolArena.Law poolActual := @raw_mem_iff_marked

#print axioms pool_bridge
#print axioms pool_law

abbrev coverageArena : Arena where
  signature := tableSignature
  Law R := ∀ {E : Type u} [Fintype E] {m : Nat} (F : Fin m → Source)
    (decode : CoarseHistory → Option (Fin m))
    (p : PassiveProtocol Address (fun _ => Option Bool)) (N : Nat) (π : Strategy)
    (M : Observer E) (mark : E → PhaseLabel m)
    (admissible : Admissible N M) (exact : ExactTraces N π M)
    (original : OriginalMarks F decode p N M mark),
    ∃ (positive : 0 < Fintype.card E) (r : E ≃ Fin (Fintype.card E))
      (T : NativeTable (supportWidth (prescribedSupport N π)) (Fintype.card E))
      (labels : Fin (Fintype.card E) → PhaseMark F decode p N π),
      (T, labels) ∈ markedPool F decode p N π (Fintype.card E) positive ∧
      (∀ U, Allowed N U → ∀ e h,
        ActualPrefix (R.readout () ⟨N, π, Fintype.card E, positive⟩ T) U (r e) h ↔ ActualPrefix M U e h) ∧
      (∀ U, Allowed N U → ∀ e h, ActualPrefix M U e h →
        (R.readout () ⟨N, π, Fintype.card E, positive⟩ T).decoder (r e) = M.decoder e ∧
        (R.readout () ⟨N, π, Fintype.card E, positive⟩ T).action (r e) = M.action e ∧
        (labels (r e)).val = mark e)

theorem coverage_bridge : (type_of% (@marked_competitor_table_coverage.{u})) ↔
    coverageArena.{u}.Law tableActual := Iff.rfl

theorem coverage_law : coverageArena.{u}.Law tableActual := @marked_competitor_table_coverage.{u}

#print axioms coverage_bridge
#print axioms coverage_law

abbrev attainmentArena : Arena where
  signature := countSignature
  Law R := ∀ {m : Nat} (F : Fin m → Source)
    (decode : CoarseHistory → Option (Fin m))
    (p : PassiveProtocol Address (fun _ => Option Bool)) (N : Nat) (π : Strategy)
    (positive : 1 ≤ N)
    (policy : π.policy = fun h => ActualJointResponseCostCore.controllerPolicy
      (ActualCoarseReadoutCompletion.compileRaw F decode p [])
      (ActualCoarseReadoutCompletion.encodeHistory (kappa_hist h))),
    ∃ (k : Nat) (posK : 0 < k)
      (T : NativeTable (supportWidth (prescribedSupport N π)) k)
      (mark : Fin k → PhaseMark F decode p N π),
      k ≤ strategyStateCard N π ∧
      T ∈ rawPool N π k posK ∧ (T, mark) ∈ markedPool F decode p N π k posK ∧
      (∀ {Carrier : Type u} [Fintype Carrier] (M : Observer Carrier),
        Admissible N M → ExactTraces N π M → R.readout () () k ≤ Fintype.card Carrier) ∧
      (∀ U : Source, terminal π U = ActualJointResponseCostCore.controllerOutcome
        (ActualCoarseReadoutCompletion.compileRaw F decode p []) U) ∧
      ∀ (tau : Address → ℝ), (∀ q, 0 ≤ tau q) → ∀ (kappa : ℝ), 0 < kappa →
        J_N N (tableObserver posK T) tau kappa =
          kappa * (k : ℝ) + fixedTraceFee N π positive tau ∧
        (∀ {Carrier : Type u} [Fintype Carrier] (M : Observer Carrier),
          Admissible N M → ExactTraces N π M →
          kappa * (k : ℝ) + fixedTraceFee N π positive tau ≤ J_N N M tau kappa) ∧
        (∀ U, Allowed N U → charge tau (terminal π U).1 ≤ fixedTraceFee N π positive tau) ∧
        ∃ U, Allowed N U ∧ fixedTraceFee N π positive tau = charge tau (terminal π U).1

theorem attainment_bridge : (type_of% (@original_exact_marked_attainment.{u})) ↔
    attainmentArena.{u}.Law countActual := Iff.rfl

theorem attainment_law : attainmentArena.{u}.Law countActual := @original_exact_marked_attainment.{u}

#print axioms attainment_bridge
#print axioms attainment_law

private def emptyFamily : Fin 0 → Source := Fin.elim0
private def noSelection : CoarseHistory → Option (Fin 0) := fun _ => none
private def oneRoute : PassiveProtocol Address (fun _ => Option Bool) :=
  .query [] (fun _ => .stop)

private theorem route_strategy : ∃ π : Strategy,
    Function.FactorsThrough π.policy kappa_hist := by
  obtain ⟨π, _, coarse, _⟩ := ActualCoarseReadoutCompletion.completion_contract 0
    emptyFamily (fun i => Fin.elim0 i) oneRoute noSelection
  exact ⟨π, coarse⟩

private def lifted {E : Type} [Fintype E] (M : Observer E) : Observer (ULift.{u} E) where
  e0 := ⟨M.e0⟩
  action e := M.action e.down
  transition e y := ⟨M.transition e.down y⟩
  decoder e := M.decoder e.down
  decoded_nodup e := M.decoded_nodup e.down

private theorem lifted_prefix_back {E : Type} [Fintype E] (M : Observer E) (U : Source)
    {e : ULift.{u} E} {h : RawHistory} (pref : ActualPrefix (lifted M) U e h) :
    ActualPrefix M U e.down h := by
  induction pref with
  | initial => exact .initial
  | query prior row ih => exact ActualPrefix.query ih row

private theorem lifted_run {E : Type} [Fintype E] (M : Observer E) (U : Source)
    {e f : E} {t : RawHistory} {b : Bool} (run : Run M U e t f b) :
    Run (lifted.{u} M) U ⟨e⟩ t ⟨f⟩ b := by
  induction run with
  | halt row => exact .halt row
  | query row tail ih => exact .query row ih

private theorem lifted_response {E : Type} [Fintype E] (M : Observer E) (e : E) (w : List Reply) :
    responseState (lifted.{u} M) ⟨e⟩ w = ⟨responseState M e w⟩ := by
  induction w generalizing e with
  | nil => rfl
  | cons y w ih =>
    simp only [responseState, List.foldl_cons]
    cases row : M.action e <;> simpa only [responseState, barStep, lifted, row] using ih _

private theorem lifted_admissible {E : Type} [Fintype E] (N : Nat) (M : Observer E)
    (adm : Admissible N M) : Admissible N (lifted.{u} M) := by
  refine ⟨adm.budget_pos, ?_, ?_, ?_⟩
  · intro U allowed
    refine ⟨(adm.legal U allowed).1, ?_⟩
    intro e h pref
    exact (adm.legal U allowed).2 e.down h (lifted_prefix_back M U pref)
  · intro U allowed
    obtain ⟨t, f, b, run, correct⟩ := adm.correct U allowed
    exact ⟨t, ⟨f⟩, b, lifted_run M U run, correct⟩
  · intro h h' same
    have old := adm.coarse same
    change M.action (responseState (lifted M) ⟨M.e0⟩ (h.map Sigma.snd)).down =
      M.action (responseState (lifted M) ⟨M.e0⟩ (h'.map Sigma.snd)).down
    rw [lifted_response, lifted_response]
    exact old

private theorem lifted_exact {E : Type} [Fintype E] (N : Nat) (π : Strategy) (M : Observer E)
    (exact : ExactTraces N π M) : ExactTraces N π (lifted.{u} M) := by
  intro U allowed
  obtain ⟨f, run⟩ := exact U allowed
  exact ⟨⟨f⟩, lifted_run M U run⟩

noncomputable def markBad : Realization markSignature :=
  realize markSignature (fun _ _ _ => .malformed) (fun e => nomatch e)

theorem marking_bad : ¬ markingArena.{u}.Law markBad := by
  intro law
  obtain ⟨π, coarse⟩ := route_strategy
  let B := strategyObserver 1 π (by omega)
  let M := lifted.{u} B
  obtain ⟨mark, marks⟩ := law emptyFamily noSelection oneRoute 1 π M
    (lifted_admissible 1 B (strategy_admissible 1 π (by omega) coarse)) (lifted_exact 1 π B (strategy_exact_run 1 π (by omega) coarse))
  have impossible := marks (.of false) le_rfl M.e0 [] ActualPrefix.initial
  simp [markBad, realize, oneRoute, routePhase, kappa_hist] at impossible

noncomputable def certificateBad : Realization certificateSignature.{u} :=
  realize certificateSignature (fun _ _ _ => True) (fun e => nomatch e)

private def halted (Carrier : Type u) [Fintype Carrier] (e : Carrier) (b : Bool) :
    Observer Carrier where
  e0 := e
  action _ := .inr b
  transition f _ := f
  decoder _ := []
  decoded_nodup _ := by simp

private theorem negative_source : ¬ ActualTreeReadoutAcquisition.Positive (.of false) := by
  rintro ⟨s, equal⟩
  have bound := ActualImageSevenLeafSeparation.minimum s
  change 3 ≤ (GenealogicalFiberTransport.substitution^[3] s).length at bound
  rw [equal] at bound
  contradiction

private theorem initial_not_true {E : Type u} [Fintype E] (N : Nat) (M : Observer E)
    (admissible : Admissible N M) : M.action M.e0 ≠ .inr true := by
  intro row
  obtain ⟨t, f, b, run, correct⟩ := admissible.correct (.of false) admissible.budget_pos
  have bit := (run_deterministic M (.of false) (Run.halt row) run).2.2
  exact negative_source (correct.mp bit.symm)

theorem certificate_bad : ¬ certificateArena.{u}.Law certificateBad.{u} := by
  intro law
  have equivalent := law 0 ActualTreeReadoutAcquisition.fallback
    (halted (ULift.{u} Unit) ⟨()⟩ false)
  have admissible := (equivalent.mp True.intro).1
  have impossible := admissible.budget_pos
  omega

theorem certificate_dependence :
    ObservationalDependence certificateSignature.{u} certificateActual.{u} := by
  intro i
  obtain ⟨π, coarse⟩ := route_strategy
  let B := strategyObserver 1 π (by omega)
  let M := lifted.{u} B
  have adm := lifted_admissible.{u} 1 B (strategy_admissible 1 π (by omega) coarse)
  have ex := lifted_exact.{u} 1 π B (strategy_exact_run 1 π (by omega) coarse)
  let context : CertificateContext.{u} := ⟨ULift.{u} (ExactState (strategyPrefixes 1 π)), inferInstance, 1, π⟩
  refine ⟨context, M, halted _ M.e0 true, ?_⟩
  intro same
  have checked := (prescribed_prefix_certificate_iff 1 π M).mpr ⟨adm, ex⟩
  change ExactCertificate 1 π M = ExactCertificate 1 π (halted _ M.e0 true) at same
  have wrong := (prescribed_prefix_certificate_iff 1 π _).mp (same ▸ checked)
  exact initial_not_true 1 _ wrong.1 rfl

noncomputable def poolBad : Realization poolSignature :=
  realize poolSignature (fun _ _ _ => ∅) (fun e => nomatch e)

theorem pool_bad : ¬ poolArena.Law poolBad := by
  classical
  intro law
  obtain ⟨π, coarse⟩ := route_strategy
  let M := strategyObserver 1 π (by omega)
  obtain ⟨positive, r, T, adm, ex, _, _, requests, caches⟩ :=
    exact_competitor_table_coverage 1 π M (strategy_admissible 1 π (by omega) coarse)
      (strategy_exact_run 1 π (by omega) coarse)
  have raw : T ∈ rawPool 1 π _ positive :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨requests, caches⟩,
      (prescribed_prefix_certificate_iff 1 π _).mpr ⟨adm, ex⟩⟩
  obtain ⟨mark, marked⟩ := (raw_mem_iff_marked emptyFamily noSelection oneRoute 1 π _ positive T).mp raw
  have impossible := (law emptyFamily noSelection oneRoute 1 π _ positive T).mpr ⟨mark, marked⟩
  simpa [poolBad, realize] using impossible

private def simpleTable (W n : Nat) (b : Bool) : NativeTable W n where
  action _ := .inr b
  transition e _ := e
  cache _ := ⟨[], by simp⟩

theorem pool_dependence : ObservationalDependence poolSignature poolActual := by
  intro i
  let context : PoolContext := ⟨1, ActualTreeReadoutAcquisition.fallback, 1, by omega⟩
  let T : NativeTable (supportWidth (prescribedSupport 1 context.strategy)) 1 := simpleTable _ _ false
  refine ⟨context, ∅, {T}, ?_⟩
  simp [poolActual, realize]

noncomputable def tableBad : Realization tableSignature :=
  realize tableSignature (fun _ p _ => halted _ ⟨0, p.positive⟩ true) (fun e => nomatch e)

theorem coverage_bad : ¬ coverageArena.{u}.Law tableBad := by
  intro law
  obtain ⟨π, coarse⟩ := route_strategy
  let B := strategyObserver 1 π (by omega)
  let M := lifted.{u} B
  have adm := lifted_admissible.{u} 1 B (strategy_admissible 1 π (by omega) coarse)
  have ex := lifted_exact.{u} 1 π B (strategy_exact_run 1 π (by omega) coarse)
  obtain ⟨labels, original⟩ := same_carrier_original_marking emptyFamily noSelection oneRoute 1 π M adm ex
  obtain ⟨positive, r, T, marks, _, _, observations⟩ :=
    law emptyFamily noSelection oneRoute 1 π M (fun e => (labels e).val) adm ex original
  have action := (observations (.of false) le_rfl M.e0 [] ActualPrefix.initial).2.1
  exact initial_not_true 1 M adm action.symm

theorem table_dependence : ObservationalDependence tableSignature tableActual := by
  intro i
  let context : PoolContext := ⟨1, ActualTreeReadoutAcquisition.fallback, 1, by omega⟩
  refine ⟨context, simpleTable _ _ false, simpleTable _ _ true, ?_⟩
  intro same
  have actions := congrArg (fun M : Observer (Fin 1) => M.action ⟨0, by omega⟩) same
  cases actions

theorem mark_dependence : ObservationalDependence markSignature markActual := by
  intro i
  exact ⟨0, .route [], .malformed, by simp [markActual, realize]⟩

theorem count_dependence : ObservationalDependence countSignature countActual := by
  intro i
  exact ⟨(), 0, 1, by simp [countActual, realize]⟩

noncomputable def countBad : Realization countSignature :=
  realize countSignature (fun _ _ k => k + 1) (fun e => nomatch e)

theorem attainment_bad : ¬ attainmentArena.{u}.Law countBad := by
  classical
  intro law
  obtain ⟨π, policy, _, _⟩ := ActualCoarseReadoutCompletion.completion_contract 0
    emptyFamily (fun i => Fin.elim0 i) oneRoute noSelection
  obtain ⟨k, positive, T, mark, _, raw, _, least, _⟩ :=
    law emptyFamily noSelection oneRoute 1 π (by omega) policy
  have native := (prescribed_prefix_certificate_iff 1 π _).mp (Finset.mem_filter.mp raw).2.2
  have bound := least (lifted.{u} (tableObserver positive T))
    (lifted_admissible 1 _ native.1) (lifted_exact 1 π _ native.2)
  have impossible : k + 1 ≤ k := by
    simpa only [countBad, realize, Fintype.card_ulift, Fintype.card_fin] using bound
  omega

theorem marking_variation : Variation markingArena.{u} markActual :=
  ⟨marking_law, markBad, marking_bad⟩

theorem marking_sensitivity : Sensitivity markingArena.{u} markActual := by
  constructor
  · intro i
    refine ⟨markBad, ?_, ?_, marking_bad⟩
    · intro j different
      exact (different (Subsingleton.elim j i)).elim
    · funext e
      cases e
  · intro e
    cases e

noncomputable def markingFamily : Registration markingArena.{u}
    (type_of% (@same_carrier_original_marking.{u})) where
  actual := markActual
  bridge := marking_bridge
  variation := marking_variation
  sensitivity := marking_sensitivity
  dependence := mark_dependence

#print axioms markingFamily

theorem certificate_variation : Variation certificateArena.{u} certificateActual.{u} :=
  ⟨certificate_law, certificateBad.{u}, certificate_bad⟩

theorem certificate_sensitivity : Sensitivity certificateArena.{u} certificateActual.{u} := by
  constructor
  · intro i
    refine ⟨certificateBad.{u}, ?_, ?_, certificate_bad⟩
    · intro j different
      exact (different (Subsingleton.elim j i)).elim
    · funext e
      cases e
  · intro e
    cases e

noncomputable def certificateFamily : Registration certificateArena.{u}
    (type_of% (@prescribed_prefix_certificate_iff.{u})) where
  actual := certificateActual.{u}
  bridge := certificate_bridge
  variation := certificate_variation
  sensitivity := certificate_sensitivity
  dependence := certificate_dependence

#print axioms certificateFamily

theorem pool_variation : Variation poolArena poolActual :=
  ⟨pool_law, poolBad, pool_bad⟩

theorem pool_sensitivity : Sensitivity poolArena poolActual := by
  constructor
  · intro i
    refine ⟨poolBad, ?_, ?_, pool_bad⟩
    · intro j different
      exact (different (Subsingleton.elim j i)).elim
    · funext e
      cases e
  · intro e
    cases e

noncomputable def poolFamily : Registration poolArena
    (type_of% (@raw_mem_iff_marked)) where
  actual := poolActual
  bridge := pool_bridge
  variation := pool_variation
  sensitivity := pool_sensitivity
  dependence := pool_dependence

#print axioms poolFamily

theorem coverage_variation : Variation coverageArena.{u} tableActual :=
  ⟨coverage_law, tableBad, coverage_bad⟩

theorem coverage_sensitivity : Sensitivity coverageArena.{u} tableActual := by
  constructor
  · intro i
    refine ⟨tableBad, ?_, ?_, coverage_bad⟩
    · intro j different
      exact (different (Subsingleton.elim j i)).elim
    · funext e
      cases e
  · intro e
    cases e

noncomputable def coverageFamily : Registration coverageArena.{u}
    (type_of% (@marked_competitor_table_coverage.{u})) where
  actual := tableActual
  bridge := coverage_bridge
  variation := coverage_variation
  sensitivity := coverage_sensitivity
  dependence := table_dependence

#print axioms coverageFamily

theorem attainment_variation : Variation attainmentArena.{u} countActual :=
  ⟨attainment_law, countBad, attainment_bad⟩

theorem attainment_sensitivity : Sensitivity attainmentArena.{u} countActual := by
  constructor
  · intro i
    refine ⟨countBad, ?_, ?_, attainment_bad⟩
    · intro j different
      exact (different (Subsingleton.elim j i)).elim
    · funext e
      cases e
  · intro e
    cases e

noncomputable def attainmentFamily : Registration attainmentArena.{u}
    (type_of% (@original_exact_marked_attainment.{u})) where
  actual := countActual
  bridge := attainment_bridge
  variation := attainment_variation
  sensitivity := attainment_sensitivity
  dependence := count_dependence

#print axioms attainmentFamily

noncomputable def markingRegistration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@same_carrier_original_marking.{u}) (Realization markSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualExactMarkedTables.markingUnit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualExactMarkedTables.markingFamily
  realizationSource := none
  generated := false
  arena := .source ⟨markingArena.{u}⟩
  objectArena := .source ⟨markingArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source markingArena.{u} ⟨markingFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(True.intro : True)⟩ True.intro
  readout := some (realize markSignature markActual.readout markActual.anchor)
  variation := .evidence ⟨(True.intro : True)⟩ True.intro
  sensitivity := .evidence ⟨(True.intro : True)⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms markingRegistration

noncomputable def certificateRegistration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, u+1, u, 0, 0, 0, 0}
    (@prescribed_prefix_certificate_iff.{u}) (Realization certificateSignature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualExactMarkedTables.certificateUnit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualExactMarkedTables.certificateFamily
  realizationSource := none
  generated := false
  arena := .source ⟨certificateArena.{u}⟩
  objectArena := .source ⟨certificateArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source certificateArena.{u} ⟨certificateFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(True.intro : True)⟩ True.intro
  readout := some (realize certificateSignature.{u} certificateActual.{u}.readout certificateActual.{u}.anchor)
  variation := .evidence ⟨(True.intro : True)⟩ True.intro
  sensitivity := .evidence ⟨(True.intro : True)⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualExactMarkedTables
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms certificateRegistration

noncomputable def poolRegistration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@raw_mem_iff_marked) (Realization poolSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualExactMarkedTables.poolUnit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualExactMarkedTables.poolFamily
  realizationSource := none
  generated := false
  arena := .source ⟨poolArena⟩
  objectArena := .source ⟨poolArena⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source poolArena ⟨poolFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(True.intro : True)⟩ True.intro
  readout := some (realize poolSignature poolActual.readout poolActual.anchor)
  variation := .evidence ⟨(True.intro : True)⟩ True.intro
  sensitivity := .evidence ⟨(True.intro : True)⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms poolRegistration

noncomputable def coverageRegistration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@marked_competitor_table_coverage.{u}) (Realization tableSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualExactMarkedTables.coverageUnit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualExactMarkedTables.coverageFamily
  realizationSource := none
  generated := false
  arena := .source ⟨coverageArena.{u}⟩
  objectArena := .source ⟨coverageArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source coverageArena.{u} ⟨coverageFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(True.intro : True)⟩ True.intro
  readout := some (realize tableSignature tableActual.readout tableActual.anchor)
  variation := .evidence ⟨(True.intro : True)⟩ True.intro
  sensitivity := .evidence ⟨(True.intro : True)⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms coverageRegistration

noncomputable def attainmentRegistration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@original_exact_marked_attainment.{u}) (Realization countSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualExactMarkedTables.attainmentUnit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualExactMarkedTables.attainmentFamily
  realizationSource := none
  generated := false
  arena := .source ⟨attainmentArena.{u}⟩
  objectArena := .source ⟨attainmentArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source attainmentArena.{u} ⟨attainmentFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(True.intro : True)⟩ True.intro
  readout := some (realize countSignature countActual.readout countActual.anchor)
  variation := .evidence ⟨(True.intro : True)⟩ True.intro
  sensitivity := .evidence ⟨(True.intro : True)⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualExactMarkedTables
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "fn", "arg", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms attainmentRegistration

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualExactMarkedTables
