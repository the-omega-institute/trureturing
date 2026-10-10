import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler
open D5.S3.Arith.FibonacciAtomic.Observer.ActualAcquisitionCacheFiber
open D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization
open D5.S3.Arith.FibonacciAtomic.ActualFiniteObserverAbsentElimination
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition
open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.Arith.FibonacciAtomic.ActualCoarseReadoutHistory (kappa_hist)
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler

abbrev Budget := {N : Nat // 1 ≤ N}

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
  realize countSignature (fun _ _ N => Fintype.card (PureState N)) (fun e => nomatch e)

abbrev countArena : Arena where
  signature := countSignature
  Law R := ∀ N, R.readout () () N = nominalCard N

abbrev traceSignature : Signature where
  Params := Address
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Address
  Anchor := Empty
  finiteAnchor := inferInstance

def traceActual : Realization traceSignature :=
  realize traceSignature (fun _ u U => (acquisitionTrace u U).map Sigma.fst)
    (fun e => nomatch e)

abbrev traceArena : Arena where
  signature := traceSignature
  Law R := ∀ (U : Source) (u : Address), R.readout () u U = (nodes U).map (u ++ ·)

abbrev controlSignature : Signature where
  Params := Budget
  State _ := RawHistory
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Sum Address Bool
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def controlActual : Realization controlSignature :=
  realize controlSignature (fun _ p h => historyAction (pureObserver p.val p.property) h)
    (fun e => nomatch e)

abbrev controlArena : Arena where
  signature := controlSignature
  Law R := ∀ (N : Nat) (positive : 1 ≤ N),
    Function.FactorsThrough (R.readout () ⟨N, positive⟩) kappa_hist

abbrev runSignature : Signature where
  Params := Unit
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := RawHistory
  Anchor := Empty
  finiteAnchor := inferInstance

def runActual : Realization runSignature :=
  realize runSignature (fun _ _ U => acquisitionTrace [] U) (fun e => nomatch e)

abbrev runArena : Arena where
  signature := runSignature
  Law R := ∀ (N : Nat) (positive : 1 ≤ N) (U : Source), Allowed N U →
    ∃ f, Run (pureObserver N positive) U (pureObserver N positive).e0
      (R.readout () () U) f (finiteDecision U)

abbrev cacheSignature : Signature where
  Params := Budget
  State p := PureState p.val
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := RawHistory
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def cacheActual : Realization cacheSignature :=
  realize cacheSignature (fun _ p e => (pureObserver p.val p.property).decoder e)
    (fun e => nomatch e)

abbrev cacheArena : Arena where
  signature := cacheSignature
  Law R := ∀ (N : Nat) (positive : 1 ≤ N) (U : Source), Allowed N U →
    ∀ {e : PureState N} {h : RawHistory}, ActualPrefix (pureObserver N positive) U e h →
      h.IsPrefix (acquisitionTrace [] U) ∧ R.readout () ⟨N, positive⟩ e = h ∧ CacheTruth h U

abbrev observerSignature : Signature where
  Params := Budget
  State _ := Unit
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Observer (PureState p.val)
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def observerActual : Realization observerSignature :=
  realize observerSignature (fun _ p _ => pureObserver p.val p.property)
    (fun e => nomatch e)

abbrev admissibilityArena : Arena where
  signature := observerSignature
  Law R := ∀ (N : Nat) (positive : 1 ≤ N), Admissible N (R.readout () ⟨N, positive⟩ ())

abbrev feeSignature : Signature where
  Params := Budget × (Address → ℝ)
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def feeActual : Realization feeSignature :=
  realize feeSignature (fun _ p U => Fee (pureObserver p.1.val p.1.property) p.2 U)
    (fun e => nomatch e)

abbrev feeArena : Arena where
  signature := feeSignature
  Law R := ∀ (N : Nat) (positive : 1 ≤ N) (tau : Address → ℝ) (U : Source),
    Allowed N U → R.readout () (⟨N, positive⟩, tau) U = ∑ q ∈ (nodes U).toFinset, tau q

abbrev priceSignature : Signature where
  Params := Budget × (Address → ℝ)
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def priceActual : Realization priceSignature :=
  realize priceSignature (fun _ p c => J_N p.1.val (pureObserver p.1.val p.1.property) p.2 c)
    (fun e => nomatch e)

abbrev priceArena : Arena where
  signature := priceSignature
  Law R := ∀ (N : Nat) (positive : 1 ≤ N) (tau : Address → ℝ) (c : ℝ),
    R.readout () (⟨N, positive⟩, tau) c = c * (nominalCard N : ℝ) + nodeMax N positive tau ∧
    ∃ U : Source, Allowed N U ∧ nodeMax N positive tau = ∑ q ∈ (nodes U).toFinset, tau q

theorem count_bridge : (type_of% (@pureState_card)) ↔ countArena.Law countActual := Iff.rfl
theorem trace_bridge : (type_of% (@trace_addresses)) ↔ traceArena.Law traceActual := Iff.rfl
theorem control_bridge : (type_of% (@pure_all_history_factorization)) ↔ controlArena.Law controlActual := Iff.rfl
theorem run_bridge : (type_of% (@pure_acquisition_run)) ↔ runArena.Law runActual := Iff.rfl
theorem cache_bridge : (type_of% (@pure_actual_prefix_cache)) ↔ cacheArena.Law cacheActual := Iff.rfl
theorem admissibility_bridge : (type_of% (@pure_admissible)) ↔ admissibilityArena.Law observerActual := Iff.rfl
theorem fee_bridge : (type_of% (@pure_node_fee)) ↔ feeArena.Law feeActual := Iff.rfl
theorem price_bridge : (type_of% (@pure_joint_price)) ↔ priceArena.Law priceActual := Iff.rfl

theorem count_actual_law : countArena.Law countActual := pureState_card
theorem trace_actual_law : traceArena.Law traceActual := trace_addresses
theorem control_actual_law : controlArena.Law controlActual := pure_all_history_factorization
theorem run_actual_law : runArena.Law runActual := pure_acquisition_run
theorem cache_actual_law : cacheArena.Law cacheActual := pure_actual_prefix_cache
theorem admissibility_actual_law : admissibilityArena.Law observerActual := pure_admissible
theorem fee_actual_law : feeArena.Law feeActual := pure_node_fee
theorem price_actual_law : priceArena.Law priceActual := pure_joint_price

theorem observer_no_dependence : ¬ ObservationalDependence observerSignature observerActual := by
  rintro h
  obtain ⟨p, x, y, different⟩ := h ()
  exact different (congrArg (observerActual.readout () p) (Subsingleton.elim x y))

#print axioms count_bridge
#print axioms trace_bridge
#print axioms control_bridge
#print axioms run_bridge
#print axioms cache_bridge
#print axioms admissibility_bridge
#print axioms fee_bridge
#print axioms price_bridge
#print axioms observer_no_dependence

private theorem nominal_positive (N : Nat) : 0 < nominalCard N := by
  unfold nominalCard
  omega

private theorem empty_coarse_mem : [] ∈ coarsePrefixes 1 := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨.of true, (allowedSources_exact 1 _).mpr (by exact Nat.le_refl 1), ?_⟩
  simp

private theorem coarse_zero : coarsePrefixes 0 = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro g member
  obtain ⟨U, allowed, _⟩ := Finset.mem_biUnion.mp member
  have bound : U.length ≤ 0 := (allowedSources_exact 0 U).mp allowed
  have positive := U.length_pos
  omega

def countRejected : Realization countSignature :=
  realize countSignature (fun _ _ _ => 0) (fun e => nomatch e)

theorem count_rejected_law : ¬ countArena.Law countRejected := by
  intro h
  have bad := h 0
  have positive := nominal_positive 0
  change 0 = nominalCard 0 at bad
  omega

noncomputable def countProof : Registration countArena (type_of% (@pureState_card)) where
  actual := countActual
  bridge := count_bridge
  variation := ⟨count_actual_law, countRejected, count_rejected_law⟩
  sensitivity := ⟨fun i => ⟨countRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, count_rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    classical
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change Fintype.card (PureState 0) ≠ Fintype.card (PureState 1)
    rw [pureState_card, pureState_card]
    have lower : 1 ≤ ∑ g ∈ coarsePrefixes 1, 2 ^ noneCount g := by
      have bound : 2 ^ noneCount [] ≤ ∑ g ∈ coarsePrefixes 1, 2 ^ noneCount g :=
        Finset.single_le_sum (f := fun g => (2 : Nat) ^ noneCount g)
          (fun _ _ => Nat.zero_le _) empty_coarse_mem
      have empty_count : 2 ^ noneCount [] = 1 := rfl
      rw [empty_count] at bound
      exact bound
    simp only [nominalCard, coarse_zero, Finset.sum_empty, Nat.add_zero]
    omega

def traceRejected : Realization traceSignature :=
  realize traceSignature (fun _ _ _ => []) (fun e => nomatch e)

theorem trace_rejected_law : ¬ traceArena.Law traceRejected := by
  intro h
  have bad := h (.of true) []
  cases bad

def traceProof : Registration traceArena (type_of% (@trace_addresses)) where
  actual := traceActual
  bridge := trace_bridge
  variation := ⟨trace_actual_law, traceRejected, trace_rejected_law⟩
  sensitivity := ⟨fun i => ⟨traceRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, trace_rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨[], .of true, .mul (.of true) (.of true), ?_⟩
    intro bad
    have lengths := congrArg List.length bad
    cases lengths

noncomputable def controlRejected : Realization controlSignature :=
  realize controlSignature (fun _ _ h =>
    if h = [⟨[], .branch⟩] then .inl [] else .inr false) (fun e => nomatch e)

theorem control_rejected_law : ¬ controlArena.Law controlRejected := by
  intro h
  have bad := h 1 (by omega) (show kappa_hist [⟨[], .branch⟩] =
    kappa_hist [⟨[], .absent⟩] from rfl)
  change (if ([⟨[], .branch⟩] : RawHistory) = [⟨[], .branch⟩] then
      Sum.inl ([] : Address) else Sum.inr false) =
    (if ([⟨[], .absent⟩] : RawHistory) = [⟨[], .branch⟩] then
      Sum.inl ([] : Address) else Sum.inr false) at bad
  simp at bad

noncomputable def controlProof : Registration controlArena (type_of% (@pure_all_history_factorization)) where
  actual := controlActual
  bridge := control_bridge
  variation := ⟨control_actual_law, controlRejected, control_rejected_law⟩
  sensitivity := ⟨fun i => ⟨controlRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, control_rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨1, by omega⟩, [], acquisitionTrace [] (.of true), ?_⟩
    obtain ⟨f, run⟩ := pure_acquisition_run 1 (by omega) (.of true) (by exact Nat.le_refl 1)
    have final := (admissible_run_contract 1 _ (pure_admissible 1 (by omega))
      (.of true) (by exact Nat.le_refl 1) run).2.2.2.1
    change historyAction (pureObserver 1 (by omega)) [] ≠
      historyAction (pureObserver 1 (by omega)) (acquisitionTrace [] (.of true))
    rw [final]
    change Sum.inl ([] : Address) ≠ Sum.inr (finiteDecision (.of true))
    exact Sum.inl_ne_inr

def runRejected : Realization runSignature :=
  realize runSignature (fun _ _ _ => []) (fun e => nomatch e)

theorem run_rejected_law : ¬ runArena.Law runRejected := by
  intro h
  obtain ⟨f, bad⟩ := h 1 (by omega) (.of true) (by exact Nat.le_refl 1)
  obtain ⟨g, good⟩ := pure_acquisition_run 1 (by omega) (.of true) (by exact Nat.le_refl 1)
  have traces := (run_deterministic _ _ bad good).1
  cases traces

def runProof : Registration runArena (type_of% (@pure_acquisition_run)) where
  actual := runActual
  bridge := run_bridge
  variation := ⟨run_actual_law, runRejected, run_rejected_law⟩
  sensitivity := ⟨fun i => ⟨runRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, run_rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), .of true, .of false, ?_⟩
    intro bad
    cases bad

def cacheRejected : Realization cacheSignature :=
  realize cacheSignature (fun _ _ _ => [⟨[], .alpha⟩]) (fun e => nomatch e)

theorem cache_rejected_law : ¬ cacheArena.Law cacheRejected := by
  intro h
  have bad := (h 1 (by omega) (.of true) (by exact Nat.le_refl 1) ActualPrefix.initial).2.1
  cases bad

noncomputable def cacheProof : Registration cacheArena (type_of% (@pure_actual_prefix_cache)) where
  actual := cacheActual
  bridge := cache_bridge
  variation := ⟨cache_actual_law, cacheRejected, cache_rejected_law⟩
  sensitivity := ⟨fun i => ⟨cacheRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, cache_rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    obtain ⟨f, run⟩ := pure_acquisition_run 1 (by omega) (.of true) (by exact Nat.le_refl 1)
    have pref := (run_from_actualPrefix _ _ run ActualPrefix.initial).1
    simp only [List.nil_append] at pref
    have decoded := (pure_actual_prefix_cache 1 (by omega) (.of true)
      (by exact Nat.le_refl 1) pref).2.1
    refine ⟨⟨1, by omega⟩, .inr (), f, ?_⟩
    change [] ≠ (pureObserver 1 (by omega)).decoder f
    rw [decoded]
    simp [acquisitionTrace]

abbrev admissibleSignature : Signature where
  Params := Nat
  State N := Observer (PureState N)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def admissibleActual : Realization admissibleSignature := by
  classical
  exact realize admissibleSignature (fun _ N M => decide (Admissible N M)) (fun e => nomatch e)

abbrev admissibleArena : Arena where
  signature := admissibleSignature
  Law R := ∀ (N : Nat) (positive : 1 ≤ N),
    R.readout () N (pureObserver N positive) = true

theorem admissible_bridge : (type_of% (@pure_admissible)) ↔
    admissibleArena.Law admissibleActual := by
  classical
  constructor
  · intro h N positive
    exact decide_eq_true (h N positive)
  · intro h N positive
    exact of_decide_eq_true (h N positive)

noncomputable def loopingObserver (N : Nat) (positive : 1 ≤ N) : Observer (PureState N) :=
  { pureObserver N positive with action := fun _ => .inl [] }

private theorem looping_no_run (N : Nat) (positive : 1 ≤ N) (U : Source)
    {e f : PureState N} {t : RawHistory} {b : Bool} :
    ¬ Run (loopingObserver N positive) U e t f b := by
  intro run
  induction run with
  | halt row => cases row
  | query _ _ ih => exact ih

theorem looping_not_admissible : ¬ Admissible 1 (loopingObserver 1 (by omega)) := by
  intro h
  obtain ⟨t, f, b, run, _⟩ := h.correct (.of true) (by exact Nat.le_refl 1)
  exact looping_no_run _ _ _ run

def admissibleRejected : Realization admissibleSignature :=
  realize admissibleSignature (fun _ _ _ => false) (fun e => nomatch e)

theorem admissible_rejected_law : ¬ admissibleArena.Law admissibleRejected := by
  intro h
  have bad := h 1 (by omega)
  cases bad

noncomputable def admissibleProof : Registration admissibleArena (type_of% (@pure_admissible)) where
  actual := admissibleActual
  bridge := admissible_bridge
  variation := ⟨admissible_bridge.mp pure_admissible, admissibleRejected, admissible_rejected_law⟩
  sensitivity := ⟨fun i => ⟨admissibleRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, admissible_rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    classical
    intro i
    refine ⟨1, pureObserver 1 (by omega), loopingObserver 1 (by omega), ?_⟩
    intro equal
    have yes : admissibleActual.readout i 1 (pureObserver 1 (by omega)) = true :=
      decide_eq_true (pure_admissible 1 (by omega))
    rw [equal] at yes
    exact looping_not_admissible (of_decide_eq_true yes)

noncomputable def feeRejected : Realization feeSignature :=
  realize feeSignature (fun i p U => feeActual.readout i p U + 1) (fun e => nomatch e)

theorem fee_rejected_law : ¬ feeArena.Law feeRejected := by
  intro h
  have bad := h 1 (by omega) (fun _ => 1) (.of true) (by exact Nat.le_refl 1)
  change Fee (pureObserver 1 (by omega)) (fun _ => 1) (.of true) + 1 = _ at bad
  rw [pure_node_fee 1 (by omega) (fun _ => 1) (.of true) (by exact Nat.le_refl 1)] at bad
  linarith

noncomputable def feeProof : Registration feeArena (type_of% (@pure_node_fee)) where
  actual := feeActual
  bridge := fee_bridge
  variation := ⟨fee_actual_law, feeRejected, fee_rejected_law⟩
  sensitivity := ⟨fun i => ⟨feeRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, fee_rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(⟨2, by omega⟩, fun _ => 1), .of true, .mul (.of true) (.of true), ?_⟩
    change Fee (pureObserver 2 (by omega)) (fun _ => 1) (.of true) ≠
      Fee (pureObserver 2 (by omega)) (fun _ => 1) (.mul (.of true) (.of true))
    rw [pure_node_fee 2 (by omega) _ _ (by exact Nat.le_succ 1),
      pure_node_fee 2 (by omega) _ _ (by exact Nat.le_refl 2)]
    norm_num [nodes]

noncomputable def priceRejected : Realization priceSignature :=
  realize priceSignature (fun i p c => priceActual.readout i p c + 1) (fun e => nomatch e)

theorem price_rejected_law : ¬ priceArena.Law priceRejected := by
  intro h
  have bad := (h 1 (by omega) (fun _ => 0) 0).1
  change J_N 1 (pureObserver 1 (by omega)) (fun _ => 0) 0 + 1 = _ at bad
  rw [(pure_joint_price 1 (by omega) (fun _ => 0) 0).1] at bad
  linarith

noncomputable def priceProof : Registration priceArena (type_of% (@pure_joint_price)) where
  actual := priceActual
  bridge := price_bridge
  variation := ⟨price_actual_law, priceRejected, price_rejected_law⟩
  sensitivity := ⟨fun i => ⟨priceRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, price_rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(⟨1, by omega⟩, fun _ => 0), 0, 1, ?_⟩
    change J_N 1 (pureObserver 1 (by omega)) (fun _ => 0) 0 ≠
      J_N 1 (pureObserver 1 (by omega)) (fun _ => 0) 1
    rw [(pure_joint_price 1 (by omega) (fun _ => 0) 0).1,
      (pure_joint_price 1 (by omega) (fun _ => 0) 1).1]
    have positive : (0 : ℝ) < nominalCard 1 := by exact_mod_cast nominal_positive 1
    intro equal
    linarith

#print axioms countProof
#print axioms traceProof
#print axioms controlProof
#print axioms runProof
#print axioms cacheProof
#print axioms admissibleProof
#print axioms feeProof
#print axioms priceProof

abbrev quotientSignature : Signature where
  Params := Unit
  State _ := RawHistory
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := CoarseHistory
  Anchor := Empty
  finiteAnchor := inferInstance

def quotientActual : Realization quotientSignature :=
  realize quotientSignature (fun _ _ h => kappa_hist h) (fun e => nomatch e)

abbrev quotientArena : Arena where
  signature := quotientSignature
  Law R := ∀ (N : Nat) (positive : 1 ≤ N),
    Function.FactorsThrough (historyAction (pureObserver N positive)) (R.readout () ())

def quotientRejected : Realization quotientSignature :=
  realize quotientSignature (fun _ _ _ => []) (fun e => nomatch e)

theorem quotient_rejected : ¬ quotientArena.Law quotientRejected := by
  intro h
  have bad := h 1 (by omega) (show quotientRejected.readout () () [] =
    quotientRejected.readout () () (acquisitionTrace [] (.of true)) from rfl)
  obtain ⟨f, run⟩ := pure_acquisition_run 1 (by omega) (.of true) (by exact Nat.le_refl 1)
  have final := (admissible_run_contract 1 _ (pure_admissible 1 (by omega))
    (.of true) (by exact Nat.le_refl 1) run).2.2.2.1
  rw [final] at bad
  change Sum.inl ([] : Address) = Sum.inr (finiteDecision (.of true)) at bad
  cases bad

def quotientProof : Registration quotientArena (type_of% (@pure_all_history_factorization)) where
  actual := quotientActual
  bridge := Iff.rfl
  variation := ⟨pure_all_history_factorization, quotientRejected, quotient_rejected⟩
  sensitivity := ⟨fun i => ⟨quotientRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, quotient_rejected⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), [], [⟨[], .alpha⟩], ?_⟩
    intro bad
    cases bad

abbrev nodeSignature : Signature where
  Params := Address → ℝ
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def nodeActual : Realization nodeSignature :=
  realize nodeSignature (fun _ tau U => ∑ q ∈ (nodes U).toFinset, tau q) (fun e => nomatch e)

abbrev nodeArena : Arena where
  signature := nodeSignature
  Law R := ∀ (N : Nat) (positive : 1 ≤ N) (tau : Address → ℝ) (U : Source),
    Allowed N U → Fee (pureObserver N positive) tau U = R.readout () tau U

noncomputable def nodeRejected : Realization nodeSignature :=
  realize nodeSignature (fun i p U => nodeActual.readout i p U + 1) (fun e => nomatch e)

theorem node_rejected : ¬ nodeArena.Law nodeRejected := by
  intro h
  have bad := h 1 (by omega) (fun _ => 1) (.of true) (by exact Nat.le_refl 1)
  rw [pure_node_fee 1 (by omega) (fun _ => 1) (.of true) (by exact Nat.le_refl 1)] at bad
  change (∑ q ∈ (nodes (.of true)).toFinset, (1 : ℝ)) =
    (∑ q ∈ (nodes (.of true)).toFinset, (1 : ℝ)) + 1 at bad
  linarith

noncomputable def nodeProof : Registration nodeArena (type_of% (@pure_node_fee)) where
  actual := nodeActual
  bridge := Iff.rfl
  variation := ⟨pure_node_fee, nodeRejected, node_rejected⟩
  sensitivity := ⟨fun i => ⟨nodeRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, node_rejected⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨fun _ => 1, .of true, .mul (.of true) (.of true), ?_⟩
    change (∑ q ∈ (nodes (.of true)).toFinset, (1 : ℝ)) ≠
      (∑ q ∈ (nodes (.mul (.of true) (.of true))).toFinset, (1 : ℝ))
    norm_num [nodes]

abbrev nominalPriceSignature : Signature where
  Params := Nat
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def nominalPriceActual : Realization nominalPriceSignature :=
  realize nominalPriceSignature (fun _ N c => c * (nominalCard N : ℝ)) (fun e => nomatch e)

abbrev nominalPriceArena : Arena where
  signature := nominalPriceSignature
  Law R := ∀ (N : Nat) (positive : 1 ≤ N) (tau : Address → ℝ) (c : ℝ),
    J_N N (pureObserver N positive) tau c = R.readout () N c + nodeMax N positive tau ∧
    ∃ U : Source, Allowed N U ∧ nodeMax N positive tau = ∑ q ∈ (nodes U).toFinset, tau q

noncomputable def nominalPriceRejected : Realization nominalPriceSignature :=
  realize nominalPriceSignature (fun i N c => nominalPriceActual.readout i N c + 1)
    (fun e => nomatch e)

theorem nominalPrice_rejected : ¬ nominalPriceArena.Law nominalPriceRejected := by
  intro h
  have bad := (h 1 (by omega) (fun _ => 0) 0).1
  rw [(pure_joint_price 1 (by omega) (fun _ => 0) 0).1] at bad
  change 0 * (nominalCard 1 : ℝ) + nodeMax 1 _ (fun _ => 0) =
    (0 * (nominalCard 1 : ℝ) + 1) + nodeMax 1 _ (fun _ => 0) at bad
  linarith

noncomputable def nominalPriceProof : Registration nominalPriceArena (type_of% (@pure_joint_price)) where
  actual := nominalPriceActual
  bridge := Iff.rfl
  variation := ⟨pure_joint_price, nominalPriceRejected, nominalPrice_rejected⟩
  sensitivity := ⟨fun i => ⟨nominalPriceRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, nominalPrice_rejected⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    change 0 * (nominalCard 1 : ℝ) ≠ 1 * (nominalCard 1 : ℝ)
    have positive : (0 : ℝ) < nominalCard 1 := by exact_mod_cast nominal_positive 1
    intro equal
    linarith

#print axioms quotientProof
#print axioms nodeProof
#print axioms nominalPriceProof

noncomputable def pureState_card_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.pureState_card) (Realization countArena.signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.pureState_card
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.countProof
  realizationSource := none
  generated := false
  arena := .source ⟨countArena⟩
  objectArena := .source ⟨countArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source countArena ⟨countProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize countArena.signature countActual.readout countActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms pureState_card_registration

noncomputable def trace_addresses_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.trace_addresses) (Realization traceArena.signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.trace_addresses
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.traceProof
  realizationSource := none
  generated := false
  arena := .source ⟨traceArena⟩
  objectArena := .source ⟨traceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source traceArena ⟨traceProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize traceArena.signature traceActual.readout traceActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler
    definition := none
    coordinates := #[1]
    readouts := #[{ path := #["body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg", "arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms trace_addresses_registration

noncomputable def pure_all_history_factorization_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.pure_all_history_factorization) (Realization quotientArena.signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.pure_all_history_factorization
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.quotientProof
  realizationSource := none
  generated := false
  arena := .source ⟨quotientArena⟩
  objectArena := .source ⟨quotientArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source quotientArena ⟨quotientProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize quotientArena.signature quotientActual.readout quotientActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "arg"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms pure_all_history_factorization_registration

noncomputable def pure_acquisition_run_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.pure_acquisition_run) (Realization runArena.signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.pure_acquisition_run
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.runProof
  realizationSource := none
  generated := false
  arena := .source ⟨runArena⟩
  objectArena := .source ⟨runArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source runArena ⟨runProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize runArena.signature runActual.readout runActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "body", "arg", "body", "fn", "fn", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms pure_acquisition_run_registration

private abbrev cacheTraceArena : Arena where
  signature := runSignature
  Law R := ∀ (N : Nat) (positive : 1 ≤ N) (U : Source), Allowed N U →
    ∀ {e : PureState N} {h : RawHistory}, ActualPrefix (pureObserver N positive) U e h →
      h.IsPrefix (R.readout () () U) ∧ (pureObserver N positive).decoder e = h ∧ CacheTruth h U

private theorem cacheTrace_rejected : ¬ cacheTraceArena.Law runRejected := by
  intro h
  obtain ⟨f, run⟩ := pure_acquisition_run 1 (by omega) (.of true) (by exact Nat.le_refl 1)
  have pref := (run_from_actualPrefix _ _ run ActualPrefix.initial).1
  simp only [List.nil_append] at pref
  have bad := (h 1 (by omega) (.of true) (by exact Nat.le_refl 1) pref).1
  change (acquisitionTrace [] (.of true)).IsPrefix [] at bad
  have empty := List.eq_nil_of_prefix_nil bad
  simp [acquisitionTrace] at empty

private def cacheTraceProof : Registration cacheTraceArena (type_of% (@pure_actual_prefix_cache)) where
  actual := runActual
  bridge := Iff.rfl
  variation := ⟨pure_actual_prefix_cache, runRejected, cacheTrace_rejected⟩
  sensitivity := ⟨fun i => ⟨runRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, cacheTrace_rejected⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), .of true, .of false, ?_⟩
    intro bad
    cases bad

#print axioms cacheTraceProof
#print axioms _root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.pure_actual_prefix_cache

noncomputable def pure_actual_prefix_cache_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.pure_actual_prefix_cache) (Realization cacheTraceArena.signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.pure_actual_prefix_cache
  realizationName := ``cacheTraceProof
  realizationSource := none
  generated := false
  arena := .source ⟨cacheTraceArena⟩
  objectArena := .source ⟨cacheTraceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source cacheTraceArena ⟨cacheTraceProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize cacheTraceArena.signature runActual.readout runActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms pure_actual_prefix_cache_registration

noncomputable def pure_admissible_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.pure_admissible) (Realization admissibleArena.signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.pure_admissible
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.admissibleProof
  realizationSource := none
  generated := false
  arena := .source ⟨admissibleArena⟩
  objectArena := .source ⟨admissibleArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source admissibleArena ⟨admissibleProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize admissibleArena.signature admissibleActual.readout admissibleActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms pure_admissible_registration

noncomputable def pure_node_fee_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.pure_node_fee) (Realization nodeArena.signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.pure_node_fee
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.nodeProof
  realizationSource := none
  generated := false
  arena := .source ⟨nodeArena⟩
  objectArena := .source ⟨nodeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source nodeArena ⟨nodeProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize nodeArena.signature nodeActual.readout nodeActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler
    definition := none
    coordinates := #[2]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms pure_node_fee_registration

noncomputable def pure_joint_price_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.pure_joint_price) (Realization nominalPriceArena.signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.pure_joint_price
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.nominalPriceProof
  realizationSource := none
  generated := false
  arena := .source ⟨nominalPriceArena⟩
  objectArena := .source ⟨nominalPriceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source nominalPriceArena ⟨nominalPriceProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize nominalPriceArena.signature nominalPriceActual.readout nominalPriceActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler
    definition := none
    coordinates := #[0]
    readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms pure_joint_price_registration

namespace NodeDepth

abbrev signature : Signature where
  Params := Source
  State _ := Address
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ _ q => q.length) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (U : Source) (q : Address), q ∈ nodes U →
    R.readout () U q + 1 ≤ U.length

theorem bridge : (type_of% (@nodes_length)) ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual := nodes_length

noncomputable def bad : Realization signature :=
  realize signature (fun _ U _ => U.length) (fun e => nomatch e)

theorem bad_law : ¬ arena.Law bad := by
  intro law
  have impossible := law (.of true) [] (by simp [nodes])
  exact (by decide : ¬ ((1 : Nat) + 1 ≤ 1)) impossible

theorem variation : Variation arena actual := ⟨actual_law, bad, bad_law⟩

theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨bad, ?_, ?_, bad_law⟩
    · intro j different
      exact (different (Subsingleton.elim j i)).elim
    · funext e
      cases e
  · intro e
    cases e

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨.mul (.of true) (.of false), [], [false], ?_⟩
  change (0 : Nat) ≠ 1
  decide

noncomputable def family : Registration arena (type_of% (@nodes_length)) where
  actual := actual
  bridge := bridge
  variation := variation
  sensitivity := sensitivity
  dependence := dependence

noncomputable def registration : LeanInformationAudit.Contract.Registration.{_, _, _,
    0, 0, 0, 0, 0, 0, 0, 0, 0} (@nodes_length) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.NodeDepth.unit
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler.NodeDepth.family
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
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end NodeDepth

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler
