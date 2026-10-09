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

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualPureAcquisitionCompiler
