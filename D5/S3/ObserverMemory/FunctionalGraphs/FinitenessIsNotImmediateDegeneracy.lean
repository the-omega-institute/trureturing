/- GID: D5/S3/ObserverMemory/FunctionalGraphs/FinitenessIsNotImmediateDegeneracy
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/FunctionalGraphs/FinitenessIsNotImmediateDegeneracy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite maps cycle; periods and transients are unbounded, with empty cases audited. -/
/- Library-search audit trail (2026-08-25):
   * Exact repository hit `finite_orbit_and_readout_eventually_periodic` supplies the finite-orbit
     conclusion from pinned Mathlib's pigeonhole theorem; it is imported and applied directly.
   * The requested functional-graph module is imported, so its canonical `PeriodicCore`,
     `periodicCoreSubspace`, and `transientSubspace` remain the sole repository definitions.
   * Exact pinned-Mathlib hits `ZMod.addOrderOf_one`, `add_left_iterate_apply`,
     `Function.minimalPeriod`, and `Nat.succ_iterate` provide the countermodel calculations.
   * Two local `smart_search.sh` queries found no stronger package theorem. Loogle and LeanSearch
     executables and LSP tools were unavailable, so they supplied no search conclusion. -/

import D5.S3.ObserverMemory.FunctionalGraphs.FiniteFunctionalGraphFittingDecomposition
import D5.S3.ObserverMemory.Prediction.FiniteOrbitPeriodBound
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.ZMod.Basic

namespace D5.S3.ObserverMemory.FunctionalGraphs.FinitenessIsNotImmediateDegeneracy

open D5.S3.ObserverMemory.InverseLimits.IdentityFuturePastGap
open D5.S3.ObserverMemory.Prediction.FiniteOrbitPeriodBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- An orbit eventually enters the canonical periodic core. -/
def EventuallyEntersPeriodicCore {Y : Type*} (tau : Y -> Y) (initial : Y) : Prop :=
  exists entry : Nat, (tau^[entry]) initial ∈ Function.periodicPts tau

/-- The exact transient length is the first time at which the orbit enters the periodic core. -/
def HasTransientLength {Y : Type*} (tau : Y -> Y) (initial : Y) (length : Nat) : Prop :=
  (forall t : Nat, t < length ->
    (tau^[t]) initial ∉ Function.periodicPts tau) /\
  (tau^[length]) initial ∈ Function.periodicPts tau

/-- The first `window` orbit states are pairwise distinct. -/
def InitialOrbitInjective {Y : Type*}
    (tau : Y -> Y) (initial : Y) (window : Nat) : Prop :=
  Function.Injective (fun t : Fin window => (tau^[t.val]) initial)

/-- Values taken by a readout on the canonical periodic core. -/
def periodicReadoutValues {Y B : Type*} (tau : Y -> Y) (q : Y -> B) : Set B :=
  Set.range (fun point : PeriodicCore tau => q point.1)

/-- Addition by one on a cyclic carrier. -/
def cyclicShift (n : Nat) : ZMod n -> ZMod n :=
  fun state => 1 + state

/-- The finite countdown update, with zero as its unique periodic state. -/
def countdownMap {n : Nat} (state : Fin (n + 1)) : Fin (n + 1) :=
  ⟨state.val - 1, lt_of_le_of_lt (Nat.sub_le state.val 1) state.isLt⟩

private theorem finite_enters_periodic_core
    {Y : Type*} [Finite Y] (tau : Y -> Y) (initial : Y) :
    EventuallyEntersPeriodicCore tau initial := by
  letI := Fintype.ofFinite Y
  obtain ⟨entry, period, hperiod, _, htail⟩ :=
    finite_orbit_and_readout_eventually_periodic
      tau (fun _ : Y => Unit.unit) initial
  refine ⟨entry, Function.mk_mem_periodicPts hperiod ?_⟩
  have hstate := (htail entry (le_refl entry)).1
  change (tau^[period]) ((tau^[entry]) initial) = (tau^[entry]) initial
  rw [<- Function.iterate_add_apply, Nat.add_comm]
  exact hstate

private theorem cyclic_shift_minimal_period (n : Nat) :
    Function.minimalPeriod (cyclicShift (n + 1)) (0 : ZMod (n + 1)) = n + 1 := by
  change addOrderOf (1 : ZMod (n + 1)) = n + 1
  exact ZMod.addOrderOf_one (n + 1)

private theorem cyclic_shift_initial_orbit_injective (n : Nat) :
    InitialOrbitInjective (cyclicShift (n + 1)) (0 : ZMod (n + 1)) n := by
  intro i j hij
  have hcast : (i.val : ZMod (n + 1)) = (j.val : ZMod (n + 1)) := by
    change ((1 + ·)^[i.val]) 0 = ((1 + ·)^[j.val]) 0 at hij
    simpa only [add_left_iterate_apply, add_zero, nsmul_one] using hij
  have hi : i.val < n + 1 := i.isLt.trans (Nat.lt_succ_self n)
  have hj : j.val < n + 1 := j.isLt.trans (Nat.lt_succ_self n)
  have hval := congrArg ZMod.val hcast
  rw [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] at hval
  exact Fin.ext hval

private theorem countdown_iterate_val {n : Nat} (t : Nat) (state : Fin (n + 1)) :
    ((countdownMap^[t]) state).val = state.val - t := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      change ((countdownMap^[t]) state).val - 1 = state.val - (t + 1)
      rw [ih]
      omega

private theorem countdown_mem_periodicPts_iff {n : Nat} (state : Fin (n + 1)) :
    state ∈ Function.periodicPts (@countdownMap n) <-> state = 0 := by
  constructor
  · rintro ⟨period, hperiod, hfixed⟩
    have hval := congrArg Fin.val hfixed
    rw [countdown_iterate_val] at hval
    apply Fin.ext
    simp only [Fin.val_zero]
    omega
  · rintro rfl
    exact Function.mk_mem_periodicPts Nat.one_pos rfl

private theorem period_lengths_are_unbounded :
    forall N : Nat,
      exists (Y : Type) (_ : Fintype Y) (tau : Y -> Y) (initial : Y),
        N < Function.minimalPeriod tau initial := by
  intro N
  refine ⟨ZMod (N + 1), inferInstance, cyclicShift (N + 1), 0, ?_⟩
  rw [cyclic_shift_minimal_period]
  exact Nat.lt_succ_self N

private theorem transient_lengths_are_unbounded :
    forall N : Nat,
      exists (Y : Type) (_ : Fintype Y) (tau : Y -> Y) (initial : Y)
        (length : Nat),
        N < length /\ HasTransientLength tau initial length := by
  intro N
  refine ⟨Fin (N + 2), inferInstance, countdownMap, Fin.last (N + 1),
    N + 1, Nat.lt_succ_self N, ?_⟩
  constructor
  · intro t ht
    rw [countdown_mem_periodicPts_iff]
    intro hzero
    have hval := congrArg Fin.val hzero
    rw [countdown_iterate_val] at hval
    simp only [Fin.val_last, Fin.val_zero] at hval
    omega
  · rw [countdown_mem_periodicPts_iff]
    apply Fin.ext
    rw [countdown_iterate_val]
    simp

private theorem no_fixed_window_forces_repetition :
    forall N : Nat,
      exists (Y : Type) (_ : Fintype Y) (tau : Y -> Y) (initial : Y),
        InitialOrbitInjective tau initial N /\
          EventuallyEntersPeriodicCore tau initial := by
  intro N
  refine ⟨ZMod (N + 1), inferInstance, cyclicShift (N + 1), 0,
    cyclic_shift_initial_orbit_injective N, ?_⟩
  exact finite_enters_periodic_core (cyclicShift (N + 1)) 0

/- The source does not define semantic quality. We use the requested honest fallback:
readout richness is the cardinality of `periodicReadoutValues`. The two finite systems below
have identical dynamics and hence equivalent periodic cores and equal minimal periods, while
their readout ranges have different cardinalities. No quality axiom is introduced. -/
/-- Periodic structure alone does not determine the richness of an attached readout. -/
theorem periodic_structure_does_not_determine_readout_richness :
    exists (tauLow tauHigh : Bool -> Bool) (qLow qHigh : Bool -> Bool),
      Nonempty (PeriodicCore tauLow ≃ PeriodicCore tauHigh) /\
      Function.minimalPeriod tauLow false =
        Function.minimalPeriod tauHigh false /\
      Nat.card (periodicReadoutValues tauLow qLow) <
        Nat.card (periodicReadoutValues tauHigh qHigh) := by
  refine ⟨id, id, fun _ => false, id, ⟨Equiv.refl _⟩, rfl, ?_⟩
  have hLow :
      periodicReadoutValues id (fun _ : Bool => false) = {false} := by
    apply Set.Subset.antisymm
    · rintro value ⟨point, rfl⟩
      simp
    · intro value hvalue
      have hfalse : value = false := Set.mem_singleton_iff.mp hvalue
      subst value
      refine ⟨⟨false, Function.mk_mem_periodicPts Nat.one_pos ?_⟩, rfl⟩
      exact Function.is_periodic_id 1 false
  have hHigh :
      periodicReadoutValues (id : Bool -> Bool) id = (Set.univ : Set Bool) := by
    apply Set.eq_univ_of_forall
    intro value
    refine ⟨⟨value, Function.mk_mem_periodicPts Nat.one_pos ?_⟩, rfl⟩
    exact Function.is_periodic_id 1 value
  rw [hLow, hHigh]
  simp

#print axioms periodic_structure_does_not_determine_readout_richness

/-- The finiteness assumption is necessary: the successor orbit on naturals never enters a
periodic core. -/
theorem finiteness_is_necessary :
    ¬EventuallyEntersPeriodicCore Nat.succ 0 := by
  rintro ⟨entry, period, hperiod, hfixed⟩
  change
    (Nat.succ^[period]) ((Nat.succ^[entry]) 0) =
      (Nat.succ^[entry]) 0 at hfixed
  simp [Nat.succ_iterate] at hfixed
  omega

#print axioms finiteness_is_necessary

/-- Every finite orbit enters its periodic core, while exact periods and exact transient lengths
are unbounded and no fixed initial window must already contain a repetition. -/
theorem finiteness_is_not_immediate_degeneracy :
    (forall (Y : Type) (_ : Finite Y) (tau : Y -> Y) (initial : Y),
      EventuallyEntersPeriodicCore tau initial) /\
    (forall N : Nat,
      exists (Y : Type) (_ : Fintype Y) (tau : Y -> Y) (initial : Y),
        N < Function.minimalPeriod tau initial) /\
    (forall N : Nat,
      exists (Y : Type) (_ : Fintype Y) (tau : Y -> Y) (initial : Y)
        (length : Nat),
        N < length /\ HasTransientLength tau initial length) /\
    (forall N : Nat,
      exists (Y : Type) (_ : Fintype Y) (tau : Y -> Y) (initial : Y),
        InitialOrbitInjective tau initial N /\
          EventuallyEntersPeriodicCore tau initial) := by
  refine ⟨?_, period_lengths_are_unbounded,
    transient_lengths_are_unbounded, no_fixed_window_forces_repetition⟩
  intro Y inst tau initial
  letI := inst
  exact finite_enters_periodic_core tau initial

#print axioms finiteness_is_not_immediate_degeneracy

-- Degenerate-case audit: the empty carrier has no point whose orbit could violate the claim.
example :
    forall (tau : Empty -> Empty) (initial : Empty),
      EventuallyEntersPeriodicCore tau initial := by
  intro _ initial
  exact initial.elim

-- A singleton identity system is periodic immediately, including transient length zero.
example : EventuallyEntersPeriodicCore (id : Unit -> Unit) () :=
  finite_enters_periodic_core id ()

example : HasTransientLength (id : Unit -> Unit) () 0 := by
  constructor
  · intro t ht
    omega
  · exact Function.mk_mem_periodicPts Nat.one_pos (Function.is_periodic_id 1 ())

-- Constant and identity maps are admitted rather than excluded by unnecessary hypotheses.
example : EventuallyEntersPeriodicCore (fun _ : Bool => false) true :=
  finite_enters_periodic_core (fun _ : Bool => false) true

example : EventuallyEntersPeriodicCore (id : Bool -> Bool) false :=
  finite_enters_periodic_core id false

-- A zero-length observation window is vacuously repetition-free.
example {Y : Type*} (tau : Y -> Y) (initial : Y) :
    InitialOrbitInjective tau initial 0 := by
  intro index
  exact Fin.elim0 index

end D5.S3.ObserverMemory.FunctionalGraphs.FinitenessIsNotImmediateDegeneracy
