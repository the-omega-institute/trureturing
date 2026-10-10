/- GID: D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteTable
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Faithful finite native tables covering every normalized bounded observer. -/

import D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Fintype.List
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverFiniteTable

universe u
open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply)
open ActualCoarseReadoutHistory (kappa_hist)
open ActualFiniteObserverAbsentElimination
open ActualObserverAbsorbingNormalization

/-- Literal native words, not equivalence classes of addresses. -/
abbrev BoundedAddress (N : Nat) := {q : Address // q ∈ Q_N N}

instance (N : Nat) : Finite (BoundedAddress N) :=
  (List.finite_length_le Bool (N - 1)).to_subtype

noncomputable instance (N : Nat) : Fintype (BoundedAddress N) := Fintype.ofFinite _

/-- Chronological first-hit caches; distinctness is on addresses, not reports. -/
abbrev NativeCache (N : Nat) :=
  {c : List (BoundedAddress N × Reply) // (c.map Prod.fst).Nodup}

instance (N : Nat) : Finite (NativeCache N) := by
  let embed : NativeCache N → {c : List (BoundedAddress N × Reply) // c.Nodup} :=
    fun c => ⟨c.val, List.Nodup.of_map Prod.fst c.property⟩
  exact Finite.of_injective embed (fun c d h => Subtype.ext
    (congrArg (fun x : {c : List (BoundedAddress N × Reply) // c.Nodup} => x.val) h))

/-- Erasing membership proofs preserves literal words, raw replies and order. -/
def decodeCache {N : Nat} (c : NativeCache N) : RawHistory :=
  c.val.map (fun a => ⟨a.1.val, a.2⟩)

private theorem decodeCache_nodup {N : Nat} (c : NativeCache N) :
    ((decodeCache c).map Sigma.fst).Nodup := by
  simpa only [decodeCache, List.map_map, Function.comp_def] using
    c.property.map (f := Subtype.val) Subtype.val_injective

/-- Complete finite native row tables; the distinguished initial label is zero. -/
structure NativeTable (N n : Nat) where
  action : Fin n → Sum (BoundedAddress N) Bool
  transition : Fin n → Reply → Fin n
  cache : Fin n → NativeCache N

instance (N n : Nat) : Finite (NativeTable N n) := by
  let embed (T : NativeTable N n) := (T.action, T.transition, T.cache)
  apply Finite.of_injective embed
  intro T S equal
  cases T
  cases S
  simpa [embed, Prod.mk.injEq] using equal

noncomputable instance (N n : Nat) : Fintype (NativeTable N n) := Fintype.ofFinite _

/-- A native table is itself an original observer, with all nominal rows priced. -/
def tableObserver {N n : Nat} (positive : 0 < n) (T : NativeTable N n) :
    Observer (Fin n) where
  e0 := ⟨0, positive⟩
  action e := (T.action e).map Subtype.val id
  transition := T.transition
  decoder e := decodeCache (T.cache e)
  decoded_nodup e := decodeCache_nodup (T.cache e)

/-- The finite pool retains exactly the original admissibility predicate.
Membership is a mathematical specification, not a price comparison algorithm. -/
noncomputable def lawfulTables (N n : Nat) (positive : 0 < n) : Finset (NativeTable N n) := by
  classical
  exact Finset.univ.filter (fun T => Admissible N (tableObserver positive T))

variable {E : Type u} [Fintype E]

/-- Relabel every complete configuration, including unreachable ones. -/
def relabel {n : Nat} (M : Observer E) (r : E ≃ Fin n) : Observer (Fin n) where
  e0 := r M.e0
  action e := M.action (r.symm e)
  transition e y := r (M.transition (r.symm e) y)
  decoder e := M.decoder (r.symm e)
  decoded_nodup e := M.decoded_nodup (r.symm e)

private theorem relabel_run {n : Nat} (M : Observer E) (r : E ≃ Fin n) (U : Source)
    {e f : E} {t : RawHistory} {b : Bool} (run : Run M U e t f b) :
    Run (relabel M r) U (r e) t (r f) b := by
  induction run with
  | halt row => exact Run.halt (by simpa [relabel] using row)
  | @query e f q t b row tail ih =>
    have step := Run.query (M := relabel M r) (U := U) (e := r e)
      (q := q) (t := t) (f := r f) (b := b)
      (by simpa [relabel] using row) (by simpa [relabel] using ih)
    simpa [relabel] using step

private theorem relabel_run_back {n : Nat} (M : Observer E) (r : E ≃ Fin n)
    (U : Source) {e f : Fin n} {t : RawHistory} {b : Bool}
    (run : Run (relabel M r) U e t f b) : Run M U (r.symm e) t (r.symm f) b := by
  induction run with
  | halt row => exact Run.halt row
  | query row tail ih =>
    have oldrow : M.action _ = .inl _ := row
    simpa [relabel] using Run.query oldrow (by simpa [relabel] using ih)

private theorem relabel_prefix {n : Nat} (M : Observer E) (r : E ≃ Fin n)
    (U : Source) {e : E} {h : RawHistory} (pref : ActualPrefix M U e h) :
    ActualPrefix (relabel M r) U (r e) h := by
  induction pref with
  | initial => exact ActualPrefix.initial
  | query prior row ih =>
    simpa [relabel] using ActualPrefix.query ih (by simpa [relabel] using row)

private theorem relabel_prefix_back {n : Nat} (M : Observer E) (r : E ≃ Fin n)
    (U : Source) {e : Fin n} {h : RawHistory}
    (pref : ActualPrefix (relabel M r) U e h) : ActualPrefix M U (r.symm e) h := by
  induction pref with
  | initial => simpa [relabel] using (ActualPrefix.initial (M := M) (U := U))
  | query prior row ih =>
    simpa [relabel] using ActualPrefix.query ih row

private theorem relabel_response {n : Nat} (M : Observer E) (r : E ≃ Fin n)
    (e : E) (w : List Reply) :
    responseState (relabel M r) (r e) w = r (responseState M e w) := by
  apply List.foldl_hom r
  intro x y
  simp only [barStep, relabel, Equiv.symm_apply_apply]
  cases M.action x <;> rfl

theorem relabel_admissible {n : Nat} (N : Nat) (M : Observer E)
    (r : E ≃ Fin n) (admissible : Admissible N M) : Admissible N (relabel M r) := by
  refine ⟨admissible.budget_pos, ?_, ?_, ?_⟩
  · intro U allowed
    have legal := admissible.legal U allowed
    refine ⟨by simpa [relabel] using legal.1, ?_⟩
    intro e h pref
    have old := legal.2 (r.symm e) h (relabel_prefix_back M r U pref)
    simpa [relabel] using old
  · intro U allowed
    obtain ⟨t, f, b, run, correct⟩ := admissible.correct U allowed
    exact ⟨t, r f, b, relabel_run M r U run, correct⟩
  · have actions (h : RawHistory) : historyAction (relabel M r) h = historyAction M h := by
      unfold historyAction historyState
      rw [show (relabel M r).e0 = r M.e0 from rfl, relabel_response]
      simp [relabel]
    intro h h' same
    rw [actions h, actions h']
    exact admissible.coarse same

theorem relabel_fee {n : Nat} (M : Observer E) (r : E ≃ Fin n)
    (tau : Address → ℝ) (U : Source) : Fee (relabel M r) tau U = Fee M tau U := by
  classical
  let old : RawHistory → Prop := fun t => ∃ f b, Run M U M.e0 t f b
  let new : RawHistory → Prop := fun t => ∃ f b, Run (relabel M r) U (relabel M r).e0 t f b
  have same : new = old := by
    funext t
    apply propext
    constructor
    · rintro ⟨f, b, run⟩
      exact ⟨r.symm f, b, by simpa [relabel] using relabel_run_back M r U run⟩
    · rintro ⟨f, b, run⟩
      exact ⟨r f, b, relabel_run M r U run⟩
  change (if total : ∃ t, new t then charge tau total.choose else 0) =
    (if total : ∃ t, old t then charge tau total.choose else 0)
  rw [same]

private def packCache (N : Nat) (c : RawHistory) (nodup : (c.map Sigma.fst).Nodup)
    (bounded : ∀ a ∈ c, a.1 ∈ Q_N N) : NativeCache N :=
  ⟨c.attach.map (fun a => (⟨a.val.1, bounded a.val a.property⟩, a.val.2)), by
    apply List.Nodup.of_map Subtype.val
    simpa only [List.map_map, Function.comp_def, List.attach_map_val] using nodup⟩

private theorem decode_packCache (N : Nat) (c : RawHistory)
    (nodup : (c.map Sigma.fst).Nodup) (bounded : ∀ a ∈ c, a.1 ∈ Q_N N) :
    decodeCache (packCache N c nodup bounded) = c := by
  simp [decodeCache, packCache, List.map_map, Function.comp_def]

/-- Any bounded observer has an exactly faithful table on the whole carrier.
No sourcewise termination, correctness or desired optimum is assumed. -/
theorem bounded_table_representation (N : Nat) (M : Observer E)
    (requests : ∀ e q, M.action e = .inl q → q ∈ Q_N N)
    (caches : ∀ e a, a ∈ M.decoder e → a.1 ∈ Q_N N) :
    ∃ (positive : 0 < Fintype.card E) (r : E ≃ Fin (Fintype.card E))
      (T : NativeTable N (Fintype.card E)),
      r M.e0 = ⟨0, positive⟩ ∧ tableObserver positive T = relabel M r := by
  classical
  let : Nonempty E := ⟨M.e0⟩
  have positive : 0 < Fintype.card E := Fintype.card_pos
  let enumeration := Fintype.equivFin E
  let r := enumeration.trans (Equiv.swap (enumeration M.e0) ⟨0, positive⟩)
  have initial : r M.e0 = ⟨0, positive⟩ := Equiv.swap_apply_left _ _
  let T : NativeTable N (Fintype.card E) :=
    { action := fun e => match row : M.action (r.symm e) with
        | .inl q => .inl ⟨q, requests (r.symm e) q row⟩
        | .inr b => .inr b
      transition := fun e y => r (M.transition (r.symm e) y)
      cache := fun e => packCache N (M.decoder (r.symm e))
        (M.decoded_nodup (r.symm e)) (caches (r.symm e)) }
  refine ⟨positive, r, T, initial, ?_⟩
  have actions : (tableObserver positive T).action = (relabel M r).action := by
    funext e
    change (T.action e).map Subtype.val id = M.action (r.symm e)
    dsimp only [T]
    split <;> simp_all
  have decoded : (tableObserver positive T).decoder = (relabel M r).decoder := by
    funext e
    exact decode_packCache N (M.decoder (r.symm e)) (M.decoded_nodup (r.symm e))
      (caches (r.symm e))
  simp only [tableObserver, relabel, Observer.mk.injEq]
  exact ⟨initial.symm, actions, rfl, decoded⟩

/-- Actual and counterfactual semantics of a representation refer to the same
source and literal histories; no reachable-state quotient is taken. -/
structure RepresentationContract (N : Nat) (M : Observer E)
    (positive : 0 < Fintype.card E) (r : E ≃ Fin (Fintype.card E))
    (T : NativeTable N (Fintype.card E)) : Prop where
  initial : r M.e0 = ⟨0, positive⟩
  actions : ∀ e, (tableObserver positive T).action (r e) = M.action e
  transitions : ∀ e y, (tableObserver positive T).transition (r e) y = r (M.transition e y)
  caches : ∀ e, (tableObserver positive T).decoder (r e) = M.decoder e
  prefixes : ∀ U e h, ActualPrefix (tableObserver positive T) U (r e) h ↔
    ActualPrefix M U e h
  runs : ∀ U e t f b, Run (tableObserver positive T) U (r e) t (r f) b ↔
    Run M U e t f b
  histories : ∀ h, historyState (tableObserver positive T) h = r (historyState M h) ∧
    historyAction (tableObserver positive T) h = historyAction M h
  fees : ∀ tau U, Fee (tableObserver positive T) tau U = Fee M tau U
  prices : ∀ tau kappa, J_N N (tableObserver positive T) tau kappa = J_N N M tau kappa
  admissible : Admissible N M → Admissible N (tableObserver positive T)

theorem representation_contract (N : Nat) (M : Observer E)
    (positive : 0 < Fintype.card E) (r : E ≃ Fin (Fintype.card E))
    (T : NativeTable N (Fintype.card E)) (initial : r M.e0 = ⟨0, positive⟩)
    (table : tableObserver positive T = relabel M r) :
    RepresentationContract N M positive r T := by
  refine ⟨initial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [table]
  · intro e; simp [relabel]
  · intro e y; simp [relabel]
  · intro e; simp [relabel]
  · intro U e h
    constructor
    · intro pref; simpa using relabel_prefix_back M r U pref
    · exact relabel_prefix M r U
  · intro U e t f b
    constructor
    · intro run; simpa using relabel_run_back M r U run
    · exact relabel_run M r U
  · intro h
    have state : historyState (relabel M r) h = r (historyState M h) :=
      by
        unfold historyState
        exact relabel_response M r M.e0 (h.map (fun a => a.2))
    refine ⟨state, ?_⟩
    unfold historyAction
    rw [state]
    change M.action (r.symm (r (historyState M h))) = M.action (historyState M h)
    rw [Equiv.symm_apply_apply]
  · exact relabel_fee M r
  · intro tau kappa
    have fees : Fee (relabel M r) tau = Fee M tau := funext (relabel_fee M r tau)
    simp only [J_N, Fintype.card_fin, maxFee, fees]
  · exact relabel_admissible N M r

/-- Every original bounded admissible competitor is covered by the finite
native table type at its exact full nominal cardinality. Normalization supplies
domination, and relabeling supplies exact semantics and prices thereafter. -/
theorem admissible_competitor_table_coverage (N : Nat) (M : Observer E)
    (admissible : Admissible N M) :
    ∃ (H : Observer E) (positive : 0 < Fintype.card E)
      (r : E ≃ Fin (Fintype.card E)) (T : NativeTable N (Fintype.card E)),
      NormalizationContract N M H ∧ RepresentationContract N H positive r T ∧
      T ∈ lawfulTables N (Fintype.card E) positive ∧
      ∀ tau : Address → ℝ, (∀ q, 0 ≤ tau q) →
        (∀ U, Allowed N U → Fee (tableObserver positive T) tau U ≤ Fee M tau U) ∧
        ∀ kappa : ℝ, 0 < kappa →
          J_N N (tableObserver positive T) tau kappa ≤ J_N N M tau kappa := by
  obtain ⟨H, _, normalization⟩ := absent_normalization_contract N M admissible
  have bounded : ∀ e a, a ∈ H.decoder e → a.1 ∈ Q_N N := by
    intro e a member
    rw [(normalization.decoder e).1] at member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  obtain ⟨positive, r, T, initial, table⟩ :=
    bounded_table_representation N H normalization.requests bounded
  have representation := representation_contract N H positive r T initial table
  have lawful : T ∈ lawfulTables N (Fintype.card E) positive := by
    classical
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      representation.admissible normalization.admissible⟩
  refine ⟨H, positive, r, T, normalization, representation, lawful, ?_⟩
  intro tau nonneg
  have domination := normalization.prices tau nonneg
  constructor
  · intro U allowed
    rw [representation.fees]
    exact domination.1 U allowed
  · intro kappa positivePrice
    rw [representation.prices]
    exact domination.2.2.2 kappa positivePrice

end D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverFiniteTable
