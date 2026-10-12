/- GID: D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverFiniteChecks
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact finite source-orbit certification of original raw-cache execution. -/

import D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverFiniteTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverFiniteChecks

universe u
open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address Reply finiteDecision Positive acquisition_foundation)
open ActualFiniteObserverAbsentElimination
open ActualObserverAbsorbingNormalization

variable {E : Type u} [Fintype E]

/-- A finite check on the original source orbit, including the halt cache.
All equality tests retain raw replies and chronological cache order. -/
def SourceCertificate (M : Observer E) (U : Source) : Prop :=
  M.decoder M.e0 = [] ∧
  (∃ j : Fin (Fintype.card E),
    M.action ((sourceStep M U)^[j.val] M.e0) = .inr (finiteDecision U)) ∧
  ∀ i : Fin (Fintype.card E),
    let e := (sourceStep M U)^[i.val] M.e0
    CacheTruth (M.decoder e) U ∧
    ∀ q : Address, M.action e = .inl q →
      M.decoder (M.transition e (queryReply (M.decoder e) q U)) =
        cacheUpdate (M.decoder e) q (queryReply (M.decoder e) q U)

/-- The guard at a query row tests its unique installed literal address. -/
noncomputable instance sourceCertificateDecidable (M : Observer E) (U : Source) :
    Decidable (SourceCertificate M U) := by
  unfold SourceCertificate
  have truth (e : E) : Decidable (CacheTruth (M.decoder e) U) := by
    unfold CacheTruth
    infer_instance
  have guard (e : E) : Decidable (∀ q : Address, M.action e = .inl q →
      M.decoder (M.transition e (queryReply (M.decoder e) q U)) =
        cacheUpdate (M.decoder e) q (queryReply (M.decoder e) q U)) := by
    cases row : M.action e with
    | inl r =>
      exact decidable_of_iff
        (M.decoder (M.transition e (queryReply (M.decoder e) r U)) =
          cacheUpdate (M.decoder e) r (queryReply (M.decoder e) r U))
        (by simp [row])
    | inr b => exact isTrue (by intro q h; simp [row] at h)
  infer_instance

/-- Finite acceptance inspects row data and the original finite source decision.
It never asks Legal, Run or Admissible for their truth value. -/
noncomputable def sourceCheck (M : Observer E) (U : Source) : Bool :=
  decide (SourceCertificate M U)

private theorem prefix_orbit (M : Observer E) (U : Source)
    {e : E} {h : RawHistory} (pref : ActualPrefix M U e h) :
    (sourceStep M U)^[h.length] M.e0 = e := by
  induction pref with
  | initial => rfl
  | @query e h q prior row ih =>
    simp only [List.length_append, List.length_singleton,
      Function.iterate_succ_apply', ih, sourceStep, row]

private theorem prefix_before_halt (M : Observer E) (U : Source)
    {j : Nat} {b : Bool}
    (halt : M.action ((sourceStep M U)^[j] M.e0) = .inr b)
    {e : E} {h : RawHistory} (pref : ActualPrefix M U e h) : h.length ≤ j := by
  induction pref with
  | initial => exact Nat.zero_le _
  | @query e h q prior row ih =>
    have ne : h.length ≠ j := by
      intro equal
      have state := prefix_orbit M U prior
      rw [equal] at state
      rw [state, row] at halt
      cases halt
    simp only [List.length_append, List.length_singleton]
    omega

private theorem run_of_orbit_halt (M : Observer E) (U : Source)
    (j : Nat) (e : E) (b : Bool)
    (halt : M.action ((sourceStep M U)^[j] e) = .inr b) :
    ∃ t f, Run M U e t f b := by
  induction j generalizing e with
  | zero => exact ⟨[], e, Run.halt halt⟩
  | succ j ih =>
    cases row : M.action e with
    | inr c =>
      have fixed : sourceStep M U e = e := by simp [sourceStep, row]
      rw [Function.iterate_fixed fixed] at halt
      have bit := Sum.inr.inj (row.symm.trans halt)
      exact ⟨[], e, Run.halt (by simpa [bit] using row)⟩
    | inl q =>
      have tail : M.action ((sourceStep M U)^[j]
          (M.transition e (queryReply (M.decoder e) q U))) = .inr b := by
        simpa [Function.iterate_succ_apply, sourceStep, row] using halt
      obtain ⟨t, f, run⟩ := ih _ tail
      exact ⟨⟨q, queryReply (M.decoder e) q U⟩ :: t, f, Run.query row run⟩

private theorem orbit_prefix_or_terminal (M : Observer E) (U : Source)
    {t : RawHistory} {f : E} {b : Bool} (run : Run M U M.e0 t f b)
    (i : Nat) : ∃ h, ActualPrefix M U ((sourceStep M U)^[i] M.e0) h := by
  have advance : ∀ k ≤ t.length,
      ∃ h, ActualPrefix M U ((sourceStep M U)^[k] M.e0) h := by
    intro k bound
    induction k with
    | zero => exact ⟨[], ActualPrefix.initial⟩
    | succ k ih =>
      obtain ⟨h, pref⟩ := ih (by omega)
      obtain ⟨q, row⟩ := (run_orbit M U run).2.2 k (by omega)
      have next := ActualPrefix.query pref row
      refine ⟨h ++ [⟨q, queryReply (M.decoder ((sourceStep M U)^[k] M.e0)) q U⟩], ?_⟩
      simpa [Function.iterate_succ_apply', sourceStep, row] using next
  by_cases before : i ≤ t.length
  · exact advance i before
  · have final := (run_orbit M U run).1
    have halt := (run_orbit M U run).2.1
    have fixed : sourceStep M U f = f := by simp [sourceStep, halt]
    have after : (sourceStep M U)^[i] M.e0 = f := by
      rw [← Nat.sub_add_cancel (show t.length ≤ i by omega),
        Function.iterate_add_apply, final, Function.iterate_fixed fixed]
    rw [after]
    exact ⟨t, by simpa using (run_from_actualPrefix M U run ActualPrefix.initial).1⟩

/-- The finite orbit guards earn legality on every actual prefix, and the
finite halt test is equivalent to correct original termination. -/
theorem sourceCheck_iff (M : Observer E) (U : Source) :
    sourceCheck M U = true ↔ Legal M U ∧
      ∃ t f b, Run M U M.e0 t f b ∧ (b = true ↔ Positive U) := by
  rw [sourceCheck, decide_eq_true_eq]
  constructor
  · rintro ⟨empty, ⟨j, halt⟩, guards⟩
    have legal : Legal M U := by
      refine ⟨empty, ?_⟩
      intro e h pref
      have bound := prefix_before_halt M U halt pref
      have state := prefix_orbit M U pref
      have g := guards ⟨h.length, lt_of_le_of_lt bound j.isLt⟩
      simpa only [state] using g
    obtain ⟨t, f, run⟩ := run_of_orbit_halt M U j M.e0 (finiteDecision U) halt
    exact ⟨legal, t, f, finiteDecision U, run, acquisition_foundation.1 U⟩
  · rintro ⟨legal, t, f, b, run, correct⟩
    have bit : b = finiteDecision U := by
      cases b <;> cases d : finiteDecision U <;> try rfl
      · exact False.elim ((Bool.false_ne_true) (correct.mpr ((acquisition_foundation.1 U).mp d)))
      · exact False.elim ((Bool.false_ne_true) (d.symm.trans
          (show finiteDecision U = true from (acquisition_foundation.1 U).mpr (correct.mp rfl))))
    refine ⟨legal.1, ⟨⟨t.length, run_length_bound M U run⟩, ?_⟩, ?_⟩
    · simpa only [(run_orbit M U run).1, bit] using (run_orbit M U run).2.1
    · intro i
      obtain ⟨h, pref⟩ := orbit_prefix_or_terminal M U run i.val
      exact legal.2 _ h pref

end D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverFiniteChecks
