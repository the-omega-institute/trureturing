/- GID: D5/S3/Arith/FibonacciAtomic/Observer/ActualObserverBoundedLowerBounds
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Bounded native replay, complete cache spectrum and nominal control lower bounds. -/

import D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverAbsorbingNormalization

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverBoundedLowerBounds

universe u
open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition
  (Address Reply readout leaves flip paid Positive source_foundation)
open ActualImageSevenLeafSeparation (minimum thirdImage seven_leaf_separation leafAddresses)
open ActualFiniteObserverAbsentElimination
open ActualObserverAbsorbingNormalization (Fee charge fee_run allowedSources allowedSources_exact)

variable {E : Type u} [Fintype E]

/-- Decoded values along every chronological response prefix, including both endpoints.
The trace is an external record, not an additional input port of the observer. -/
noncomputable def cachedVisits (M : Observer E) (t : RawHistory) : Finset RawHistory := by
  classical
  exact (Finset.range (t.length + 1)).image
    (fun i => M.decoder (historyState M (t.take i)))

/-- Distinct original positive sources in the complete bounded domain. -/
noncomputable def positiveSources (N : Nat) : Finset Source := by
  classical
  exact (allowedSources N).filter Positive

private theorem flip_length (U : Source) (q : Address) :
    (flip U q).length = U.length := by
  induction U generalizing q with
  | of b => cases q <;> rfl
  | mul L R ihL ihR =>
    cases q with
    | nil => rfl
    | cons d q =>
      cases d <;> simp only [ActualTreeReadoutAcquisition.flip, FreeMagma.length, ihL, ihR]

/-- Replay preserves the same nominal terminal row as well as the exact raw trace.
Stored hits are identical without any cache-truth assumption; misses use agreement. -/
private theorem run_replay (M : Observer E) (U V : Source)
    {e f : E} {t : RawHistory} {b : Bool} (run : Run M U e t f b)
    (agree : ∀ q ∈ paid t, readout q V = readout q U) : Run M V e t f b := by
  induction run with
  | halt row => exact Run.halt row
  | @query e f q t b row tail ih =>
    have head : q ∈ paid (⟨q, queryReply (M.decoder e) q U⟩ :: t) := by
      simp [paid]
    have reply : queryReply (M.decoder e) q V = queryReply (M.decoder e) q U := by
      unfold queryReply
      cases (M.decoder e).find? (fun a => a.1 == q) with
      | none => exact agree q head
      | some a => rfl
    have rest := ih (fun r hr => agree r (by simpa [paid] using Or.inr hr))
    simpa only [reply] using Run.query (U := V) row (by simpa only [reply] using rest)

private theorem bounded_leaf_coverage (N : Nat) (M : Observer E)
    (admissible : Admissible N M) (U : Source) (allowed : Allowed N U)
    (positive : Positive U) {t : RawHistory} {f : E} {b : Bool}
    (run : Run M U M.e0 t f b) : (leaves U).toFinset ⊆ paid t := by
  intro q hq
  by_contra missing
  have leaf : q ∈ leaves U := List.mem_toFinset.mp hq
  have negative : ¬ Positive (flip U q) := by
    obtain ⟨s, hs⟩ := positive
    subst U
    exact source_foundation.2.1 s q leaf
  have flip_allowed : Allowed N (flip U q) := by
    change (flip U q).length ≤ N
    rw [flip_length]
    exact allowed
  have replay := run_replay M U (flip U q) run (by
    intro r hr
    exact source_foundation.2.2.2.1 U q leaf r (by
      intro eqn
      subst r
      exact missing hr))
  have old := (admissible_run_contract N M admissible U allowed run).2.2.2.2.2.2.2
  have new := (admissible_run_contract N M admissible (flip U q) flip_allowed replay).2.2.2.2.2.2.2
  exact negative (new.mp (old.mpr positive))

private theorem paid_update (cache : RawHistory) (q : Address) (y : Reply) :
    paid (cacheUpdate cache q y) = insert q (paid cache) := by
  classical
  by_cases hit : q ∈ cache.map Sigma.fst
  · simp [cacheUpdate, hit, paid, Finset.insert_eq_of_mem (List.mem_toFinset.mpr hit)]
  · simp [cacheUpdate, hit, paid, List.map_append, Finset.union_comm]

private theorem terminal_mem_visits (M : Observer E) (h : RawHistory) :
    M.decoder (historyState M h) ∈ cachedVisits M h := by
  classical
  exact Finset.mem_image.mpr ⟨h.length, Finset.mem_range.mpr (by omega), by simp⟩

private theorem visits_snoc (M : Observer E) (h : RawHistory)
    (a : Sigma (fun _ : Address => Reply)) :
    cachedVisits M (h ++ [a]) =
      insert (M.decoder (historyState M (h ++ [a]))) (cachedVisits M h) := by
  classical
  ext c
  constructor
  · intro hc
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hc
    have bound : i ≤ h.length + 1 := by
      simp only [Finset.mem_range, List.length_append, List.length_singleton] at hi
      omega
    by_cases old : i ≤ h.length
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_range.mpr (by omega), ?_⟩
      simp [List.take_append, Nat.sub_eq_zero_of_le old]
    · have eqn : i = (h ++ [a]).length := by
        simp only [List.length_append, List.length_singleton]
        omega
      simp only [eqn, List.take_length]
      exact Finset.mem_insert_self _ _
  · intro hc
    rcases Finset.mem_insert.mp hc with hc | hc
    · rw [hc]
      exact terminal_mem_visits M _
    · obtain ⟨i, hi, eqn⟩ := Finset.mem_image.mp hc
      have old : i ≤ h.length := by
        simp only [Finset.mem_range] at hi
        omega
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_range.mpr (by
        simp only [List.length_append, List.length_singleton]
        omega), ?_⟩
      simpa [List.take_append, Nat.sub_eq_zero_of_le old] using eqn

/-- Every actual first-occurrence append creates one new decoded value. Hits
preserve the full ordered cache; prior values cannot already contain the new address. -/
private theorem prefix_cache_spectrum (M : Observer E) (U : Source) (legal : Legal M U)
    {e : E} {h : RawHistory} (pref : ActualPrefix M U e h) :
    paid (M.decoder e) = paid h ∧
    (cachedVisits M h).card = (paid h).card + 1 ∧
    ∀ c ∈ cachedVisits M h, paid c ⊆ paid h := by
  classical
  induction pref with
  | initial =>
    simp [cachedVisits, historyState, responseState, legal.1, paid]
  | @query e h q prior row ih =>
    let y := queryReply (M.decoder e) q U
    have next := ActualPrefix.query prior row
    have state := (actualPrefix_semantics M U legal prior).1
    have nextstate := (actualPrefix_semantics M U legal next).1
    have update := (legal.2 e h prior).2 q row
    have support : paid (h ++ [⟨q, y⟩]) = insert q (paid h) := by
      simp [paid, List.map_append, Finset.union_comm]
    have nextsupport : paid (M.decoder (M.transition e y)) = insert q (paid h) := by
      rw [update, paid_update, ih.1]
    have visits : cachedVisits M (h ++ [⟨q, y⟩]) =
        insert (M.decoder (M.transition e y)) (cachedVisits M h) := by
      rw [visits_snoc, nextstate]
    refine ⟨nextsupport.trans support.symm, ?_, ?_⟩
    · rw [visits, support]
      by_cases hit : q ∈ paid h
      · have oldhit : q ∈ (M.decoder e).map Sigma.fst := by
          have mem : q ∈ paid (M.decoder e) := by rw [ih.1]; exact hit
          exact List.mem_toFinset.mp mem
        have same : M.decoder (M.transition e y) = M.decoder e := by
          rw [update, cacheUpdate, if_pos oldhit]
        have member : M.decoder e ∈ cachedVisits M h := by
          simpa only [state] using terminal_mem_visits M h
        rw [same, Finset.insert_eq_of_mem member, Finset.insert_eq_of_mem hit, ih.2.1]
      · have fresh : M.decoder (M.transition e y) ∉ cachedVisits M h := by
          intro member
          have := ih.2.2 _ member
          apply hit
          apply this
          rw [nextsupport]
          exact Finset.mem_insert_self _ _
        rw [Finset.card_insert_of_notMem fresh, Finset.card_insert_of_notMem hit, ih.2.1]
    · rw [visits, support]
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · rw [nextsupport]
      · exact (ih.2.2 c hc).trans (Finset.subset_insert _ _)

private theorem prefix_take (M : Observer E) (U : Source) (legal : Legal M U)
    {e : E} {h : RawHistory} (pref : ActualPrefix M U e h) :
    ∀ i ≤ h.length, ActualPrefix M U (historyState M (h.take i)) (h.take i) := by
  induction pref with
  | initial =>
    intro i hi
    have : i = 0 := by simpa using hi
    subst i
    exact ActualPrefix.initial
  | @query e h q prior row ih =>
    intro i hi
    by_cases old : i ≤ h.length
    · simpa [List.take_append, Nat.sub_eq_zero_of_le old] using ih i old
    · have eqn : i = (h ++ [⟨q, queryReply (M.decoder e) q U⟩] : RawHistory).length := by
        simp only [List.length_append, List.length_singleton] at hi ⊢
        omega
      rw [eqn, List.take_length]
      have next := ActualPrefix.query prior row
      rw [(actualPrefix_semantics M U legal next).1]
      exact next

private theorem run_cache_spectrum (M : Observer E) (U : Source) (legal : Legal M U)
    {t : RawHistory} {f : E} {b : Bool} (run : Run M U M.e0 t f b) :
    paid (M.decoder f) = paid t ∧
    (cachedVisits M t).card = (paid t).card + 1 ∧
    ∀ i ≤ t.length, ActualPrefix M U (historyState M (t.take i)) (t.take i) := by
  have pref := (run_from_actualPrefix M U run ActualPrefix.initial).1
  simp only [List.nil_append] at pref
  have spectrum := prefix_cache_spectrum M U legal pref
  exact ⟨spectrum.1, spectrum.2.1, prefix_take M U legal pref⟩

/-- Complete bounded-source cache and nominal control lower bounds. The exact
cache count includes the empty and terminal caches and every repeated request. -/
theorem bounded_cache_control_lower_bounds (N : Nat) (M : Observer E)
    (admissible : Admissible N M) :
    (∀ U : Source, Allowed N U → Positive U →
      ∀ {t : RawHistory} {f : E} {b : Bool}, Run M U M.e0 t f b →
        (leaves U).toFinset ⊆ paid t ∧ U.length + 1 ≤ Fintype.card E ∧
        ∀ tau : Address → ℝ, (∀ q, 0 ≤ tau q) →
          (∑ q ∈ (leaves U).toFinset, tau q) ≤ Fee M tau U) ∧
    (∀ U : Source, Allowed N U →
      ∀ {t : RawHistory} {f : E} {b : Bool}, Run M U M.e0 t f b →
        paid (M.decoder f) = paid t ∧
        (cachedVisits M t).card = (paid t).card + 1 ∧
        ∀ i ≤ t.length, ActualPrefix M U (historyState M (t.take i)) (t.take i)) ∧
    (0 < (positiveSources N).card → (positiveSources N).card + 2 ≤ Fintype.card E) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro U allowed positive t f b run
    have coverage := bounded_leaf_coverage N M admissible U allowed positive run
    have spectrum := run_cache_spectrum M U (admissible.legal U allowed) run
    refine ⟨coverage, ?_, ?_⟩
    · have contained : cachedVisits M t ⊆ Finset.univ.image M.decoder := by
        intro c hc
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
        exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
      have count := (Finset.card_le_card contained).trans
        (Finset.card_image_le (s := Finset.univ) (f := M.decoder))
      have leafcount := (seven_leaf_separation.1 U).1
      change (leaves U).toFinset.card = U.length at leafcount
      have leaves_le := Finset.card_le_card coverage
      rw [spectrum.2.1, Finset.card_univ] at count
      omega
    · intro tau nonneg
      rw [fee_run M tau U run, charge]
      exact Finset.sum_le_sum_of_subset_of_nonneg coverage (fun q _ _ => nonneg q)
  · intro U allowed t f b run
    exact run_cache_spectrum M U (admissible.legal U allowed) run
  · intro positive_count
    let Pos := {U : Source // U ∈ positiveSources N}
    have domain (U : Pos) : Allowed N U.val :=
      (allowedSources_exact N U.val).mp (Finset.mem_filter.mp U.property).1
    have positive (U : Pos) : Positive U.val := (Finset.mem_filter.mp U.property).2
    have runs (U : Pos) := admissible.correct U.val (domain U)
    choose trace finish bit execution correct using runs
    have contracts (U : Pos) := admissible_run_contract N M admissible U.val
      (domain U) (execution U)
    have halt (U : Pos) : M.action (finish U) = .inr true := by
      have bt : bit U = true := (correct U).mpr (positive U)
      simpa only [bt] using (contracts U).2.2.1
    have injective : Function.Injective finish := by
      intro U V same
      apply Subtype.ext
      apply Eq.symm
      apply source_foundation.2.2.1 U.val V.val
      intro q leaf
      have coverage := bounded_leaf_coverage N M admissible U.val (domain U)
        (positive U) (execution U)
      have support := (run_cache_spectrum M U.val (admissible.legal U.val (domain U))
        (execution U)).1
      have member : q ∈ paid (M.decoder (finish U)) := by
        rw [support]
        exact coverage (List.mem_toFinset.mpr leaf)
      obtain ⟨a, ha, addr⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
      have truthU := (contracts U).2.2.2.2.2.1 a ha
      have truthV := (contracts V).2.2.2.2.2.1 a (by simpa only [same] using ha)
      simpa only [addr] using truthV.symm.trans truthU
    let terminalRows := Finset.univ.image finish
    have terminal_count : terminalRows.card = (positiveSources N).card := by
      rw [Finset.card_image_of_injective _ injective, Finset.card_univ]
      exact Fintype.card_coe _
    have neg_allowed : Allowed N (.of false) := admissible.budget_pos
    have neg : ¬ Positive (.of false) := by
      intro h
      obtain ⟨s, hs⟩ := h
      have bound := minimum s
      change 3 ≤ (GenealogicalFiberTransport.substitution^[3] s).length at bound
      rw [hs] at bound
      contradiction
    obtain ⟨nt, nf, nb, nr, nc⟩ := admissible.correct (.of false) neg_allowed
    have nb_false : nb = false := by
      cases nb
      · rfl
      · exact (neg (nc.mp rfl)).elim
    have neg_halt : M.action nf = .inr false := by
      simpa only [nb_false] using (run_from_actualPrefix M (.of false) nr
        ActualPrefix.initial).2
    have neg_fresh : nf ∉ terminalRows := by
      intro member
      obtain ⟨U, _, eqn⟩ := Finset.mem_image.mp member
      have h := halt U
      rw [eqn, neg_halt] at h
      cases h
    obtain ⟨U, hU⟩ := Finset.card_pos.mp positive_count
    let P : Pos := ⟨U, hU⟩
    have initial_query : ∀ b, M.action M.e0 ≠ .inr b := by
      intro b row
      have posbit := (run_deterministic M U (Run.halt row) (execution P)).2.2
      have negbit := (run_deterministic M (.of false) (Run.halt row) nr).2.2
      have pos_true := (correct P).mpr (positive P)
      rw [nb_false] at negbit
      change b = bit P at posbit
      rw [pos_true, negbit] at posbit
      cases posbit
    have initial_fresh : M.e0 ∉ insert nf terminalRows := by
      intro member
      rcases Finset.mem_insert.mp member with same | member
      · exact initial_query false (same ▸ neg_halt)
      · obtain ⟨U, _, eqn⟩ := Finset.mem_image.mp member
        exact initial_query true (eqn ▸ halt U)
    have count := Finset.card_le_card
      (Finset.subset_univ (insert M.e0 (insert nf terminalRows)))
    rw [Finset.card_insert_of_notMem initial_fresh, Finset.card_insert_of_notMem neg_fresh,
      terminal_count, Finset.card_univ] at count
    omega

#print axioms bounded_cache_control_lower_bounds

end D5.S3.Arith.FibonacciAtomic.Observer.ActualObserverBoundedLowerBounds
