/- GID: D5/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Observer/DelayedOriginalReadout
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Executable guarded recovery of arbitrary original addresses at every substitution epoch. -/

import D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout

open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout leaves)
open ActualLeafHistoryRigidity (subtree)
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Hist execute)

/-- The rightmost label contributes zero for alpha and one for beta. -/
def rightClock : Source → Nat
  | .of true => 0
  | .of false => 1
  | .mul _ y => 2 + rightClock y

/-- A physical suffix of right edges. -/
def rights (n : Nat) : Address := List.replicate n true

private theorem clock_step (u : Source) : rightClock (substitution u) = rightClock u + 1 := by
  induction u with
  | of b => cases b <;> rfl
  | mul x y hx hy =>
    rw [show substitution (.mul x y) = .mul (substitution x) (substitution y) from
      substitution.map_mul x y]
    simp only [FreeMagma.mul_eq, rightClock, hy]
    omega

/-- Substitution advances the right clock by precisely the certified epoch. -/
theorem right_clock_iterate (N : Nat) (u : Source) :
    rightClock (substitution^[N] u) = rightClock u + N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ_apply', clock_step, ih]
    omega

/-- A right-spine reply gives exactly one of the four clock intervals. -/
theorem right_clock_readout (s : Nat) (u : Source) :
    (readout (rights s) u = .absent ↔ rightClock u < 2*s) ∧
    (readout (rights s) u = .alpha ↔ rightClock u = 2*s) ∧
    (readout (rights s) u = .beta ↔ rightClock u = 2*s+1) ∧
    (readout (rights s) u = .branch ↔ 2*s+2 ≤ rightClock u) := by
  induction s generalizing u with
  | zero =>
    cases u with
    | of b => cases b <;> simp [rights, readout, rightClock]
    | mul x y => simp [rights, readout, rightClock] <;> omega
  | succ s ih =>
    cases u with
    | of b => cases b <;> simp [rights, List.replicate_succ, readout, rightClock] <;> omega
    | mul x y =>
      simp only [rights, List.replicate_succ, readout, rightClock]
      have h := ih y
      simp only [rights] at h
      rcases h with ⟨ha, hb, hc, hd⟩
      exact ⟨ha.trans (by omega), hb.trans (by omega),
        hc.trans (by omega), hd.trans (by omega)⟩

private theorem clock_at_step (p : Address) (u : Source) :
    match subtree p u, subtree p (substitution u) with
    | some x, some y => rightClock y = rightClock x + 1
    | none, some y => rightClock y ≤ 1
    | none, none => True
    | some _, none => False := by
  induction p generalizing u with
  | nil => exact clock_step u
  | cons d p ih =>
    cases u with
    | of b =>
      cases b with
      | false =>
        rw [show substitution (.of false) = .mul (.of false) (.of true) from rfl]
        cases d <;> cases p <;> simp [subtree, rightClock]
      | true =>
        rw [show substitution (.of true) = .of false from rfl]
        simp [subtree]
    | mul x y =>
      rw [show substitution (.mul x y) = .mul (substitution x) (substitution y) from
      substitution.map_mul x y]
      cases d <;> simpa only [FreeMagma.mul_eq, subtree] using ih _

/-- Original nodes retain their clock; newborn nodes have clock at most N.
Only a scalar clock is transported, with no current-presence assumption. -/
theorem address_clock_bounds (N : Nat) (p : Address) (u : Source) :
    (∀ x, subtree p u = some x → ∃ y,
      subtree p (substitution^[N] u) = some y ∧ rightClock y = rightClock x + N) ∧
    (subtree p u = none → ∀ y, subtree p (substitution^[N] u) = some y →
      rightClock y ≤ N) := by
  induction N with
  | zero =>
    constructor
    · intro x hx
      exact ⟨x, hx, by omega⟩
    · intro h y hy
      simp only [Function.iterate_zero, id_eq, h] at hy
      contradiction
  | succ N ih =>
    rw [Function.iterate_succ_apply']
    have hs := clock_at_step p (substitution^[N] u)
    constructor
    · intro x hx
      obtain ⟨z, hz, hc⟩ := ih.1 x hx
      rw [hz] at hs
      cases hy : subtree p (substitution (substitution^[N] u)) with
      | none => simp [hy] at hs
      | some y => exact ⟨y, rfl, by simp only [hy] at hs; omega⟩
    · intro hx y hy
      rw [hy] at hs
      cases hz : subtree p (substitution^[N] u) with
      | none => simp only [hz] at hs; omega
      | some z =>
        simp only [hz] at hs
        have hc := ih.2 hx z hz
        omega

/-- Ceiling of half the certified epoch, including zero. -/
def halfCeil (N : Nat) : Nat := N/2 + N%2

/-- The total odd/even inverse table for a label probe. -/
def decodeLabel (N : Nat) (r : Reply) : Reply :=
  if N%2 = 0 then r else
    match r with
    | .absent => .alpha
    | .alpha => .beta
    | .beta | .branch => .branch

/-- The parent probe recognizes original presence, not current presence. -/
def guardAccept (N : Nat) (r : Reply) : Bool :=
  if N%2 = 0 then r != .absent else r == .beta || r == .branch

/-- The fixed chronological physical query list retains repeated calls. -/
def originalQueries (N : Nat) (p : Address) : List Address :=
  if N = 0 then [p] else
  if p = [] then [rights (halfCeil N)] else
    [p.dropLast ++ rights (N/2+1), p ++ rights (halfCeil N)]

/-- Decode any supplied reply list, with absent as the malformed-input default. -/
def originalDecode (N : Nat) (p : Address) (rs : List Reply) : Reply :=
  if N = 0 then rs.headD .absent else
  if p = [] then decodeLabel N (rs.headD .absent) else
    match rs with
    | guard :: label :: _ => if guardAccept N guard then decodeLabel N label else .absent
    | _ => .absent

private theorem label_clock_decode (N : Nat) (x y : Source)
    (hc : rightClock y = rightClock x + N) :
    decodeLabel N (readout (rights (halfCeil N)) y) = readout [] x := by
  have h := right_clock_readout (halfCeil N) y
  have hmod := Nat.mod_lt N (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div N 2
  by_cases he : N%2 = 0
  · simp only [decodeLabel, if_pos he]
    have hs : halfCeil N = N/2 := by simp [halfCeil, he]
    cases x with
    | of b =>
      cases b
      · exact h.2.2.1.mpr (by simp only [rightClock] at hc; rw [hs]; omega)
      · exact h.2.1.mpr (by simp only [rightClock] at hc; rw [hs]; omega)
    | mul l r =>
      exact h.2.2.2.mpr (by simp only [rightClock] at hc; rw [hs]; omega)
  · have he' : N%2 = 1 := by omega
    have hs : halfCeil N = N/2+1 := by simp [halfCeil, he']
    cases x with
    | of b =>
      cases b
      · have hr := h.2.1.mpr (by simp only [rightClock] at hc; rw [hs]; omega)
        rw [hr]
        simp [decodeLabel, he, readout]
      · have hr := h.1.mpr (by simp only [rightClock] at hc; rw [hs]; omega)
        rw [hr]
        simp [decodeLabel, he, readout]
    | mul l r =>
      simp only [rightClock] at hc
      by_cases ht : rightClock y = 2*halfCeil N+1
      · rw [h.2.2.1.mpr ht]
        simp [decodeLabel, he, readout]
      · have ht' : 2*halfCeil N+2 ≤ rightClock y := by rw [hs] at *; omega
        rw [h.2.2.2.mpr ht']
        simp [decodeLabel, he, readout]

private theorem guard_clock (N : Nat) (y : Source) :
    guardAccept N (readout (rights (N/2+1)) y) = true ↔ N+2 ≤ rightClock y := by
  have h := right_clock_readout (N/2+1) y
  have hmod := Nat.mod_lt N (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div N 2
  cases hr : readout (rights (N/2+1)) y <;>
    simp only [hr, reduceCtorEq, guardAccept] at * <;>
    split_ifs <;> simp_all <;> omega

/-- The physical parent guard is equivalent to original child presence. -/
theorem original_presence_guard (N : Nat) (a : Address) (d : Bool) (u : Source) :
    guardAccept N (readout (a ++ rights (N/2+1)) (substitution^[N] u)) = true ↔
      readout (a ++ [d]) u ≠ .absent := by
  have readAt := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [readAt, readAt]
  have bounds := address_clock_bounds N a u
  cases hx : subtree a u with
  | none =>
    simp only [hx, ne_eq, not_true_eq_false, iff_false]
    cases hy : subtree a (substitution^[N] u) with
    | none => simp [guardAccept, hy]
    | some y =>
      simp only [hy, guard_clock, not_le]
      have hb := bounds.2 hx y hy
      omega
  | some x =>
    obtain ⟨y, hy, hc⟩ := bounds.1 x hx
    rw [hy, guard_clock]
    cases x with
    | of b =>
      cases b <;> simp only [rightClock] at hc <;>
        simp only [readout, ne_eq, not_true_eq_false, iff_false, not_le] <;> omega
    | mul l r =>
      simp only [rightClock] at hc
      have hb : N+2 ≤ rightClock y := by omega
      rw [iff_true_intro hb]
      cases d
      · cases l with
        | of b => cases b <;> simp [readout]
        | mul s t => simp [readout]
      · cases r with
        | of b => cases b <;> simp [readout]
        | mul s t => simp [readout]

private theorem present_label_decode (N : Nat) (p : Address) (u : Source)
    (hp : readout p u ≠ .absent) :
    decodeLabel N (readout (p ++ rights (halfCeil N)) (substitution^[N] u)) = readout p u := by
  have readAt := ActualLeafHistoryRigidity.actual_address_geometry.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hroot := readAt p [] u
  simp only [List.append_nil] at hroot
  cases hx : subtree p u with
  | none => simp [hroot, hx] at hp
  | some x =>
    obtain ⟨y, hy, hc⟩ := (address_clock_bounds N p u).1 x hx
    rw [readAt, hy, hroot, hx]
    exact label_clock_decode N x y hc

/-- The total generated decoder recovers all original replies, including absence. -/
theorem original_decoder_correct (N : Nat) (p : Address) (u : Source) :
    originalDecode N p ((originalQueries N p).map (fun q => readout q (substitution^[N] u))) =
      readout p u := by
  by_cases hN : N = 0
  · subst N
    simp [originalQueries, originalDecode]
  · by_cases hp : p = []
    · subst p
      simpa [originalQueries, originalDecode, hN] using
        label_clock_decode N u (substitution^[N] u) (right_clock_iterate N u)
    · let a := p.dropLast
      let d := p.getLast hp
      have he : p = a ++ [d] := (List.dropLast_concat_getLast hp).symm
      have hg := original_presence_guard N a d u
      rw [← he] at hg
      simp only [originalQueries, originalDecode, if_neg hN, if_neg hp,
        List.map_cons, List.map_nil]
      change (if guardAccept N (readout (a ++ rights (N/2+1)) (substitution^[N] u)) then
        decodeLabel N (readout (p ++ rights (halfCeil N)) (substitution^[N] u)) else .absent) = _
      by_cases hpres : readout p u ≠ .absent
      · rw [if_pos (hg.mpr hpres)]
        exact present_label_decode N p u hpres
      · rw [if_neg (fun h => hpres (hg.mp h))]
        exact (not_ne_iff.mp hpres).symm

private theorem original_query_bounds (N : Nat) (p : Address) :
    (originalQueries N p).length ≤ 2 ∧
    ∀ q ∈ originalQueries N p, q.length ≤ p.length + halfCeil N := by
  have hmod := Nat.mod_lt N (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div N 2
  unfold originalQueries
  split_ifs with hN hp
  · simp [hN, halfCeil]
  · subst p
    simp [rights]
  · constructor
    · simp
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · simp only [List.length_append, List.length_dropLast, rights, List.length_replicate]
        have hn : 0 < p.length := List.length_pos_iff.mpr hp
        unfold halfCeil
        omega
      · simp [rights]

/-- A computable finite chain submitting every list entry in order. -/
def queryChain : List Address → PassiveProtocol Address (fun _ => Reply)
  | [] => .stop
  | q :: qs => .query q (fun _ => queryChain qs)

/-- The chronological actual transcript of a fixed physical list. -/
def listTrace (qs : List Address) (u : Source) : Hist (fun _ : Address => Reply) :=
  qs.map (fun q => ⟨q, readout q u⟩)

private theorem chain_trace (qs : List Address) (u : Source) :
    runPassiveProtocol readout (queryChain qs) u = listTrace qs u := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simpa [queryChain, runPassiveProtocol, listTrace] using congrArg (List.cons (⟨q, readout q u⟩ : Sigma (fun _ : Address => Reply))) ih

/-- A total history controller uses only the number of consumed new replies. -/
def listController {L : Type} (qs : List Address) (finish : Hist (fun _ : Address => Reply) → L)
    (h : Hist (fun _ : Address => Reply)) : Sum Address L :=
  match qs[h.length]? with
  | some q => .inl q
  | none => .inr (finish h)

private theorem controller_suffix {L : Type} (qs : List Address)
    (finish : Hist (fun _ : Address => Reply) → L) (u : Source)
    (h : Hist (fun _ : Address => Reply)) (pre rest : List Address)
    (hs : qs = pre ++ rest) (hlen : h.length = pre.length) :
    execute readout (listController qs finish) (rest.length+1) h u =
      some (listTrace rest u, finish (h ++ listTrace rest u)) := by
  induction rest generalizing h pre with
  | nil =>
    subst qs
    simp [execute, listController, hlen, listTrace]
  | cons q rest ih =>
    have hnext : listController qs finish h = .inl q := by
      simp [listController, hs, hlen]
    change execute readout (listController qs finish) ((rest.length+1)+1) h u = _
    rw [execute, hnext]
    have hs' : qs = (pre ++ [q]) ++ rest := by simp [hs]
    have hl' : (h ++ [(⟨q, readout q u⟩ : Sigma (fun _ : Address => Reply))]).length = (pre ++ [q]).length := by simp [hlen]
    dsimp only
    rw [ih _ _ hs' hl']
    simp [listTrace, List.append_assoc]

/-- Generated finite protocols agree with an executable history controller and terminate. -/
theorem fixed_list_execution {L : Type} (qs : List Address)
    (finish : Hist (fun _ : Address => Reply) → L) (u : Source) :
    runPassiveProtocol readout (queryChain qs) u = listTrace qs u ∧
    execute readout (listController qs finish) (qs.length+1) [] u =
      some (listTrace qs u, finish (listTrace qs u)) ∧
    (listTrace qs u).map Sigma.fst = qs ∧ (listTrace qs u).length = qs.length := by
  refine ⟨chain_trace qs u, ?_, ?_, ?_⟩
  · simpa using controller_suffix qs finish u [] [] qs (by simp) rfl
  · simp [listTrace, List.map_map, Function.comp_def]
  · simp [listTrace]

/-- The effective original-read service has at most two chronological calls and bounded addresses. -/
theorem original_decoder_service (N : Nat) (p : Address) (u : Source) :
    let qs := originalQueries N p
    let finish := fun h : Hist (fun _ : Address => Reply) => originalDecode N p (h.map Sigma.snd)
    execute readout (listController qs finish) (qs.length+1) [] (substitution^[N] u) =
      some (listTrace qs (substitution^[N] u), readout p u) ∧
    (listTrace qs (substitution^[N] u)).length ≤ 2 ∧
    (∀ q ∈ qs, q.length ≤ p.length + halfCeil N) ∧
    ((N = 0 ∨ p = []) → qs.length = 1) := by
  dsimp only
  have run := (fixed_list_execution (originalQueries N p)
    (fun h => originalDecode N p (h.map Sigma.snd)) (substitution^[N] u)).2.1
  have correct := original_decoder_correct N p u
  simp only [listTrace, List.map_map, Function.comp_def] at run
  rw [correct] at run
  refine ⟨run, ?_, (original_query_bounds N p).2, ?_⟩
  · simpa [listTrace] using (original_query_bounds N p).1
  · rintro (rfl | rfl) <;> simp [originalQueries] <;> split_ifs <;> rfl

#print axioms original_decoder_service
end D5.S3.Arith.FibonacciAtomic.Observer.DelayedOriginalReadout
