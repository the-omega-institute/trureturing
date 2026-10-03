/- GID: D5/S3/Combinatorics/GreedyBrick/LiteralRestTrace
   generality: G
   mirror-B: D5/B/S3/Combinatorics/GreedyBrick/LiteralRestTrace
   mirror-E: none(waiver:unbounded-literal-clock-coupling)
   anchors: [mathlib/module/Mathlib.Data.Nat.Find, mathlib/module/Mathlib.Order.WellFounded]
   utility: none
   digest: A cofinal rest clock couples literal placements to an unbounded rest trace. -/

import D5.S3.Combinatorics.GreedyBrick.RestBlock
import D5.S3.Combinatorics.GreedyBrick.EventRealization
import Mathlib.Order.WellFounded

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace

open SuccessorBand RestBlock EventRealization
open D5.S3.ArithSums.GreedyBrickCapacityTotality

/-- Starting after brick one, the literal capacity placements admit an
initialized rest-event trace. Its endpoints form a strictly increasing
cofinal clock. Every sampled capacity and every intermediate brick agrees
with the same literal trajectory; each positive brick belongs to an event
interval. Height unboundedness is derived, not supplied as a premise.
The capacity and RestBlock imports are unadmitted mathematical inputs;
continuous rectangle-history correspondence is a separate obligation. -/
theorem literal_trace_realization :
    ∃ T : RestTrace,
      (∀ e, T.bin (e + 1) = firstZeroBin (T.state e).capacity) ∧
      (∀ e, (T.state e).capacity.reverse = trajectory (T.state e).endpoint) ∧
      StrictMono (fun e => (T.state e).endpoint) ∧
      (∀ N, ∃ e, N ≤ (T.state e).endpoint) ∧
      (∀ e d, placeBricks (T.state e).endpoint (T.state e).capacity.reverse d =
        trajectory ((T.state e).endpoint + d)) ∧
      (∀ N, 1 ≤ N → ∃ e d, d < T.bin (e + 1) ∧
        N = (T.state e).endpoint + d ∧
        trajectory N = placeBricks (T.state e).endpoint (T.state e).capacity.reverse d) := by
  classical
  let initial : RestState := ⟨1, [1], by simp⟩
  let next (s : RestState) : RestState := (literal_rest_block s).choose
  have next_spec (s : RestState) :
      RestEventStep s (next s) (firstZeroBin s.capacity) ∧
      placeBricks s.endpoint s.capacity.reverse (firstZeroBin s.capacity) =
        (next s).capacity.reverse := (literal_rest_block s).choose_spec
  let state : ℕ → RestState := fun e => Nat.rec initial (fun _ s => next s) e
  have state_zero : state 0 = initial := rfl
  have state_succ (e : ℕ) : state (e + 1) = next (state e) := rfl
  let bin : ℕ → ℕ := fun e => match e with
    | 0 => 1
    | e + 1 => firstZeroBin (state e).capacity
  have block (e : ℕ) :
      RestEventStep (state e) (state (e + 1)) (bin (e + 1)) ∧
      placeBricks (state e).endpoint (state e).capacity.reverse (bin (e + 1)) =
        (state (e + 1)).capacity.reverse := by
    simpa only [state_succ, bin] using next_spec (state e)
  have run (d N : ℕ) : placeBricks N (trajectory N) d = trajectory (N + d) := by
    induction d generalizing N with
    | zero => simp [placeBricks]
    | succ d ih =>
      change placeBricks (N + 1) (trajectory (N + 1)) d = trajectory (N + (d + 1))
      simpa only [Nat.add_assoc, Nat.add_comm 1 d] using ih (N + 1)
  have coupling (e : ℕ) :
      (state e).capacity.reverse = trajectory (state e).endpoint := by
    induction e with
    | zero => simp [state_zero, initial, trajectory, step, transfer]
    | succ e ih =>
      have hb := (block e).2
      rw [ih, run] at hb
      rw [← hb, (block e).1.endpoint_eq]
  have clock : StrictMono (fun e => (state e).endpoint) :=
    strictMono_nat_of_lt_succ fun e => by
      rw [(block e).1.endpoint_eq]
      have := (block e).1.label_pos
      omega
  have cofinal (N : ℕ) : ∃ e, N ≤ (state e).endpoint :=
    ⟨N, clock.id_le N⟩
  have height_mono : Monotone (fun N => (trajectory N).length) :=
    monotone_nat_of_le_succ fun N => (reachable_invariants N).2.2.1
  have unbounded (h : ℕ) : ∃ e, h ≤ (state e).capacity.length := by
    obtain ⟨B, _, hB, _, _⟩ := birth_totality (h + 1) (by omega)
    obtain ⟨e, he⟩ := cofinal B
    have hm := height_mono he
    change (trajectory B).length ≤ (trajectory (state e).endpoint).length at hm
    rw [hB, ← coupling e, List.length_reverse] at hm
    exact ⟨e, by omega⟩
  let T : RestTrace := {
    state := state
    bin := bin
    step := fun e => (block e).1
    initial_endpoint := rfl
    initial_capacity := rfl
    initial_bin := rfl
    unbounded := unbounded }
  refine ⟨T, (fun _ => rfl), coupling, clock, cofinal, ?_, ?_⟩
  · intro e d
    change placeBricks (state e).endpoint (state e).capacity.reverse d = _
    rw [coupling e]
    exact run d (state e).endpoint
  · intro N hN
    have above : ∃ e, N < (state e).endpoint := by
      obtain ⟨e, he⟩ := cofinal (N + 1)
      exact ⟨e, by omega⟩
    let f := Nat.find above
    have hf : N < (state f).endpoint := Nat.find_spec above
    have hfpos : 0 < f := by
      by_contra hn
      have hz : f = 0 := by omega
      rw [hz, state_zero] at hf
      change N < 1 at hf
      omega
    let e := f - 1
    have hef : e + 1 = f := by dsimp [e]; omega
    have he : (state e).endpoint ≤ N := by
      have hm := Nat.find_min above (show e < f by dsimp [e]; omega)
      omega
    let d := N - (state e).endpoint
    have hd : d < bin (e + 1) := by
      rw [← hef, (block e).1.endpoint_eq] at hf
      dsimp [d]
      omega
    have hNd : N = (state e).endpoint + d := by dsimp [d]; omega
    refine ⟨e, d, hd, hNd, ?_⟩
    change trajectory N = placeBricks (state e).endpoint (state e).capacity.reverse d
    rw [coupling e, run, ← hNd]

#print axioms literal_trace_realization

end D5.S3.Combinatorics.GreedyBrick.LiteralRestTrace
