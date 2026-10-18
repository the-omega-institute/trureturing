/- GID: D5/S3/ObserverMemory/Algorithms/FixedResponseArithmetic
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/FixedResponseArithmetic
   mirror-E: none(waiver:unbounded-symbolic-execution)
   anchors: []
   utility: none
   digest: Executable endpoint-tagged progressions describe exact fixed-response update counts. -/

import D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution
import D5.S3.ObserverMemory.Prediction.FiniteOrbitPeriodBound
import D5.S3.ObserverMemory.Prediction.EventualCycleAverage
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.PeriodicPts.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.FixedResponseArithmetic

open GuardedPhaseExecution
open scoped BigOperators

universe u v w
variable {Q : Type u} {A : Type v} {R : Type w}

/-- The genuine successor is undefined at a halt. -/
def successor (prog : Q → Instruction Q A R) (reply : A → R) (x : Q) : Option Q :=
  match prog x with
  | .read a k => some (k (reply a))
  | .update y => some y
  | .halt => none

/-- Totalization has a separate absorbing sink, not a halt self-loop. -/
def step (prog : Q → Instruction Q A R) (reply : A → R) : Option Q → Option Q
  | none => none
  | some x => successor prog reply x

/-- Only a real update instruction contributes unit weight. -/
def weight (prog : Q → Instruction Q A R) : Option Q → Nat
  | none => 0
  | some x => match prog x with
    | .update _ => 1
    | _ => 0

private theorem iterate_none (prog : Q → Instruction Q A R) (reply : A → R)
    (n : Nat) : (step prog reply)^[n] none = none := by
  exact Function.iterate_fixed (f := step prog reply) rfl n

private theorem fixed_path_iff_iterate (prog : Q → Instruction Q A R) (reply : A → R)
    (x y : Q) (d : Nat) :
    FixedPath prog reply x y d ↔ ∃ n,
      (step prog reply)^[n] (some x) = some y ∧
      birkhoffSum (step prog reply) (weight prog) n (some x) = d := by
  constructor
  · intro path
    induction path with
    | refl x => exact ⟨0, rfl, rfl⟩
    | @read x a k y d hop tail ih =>
        obtain ⟨n, endpoint, count⟩ := ih
        refine ⟨n + 1, ?_, ?_⟩
        · simpa [Function.iterate_succ_apply, step, successor, hop] using endpoint
        · simpa [birkhoffSum_succ', step, successor, weight, hop] using count
    | @update x z y d hop tail ih =>
        obtain ⟨n, endpoint, count⟩ := ih
        refine ⟨n + 1, ?_, ?_⟩
        · simpa [Function.iterate_succ_apply, step, successor, hop] using endpoint
        · simp [birkhoffSum_succ', step, successor, weight, hop, count, Nat.add_comm]
  · rintro ⟨n, endpoint, count⟩
    induction n generalizing x d with
    | zero =>
        simp only [Function.iterate_zero, id_eq, Option.some.injEq] at endpoint
        subst y
        simpa [birkhoffSum_zero] using (count ▸ FixedPath.refl x)
    | succ n ih =>
        cases hop : prog x with
        | read a k =>
            have endpoint' : (step prog reply)^[n] (some (k (reply a))) = some y := by
              simpa [Function.iterate_succ_apply, step, successor, hop] using endpoint
            have count' : birkhoffSum (step prog reply) (weight prog) n
                (some (k (reply a))) = d := by
              simpa [birkhoffSum_succ', step, successor, weight, hop] using count
            exact .read hop (ih _ _ endpoint' count')
        | update z =>
            have endpoint' : (step prog reply)^[n] (some z) = some y := by
              simpa [Function.iterate_succ_apply, step, successor, hop] using endpoint
            have count' : 1 + birkhoffSum (step prog reply) (weight prog) n (some z) = d := by
              simpa [birkhoffSum_succ', step, successor, weight, hop] using count
            have path := ih z _ endpoint' rfl
            convert FixedPath.update hop path using 1; omega
        | halt =>
            simp [Function.iterate_succ_apply, step, successor, hop, iterate_none] at endpoint

private theorem periodic_sum {Y : Type*} (f : Y → Y) (g : Y → Nat)
    {p : Nat} (hp : 0 < p) {y : Y} (hy : Function.IsPeriodicPt f p y) (n : Nat) :
    birkhoffSum f g n y = (n / p) * birkhoffSum f g p y +
      birkhoffSum f g (n % p) y := by
  have h := Prediction.EventualCycleAverage.sum_cycle_mod_eq_blocks_remainder hp
    (fun i : Fin p => (g ((f^[i.val]) y) : Real)) n
  simp only [hy.iterate_mod_apply] at h
  exact_mod_cast h

private theorem collision_values {Y : Type*} (f : Y → Y) (g : Y → Nat)
    (x : Y) {mu p : Nat} (hp : 0 < p)
    (collision : (f^[mu + p]) x = (f^[mu]) x)
    (m r : Nat) (hr : r < p) :
    (f^[mu + m * p + r]) x = (f^[mu + r]) x ∧
      birkhoffSum f g (mu + m * p + r) x =
        birkhoffSum f g (mu + r) x + m * birkhoffSum f g p ((f^[mu]) x) := by
  have hy : Function.IsPeriodicPt f p ((f^[mu]) x) := by
    change (f^[p]) ((f^[mu]) x) = (f^[mu]) x
    simpa only [Nat.add_comm mu p, Function.iterate_add_apply] using collision
  have hmod : (m * p + r) % p = r := by simp [Nat.add_mod, Nat.mod_eq_of_lt hr]
  have hdiv : (m * p + r) / p = m := by
    simp [Nat.add_div, Nat.mul_div_left _ hp, Nat.mod_eq_of_lt hr,
      Nat.div_eq_of_lt hr, hp, hr]
  constructor
  · rw [show mu + m * p + r = (m * p + r) + mu by omega,
      Function.iterate_add_apply, ← hy.iterate_mod_apply, hmod]
    rw [show mu + r = r + mu by omega, Function.iterate_add_apply]
  · rw [show mu + m * p + r = mu + (m * p + r) by omega,
      birkhoffSum_add_right_apply, periodic_sum f g hp hy, hmod, hdiv,
      birkhoffSum_add_right_apply]
    omega

/-- Each record keeps its actual endpoint and the natural progression coefficients. -/
structure Record (Q : Type u) where
  endpoint : Option Q
  offset : Nat
  increment : Nat

/-- All valid bounded collisions are scanned, with every step residue retained.
Singleton records cover the bounded prefix. Coefficients require no choice. -/
def records [Fintype Q] [DecidableEq Q]
    (prog : Q → Instruction Q A R) (reply : A → R) (x : Q) : List (Record Q) :=
  let f := step prog reply
  let g := weight prog
  let N := Fintype.card (Option Q)
  (List.range N).map (fun t => ⟨(f^[t]) (some x), birkhoffSum f g t (some x), 0⟩) ++
  (List.range N).flatMap (fun mu =>
    (List.range (N + 1)).flatMap (fun p =>
      if 0 < p ∧ mu + p ≤ N ∧ (f^[mu + p]) (some x) = (f^[mu]) (some x) then
        (List.range p).map (fun r =>
          ⟨(f^[mu + r]) (some x), birkhoffSum f g (mu + r) (some x),
            birkhoffSum f g p ((f^[mu]) (some x))⟩)
      else []))

/-- Exact membership in the endpoint-tagged union of natural progressions. -/
def Supports (data : List (Record Q)) (y : Q) (d : Nat) : Prop :=
  ∃ rec ∈ data, rec.endpoint = some y ∧ ∃ m, d = rec.offset + rec.increment * m

private theorem records_iff_iterate [Fintype Q] [DecidableEq Q]
    (prog : Q → Instruction Q A R) (reply : A → R) (x y : Q) (d : Nat) :
    Supports (records prog reply x) y d ↔ ∃ n,
      (step prog reply)^[n] (some x) = some y ∧
      birkhoffSum (step prog reply) (weight prog) n (some x) = d := by
  let f := step prog reply
  let g := weight prog
  let N := Fintype.card (Option Q)
  constructor
  · rintro ⟨rec, hrec, endpoint, m, count⟩
    simp only [records, List.mem_append, List.mem_map, List.mem_flatMap,
      List.mem_range] at hrec
    rcases hrec with ⟨t, ht, rfl⟩ | ⟨mu, hmu, p, hpb, hrec⟩
    · exact ⟨t, endpoint, by simpa using count.symm⟩
    · split_ifs at hrec with valid
      · simp only [List.mem_map, List.mem_range] at hrec
        obtain ⟨r, hr, rfl⟩ := hrec
        obtain ⟨he, hw⟩ := collision_values f g (some x) valid.1 valid.2.2 m r hr
        refine ⟨mu + m * p + r, he.trans endpoint, ?_⟩
        exact hw.trans (by simpa only [Nat.mul_comm] using count.symm)
      · simp at hrec
  · rintro ⟨n, endpoint, count⟩
    obtain ⟨mu, p, hp, bound, periodic⟩ :=
      Prediction.FiniteOrbitPeriodBound.finite_orbit_and_readout_eventually_periodic
        f g (some x)
    have collision : (f^[mu + p]) (some x) = (f^[mu]) (some x) :=
      (periodic mu le_rfl).1
    by_cases hn : n < mu
    · refine ⟨⟨(f^[n]) (some x), birkhoffSum f g n (some x), 0⟩, ?_, endpoint, 0, ?_⟩
      · apply List.mem_append_left
        exact List.mem_map.mpr ⟨n, List.mem_range.mpr (by omega), rfl⟩
      · simpa using count.symm
    · let m := (n - mu) / p
      let r := (n - mu) % p
      have hr : r < p := Nat.mod_lt _ hp
      have hn' : mu + m * p + r = n := by
        have : m * p + r = n - mu := by
          dsimp [m, r]
          simpa only [Nat.mul_comm] using Nat.div_add_mod (n - mu) p
        omega
      obtain ⟨he, hw⟩ := collision_values f g (some x) hp collision m r hr
      rw [hn'] at he hw
      refine ⟨⟨(f^[mu + r]) (some x), birkhoffSum f g (mu + r) (some x),
        birkhoffSum f g p ((f^[mu]) (some x))⟩, ?_, he.symm.trans endpoint, m, ?_⟩
      · apply List.mem_append_right
        apply List.mem_flatMap.mpr
        refine ⟨mu, List.mem_range.mpr (by omega), ?_⟩
        apply List.mem_flatMap.mpr
        refine ⟨p, List.mem_range.mpr (by omega), ?_⟩
        rw [if_pos (show 0 < p ∧ mu + p ≤ N ∧
          (f^[mu + p]) (some x) = (f^[mu]) (some x) from ⟨hp, bound, collision⟩)]
        exact List.mem_map.mpr ⟨r, List.mem_range.mpr hr, rfl⟩
      · simpa only [Nat.mul_comm] using count.symm.trans hw

/-- For every finite table, endpoint and natural weight, the executable records
describe precisely the original paths, including empty paths and halt endpoints. -/
theorem fixed_path_iff_support [Fintype Q] [DecidableEq Q]
    (prog : Q → Instruction Q A R) (reply : A → R) (x y : Q) (d : Nat) :
    FixedPath prog reply x y d ↔ Supports (records prog reply x) y d := by
  exact (fixed_path_iff_iterate prog reply x y d).trans
    (records_iff_iterate prog reply x y d).symm

#print axioms fixed_path_iff_support

end D5.S3.ObserverMemory.Algorithms.FixedResponseArithmetic
