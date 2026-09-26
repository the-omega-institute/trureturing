/- GID: D5/S3/Combinatorics/WheelHivExtinctionRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/WheelHivExtinctionRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/WheelHivExtinctionRefutation.claim; result=D5/S3/Combinatorics/WheelHivExtinctionRefutation.result; claim=D5/S3/Combinatorics/WheelHivExtinctionRefutation.claim
   digest: Refutes Conjecture 1 of Espinosa-Garcia et al., arXiv:2608.00340v1: in the Mukwembi HIV cellular automaton on the wheel W_18 with replacement parameter R = 4 every admissible initial state dies out by time 25, so 4 lies in the extinction set of W_18, which the conjecture puts equal to 3 together with all R >= 17. -/

/-
proof_shape: result: content
escape_witness: form (2), the public conclusion `result` itself: a bit-sliced simulation runs all
  2^18 admissible initial states of W_18 at once, one bit per state, in masks of the infected and
  dead vertices; the masks at time 0 have bit j of vertex v equal to bit v of j (`testBit_coord`,
  from the doubling construction `testBit_rep`), counting masks give "at least k infected
  neighbours" bit by bit (`testBit_ge`), one masked step decodes to one step of the rules at every
  bit (`step_decode`, through `count_nb`), so the masks after t steps decode to the t-th state of
  every initial state (`iter_decode`); the kernel evaluates the masks after 25 steps to zero
  (`clear25`), hence every admissible initial state dies out by time 25 (`extinct`, with the code
  `bitsValue` of the initial state)
admission_basis: open-problem-resolution (issue #10263)
Direct frozen dependencies: D5/S0/Computability/PhysicalDivider/WordArithmetic: `bitsValue`
  (statement_id sha256:0af0922a52ff96d028cb9f4bec5193f78a5e7bd5682a53e4e7d741355640fe55),
  `bitsValue_fixedBits` (sha256:17079846beefc5a86338e787baba95b7d10d646add645d512f59fd75d81488d3) and
  `fixedBits_bitsValue` (sha256:a7e5115d9e62ba2f7af0aa652d5e4b129d6eb5a886fc3e0a12002ba1e57c4607)
-/

import D5.S0.Computability.PhysicalDivider.WordArithmetic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.WheelHivExtinctionRefutation

open Lax51Proofs.RamToTM (bitsValue bitsValue_fixedBits fixedBits_bitsValue)

/-!
Espinosa-García, Figueroa, Fresán-Figueroa, Maldonado, Sánchez-Solís, *Extinction thresholds in a
graph-based model of HIV infection dynamics*, arXiv:2608.00340v1, Section 2 and Conjecture 1. A state
of a graph `G` is `f : V(G) → {0, 1, 2}` (healthy, infected, dead); an admissible initial state takes
values in `{0, 1}`. With `d_{t,I}(v)` the number of infected neighbours of `v`, a healthy vertex
becomes infected when `d ≥ 1` and stays healthy otherwise, an infected vertex dies, and a dead vertex
is replaced by an infected one when `d ≥ R` and by a healthy one otherwise. The extinction set `𝓔(G)`
is the set of positive `R` for which every admissible initial state reaches the all-healthy state.
Conjecture 1: `𝓔(W_n) = {3} ∪ {R ≥ n - 1}` for even `n ≥ 12` and `𝓔(W_n) = {4} ∪ {R ≥ n - 1}` for
odd `n ≥ 17`, where `W_n = K₁ ∨ C_{n-1}`. It fails at `n = 18`: `4 ∈ 𝓔(W_18)`.
-/

/-- The wheel `W_n = K₁ ∨ C_{n-1}` on `Fin n`: vertex `0` is the hub, joined to every other vertex, and
the cycle visits `1, 2, …, n - 1` in order and closes from `n - 1` back to `1`. -/
def wheelAdj (n : ℕ) (u v : Fin n) : Prop :=
  u ≠ v ∧ (u.val = 0 ∨ v.val = 0 ∨ u.val + 1 = v.val ∨ v.val + 1 = u.val ∨
    (u.val = 1 ∧ v.val = n - 1) ∨ (v.val = 1 ∧ u.val = n - 1))

instance (n : ℕ) : DecidableRel (wheelAdj n) := fun u v => by
  unfold wheelAdj; infer_instance

/-- `d_{t,I}(v)`: the number of neighbours of `v` that are infected in the state `f`. -/
def infectedCount {n : ℕ} (adj : Fin n → Fin n → Prop) [DecidableRel adj]
    (f : Fin n → Fin 3) (v : Fin n) : ℕ :=
  (Finset.univ.filter fun u => adj v u ∧ f u = 1).card

/-- One step of the rules with replacement parameter `R` (`0` healthy, `1` infected, `2` dead). -/
def step {n : ℕ} (adj : Fin n → Fin n → Prop) [DecidableRel adj] (R : ℕ)
    (f : Fin n → Fin 3) : Fin n → Fin 3 := fun v =>
  if f v = 1 then 2
  else if f v = 0 then (if infectedCount adj f v = 0 then 0 else 1)
  else (if R ≤ infectedCount adj f v then 1 else 0)

/-- The extinction set: the positive `R` for which every admissible initial state `f₀` reaches the
all-healthy state. -/
def extinctionSet (n : ℕ) (adj : Fin n → Fin n → Prop) [DecidableRel adj] : Set ℕ :=
  {R | 0 < R ∧ ∀ f₀ : Fin n → Fin 2,
    ∃ t, (step adj R)^[t] (fun v => (f₀ v).castSucc) = fun _ => 0}

/-- Conjecture 1 of arXiv:2608.00340v1. -/
def claim : Prop :=
  (∀ n : ℕ, Even n → 12 ≤ n → extinctionSet n (wheelAdj n) = {3} ∪ {R | n - 1 ≤ R}) ∧
  (∀ n : ℕ, Odd n → 17 ≤ n → extinctionSet n (wheelAdj n) = {4} ∪ {R | n - 1 ≤ R})

/-! Bit-sliced simulation of `W_18` with `R = 4`: bit `j` of a mask stands for the initial state
whose vertex `v` is infected exactly when bit `v` of `j` is set. -/

private def rep (b w : ℕ) : ℕ → ℕ
  | 0 => b
  | k + 1 => rep b w k ||| (rep b w k <<< (w * 2 ^ k))

private def coord (v : ℕ) : ℕ := rep ((2 ^ 2 ^ v - 1) <<< 2 ^ v) (2 ^ (v + 1)) (17 - v)

private def ge (all : ℕ) : ℕ → List ℕ → ℕ
  | 0, _ => all
  | _ + 1, [] => 0
  | k + 1, x :: xs => ge all (k + 1) xs ||| (x &&& ge all k xs)

private def all18 : ℕ := 2 ^ 2 ^ 18 - 1

private def stepM (s : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  (List.finRange 18).map fun v =>
    ((((all18 ^^^ ((s.getD v.val (0, 0)).1 ||| (s.getD v.val (0, 0)).2)) &&&
        ge all18 1 (((List.finRange 18).filter fun u => decide (wheelAdj 18 v u)).map
          fun u => (s.getD u.val (0, 0)).1)) |||
      ((s.getD v.val (0, 0)).2 &&& ge all18 4 (((List.finRange 18).filter
          fun u => decide (wheelAdj 18 v u)).map fun u => (s.getD u.val (0, 0)).1))),
      (s.getD v.val (0, 0)).1)

private def decode (s : List (ℕ × ℕ)) (j : ℕ) : Fin 18 → Fin 3 := fun v =>
  if (s.getD v.val (0, 0)).1.testBit j then 1
  else if (s.getD v.val (0, 0)).2.testBit j then 2 else 0

private def iterM : ℕ → List (ℕ × ℕ) → List (ℕ × ℕ)
  | 0, s => s
  | t + 1, s => iterM t (stepM s)

private def initM : List (ℕ × ℕ) := (List.finRange 18).map fun v => (coord v.val, 0)

private def allClear (s : List (ℕ × ℕ)) : Bool := s.all fun p => p.1 == 0 && p.2 == 0

set_option maxRecDepth 100000 in
/-- Conjecture 1 fails at `n = 18`: every admissible initial state of `W_18` dies out by time 25 when
`R = 4`, so `4 ∈ 𝓔(W_18)`, while the conjectured set `{3} ∪ {R ≥ 17}` does not contain `4`. -/
theorem result : ¬ claim := by
  have rep_lt : ∀ (b w : ℕ) (hb : b < 2 ^ w), ∀ k, rep b w k < 2 ^ (w * 2 ^ k) := by
    intro b w hb k
    induction k with
    | zero => simpa [rep] using hb
    | succ k ih =>
      simp only [rep]
      have h1 : rep b w k <<< (w * 2 ^ k) < 2 ^ (w * 2 ^ (k + 1)) := by
        rw [Nat.shiftLeft_eq, pow_succ, show w * (2 ^ k * 2) = w * 2 ^ k + w * 2 ^ k by ring, pow_add]
        exact Nat.mul_lt_mul_of_pos_right ih (by positivity)
      have h0 : rep b w k < 2 ^ (w * 2 ^ (k + 1)) :=
        lt_of_lt_of_le ih (Nat.pow_le_pow_right (by norm_num) (by rw [pow_succ]; nlinarith [Nat.zero_le w, pow_pos (show 0 < 2 by norm_num) k]))
      exact Nat.or_lt_two_pow h0 h1
  have testBit_rep : ∀ (b w : ℕ) (hb : b < 2 ^ w), ∀ k j, j < w * 2 ^ k → (rep b w k).testBit j = b.testBit (j % w) := by
    intro b w hb k
    induction k with
    | zero => intro j hj; simp [rep, Nat.mod_eq_of_lt (by simpa using hj)]
    | succ k ih =>
      intro j hj
      simp only [rep, Nat.testBit_or, Nat.testBit_shiftLeft]
      by_cases hjk : j < w * 2 ^ k
      · rw [ih j hjk]
        simp [show ¬ (w * 2 ^ k ≤ j) by omega]
      · have hlow : (rep b w k).testBit j = false :=
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (rep_lt b w hb k) (Nat.pow_le_pow_right (by norm_num) (by omega)))
        have hj' : j - w * 2 ^ k < w * 2 ^ k := by
          rw [pow_succ, show w * (2 ^ k * 2) = 2 * (w * 2 ^ k) by ring] at hj; omega
        rw [hlow, ih _ hj']
        have : (j - w * 2 ^ k) % w = j % w := by
          conv_rhs => rw [show j = (j - w * 2 ^ k) + w * 2 ^ k by omega]
          rw [Nat.add_mul_mod_self_left]
        simp [show w * 2 ^ k ≤ j by omega, this]
  have testBit_coord : ∀ (v : ℕ) (hv : v < 18) (j : ℕ) (hj : j < 2 ^ 18), (coord v).testBit j = j.testBit v := by
    intro v hv j hj
    unfold coord
    have hb : (2 ^ 2 ^ v - 1) <<< 2 ^ v < 2 ^ 2 ^ (v + 1) := by
      rw [Nat.shiftLeft_eq, pow_succ, pow_mul, sq]
      have h1 : 2 ^ 2 ^ v - 1 < 2 ^ 2 ^ v := Nat.sub_lt (by positivity) (by norm_num)
      exact Nat.mul_lt_mul_of_pos_right h1 (by positivity)
    rw [testBit_rep _ _ hb _ _ (by
      rw [← pow_add, show v + 1 + (17 - v) = 18 by omega]; exact hj)]
    rw [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
    rw [Nat.testBit_eq_decide_div_mod_eq (x := j), Nat.mod_pow_succ]
    have h1 : j % 2 ^ v < 2 ^ v := Nat.mod_lt _ (by positivity)
    have h2 : j / 2 ^ v % 2 < 2 := Nat.mod_lt _ (by norm_num)
    generalize j % 2 ^ v = t at *
    generalize j / 2 ^ v % 2 = d at *
    generalize 2 ^ v = P at *
    rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
    · simp; omega
    · simp; omega
  have testBit_ge : ∀ (all : ℕ) (j : ℕ) (hall : all.testBit j = true), ∀ (xs : List ℕ) (k : ℕ), (ge all k xs).testBit j = decide (k ≤ (xs.filter fun x => x.testBit j).length) := by
    intro all j hall xs
    induction xs with
    | nil => intro k; cases k <;> simp [ge, hall]
    | cons x xs ih =>
      intro k
      cases k with
      | zero => simp [ge, hall]
      | succ k =>
        simp only [ge, Nat.testBit_or, Nat.testBit_and, ih, List.filter_cons]
        by_cases hx : x.testBit j = true
        · simp [hx]; omega
        · simp [hx]

  have testBit_bits : ∀ (bs : List Bool) (i : ℕ), (bitsValue bs).testBit i = bs.getD i false := by
    intro bs
    induction bs with
    | nil => intro i; simp [bitsValue]
    | cons b bs ih =>
      intro i
      cases i with
      | zero => simp [bitsValue]
      | succ i => simp [bitsValue, Nat.testBit_bit_succ, ih]
  have bits_lt : ∀ bs : List Bool, bitsValue bs < 2 ^ bs.length := by
    intro bs
    have h := bitsValue_fixedBits bs.length (bitsValue bs)
    rw [fixedBits_bitsValue] at h
    rw [h]
    exact Nat.mod_lt _ (by positivity)
  have card_eq_length : ∀ (p : Fin 18 → Prop) [DecidablePred p], (Finset.univ.filter p).card = ((List.finRange 18).filter fun u => decide (p u)).length := by
    intro p _
    rw [Fin.univ_def]
    rfl
  have getD_stepM : ∀ (s : List (ℕ × ℕ)) (v : Fin 18), (stepM s).getD v.val (0, 0) = ((((all18 ^^^ ((s.getD v.val (0, 0)).1 ||| (s.getD v.val (0, 0)).2)) &&& ge all18 1 (((List.finRange 18).filter fun u => decide (wheelAdj 18 v u)).map fun u => (s.getD u.val (0, 0)).1)) ||| ((s.getD v.val (0, 0)).2 &&& ge all18 4 (((List.finRange 18).filter fun u => decide (wheelAdj 18 v u)).map fun u => (s.getD u.val (0, 0)).1))), (s.getD v.val (0, 0)).1) := by
    intro s v
    simp [stepM, List.getD_eq_getElem?_getD, v.isLt]
  have count_nb : ∀ (s : List (ℕ × ℕ)) (j : ℕ) (v : Fin 18), ((((List.finRange 18).filter fun u => decide (wheelAdj 18 v u)).map fun u => (s.getD u.val (0, 0)).1).filter fun x => x.testBit j).length = infectedCount (wheelAdj 18) (decode s j) v := by
    intro s j v
    unfold infectedCount
    rw [card_eq_length, List.filter_map, List.length_map, List.filter_filter]
    congr 1
    apply List.filter_congr
    intro u _
    simp only [decode, Function.comp]
    split_ifs with h1 h2
    · rw [h1]; simp
    · rw [Bool.not_eq_true] at h1; rw [h1]; simp
    · rw [Bool.not_eq_true] at h1; rw [h1]; simp
  have all18_bit : ∀ (j : ℕ) (hj : j < 2 ^ 18), all18.testBit j = true := by
    intro j hj
    simp only [all18, Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
    exact hj
  have step_decode : ∀ (s : List (ℕ × ℕ)) (j : ℕ) (hj : j < 2 ^ 18)
    (hd : ∀ v : Fin 18, ¬ ((s.getD v.val (0, 0)).1.testBit j = true ∧
      (s.getD v.val (0, 0)).2.testBit j = true)), decode (stepM s) j = step (wheelAdj 18) 4 (decode s j) ∧ ∀ v : Fin 18, ¬ (((stepM s).getD v.val (0, 0)).1.testBit j = true ∧ ((stepM s).getD v.val (0, 0)).2.testBit j = true) := by
    intro s j hj hd
    have hall := all18_bit j hj
    have hge := testBit_ge all18 j hall
    constructor
    · funext v
      have hc := count_nb s j v
      simp only [decode, getD_stepM, step, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, hall, hge, hc]
      have hdv := hd v
      by_cases h1 : (s.getD v.val (0, 0)).1.testBit j = true <;>
      by_cases h2 : (s.getD v.val (0, 0)).2.testBit j = true <;>
      simp_all; split_ifs <;> simp_all
    · intro v
      have hdv := hd v
      simp only [getD_stepM, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, hall]
      by_cases h1 : (s.getD v.val (0, 0)).1.testBit j = true <;> simp_all
  have iter_decode : ∀ (j : ℕ) (hj : j < 2 ^ 18), ∀ (t : ℕ) (s : List (ℕ × ℕ)), (∀ v : Fin 18, ¬ ((s.getD v.val (0, 0)).1.testBit j = true ∧ (s.getD v.val (0, 0)).2.testBit j = true)) → decode (iterM t s) j = (step (wheelAdj 18) 4)^[t] (decode s j) := by
    intro j hj t
    induction t with
    | zero => intro s _; rfl
    | succ t ih =>
      intro s hd
      obtain ⟨h1, h2⟩ := step_decode s j hj hd
      rw [iterM, ih _ h2, h1, Function.iterate_succ_apply]
  have clear25 : allClear (iterM 25 initM) = true := by
    decide +kernel
  have extinct : ∀ (f₀ : Fin 18 → Fin 2), (step (wheelAdj 18) 4)^[25] (fun v => (f₀ v).castSucc) = fun _ => 0 := by
    intro f₀
    let bs : List Bool := (List.finRange 18).map fun v => decide (f₀ v = 1)
    have hlen : bs.length = 18 := by simp [bs]
    have hj : bitsValue bs < 2 ^ 18 := hlen ▸ bits_lt bs
    have hbit : ∀ v : Fin 18, (bitsValue bs).testBit v.val = decide (f₀ v = 1) := by
      intro v
      rw [testBit_bits]
      simp [bs, List.getD_eq_getElem?_getD, v.isLt]
    have hinit : ∀ v : Fin 18, initM.getD v.val (0, 0) = (coord v.val, 0) := by
      intro v; simp [initM, List.getD_eq_getElem?_getD, v.isLt]
    have hd0 : ∀ v : Fin 18, ¬ ((initM.getD v.val (0, 0)).1.testBit (bitsValue bs) = true ∧
        (initM.getD v.val (0, 0)).2.testBit (bitsValue bs) = true) := by
      intro v; rw [hinit]; simp
    have hdec : decode initM (bitsValue bs) = fun v => (f₀ v).castSucc := by
      funext v
      simp only [decode, hinit, testBit_coord v.val v.isLt _ hj, hbit, Nat.zero_testBit]
      generalize f₀ v = a
      fin_cases a <;> rfl
    have hstep_len : ∀ s, (stepM s).length = 18 := by intro s; simp [stepM]
    have hiter_len : ∀ t s, s.length = 18 → (iterM t s).length = 18 := by
      intro t
      induction t with
      | zero => intro s h; exact h
      | succ t ih => intro s _; exact ih _ (hstep_len s)
    have hlen25 : (iterM 25 initM).length = 18 := hiter_len 25 initM (by simp [initM])
    have hall := iter_decode (bitsValue bs) hj 25 initM hd0
    rw [hdec] at hall
    rw [← hall]
    funext v
    have hc := clear25
    simp only [allClear, List.all_eq_true] at hc
    have hmem : (iterM 25 initM).getD v.val (0, 0) ∈ iterM 25 initM := by
      rw [List.getD_eq_getElem _ _ (by rw [hlen25]; exact v.isLt)]
      exact List.getElem_mem _
    have hv := hc _ hmem
    simp only [Bool.and_eq_true, beq_iff_eq] at hv
    simp only [decode]
    rw [hv.1, hv.2]
    simp

  intro h
  have h18 := h.1 18 ⟨9, rfl⟩ (by norm_num)
  have h4 : (4 : ℕ) ∈ extinctionSet 18 (wheelAdj 18) := ⟨by norm_num, fun f₀ => ⟨25, extinct f₀⟩⟩
  rw [h18] at h4
  simp at h4

#print axioms result

end D5.S3.Combinatorics.WheelHivExtinctionRefutation
