/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2Words
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeJ2Words
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Five literal native J2 words have their actual independently specified ports. -/
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleOwnership
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeSwitches

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2Words

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleOwnership
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeSwitches
open Equiv Fin.NatCast

/-- The three actual right ports, with labels p=0, q=m and v=m-1. -/
def rightPort (m : ℕ) (i : Fin 3) : Configuration m :=
  let s := Equiv.swap (⟨m - 1, by omega⟩ : Fin (m + 1)) (Fin.last m)
  match i.val with
  | 0 => finRotate (m + 1) ^ m
  | 1 => s
  | _ => s * (b m * c m)

/-- The actual left port is across its literal v-terminal b edge. -/
def leftPort (m : ℕ) (i : Fin 3) : Configuration m := rightPort m i * b m

/-- Exchange the two actual marked labels p and q. -/
def bar {m : ℕ} (z : Configuration m) : Configuration m :=
  Equiv.swap (0 : Fin (m + 1)) (Fin.last m) * z

/-- Five words in actual prefix-reversal generators, not assumed factor paths. -/
def word (m : ℕ) (i : Fin 5) : List (Configuration m) :=
  let repeatedCH := (List.replicate (m - 3) ([c m] ++ uWord m m)).flatten
  match i.val with
  | 0 => [a m, b m, c m] ++ uWord m (m - 2) ++ [c m] ++ uWord m (m - 1)
  | 1 => (List.replicate (m - 1) [a m, b m]).flatten ++ repeatedCH ++ [c m, a m]
  | 2 => [a m] ++ repeatedCH ++ [c m, a m, b m, a m]
  | 3 => [a m, c m] ++ uWord m (m - 2)
  | _ => [a m, b m, c m] ++ uWord m (m - 1)

/-- Starts are actual ports defined independently of the words. -/
def wordStart (m : ℕ) (i : Fin 5) : Configuration m :=
  match i.val with
  | 0 => rightPort m 0
  | 1 => leftPort m 0
  | 2 => rightPort m 1
  | 3 => leftPort m 2
  | _ => bar (rightPort m 0)

/-- Finishes are the five required independently specified J2 port pairs. -/
def wordFinish (m : ℕ) (i : Fin 5) : Configuration m :=
  match i.val with
  | 0 => rightPort m 2
  | 1 => bar (leftPort m 1)
  | 2 => bar (leftPort m 2)
  | 3 => bar (rightPort m 2)
  | _ => bar (rightPort m 1)

/-- The independently specified five J2 edge counts. -/
def wordLength (m : ℕ) (i : Fin 5) : ℕ :=
  match i.val with
  | 0 => 4 * m
  | 1 => 2 * m * m - 2 * m - 6
  | 2 => 2 * m * m - 4 * m - 1
  | 3 => 2 * m - 1
  | _ => 2 * m + 2

private theorem h_product (m : ℕ) : (uWord m m).prod = b m := by
  rw [uWord_product, rotate_pow_eq_cycle, b_eq_cycle_a]
  congr 1
  have hr : (m : Fin (m + 1)) = Fin.last m := by apply Fin.ext; simp
  rw [hr, ← Fin.neg_last m, neg_neg]

private theorem b_sq (m : ℕ) : b m * b m = 1 := by
  apply Equiv.ext
  intro i
  exact PrefixReversalTripleOddNonGeneration.reverseIndex_involutive
    (L := m) (by omega) i

private theorem cb_long {m : ℕ} (hm : 5 ≤ m) :
    (c m * b m) ^ (m - 3) = (b m * c m) ^ 3 := by
  have hbc : (b m * c m) ^ m = 1 := by
    simpa only [eWord, List.prod_flatten, List.map_replicate, List.prod_replicate,
      List.prod_cons, List.prod_nil, mul_one] using
      (native_e_simple_trace (by omega : 3 ≤ m) (1 : Configuration m)).1
  have hcb : c m * b m = (b m * c m)⁻¹ := by
    symm
    apply inv_eq_of_mul_eq_one_right
    rw [mul_assoc, ← mul_assoc (c m), c_sq, one_mul, b_sq]
  rw [hcb, inv_pow]
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_add, show m - 3 + 3 = m by omega, hbc]

private theorem mod_two_cases {x n : ℕ} (_hn : 0 < n) (hx : x < 2 * n) :
    x % n = if x < n then x else x - n := by
  by_cases h : x < n
  · simp only [if_pos h, Nat.mod_eq_of_lt h]
  · rw [if_neg h, Nat.mod_eq_sub_mod (by omega : n ≤ x),
      Nat.mod_eq_of_lt (by omega : x - n < n)]

private theorem swap_val {m : ℕ} (x y i : Fin (m + 1)) :
    ((Equiv.swap x y) i).val =
      if i.val = x.val then y.val else if i.val = y.val then x.val else i.val := by
  classical
  simp only [Equiv.swap_apply_def, Fin.ext_iff]
  split_ifs <;> rfl

private theorem rotate_val (m k : ℕ) (i : Fin (m + 1)) :
    ((finRotate (m + 1) ^ k) i).val = (i.val + k) % (m + 1) := by
  simp only [rotate_pow_eq_cycle, finCycle_apply, Fin.val_add, Fin.val_natCast]
  simp only [Nat.add_mod, Nat.mod_mod]

private theorem a_val (m : ℕ) (i : Fin (m + 1)) :
    ((a m) i).val = m - i.val := by
  rw [a_apply]
  simp only [Fin.val_rev]
  omega

macro "solve_j2_coordinate" m:term : tactic => `(tactic| {
  simp only [wordStart, wordFinish, word, leftPort, rightPort, bar,
    List.prod_append, List.prod_flatten, List.map_replicate, List.prod_replicate,
    List.prod_cons, List.prod_nil, mul_one, h_product, uWord_product,
    ab_eq_rotate, cb_long (by omega : 5 ≤ $m)]
  apply Equiv.ext
  intro j
  apply Fin.ext
  have hj := j.isLt
  have hposition : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨
      j.val = $m - 3 ∨ j.val = $m - 2 ∨ j.val = $m - 1 ∨ j.val = $m ∨
      (4 ≤ j.val ∧ j.val < $m - 3) := by omega
  rcases hposition with h | h | h | h | h | h | h | h | h
  all_goals
    simp (disch := omega) only [h, Equiv.Perm.mul_apply, a_val, b_apply, c_apply,
      rotate_val, native_bc_pow_val (by omega : 2 ≤ $m), swap_val,
      Fin.val_last, Fin.val_zero, mod_two_cases, if_pos, if_neg, ite_true, ite_false]
    <;> omega
})

set_option maxHeartbeats 800000 in
private theorem endpoint_0_large {m : ℕ} (hm : 8 ≤ m) :
    wordStart m 0 * (word m 0).prod = wordFinish m 0 := by
  solve_j2_coordinate m

set_option maxHeartbeats 800000 in
private theorem endpoint_1_large {m : ℕ} (hm : 8 ≤ m) :
    wordStart m 1 * (word m 1).prod = wordFinish m 1 := by
  solve_j2_coordinate m

set_option maxHeartbeats 800000 in
private theorem endpoint_2_large {m : ℕ} (hm : 8 ≤ m) :
    wordStart m 2 * (word m 2).prod = wordFinish m 2 := by
  solve_j2_coordinate m

set_option maxHeartbeats 800000 in
private theorem endpoint_3_large {m : ℕ} (hm : 8 ≤ m) :
    wordStart m 3 * (word m 3).prod = wordFinish m 3 := by
  solve_j2_coordinate m

set_option maxHeartbeats 800000 in
private theorem endpoint_4_large {m : ℕ} (hm : 8 ≤ m) :
    wordStart m 4 * (word m 4).prod = wordFinish m 4 := by
  solve_j2_coordinate m

set_option maxHeartbeats 800000 in
/-- Each of the five literal words ends at its actual required port, for every
native size with at least three residual A labels. Factor-edge legality and
exhaustive path-component support are separate obligations. -/
theorem native_j2_word_endpoints {m : ℕ} (hm : 5 ≤ m) (i : Fin 5) :
    wordStart m i * (word m i).prod = wordFinish m i := by
  by_cases hlarge : 8 ≤ m
  · fin_cases i
    · exact endpoint_0_large hlarge
    · exact endpoint_1_large hlarge
    · exact endpoint_2_large hlarge
    · exact endpoint_3_large hlarge
    · exact endpoint_4_large hlarge
  · have hsize : m = 5 ∨ m = 6 ∨ m = 7 := by omega
    rcases hsize with rfl | rfl | rfl
    all_goals fin_cases i <;> (set_option maxRecDepth 4096 in decide)

#print axioms native_j2_word_endpoints

/-- All five literal words have their exact required lengths, for every native
size with at least three residual A labels. -/
theorem native_j2_word_lengths {m : ℕ} (hm : 5 ≤ m) (i : Fin 5) :
    (word m i).length = wordLength m i := by
  have h3 : m - 3 + 3 = m := by omega
  have h1 : m - 1 + 1 = m := by omega
  have hrepeat : (m - 3) * (2 * m + 1 + 1) + 4 * m + 6 = 2 * m * m := by
    nlinarith
  fin_cases i
  all_goals
    simp [word, wordLength, uWord_length]
    omega

#print axioms native_j2_word_lengths

end D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2Words
