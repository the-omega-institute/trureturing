/- GID: D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SurvivingSeams
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SurvivingSeams
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact actual seam coordinates and seeds for the five surviving J2 words. -/
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingModel
set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingEdges

open D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2Words
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedPorts
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2EdgeClassification
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2CutLabels
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2MarkedInventory
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarGrafting
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleComplement
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCircleOwnership
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeCoreSplicing
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarContacts
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeSwitches
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeContactIteration
open D5.S3.Combinatorics.Graph.PrefixReversal.NativeF2NativeInventory
open Equiv Fin.NatCast
open D5.S3.Combinatorics.Graph.Walks.LeafNonbacktrackingComponent

open private contactAnchor_val from
  D5.S3.Combinatorics.Graph.PrefixReversal.NativeStarContacts

private def j2Contact {m : Nat} (hm : 5 ≤ m) : Fin (m - 2) :=
  ⟨m - 3, by omega⟩

private theorem j2_swap_val {m : Nat} (x y i : Fin (m + 1)) :
    ((Equiv.swap x y) i).val =
      if i.val = x.val then y.val else if i.val = y.val then x.val else i.val := by
  classical
  simp only [Equiv.swap_apply_def, Fin.ext_iff]
  split_ifs <;> rfl

private theorem j2_rotate_val (m k : Nat) (i : Fin (m + 1)) :
    ((finRotate (m + 1) ^ k) i).val = (i.val + k) % (m + 1) := by
  simp only [rotate_pow_eq_cycle, finCycle_apply, Fin.val_add, Fin.val_natCast]
  simp only [Nat.add_mod, Nat.mod_mod]

private theorem j2_mod_two_cases {x n : Nat} (_hn : 0 < n) (hx : x < 2 * n) :
    x % n = if x < n then x else x - n := by
  by_cases h : x < n
  · simp only [if_pos h, Nat.mod_eq_of_lt h]
  · rw [if_neg h, Nat.mod_eq_sub_mod (by omega : n ≤ x),
      Nat.mod_eq_of_lt (by omega : x - n < n)]

/-- Only fixed-size offsets are split; m is arbitrary, not bounded. -/
macro "solve_j2_seam_coordinate" m:term : tactic => `(tactic| {
  simp only [wordStart, wordFinish, rightPort, leftPort, bar,
    NativeCoreSplicing.cutStart, cutGenerator, tCircleAnchor, lowerPort, gapAnchor, j2Contact,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, uWord_product, ab_eq_rotate]
  apply Equiv.ext
  intro i
  apply Fin.ext
  have hi := i.isLt
  have hposition : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨
      i.val = $m - 3 ∨ i.val = $m - 2 ∨ i.val = $m - 1 ∨ i.val = $m ∨
      (4 ≤ i.val ∧ i.val < $m - 3) := by omega
  rcases hposition with h | h | h | h | h | h | h | h | h
  all_goals
    simp (disch := omega) only [h, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
      pow_one, a_apply, Fin.val_rev,
      b_apply, c_apply, j2_rotate_val, native_bc_pow_val (by omega : 2 ≤ $m),
      j2_swap_val, contactAnchor_val, Fin.val_mk, Fin.val_last, Fin.val_zero,
      j2_mod_two_cases, if_pos, if_neg, ite_true, ite_false]
    <;> (try split_ifs) <;> omega
})

private theorem j2_h_product (m : Nat) : (uWord m m).prod = b m := by
  rw [uWord_product, rotate_pow_eq_cycle, b_eq_cycle_a]
  congr 1
  have hr : (m : Fin (m + 1)) = Fin.last m := by apply Fin.ext; simp
  rw [hr, ← Fin.neg_last m, neg_neg]

private theorem j2_cb_pow_succ (m t : Nat) :
    (c m * b m) ^ (t + 1) = c m * (b m * c m) ^ t * b m := by
  induction t with
  | zero => simp only [Nat.zero_add, pow_one, pow_zero, mul_one]
  | succ t ih =>
    calc
      _ = (c m * b m) ^ (t + 1) * (c m * b m) := pow_succ _ _
      _ = (c m * (b m * c m) ^ t * b m) * (c m * b m) := by rw [ih]
      _ = c m * ((b m * c m) ^ t * (b m * c m)) * b m := by
        simp only [mul_assoc]
      _ = c m * (b m * c m) ^ (t + 1) * b m := by rw [pow_succ]

private theorem j2_b_cb_pow (m t : Nat) :
    b m * (c m * b m) ^ t = (b m * c m) ^ t * b m := by
  induction t with
  | zero => simp only [pow_zero, mul_one, one_mul]
  | succ t ih =>
    calc
      _ = (b m * (c m * b m) ^ t) * (c m * b m) := by
        rw [pow_succ, mul_assoc]
      _ = ((b m * c m) ^ t * b m) * (c m * b m) := by rw [ih]
      _ = (b m * c m) ^ (t + 1) * b m := by
        rw [pow_succ]
        simp only [mul_assoc]

private theorem j2_bc_order {m : Nat} (hm : 5 ≤ m) :
    (b m * c m) ^ m = 1 := by
  simpa only [eWord, List.prod_flatten, List.map_replicate, List.prod_replicate,
    List.prod_cons, List.prod_nil, mul_one] using
    (native_e_simple_trace (by omega : 3 ≤ m) (1 : Configuration m)).1

/-- Actual c starting vertices before any repeated blocks. These six exact
identities are the seeds for all five word traces. -/
private theorem j2_word0_first_seed {m : Nat} (hm : 5 ≤ m) :
    wordStart m 0 * a m * b m = 1 := by
  solve_j2_seam_coordinate m

private theorem j2_word0_second_seed {m : Nat} (hm : 5 ≤ m) :
    wordStart m 0 * a m * b m * c m * (uWord m (m - 2)).prod =
      contactAnchor (j2Contact hm) := by
  solve_j2_seam_coordinate m

private theorem j2_word1_seed {m : Nat} (hm : 5 ≤ m) :
    wordStart m 1 * (a m * b m) ^ (m - 1) = a m := by
  solve_j2_seam_coordinate m

private theorem j2_word2_seed {m : Nat} (hm : 5 ≤ m) :
    wordStart m 2 * a m = contactAnchor (j2Contact hm) * b m := by
  solve_j2_seam_coordinate m

private theorem j2_word3_seed {m : Nat} (hm : 5 ≤ m) :
    wordStart m 3 * a m =
      contactAnchor (j2Contact hm) * (b m * c m) ^ (m - 1) := by
  solve_j2_seam_coordinate m

private theorem j2_word4_seed {m : Nat} (hm : 5 ≤ m) :
    wordStart m 4 * a m * b m =
      Equiv.swap (0 : Fin (m + 1)) (Fin.last m) := by
  solve_j2_seam_coordinate m

private theorem j2_reverse_t_seam {m : Nat}
    (p : Fin m ⊕ Fin (m - 2)) (x : Configuration m)
    (hx : x = NativeCoreSplicing.cutStart p * cutGenerator p * c m) :
    F2Seam m s(x, x * c m) := by
  left
  refine ⟨p, ?_⟩
  rw [hx]
  simp only [mul_assoc, c_sq, mul_one]
  exact Sym2.eq_swap

private theorem j2_reverse_e_seam {m : Nat} (j : Fin (m - 2)) (i : Fin m)
    (x : Configuration m)
    (hx : x = gapAnchor (contactAnchor j) i * b m * c m) :
    F2Seam m s(x, x * c m) := by
  right
  refine ⟨j, i, ?_⟩
  rw [hx]
  simp only [mul_assoc, c_sq, mul_one]
  exact Sym2.eq_swap

private theorem j2_lower_t_seam {m : Nat} (hm : 5 ≤ m) (j : Fin (m - 2)) :
    F2Seam m s(lowerPort j * b m, lowerPort j * b m * c m) := by
  have hj := j.isLt
  left
  refine ⟨Sum.inl ⟨j.val, by omega⟩, ?_⟩
  simp [NativeCoreSplicing.cutStart, cutGenerator, tCircleAnchor, gapAnchor, lowerPort,
    show j.val ≠ m - 1 by omega, show ¬ m - 2 ≤ j.val by omega]

private theorem j2_first_t_seam {m : Nat} (hm : 5 ≤ m) :
    F2Seam m s(a m, a m * c m) := by
  left
  refine ⟨Sum.inl ⟨m - 1, by omega⟩, ?_⟩
  simp [NativeCoreSplicing.cutStart, cutGenerator, show m - 2 ≤ m - 1 by omega]

/-- Word 1 has m-2 c steps. The initial one is the first core seam;
the remaining steps traverse the lower T chain in its actual direction. -/
private theorem j2_word1_repeated_c {m : Nat} (hm : 5 ≤ m) (t : Fin (m - 2)) :
    F2Seam m s(a m * (c m * b m) ^ t.val,
      a m * (c m * b m) ^ t.val * c m) := by
  by_cases ht : t.val = 0
  · simpa only [ht, pow_zero, mul_one] using j2_first_t_seam hm
  · let j : Fin (m - 2) := ⟨t.val - 1, by have ht' := t.isLt; omega⟩
    have he : a m * (c m * b m) ^ t.val = lowerPort j * b m := by
      rw [show t.val = (t.val - 1) + 1 by omega, j2_cb_pow_succ]
      simp only [lowerPort, j, mul_assoc]
    rw [he]
    exact j2_lower_t_seam hm j

/-- Word 2 has m-2 c steps, all from one complete actual contact supplier.
The gap index is exactly the ordinal of the c step, including the final c. -/
private theorem j2_word2_repeated_c {m : Nat} (hm : 5 ≤ m) (t : Fin (m - 2)) :
    F2Seam m
      s(contactAnchor (j2Contact hm) * b m * (c m * b m) ^ t.val,
        contactAnchor (j2Contact hm) * b m * (c m * b m) ^ t.val * c m) := by
  let i : Fin m := ⟨t.val, by have ht := t.isLt; omega⟩
  have he : contactAnchor (j2Contact hm) * b m * (c m * b m) ^ t.val =
      gapAnchor (contactAnchor (j2Contact hm)) i * b m := by
    rw [mul_assoc, j2_b_cb_pow]
    simp only [gapAnchor, i, mul_assoc]
  rw [he]
  exact Or.inr ⟨j2Contact hm, i, rfl⟩

private theorem j2_word0_first_c {m : Nat} (hm : 5 ≤ m) :
    F2Seam m s((1 : Configuration m), c m) := by
  let p : Fin m ⊕ Fin (m - 2) := Sum.inr (j2Contact hm)
  have he : NativeCoreSplicing.cutStart p * cutGenerator p * c m = 1 := by
    dsimp only [p]
    solve_j2_seam_coordinate m
  simpa only [one_mul] using j2_reverse_t_seam p 1 he.symm

private theorem j2_word0_second_c {m : Nat} (hm : 5 ≤ m) :
    F2Seam m s(contactAnchor (j2Contact hm), contactAnchor (j2Contact hm) * c m) := by
  let i : Fin m := ⟨m - 1, by omega⟩
  apply j2_reverse_e_seam (j2Contact hm) i _
  simp only [gapAnchor, i, mul_assoc, ← pow_succ,
    show m - 1 + 1 = m by omega, j2_bc_order hm, mul_one]

private theorem j2_word3_c {m : Nat} (hm : 5 ≤ m) :
    F2Seam m s(contactAnchor (j2Contact hm) * (b m * c m) ^ (m - 1),
      contactAnchor (j2Contact hm) * (b m * c m) ^ (m - 1) * c m) := by
  let i : Fin m := ⟨m - 2, by omega⟩
  apply j2_reverse_e_seam (j2Contact hm) i _
  simp only [gapAnchor, i, mul_assoc, ← pow_succ,
    show m - 2 + 1 = m - 1 by omega]

private theorem j2_word4_c {m : Nat} (hm : 5 ≤ m) :
    F2Seam m
      s(Equiv.swap (0 : Fin (m + 1)) (Fin.last m),
        Equiv.swap (0 : Fin (m + 1)) (Fin.last m) * c m) := by
  let p : Fin m ⊕ Fin (m - 2) := Sum.inl ⟨m - 3, by omega⟩
  have he : NativeCoreSplicing.cutStart p * cutGenerator p * c m =
      Equiv.swap (0 : Fin (m + 1)) (Fin.last m) := by
    dsimp only [p]
    solve_j2_seam_coordinate m
  exact j2_reverse_t_seam p _ he.symm

private theorem j2_word1_initial_reflected {m : Nat} (hm : 5 ≤ m) :
    wordStart m 1 = finRotate (m + 1) ^ (m - 1) * a m := by
  solve_j2_seam_coordinate m

private theorem j2_word0_contact_reflected {m : Nat} (hm : 5 ≤ m) :
    c m = contactAnchor (j2Contact hm) * finRotate (m + 1) ^ (m - 2) * a m := by
  solve_j2_seam_coordinate m

private theorem j2_word0_final_b_start {m : Nat} (hm : 5 ≤ m) :
    contactAnchor (j2Contact hm) * c m =
      gapAnchor (contactAnchor (j2Contact hm)) ⟨m - 1, by omega⟩ * b m := by
  solve_j2_seam_coordinate m

private theorem j2_word2_initial_positive {m : Nat} (hm : 5 ≤ m) :
    wordStart m 2 = contactAnchor (j2Contact hm) * finRotate (m + 1) ^ m := by
  solve_j2_seam_coordinate m

private theorem j2_word3_initial_reflected {m : Nat} (hm : 5 ≤ m) :
    wordStart m 3 =
      gapAnchor (contactAnchor (j2Contact hm)) ⟨m - 1, by omega⟩ * a m := by
  solve_j2_seam_coordinate m

private theorem j2_word3_final_b_start {m : Nat} (hm : 5 ≤ m) :
    wordStart m 3 * a m * c m =
      gapAnchor (contactAnchor (j2Contact hm)) ⟨m - 2, by omega⟩ * b m := by
  rw [j2_word3_seed hm, show m - 1 = (m - 2) + 1 by omega, pow_succ]
  simp only [gapAnchor, Fin.val_mk, mul_assoc, c_sq, mul_one]

private theorem j2_word4_final_b_start {m : Nat} (hm : 5 ≤ m) :
    wordStart m 4 * a m * b m * c m = lowerPort (j2Contact hm) * b m := by
  solve_j2_seam_coordinate m

private theorem j2_cb_c_pow (m t : Nat) :
    (c m * b m) ^ t * c m = c m * (b m * c m) ^ t := by
  induction t with
  | zero => simp only [pow_zero, one_mul, mul_one]
  | succ t ih =>
    calc
      _ = (c m * b m) * ((c m * b m) ^ t * c m) := by
        rw [pow_succ', mul_assoc]
      _ = (c m * b m) * (c m * (b m * c m) ^ t) := by rw [ih]
      _ = c m * ((b m * c m) * (b m * c m) ^ t) := by simp only [mul_assoc]
      _ = c m * (b m * c m) ^ (t + 1) := by rw [pow_succ']

private theorem j2_word1_final_a_start {m : Nat} (hm : 5 ≤ m) :
    wordStart m 1 * (a m * b m) ^ (m - 1) *
        (c m * b m) ^ (m - 3) * c m = lowerPort (j2Contact hm) := by
  rw [j2_word1_seed hm, mul_assoc (a m), j2_cb_c_pow]
  simp only [lowerPort, j2Contact, Fin.val_mk, mul_assoc]

private theorem j2_word2_final_aba_start {m : Nat} (hm : 5 ≤ m) :
    wordStart m 2 * a m * (c m * b m) ^ (m - 3) * c m =
      gapAnchor (contactAnchor (j2Contact hm)) ⟨m - 2, by omega⟩ := by
  rw [j2_word2_seed hm, mul_assoc (contactAnchor (j2Contact hm)), j2_b_cb_pow]
  simp only [← mul_assoc, gapAnchor, Fin.val_mk]
  rw [show m - 2 = (m - 3) + 1 by omega, pow_succ]
  simp only [mul_assoc]



end D5.S3.Combinatorics.Graph.PrefixReversal.NativeJ2SurvivingEdges
