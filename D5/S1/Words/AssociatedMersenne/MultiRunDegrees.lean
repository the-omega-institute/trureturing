/- GID: D5/S1/Words/AssociatedMersenne/MultiRunDegrees
   generality: G
   mirror-B: D5/B/S1/Words/AssociatedMersenne/MultiRunDegrees
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Pair-local legal flips determine the degree of words with several runs. -/

/-
admission_basis: escape-witness
Module content theorem: degree_raw_multi
Run marks: IsOneRunStart permits r = 0; IsMarkedStart requires positive r.
Singleton correction: [(r,1)] has provisionalDegree min r 2 + 1 and tupleDegree min r 2.
The transfer correction is X * (1 - Y) * Rser before marking and
X * derivative (X * (1 - Y) * Rser) after marking.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14898
Direct frozen dependencies:
  none (the other D5 imports belong to this delivery).
Declarations:
  extendLastGap_ne_nil: proof_shape: bind-only; escape_witness: none; consumer: MultiRunDegrees.raw_first_delete_legal
  extendLastGap_valid: proof_shape: bind-only; escape_witness: none; consumer: MultiRunDegrees.raw_first_delete_legal
  rawWord_extendLastGap: proof_shape: bind-only; escape_witness: none; consumer: MultiRunDegrees.raw_first_delete_legal
  linearize_flip_at: proof_shape: bind-only; escape_witness: none; consumer: MultiRunDegrees.raw_first_delete_reading
  set_first_right_endpoint: proof_shape: bind-only; escape_witness: none; consumer: MultiRunDegrees.raw_right_delete_legal
  raw_right_delete_legal: proof_shape: content; escape_witness: MultiRunDegrees.raw_right_delete_legal;
  raw_coordinate_sum: proof_shape: bind-only; escape_witness: none; consumer: MultiRunDegrees.degree_pair_sum
  degree_pair_sum: proof_shape: bind-only; escape_witness: none; consumer: MultiRunDegrees.degree_raw_multi
  set_first_one: proof_shape: bind-only; escape_witness: none; consumer: MultiRunDegrees.raw_first_delete_reading
  raw_first_delete_reading: proof_shape: bind-only; escape_witness: none; consumer: MultiRunDegrees.raw_first_delete_legal
  raw_first_delete_legal: proof_shape: content; escape_witness: MultiRunDegrees.raw_first_delete_legal;
  raw_singleton_delete_legal: proof_shape: content; escape_witness: MultiRunDegrees.raw_singleton_delete_legal;
  set_last_gap_zero: proof_shape: bind-only; escape_witness: none; consumer: MultiRunDegrees.raw_left_insert_encoding
  raw_left_insert_encoding: proof_shape: bind-only; escape_witness: none; consumer: MultiRunDegrees.raw_left_insert_iff
  raw_left_insert_iff: proof_shape: content; escape_witness: MultiRunDegrees.raw_left_insert_iff;
  run_endpoint_sum: proof_shape: bind-only; escape_witness: none; consumer: MultiRunDegrees.raw_pair_flip_sum
  interior_gap_sum: proof_shape: bind-only; escape_witness: none; consumer: MultiRunDegrees.local_zero_flip_sum
  local_zero_flip_sum: proof_shape: bind-only; escape_witness: none; consumer: MultiRunDegrees.raw_pair_flip_sum
  linearize_at_pair: proof_shape: bind-only; escape_witness: none; consumer: MultiRunDegrees.degree_raw_multi
  rotate_valid: proof_shape: bind-only; escape_witness: none; consumer: MultiRunDegrees.degree_raw_multi
  rotate_two_pairs: proof_shape: bind-only; escape_witness: none; consumer: MultiRunDegrees.degree_raw_multi
  set_first_zero: proof_shape: bind-only; escape_witness: none; consumer: MultiRunDegrees.raw_right_insert_encoding
  raw_right_insert_encoding: proof_shape: bind-only; escape_witness: none; consumer: MultiRunDegrees.raw_right_insert_iff
  raw_right_insert_iff: proof_shape: content; escape_witness: MultiRunDegrees.raw_right_insert_iff;
  set_gap_position: proof_shape: bind-only; escape_witness: none; consumer: MultiRunDegrees.raw_gap_insert_encoding
  raw_gap_insert_encoding: proof_shape: bind-only; escape_witness: none; consumer: MultiRunDegrees.raw_gap_insert_iff
  raw_gap_insert_iff: proof_shape: content; escape_witness: MultiRunDegrees.raw_gap_insert_iff;
  raw_first_valid_start: proof_shape: content; escape_witness: CircularWords.marked_start_iff;
  raw_one_delete_iff: proof_shape: content; escape_witness: MultiRunDegrees.raw_one_delete_iff;
  raw_pair_flip_iff: proof_shape: content; escape_witness: MultiRunDegrees.raw_pair_flip_iff;
  raw_pair_flip_sum: proof_shape: content; escape_witness: MultiRunDegrees.raw_pair_flip_sum;
  degree_raw_multi: proof_shape: content; escape_witness: MultiRunDegrees.degree_raw_multi;
  degree_tuple_encoding: proof_shape: content; escape_witness: MultiRunDegrees.degree_tuple_encoding;
  degree_wordOfTuple: proof_shape: content; escape_witness: MultiRunDegrees.degree_raw_multi;
-/

import D5.S1.Words.AssociatedMersenne.SingleRunDegrees
import Mathlib.Data.List.ModifyLast

open D5.S1.Words.AssociatedMersenne.CircularWords
open D5.S1.Words.AssociatedMersenne.RunTupleBijection
open D5.S1.Words.AssociatedMersenne.SingleRunDegrees

namespace D5.S1.Words.AssociatedMersenne.MultiRunDegrees

open scoped BigOperators

open Classical
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

noncomputable section

private def extendLastGap (t : List (Nat × Nat)) (a : Nat) : List (Nat × Nat) :=
  List.modifyLast (fun b => (b.1,b.2+a)) t

private lemma extendLastGap_ne_nil (t : List (Nat × Nat)) (ht : t ≠ []) (a : Nat) :
    extendLastGap t a ≠ [] := by
  cases t with
  | nil => contradiction
  | cons b t =>
    cases t with
    | nil => simp [extendLastGap, List.modifyLast, List.modifyLast.go]
    | cons c t =>
      have heq : extendLastGap (b::c::t) a = b :: extendLastGap (c::t) a := by
        simpa [extendLastGap] using List.modifyLast_append_of_right_ne_nil
          (fun b : Nat × Nat => (b.1,b.2+a)) [b] (c::t) (by simp)
      rw [heq]
      simp

private lemma extendLastGap_valid (t : List (Nat × Nat)) (a : Nat)
    (hp : ∀ b ∈ t, 0 < b.1 ∧ b.1 < b.2) :
    ∀ b ∈ extendLastGap t a, 0 < b.1 ∧ b.1 < b.2 := by
  induction t with
  | nil => simp [extendLastGap, List.modifyLast, List.modifyLast.go]
  | cons b t ih =>
    have hb := hp b (by simp)
    have hpt : ∀ c ∈ t, 0 < c.1 ∧ c.1 < c.2 := fun c hc => hp c (by simp [hc])
    cases t with
    | nil =>
      simp only [extendLastGap, List.modifyLast, List.modifyLast.go]
      change ∀ c ∈ [(b.1,b.2+a)], 0 < c.1 ∧ c.1 < c.2
      simp only [List.mem_singleton]
      intro c hc
      subst c
      exact ⟨hb.1,by dsimp; omega⟩
    | cons c t =>
      have heq : extendLastGap (b::c::t) a = b :: extendLastGap (c::t) a := by
        simpa [extendLastGap] using List.modifyLast_append_of_right_ne_nil
          (fun b : Nat × Nat => (b.1,b.2+a)) [b] (c::t) (by simp)
      rw [heq]
      simp only [List.mem_cons]
      intro d hd
      rcases hd with rfl | hd
      · exact hb
      · exact ih hpt d hd

private theorem rawWord_extendLastGap (t : List (Nat × Nat)) (ht : t ≠ []) (a : Nat) :
    rawWord (extendLastGap t a) = rawWord t ++ List.replicate a false := by
  induction t with
  | nil => contradiction
  | cons b t ih =>
    cases t with
    | nil =>
      change rawWord [(b.1,b.2+a)] = rawWord [b] ++ List.replicate a false
      simp only [rawWord_cons, show rawWord [] = [] from rfl,
        List.append_nil, List.replicate_add, List.append_assoc]
    | cons c t =>
      have heq : extendLastGap (b::c::t) a = b :: extendLastGap (c::t) a := by
        simpa [extendLastGap] using List.modifyLast_append_of_right_ne_nil
          (fun b : Nat × Nat => (b.1,b.2+a)) [b] (c::t) (by simp)
      rw [heq]
      simp only [rawWord_cons]
      rw [ih (by simp)]
      simp only [rawWord_cons, List.append_assoc]

private theorem linearize_flip_at {n : Nat} (w : Fin n → Bool) (i : Fin n)
    (j : Nat) (hj : j < n) :
    linearize (CircularWords.flip w (cycAdd i j)) i =
      (linearize w i).set j (!w (cycAdd i j)) := by
  apply List.ext_getElem
  · simp [linearize]
  · intro k hk hk'
    have hkn : k < n := by simpa [linearize] using hk
    simp only [linearize, List.getElem_ofFn, List.getElem_set]
    have heq : cycAdd i k = cycAdd i j ↔ k = j := cycAdd_inj i hkn hj
    simp [CircularWords.flip, Function.update_apply, heq, eq_comm]

private lemma set_first_right_endpoint (r z : Nat) (post : List Bool) (hr : 0 < r) :
    (List.replicate r true ++ List.replicate z false ++ post).set (r-1) false =
      List.replicate (r-1) true ++ List.replicate (z+1) false ++ post := by
  have hr' : r = (r-1)+1 := by omega
  conv_lhs => rw [hr', List.replicate_add]
  simp [List.set_append, List.replicate_succ, List.append_assoc]

private theorem raw_right_delete_legal {n : Nat} (w : Fin n → Bool) (i : Fin n)
    (r z : Nat) (t : List (Nat × Nat)) (hr : 2 ≤ r) (hz : r < z)
    (hp : ∀ b ∈ t, 0 < b.1 ∧ b.1 < b.2)
    (he : linearize w i = rawWord ((r,z)::t)) :
    Admissible (CircularWords.flip w (cycAdd i (r-1))) := by
  have hlen : n = r+z+(rawWord t).length := by
    have h := congrArg List.length he
    simpa [linearize_length, rawWord_cons, Nat.add_assoc] using h
  have hn : r-1 < n := by omega
  have hbit : w (cycAdd i (r-1)) = true := by
    have hv := linearize_get_optional w i (r-1) hn
    rw [he, rawWord_cons] at hv
    simp [List.getElem?_append, show r-1 < r by omega] at hv
    exact hv
  apply raw_encoding_admissible _ i ((r-1,z+1)::t) (by simp) ?_ ?_
  · intro b hb
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨by omega, by omega⟩
    · exact hp b hb
  · rw [linearize_flip_at w i (r-1) hn, hbit, Bool.not_true, he,
      rawWord_cons, set_first_right_endpoint r z (rawWord t) (by omega)]
    simp only [rawWord_cons]

private theorem raw_coordinate_sum {M : Type*} [AddCommMonoid M]
    (t : List (Nat × Nat)) (f : Nat → M) :
    (∑ j ∈ Finset.range (rawWord t).length, f j) =
      ∑ p : Fin t.length, ∑ j ∈ Finset.range (t[p.val].1+t[p.val].2),
        f (pairPrefix t p.val+j) := by
  induction t generalizing f with
  | nil => simp [rawWord]
  | cons b t ih =>
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    simp only [List.length_cons, List.getElem_cons_zero, Fin.val_zero,
      pairPrefix, List.take_zero, show rawWord [] = [] from rfl,
      List.length_nil, Nat.zero_add]
    simp only [rawWord_cons, List.length_append, List.length_replicate]
    rw [Finset.sum_range_add]
    rw [ih (fun j => f (b.1+b.2+j))]
    congr 1
    apply Finset.sum_congr rfl
    intro p hp
    simp only [pairPrefix, Fin.val_succ, List.getElem_cons_succ, List.take_succ_cons,
      rawWord_cons, List.length_append, List.length_replicate, Nat.add_assoc]

private theorem degree_pair_sum {n : Nat} (w : Fin n → Bool) (i : Fin n)
    (t : List (Nat × Nat)) (he : linearize w i = rawWord t) :
    degree w = ∑ p : Fin t.length,
      ∑ j ∈ Finset.range (t[p.val].1+t[p.val].2),
        if Admissible (CircularWords.flip w (cycAdd i (pairPrefix t p.val+j))) then 1 else 0 := by
  classical
  have hlen : n = (rawWord t).length := by
    have h := congrArg List.length he
    simpa [linearize_length] using h
  have hd : degree w = ∑ j ∈ Finset.range n,
      if Admissible (CircularWords.flip w (cycAdd i j)) then 1 else 0 := by
    unfold degree
    change (Finset.univ.filter (fun q : Fin n => Admissible (CircularWords.flip w q))).card = _
    rw [show (Finset.univ.filter (fun q : Fin n => Admissible (CircularWords.flip w q))).card =
      ∑ q : Fin n, if Admissible (CircularWords.flip w q) then (1:Nat) else 0 by simp]
    rw [← Fin.sum_univ_eq_sum_range]
    symm
    exact Equiv.sum_comp (Equiv.ofBijective (fun j : Fin n => cycAdd i j.val) (cycAdd_bijective i))
      (fun q : Fin n => if Admissible (CircularWords.flip w q) then (1:Nat) else 0)
  have hs := raw_coordinate_sum t (fun j => if Admissible (CircularWords.flip w (cycAdd i j)) then (1:Nat) else 0)
  rw [← hlen] at hs
  exact hd.trans hs

private lemma set_first_one (r z : Nat) (post : List Bool) (hr : 0 < r) :
    (List.replicate r true ++ List.replicate z false ++ post).set 0 false =
      [false] ++ (List.replicate (r-1) true ++ List.replicate z false ++ post) := by
  cases r with
  | zero => omega
  | succ r => simp [List.replicate_succ, List.set_cons_zero, List.cons_append, List.append_assoc]

private lemma raw_first_delete_reading {n : Nat} (w : Fin n → Bool) (i : Fin n)
    (r z : Nat) (t : List (Nat × Nat)) (hr : 0 < r) (hz : r < z)
    (he : linearize w i = rawWord ((r,z)::t)) :
    linearize (CircularWords.flip w i) i =
      [false] ++ (List.replicate (r-1) true ++ List.replicate z false ++ rawWord t) := by
  have hlen : n = r+z+(rawWord t).length := by
    have h := congrArg List.length he
    simpa [linearize_length, rawWord_cons, Nat.add_assoc] using h
  have hbit : w i = true := by
    have hv := linearize_get_optional w i 0 (by omega)
    rw [he, rawWord_cons, cycAdd_zero] at hv
    simp [List.getElem?_append, hr] at hv
    exact hv
  have hflip := linearize_flip_at w i 0 (by omega)
  rw [cycAdd_zero, hbit, Bool.not_true, he, rawWord_cons,
    set_first_one r z (rawWord t) hr] at hflip
  exact hflip

private theorem raw_first_delete_legal {n : Nat} (w : Fin n → Bool) (i : Fin n)
    (r z : Nat) (t : List (Nat × Nat)) (hr : 2 ≤ r) (hz : r < z)
    (hp : ∀ b ∈ t, 0 < b.1 ∧ b.1 < b.2)
    (he : linearize w i = rawWord ((r,z)::t)) : Admissible (CircularWords.flip w i) := by
  have henc : linearize (CircularWords.flip w i) (cycAdd i 1) =
      rawWord ((r-1,z)::t) ++ List.replicate 1 false := by
    rw [linearize_move_mark, raw_first_delete_reading w i r z t (by omega) hz he]
    have hrot := List.rotate_append_length_eq [false]
      (List.replicate (r-1) true ++ List.replicate z false ++ rawWord t)
    simpa only [List.length_singleton, rawWord_cons, List.replicate_one] using hrot
  let u := (r-1,z)::t
  have hu : u ≠ [] := by simp [u]
  have hup : ∀ b ∈ u, 0 < b.1 ∧ b.1 < b.2 := by
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨by omega,by omega⟩
    · exact hp b hb
  apply raw_encoding_admissible _ (cycAdd i 1) (extendLastGap u 1)
    (extendLastGap_ne_nil u hu 1) (extendLastGap_valid u 1 hup)
  rw [rawWord_extendLastGap u hu 1]
  exact henc

private theorem raw_singleton_delete_legal {n : Nat} (w : Fin n → Bool) (i : Fin n)
    (z : Nat) (t : List (Nat × Nat)) (hz : 1 < z)
    (hp : ∀ b ∈ t, 0 < b.1 ∧ b.1 < b.2)
    (he : linearize w i = rawWord ((1,z)::t)) : Admissible (CircularWords.flip w i) := by
  have hread : linearize (CircularWords.flip w i) i = List.replicate (z+1) false ++ rawWord t := by
    rw [raw_first_delete_reading w i 1 z t (by omega) hz he]
    simp [List.replicate_succ, List.cons_append]
  by_cases ht : t = []
  · subst t
    have hzero : CircularWords.flip w i = (fun _ : Fin n => false) := by
      apply linearize_injective i
      have hlen := congrArg List.length hread
      have heq : n = z+1 := by simpa [linearize_length, rawWord] using hlen
      change linearize (CircularWords.flip w i) i = linearize (fun _ : Fin n => false) i
      rw [hread]
      simp [linearize, rawWord, List.ofFn_const, heq, List.replicate_succ]
    rw [hzero]
    exact zero_admissible n
  · have henc : linearize (CircularWords.flip w i) (cycAdd i (z+1)) =
        rawWord t ++ List.replicate (z+1) false := by
      rw [linearize_move_mark, hread]
      simpa using List.rotate_append_length_eq (List.replicate (z+1) false) (rawWord t)
    apply raw_encoding_admissible _ (cycAdd i (z+1)) (extendLastGap t (z+1))
      (extendLastGap_ne_nil t ht (z+1)) (extendLastGap_valid t (z+1) hp)
    rw [rawWord_extendLastGap t ht (z+1)]
    exact henc

private lemma set_last_gap_zero (r z u v : Nat) (post : List Bool) (hz : 0 < z) :
    (List.replicate r true ++ List.replicate z false ++
      List.replicate u true ++ List.replicate v false ++ post).set (r+z-1) true =
      List.replicate r true ++ List.replicate (z-1) false ++
        List.replicate (u+1) true ++ List.replicate v false ++ post := by
  have hzrep : List.replicate z false = List.replicate (z-1) false ++ [false] := by
    change List.replicate z false = List.replicate (z-1) false ++ List.replicate 1 false
    rw [← List.replicate_add]
    congr 1
    omega
  have he : r+z-1 = r+(z-1) := by omega
  rw [hzrep, he]
  simp only [List.append_assoc]
  rw [List.set_append_right (r+(z-1)) true (by simp)]
  simp only [List.length_replicate, Nat.add_sub_cancel_left]
  rw [List.set_append_right (z-1) true (by simp)]
  simp only [List.length_replicate, Nat.sub_self, List.singleton_append, List.set_cons_zero]
  rw [List.replicate_succ]
  simp only [List.append_assoc, List.cons_append]

private lemma raw_left_insert_encoding {n : Nat} (w : Fin n → Bool) (i : Fin n)
    (r z u v : Nat) (t : List (Nat × Nat)) (hr : 0 < r) (hz : r < z)
    (he : linearize w i = rawWord ((r,z)::(u,v)::t)) :
    linearize (CircularWords.flip w (cycAdd i (r+z-1))) i = rawWord ((r,z-1)::(u+1,v)::t) := by
  have hlen : n = r+z+u+v+(rawWord t).length := by
    have h := congrArg List.length he
    simpa [linearize_length, rawWord_cons, Nat.add_assoc] using h
  have hn : r+z-1 < n := by omega
  have hbit : w (cycAdd i (r+z-1)) = false := by
    have hv := linearize_get_optional w i (r+z-1) hn
    rw [he, rawWord_cons] at hv
    simp [List.getElem?_append, show ¬r+z-1 < r by omega,
      show r+z-1-r = z-1 by omega, show z-1 < z by omega] at hv
    exact hv
  rw [linearize_flip_at w i (r+z-1) hn, hbit, Bool.not_false, he]
  simp only [rawWord_cons, List.append_assoc]
  simpa only [List.append_assoc] using set_last_gap_zero r z u v (rawWord t) (by omega)

private theorem raw_left_insert_iff {n : Nat} (w : Fin n → Bool) (i : Fin n)
    (r z u v : Nat) (t : List (Nat × Nat)) (hr : 0 < r) (hz : r < z)
    (hu : 0 < u) (hv : u < v) (hp : ∀ b ∈ t, 0 < b.1 ∧ b.1 < b.2)
    (he : linearize w i = rawWord ((r,z)::(u,v)::t)) :
    Admissible (CircularWords.flip w (cycAdd i (r+z-1))) ↔ r+1 < z ∧ u+1 < v := by
  have henc := raw_left_insert_encoding w i r z u v t hr hz he
  have hpos : ∀ b ∈ (r,z-1)::(u+1,v)::t, 0 < b.1 ∧ 0 < b.2 := by
    intro b hb
    simp only [List.mem_cons] at hb
    rcases hb with rfl | rfl | hb
    · exact ⟨hr,by omega⟩
    · exact ⟨by omega,by omega⟩
    · have h := hp b hb; exact ⟨h.1,by omega⟩
  rw [raw_encoding_admissible_iff _ i _ (by simp) hpos henc]
  constructor
  · intro hg
    have h1 := hg (r,z-1) (by simp)
    have h2 := hg (u+1,v) (by simp)
    dsimp at h1 h2
    omega
  · intro h b hb
    simp only [List.mem_cons] at hb
    rcases hb with rfl | rfl | hb
    · dsimp; omega
    · exact h.2
    · exact (hp b hb).2

private lemma run_endpoint_sum (r : Nat) (hr : 0 < r) :
    (∑ j ∈ Finset.range r, if j=0 ∨ j+1=r then (1:Nat) else 0) = min r 2 := by
  have he : (Finset.range r).filter (fun j => j=0 ∨ j+1=r) = {0,r-1} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [Finset.sum_boole]
  change ((Finset.range r).filter (fun j => j=0 ∨ j+1=r)).card = _
  rw [he]
  by_cases hr1 : r=1
  · subst r; simp
  · rw [Finset.card_pair (by omega : 0 ≠ r-1), Nat.min_eq_right (by omega)]

private lemma interior_gap_sum (r z : Nat) (hr : 0 < r) (hz : r < z) :
    (∑ p ∈ Finset.range z, if r < p ∧ p+2 < z then (1:Nat) else 0) = z-r-3 := by
  have he : (Finset.range z).filter (fun p => r < p ∧ p+2 < z) = Finset.Ico (r+1) (z-2) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [Finset.sum_boole]
  change ((Finset.range z).filter (fun p => r < p ∧ p+2 < z)).card = _
  rw [he, Nat.card_Ico]
  omega

private def zeroLocalPred (r z u v p : Nat) : Prop :=
  (p=0 ∧ r+2 < z) ∨ (p+1=z ∧ r+1 < z ∧ u+1 < v) ∨
    (r<p ∧ p+2<z)

private theorem local_zero_flip_sum (r s u a : Nat) (hr : 0 < r) (hu : 0 < u) :
    (∑ p ∈ Finset.range (r+1+s),
      if zeroLocalPred r (r+1+s) u (u+1+a) p then (1:Nat) else 0) =
        s-1 + if 1 ≤ s ∧ 1 ≤ a then 1 else 0 := by
  let z := r+1+s
  have he : ∀ p < z,
      (if zeroLocalPred r z u (u+1+a) p then (1:Nat) else 0) =
      (if p=0 then (if r+2<z then 1 else 0) else 0) +
      (if p=z-1 then (if r+1<z ∧ u+1<u+1+a then 1 else 0) else 0) +
      (if r<p ∧ p+2<z then 1 else 0) := by
    intro p hp
    dsimp [zeroLocalPred]
    by_cases hp0 : p=0
    · subst p; simp [show ¬r<0 by omega, show ¬0+1=z by dsimp [z]; omega,
        show ¬0=z-1 by dsimp [z]; omega]
    · by_cases hpl : p+1=z
      · have hpz : p=z-1 := by omega
        simp [hpz,show z-1 ≠ 0 by dsimp [z]; omega,
          show z-1+1=z by dsimp [z]; omega,show ¬z-1+2<z by dsimp [z]; omega]
      · have hpz : p≠z-1 := by dsimp [z] at *; omega
        simp [hp0,hpl,hpz]
  calc
    _ = (∑ p ∈ Finset.range z, (
      (if p=0 then (if r+2<z then (1:Nat) else 0) else 0) +
      (if p=z-1 then (if r+1<z ∧ u+1<u+1+a then 1 else 0) else 0) +
      (if r<p ∧ p+2<z then 1 else 0))) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact he p (Finset.mem_range.mp hp)
    _ = (if r+2<z then 1 else 0) +
        (if r+1<z ∧ u+1<u+1+a then 1 else 0) + (z-r-3) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        interior_gap_sum r z hr (by dsimp [z]; omega)]
      simp [Finset.sum_ite_eq', show 0<z by dsimp [z]; omega,
        show z-1<z by dsimp [z]; omega]
    _ = _ := by
      dsimp [z]
      split_ifs <;> omega

private theorem linearize_at_pair {n : Nat} (w : Fin n → Bool) (i : Fin n)
    (t : List (Nat × Nat)) (he : linearize w i = rawWord t) (p : Fin t.length) :
    linearize w (cycAdd i (pairPrefix t p.val)) = rawWord (t.rotate p.val) := by
  have hd : rawWord t = rawWord (t.take p.val) ++ rawWord (t.drop p.val) := by
    rw [← rawWord_append, List.take_append_drop]
  rw [pairPrefix, linearize_move_mark, he, hd, List.rotate_append_length_eq,
    ← rawWord_append, List.rotate_eq_drop_append_take (Nat.le_of_lt p.isLt)]

private lemma rotate_valid (t : List (Nat × Nat)) (p : Nat)
    (hp : ∀ b ∈ t, 0 < b.1 ∧ b.1 < b.2) :
    ∀ b ∈ t.rotate p, 0 < b.1 ∧ b.1 < b.2 := by
  intro b hb
  exact hp b ((List.rotate_perm t p).mem_iff.mp hb)

private lemma rotate_two_pairs (t : List (Nat × Nat)) (p : Fin t.length) (ht : 2 ≤ t.length) :
    ∃ b c u, t.rotate p.val = b::c::u ∧ b = t[p.val] ∧
      c = t[(p.val+1)%t.length]'(Nat.mod_lt _ (by omega)) := by
  have hlen : (t.rotate p.val).length = t.length := List.length_rotate t p.val
  cases hrot : t.rotate p.val with
  | nil => simp [hrot] at hlen; omega
  | cons b v =>
    cases v with
    | nil => simp [hrot] at hlen; omega
    | cons c u =>
      refine ⟨b,c,u,rfl,?_,?_⟩
      · have hget := List.getElem_rotate (l := t) (n := p.val) (k := 0) (by rw [hlen]; omega)
        simpa [hrot,Nat.mod_eq_of_lt p.isLt] using hget
      · have hget := List.getElem_rotate (l := t) (n := p.val) (k := 1) (by rw [hlen]; omega)
        simpa [hrot,Nat.add_comm] using hget

private lemma set_first_zero (r z : Nat) (post : List Bool) (hz : 0 < z) :
    (List.replicate r true ++ List.replicate z false ++ post).set r true =
      List.replicate (r+1) true ++ List.replicate (z-1) false ++ post := by
  rw [List.set_append_left r true (by simp; omega),
    List.set_append_right r true (by simp)]
  simp only [List.length_replicate, Nat.sub_self]
  have hz' : z = (z-1)+1 := by omega
  rw [hz', List.replicate_succ]
  simp only [List.set_cons_zero, List.replicate_add, List.replicate_one,
    List.append_assoc, List.singleton_append]
  rfl

private lemma raw_right_insert_encoding {n : Nat} (w : Fin n → Bool) (i : Fin n)
    (r z : Nat) (t : List (Nat × Nat)) (hr : 0 < r) (hz : r < z)
    (he : linearize w i = rawWord ((r,z)::t)) :
    linearize (CircularWords.flip w (cycAdd i r)) i = rawWord ((r+1,z-1)::t) := by
  have hlen : n = r+z+(rawWord t).length := by
    have h := congrArg List.length he
    simpa [linearize_length, rawWord_cons, Nat.add_assoc] using h
  have hn : r < n := by omega
  have hbit : w (cycAdd i r) = false := by
    have hv := linearize_get_optional w i r hn
    rw [he, rawWord_cons] at hv
    simp [List.getElem?_append, show 0 < z by omega] at hv
    exact hv
  rw [linearize_flip_at w i r hn, hbit, Bool.not_false, he,
    rawWord_cons, set_first_zero r z (rawWord t) (by omega)]
  simp only [rawWord_cons]

private theorem raw_right_insert_iff {n : Nat} (w : Fin n → Bool) (i : Fin n)
    (r z : Nat) (t : List (Nat × Nat)) (hr : 0 < r) (hz : r < z)
    (hp : ∀ b ∈ t, 0 < b.1 ∧ b.1 < b.2)
    (he : linearize w i = rawWord ((r,z)::t)) :
    Admissible (CircularWords.flip w (cycAdd i r)) ↔ r+2 < z := by
  have henc := raw_right_insert_encoding w i r z t hr hz he
  have hpos : ∀ b ∈ (r+1,z-1)::t, 0 < b.1 ∧ 0 < b.2 := by
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨by omega, by omega⟩
    · have h := hp b hb; exact ⟨h.1, by omega⟩
  rw [raw_encoding_admissible_iff _ i _ (by simp) hpos henc]
  constructor
  · intro hg
    have h := hg (r+1,z-1) (by simp)
    dsimp at h
    omega
  · intro hg b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · dsimp; omega
    · exact (hp b hb).2

private lemma set_gap_position (r z p : Nat) (post : List Bool) (hp : p < z) :
    (List.replicate r true ++ List.replicate z false ++ post).set (r+p) true =
      List.replicate r true ++ List.replicate p false ++
        List.replicate 1 true ++ List.replicate (z-p-1) false ++ post := by
  rw [List.set_append_left (r+p) true (by simp; omega),
    List.set_append_right (r+p) true (by simp)]
  simp only [List.length_replicate, Nat.add_sub_cancel_left]
  rw [List.set_eq_take_append_cons_drop]
  simp [hp, List.take_replicate, List.drop_replicate, Nat.min_eq_left (by omega : p ≤ z),
    Nat.sub_sub, List.append_assoc]

private lemma raw_gap_insert_encoding {n : Nat} (w : Fin n → Bool) (i : Fin n)
    (r z p : Nat) (t : List (Nat × Nat)) (hr : 0 < r) (hz : r < z) (hp : p < z)
    (he : linearize w i = rawWord ((r,z)::t)) :
    linearize (CircularWords.flip w (cycAdd i (r+p))) i = rawWord ((r,p)::(1,z-p-1)::t) := by
  have hlen : n = r+z+(rawWord t).length := by
    have h := congrArg List.length he
    simpa [linearize_length, rawWord_cons, Nat.add_assoc] using h
  have hn : r+p < n := by omega
  have hbit : w (cycAdd i (r+p)) = false := by
    have hv := linearize_get_optional w i (r+p) hn
    rw [he, rawWord_cons] at hv
    simp [List.getElem?_append, show ¬r+p < r by omega,
      show r+p-r = p by omega, hp] at hv
    exact hv
  rw [linearize_flip_at w i (r+p) hn, hbit, Bool.not_false, he,
    rawWord_cons, set_gap_position r z p (rawWord t) hp]
  simp only [rawWord_cons, List.append_assoc]

private theorem raw_gap_insert_iff {n : Nat} (w : Fin n → Bool) (i : Fin n)
    (r z p : Nat) (t : List (Nat × Nat)) (hr : 0 < r) (hz : r < z)
    (hp : 0 < p) (hpz : p+1 < z)
    (ht : ∀ b ∈ t, 0 < b.1 ∧ b.1 < b.2)
    (he : linearize w i = rawWord ((r,z)::t)) :
    Admissible (CircularWords.flip w (cycAdd i (r+p))) ↔ r < p ∧ p+2 < z := by
  have henc := raw_gap_insert_encoding w i r z p t hr hz (by omega) he
  have hpos : ∀ b ∈ (r,p)::(1,z-p-1)::t, 0 < b.1 ∧ 0 < b.2 := by
    intro b hb
    simp only [List.mem_cons] at hb
    rcases hb with rfl | rfl | hb
    · exact ⟨hr,hp⟩
    · exact ⟨by omega,by omega⟩
    · have h := ht b hb; exact ⟨h.1, by omega⟩
  rw [raw_encoding_admissible_iff _ i _ (by simp) hpos henc]
  constructor
  · intro hg
    have h1 := hg (r,p) (by simp)
    have h2 := hg (1,z-p-1) (by simp)
    dsimp at h1 h2
    omega
  · intro h b hb
    simp only [List.mem_cons] at hb
    rcases hb with rfl | rfl | hb
    · exact h.1
    · dsimp; omega
    · exact (ht b hb).2

private lemma raw_first_valid_start {n : Nat} (w : Fin n → Bool) (i : Fin n)
    (r z : Nat) (t : List (Nat × Nat)) (hr : 0 < r) (hz : r < z)
    (hp : ∀ b ∈ t, 0 < b.1 ∧ b.1 < b.2)
    (he : linearize w i = rawWord ((r,z)::t)) : IsOneRunStart w i r := by
  have hpos : ∀ b ∈ (r,z)::t, 0 < b.1 ∧ 0 < b.2 := by
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨hr,by omega⟩
    · have h := hp b hb; exact ⟨h.1,by omega⟩
  have hm := raw_encoding_marked w i ((r,z)::t) (by simp) hpos he
  exact first_raw_run_start (r := r) (z := z) w i hr (by omega) (rawWord t) hm
    (by simpa [rawWord_cons] using he)

private theorem raw_one_delete_iff {n : Nat} (w : Fin n → Bool) (i : Fin n)
    (r z p : Nat) (t : List (Nat × Nat)) (hr : 0 < r) (hz : r < z) (hp : p < r)
    (ht : ∀ b ∈ t, 0 < b.1 ∧ b.1 < b.2)
    (he : linearize w i = rawWord ((r,z)::t)) :
    Admissible (CircularWords.flip w (cycAdd i p)) ↔ p = 0 ∨ p+1 = r := by
  constructor
  · intro ha
    by_contra hn
    have hs := raw_first_valid_start w i r z t hr hz ht he
    exact run_interior_delete_illegal hs (by omega) (by omega) ha
  · intro hend
    by_cases hr1 : r = 1
    · subst r
      have hp0 : p = 0 := by omega
      rw [hp0,cycAdd_zero]
      exact raw_singleton_delete_legal w i z t hz ht he
    · rcases hend with hp0 | hpr
      · rw [hp0,cycAdd_zero]
        exact raw_first_delete_legal w i r z t (by omega) hz ht he
      · have hp' : p = r-1 := by omega
        rw [hp']
        exact raw_right_delete_legal w i r z t (by omega) hz ht he

private theorem raw_pair_flip_iff {n : Nat} (w : Fin n → Bool) (i : Fin n)
    (r z u v j : Nat) (t : List (Nat × Nat))
    (hr : 0 < r) (hz : r < z) (hu : 0 < u) (hv : u < v) (hj : j < r+z)
    (hp : ∀ b ∈ t, 0 < b.1 ∧ b.1 < b.2)
    (he : linearize w i = rawWord ((r,z)::(u,v)::t)) :
    Admissible (CircularWords.flip w (cycAdd i j)) ↔
      (j < r ∧ (j = 0 ∨ j+1 = r)) ∨
      (j = r ∧ r+2 < z) ∨
      (j+1 = r+z ∧ r+1 < z ∧ u+1 < v) ∨
      (2*r < j ∧ j+2 < r+z) := by
  have ht : ∀ b ∈ (u,v)::t, 0 < b.1 ∧ b.1 < b.2 := by
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨hu,hv⟩
    · exact hp b hb
  by_cases hjr : j < r
  · rw [raw_one_delete_iff w i r z j ((u,v)::t) hr hz hjr ht he]
    omega
  · by_cases hj0 : j = r
    · subst j
      rw [raw_right_insert_iff w i r z ((u,v)::t) hr hz ht he]
      omega
    · by_cases hjlast : j+1 = r+z
      · have heq : j = r+z-1 := by omega
        rw [heq, raw_left_insert_iff w i r z u v t hr hz hu hv hp he]
        omega
      · have hjp : j = r+(j-r) := by omega
        rw [hjp, raw_gap_insert_iff w i r z (j-r) ((u,v)::t) hr hz
          (by omega) (by omega) ht he]
        omega

private theorem raw_pair_flip_sum {n : Nat} (w : Fin n → Bool) (i : Fin n)
    (r s u a : Nat) (t : List (Nat × Nat)) (hr : 0 < r) (hu : 0 < u)
    (hp : ∀ b ∈ t, 0 < b.1 ∧ b.1 < b.2)
    (he : linearize w i = rawWord ((r,r+1+s)::(u,u+1+a)::t)) :
    (∑ j ∈ Finset.range (r+(r+1+s)),
      if Admissible (CircularWords.flip w (cycAdd i j)) then (1:Nat) else 0) =
        min r 2 + (s-1) + if 1 ≤ s ∧ 1 ≤ a then 1 else 0 := by
  let z := r+1+s
  have ht : ∀ b ∈ (u,u+1+a)::t, 0 < b.1 ∧ b.1 < b.2 := by
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨hu,by dsimp; omega⟩
    · exact hp b hb
  rw [Finset.sum_range_add]
  have hone : (∑ j ∈ Finset.range r,
      if Admissible (CircularWords.flip w (cycAdd i j)) then (1:Nat) else 0) = min r 2 := by
    calc
      _ = (∑ j ∈ Finset.range r, if j=0 ∨ j+1=r then (1:Nat) else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [raw_one_delete_iff w i r z j ((u,u+1+a)::t) hr
          (by dsimp [z]; omega) (Finset.mem_range.mp hj) ht he]
        split_ifs <;> rfl
      _ = _ := run_endpoint_sum r hr
  have hzero : (∑ p ∈ Finset.range z,
      if Admissible (CircularWords.flip w (cycAdd i (r+p))) then (1:Nat) else 0) =
      s-1 + if 1 ≤ s ∧ 1 ≤ a then 1 else 0 := by
    calc
      _ = (∑ p ∈ Finset.range z, if zeroLocalPred r z u (u+1+a) p then (1:Nat) else 0) := by
        apply Finset.sum_congr rfl
        intro p hpz
        have hif : Admissible (CircularWords.flip w (cycAdd i (r+p))) ↔ zeroLocalPred r z u (u+1+a) p := by
          rw [raw_pair_flip_iff w i r z u (u+1+a) (r+p) t hr
            (by dsimp [z]; omega) hu (by omega) (by have := Finset.mem_range.mp hpz; omega) hp he]
          dsimp [zeroLocalPred]
          omega
        rw [hif]
      _ = _ := local_zero_flip_sum r s u a hr hu
  rw [hone,hzero]
  omega

theorem degree_raw_multi {n : Nat} (w : Fin n → Bool) (i : Fin n)
    (t : List (Nat × Nat)) (ht : 2 ≤ t.length)
    (hp : ∀ b ∈ t, 0 < b.1 ∧ b.1 < b.2) (he : linearize w i = rawWord t) :
    degree w = ∑ p : Fin t.length,
      (min t[p.val].1 2 + (t[p.val].2-(t[p.val].1+1)-1) +
        if t[p.val].1+1 < t[p.val].2 ∧
            (t[(p.val+1)%t.length]'(Nat.mod_lt _ (by omega))).1+1 <
              (t[(p.val+1)%t.length]'(Nat.mod_lt _ (by omega))).2 then 1 else 0) := by
  rw [degree_pair_sum w i t he]
  apply Finset.sum_congr rfl
  intro p hpu
  obtain ⟨b,c,u,hrot,hb,hc⟩ := rotate_two_pairs t p ht
  have hvalid := rotate_valid t p.val hp
  have hbp := hvalid b (by rw [hrot]; simp)
  have hcp := hvalid c (by rw [hrot]; simp)
  have hup : ∀ d ∈ u, 0 < d.1 ∧ d.1 < d.2 := by
    intro d hd
    exact hvalid d (by rw [hrot]; simp [hd])
  have he' : linearize w (cycAdd i (pairPrefix t p.val)) = rawWord (b::c::u) := by
    rw [linearize_at_pair w i t he p, hrot]
  have hzb : b.1+1+(b.2-(b.1+1)) = b.2 := by omega
  have hzc : c.1+1+(c.2-(c.1+1)) = c.2 := by omega
  have he'' : linearize w (cycAdd i (pairPrefix t p.val)) =
      rawWord ((b.1,b.1+1+(b.2-(b.1+1)))::(c.1,c.1+1+(c.2-(c.1+1)))::u) := by
    rw [hzb,hzc]
    exact he'
  have hs := raw_pair_flip_sum w (cycAdd i (pairPrefix t p.val))
    b.1 (b.2-(b.1+1)) c.1 (c.2-(c.1+1)) u hbp.1 hcp.1 hup he''
  rw [hzb] at hs
  have hiff : (1 ≤ b.2-(b.1+1) ∧ 1 ≤ c.2-(c.1+1)) ↔
      b.1+1<b.2 ∧ c.1+1<c.2 := by omega
  simp only [hiff] at hs
  simpa only [cycAdd_assoc, hb, hc] using hs

def tupleDegree (t : List (Nat × Nat)) : Nat :=
  if t.length=1 then
    (t.map (fun b => min b.1 2 + if 2 ≤ b.2 then b.2 else 0)).sum
  else ∑ p : Fin t.length,
    (min t[p.val].1 2 + (t[p.val].2-1) +
      if 1 ≤ t[p.val].2 ∧
        1 ≤ (t[(p.val+1)%t.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt p.isLt))).2 then 1 else 0)

private theorem degree_tuple_encoding {n : Nat} (w : Fin n → Bool) (i : Fin n)
    (t : List (Nat × Nat)) (hne : t ≠ []) (hp : ∀ b ∈ t, 0 < b.1)
    (he : linearize w i = tupleList t) : degree w = tupleDegree t := by
  have hrp : ∀ b ∈ rawPairs t, 0 < b.1 ∧ b.1 < b.2 := by
    intro b hb
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
    exact ⟨hp c hc,by omega⟩
  have hraw : linearize w i = rawWord (rawPairs t) := by rw [he,tupleList_eq_rawPairs]
  by_cases ht1 : t.length=1
  · obtain ⟨b,htb⟩ := List.length_eq_one_iff.mp ht1
    subst t
    have h := degree_raw_singleton w i b.1 (b.1+1+b.2) (hp b (by simp)) (by omega)
      (by simpa [rawPairs] using hraw)
    simpa [tupleDegree,show b.1+1+b.2-b.1-1=b.2 by omega] using h
  · have ht2 : 2 ≤ (rawPairs t).length := by
      simp only [rawPairs,List.length_map]
      have htpos := List.length_pos_iff_ne_nil.mpr hne
      omega
    have h := degree_raw_multi w i (rawPairs t) ht2 hrp hraw
    rw [tupleDegree,if_neg ht1]
    let e : Fin t.length ≃ Fin (rawPairs t).length :=
      finCongr (by simp [rawPairs])
    rw [← e.sum_comp] at h
    have hev : ∀ p : Fin t.length, (e p).val=p.val := fun p => rfl
    simp only [hev] at h
    simp only [rawPairs,List.length_map,List.getElem_map,Prod.fst,Prod.snd] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro p hpu
    have hsub : t[p.val].1+1+t[p.val].2-(t[p.val].1+1)-1=t[p.val].2-1 := by omega
    rw [hsub]
    have hif : (t[p.val].1+1<t[p.val].1+1+t[p.val].2 ∧
      (t[(p.val+1)%t.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt p.isLt))).1+1<
        (t[(p.val+1)%t.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt p.isLt))).1+1+
          (t[(p.val+1)%t.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt p.isLt))).2) ↔
      1 ≤ t[p.val].2 ∧ 1 ≤ (t[(p.val+1)%t.length]'(Nat.mod_lt _ (Nat.zero_lt_of_lt p.isLt))).2 := by omega
    simp only [hif]

lemma degree_wordOfTuple {n : Nat} (i : Fin n) (t : GoodTuple n) :
    degree (wordOfTuple i t.val t.property.2.2) = tupleDegree t.val :=
  degree_tuple_encoding _ i t.val t.property.1 t.property.2.1
    (linearize_wordOfTuple i t.val t.property.2.2)

end
end MultiRunDegrees
