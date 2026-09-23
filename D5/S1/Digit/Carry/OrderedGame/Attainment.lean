/- GID: D5/S1/Digit/Carry/OrderedGame/Attainment
   generality: I
   mirror-B: D5/B/S1/Digit/Carry/OrderedGame/Attainment
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Exact inversion accounting for the ordered longest-game strategy. -/

import D5.S1.Digit.Carry.OrderedGame
import Mathlib.Data.List.Chain

namespace D5.S1.Digit.Carry.OrderedGame

open ListInversions

/-- The existing inversion counter vanishes exactly on nondecreasing raw states. -/
theorem inversions_zero_iff_sorted (s : List ℕ) :
    inv (decode s) = 0 ↔ s.Pairwise (· ≤ ·) := by
  induction s with
  | nil => simp [decode, inv]
  | cons x xs ih =>
    simp only [decode, List.map_cons, inv, Nat.add_eq_zero, List.pairwise_cons]
    change (inv (decode xs) = 0 ∧ _) ↔ _
    rw [ih]
    simp only [List.countP_eq_zero, List.mem_map, forall_exists_index, and_imp]
    constructor
    · rintro ⟨hs, h⟩
      refine ⟨?_, hs⟩
      intro y hy
      have := h (y + 1) y hy rfl
      simpa using this
    · rintro ⟨h, hs⟩
      refine ⟨hs, ?_⟩
      intro y z hz heq
      subst y
      simpa using h z hz

/-- Actual LGS selection makes every carry attain its full carry-and-sort reward.
The switch case retains every permitted adjacent inversion choice. -/
theorem lgs_move_potential {p a s t} (step : LGSMove p a s t) :
    1 + inv (decode t) = inv (decode s) + reward s a := by
  classical
  have shift (l : List ℕ) : inv (decode l) = inv l := by
    induction l with
    | nil => rfl
    | cons x xs ih =>
      simp only [decode, List.map_cons, inv] at *
      rw [ih, List.countP_map]
      simp [Function.comp_def]
  have sorted (ha : a ≠ .switch) : s.Pairwise (· ≤ ·) := by
    apply List.isChain_iff_pairwise.mp
    apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
    intro x y P S heq
    by_contra h
    have move : Move P.length .switch s (P ++ y :: x :: S) := by
      subst s
      simpa using Move.switch P S x y (by omega)
    have bad := step.2 _ _ _ move
    apply bad
    left
    cases a <;> simp_all [priority]
  obtain ⟨move, preferred⟩ := step
  rw [shift, shift]
  cases move with
  | switch P S i j h =>
    rw [inv_window, inv_window]
    simp [inv, reward, show ¬i < j by omega, h]
    omega
  | ones P S =>
    have hs := sorted (by simp)
    have hp : P = [] := by
      cases P with
      | nil => rfl
      | cons x xs =>
        have hx : x = 0 := by
          have := (List.pairwise_cons.mp hs).1 0 (by simp)
          omega
        subst x
        cases xs with
        | nil =>
          have hm : Move 0 .ones (0 :: [] ++ [0, 0] ++ S) ([1] ++ 0 :: S) :=
            Move.ones [] (0 :: S)
          have := preferred _ _ _ hm
          simp [Preferred, priority] at this
        | cons y ys =>
          have hy : y = 0 := by
            have htail := (List.pairwise_cons.mp hs).2
            have := (List.pairwise_cons.mp htail).1 0 (by simp)
            omega
          subst y
          have hm := Move.ones [] (ys ++ [0, 0] ++ S)
          have := preferred _ _ _ hm
          simp [Preferred, priority] at this
    subst P
    have si : inv S = 0 := by
      rw [← shift, inversions_zero_iff_sorted]
      exact (List.pairwise_append.mp hs).2.1
    have ct : S.countP (fun x => decide (x < 1)) = S.count 0 := by
      rw [List.count_eq_countP]
      apply List.countP_congr
      intro x hx
      simp only [decide_eq_true_eq, beq_iff_eq]
      omega
    simp only [List.nil_append, List.cons_append, List.nil_append, inv,
      List.countP_cons, List.countP_nil, Nat.lt_irrefl, decide_false, Bool.false_eq_true,
      ite_false, Nat.add_zero, si, ct]
    simp [reward, rawCounts, Multiset.toFinsupp_apply, Nat.add_comm]
  | twos P S =>
    have hs := sorted (by simp)
    simp only [List.pairwise_append, List.pairwise_cons, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, forall_eq_or_imp, forall_eq, and_true,
      true_and] at hs
    have pbound : ∀ x ∈ P, x ≤ 1 := fun x hx => (hs.1.2.2 x hx).1
    have sbound : ∀ x ∈ S, 1 ≤ x := fun x hx => hs.2.2 1 (by simp) x hx
    rw [inv_window, inv_window]
    simp only [inv, List.countP_cons, List.countP_nil, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, ← List.countP_eq_length_filter]
    have cp (k : ℕ) (hk : 1 ≤ k) : P.countP (fun x => decide (k < x)) = 0 := by
      apply List.countP_eq_zero.mpr
      intro x hx
      simp only [Bool.not_eq_true, decide_eq_false_iff_not]
      have := pbound x hx
      omega
    have cs (k : ℕ) (hk : k ≤ 1) : S.countP (fun x => decide (x < k)) = 0 := by
      apply List.countP_eq_zero.mpr
      intro x hx
      simp only [Bool.not_eq_true, decide_eq_false_iff_not]
      have := sbound x hx
      omega
    have c0 : P.countP (fun x => decide (0 < x)) = P.count 1 := by
      rw [List.count_eq_countP]
      apply List.countP_congr
      intro x hx
      have := pbound x hx
      simp only [decide_eq_true_eq, beq_iff_eq]
      omega
    have c2 : S.countP (fun x => decide (x < 2)) = S.count 1 := by
      rw [List.count_eq_countP]
      apply List.countP_congr
      intro x hx
      have := sbound x hx
      simp only [decide_eq_true_eq, beq_iff_eq]
      omega
    rw [cp 1 (by omega), cp 2 (by omega), cs 0 (by omega), cs 1 (by omega), c0, c2]
    simp [reward, rawCounts, Multiset.toFinsupp_apply,
      List.count_append]
    omega
  | split P S i =>
    have hs := sorted (by simp)
    have hp := (List.pairwise_append.mp (List.pairwise_append.mp hs).1).2.2
    have hb := (List.pairwise_append.mp hs).2.2
    have pbound : ∀ x ∈ P, x ≤ i + 2 := fun x hx => hp x hx (i + 2) (by simp)
    have sbound : ∀ x ∈ S, i + 2 ≤ x := fun x hx => hb (i + 2) (by simp) x hx
    have cp (k : ℕ) (hk : i + 2 ≤ k) : P.countP (fun x => decide (k < x)) = 0 := by
      apply List.countP_eq_zero.mpr
      intro x hx
      simp only [decide_eq_true_eq]
      have := pbound x hx
      omega
    have cs (k : ℕ) (hk : k ≤ i + 2) : S.countP (fun x => decide (x < k)) = 0 := by
      apply List.countP_eq_zero.mpr
      intro x hx
      simp only [decide_eq_true_eq]
      have := sbound x hx
      omega
    have low (L : List ℕ) (bound : ∀ x ∈ L, x ≤ i + 2) :
        L.countP (fun x => decide (i < x)) = L.count (i + 1) + L.count (i + 2) := by
      induction L with
      | nil => simp
      | cons x xs ih =>
        have hx := bound x (by simp)
        have tail := ih (fun y hy => bound y (by simp [hy]))
        simp only [List.countP_cons, List.count_cons, decide_eq_true_eq, beq_iff_eq]
        split_ifs <;> omega
    have high : S.countP (fun x => decide (x < i + 3)) = S.count (i + 2) := by
      rw [List.count_eq_countP]
      apply List.countP_congr
      intro x hx
      have := sbound x hx
      simp only [decide_eq_true_eq, beq_iff_eq]
      omega
    have absent : S.count (i + 1) = 0 := by
      rw [List.count_eq_zero]
      intro h
      have := sbound (i + 1) h
      omega
    rw [inv_window, inv_window]
    simp only [inv, List.countP_cons, List.countP_nil, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, ← List.countP_eq_length_filter]
    rw [cp (i + 2) (by omega), cp (i + 3) (by omega),
      cs i (by omega), cs (i + 2) (by omega), low P pbound, high]
    simp [reward, rawCounts, Multiset.toFinsupp_apply, List.count_append, absent,
      show ¬i + 3 < i by omega]
    omega
  | merge P S i =>
    have hs := sorted (by simp)
    have hp := (List.pairwise_append.mp (List.pairwise_append.mp hs).1).2.2
    have hb := (List.pairwise_append.mp hs).2.2
    have pbound : ∀ x ∈ P, x ≤ i := fun x hx => hp x hx i (by simp)
    have sbound : ∀ x ∈ S, i + 1 ≤ x := fun x hx => hb (i + 1) (by simp) x hx
    have cp (k : ℕ) (hk : i ≤ k) : P.countP (fun x => decide (k < x)) = 0 := by
      apply List.countP_eq_zero.mpr
      intro x hx
      simp only [decide_eq_true_eq]
      have := pbound x hx
      omega
    have cs (k : ℕ) (hk : k ≤ i + 1) : S.countP (fun x => decide (x < k)) = 0 := by
      apply List.countP_eq_zero.mpr
      intro x hx
      simp only [decide_eq_true_eq]
      have := sbound x hx
      omega
    have high : S.countP (fun x => decide (x < i + 2)) = S.count (i + 1) := by
      rw [List.count_eq_countP]
      apply List.countP_congr
      intro x hx
      have := sbound x hx
      simp only [decide_eq_true_eq, beq_iff_eq]
      omega
    have absent : P.count (i + 1) = 0 := by
      rw [List.count_eq_zero]
      intro h
      have := pbound (i + 1) h
      omega
    rw [inv_window, inv_window]
    simp only [inv, List.countP_cons, List.countP_nil, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, ← List.countP_eq_length_filter]
    rw [cp i (by omega), cp (i + 1) (by omega), cp (i + 2) (by omega),
      cs i (by omega), cs (i + 1) (by omega), high]
    simp [reward, rawCounts, Multiset.toFinsupp_apply, List.count_append, absent,
      show ¬i + 1 < i by omega]
    omega

/-- Exact telescoping holds for every permitted strategy path, without restricting
switch order, initial sortedness, or terminality. -/
theorem lgs_path_potential {s t : List ℕ} {length weight : ℕ}
    (path : LGSPath s t length weight) :
    length + inv (decode t) = inv (decode s) + weight := by
  induction path with
  | nil => simp
  | cons step tail ih => have := lgs_move_potential step; omega

/-- Every switch phase can finish, and every legal zero-reward path has the
same sorted endpoint and exact inversion length when no switch remains. -/
theorem switch_normalization (s : List ℕ) :
    ∃ t, LGSPath s t (inv (decode s)) 0 ∧ t.Pairwise (· ≤ ·) ∧ s.Perm t ∧
      ∀ u length, Path s u length 0 → (∀ p v, ¬Move p .switch u v) →
        u = t ∧ length = inv (decode s) ∧ rawCounts u = rawCounts s := by
  classical
  have no_switch (l : List ℕ) :
      (∀ p v, ¬Move p .switch l v) ↔ l.Pairwise (· ≤ ·) := by
    constructor
    · intro h
      apply List.isChain_iff_pairwise.mp
      apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
      intro x y P S heq
      by_contra hn
      have hm := Move.switch P S x y (by omega)
      apply h P.length (P ++ [y, x] ++ S)
      simpa [heq] using hm
    · intro h p v hm
      cases hm with
      | switch P S x y hxy =>
        have := (List.pairwise_append.mp (List.pairwise_append.mp h).1).2.1
        simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil,
          or_false, forall_eq] at this
        omega
  have zero_path {a b : List ℕ} {n w : ℕ} (path : Path a b n w) (hw : w = 0) :
      a.Perm b ∧ n + inv (decode b) = inv (decode a) := by
    induction path with
    | nil => exact ⟨List.Perm.refl _, by simp⟩
    | @cons p act a b c n w move tail ih =>
      have hw' : w = 0 := by omega
      have hr : reward a act = 0 := by omega
      obtain ⟨perm, eqn⟩ := ih hw'
      cases move with
      | switch P S i j hij =>
        have hm : LGSMove P.length .switch (P ++ [i, j] ++ S) (P ++ [j, i] ++ S) := by
          refine ⟨Move.switch P S i j hij, ?_⟩
          intro q b u hb
          cases b <;> simp [Preferred, priority]
        have eqn' := lgs_move_potential hm
        refine ⟨?_, ?_⟩
        · exact ((List.Perm.swap j i []).append_left P |>.append_right S).trans perm
        · simp only [reward] at eqn'
          omega
      | ones P S | twos P S | split P S i | merge P S i =>
        simp [reward, rawCounts, Multiset.toFinsupp_apply, List.count_append] at hr <;> omega
  have finish : ∀ n (l : List ℕ), inv (decode l) = n →
      ∃ t, LGSPath l t (inv (decode l)) 0 ∧ t.Pairwise (· ≤ ·) ∧ l.Perm t := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro l heq
      by_cases hs : l.Pairwise (· ≤ ·)
      · refine ⟨l, ?_, hs, List.Perm.refl _⟩
        rw [(inversions_zero_iff_sorted l).mpr hs]
        exact .nil l
      · have hn := mt (no_switch l).mp hs
        push Not at hn
        obtain ⟨p, v, hm⟩ := hn
        have hg : LGSMove p .switch l v := by
          refine ⟨hm, ?_⟩
          intro q b u hb
          cases b <;> simp [Preferred, priority]
        have eqn := lgs_move_potential hg
        simp only [reward, Nat.add_zero] at eqn
        obtain ⟨t, path, ht, perm⟩ := ih (inv (decode v)) (by omega) v rfl
        refine ⟨t, ?_, ht, ?_⟩
        · have hc := LGSPath.cons hg path
          simpa only [reward, Nat.zero_add, Nat.add_comm, eqn] using hc
        · cases hm with
          | switch P S i j hij =>
            exact ((List.Perm.swap j i []).append_left P |>.append_right S).trans perm
  obtain ⟨t, path, ht, perm⟩ := finish _ s rfl
  refine ⟨t, path, ht, perm, ?_⟩
  intro u length hp hn
  have hu := (no_switch u).mp hn
  obtain ⟨pu, eqn⟩ := zero_path hp rfl
  refine ⟨List.Perm.eq_of_pairwise' hu ht (pu.symm.trans perm), ?_, ?_⟩
  · rw [(inversions_zero_iff_sorted u).mpr hu] at eqn
    omega
  · apply congrArg Multiset.toFinsupp
    exact Quotient.sound pu.symm

end D5.S1.Digit.Carry.OrderedGame
