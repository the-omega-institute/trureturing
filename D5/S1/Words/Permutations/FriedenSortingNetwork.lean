/- GID: D5/S1/Words/Permutations/FriedenSortingNetwork
   generality: G
   mirror-B: D5/B/S1/Words/Permutations/FriedenSortingNetwork
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Chronological restriction of a reduced reversal word and its four-wire obstruction. -/

/- admission_basis: escape-witness.
   quartet_left: proof_shape: content. Its live escape_witness increasing_trace orders
   the labels of each crossing of a reduced reversal and constrains the retained word.
   left_ne_right: proof_shape: bind-only. Consumers include rank_step_move_right and mirror_step.
   Direct frozen dependencies: none. -/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Powerset

namespace D5.S1.Words.Permutations.Frieden

abbrev Word (n : Nat) := List (Fin (n - 1))
abbrev State (n : Nat) := Equiv.Perm (Fin n)
abbrev Orientation (n : Nat) := Fin (n - 2) → Bool

def left {n : Nat} (i : Fin (n - 1)) : Fin n := ⟨i.val, by omega⟩

def right {n : Nat} (i : Fin (n - 1)) : Fin n := ⟨i.val + 1, by omega⟩

def step {n : Nat} (p : State n) (i : Fin (n - 1)) : State n :=
  (Equiv.swap (left i) (right i)).trans p

def endpoints {n : Nat} (p : State n) (i : Fin (n - 1)) : Fin n × Fin n :=
  (p (left i), p (right i))

def crossingPairsFrom {n : Nat} (p : State n) : Word n → List (Fin n × Fin n)
  | [] => []
  | i :: rest => endpoints p i :: crossingPairsFrom (step p i) rest

def restrictFrom {n : Nat} (S : Finset (Fin n)) (p : State n) : Word n → List Nat
  | [] => []
  | i :: rest =>
      let tail := restrictFrom S (step p i) rest
      if p (left i) ∈ S ∧ p (right i) ∈ S then
        (((List.finRange n).take i.val).countP (fun j => decide (p j ∈ S)) + 1) :: tail
      else tail

def restrict {n : Nat} (w : Word n) (S : Finset (Fin n)) : List Nat :=
  restrictFrom S (Equiv.refl _) w

def forbidden : List (List Nat) :=
  [[1,2,3,2,1,2], [3,2,1,2,3,2], [2,1,2,3,2,1], [2,3,2,1,2,3]]

def AvoidsX {n : Nat} (w : Word n) : Prop :=
  ∀ S : Finset (Fin n), S.card = 4 → restrict w S ∉ forbidden

def ReducedReversal {n : Nat} (w : Word n) : Prop :=
  w.length = n * (n - 1) / 2 ∧ w.foldl step (Equiv.refl _) = Fin.revPerm

theorem left_ne_right {n : Nat} (i : Fin (n - 1)) : left i ≠ right i := by
  intro h
  have hv := congrArg Fin.val h
  exact (Nat.ne_of_lt (Nat.lt_succ_self i.val)) hv

private theorem swap_order_of_not_hit {n : Nat} (i : Fin (n - 1)) (a b : Fin n)
    (h₁ : ¬(a = left i ∧ b = right i))
    (h₂ : ¬(a = right i ∧ b = left i)) :
    Equiv.swap (left i) (right i) a < Equiv.swap (left i) (right i) b ↔ a < b := by
  have hpos : (right i).val = (left i).val + 1 := rfl
  have hne := left_ne_right i
  by_cases hal : a = left i <;> by_cases har : a = right i <;>
    by_cases hbl : b = left i <;> by_cases hbr : b = right i
  all_goals simp_all [Equiv.swap_apply_def]
  all_goals simp only [Fin.lt_def, Fin.ext_iff] at *
  all_goals omega

private def crossingSetsFrom {n : Nat} (p : State n) (w : Word n) : List (Finset (Fin n)) :=
  (crossingPairsFrom p w).map (fun (a,b) => {a,b})

private theorem order_step_of_not_crossed {n : Nat} (p : State n) (i : Fin (n - 1))
    (a b : Fin n) (h : {a,b} ≠ ({p (left i),p (right i)} : Finset (Fin n))) :
    (step p i).symm a < (step p i).symm b ↔ p.symm a < p.symm b := by
  simp only [step, Equiv.symm_trans_apply, Equiv.symm_swap]
  apply swap_order_of_not_hit
  · rintro ⟨ha, hb⟩
    have ha' : a = p (left i) := by simpa using congrArg p ha
    have hb' : b = p (right i) := by simpa using congrArg p hb
    exact h (by rw [ha', hb'])
  · rintro ⟨ha, hb⟩
    have ha' : a = p (right i) := by simpa using congrArg p ha
    have hb' : b = p (left i) := by simpa using congrArg p hb
    exact h (by rw [ha', hb', Finset.pair_comm])

private theorem order_replay_of_not_crossed {n : Nat} (w : Word n) (p : State n)
    (a b : Fin n) (h : {a,b} ∉ crossingSetsFrom p w) :
    (w.foldl step p).symm a < (w.foldl step p).symm b ↔ p.symm a < p.symm b := by
  induction w generalizing p with
  | nil => rfl
  | cons i rest ih =>
    simp only [crossingSetsFrom, crossingPairsFrom, endpoints, List.map_cons,
      List.mem_cons, not_or] at h
    exact (ih (step p i) h.2).trans (order_step_of_not_crossed p i a b h.1)

private theorem pair_occurs {n : Nat} (w : Word n)
    (h : w.foldl step (Equiv.refl _) = Fin.revPerm) {a b : Fin n} (hne : a ≠ b) :
    {a,b} ∈ crossingSetsFrom (Equiv.refl _) w := by
  by_contra hab
  have hord := order_replay_of_not_crossed w (Equiv.refl _) a b hab
  rw [h] at hord
  simp only [Fin.revPerm_symm, Fin.revPerm_apply, Fin.rev_lt_rev,
    Equiv.refl_symm, Equiv.refl_apply] at hord
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (not_lt_of_ge hlt.le) (hord.mpr hlt)
  · exact (not_lt_of_ge hgt.le) (hord.mp hgt)

private theorem crossingSetsFrom_length {n : Nat} (w : Word n) (p : State n) :
    (crossingSetsFrom p w).length = w.length := by
  induction w generalizing p with
  | nil => rfl
  | cons i rest ih =>
    change (crossingSetsFrom (step p i) rest).length + 1 = rest.length + 1
    rw [ih]

private theorem pair_uniqueness {n : Nat} (w : Word n) (h : ReducedReversal w) :
    (crossingSetsFrom (Equiv.refl _) w).Nodup := by
  let pairs := crossingSetsFrom (Equiv.refl _) w
  have hsubset : Finset.powersetCard 2 (Finset.univ : Finset (Fin n)) ⊆ pairs.toFinset := by
    intro s hs
    have hcard : s.card = 2 := (Finset.mem_powersetCard.mp hs).2
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
    exact List.mem_toFinset.mpr (pair_occurs w h.2 hab)
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
    Nat.choose_two_right, ← h.1, ← crossingSetsFrom_length w (Equiv.refl _)] at hcard
  have hEq : pairs.toFinset.card = pairs.length :=
    le_antisymm (List.toFinset_card_le pairs) hcard
  exact Multiset.toFinset_card_eq_card_iff_nodup.mp hEq

private theorem crossingSetsFrom_cons {n : Nat} (p : State n) (i : Fin (n - 1)) (v : Word n) :
    crossingSetsFrom p (i :: v) =
      {p (left i), p (right i)} :: crossingSetsFrom (step p i) v := rfl

private theorem crossingSetsFrom_append {n : Nat} (u v : Word n) (p : State n) :
    crossingSetsFrom p (u ++ v) =
      crossingSetsFrom p u ++ crossingSetsFrom (u.foldl step p) v := by
  induction u generalizing p with
  | nil => rfl
  | cons i u ih => simp [crossingSetsFrom_cons, ih]

private theorem swaps_increasing {n : Nat} (u v : Word n) (i : Fin (n - 1))
    (h : ReducedReversal (u ++ i :: v)) :
    let p := u.foldl step (Equiv.refl _)
    p (left i) < p (right i) := by
  let p := u.foldl step (Equiv.refl _)
  let a := p (left i)
  let b := p (right i)
  have hnodup := pair_uniqueness _ h
  rw [crossingSetsFrom_append] at hnodup
  change (crossingSetsFrom (Equiv.refl _) u ++ crossingSetsFrom p (i :: v)).Nodup at hnodup
  have hb : {a,b} ∈ crossingSetsFrom p (i :: v) := by simp [crossingSetsFrom_cons, a, b]
  have hmiss : {a,b} ∉ crossingSetsFrom (Equiv.refl _) u := by
    intro ha
    exact (List.nodup_append.mp hnodup).2.2 {a,b} ha {a,b} hb rfl
  have hord := order_replay_of_not_crossed u (Equiv.refl _) a b hmiss
  change p.symm a < p.symm b ↔ a < b at hord
  apply hord.mp
  simp [a, b, left, right, Fin.lt_def]

private theorem mem_take_finRange {n k : Nat} (j : Fin n) :
    j ∈ (List.finRange n).take k ↔ j.val < k := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨m, hm, he⟩
    rw [List.getElem_take, List.getElem_finRange] at he
    have hval := congrArg Fin.val he
    simp [List.length_take] at hm
    exact hval ▸ hm.1
  · intro h
    refine ⟨j.val, by simp [List.length_take, h, j.isLt], ?_⟩
    rw [List.getElem_take, List.getElem_finRange]
    rfl

def below {n : Nat} (S : Finset (Fin n)) (p : State n) (a : Fin n) :=
  S.filter (fun b => p.symm b < p.symm a)

def rank {n : Nat} (S : Finset (Fin n)) (p : State n) (a : Fin n) :=
  (below S p a).card

private theorem rank_left {n : Nat} (S : Finset (Fin n)) (p : State n)
    (i : Fin (n - 1)) :
    ((List.finRange n).take i.val).countP (fun j => decide (p j ∈ S)) =
      rank S p (p (left i)) := by
  let L := ((List.finRange n).take i.val).filter (fun j => decide (p j ∈ S))
  have hn : L.Nodup := ((List.nodup_finRange n).sublist (List.take_sublist _ _)).filter _
  have he : L.toFinset.map p.toEmbedding = below S p (p (left i)) := by
    ext b
    simp only [Finset.mem_map, Equiv.toEmbedding_apply, List.mem_toFinset, L,
      List.mem_filter, decide_eq_true_eq, mem_take_finRange, below, Finset.mem_filter,
      Equiv.symm_apply_apply]
    constructor
    · rintro ⟨j, ⟨hj, hb⟩, rfl⟩
      exact ⟨hb, by simpa [Fin.lt_def, left] using hj⟩
    · rintro ⟨hb, hj⟩
      exact ⟨p.symm b, ⟨hj, by simpa using hb⟩, p.apply_symm_apply b⟩
  rw [List.countP_eq_length_filter]
  change L.length = _
  rw [rank, ← he, Finset.card_map, List.toFinset_card_of_nodup hn]

theorem restrict_cons {n : Nat} (S : Finset (Fin n)) (p : State n)
    (i : Fin (n - 1)) (w : Word n) :
    restrictFrom S p (i :: w) =
      if p (left i) ∈ S ∧ p (right i) ∈ S then
        (rank S p (p (left i)) + 1) :: restrictFrom S (step p i) w
      else restrictFrom S (step p i) w := by
  rw [restrictFrom, rank_left]

private theorem restrict_append {n : Nat} (S : Finset (Fin n)) (p : State n)
    (u v : Word n) :
    restrictFrom S p (u ++ v) =
      restrictFrom S p u ++ restrictFrom S (u.foldl step p) v := by
  induction u generalizing p with
  | nil => rfl
  | cons i u ih =>
    by_cases h : p (left i) ∈ S ∧ p (right i) ∈ S <;>
      simp [restrict_cons, h, ih]

private theorem crossing_append {n : Nat} (p : State n) (u v : Word n) :
    crossingPairsFrom p (u ++ v) =
      crossingPairsFrom p u ++ crossingPairsFrom (u.foldl step p) v := by
  induction u generalizing p with
  | nil => rfl
  | cons i u ih => simp [crossingPairsFrom, ih]

private theorem increasing_trace {n : Nat} {w : Word n} (hw : ReducedReversal w) :
    ∀ q ∈ crossingPairsFrom (Equiv.refl _) w, q.1 < q.2 := by
  have aux (u v : Word n) (h : w = u ++ v) :
      ∀ q ∈ crossingPairsFrom (u.foldl step (Equiv.refl _)) v, q.1 < q.2 := by
    induction v generalizing u with
    | nil => simp [crossingPairsFrom]
    | cons i v ih =>
      intro q hq
      rw [crossingPairsFrom, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact swaps_increasing u v i (h ▸ hw)
      · apply ih (u ++ [i]) (by simpa using h) q
        simpa using hq
  exact aux [] w rfl

private theorem pos_step {n : Nat} (p : State n) (i : Fin (n - 1)) (a : Fin n) :
    (step p i).symm a = Equiv.swap (left i) (right i) (p.symm a) := by
  simp [step]

private theorem pos_step_left {n : Nat} (p : State n) (i : Fin (n - 1)) :
    (step p i).symm (p (left i)) = right i := by simp [pos_step]

private theorem pos_step_right {n : Nat} (p : State n) (i : Fin (n - 1)) :
    (step p i).symm (p (right i)) = left i := by simp [pos_step]

private theorem pos_before_cross {n : Nat} (p : State n) (w : Word n)
    (hn : (crossingSetsFrom p w).Nodup) {a b : Fin n}
    (hab : (a,b) ∈ crossingPairsFrom p w) : p.symm a < p.symm b := by
  have splitCross {p : State n} {w : Word n}
      (hab : (a,b) ∈ crossingPairsFrom p w) :
      ∃ s i t, w = s ++ i :: t ∧ endpoints (s.foldl step p) i = (a,b) := by
    induction w generalizing p with
    | nil => simp [crossingPairsFrom] at hab
    | cons i w ih =>
      rw [crossingPairsFrom, List.mem_cons] at hab
      rcases hab with hab | hab
      · exact ⟨[], i, w, rfl, hab.symm⟩
      · obtain ⟨s, j, t, rfl, hj⟩ := ih hab
        exact ⟨i :: s, j, t, rfl, hj⟩
  obtain ⟨s, i, t, rfl, hi⟩ := splitCross hab
  rw [crossingSetsFrom_append, crossingSetsFrom_cons] at hn
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hi.symm
  have hmiss : {(s.foldl step p) (left i), (s.foldl step p) (right i)} ∉
      crossingSetsFrom p s := by
    intro hm
    exact (List.nodup_append.mp hn).2.2 _ hm _ (by simp) rfl
  apply (order_replay_of_not_crossed s p _ _ hmiss).mp
  simp [left, right, Fin.lt_def]

private theorem pos_after_cross {n : Nat} (p : State n) (w : Word n)
    (hn : (crossingSetsFrom p w).Nodup) {a b : Fin n}
    (hab : (a,b) ∈ crossingPairsFrom p w) :
    (w.foldl step p).symm b < (w.foldl step p).symm a := by
  induction w generalizing p with
  | nil => simp [crossingPairsFrom] at hab
  | cons i w ih =>
    rw [crossingPairsFrom, List.mem_cons] at hab
    rcases List.nodup_cons.mp hn with ⟨hm, hn'⟩
    rcases hab with hab | hab
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hab
      have hmiss : {p (right i),p (left i)} ∉ crossingSetsFrom (step p i) w := by
        rw [Finset.pair_comm]
        exact hm
      rw [List.foldl_cons, order_replay_of_not_crossed w (step p i) _ _ hmiss,
        pos_step_right, pos_step_left]
      simp [left, right, Fin.lt_def]
    · exact ih _ hn' hab

private theorem pair_mem_iff {n : Nat} (p : State n) (w : Word n) (a b : Fin n)
    (hne : a ≠ b) :
    {a,b} ∈ crossingSetsFrom p w ↔
      (a,b) ∈ crossingPairsFrom p w ∨ (b,a) ∈ crossingPairsFrom p w := by
  simp only [crossingSetsFrom, List.mem_map]
  constructor
  · rintro ⟨⟨x,y⟩, h, he⟩
    have ha : a = x ∨ a = y := by
      have : a ∈ ({x,y} : Finset (Fin n)) := by rw [he]; simp
      simpa using this
    have hb : b = x ∨ b = y := by
      have : b ∈ ({x,y} : Finset (Fin n)) := by rw [he]; simp
      simpa using this
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all
  · rintro (h | h)
    · exact ⟨(a,b), h, rfl⟩
    · exact ⟨(b,a), h, Finset.pair_comm _ _⟩

private theorem pos_unchanged_order {n : Nat} (p : State n) (i : Fin (n - 1))
    (a b : Fin n)
    (h₁ : ¬(a = p (left i) ∧ b = p (right i)))
    (h₂ : ¬(a = p (right i) ∧ b = p (left i))) :
    (step p i).symm a < (step p i).symm b ↔ p.symm a < p.symm b := by
  rw [pos_step, pos_step]
  apply swap_order_of_not_hit
  · simpa [Equiv.symm_apply_eq] using h₁
  · simpa [Equiv.symm_apply_eq] using h₂

theorem rank_step_stay {n : Nat} (S : Finset (Fin n)) (p : State n)
    (i : Fin (n - 1)) (a : Fin n) (ha : a ∈ S)
    (h : ¬(p (left i) ∈ S ∧ p (right i) ∈ S)) :
    rank S (step p i) a = rank S p a := by
  unfold rank
  congr 1
  ext b
  simp only [below, Finset.mem_filter]
  by_cases hb : b ∈ S
  · simp only [hb, true_and]
    apply pos_unchanged_order
    · rintro ⟨rfl, he⟩
      exact h ⟨hb, he ▸ ha⟩
    · rintro ⟨rfl, he⟩
      exact h ⟨he ▸ ha, hb⟩
  · simp [hb]

theorem rank_step_move_right {n : Nat} (S : Finset (Fin n)) (p : State n)
    (i : Fin (n - 1)) (hr : p (right i) ∈ S) :
    rank S (step p i) (p (left i)) = rank S p (p (left i)) + 1 := by
  have hne : p (right i) ≠ p (left i) := fun h => left_ne_right i (p.injective h.symm)
  have he : below S (step p i) (p (left i)) =
      insert (p (right i)) (below S p (p (left i))) := by
    ext b
    by_cases hb : b = p (right i)
    · subst b
      simp only [below, Finset.mem_filter, Finset.mem_insert, true_or]
      rw [pos_step_left, pos_step_right]
      exact iff_true_intro ⟨hr, by simp [Fin.lt_def, left, right]⟩
    · rw [Finset.mem_insert]
      simp only [hb, false_or, below, Finset.mem_filter]
      rw [pos_unchanged_order p i _ _ (by simp [hne.symm]) (by simp [hb])]
  have hm : p (right i) ∉ below S p (p (left i)) := by
    simp [below, Fin.lt_def, left, right]
  rw [rank, he, Finset.card_insert_of_notMem hm]
  rfl

theorem rank_right_before {n : Nat} (S : Finset (Fin n)) (p : State n)
    (i : Fin (n - 1)) (hl : p (left i) ∈ S) :
    rank S p (p (right i)) = rank S p (p (left i)) + 1 := by
  have he : below S p (p (right i)) =
      insert (p (left i)) (below S p (p (left i))) := by
    ext b
    simp only [below, Finset.mem_filter, Finset.mem_insert, Equiv.symm_apply_apply]
    have hb : b = p (left i) ↔ p.symm b = left i := by
      rw [Equiv.symm_apply_eq, eq_comm]
    rw [hb]
    simp only [Fin.lt_def, Fin.ext_iff, left, right]
    by_cases hm : b ∈ S
    · simp only [hm, true_and]
      omega
    · have hn : p.symm b ≠ left i := fun h => hm ((hb.mpr h).symm ▸ hl)
      simp only [hm, false_and, or_false, false_iff]
      exact fun h => hn (Fin.ext h)
  have hm : p (left i) ∉ below S p (p (left i)) := by simp [below]
  rw [rank, he, Finset.card_insert_of_notMem hm]
  rfl

theorem rank_step_move_left {n : Nat} (S : Finset (Fin n)) (p : State n)
    (i : Fin (n - 1)) (hl : p (left i) ∈ S) :
    rank S (step p i) (p (right i)) = rank S p (p (left i)) := by
  have hs : step p i (left i) = p (right i) := by simp [step]
  have hr : step p i (right i) = p (left i) := by simp [step]
  have he : step (step p i) i = p := by
    ext j
    simp [step]
  have h := rank_step_move_right S (step p i) i (hr.symm ▸ hl)
  rw [he, hs, rank_right_before S p i hl] at h
  omega

private def selected {n : Nat} (S : Finset (Fin n)) (q : Fin n × Fin n) : Prop :=
  q.1 ∈ S ∧ q.2 ∈ S

private theorem restrict_empty_of {n : Nat} (S : Finset (Fin n)) (p : State n)
    (w : Word n) (h : ∀ q ∈ crossingPairsFrom p w, ¬selected S q) :
    restrictFrom S p w = [] := by
  induction w generalizing p with
  | nil => rfl
  | cons i w ih =>
    have hm : ¬(p (left i) ∈ S ∧ p (right i) ∈ S) :=
      h (endpoints p i) (by simp [crossingPairsFrom])
    rw [restrict_cons, ite_eq_right hm]
    exact ih _ (fun q hq => h q (by simp [crossingPairsFrom, hq]))

private theorem restrict_moving_right {n : Nat} (S : Finset (Fin n)) (p : State n)
    (w : Word n) (r : Fin n) (hr : r ∈ S)
    (h : ∀ q ∈ crossingPairsFrom p w, selected S q → q.1 = r) :
    let a := rank S p r
    let b := rank S (w.foldl step p) r
    a ≤ b ∧ restrictFrom S p w = List.range' (a + 1) (b - a) := by
  dsimp only
  induction w generalizing p with
  | nil => simp [restrictFrom]
  | cons i w ih =>
    have ht := ih (step p i) (fun q hq => h q (by simp [crossingPairsFrom, hq]))
    rw [List.foldl_cons]
    rw [restrict_cons]
    by_cases hm : selected S (endpoints p i)
    · have he : p (left i) = r := h _ (by simp [crossingPairsFrom]) hm
      have he' : rank S (step p i) r = rank S p r + 1 := by
        rw [← he]
        exact rank_step_move_right S p i hm.2
      rw [ite_eq_left (show p (left i) ∈ S ∧ p (right i) ∈ S from hm), he]
      rw [he'] at ht
      have hb : rank S (w.foldl step (step p i)) r - rank S p r =
          (rank S (w.foldl step (step p i)) r - (rank S p r + 1)) + 1 := by omega
      exact ⟨by omega, by rw [hb, List.range'_succ, ht.2]⟩
    · rw [ite_eq_right (show ¬(p (left i) ∈ S ∧ p (right i) ∈ S) from hm)]
      rw [rank_step_stay S p i r hr hm] at ht
      exact ht

private theorem restrict_moving_left {n : Nat} (S : Finset (Fin n)) (p : State n)
    (w : Word n) (r : Fin n) (hr : r ∈ S)
    (h : ∀ q ∈ crossingPairsFrom p w, selected S q → q.2 = r) :
    let a := rank S p r
    let b := rank S (w.foldl step p) r
    b ≤ a ∧ restrictFrom S p w = (List.range' (b + 1) (a - b)).reverse := by
  dsimp only
  induction w generalizing p with
  | nil => simp [restrictFrom]
  | cons i w ih =>
    have ht := ih (step p i) (fun q hq => h q (by simp [crossingPairsFrom, hq]))
    rw [List.foldl_cons]
    rw [restrict_cons]
    by_cases hm : selected S (endpoints p i)
    · have he : p (right i) = r := h _ (by simp [crossingPairsFrom]) hm
      have hs : rank S (step p i) r = rank S p (p (left i)) := by
        rw [← he]
        exact rank_step_move_left S p i hm.1
      have he' : rank S p r = rank S p (p (left i)) + 1 := by
        rw [← he]
        exact rank_right_before S p i hm.1
      rw [ite_eq_left (show p (left i) ∈ S ∧ p (right i) ∈ S from hm), ht.2, hs, he']
      rw [hs] at ht
      have hb : rank S p (p (left i)) + 1 - rank S (w.foldl step (step p i)) r =
          (rank S p (p (left i)) - rank S (w.foldl step (step p i)) r) + 1 := by omega
      rw [hb, List.range'_concat, List.reverse_append]
      simp only [List.reverse_singleton, List.singleton_append, Nat.one_mul, List.cons.injEq,
        and_true]
      exact ⟨by omega, by omega⟩
    · rw [ite_eq_right (show ¬(p (left i) ∈ S ∧ p (right i) ∈ S) from hm)]
      rw [rank_step_stay S p i r hr hm] at ht
      exact ht

private theorem pos_fold_middle {n : Nat} (i : Fin (n - 1)) (m : Word n)
    (hm : ∀ j ∈ m, j.val ≠ i.val ∧ j.val ≠ i.val + 1)
    (p : State n) (a : Fin n) :
    let c := i.val + 1
    let a₀ := (p.symm a).val
    let a₁ := ((m.foldl step p).symm a).val
    (a₁ < c ↔ a₀ < c) ∧ (a₁ = c ↔ a₀ = c) ∧ (c < a₁ ↔ c < a₀) := by
  dsimp only
  induction m generalizing p with
  | nil => exact ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩
  | cons j m ih =>
    have hj := hm j (by simp)
    have ht := ih (fun k hk => hm k (by simp [hk])) (step p j)
    rw [List.foldl_cons, ht.1, ht.2.1, ht.2.2, pos_step]
    rw [Equiv.swap_apply_def]
    split
    · rename_i h
      rw [h]
      simp only [left, right]
      omega
    · split
      · rename_i h
        rw [h]
        simp only [left, right]
        omega
      · exact ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

private theorem pos_split_middle {n : Nat} (i : Fin (n - 1)) (m : Word n)
    (hm : ∀ j ∈ m, j.val ≠ i.val ∧ j.val ≠ i.val + 1)
    (p : State n) {a b : Fin n} (hab : (a,b) ∈ crossingPairsFrom p m) :
    let c := i.val + 1
    (((p.symm a).val < c ∧ (p.symm b).val < c) ∨
      (c < (p.symm a).val ∧ c < (p.symm b).val)) := by
  dsimp only
  induction m generalizing p with
  | nil => simp [crossingPairsFrom] at hab
  | cons j m ih =>
    rw [crossingPairsFrom, List.mem_cons] at hab
    rcases hab with hab | hab
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hab
      simp only [Equiv.symm_apply_apply, left, right]
      have hj := hm j (by simp)
      omega
    · have h := ih (fun k hk => hm k (by simp [hk])) (step p j) hab
      have ha := pos_fold_middle i [j] (by simpa using hm j (by simp)) p a
      have hb := pos_fold_middle i [j] (by simpa using hm j (by simp)) p b
      change ((_ < _ ↔ _) ∧ (_ = _ ↔ _) ∧ (_ < _ ↔ _)) at ha hb
      exact h.imp (fun h => ⟨ha.1.mp h.1, hb.1.mp h.2⟩)
        (fun h => ⟨ha.2.2.mp h.1, hb.2.2.mp h.2⟩)

private theorem rank_rightmost {n : Nat} (S : Finset (Fin n)) (p : State n) (a : Fin n)
    (ha : a ∈ S) (h : ∀ b ∈ S, b ≠ a → p.symm b < p.symm a) :
    rank S p a = S.card - 1 := by
  have he : below S p a = S.erase a := by
    ext b
    simp only [below, Finset.mem_filter, Finset.mem_erase]
    exact ⟨fun ⟨hb, hn⟩ => ⟨ne_of_lt hn ∘ congrArg p.symm, hb⟩,
      fun ⟨hne, hb⟩ => ⟨hb, h b hb hne⟩⟩
  rw [rank, he, Finset.card_erase_of_mem ha]

private theorem rank_reversal {n : Nat} (S : Finset (Fin n)) (a : Fin n)
    (ha : a ∈ S) :
    rank S (Equiv.refl _) a + rank S Fin.revPerm a + 1 = S.card := by
  have he : S.filter (fun b => ¬b < a) = insert a (below S Fin.revPerm a) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_insert, below,
      Fin.revPerm_symm, Fin.revPerm_apply, Fin.rev_lt_rev]
    by_cases hb : b = a
    · simp [hb, ha]
    · rw [not_lt]
      have hn : a ≠ b := Ne.symm hb
      simp [hb, lt_iff_le_and_ne, hn]
  have hn : a ∉ below S Fin.revPerm a := by simp [below]
  have h := Finset.card_filter_add_card_filter_not (s := S) (· < a)
  rw [he, Finset.card_insert_of_notMem hn] at h
  rw [← Nat.add_assoc] at h
  exact h

private theorem restrict_single_of {n : Nat} (S : Finset (Fin n)) (p : State n)
    (w : Word n) (ab : Fin n × Fin n) (k : Nat)
    (hn : (crossingSetsFrom p w).Nodup)
    (hab : ab ∈ crossingPairsFrom p w)
    (hs : selected S ab)
    (ho : ∀ q ∈ crossingPairsFrom p w, selected S q → q = ab)
    (hk : ∀ u i v, w = u ++ i :: v →
      endpoints (u.foldl step p) i = ab →
      rank S (u.foldl step p) ab.1 = k) :
    restrictFrom S p w = [k + 1] := by
  induction w generalizing p with
  | nil => simp [crossingPairsFrom] at hab
  | cons i w ih =>
    rw [restrict_cons]
    by_cases hm : p (left i) ∈ S ∧ p (right i) ∈ S
    · have he := ho (endpoints p i) (by simp [crossingPairsFrom]) hm
      have hr := hk [] i w rfl he
      change rank S p ab.1 = k at hr
      have ha : p (left i) = ab.1 := congrArg Prod.fst he
      have hmiss := (List.nodup_cons.mp (by rwa [crossingSetsFrom_cons] at hn)).1
      have hnil : restrictFrom S (step p i) w = [] := by
        apply restrict_empty_of
        intro q hq hqs
        have he' := ho q (by simp [crossingPairsFrom, hq]) hqs
        apply hmiss
        apply List.mem_map.mpr
        exact ⟨q, hq, by rw [he', ← he]; rfl⟩
      rw [ite_eq_left hm, ha, hr, hnil]
    · rw [ite_eq_right hm]
      apply ih (step p i) (List.nodup_cons.mp hn).2
      · rw [crossingPairsFrom, List.mem_cons] at hab
        exact hab.resolve_left (fun h => hm (show selected S (endpoints p i) from h ▸ hs))
      · exact fun q hq => ho q (by simp [crossingPairsFrom, hq])
      · intro u j v h hu
        exact hk (i :: u) j v (congrArg (i :: ·) h) hu

private theorem right_quartet_words (k : Nat) (hk : k ≤ 3) :
    List.range' (k + 1) (3 - k) ++ [2,1,2] ++
      (List.range' (3 - k + 1) k).reverse ∈ forbidden := by
  have h : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem quartet_left {n : Nat} (u m v : Word n) (i : Fin (n - 1))
    (hi : i.val + 2 < n)
    (hm : ∀ j ∈ m, j.val ≠ i.val ∧ j.val ≠ i.val + 1)
    (hw : ReducedReversal (u ++ (i :: m ++ i :: v))) :
    ∃ S : Finset (Fin n), S.card = 4 ∧ restrict (u ++ (i :: m ++ i :: v)) S ∈ forbidden := by
  let p := u.foldl step (Equiv.refl (Fin n))
  let pA := step p i
  let q := m.foldl step pA
  let qB := step q i
  let x := p (left i)
  let y := p (right i)
  let z := q (left i)
  let r := p ⟨i.val + 2, hi⟩
  have hword : u ++ (i :: m ++ i :: v) = (u ++ i :: m) ++ i :: v := by
    simp [List.append_assoc]
  have hxy : x < y := swaps_increasing u (m ++ i :: v) i hw
  have hzpos : q.symm z = left i := q.symm_apply_apply _
  have hxa : pA.symm x = right i := pos_step_left p i
  have hya : pA.symm y = left i := pos_step_right p i
  have hxp : p.symm x = left i := p.symm_apply_apply _
  have hyp : p.symm y = right i := p.symm_apply_apply _
  have hrp : (p.symm r).val = i.val + 2 := congrArg Fin.val (p.symm_apply_apply _)
  have hra : (pA.symm r).val = i.val + 2 := by
    change ((step p i).symm r).val = _
    rw [pos_step, Equiv.swap_apply_of_ne_of_ne]
    · exact hrp
    · intro h
      have := congrArg Fin.val h
      change (p.symm r).val = i.val at this
      omega
    · intro h
      have := congrArg Fin.val h
      change (p.symm r).val = i.val + 1 at this
      omega
  have hxq : q.symm x = right i := by
    apply Fin.ext
    exact (pos_fold_middle i m hm pA x).2.1.mpr (congrArg Fin.val hxa)
  have hxq' : q (right i) = x := by rw [← hxq, Equiv.apply_symm_apply]
  have hzx : z < x := by
    have h := swaps_increasing (u ++ i :: m) v i (hword ▸ hw)
    change ((u ++ i :: m).foldl step (Equiv.refl _)) (left i) <
      ((u ++ i :: m).foldl step (Equiv.refl _)) (right i) at h
    rw [List.foldl_append, List.foldl_cons] at h
    change z < q (right i) at h
    rwa [hxq'] at h
  have hza : (pA.symm z).val < i.val + 1 :=
    (pos_fold_middle i m hm pA z).1.mp (by rw [hzpos]; exact Nat.lt_succ_self _)
  have hyq : (q.symm y).val < i.val + 1 :=
    (pos_fold_middle i m hm pA y).1.mpr (by rw [hya]; exact Nat.lt_succ_self _)
  have hrq : i.val + 1 < (q.symm r).val :=
    (pos_fold_middle i m hm pA r).2.2.mpr (by omega)
  have hrx : r ≠ x := by
    intro h
    rw [h, hxq] at hrq
    exact (Nat.lt_irrefl _) hrq
  have hry : r ≠ y := by
    intro h
    rw [h] at hrq
    omega
  have hrz : r ≠ z := by
    intro h
    rw [h, hzpos] at hrq
    exact (Nat.not_succ_le_self _) (Nat.le_of_lt hrq)
  have hzy : z < y := hzx.trans hxy
  have hzp : (p.symm z).val < i.val := by
    have hne₁ : p.symm z ≠ left i := by
      intro he
      exact hzx.ne (p.symm.injective (he.trans hxp.symm))
    have hne₂ : p.symm z ≠ right i := by
      intro he
      exact hzy.ne (p.symm.injective (he.trans hyp.symm))
    change ((step p i).symm z).val < i.val + 1 at hza
    rw [pos_step, Equiv.swap_apply_of_ne_of_ne hne₁ hne₂] at hza
    have hv : (p.symm z).val ≠ i.val := fun h => hne₁ (Fin.ext h)
    omega
  have hzyA : pA.symm z < pA.symm y := by
    rw [hya]
    have hne : (pA.symm z).val ≠ i.val := by
      intro hh
      exact hzy.ne (pA.symm.injective ((Fin.ext hh).trans hya.symm))
    exact show (pA.symm z).val < i.val by omega
  have hyzq : q.symm y < q.symm z := by
    rw [hzpos]
    have hne : (q.symm y).val ≠ i.val := by
      intro hh
      exact hzy.ne (q.symm.injective ((Fin.ext hh).trans hzpos.symm)).symm
    exact show (q.symm y).val < i.val by omega
  let S : Finset (Fin n) := {z,x,y,r}
  have hcard : S.card = 4 := by
    change ({z,x,y,r} : Finset (Fin n)).card = 4
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    all_goals simp [hzx.ne, hzy.ne, hxy.ne, Ne.symm hrz, Ne.symm hrx, Ne.symm hry]
  have hmem (a : Fin n) : a ∈ S ↔ a = z ∨ a = x ∨ a = y ∨ a = r := by
    simp [S]
  have hzS := (hmem z).mpr (Or.inl rfl)
  have hxS := (hmem x).mpr (Or.inr (Or.inl rfl))
  have hyS := (hmem y).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hrS := (hmem r).mpr (Or.inr (Or.inr (Or.inr rfl)))
  have hset : (crossingSetsFrom (Equiv.refl _) u ++
      (crossingSetsFrom p (i :: m ++ [i]) ++ crossingSetsFrom qB v)).Nodup := by
    have h := pair_uniqueness _ hw
    rw [crossingSetsFrom_append] at h
    change (crossingSetsFrom (Equiv.refl _) u ++ crossingSetsFrom p (i :: m ++ i :: v)).Nodup at h
    have he : i :: m ++ i :: v = (i :: m ++ [i]) ++ v := by simp [List.append_assoc]
    rw [he, crossingSetsFrom_append] at h
    simpa only [List.foldl_cons, List.foldl_append, List.foldl_nil, qB, q, pA] using h
  have hcentral : crossingSetsFrom p (i :: m ++ [i]) =
      {x,y} :: (crossingSetsFrom pA m ++ [{z,x}]) := by
    change crossingSetsFrom p (i :: (m ++ [i])) = _
    rw [crossingSetsFrom_cons, crossingSetsFrom_append, crossingSetsFrom_cons]
    change {x,y} :: (crossingSetsFrom pA m ++ [{z, q (right i)}]) = _
    rw [hxq']
  have hnodup := List.nodup_append.mp hset
  have hnodupM : (crossingSetsFrom pA m).Nodup := by
    have hc := (List.nodup_append.mp hnodup.2.1).1
    rw [hcentral] at hc
    exact (List.nodup_append.mp (List.nodup_cons.mp hc).2).1
  have hzym : {z,y} ∈ crossingSetsFrom pA m := by
    by_contra h
    exact (not_lt_of_ge hyzq.le) ((order_replay_of_not_crossed m pA z y h).mpr hzyA)
  have hinc :
      ∀ ab ∈ crossingPairsFrom (Equiv.refl _) u ++
        crossingPairsFrom pA m ++ crossingPairsFrom qB v, ab.1 < ab.2 := by
    intro ab hab
    apply increasing_trace hw ab
    rw [crossing_append]
    change ab ∈ crossingPairsFrom (Equiv.refl _) u ++
      (endpoints p i :: crossingPairsFrom pA (m ++ i :: v))
    rw [crossing_append, crossingPairsFrom]
    change ab ∈ crossingPairsFrom (Equiv.refl _) u ++
      (endpoints p i :: (crossingPairsFrom pA m ++ endpoints q i :: crossingPairsFrom qB v))
    simp only [List.mem_append, List.mem_cons] at *
    tauto
  have hzym' : (z,y) ∈ crossingPairsFrom pA m := by
    rcases (pair_mem_iff pA m z y hzy.ne).mp hzym with h | h
    · exact h
    · exact (lt_asymm hzy (hinc (y,z) (by simp [h]))).elim
  have hmid (ab : Fin n × Fin n) (hab : ab ∈ crossingPairsFrom pA m)
      (hs : selected S ab) : ab = (z,y) := by
    obtain ⟨a,b⟩ := ab
    have hpos := pos_split_middle i m hm pA hab
    dsimp only at hpos
    have hord : a < b := hinc (a,b) (by simp [hab])
    have hxv : (pA.symm x).val = i.val + 1 := congrArg Fin.val hxa
    have hyv : (pA.symm y).val = i.val := congrArg Fin.val hya
    have ha := (hmem a).mp hs.1
    have hb := (hmem b).mp hs.2
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
    all_goals first
      | rfl
      | exact (lt_irrefl _ hord).elim
      | exact (lt_asymm hzy hord).elim
      | omega

  have hresM : restrictFrom S pA m = [1] := by
    apply restrict_single_of S pA m (z,y) 0 hnodupM hzym' ⟨hzS, hyS⟩ hmid
    intro s j t h he
    let P := s.foldl step pA
    obtain ⟨hl, hr⟩ := Prod.mk.inj he
    change P (left j) = z at hl
    change P (right j) = y at hr
    have hms : ∀ k ∈ s, k.val ≠ i.val ∧ k.val ≠ i.val + 1 := by
      intro k hk
      exact hm k (by rw [h]; simp [hk])
    have hPz : (P.symm z).val < i.val + 1 := (pos_fold_middle i s hms pA z).1.mpr hza
    have hPx : (P.symm x).val = i.val + 1 :=
      (pos_fold_middle i s hms pA x).2.1.mpr (congrArg Fin.val hxa)
    have hPr : i.val + 1 < (P.symm r).val :=
      (pos_fold_middle i s hms pA r).2.2.mpr (by omega)
    have hPzy : (P.symm z).val < (P.symm y).val := by
      rw [← hl, ← hr, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      exact Nat.lt_succ_self _
    have he : below S P z = ∅ := by
      ext b
      simp only [below, Finset.mem_filter, Finset.notMem_empty, iff_false, hmem, Fin.lt_def]
      rintro ⟨hb, hlt⟩
      rcases hb with rfl | rfl | rfl | rfl <;> omega
    change rank S P z = 0
    simp [rank, he]
  have hcore (a b : Fin n) (ha : a ∈ S) (hb : b ∈ S)
      (hab : a < b) (har : a ≠ r) (hbr : b ≠ r) :
      {a,b} ∈ crossingSetsFrom p (i :: m ++ [i]) := by
    rw [hcentral]
    rcases (hmem a).mp ha with rfl | rfl | rfl | hh
    · rcases (hmem b).mp hb with rfl | rfl | rfl | hh
      · exact (lt_irrefl _ hab).elim
      · simp
      · simp [hzym]
      · exact (hbr hh).elim
    · rcases (hmem b).mp hb with rfl | rfl | rfl | hh
      · exact (lt_asymm hzx hab).elim
      · exact (lt_irrefl _ hab).elim
      · simp
      · exact (hbr hh).elim
    · rcases (hmem b).mp hb with rfl | rfl | rfl | hh
      · exact (lt_asymm hzy hab).elim
      · exact (lt_asymm hxy hab).elim
      · exact (lt_irrefl _ hab).elim
      · exact (hbr hh).elim
    · exact (har hh).elim
  have hbpos : qB.symm z = right i ∧ qB.symm x = left i := by
    constructor
    · exact pos_step_left q i
    · rw [← hxq']
      exact pos_step_right q i
  have hqB_stays (a : Fin n) (ha : a ≠ z) (hb : a ≠ x) :
      qB.symm a = q.symm a := by
    have ha' : q.symm a ≠ left i := fun h => ha (by rw [← hzpos] at h; exact q.symm.injective h)
    have hb' : q.symm a ≠ right i := fun h => hb (by rw [← hxq] at h; exact q.symm.injective h)
    exact (pos_step q i a).trans (Equiv.swap_apply_of_ne_of_ne ha' hb')
  have hyB := hqB_stays y hzy.ne.symm hxy.ne.symm
  have hrB := hqB_stays r hrz hrx
  have hrightP : ∀ a ∈ S, a ≠ r → p.symm a < p.symm r := by
    intro a ha har
    rcases (hmem a).mp ha with rfl | rfl | rfl | ht
    · exact show (p.symm z).val < (p.symm r).val by omega
    · rw [hxp]
      exact show i.val < (p.symm r).val by omega
    · rw [hyp]
      exact show i.val + 1 < (p.symm r).val by omega
    · exact (har ht).elim
  have hrightB : ∀ a ∈ S, a ≠ r → qB.symm a < qB.symm r := by
    intro a ha har
    rw [hrB]
    rcases (hmem a).mp ha with rfl | rfl | rfl | ht
    · rw [hbpos.1]
      exact hrq
    · rw [hbpos.2]
      exact show i.val < (q.symm r).val by omega
    · rw [hyB]
      exact show (q.symm y).val < (q.symm r).val by omega
    · exact (har ht).elim
  have hprefix (ab : Fin n × Fin n) (hab : ab ∈ crossingPairsFrom (Equiv.refl _) u)
      (hs : selected S ab) : ab.1 = r := by
    obtain ⟨a,b⟩ := ab
    have hlt := hinc (a,b) (by simp [hab])
    have hp := pos_after_cross _ _ hnodup.1 hab
    change p.symm b < p.symm a at hp
    by_contra ha
    by_cases hb : b = r
    · exact (lt_asymm (hrightP a hs.1 ha) (hb ▸ hp))
    · have hc := hcore a b hs.1 hs.2 hlt ha hb
      exact hnodup.2.2 _ (List.mem_map.mpr ⟨_, hab, rfl⟩) _ (List.mem_append_left _ hc) rfl
  have hsuffix (ab : Fin n × Fin n) (hab : ab ∈ crossingPairsFrom qB v)
      (hs : selected S ab) : ab.2 = r := by
    obtain ⟨a,b⟩ := ab
    have hlt := hinc (a,b) (by simp [hab])
    have hp := pos_before_cross _ _ (List.nodup_append.mp hnodup.2.1).2.1 hab
    by_contra hb
    by_cases ha : a = r
    · exact (lt_asymm (hrightB b hs.2 hb) (ha ▸ hp))
    · have hc := hcore a b hs.1 hs.2 hlt ha hb
      exact (List.nodup_append.mp hnodup.2.1).2.2 _ hc _ (List.mem_map.mpr ⟨_, hab, rfl⟩) rfl
  have hresA : restrictFrom S p [i] = [2] := by
    rw [restrict_cons, ite_eq_left (show p (left i) ∈ S ∧ p (right i) ∈ S from ⟨hxS,hyS⟩)]
    have he : below S p x = {z} := by
      ext a
      simp only [below, Finset.mem_filter, Finset.mem_singleton, hmem, hxp, Fin.lt_def]
      constructor
      · rintro ⟨(rfl | rfl | rfl | rfl), hlt⟩
        · rfl
        · rw [hxp] at hlt
          omega
        · rw [hyp] at hlt
          exact (Nat.not_succ_le_self _ (Nat.le_of_lt hlt)).elim
        · exact (by change (p.symm r).val < i.val at hlt; omega : False).elim
      · rintro rfl
        exact ⟨Or.inl rfl, hzp⟩
    change [rank S p x + 1] = _
    simp [rank, he]
  have hresB : restrictFrom S q [i] = [2] := by
    rw [restrict_cons, ite_eq_left (show q (left i) ∈ S ∧ q (right i) ∈ S from ⟨hzS,hxq'.symm ▸ hxS⟩)]
    have he : below S q z = {y} := by
      ext a
      simp only [below, Finset.mem_filter, Finset.mem_singleton, hmem, hzpos, Fin.lt_def]
      constructor
      · rintro ⟨(rfl | rfl | rfl | rfl), hlt⟩
        · rw [hzpos] at hlt
          omega
        · rw [hxq] at hlt
          exact (Nat.not_succ_le_self _ (Nat.le_of_lt hlt)).elim
        · rfl
        · exact (by change (q.symm r).val < i.val at hlt; omega : False).elim
      · rintro rfl
        exact ⟨Or.inr (Or.inr (Or.inl rfl)), hzpos ▸ hyzq⟩
    change [rank S q z + 1] = _
    simp [rank, he]
  have hresP := restrict_moving_right S (Equiv.refl _) u r hrS hprefix
  have hresV := restrict_moving_left S qB v r hrS hsuffix
  have hpRank : rank S p r = 3 := by rw [rank_rightmost S p r hrS hrightP, hcard]
  have hbRank : rank S qB r = 3 := by rw [rank_rightmost S qB r hrS hrightB, hcard]
  have hvEnd : v.foldl step qB = Fin.revPerm := by
    simpa only [List.foldl_append, List.foldl_cons, p, pA, q, qB] using hw.2
  change rank S (Equiv.refl _) r ≤ rank S p r ∧ _ at hresP
  dsimp only at hresP hresV
  change _ ∧ restrictFrom S (Equiv.refl _) u =
    List.range' (rank S (Equiv.refl _) r + 1) (rank S p r - rank S (Equiv.refl _) r) at hresP
  rw [hpRank] at hresP
  rw [hvEnd, hbRank] at hresV
  have hrank := rank_reversal S r hrS
  rw [hcard] at hrank
  have hrank' : rank S Fin.revPerm r = 3 - rank S (Equiv.refl _) r := by omega
  have hrank'' : 3 - rank S Fin.revPerm r = rank S (Equiv.refl _) r := by omega
  rw [hrank'', hrank'] at hresV
  refine ⟨S, hcard, ?_⟩
  have he : u ++ (i :: m ++ i :: v) = u ++ ([i] ++ (m ++ ([i] ++ v))) := rfl
  rw [restrict, he, restrict_append, restrict_append]
  change restrictFrom S (Equiv.refl _) u ++
    (restrictFrom S p [i] ++ restrictFrom S pA (m ++ ([i] ++ v))) ∈ forbidden
  rw [restrict_append, restrict_append]
  change restrictFrom S (Equiv.refl _) u ++
    (restrictFrom S p [i] ++ (restrictFrom S pA m ++ (restrictFrom S q [i] ++
      restrictFrom S qB v))) ∈ forbidden
  rw [hresP.2, hresA, hresM, hresB, hresV.2]
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using
    right_quartet_words (rank S (Equiv.refl _) r) hresP.1

/-- The successive directions of a wire, with true for a move to the right. -/
def wireDirections {n : Nat} (p : State n) (a : Fin n) : Word n → List Bool
  | [] => []
  | i :: w =>
    let rest := wireDirections (step p i) a w
    if p (left i) = a then true :: rest
    else if p (right i) = a then false :: rest
    else rest

private def wirePartners {n : Nat} (p : State n) (a : Fin n) : Word n → List (Fin n)
  | [] => []
  | i :: w =>
    let rest := wirePartners (step p i) a w
    if p (left i) = a then p (right i) :: rest
    else if p (right i) = a then p (left i) :: rest
    else rest

private theorem wirePartners_spec {n : Nat} (p : State n) (a b : Fin n) (w : Word n)
    (h : b ∈ wirePartners p a w) : b ≠ a ∧ {a,b} ∈ crossingSetsFrom p w := by
  induction w generalizing p with
  | nil => simp [wirePartners] at h
  | cons i w ih =>
    rw [wirePartners] at h
    rw [crossingSetsFrom_cons]
    by_cases hl : p (left i) = a
    · rw [ite_eq_left hl] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨fun he => left_ne_right i (p.injective (hl.trans he.symm)),
          by rw [hl]; exact List.mem_cons_self⟩
      · exact (ih _ h).imp id (List.mem_cons_of_mem _)
    · rw [ite_eq_right hl] at h
      by_cases hr : p (right i) = a
      · rw [ite_eq_left hr] at h
        rcases List.mem_cons.mp h with rfl | h
        · exact ⟨hl, by rw [hr, Finset.pair_comm a (p (left i))]; exact List.mem_cons_self⟩
        · exact (ih _ h).imp id (List.mem_cons_of_mem _)
      · exact (ih _ (by rwa [ite_eq_right hr] at h)).imp id (List.mem_cons_of_mem _)

private theorem wirePartners_nodup {n : Nat} (p : State n) (a : Fin n) (w : Word n)
    (hn : (crossingSetsFrom p w).Nodup) : (wirePartners p a w).Nodup := by
  induction w generalizing p with
  | nil => exact List.nodup_nil
  | cons i w ih =>
    rw [crossingSetsFrom_cons, List.nodup_cons] at hn
    rw [wirePartners]
    by_cases hl : p (left i) = a
    · rw [ite_eq_left hl, List.nodup_cons]
      exact ⟨fun h => hn.1 (by rw [hl]; exact (wirePartners_spec _ _ _ _ h).2), ih _ hn.2⟩
    · rw [ite_eq_right hl]
      by_cases hr : p (right i) = a
      · rw [ite_eq_left hr, List.nodup_cons]
        exact ⟨fun h => hn.1 (by rw [hr, Finset.pair_comm]; exact (wirePartners_spec _ _ _ _ h).2),
          ih _ hn.2⟩
      · rw [ite_eq_right hr]
        exact ih _ hn.2

private theorem wireDirections_length {n : Nat} (p : State n) (a : Fin n) (w : Word n) :
    (wireDirections p a w).length = (wirePartners p a w).length := by
  induction w generalizing p with
  | nil => rfl
  | cons i w ih =>
    rw [wireDirections, wirePartners]
    by_cases hl : p (left i) = a <;> by_cases hr : p (right i) = a <;> simp [hl, hr, ih]

/-- Pair uniqueness bounds the number of moves of each wire. -/
theorem wire_directions_bound {n : Nat} (w : Word n)
    (a : Fin n) (hw : ReducedReversal w) :
    (wireDirections (Equiv.refl _) a w).length ≤ n - 1 := by
  rw [wireDirections_length, ← List.toFinset_card_of_nodup
    (wirePartners_nodup _ _ _ (pair_uniqueness w hw))]
  have hs : (wirePartners (Equiv.refl _) a w).toFinset ⊆ Finset.univ.erase a := by
    intro b hb
    exact Finset.mem_erase.mpr ⟨(wirePartners_spec _ _ _ _ (List.mem_toFinset.mp hb)).1,
      Finset.mem_univ b⟩
  have h := Finset.card_le_card hs
  simpa [Finset.card_erase_of_mem (Finset.mem_univ a), Fintype.card_fin] using h

theorem rank_other {n : Nat} (S : Finset (Fin n)) (p : State n)
    (i : Fin (n - 1)) (a : Fin n) (hl : p (left i) ≠ a) (hr : p (right i) ≠ a) :
    rank S (step p i) a = rank S p a := by
  unfold rank
  congr 1
  ext b
  simp only [below, Finset.mem_filter, pos_unchanged_order p i b a
    (by rintro ⟨_, he⟩; exact hr he.symm) (by rintro ⟨_, he⟩; exact hl he.symm)]

end D5.S1.Words.Permutations.Frieden
