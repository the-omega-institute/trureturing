/- GID: D5/S1/Words/AssociatedMersenne/CircularWords
   generality: G
   mirror-B: D5/B/S1/Words/AssociatedMersenne/CircularWords
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Labelled circular words, positive run marks, rotations and zero words. -/

/-
admission_basis: escape-witness
Module content theorem: nonzero_has_marked_start
Run marks: IsOneRunStart permits r = 0; IsMarkedStart requires positive r.
Singleton correction: [(r,1)] has provisionalDegree min r 2 + 1 and tupleDegree min r 2.
The transfer correction is X * (1 - Y) * Rser before marking and
X * derivative (X * (1 - Y) * Rser) after marking.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/14898
Direct frozen dependencies:
  none (the other D5 imports belong to this delivery).
Declarations:
  split_reverse_map: proof_shape: bind-only; escape_witness: none; consumers: RunTupleBijection.splitBy_map_injective
  cycAdd_sub_one: proof_shape: bind-only; escape_witness: none; consumer: CircularWords.cycAdd_predecessor_pos
  start_large_false: proof_shape: bind-only; escape_witness: none; consumer: CircularWords.admissible_iff_BP
  finAll_true_iff: proof_shape: bind-only; escape_witness: none; consumer: CircularWords.runStartB_iff
  finAny_true_iff: proof_shape: bind-only; escape_witness: none; consumer: CircularWords.admissibleB_iff
  runStartB_iff: proof_shape: bind-only; escape_witness: none; consumer: CircularWords.admissibleB_iff
  admissibleB_iff: proof_shape: bind-only; escape_witness: none; consumer: CircularWords.admissibleB_iff_literal
  startBP_to_start: proof_shape: bind-only; escape_witness: none; consumer: CircularWords.admissible_iff_BP
  start_to_startBP: proof_shape: bind-only; escape_witness: none; consumer: CircularWords.admissible_iff_BP
  admissible_iff_BP: proof_shape: bind-only; escape_witness: none; consumer: CircularWords.admissibleB_iff_literal
  admissibleB_iff_literal: proof_shape: bind-only; escape_witness: none; consumer: CircularWords.singleton_admissible_iff
  cycAdd_zero: proof_shape: bind-only; escape_witness: none; consumer: SingleRunDegrees.insert_interior_admissible_iff
  cycAdd_val: proof_shape: bind-only; escape_witness: none; consumer: CircularWords.cycAdd_offset
  cycAdd_assoc: proof_shape: bind-only; escape_witness: none; consumer: CircularWords.cycAdd_index_add
  cycAdd_inj: proof_shape: bind-only; escape_witness: none; consumer: CircularWords.cycAdd_bijective
  zero_admissible: proof_shape: bind-only; escape_witness: none; consumer: SingleRunDegrees.delete_first_admissible
  flip_zero_true: proof_shape: bind-only; escape_witness: none; consumer: CircularWords.singleton_admissible
  flip_zero_false: proof_shape: bind-only; escape_witness: none; consumer: CircularWords.singleton_admissible
  singleton_admissible: proof_shape: content; escape_witness: CircularWords.singleton_admissible;
  singleton_admissible_iff: proof_shape: content; escape_witness: CircularWords.singleton_admissible_iff;
  zero_degree: proof_shape: content; escape_witness: CircularWords.zero_degree;
  cycAdd_mod: proof_shape: bind-only; escape_witness: none; consumer: CircularWords.cycAdd_index_add
  cycAdd_offset: proof_shape: bind-only; escape_witness: none; consumer: CircularWords.cycAdd_surjective
  offset_lt: proof_shape: bind-only; escape_witness: none; consumer: CircularWords.cycAdd_surjective
  cycAdd_surjective: proof_shape: bind-only; escape_witness: none; consumer: CircularWords.cycAdd_bijective
  cycAdd_bijective: proof_shape: bind-only; escape_witness: none; consumer: MultiRunDegrees.degree_pair_sum
  linearize_injective: proof_shape: bind-only; escape_witness: none; consumer: MultiRunDegrees.raw_singleton_delete_legal
  linearize_length: proof_shape: bind-only; escape_witness: none; consumer: MultiRunDegrees.degree_pair_sum
  one_run_length_unique: proof_shape: bind-only; escape_witness: none; consumer: SingleRunDegrees.inserted_start_pos_iff
  marked_start_true: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.first_raw_gap_strict
  marked_start_predecessor: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.first_raw_run_start
  marked_start_iff: proof_shape: content; escape_witness: CircularWords.marked_start_iff;
  cycAdd_predecessor_pos: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.marked_raw_boundary
  nonzero_has_marked_start: proof_shape: content; escape_witness: CircularWords.nonzero_has_marked_start;
  admissible_nonzero_has_marked_start: proof_shape: content; escape_witness: CircularWords.admissible_nonzero_has_marked_start;
  card_marks: proof_shape: bind-only; escape_witness: none; consumer: CircularWords.card_marked_words
  card_marked_words: proof_shape: bind-only; escape_witness: none; consumer: CircularWords.marked_double_count_of_equiv
  marked_double_count_of_equiv: proof_shape: bind-only; escape_witness: none; consumer: MarkedDegreeEnumeration.marked_degree_double_count
  cycAdd_index_add: proof_shape: bind-only; escape_witness: none; consumer: CircularWords.rotateWord_admissible_iff
  rotateWord_add: proof_shape: bind-only; escape_witness: none; consumer: CircularWords.rotateWord_admissible_iff
  rotateWord_sub_one: proof_shape: bind-only; escape_witness: none; consumer: CircularWords.rotateWord_start
  rotateWord_start: proof_shape: bind-only; escape_witness: none; consumer: CircularWords.rotateWord_admissible_iff
  rotateWord_admissible_iff: proof_shape: bind-only; escape_witness: none; consumer: SingleRunDegrees.delete_first_admissible
  rotateWord_flip: proof_shape: bind-only; escape_witness: none; consumer: CircularWords.rotateWord_degree
  rotateWord_degree: proof_shape: bind-only; escape_witness: none; consumer: SingleRunDegrees.degree_raw_singleton
  next_one_gap_bound: proof_shape: bind-only; escape_witness: none; consumer: RunTupleBijection.first_raw_gap_strict
  linearize_move_mark: proof_shape: bind-only; escape_witness: none; consumer: MultiRunDegrees.linearize_at_pair
-/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.List.SplitBy

namespace D5.S1.Words.AssociatedMersenne.CircularWords

open scoped BigOperators

open Classical
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

noncomputable section

-- Reverse the blocks, reverse each block, and transport its entries. Internal links
-- and separating boundaries are both preserved, so splitBy uniqueness identifies them.
theorem split_reverse_map {α β : Type*} (r : α → α → Bool)
    (s : β → β → Bool) (f : α → β) (l : List α)
    (h : ∀ a ∈ l, ∀ b ∈ l, s (f b) (f a) = r a b) :
    (l.reverse.map f).splitBy s =
      ((l.splitBy r).reverse.map (fun b => b.reverse.map f)) := by
  apply List.splitBy_eq_iff.mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · conv_lhs => rw [← List.flatten_splitBy r l]
    simp only [List.reverse_flatten, List.map_flatten, List.map_reverse,
      List.map_map, Function.comp_def]
  · simp only [List.mem_map, List.mem_reverse, not_exists, not_and]
    intro b hb he
    have : b = [] := by simpa using he
    exact List.nil_notMem_splitBy r l (this ▸ hb)
  · intro b hb
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
    have hc' := List.mem_reverse.mp hc
    rw [List.isChain_map, List.isChain_reverse]
    apply (List.isChain_of_mem_splitBy hc').imp_of_mem_imp
    intro a b ha hb hab
    rw [h a ?_ b ?_]
    · exact hab
    · rw [← List.flatten_splitBy r l]
      exact List.mem_flatten.mpr ⟨c, hc', ha⟩
    · rw [← List.flatten_splitBy r l]
      exact List.mem_flatten.mpr ⟨c, hc', hb⟩
  · rw [List.isChain_map, List.isChain_reverse]
    apply (List.isChain_getLast_head_splitBy r l).imp_of_mem_imp
    intro a b ha hb hab
    obtain ⟨ha', hb', hab⟩ := hab
    refine ⟨by simpa, by simpa, ?_⟩
    simp only [List.getLast_map, List.getLast_reverse, List.head_map, List.head_reverse]
    rw [h (a.getLast ha') ?_ (b.head hb') ?_]
    · exact hab
    · rw [← List.flatten_splitBy r l]
      exact List.mem_flatten.mpr ⟨a, ha, List.getLast_mem _⟩
    · rw [← List.flatten_splitBy r l]
      exact List.mem_flatten.mpr ⟨b, hb, List.head_mem _⟩


def cycAdd {n : Nat} (i : Fin n) (j : Nat) : Fin n :=
  letI : NeZero n := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt)⟩
  Fin.ofNat n (i.val + j)

def cycSub {n : Nat} (i : Fin n) (j : Nat) : Fin n :=
  letI : NeZero n := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt i.isLt)⟩
  Fin.ofNat n (i.val + n - j)

def IsOneRunStart {n : Nat} (w : Fin n → Bool) (i : Fin n) (r : Nat) : Prop :=
  w (cycSub i 1) = false ∧
    (∀ j < r, w (cycAdd i j) = true) ∧
    w (cycAdd i r) = false

def Admissible {n : Nat} (w : Fin n → Bool) : Prop :=
  (n = 0 ∨ ∃ i, w i = false) ∧
    ∀ i r, IsOneRunStart w i r → ∀ j ≤ r, w (cycAdd (cycAdd i r) j) = false

def flip {n : Nat} (w : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update w i (!w i)

noncomputable def degree {n : Nat} (w : Fin n → Bool) : Nat := by
  classical exact (Finset.univ.filter (fun i => Admissible (flip w i))).card

noncomputable def N (n k : Nat) : Nat := by
  classical exact (Finset.univ.filter (fun w : Fin n → Bool => Admissible w ∧ degree w = k)).card

private def finAll {n : Nat} (p : Fin n → Bool) : Bool :=
  (List.finRange n).all p

private def finAny {n : Nat} (p : Fin n → Bool) : Bool :=
  (List.finRange n).any p

private def runStartB {n : Nat} (w : Fin n → Bool) (i : Fin n) (r : Fin (n + 1)) : Bool :=
  (decide (r.val < n)) &&
  decide (w (cycSub i 1) = false) &&
  finAll (fun j : Fin (n + 1) =>
    decide (r.val ≤ j.val) || decide (w (cycAdd i j.val) = true)) &&
  decide (w (cycAdd i r.val) = false)

private def admissibleB {n : Nat} (w : Fin n → Bool) : Bool :=
  ((decide (n = 0)) || finAny (fun i : Fin n => decide (w i = false))) &&
  finAll (fun i : Fin n =>
    finAll (fun r : Fin (n + 1) =>
      (!runStartB w i r) ||
      finAll (fun j : Fin (n + 1) =>
        decide (r.val < j.val) || decide (w (cycAdd (cycAdd i r.val) j.val) = false))))

lemma cycAdd_sub_one (n : Nat) (i : Fin n) : cycAdd i (n - 1) = cycSub i 1 := by
  apply Fin.ext
  simp [cycAdd, cycSub]
  have hn : 1 ≤ n := Nat.succ_le_iff.mp (Nat.zero_lt_of_lt i.isLt)
  rw [Nat.add_sub_assoc hn]

lemma start_large_false {n : Nat} (w : Fin n → Bool) (i : Fin n) (r : Nat)
    (hr : n ≤ r) : ¬ IsOneRunStart w i r := by
  intro h
  have hlt : n - 1 < r := by
    have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
    omega
  have ht := h.2.1 (n - 1) hlt
  have hp := h.1
  rw [cycAdd_sub_one] at ht
  exact Bool.noConfusion (hp.symm.trans ht)

private lemma finAll_true_iff {n : Nat} (p : Fin n → Bool) :
    finAll p = true ↔ ∀ x, p x = true := by
  simp [finAll, List.all_eq_true]

private lemma finAny_true_iff {n : Nat} (p : Fin n → Bool) :
    finAny p = true ↔ ∃ x, p x = true := by
  simp [finAny, List.any_eq_true]

private def IsOneRunStartBP {n : Nat} (w : Fin n → Bool) (i : Fin n) (r : Fin (n + 1)) : Prop :=
  r.val < n ∧
  w (cycSub i 1) = false ∧
  (∀ j : Fin (n + 1), j.val < r.val → w (cycAdd i j.val) = true) ∧
  w (cycAdd i r.val) = false

private lemma runStartB_iff {n : Nat} (w : Fin n → Bool) (i : Fin n) (r : Fin (n+1)) :
    runStartB w i r = true ↔ IsOneRunStartBP w i r := by
  simp only [runStartB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    finAll_true_iff, IsOneRunStartBP]
  constructor
  · rintro ⟨⟨⟨hr, hp⟩, hall⟩, he⟩
    refine ⟨hr, hp, ?_, he⟩
    intro j hj
    exact Or.resolve_left (hall j) (by omega)
  · rintro ⟨hr, hp, hall, he⟩
    refine ⟨⟨⟨hr, hp⟩, ?_⟩, he⟩
    intro j
    by_cases h : r ≤ j
    · exact Or.inl h
    · exact Or.inr (hall j (by omega))

private def AdmissibleBP {n : Nat} (w : Fin n → Bool) : Prop :=
  (n = 0 ∨ ∃ i, w i = false) ∧
    ∀ i : Fin n, ∀ r : Fin (n + 1), IsOneRunStartBP w i r →
      ∀ j : Fin (n + 1), j.val ≤ r.val →
        w (cycAdd (cycAdd i r.val) j.val) = false

private lemma admissibleB_iff {n : Nat} (w : Fin n → Bool) :
    admissibleB w = true ↔ AdmissibleBP w := by
  simp only [admissibleB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    finAny_true_iff, finAll_true_iff, AdmissibleBP]
  constructor
  · rintro ⟨h0, hall⟩
    refine ⟨h0, ?_⟩
    intro i r hrs j hj
    have h := hall i r
    have hrun : runStartB w i r = true := (runStartB_iff w i r).mpr hrs
    have hnot : ¬ ((!runStartB w i r) = true) := by simp [hrun]
    rcases h with hbad | hgood
    · exact False.elim (hnot hbad)
    · exact (hgood j).resolve_left (by omega)
  · rintro ⟨h0, hall⟩
    refine ⟨h0, ?_⟩
    intro i r
    by_cases hrs : IsOneRunStartBP w i r
    · have hrun : runStartB w i r = true := (runStartB_iff w i r).mpr hrs
      right
      intro j
      by_cases hj : r.val < j.val
      · exact Or.inl hj
      · exact Or.inr (hall i r hrs j (by omega))
    · left
      have hne : runStartB w i r ≠ true := by
        intro hb
        exact hrs ((runStartB_iff w i r).mp hb)
      have hf : runStartB w i r = false := Bool.eq_false_of_not_eq_true hne
      simp [hf]

private lemma startBP_to_start {n : Nat} {w : Fin n → Bool} {i : Fin n} {r : Fin (n+1)}
    (h : IsOneRunStartBP w i r) : IsOneRunStart w i r.val := by
  refine ⟨h.2.1, ?_, h.2.2.2⟩
  intro j hj
  have hj' : j < n + 1 := by omega
  let jj : Fin (n+1) := ⟨j, hj'⟩
  exact h.2.2.1 jj (by simpa [jj] using hj)

private lemma start_to_startBP {n : Nat} {w : Fin n → Bool} {i : Fin n} {r : Nat}
    (h : IsOneRunStart w i r) :
    IsOneRunStartBP w i ⟨r, Nat.lt_succ_of_lt (by
      by_contra hn
      exact start_large_false w i r (Nat.le_of_not_gt hn) h)⟩ := by
  have hr : r < n := by
    by_contra hn
    exact start_large_false w i r (Nat.le_of_not_gt hn) h
  refine ⟨hr, h.1, ?_, h.2.2⟩
  intro j hj
  exact h.2.1 j hj

private lemma admissible_iff_BP {n : Nat} (w : Fin n → Bool) :
    Admissible w ↔ AdmissibleBP w := by
  constructor
  · rintro ⟨h0, hall⟩
    refine ⟨h0, ?_⟩
    intro i r hrs j hj
    have hr := startBP_to_start hrs
    have h := hall i r.val hr
    exact h j.val hj
  · rintro ⟨h0, hall⟩
    refine ⟨h0, ?_⟩
    intro i r hrs j hj
    have hr : r < n := by
      by_contra hn
      exact start_large_false w i r (Nat.le_of_not_gt hn) hrs
    let rr : Fin (n+1) := ⟨r, Nat.lt_succ_of_lt hr⟩
    have hs : IsOneRunStartBP w i rr := start_to_startBP hrs
    let jj : Fin (n+1) := ⟨j, by omega⟩
    exact hall i rr hs jj (by simpa [jj, rr] using hj)

private lemma admissibleB_iff_literal {n : Nat} (w : Fin n → Bool) :
    admissibleB w = true ↔ Admissible w :=
  (admissibleB_iff w).trans (admissible_iff_BP w).symm

lemma cycAdd_zero {n : Nat} (i : Fin n) : cycAdd i 0 = i := by
  apply Fin.ext
  simp [cycAdd]

lemma cycAdd_val {n : Nat} (i : Fin n) (j : Nat) :
    (cycAdd i j).val = (i.val + j) % n := by rfl

lemma cycAdd_assoc {n : Nat} (i : Fin n) (j k : Nat) :
    cycAdd (cycAdd i j) k = cycAdd i (j + k) := by
  apply Fin.ext
  change ((i.val + j) % n + k) % n = (i.val + (j + k)) % n
  rw [Nat.mod_add_mod]
  rw [Nat.add_assoc]

lemma cycAdd_inj {n : Nat} (i : Fin n) {j k : Nat} (hj : j < n) (hk : k < n) :
    cycAdd i j = cycAdd i k ↔ j = k := by
  constructor
  · intro h
    have hval := congrArg Fin.val h
    change (i.val + j) % n = (i.val + k) % n at hval
    have hi := i.isLt
    have hsumj : i.val + j < 2 * n := by omega
    have hsumk : i.val + k < 2 * n := by omega
    have hmod : Nat.ModEq n (i.val + j) (i.val + k) := hval
    exact (Nat.ModEq.add_left_cancel' i.val hmod).eq_of_lt_of_lt hj hk
  · rintro rfl; rfl

lemma zero_admissible (n : Nat) : Admissible (fun _ : Fin n => false) := by
  constructor
  · by_cases hn : n = 0
    · exact Or.inl hn
    · exact Or.inr ⟨⟨0, Nat.pos_of_ne_zero hn⟩, rfl⟩
  · intro i r hr j hj
    rfl

private lemma flip_zero_true {n : Nat} (i q : Fin n) :
    flip (fun _ : Fin n => false) i q = true ↔ q = i := by
  simp [flip, Function.update_apply]

private lemma flip_zero_false {n : Nat} (i q : Fin n) :
    flip (fun _ : Fin n => false) i q = false ↔ q ≠ i := by
  simp [flip, Function.update_apply]

private lemma singleton_admissible {n : Nat} (i : Fin n) (hn : 3 ≤ n) :
    Admissible (flip (fun _ : Fin n => false) i) := by
  have hneq (a : Nat) (ha : a < n) (hpos : a ≠ 0) : cycAdd i a ≠ i := by
    intro he
    have he' : cycAdd i a = cycAdd i 0 := he.trans (cycAdd_zero i).symm
    exact hpos ((cycAdd_inj i ha (by omega)).mp he')
  constructor
  · right
    exact ⟨cycAdd i 1, (flip_zero_false i _).mpr (hneq 1 (by omega) (by omega))⟩
  · intro a r hrs j hj
    by_cases hr : r = 0
    · subst r
      have hj0 : j = 0 := by omega
      subst j
      simpa [cycAdd_zero] using hrs.2.2
    · have ha : a = i := by
        apply (flip_zero_true i a).mp
        simpa [cycAdd_zero] using hrs.2.1 0 (by omega)
      subst a
      have hr1 : r = 1 := by
        by_contra h
        have ht := hrs.2.1 1 (by omega)
        have hi := (flip_zero_true i _).mp ht
        exact hneq 1 (by omega) (by omega) hi
      subst r
      rw [cycAdd_assoc]
      exact (flip_zero_false i _).mpr (hneq (1 + j) (by omega) (by omega))

private lemma singleton_admissible_iff {n : Nat} (i : Fin n) :
    Admissible (flip (fun _ : Fin n => false) i) ↔ 3 ≤ n := by
  constructor
  · intro h
    by_contra hn
    have hn2 : n ≤ 2 := by omega
    rw [← admissibleB_iff_literal] at h
    interval_cases n <;> fin_cases i <;> norm_num [admissibleB, runStartB, finAny, finAll, flip, cycAdd, cycSub, List.finRange, Function.update_apply, Fin.last] at h <;> simp_all
  · exact singleton_admissible i

lemma zero_degree (n : Nat) :
    degree (fun _ : Fin n => false) = if n ≤ 2 then 0 else n := by
  classical
  unfold degree
  simp_rw [singleton_admissible_iff]
  by_cases h : n ≤ 2
  · simp [h, show ¬ 3 ≤ n by omega]
  · simp [h, show 3 ≤ n by omega]

private lemma cycAdd_mod {n : Nat} (i : Fin n) (j : Nat) :
    cycAdd i (j % n) = cycAdd i j := by
  apply Fin.ext
  change (i.val + j % n) % n = (i.val + j) % n
  exact Nat.add_mod_mod i.val j n

def offset {n : Nat} (i q : Fin n) : Nat := (q.val + n - i.val) % n

lemma cycAdd_offset {n : Nat} (i q : Fin n) : cycAdd i (offset i q) = q := by
  unfold offset
  rw [cycAdd_mod]
  apply Fin.ext
  rw [cycAdd_val]
  have h : i.val + (q.val + n - i.val) = q.val + n := by
    have hi := i.isLt
    omega
  rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt q.isLt]

lemma offset_lt {n : Nat} (i q : Fin n) : offset i q < n :=
  Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)

private lemma cycAdd_surjective {n : Nat} (i : Fin n) :
    Function.Surjective (fun j : Fin n => cycAdd i j.val) := by
  intro q
  exact ⟨⟨offset i q, offset_lt i q⟩, cycAdd_offset i q⟩

lemma cycAdd_bijective {n : Nat} (i : Fin n) :
    Function.Bijective (fun j : Fin n => cycAdd i j.val) := by
  refine ⟨?_, cycAdd_surjective i⟩
  intro j k h
  exact Fin.ext ((cycAdd_inj i j.isLt k.isLt).mp h)

def linearize {n : Nat} (w : Fin n → Bool) (i : Fin n) : List Bool :=
  List.ofFn (fun j : Fin n => w (cycAdd i j.val))

lemma linearize_injective {n : Nat} (i : Fin n) :
    Function.Injective (fun w : Fin n → Bool => linearize w i) := by
  intro w v h
  have hf := List.ofFn_injective h
  funext q
  obtain ⟨j, hj⟩ := cycAdd_surjective i q
  simpa only [hj] using congrFun hf j

lemma linearize_length {n : Nat} (w : Fin n → Bool) (i : Fin n) :
    (linearize w i).length = n := by simp [linearize]

lemma one_run_length_unique {n : Nat} {w : Fin n → Bool} {i : Fin n} {r s : Nat}
    (hr : IsOneRunStart w i r) (hs : IsOneRunStart w i s) : r = s := by
  rcases lt_trichotomy r s with h | h | h
  · have ht := hs.2.1 r h
    exact False.elim (Bool.noConfusion (hr.2.2.symm.trans ht))
  · exact h
  · have ht := hr.2.1 s h
    exact False.elim (Bool.noConfusion (hs.2.2.symm.trans ht))

def IsMarkedStart {n : Nat} (w : Fin n → Bool) (i : Fin n) : Prop :=
  ∃ r, 0 < r ∧ IsOneRunStart w i r

lemma marked_start_true {n : Nat} {w : Fin n → Bool} {i : Fin n}
    (h : IsMarkedStart w i) : w i = true := by
  obtain ⟨r, hr, hs⟩ := h
  simpa [cycAdd_zero] using hs.2.1 0 hr

lemma marked_start_predecessor {n : Nat} {w : Fin n → Bool} {i : Fin n}
    (h : IsMarkedStart w i) : w (cycSub i 1) = false := by
  obtain ⟨r, _, hs⟩ := h
  exact hs.1

lemma marked_start_iff {n : Nat} (w : Fin n → Bool) (i : Fin n) :
    IsMarkedStart w i ↔ w (cycSub i 1) = false ∧ w i = true := by
  constructor
  · intro h
    exact ⟨marked_start_predecessor h, marked_start_true h⟩
  · rintro ⟨hp, hi⟩
    have hex : ∃ r : Nat, w (cycAdd i r) = false :=
      ⟨n - 1, by simpa only [cycAdd_sub_one] using hp⟩
    let r := Nat.find hex
    have hr : w (cycAdd i r) = false := Nat.find_spec hex
    have hpos : 0 < r := by
      by_contra hn
      have hzero : r = 0 := by omega
      rw [hzero, cycAdd_zero, hi] at hr
      contradiction
    refine ⟨r, hpos, hp, ?_, hr⟩
    intro j hj
    exact Bool.eq_true_of_not_eq_false (Nat.find_min hex hj)

lemma cycAdd_predecessor_pos {n : Nat} (i : Fin n) (j : Nat) (hj : 0 < j) :
    cycSub (cycAdd i j) 1 = cycAdd i (j - 1) := by
  rw [← cycAdd_sub_one, cycAdd_assoc]
  apply Fin.ext
  simp only [cycAdd_val]
  have h : j + (n - 1) = (j - 1) + n := by
    have hn := Nat.zero_lt_of_lt i.isLt
    omega
  rw [h, ← Nat.add_assoc, Nat.add_mod_right]

lemma nonzero_has_marked_start {n : Nat} (w : Fin n → Bool)
    (hzero : ∃ p, w p = false) (hone : ∃ q, w q = true) :
    ∃ i, IsMarkedStart w i := by
  obtain ⟨p, hp⟩ := hzero
  obtain ⟨q, hq⟩ := hone
  have hex : ∃ j : Nat, w (cycAdd p j) = true :=
    ⟨offset p q, by simpa [cycAdd_offset] using hq⟩
  let j := Nat.find hex
  have hj : w (cycAdd p j) = true := Nat.find_spec hex
  have hpos : 0 < j := by
    by_contra hn
    have hz : j = 0 := by omega
    rw [hz, cycAdd_zero, hp] at hj
    contradiction
  refine ⟨cycAdd p j, (marked_start_iff _ _).mpr ⟨?_, hj⟩⟩
  rw [cycAdd_predecessor_pos p j hpos]
  exact Bool.eq_false_of_not_eq_true (Nat.find_min hex (by omega))

lemma admissible_nonzero_has_marked_start {n : Nat} (w : Fin n → Bool)
    (ha : Admissible w) (hone : ∃ q, w q = true) : ∃ i, IsMarkedStart w i := by
  have hzero : ∃ p, w p = false := by
    rcases ha.1 with hn | hz
    · subst n
      obtain ⟨q, _⟩ := hone
      exact Fin.elim0 q
    · exact hz
  exact nonzero_has_marked_start w hzero hone

def runCount {n : Nat} (w : Fin n → Bool) : Nat :=
  (Finset.univ.filter (IsMarkedStart w)).card

def DegreeRunWords (n ell k : Nat) :=
  { w : Fin n → Bool // Admissible w ∧ degree w = k ∧ runCount w = ell }

def MarkedDegreeRunWords (n ell k : Nat) :=
  (w : DegreeRunWords n ell k) × {i : Fin n // IsMarkedStart w.val i}

instance instFintypeDegreeRunWords (n ell k : Nat) : Fintype (DegreeRunWords n ell k) := inferInstanceAs
  (Fintype {w : Fin n → Bool // Admissible w ∧ degree w = k ∧ runCount w = ell})

instance instFintypeMarkedDegreeRunWords (n ell k : Nat) : Fintype (MarkedDegreeRunWords n ell k) := inferInstanceAs
  (Fintype ((w : DegreeRunWords n ell k) × {i : Fin n // IsMarkedStart w.val i}))

private lemma card_marks {n : Nat} (w : Fin n → Bool) :
    Fintype.card {i : Fin n // IsMarkedStart w i} = runCount w := by
  simp [runCount, Fintype.card_subtype]

private theorem card_marked_words (n ell k : Nat) :
    Fintype.card (MarkedDegreeRunWords n ell k) =
      ell * Fintype.card (DegreeRunWords n ell k) := by
  change Fintype.card ((w : DegreeRunWords n ell k) ×
    {i : Fin n // IsMarkedStart w.val i}) = _
  rw [Fintype.card_sigma]
  have h : ∀ w : DegreeRunWords n ell k,
      Fintype.card {i : Fin n // IsMarkedStart w.val i} = ell := by
    intro w
    rw [card_marks, w.property.2.2]
  simp_rw [h]
  simp [Nat.mul_comm]

theorem marked_double_count_of_equiv (n ell k : Nat) (T : Type*) [Fintype T]
    (e : MarkedDegreeRunWords n ell k ≃ Fin n × T) :
    ell * Fintype.card (DegreeRunWords n ell k) = n * Fintype.card T := by
  rw [← card_marked_words, Fintype.card_congr e, Fintype.card_prod, Fintype.card_fin]

def rotateWord {n : Nat} (w : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  fun j => w (cycAdd i j.val)

private lemma cycAdd_index_add {n : Nat} (i a : Fin n) (j : Nat) :
    cycAdd i (cycAdd a j).val = cycAdd (cycAdd i a.val) j := by
  change cycAdd i ((a.val + j) % n) = _
  rw [cycAdd_mod, cycAdd_assoc]

private lemma rotateWord_add {n : Nat} (w : Fin n → Bool) (i a : Fin n) (j : Nat) :
    rotateWord w i (cycAdd a j) = w (cycAdd (cycAdd i a.val) j) := by
  unfold rotateWord
  rw [cycAdd_val, cycAdd_mod, cycAdd_assoc]

private lemma rotateWord_sub_one {n : Nat} (w : Fin n → Bool) (i a : Fin n) :
    rotateWord w i (cycSub a 1) = w (cycSub (cycAdd i a.val) 1) := by
  rw [← cycAdd_sub_one n a, rotateWord_add, cycAdd_sub_one]

private lemma rotateWord_start {n : Nat} (w : Fin n → Bool) (i a : Fin n) (r : Nat) :
    IsOneRunStart (rotateWord w i) a r ↔ IsOneRunStart w (cycAdd i a.val) r := by
  unfold IsOneRunStart
  simp only [rotateWord_add, rotateWord_sub_one]

theorem rotateWord_admissible_iff {n : Nat} (w : Fin n → Bool) (i : Fin n) :
    Admissible (rotateWord w i) ↔ Admissible w := by
  have hzero : (∃ a, rotateWord w i a = false) ↔ (∃ a, w a = false) := by
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨cycAdd i a.val, ha⟩
    · rintro ⟨a, ha⟩
      obtain ⟨b, hb⟩ := cycAdd_surjective i a
      change cycAdd i b.val = a at hb
      exact ⟨b, by simpa [rotateWord, hb] using ha⟩
  constructor
  · intro ha
    refine ⟨by simpa only [hzero] using ha.1, ?_⟩
    intro a r hs j hj
    obtain ⟨b, hb⟩ := cycAdd_surjective i a
    change cycAdd i b.val = a at hb
    have hs' : IsOneRunStart (rotateWord w i) b r := (rotateWord_start w i b r).mpr
      (by simpa only [hb] using hs)
    have hz := ha.2 b r hs' j hj
    rw [rotateWord_add, cycAdd_index_add, hb] at hz
    exact hz
  · intro ha
    refine ⟨by simpa only [hzero] using ha.1, ?_⟩
    intro a r hs j hj
    have hs' := (rotateWord_start w i a r).mp hs
    have hz := ha.2 (cycAdd i a.val) r hs' j hj
    rw [rotateWord_add, cycAdd_index_add]
    exact hz

private lemma rotateWord_flip {n : Nat} (w : Fin n → Bool) (i a : Fin n) :
    rotateWord (flip w (cycAdd i a.val)) i = flip (rotateWord w i) a := by
  funext q
  unfold rotateWord flip
  have h : cycAdd i q.val = cycAdd i a.val ↔ q = a := (cycAdd_bijective i).1.eq_iff
  simp [Function.update_apply, h]

lemma rotateWord_degree {n : Nat} (w : Fin n → Bool) (i : Fin n) :
    degree (rotateWord w i) = degree w := by
  classical
  unfold degree
  apply Finset.card_bij (fun a _ => cycAdd i a.val)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [← rotateWord_admissible_iff (flip w (cycAdd i a.val)) i, rotateWord_flip]
    exact ha
  · intro a ha b hb hab
    exact (cycAdd_bijective i).1 hab
  · intro b hb
    obtain ⟨a, ha⟩ := cycAdd_surjective i b
    refine ⟨a, ?_, ha⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    rw [← ha, ← rotateWord_admissible_iff (flip w (cycAdd i a.val)) i,
      rotateWord_flip] at hb
    exact hb

theorem next_one_gap_bound {n : Nat} {w : Fin n → Bool} {a : Fin n} {r z : Nat}
    (ha : Admissible w) (hs : IsOneRunStart w a r)
    (hnext : w (cycAdd a (r+z)) = true) : r < z := by
  by_contra hz
  have h := ha.2 a r hs z (by omega)
  rw [cycAdd_assoc] at h
  exact Bool.noConfusion (h.symm.trans hnext)

theorem linearize_move_mark {n : Nat} (w : Fin n → Bool) (i : Fin n) (p : Nat) :
    linearize w (cycAdd i p) = (linearize w i).rotate p := by
  apply List.ext_getElem
  · simp [linearize]
  · intro j hj hj'
    have hjn : j < n := by simpa [linearize] using hj
    rw [List.getElem_rotate]
    simp only [linearize, List.getElem_ofFn, List.length_ofFn]
    rw [cycAdd_mod, cycAdd_assoc, Nat.add_comm p j]

end
end CircularWords
