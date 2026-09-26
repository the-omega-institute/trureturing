/- GID: D5/S3/StatisticalMechanics/Sandpiles/TorusColumnToppling
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Sandpiles/TorusColumnToppling
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: OEIS A293452: the n x 1 torus sandpile needs A023855(n-1) topplings in every order. -/

/-
proof_shape: result: content
escape_witness: form (2), the conclusion `result` itself, produced on its live path by the least
  action inequality `least_action` (every legal sequence topples each cell at most as often as the
  explicit target odometer u*) and the discrete maximum principle `odometer_eq` (a legal sequence
  ending in a final state has exactly the odometer u*); the first by induction along the sequence,
  the second by comparing the leftmost and rightmost maximum of the defect u* - v
admission_basis: open-problem-resolution (issue #10122)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.StatisticalMechanics.Sandpiles.TorusColumnToppling

open Finset

/-!
OEIS A249872 (Lars Blomberg, 2014) and A293452 (Joerg Arndt, 2017): on the `n × k` torus fill each
cell except `c[0,0]` with 4 grains; while some cell holds at least 4 grains, choose one, decrement
it by 4 and increment its 4 neighbours by 1, except `c[0,0]`, which never increases. `T(n, k)` is
the number of iterations. A293452 conjectures `T(n,1) = A023855(n)`; the printed index is off by one
(`T(1,1) = 0`, `A023855(1) = 1`), and the statement proved here is `T(n,1) = A023855(n - 1)`,
`n ≥ 2`, for every choice of the cells.
-/

/-- Cells `c[i,j]` of the `n × k` torus. -/
abbrev Cell (n k : ℕ) := ZMod n × ZMod k

/-- The initial configuration: 4 grains on every cell except `c[0,0]`. -/
def initial (n k : ℕ) (q : Cell n k) : ℤ := if q = 0 then 0 else 4

/-- The four torus neighbours of a cell. -/
def neighbours {n k : ℕ} (p : Cell n k) : List (Cell n k) :=
  [(p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, p.2 + 1), (p.1, p.2 - 1)]

/-- Toppling `p`: it loses 4 grains and each of its 4 neighbours gains one, except `c[0,0]`. -/
def topple {n k : ℕ} (c : Cell n k → ℤ) (p : Cell n k) (q : Cell n k) : ℤ :=
  c q - (if q = p then 4 else 0) + (if q = 0 then 0 else ((neighbours p).count q : ℤ))

/-- The configuration after toppling the cells of `L` in order. -/
def run {n k : ℕ} (L : List (Cell n k)) : Cell n k → ℤ := L.foldl topple (initial n k)

/-- Every toppled cell holds at least 4 grains when it is toppled. -/
def Legal {n k : ℕ} (L : List (Cell n k)) : Prop :=
  ∀ (i : ℕ) (h : i < L.length), 4 ≤ run (L.take i) (L.get ⟨i, h⟩)

/-- No cell holds 4 or more grains. -/
def Stable {n k : ℕ} (c : Cell n k → ℤ) : Prop := ∀ q, c q < 4

/-- OEIS A023855: `a(n) = 1*(n) + 2*(n-1) + ... + (n+1-k)*k`, `k = floor((n+1)/2)`. -/
def a023855 (m : ℕ) : ℕ := ∑ j ∈ Finset.Icc 1 ((m + 1) / 2), j * (m + 1 - j)

/-- OEIS A293452 (corrected index): for `n ≥ 2` the `n × 1` torus reaches a final state, and every
legal toppling sequence ending in a final state has `A023855(n - 1)` topplings. -/
def claim : Prop := ∀ n : ℕ, 2 ≤ n →
  (∃ L : List (Cell n 1), Legal L ∧ Stable (run L)) ∧
    ∀ L : List (Cell n 1), Legal L → Stable (run L) → L.length = a023855 (n - 1)

/-- Toppling counts on the `n × 1` torus. -/
private def cnt {n : ℕ} (L : List (Cell n 1)) (i : ZMod n) : ℕ := L.count ((i, 0) : Cell n 1)

/-- Twice the target odometer. -/
private def g (n x : ℕ) : ℕ := x * (n - x) + (if n % 2 = 0 then min x (n - x) else 0)

/-- The target odometer. -/
private def f (n x : ℕ) : ℕ := g n x / 2

/-- The target odometer on the torus cells. -/
private def ustar (n : ℕ) (i : ZMod n) : ℕ := f n i.val

theorem result : claim := by
  intro n hn
  have : NeZero n := ⟨by omega⟩
  -- toppling sequences and their odometer
  have run_append : ∀ (L : List (Cell n 1)) (p : Cell n 1), run (L ++ [p]) = topple (run L) p := by
    intro L p
    simp [run, List.foldl_append]
  have legal_append : ∀ (L : List (Cell n 1)) (p : Cell n 1),
      Legal (L ++ [p]) ↔ Legal L ∧ 4 ≤ run L p := by
    intro L p
    constructor
    · intro h
      refine ⟨fun i hi => ?_, ?_⟩
      · have := h i (by simp; omega)
        simpa [List.take_append_of_le_length (le_of_lt hi), List.getElem_append_left hi] using this
      · have := h L.length (by simp)
        simpa using this
    · rintro ⟨hL, hp⟩ i hi
      simp at hi
      rcases Nat.lt_or_ge i L.length with h | h
      · have := hL i h
        simpa [List.take_append_of_le_length (le_of_lt h), List.getElem_append_left h] using this
      · have : i = L.length := by omega
        subst this
        simpa using hp
  have run_eq : ∀ (L : List (Cell n 1)) (q : Cell n 1),
      run L q = initial n 1 q - 4 * (L.count q : ℤ) +
        (if q = 0 then 0 else ((L.map fun p => (neighbours p).count q).sum : ℤ)) := by
    intro L q
    induction L using List.reverseRecOn with
    | nil => simp [run]
    | append_singleton L p ih =>
      rw [run_append, topple, ih]
      simp only [List.count_append, List.map_append, List.sum_append, List.count_cons,
        List.count_nil,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      by_cases h1 : q = 0
      · subst h1
        by_cases h2 : p = 0
        · subst h2; simp; ring
        · simp [h2, Ne.symm h2]
      · by_cases h2 : p = q
        · subst h2; simp [h1]; ring
        · simp [h1, h2, Ne.symm h2]; ring
  -- the n × 1 torus: every cell is (i, 0)
  have cell_eq : ∀ (p : Cell n 1), p = (p.1, 0) := by
    intro p
    ext
    · rfl
    · exact Subsingleton.elim _ _
  have nbr_sum : ∀ (L : List (Cell n 1)) (i : ZMod n),
      (L.map fun p => (neighbours p).count ((i, 0) : Cell n 1)).sum =
        cnt L (i - 1) + cnt L (i + 1) + 2 * cnt L i := by
    intro L i
    induction L with
    | nil => simp [cnt]
    | cons p L ih =>
      rw [List.map_cons, List.sum_cons, ih]
      obtain ⟨a, z⟩ := p
      obtain rfl : z = 0 := Subsingleton.elim _ _
      have e1 : ((0 : ZMod 1) + 1) = 0 := Subsingleton.elim _ _
      have e2 : ((0 : ZMod 1) - 1) = 0 := Subsingleton.elim _ _
      have c1 : (a + 1 = i) ↔ (a = i - 1) := by constructor <;> intro h <;> subst h <;> ring
      have c2 : (a - 1 = i) ↔ (a = i + 1) := by constructor <;> intro h <;> subst h <;> ring
      simp only [neighbours, e1, e2, cnt, List.count_cons, List.count_nil, Prod.mk.injEq, and_true,
        beq_iff_eq, c1, c2]
      by_cases b1 : a = i - 1 <;> by_cases b2 : a = i + 1 <;> by_cases a3 : a = i <;>
        simp [b1, b2, a3] <;> omega
  have run_one : ∀ (L : List (Cell n 1)) (i : ZMod n),
      run L (i, 0) = if i = 0 then -4 * (cnt L 0 : ℤ)
        else 4 - 2 * (cnt L i : ℤ) + cnt L (i - 1) + cnt L (i + 1) := by
    intro L i
    have h0 : ((i, 0) : Cell n 1) = 0 ↔ i = 0 := by
      constructor
      · intro h; exact congrArg Prod.fst h
      · intro h; subst h; rfl
    rw [run_eq, nbr_sum]
    by_cases hi : i = 0
    · subst hi; simp [initial, cnt]
    · have : ((i, 0) : Cell n 1) ≠ 0 := fun h => hi (h0.mp h)
      simp only [initial, this, if_false, hi, cnt]
      push_cast; ring
  have cnt_zero : ∀ (L : List (Cell n 1)), Legal L → cnt L 0 = 0 := by
    intro L hL
    induction L using List.reverseRecOn with
    | nil => simp [cnt]
    | append_singleton L p ih =>
      rw [legal_append] at hL
      have h := ih hL.1
      have hp := hL.2
      obtain ⟨a, z⟩ := p
      obtain rfl : z = 0 := Subsingleton.elim _ _
      by_cases ha : a = 0
      · subst ha
        rw [run_one] at hp
        simp [h] at hp
      · simp only [cnt, List.count_append, List.count_cons, List.count_nil] at h ⊢
        simp [h, ha]
  -- the target odometer u*(x) = (x(n - x) + [n even] min(x, n - x)) / 2
  have g_even : ∀ x, x ≤ n → 2 ∣ g n x := by
    intro x hx
    unfold g
    rw [← even_iff_two_dvd]
    split_ifs with hn
    · rcases le_total x (n - x) with h | h
      · rw [min_eq_left h, show x * (n - x) + x = x * (n - x + 1) by ring, Nat.even_mul]
        rcases Nat.even_or_odd x with e | o
        · exact Or.inl e
        · right; rw [Nat.even_iff] at *; rw [Nat.odd_iff] at o; omega
      · rw [min_eq_right h, show x * (n - x) + (n - x) = (x + 1) * (n - x) by ring, Nat.even_mul]
        rcases Nat.even_or_odd x with e | o
        · right; rw [Nat.even_iff] at *; omega
        · left; rw [Nat.even_iff]; rw [Nat.odd_iff] at o; omega
    · rw [add_zero, Nat.even_mul]
      rcases Nat.even_or_odd x with e | o
      · exact Or.inl e
      · right; rw [Nat.even_iff]; rw [Nat.odd_iff] at o; omega
  have two_f : ∀ x, x ≤ n → 2 * f n x = g n x := by
    intro x hx
    unfold f; exact Nat.mul_div_cancel' (g_even x hx)
  have f_zero : f n 0 = 0 := by
    simp [f, g]
  have f_self : f n n = 0 := by
    simp [f, g]
  have f_second : ∀ x, 1 ≤ x → x + 1 ≤ n →
      ((f n (x - 1) : ℤ) + f n (x + 1) - 2 * f n x) =
        -1 - (if n % 2 = 0 ∧ 2 * x = n then 1 else 0) := by
    intro x h1 h2
    have e1 := two_f (x - 1) (by omega)
    have e2 := two_f (x + 1) (by omega)
    have e3 := two_f x (by omega)
    have key : (2 : ℤ) * ((f n (x - 1) : ℤ) + f n (x + 1) - 2 * f n x) =
        (g n (x - 1) : ℤ) + g n (x + 1) - 2 * g n x := by
      have := congrArg (fun t : ℕ => (t : ℤ)) e1
      have := congrArg (fun t : ℕ => (t : ℤ)) e2
      have := congrArg (fun t : ℕ => (t : ℤ)) e3
      push_cast at *
      linarith
    have hg : (g n (x - 1) : ℤ) + g n (x + 1) - 2 * g n x =
        -2 - 2 * (if n % 2 = 0 ∧ 2 * x = n then 1 else 0) := by
      unfold g
      have c1 : ((x - 1 : ℕ) : ℤ) = x - 1 := by push_cast [Nat.cast_sub (show 1 ≤ x by omega)]; ring
      have c2 : ((n - (x - 1) : ℕ) : ℤ) = n - x + 1 := by
        rw [Nat.cast_sub (show x - 1 ≤ n by omega), c1]; ring
      have c3 : ((n - (x + 1) : ℕ) : ℤ) = n - x - 1 := by
        rw [Nat.cast_sub (show x + 1 ≤ n by omega)]; push_cast; ring
      have c4 : ((n - x : ℕ) : ℤ) = n - x := by rw [Nat.cast_sub (show x ≤ n by omega)]
      push_cast
      rw [c1, c2, c3, c4]
      by_cases hn : n % 2 = 0
      · simp only [hn, if_true, true_and]
        rcases lt_trichotomy (2 * x) n with h | h | h
        · have : ¬ (2 * x = n) := by omega
          simp only [this, if_false]
          rw [min_eq_left (by omega), min_eq_left (by omega), min_eq_left (by omega)]; ring
        · simp only [h, if_true]
          rw [min_eq_left (by omega), min_eq_right (by omega), min_eq_left (by omega)]
          have : (n : ℤ) = 2 * x := by exact_mod_cast h.symm
          rw [this]; ring
        · have : ¬ (2 * x = n) := by omega
          simp only [this, if_false]
          rw [min_eq_right (by omega), min_eq_right (by omega), min_eq_right (by omega)]; ring
      · simp only [hn, if_false, false_and]; ring
    split_ifs at hg ⊢ <;> linarith
  have val_sub_one : ∀ (i : ZMod n), i ≠ 0 → (i - 1).val = i.val - 1 := by
    intro i hi
    have h1 : 1 ≤ i.val := Nat.one_le_iff_ne_zero.mpr ((ZMod.val_ne_zero i).mpr hi)
    have : i - 1 = ((i.val - 1 : ℕ) : ZMod n) := by
      rw [Nat.cast_sub h1, ZMod.natCast_zmod_val, Nat.cast_one]
    rw [this, ZMod.val_cast_of_lt (by have := ZMod.val_lt i; omega)]
  have ustar_succ : ∀ (i : ZMod n), ustar n (i + 1) = f n (i.val + 1) := by
    intro i
    unfold ustar
    have hlt := ZMod.val_lt i
    rcases Nat.lt_or_ge (i.val + 1) n with h | h
    · have : i + 1 = ((i.val + 1 : ℕ) : ZMod n) := by push_cast; rw [ZMod.natCast_zmod_val]
      rw [this, ZMod.val_cast_of_lt h]
    · have e : i.val + 1 = n := by omega
      have : i + 1 = 0 := by
        have : ((i.val + 1 : ℕ) : ZMod n) = 0 := by rw [e, ZMod.natCast_self]
        push_cast at this; rwa [ZMod.natCast_zmod_val] at this
      rw [this, ZMod.val_zero, e, f_zero, f_self]
  have cstar : ∀ (i : ZMod n), i ≠ 0 →
      (4 : ℤ) - 2 * ustar n i + ustar n (i - 1) + ustar n (i + 1) =
        3 - (if n % 2 = 0 ∧ 2 * i.val = n then 1 else 0) := by
    intro i hi
    have : NeZero n := ⟨by omega⟩
    have h1 : 1 ≤ i.val := Nat.one_le_iff_ne_zero.mpr ((ZMod.val_ne_zero i).mpr hi)
    have h2 := ZMod.val_lt i
    rw [ustar_succ]
    unfold ustar
    rw [val_sub_one i hi]
    have := f_second i.val h1 (by omega)
    linarith
  -- least action and the discrete maximum principle
  have least_action : ∀ (L : List (Cell n 1)), Legal L → ∀ i, cnt L i ≤ ustar n i := by
    intro L hL
    have : NeZero n := ⟨by omega⟩
    induction L using List.reverseRecOn with
    | nil => intro i; simp [cnt]
    | append_singleton L p ih =>
      rw [legal_append] at hL
      have hle := ih hL.1
      have hp := hL.2
      obtain ⟨a, z⟩ := p
      obtain rfl : z = 0 := Subsingleton.elim _ _
      have ha : a ≠ 0 := by
        intro h; subst h
        rw [run_one] at hp; simp at hp; omega
      rw [run_one, if_neg ha] at hp
      have hc := cstar a ha
      have l1 := hle (a - 1)
      have l2 := hle (a + 1)
      have hlt : cnt L a < ustar n a := by
        have : (cnt L (a - 1) : ℤ) ≤ ustar n (a - 1) := by exact_mod_cast l1
        have : (cnt L (a + 1) : ℤ) ≤ ustar n (a + 1) := by exact_mod_cast l2
        have : (0 : ℤ) ≤ (if n % 2 = 0 ∧ 2 * a.val = n then 1 else 0) := by split_ifs <;> norm_num
        have : (cnt L a : ℤ) < ustar n a := by linarith
        exact_mod_cast this
      intro i
      simp only [cnt, List.count_append, List.count_cons, List.count_nil, Prod.mk.injEq, and_true,
        beq_iff_eq] at hle hlt ⊢
      by_cases hia : a = i
      · subst hia; simp; omega
      · simp [hia]; exact hle i
  have odometer_eq : ∀ (L : List (Cell n 1)), Legal L → Stable (run L) →
      ∀ i, cnt L i = ustar n i := by
    intro L hL hs
    have : NeZero n := ⟨by omega⟩
    let D : ℕ → ℤ := fun x => (ustar n (x : ZMod n) : ℤ) - cnt L (x : ZMod n)
    have la := least_action L hL
    have Dnn : ∀ x, 0 ≤ D x := fun x => by
      have h := la (x : ZMod n)
      have : (cnt L (x : ZMod n) : ℤ) ≤ ustar n (x : ZMod n) := by exact_mod_cast h
      simp only [D]; linarith
    have D0 : D 0 = 0 := by
      simp only [D, Nat.cast_zero, ustar, ZMod.val_zero, f_zero, cnt_zero L hL]; simp
    have Dn : D n = 0 := by
      have : ((n : ℕ) : ZMod n) = 0 := ZMod.natCast_self n
      simp only [D, this]; simpa [D] using D0
    have lap : ∀ x, 1 ≤ x → x + 1 ≤ n →
        D (x - 1) + D (x + 1) - 2 * D x ≥ -(if n % 2 = 0 ∧ 2 * x = n then 1 else 0) := by
      intro x h1 h2
      set i : ZMod n := (x : ZMod n) with hi
      have hval : i.val = x := ZMod.val_cast_of_lt (by omega)
      have hne : i ≠ 0 := by
        intro h; rw [h, ZMod.val_zero] at hval; omega
      have e1 : ((x - 1 : ℕ) : ZMod n) = i - 1 := by rw [Nat.cast_sub h1]; simp [hi]
      have e2 : ((x + 1 : ℕ) : ZMod n) = i + 1 := by push_cast; rfl
      have hr := hs (i, 0)
      rw [run_one, if_neg hne] at hr
      have hc := cstar i hne
      rw [hval] at hc
      simp only [D, e1, e2, ← hi]
      linarith
    -- the maximum of `D` is zero
    obtain ⟨xm, hxm, hmax⟩ := Finset.exists_max_image (Finset.range (n + 1)) D ⟨0, by simp⟩
    have hM : D xm ≤ 0 := by
      by_contra hpos
      push Not at hpos
      set M := D xm
      let S := (Finset.range (n + 1)).filter (fun x => D x = M)
      have hS : S.Nonempty := ⟨xm, by simp only [S, Finset.mem_filter]; exact ⟨hxm, rfl⟩⟩
      have inS : ∀ x, x ∈ S ↔ x ≤ n ∧ D x = M := fun x => by
        simp [S]
      have leM : ∀ x, x ≤ n → D x ≤ M := fun x hx => hmax x (by simp; omega)
      set x0 := S.min' hS
      set x1 := S.max' hS
      have hx0 := (inS x0).mp (S.min'_mem hS)
      have hx1 := (inS x1).mp (S.max'_mem hS)
      have x0pos : 1 ≤ x0 := by
        rcases Nat.eq_zero_or_pos x0 with h | h
        · rw [h, D0] at hx0; linarith [hx0.2]
        · exact h
      have x0lt : x0 + 1 ≤ n := by
        rcases Nat.lt_or_ge x0 n with h | h
        · omega
        · have : x0 = n := by omega
          rw [this, Dn] at hx0; linarith [hx0.2]
      have x1pos : 1 ≤ x1 := le_trans x0pos (S.min'_le_max' hS)
      have x1lt : x1 + 1 ≤ n := by
        rcases Nat.lt_or_ge x1 n with h | h
        · omega
        · have : x1 = n := by omega
          rw [this, Dn] at hx1; linarith [hx1.2]
      -- at the leftmost maximum the left neighbour is strictly smaller
      have left : D (x0 - 1) < M := by
        rcases lt_or_eq_of_le (leM (x0 - 1) (by omega)) with h | h
        · exact h
        · exfalso
          have hmem : x0 - 1 ∈ S := (inS _).mpr ⟨by omega, h⟩
          have := S.min'_le (x0 - 1) hmem
          omega
      have right : D (x1 + 1) < M := by
        rcases lt_or_eq_of_le (leM (x1 + 1) (by omega)) with h | h
        · exact h
        · exfalso
          have hmem : x1 + 1 ∈ S := (inS _).mpr ⟨by omega, h⟩
          have := S.le_max' (x1 + 1) hmem
          omega
      have l0 := lap x0 x0pos x0lt
      have l1 := lap x1 x1pos x1lt
      have r0 := leM (x0 + 1) x0lt
      have r1 := leM (x1 - 1) (by omega)
      rw [hx0.2] at l0
      rw [hx1.2] at l1
      by_cases c0 : n % 2 = 0 ∧ 2 * x0 = n
      · -- then the right neighbour of `x0` is also a maximum, so `x1 > x0`
        have hge : D (x0 + 1) = M := by
          simp only [c0, and_self, if_true] at l0; linarith
        have hmem : x0 + 1 ∈ S := (inS _).mpr ⟨x0lt, hge⟩
        have := S.le_max' (x0 + 1) hmem
        have c1 : ¬ (n % 2 = 0 ∧ 2 * x1 = n) := by omega
        simp only [c1, if_false] at l1
        linarith
      · simp only [c0, if_false] at l0
        linarith
    intro i
    have hval := ZMod.val_lt i
    have h1 := hmax i.val (by simp; omega)
    have h2 := Dnn i.val
    have : D i.val = 0 := by linarith
    simp only [D, ZMod.natCast_zmod_val] at this
    omega
  -- the length of a sequence and the total of the target odometer
  have length_eq : ∀ (L : List (Cell n 1)), L.length = ∑ i : ZMod n, cnt L i := by
    intro L
    have h : ∀ L : List (Cell n 1), L.length = ∑ q : Cell n 1, L.count q := by
      intro L
      induction L with
      | nil => simp
      | cons p L ih =>
        simp only [List.length_cons, List.count_cons, Finset.sum_add_distrib, ih, beq_iff_eq]
        simp
    rw [h, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_unique]
    rfl
  have sum_A : ∀ B, B ≤ n + 1 →
      6 * ((∑ x ∈ Finset.range B, x * (n - x) : ℕ) : ℚ) =
        3 * n * B * (B - 1) - (B - 1) * B * (2 * B - 1) := by
    intro B hB
    induction B with
    | zero => simp
    | succ B ih =>
      rw [Finset.sum_range_succ, Nat.cast_add, mul_add, ih (by omega), Nat.cast_mul,
        Nat.cast_sub (show B ≤ n by omega)]
      push_cast; ring
  have sum_R : ∀ K, K ≤ n →
      6 * ((∑ j ∈ Finset.Icc 1 K, j * (n - j) : ℕ) : ℚ) =
        3 * n * K * (K + 1) - K * (K + 1) * (2 * K + 1) := by
    intro K hK
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Nat.cast_add, mul_add, ih (by omega), Nat.cast_mul,
        Nat.cast_sub (show K + 1 ≤ n by omega)]
      push_cast; ring
  have sum_min : ∀ m : ℕ, ∑ x ∈ Finset.range (2 * m), min x (2 * m - x) = m * m := by
    intro m
    rw [two_mul, Finset.sum_range_add]
    have h1 : ∑ x ∈ Finset.range m, min x (m + m - x) = ∑ x ∈ Finset.range m, x :=
      Finset.sum_congr rfl fun x hx => by
        simp only [Finset.mem_range] at hx; exact min_eq_left (by omega)
    have h2 : ∑ y ∈ Finset.range m, min (m + y) (m + m - (m + y)) =
        ∑ y ∈ Finset.range m, (m - 1 - y + 1) :=
      Finset.sum_congr rfl fun y hy => by
        simp only [Finset.mem_range] at hy; rw [min_eq_right (by omega)]; omega
    rw [h1, h2, Finset.sum_range_reflect (fun j => j + 1) m, Finset.sum_add_distrib]
    have h3 := Finset.sum_range_id_mul_two m
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      rw [show k + 1 - 1 = k by omega] at h3
      have : (∑ i ∈ Finset.range (k + 1), i) * 2 = (k + 1) * k := h3
      nlinarith
  have sum_f : ∑ x ∈ Finset.range n, f n x = a023855 (n - 1) := by
    have e2 : 2 * ∑ x ∈ Finset.range n, f n x = ∑ x ∈ Finset.range n, g n x := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x hx => two_f x (by simp at hx; omega)
    unfold a023855
    rw [show n - 1 + 1 = n by omega]
    have hR := sum_R (n / 2) (by omega)
    have hA := sum_A n (by omega)
    have hsub : ∑ j ∈ Finset.Icc 1 (n / 2), j * (n - j) =
        ∑ j ∈ Finset.Icc 1 (n / 2), j * (n - j) := rfl
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · have hg : ∑ x ∈ Finset.range n, g n x = ∑ x ∈ Finset.range n, x * (n - x) + m * m := by
        unfold g
        have hev : n % 2 = 0 := by omega
        simp only [hev, if_true, Finset.sum_add_distrib]
        rw [show n = 2 * m by omega, sum_min]
      have hk : n / 2 = m := by omega
      rw [hk] at hR ⊢
      have e2' : (2 : ℚ) * ((∑ x ∈ Finset.range n, f n x : ℕ) : ℚ) =
          ((∑ x ∈ Finset.range n, x * (n - x) : ℕ) : ℚ) + (m : ℚ) * m := by
        have := congrArg (fun t : ℕ => (t : ℚ)) (e2.trans hg); push_cast at this ⊢; linarith
      have hn' : (n : ℚ) = 2 * m := by exact_mod_cast (show n = 2 * m by omega)
      have : ((∑ x ∈ Finset.range n, f n x : ℕ) : ℚ) =
          ((∑ j ∈ Finset.Icc 1 m, j * (n - j) : ℕ) : ℚ) := by
        rw [hn'] at hA hR
        linear_combination (1 / 2 : ℚ) * e2' + (1 / 12 : ℚ) * hA - (1 / 6 : ℚ) * hR
      exact_mod_cast this
    · have hg : ∑ x ∈ Finset.range n, g n x = ∑ x ∈ Finset.range n, x * (n - x) := by
        unfold g
        have hod : n % 2 ≠ 0 := by omega
        simp only [hod, if_false, add_zero]
      have hk : n / 2 = m := by omega
      rw [hk] at hR ⊢
      have e2' : (2 : ℚ) * ((∑ x ∈ Finset.range n, f n x : ℕ) : ℚ) =
          ((∑ x ∈ Finset.range n, x * (n - x) : ℕ) : ℚ) := by
        have := congrArg (fun t : ℕ => (t : ℚ)) (e2.trans hg); push_cast at this ⊢; linarith
      have hn' : (n : ℚ) = 2 * m + 1 := by exact_mod_cast hm
      have : ((∑ x ∈ Finset.range n, f n x : ℕ) : ℚ) =
          ((∑ j ∈ Finset.Icc 1 m, j * (n - j) : ℕ) : ℚ) := by
        rw [hn'] at hA hR
        linear_combination (1 / 2 : ℚ) * e2' + (1 / 12 : ℚ) * hA - (1 / 6 : ℚ) * hR
      exact_mod_cast this
  have sum_ustar : ∑ i : ZMod n, ustar n i = ∑ x ∈ Finset.range n, f n x := by
    refine Finset.sum_nbij' ZMod.val (fun x => (x : ZMod n)) ?_ ?_ ?_ ?_ ?_
    · intro r _; simpa using ZMod.val_lt r
    · intro i _; simp
    · intro r _; simp
    · intro i hi; simp only [Finset.mem_range] at hi; exact ZMod.val_cast_of_lt hi
    · intro r _; rfl
  have total : ∑ i : ZMod n, ustar n i = a023855 (n - 1) := by
    rw [sum_ustar, sum_f]
  have bound : ∀ L : List (Cell n 1), Legal L → L.length ≤ a023855 (n - 1) := by
    intro L hL
    rw [length_eq, ← total]
    exact Finset.sum_le_sum fun i _ => least_action L hL i
  refine ⟨?_, fun L hL hs => ?_⟩
  · classical
    let P : ℕ → Prop := fun ℓ => ∃ L : List (Cell n 1), Legal L ∧ L.length = ℓ
    have P0 : P 0 := ⟨[], fun i h => by simp at h, rfl⟩
    have hspec := Nat.findGreatest_spec (P := P) (Nat.zero_le (a023855 (n - 1))) P0
    obtain ⟨L, hL, hlen⟩ := hspec
    refine ⟨L, hL, fun q => ?_⟩
    by_contra hq
    push Not at hq
    have hL' : Legal (L ++ [q]) := (legal_append L q).mpr ⟨hL, hq⟩
    have hb := bound _ hL'
    simp only [List.length_append, List.length_singleton] at hb
    have h1 : Nat.findGreatest P (a023855 (n - 1)) < L.length + 1 := by omega
    exact Nat.findGreatest_is_greatest h1 hb ⟨L ++ [q], hL', by simp⟩
  · rw [length_eq, ← total]
    exact Finset.sum_congr rfl fun i _ => odometer_eq L hL hs i



end D5.S3.StatisticalMechanics.Sandpiles.TorusColumnToppling
