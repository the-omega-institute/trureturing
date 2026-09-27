/- GID: D5/S3/Combinatorics/LatticeWalkNearMaximalArea
   generality: G
   mirror-B: D5/B/S3/Combinatorics/LatticeWalkNearMaximalArea
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Proves the conjecture of OEIS A385672 (Andrei Zabolotskii, 2025): for k < n the number of 2n-step square-lattice walks of algebraic area n^2 - k is 2 A029552(k), and the number of (2n+1)-step walks of area n^2 + n - k is 4 A098613(k). -/

/-
proof_shape: result: content
escape_witness: form (2), the public conclusion `result` itself: the area of a walk is at most
  r u + l d for its numbers of right, up, left and down steps (`bound`), so a walk whose area is
  above the stated range uses only right and up steps or only left and down steps (`mono`);
  exchanging right with left and up with down keeps the area (`area_flip`); an up-right word with u
  up steps and r right steps has area u r minus its inversions (`area_bool`); words with u up steps
  and m inversions satisfy the recurrence of partitions of m into parts at most u (`word_rec`,
  `boxed_rec` through `Nat.Partition.partitionWithPartEquiv`), so for u + m at most the length and
  m at most u they are counted by the partitions of m (`core`); summing over u gives the two theta
  coefficients
admission_basis: open-problem-resolution (issue #10337)
Direct frozen dependencies: `D5/S1/Digit/Carry/ListInversions`: `inv`
-/

import D5.S1.Digit.Carry.ListInversions
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Bool.Count
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.LatticeWalkNearMaximalArea

open D5.S1.Digit.Carry

/-- A unit step of a walk on the square lattice. -/
inductive Step
  | right
  | left
  | up
  | down
  deriving DecidableEq

instance : Fintype Step :=
  ⟨{Step.right, Step.left, Step.up, Step.down}, fun s => by cases s <;> simp⟩

/-- The integral of `y dx` along a walk that starts at height `y`: a right step adds the current
height and a left step subtracts it. -/
def areaFrom : ℤ → List Step → ℤ
  | _, [] => 0
  | y, Step.right :: w => y + areaFrom y w
  | y, Step.left :: w => -y + areaFrom y w
  | y, Step.up :: w => areaFrom (y + 1) w
  | y, Step.down :: w => areaFrom (y - 1) w

/-- The algebraic area of a walk from the origin. -/
def area (w : List Step) : ℤ := areaFrom 0 w

/-- A385672: the number of `n`-step walks with algebraic area `k`. -/
def walkCount (n : ℕ) (k : ℤ) : ℕ :=
  (Finset.univ.filter fun w : Fin n → Step => area (List.ofFn w) = k).card

/-- A000041: the number of partitions of `m`. -/
def partitionCount (m : ℕ) : ℕ := Fintype.card m.Partition

/-- A029552, from its generating function `(1 + 2 Σ_{j>0} x^(j^2)) / ∏_{i>0} (1 - x^i)`. -/
def a029552 (k : ℕ) : ℕ :=
  partitionCount k +
    2 * ∑ j ∈ (Finset.Icc 1 k).filter (fun j => j ^ 2 ≤ k), partitionCount (k - j ^ 2)

/-- A098613, from its generating function `(Σ_{j>0} x^(j^2-j)) / ∏_{i>0} (1 - x^i)`. -/
def a098613 (k : ℕ) : ℕ :=
  ∑ j ∈ (Finset.Icc 1 (k + 1)).filter (fun j => j ^ 2 - j ≤ k), partitionCount (k - (j ^ 2 - j))

/-- The conjecture of A385672. -/
def claim : Prop :=
  ∀ n k : ℕ, k < n →
    walkCount (2 * n) ((n : ℤ) ^ 2 - k) = 2 * a029552 k ∧
      walkCount (2 * n + 1) ((n : ℤ) ^ 2 + n - k) = 4 * a098613 k

/-- Exchange right with left and up with down. -/
private def flipStep : Step → Step
  | Step.right => Step.left
  | Step.left => Step.right
  | Step.up => Step.down
  | Step.down => Step.up

/-- Read `true` as an up step and `false` as a right step. -/
private def toStep : Bool → Step
  | true => Step.up
  | false => Step.right

/-- Words of length `L` with `u` letters `true` and `m` inversions, a `false` before a `true`
being an inversion of the word read with `false ↦ 1` and `true ↦ 0`. -/
private def wordCount (L u m : ℕ) : ℕ :=
  (Finset.univ.filter fun b : Fin L → Bool =>
    (List.ofFn b).count true = u ∧
      ListInversions.inv ((List.ofFn b).map fun x => (!x).toNat) = m).card

/-- The words of length `N` with `u` up steps and area `A`, counted through their inversions. -/
private def summand (N : ℕ) (A : ℤ) (u : ℕ) : ℕ :=
  if 0 ≤ (u : ℤ) * (N - u) - A then wordCount N u ((u : ℤ) * (N - u) - A).toNat else 0

/-- Partitions of `m` with all parts at most `u`. -/
private def boxedCount (u m : ℕ) : ℕ := (Nat.Partition.restricted m (· ≤ u)).card

theorem result : claim := by
  classical
  -- the inversions of a Boolean word, read with `false ↦ 1` and `true ↦ 0`
  have inv_true : ∀ w : List Bool, ListInversions.inv ((true :: w).map fun x => (!x).toNat) =
      ListInversions.inv (w.map fun x => (!x).toNat) := by
    intro w
    simp [ListInversions.inv]
  have inv_false : ∀ w : List Bool, ListInversions.inv ((false :: w).map fun x => (!x).toNat) =
      w.count true + ListInversions.inv (w.map fun x => (!x).toNat) := by
    intro w
    rw [List.map_cons, ListInversions.inv, List.countP_map, List.count_eq_countP, add_comm]
    congr 2
    funext x
    cases x <;> rfl
  -- splitting a word at its first letter
  have split : ∀ (L : ℕ) (Q : List Bool → Prop) [DecidablePred Q],
      (Finset.univ.filter fun f : Fin (L + 1) → Bool => Q (List.ofFn f)).card =
        (Finset.univ.filter fun g : Fin L → Bool => Q (true :: List.ofFn g)).card +
          (Finset.univ.filter fun g : Fin L → Bool => Q (false :: List.ofFn g)).card := by
    intro L Q _
    simp only [Finset.card_filter]
    rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (L + 1) => Bool), Fintype.sum_prod_type,
      Fintype.sum_bool]
    simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
  -- words without `true`
  have word_zero : ∀ L m, wordCount L 0 m = if m = 0 then 1 else 0 := by
    intro L
    induction L with
    | zero =>
      intro m
      unfold wordCount
      by_cases hm : m = 0
      · subst hm
        simp [ListInversions.inv]
      · simp [ListInversions.inv, hm]
        omega
    | succ L ih =>
      intro m
      rw [← ih m]
      unfold wordCount
      rw [split L
        (fun l => l.count true = 0 ∧ ListInversions.inv (l.map fun x => (!x).toNat) = m)]
      have h1 : (Finset.univ.filter fun g : Fin L → Bool =>
          (true :: List.ofFn g).count true = 0 ∧
            ListInversions.inv ((true :: List.ofFn g).map fun x => (!x).toNat) = m).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro g _ h
        simp at h
      rw [h1, zero_add]
      congr 1
      apply Finset.filter_congr
      intro g _
      simp only [inv_false, List.count_cons_of_ne (Bool.false_ne_true)]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by omega⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by omega⟩
  -- first-letter recurrence
  have word_rec : ∀ L u m, wordCount (L + 1) (u + 1) m =
      wordCount L u m + if u + 1 ≤ m then wordCount L (u + 1) (m - (u + 1)) else 0 := by
    intro L u m
    unfold wordCount
    rw [split L
      (fun l => l.count true = u + 1 ∧ ListInversions.inv (l.map fun x => (!x).toNat) = m)]
    congr 1
    · congr 1
      apply Finset.filter_congr
      intro g _
      simp only [inv_true, List.count_cons_self, Nat.add_right_cancel_iff]
    · split_ifs with h
      · congr 1
        apply Finset.filter_congr
        intro g _
        simp only [inv_false, List.count_cons_of_ne (Bool.false_ne_true)]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, by omega⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h1, by omega⟩
      · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro g _ hg
        simp only [inv_false, List.count_cons_of_ne (Bool.false_ne_true)] at hg
        omega
  -- partitions with all parts at most `0`
  have boxed_zero : ∀ m, boxedCount 0 m = if m = 0 then 1 else 0 := by
    intro m
    unfold boxedCount Nat.Partition.restricted
    split_ifs with hm
    · subst hm
      rw [Finset.card_eq_one]
      refine ⟨default, ?_⟩
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro _
        exact Subsingleton.elim _ _
      · intro _ i hi
        exact absurd (p.parts_pos hi) (by have := Nat.Partition.le_of_mem_parts hi; omega)
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro p _ h
      have hne : p.parts ≠ 0 := by
        intro h0
        have := p.parts_sum
        rw [h0] at this
        simp at this
        omega
      obtain ⟨i, hi⟩ := Multiset.exists_mem_of_ne_zero hne
      have := p.parts_pos hi
      have := h i hi
      omega
  -- recurrence by whether the part `u + 1` occurs
  have boxed_rec : ∀ u m, boxedCount (u + 1) m =
      boxedCount u m + if u + 1 ≤ m then boxedCount (u + 1) (m - (u + 1)) else 0 := by
    intro u m
    unfold boxedCount Nat.Partition.restricted
    rw [← Finset.card_filter_add_card_filter_not (fun p : m.Partition => u + 1 ∈ p.parts)]
    rw [add_comm]
    congr 1
    · congr 1
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro p _
      constructor
      · rintro ⟨h1, h2⟩ i hi
        have := h1 i hi
        have : i ≠ u + 1 := fun h => h2 (h ▸ hi)
        omega
      · intro h
        refine ⟨fun i hi => by have := h i hi; omega, fun hu => ?_⟩
        have := h _ hu
        omega
    · split_ifs with hm
      · rw [Finset.filter_filter]
        refine Finset.card_bij'
          (fun p hp => Nat.Partition.partitionWithPartEquiv (Nat.succ_pos u) hm
            ⟨p, (Finset.mem_filter.1 hp).2.2⟩)
          (fun q _ => ((Nat.Partition.partitionWithPartEquiv (Nat.succ_pos u) hm).symm q).1)
          ?_ ?_ ?_ ?_
        · intro p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
          intro i hi
          rw [Nat.Partition.partitionWithPartEquiv_apply_parts] at hi
          exact hp.1 i (Multiset.mem_of_mem_erase hi)
        · intro q hq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
          rw [Nat.Partition.partitionWithPartEquiv_symm_apply_parts]
          refine ⟨fun i hi => ?_, Multiset.mem_cons_self _ _⟩
          rcases Multiset.mem_cons.1 hi with rfl | hi
          · exact le_refl _
          · exact hq i hi
        · intro p hp
          simp
        · intro q hq
          simp
      · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro p _ h
        have := Nat.Partition.le_of_mem_parts h
        omega
  have boxed_full : ∀ u m, m ≤ u → boxedCount u m = Fintype.card m.Partition := by
    intro u m hm
    unfold boxedCount Nat.Partition.restricted
    rw [Finset.filter_true_of_mem, Finset.card_univ]
    intro p _ i hi
    exact le_trans (Nat.Partition.le_of_mem_parts hi) hm
  have core : ∀ L u m : ℕ, u + m ≤ L → m ≤ u → wordCount L u m = partitionCount m := by
    have main : ∀ L u m : ℕ, u + m ≤ L → wordCount L u m = boxedCount u m := by
      intro L
      induction L with
      | zero =>
        intro u m h
        have hu : u = 0 := by omega
        have hm : m = 0 := by omega
        subst hu hm
        rw [word_zero, boxed_zero]
      | succ L ih =>
        intro u m h
        cases u with
        | zero => rw [word_zero, boxed_zero]
        | succ u =>
          rw [word_rec, boxed_rec, ih u m (by omega)]
          split_ifs with hm
          · rw [ih (u + 1) (m - (u + 1)) (by omega)]
          · rfl
    intro L u m h hm
    rw [main L u m h, boxed_full u m hm]
    rfl
  -- step counts
  have hlen : ∀ w : List Step, (w.length : ℤ) =
      w.count Step.right + w.count Step.left + w.count Step.up + w.count Step.down := by
    intro w
    have h := Multiset.sum_count_eq_card (s := Finset.univ) (m := (w : Multiset Step))
      (fun a _ => Finset.mem_univ a)
    simp only [Multiset.coe_count, Multiset.coe_card] at h
    rw [← h]
    push_cast
    simp [Finset.univ, Fintype.elems]
    ring
  -- each right step sees height at most `y + #up`, each left step depth at most `-y + #down`
  have bound : ∀ (w : List Step) (y : ℤ), areaFrom y w ≤
      (w.count Step.right : ℤ) * (y + w.count Step.up) +
        (w.count Step.left : ℤ) * (-y + w.count Step.down) := by
    intro w
    induction w with
    | nil => intro y; simp [areaFrom]
    | cons s w ih =>
      intro y
      have hR : (0 : ℤ) ≤ w.count Step.right := Nat.cast_nonneg _
      have hL : (0 : ℤ) ≤ w.count Step.left := Nat.cast_nonneg _
      have hU : (0 : ℤ) ≤ w.count Step.up := Nat.cast_nonneg _
      have hD : (0 : ℤ) ≤ w.count Step.down := Nat.cast_nonneg _
      cases s
      · have := ih y
        simp [areaFrom]
        nlinarith
      · have := ih y
        simp [areaFrom]
        nlinarith
      · have := ih (y + 1)
        simp [areaFrom]
        nlinarith
      · have := ih (y - 1)
        simp [areaFrom]
        nlinarith
  -- a walk of large area uses only right and up steps, or only left and down steps
  have mono : ∀ w : List Step, 1 + ((w.length : ℤ) - 1) ^ 2 < 4 * area w →
      (Step.left ∉ w ∧ Step.down ∉ w) ∨ (Step.right ∉ w ∧ Step.up ∉ w) := by
    intro w h
    by_cases h1 : Step.left ∉ w ∧ Step.down ∉ w
    · exact Or.inl h1
    by_cases h2 : Step.right ∉ w ∧ Step.up ∉ w
    · exact Or.inr h2
    exfalso
    have hb := bound w 0
    have hl := hlen w
    have hab : 1 ≤ w.count Step.left + w.count Step.down := by
      rcases not_and_or.1 h1 with h | h
      · have := List.count_pos_iff.2 (not_not.1 h)
        omega
      · have := List.count_pos_iff.2 (not_not.1 h)
        omega
    have haa : 1 ≤ w.count Step.right + w.count Step.up := by
      rcases not_and_or.1 h2 with h | h
      · have := List.count_pos_iff.2 (not_not.1 h)
        omega
      · have := List.count_pos_iff.2 (not_not.1 h)
        omega
    have hab' : (1 : ℤ) ≤ w.count Step.left + w.count Step.down := by exact_mod_cast hab
    have haa' : (1 : ℤ) ≤ w.count Step.right + w.count Step.up := by exact_mod_cast haa
    unfold area at h
    nlinarith [sq_nonneg ((w.count Step.right : ℤ) - w.count Step.up),
      sq_nonneg ((w.count Step.left : ℤ) - w.count Step.down),
      mul_nonneg (sub_nonneg.2 haa') (sub_nonneg.2 hab')]
  -- exchanging right with left and up with down keeps the area
  have area_flip : ∀ (w : List Step) (y : ℤ), areaFrom (-y) (w.map flipStep) = areaFrom y w := by
    intro w
    induction w with
    | nil => intro y; simp [areaFrom]
    | cons s w ih =>
      intro y
      cases s
      · simp [areaFrom, flipStep, ih]
      · simp [areaFrom, flipStep, ih]
      · simp only [List.map_cons, flipStep, areaFrom]
        rw [show -y - 1 = -(y + 1) by ring, ih]
      · simp only [List.map_cons, flipStep, areaFrom]
        rw [show -y + 1 = -(y - 1) by ring, ih]
  -- area of an up-right word
  have area_bool : ∀ (l : List Bool) (y : ℤ),
      areaFrom y (l.map toStep) + ListInversions.inv (l.map fun x => (!x).toNat) =
        (y + l.count true) * l.count false := by
    intro l
    induction l with
    | nil => intro y; simp [areaFrom, ListInversions.inv]
    | cons b l ih =>
      intro y
      cases b
      · have := ih y
        rw [inv_false]
        simp only [List.map_cons, toStep, areaFrom, List.count_cons]
        simp
        linear_combination this
      · have := ih (y + 1)
        rw [inv_true]
        simp only [List.map_cons, toStep, areaFrom, List.count_cons]
        simp
        linear_combination this
  -- reduction of the walk count to up-right words
  have reduce : ∀ (N : ℕ) (A : ℤ), 1 ≤ N → 1 + ((N : ℤ) - 1) ^ 2 < 4 * A →
      walkCount N A = 2 * ∑ u ∈ Finset.range (N + 1), summand N A u := by
    intro N A hN hA
    have mem_of : ∀ (w : Fin N → Step) (i : Fin N), w i ∈ List.ofFn w := by
      intro w i
      rw [List.mem_ofFn]
      exact ⟨i, rfl⟩
    have split_walks : walkCount N A =
        (Finset.univ.filter fun w : Fin N → Step =>
          area (List.ofFn w) = A ∧ ∀ i, w i = Step.right ∨ w i = Step.up).card +
        (Finset.univ.filter fun w : Fin N → Step =>
          area (List.ofFn w) = A ∧ ∀ i, w i = Step.left ∨ w i = Step.down).card := by
      unfold walkCount
      rw [← Finset.card_union_of_disjoint]
      · congr 1
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
        constructor
        · intro hw
          have hm := mono (List.ofFn w) (by rw [List.length_ofFn, hw]; exact hA)
          rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · left
            refine ⟨hw, fun i => ?_⟩
            have hi := mem_of w i
            cases h : w i
            · exact Or.inl rfl
            · rw [h] at hi; exact absurd hi h1
            · exact Or.inr rfl
            · rw [h] at hi; exact absurd hi h2
          · right
            refine ⟨hw, fun i => ?_⟩
            have hi := mem_of w i
            cases h : w i
            · rw [h] at hi; exact absurd hi h1
            · exact Or.inl rfl
            · rw [h] at hi; exact absurd hi h2
            · exact Or.inr rfl
        · rintro (⟨hw, _⟩ | ⟨hw, _⟩) <;> exact hw
      · rw [Finset.disjoint_filter]
        intro w _ h1 h2
        rcases h1.2 ⟨0, hN⟩ with h | h <;> rcases h2 with ⟨_, h2⟩ <;>
          rcases h2 ⟨0, hN⟩ with h' | h' <;> rw [h] at h' <;> exact Step.noConfusion h'
    have hflip : ∀ w : Fin N → Step, area (List.ofFn (flipStep ∘ w)) = area (List.ofFn w) := by
      intro w
      rw [← List.map_ofFn]
      unfold area
      have := area_flip (List.ofFn w) 0
      rw [neg_zero] at this
      exact this
    have hinv : ∀ s, flipStep (flipStep s) = s := by
      intro s
      cases s <;> rfl
    have flip_eq : (Finset.univ.filter fun w : Fin N → Step =>
          area (List.ofFn w) = A ∧ ∀ i, w i = Step.left ∨ w i = Step.down).card =
        (Finset.univ.filter fun w : Fin N → Step =>
          area (List.ofFn w) = A ∧ ∀ i, w i = Step.right ∨ w i = Step.up).card := by
      refine Finset.card_bij' (fun w _ => flipStep ∘ w) (fun w _ => flipStep ∘ w) ?_ ?_ ?_ ?_
      · intro w hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        refine ⟨by rw [hflip]; exact hw.1, fun i => ?_⟩
        rcases hw.2 i with h | h <;> simp [h, flipStep]
      · intro w hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        refine ⟨by rw [hflip]; exact hw.1, fun i => ?_⟩
        rcases hw.2 i with h | h <;> simp [h, flipStep]
      · intro w _
        funext i
        simp [hinv]
      · intro w _
        funext i
        simp [hinv]
    have ur_eq : (Finset.univ.filter fun w : Fin N → Step =>
          area (List.ofFn w) = A ∧ ∀ i, w i = Step.right ∨ w i = Step.up).card =
        (Finset.univ.filter fun b : Fin N → Bool => area (List.ofFn (toStep ∘ b)) = A).card := by
      refine Finset.card_bij' (fun w _ => fun i => decide (w i = Step.up))
        (fun b _ => toStep ∘ b) ?_ ?_ ?_ ?_
      · intro w hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        have : (toStep ∘ fun i => decide (w i = Step.up)) = w := by
          funext i
          rcases hw.2 i with h | h <;> simp [h, toStep]
        rw [this]
        exact hw.1
      · intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        refine ⟨hb, fun i => ?_⟩
        cases h : b i <;> simp [h, toStep]
      · intro w hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
        funext i
        rcases hw.2 i with h | h <;> simp [h, toStep]
      · intro b _
        funext i
        cases h : b i <;> simp [h, toStep]
    have key : ∀ b : Fin N → Bool, area (List.ofFn (toStep ∘ b)) +
        ListInversions.inv ((List.ofFn b).map fun x => (!x).toNat) =
        ((List.ofFn b).count true : ℤ) * ((N : ℤ) - (List.ofFn b).count true) := by
      intro b
      have h1 := area_bool (List.ofFn b) 0
      have h2 := List.count_true_add_count_false (List.ofFn b)
      rw [List.length_ofFn] at h2
      have h3 : ((List.ofFn b).count false : ℤ) = N - (List.ofFn b).count true := by
        omega
      rw [zero_add, h3] at h1
      rw [← List.map_ofFn]
      exact h1
    have bool_sum : (Finset.univ.filter fun b : Fin N → Bool =>
        area (List.ofFn (toStep ∘ b)) = A).card = ∑ u ∈ Finset.range (N + 1), summand N A u := by
      rw [Finset.card_eq_sum_card_fiberwise
        (f := fun b : Fin N → Bool => (List.ofFn b).count true) (t := Finset.range (N + 1))]
      · apply Finset.sum_congr rfl
        intro u _
        rw [Finset.filter_filter]
        unfold summand
        split_ifs with he
        · unfold wordCount
          congr 1
          apply Finset.filter_congr
          intro b _
          have hk := key b
          constructor
          · rintro ⟨h1, h2⟩
            refine ⟨h2, ?_⟩
            rw [h2, h1] at hk
            generalize (u : ℤ) * ((N : ℤ) - u) = P at hk he
            omega
          · rintro ⟨h1, h2⟩
            refine ⟨?_, h1⟩
            rw [h1, h2] at hk
            generalize (u : ℤ) * ((N : ℤ) - u) = P at hk he
            omega
        · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro b _ hb
          have hk := key b
          rw [hb.1, hb.2] at hk
          generalize (u : ℤ) * ((N : ℤ) - u) = P at hk he
          omega
      · intro b _
        have := List.count_le_length (a := true) (l := List.ofFn b)
        rw [List.length_ofFn] at this
        exact Finset.mem_coe.2 (Finset.mem_range.2 (Nat.lt_succ_of_le this))
    rw [split_walks, flip_eq, ur_eq, bool_sum]
    ring
  -- evaluating a summand
  have summand_eval : ∀ (N : ℕ) (A : ℤ) (u m : ℕ), (u : ℤ) * (N - u) - A = m → u + m ≤ N →
      m ≤ u → summand N A u = partitionCount m := by
    intro N A u m he h1 h2
    unfold summand
    rw [he, if_pos (Nat.cast_nonneg m), Int.toNat_natCast]
    exact core N u m h1 h2
  have summand_zero : ∀ (N : ℕ) (A : ℤ) (u : ℕ), (u : ℤ) * (N - u) - A < 0 →
      summand N A u = 0 := by
    intro N A u he
    unfold summand
    rw [if_neg (not_le.2 he)]
  intro n k hk
  have hn : 1 ≤ n := by omega
  constructor
  · -- even length
    have hA : 1 + (((2 * n : ℕ) : ℤ) - 1) ^ 2 < 4 * ((n : ℤ) ^ 2 - k) := by
      push_cast
      have : (k : ℤ) + 1 ≤ n := by exact_mod_cast hk
      nlinarith
    rw [reduce (2 * n) _ (by omega) hA]
    congr 1
    let h : ℕ → ℕ := fun j => if j ^ 2 ≤ k then partitionCount (k - j ^ 2) else 0
    have right_half : ∀ x ∈ Finset.range (n + 1),
        summand (2 * n) ((n : ℤ) ^ 2 - k) (n + x) = h x := by
      intro x hx
      rw [Finset.mem_range] at hx
      simp only [h]
      split_ifs with hxk
      · obtain ⟨m, rfl⟩ : ∃ m, k = m + x ^ 2 := ⟨k - x ^ 2, (Nat.sub_add_cancel hxk).symm⟩
        rw [Nat.add_sub_cancel]
        have hx2 : x ≤ x ^ 2 + 1 := by nlinarith
        apply summand_eval _ _ _ m
        · push_cast
          ring
        · generalize x ^ 2 = X at *
          omega
        · generalize x ^ 2 = X at *
          omega
      · apply summand_zero
        push_cast
        have : (k : ℤ) < (x : ℤ) ^ 2 := by exact_mod_cast not_le.1 hxk
        nlinarith
    have left_half : ∀ x ∈ Finset.range n,
        summand (2 * n) ((n : ℤ) ^ 2 - k) (n - 1 - x) = h (x + 1) := by
      intro x hx
      rw [Finset.mem_range] at hx
      simp only [h]
      have hcast : ((n - 1 - x : ℕ) : ℤ) = n - 1 - x := by omega
      split_ifs with hxk
      · obtain ⟨m, rfl⟩ : ∃ m, k = m + (x + 1) ^ 2 :=
          ⟨k - (x + 1) ^ 2, (Nat.sub_add_cancel hxk).symm⟩
        rw [Nat.add_sub_cancel]
        have hx2 : x + 1 ≤ (x + 1) ^ 2 := by nlinarith
        apply summand_eval _ _ _ m
        · push_cast [hcast]
          ring
        · generalize (x + 1) ^ 2 = X at *
          omega
        · generalize (x + 1) ^ 2 = X at *
          omega
      · apply summand_zero
        push_cast [hcast]
        have : (k : ℤ) < ((x : ℤ) + 1) ^ 2 := by exact_mod_cast not_le.1 hxk
        nlinarith
    rw [show 2 * n + 1 = n + (n + 1) by ring, Finset.sum_range_add,
      ← Finset.sum_range_reflect, Finset.sum_congr rfl left_half, Finset.sum_congr rfl right_half,
      Finset.sum_range_succ' h]
    unfold a029552
    rw [Finset.sum_filter]
    have tail : ∑ x ∈ Finset.range n, h (x + 1) =
        ∑ j ∈ Finset.Icc 1 k, if j ^ 2 ≤ k then partitionCount (k - j ^ 2) else 0 := by
      have hsub : Finset.Icc 1 k ⊆ Finset.Ico 1 (n + 1) := by
        intro j hj
        simp only [Finset.mem_Icc, Finset.mem_Ico] at hj ⊢
        omega
      rw [Finset.sum_subset hsub, Finset.sum_Ico_eq_sum_range]
      · apply Finset.sum_congr rfl
        intro x _
        simp only [h, add_comm 1 x]
      · intro j hj hj'
        simp only [Finset.mem_Icc, Finset.mem_Ico, not_and, not_le] at hj hj'
        have hkj : k < j := hj' hj.1
        have : k < j ^ 2 := by nlinarith
        simp [not_le.2 this]
    rw [tail]
    simp only [h, Nat.zero_pow two_pos, Nat.zero_le, if_true, Nat.sub_zero]
    ring
  · -- odd length
    have hA : 1 + (((2 * n + 1 : ℕ) : ℤ) - 1) ^ 2 < 4 * ((n : ℤ) ^ 2 + n - k) := by
      push_cast
      have : (k : ℤ) + 1 ≤ n := by exact_mod_cast hk
      nlinarith
    rw [reduce (2 * n + 1) _ (by omega) hA]
    let h : ℕ → ℕ := fun x => if x * (x + 1) ≤ k then partitionCount (k - x * (x + 1)) else 0
    have right_half : ∀ x ∈ Finset.range (n + 1),
        summand (2 * n + 1) ((n : ℤ) ^ 2 + n - k) (n + 1 + x) = h x := by
      intro x hx
      rw [Finset.mem_range] at hx
      simp only [h]
      split_ifs with hxk
      · obtain ⟨m, rfl⟩ : ∃ m, k = m + x * (x + 1) :=
          ⟨k - x * (x + 1), (Nat.sub_add_cancel hxk).symm⟩
        rw [Nat.add_sub_cancel]
        have hx2 : x ≤ x * (x + 1) := by nlinarith
        apply summand_eval _ _ _ m
        · push_cast
          ring
        · generalize x * (x + 1) = X at *
          omega
        · generalize x * (x + 1) = X at *
          omega
      · apply summand_zero
        push_cast
        have : (k : ℤ) < (x : ℤ) * (x + 1) := by exact_mod_cast not_le.1 hxk
        nlinarith
    have left_half : ∀ x ∈ Finset.range (n + 1),
        summand (2 * n + 1) ((n : ℤ) ^ 2 + n - k) (n + 1 - 1 - x) = h x := by
      intro x hx
      rw [Finset.mem_range] at hx
      rw [show n + 1 - 1 - x = n - x by omega]
      simp only [h]
      have hcast : ((n - x : ℕ) : ℤ) = n - x := by omega
      split_ifs with hxk
      · obtain ⟨m, rfl⟩ : ∃ m, k = m + x * (x + 1) :=
          ⟨k - x * (x + 1), (Nat.sub_add_cancel hxk).symm⟩
        rw [show m + x * (x + 1) - x * (x + 1) = m from Nat.add_sub_cancel m _]
        have hx2 : x ≤ x * (x + 1) := by nlinarith
        apply summand_eval _ _ _ m
        · push_cast [hcast]
          ring
        · generalize x * (x + 1) = X at *
          omega
        · generalize x * (x + 1) = X at *
          omega
      · apply summand_zero
        push_cast [hcast]
        have : (k : ℤ) < (x : ℤ) * (x + 1) := by exact_mod_cast not_le.1 hxk
        nlinarith
    rw [show 2 * n + 1 + 1 = (n + 1) + (n + 1) by ring, Finset.sum_range_add,
      ← Finset.sum_range_reflect, Finset.sum_congr rfl left_half, Finset.sum_congr rfl right_half]
    have total : ∑ x ∈ Finset.range (n + 1), h x = a098613 k := by
      unfold a098613
      rw [Finset.sum_filter]
      rw [← Finset.sum_subset (s₁ := Finset.range (k + 1)) (s₂ := Finset.range (n + 1))]
      · rw [show Finset.Icc 1 (k + 1) = Finset.Ico 1 (k + 2) by
          ext x
          simp only [Finset.mem_Icc, Finset.mem_Ico]
          omega, Finset.sum_Ico_eq_sum_range]
        apply Finset.sum_congr rfl
        intro x _
        have hsq : (1 + x) ^ 2 - (1 + x) = x * (x + 1) := by
          rw [Nat.sub_eq_iff_eq_add (by nlinarith)]
          ring
        simp only [h, hsq]
      · intro x hx
        simp only [Finset.mem_range] at hx ⊢
        omega
      · intro x hx hx'
        simp only [Finset.mem_range, not_lt] at hx hx'
        have : k < x * (x + 1) := by nlinarith
        simp [h, not_le.2 this]
    rw [total]
    ring

end D5.S3.Combinatorics.LatticeWalkNearMaximalArea
