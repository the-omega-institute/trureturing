/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The common six-lag recurrence for Hardin's rectangular arrays. -/

/-
result: proof_shape: content
fin_constant: proof_shape=bind-only; consumers=mixed_uniform
escape_witness: low_count counts sum-two rectangles by independent row fibers
  alternating between a first-row edge-sum profile and its complement.
admission_basis: open-problem-resolution (#34236; Proved)
Direct frozen dependencies: none.
-/

import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Hardin's common row and column recurrence for literal constant-stress arrays. -/

namespace D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Recurrence
open scoped BigOperators
noncomputable section

abbrev Grid (n k : ℕ) := Fin (n + 1) → Fin (k + 1) → Fin 4

/-- The literal contiguous block condition over the four-element alphabet. -/
def Legal {n k : ℕ} (a : Grid n k) : Prop :=
  ∀ (i : Fin n) (j : Fin k),
    Int.natAbs (((a i.castSucc j.castSucc).val : ℤ) + ((a i.succ j.succ).val : ℤ) -
      (((a i.castSucc j.succ).val : ℤ) + ((a i.succ j.castSucc).val : ℤ))) = 4

/-- The published integer-valued count, with n+1 rows and k+1 columns. -/
def T (n k : ℕ) : ℤ := Nat.card {a : Grid n k // Legal a}

private def block {n k : ℕ} (a : Grid n k) (i : Fin n) (j : Fin k) : ℕ :=
  (a i.castSucc j.castSucc).val + (a i.castSucc j.succ).val +
    (a i.succ j.castSucc).val + (a i.succ j.succ).val

private def Mixed {n k : ℕ} (a : Grid n k) : Prop :=
  ∀ i j, block a i j = 2 ∨ block a i j = 10

private def Low {n k : ℕ} (a : Grid n k) : Prop := ∀ i j, block a i j = 2
private def High {n k : ℕ} (a : Grid n k) : Prop := ∀ i j, block a i j = 10

private def checker {n k : ℕ} (a : Grid n k) : Grid n k :=
  fun i j => if (i.val + j.val) % 2 = 0 then (a i j).rev else a i j

private theorem checker_involutive {n k : ℕ} (a : Grid n k) : checker (checker a) = a := by
  funext i j
  by_cases h : (i.val + j.val) % 2 = 0 <;> simp [checker, h]

private theorem checker_iff {n k : ℕ} (a : Grid n k) : Legal a ↔ Mixed (checker a) := by
  unfold Legal Mixed
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Int.natAbs_eq_iff]
  simp only [block, checker, Fin.val_castSucc, Fin.val_succ]
  have ha := (a i.castSucc j.castSucc).isLt
  have hb := (a i.castSucc j.succ).isLt
  have hc := (a i.succ j.castSucc).isLt
  have hd := (a i.succ j.succ).isLt
  by_cases h : (i.val + j.val) % 2 = 0
  · have h1 : (i.val + (j.val + 1)) % 2 ≠ 0 := by omega
    have h2 : (i.val + 1 + j.val) % 2 ≠ 0 := by omega
    have h3 : (i.val + 1 + (j.val + 1)) % 2 = 0 := by omega
    simp only [h, h1, h2, h3, ite_true, ite_false, Fin.val_rev]
    omega
  · have h1 : (i.val + (j.val + 1)) % 2 = 0 := by omega
    have h2 : (i.val + 1 + j.val) % 2 = 0 := by omega
    have h3 : (i.val + 1 + (j.val + 1)) % 2 ≠ 0 := by omega
    simp only [h, h1, h2, h3, ite_true, ite_false, Fin.val_rev]
    omega

private def checkerEquiv (n k : ℕ) : {a : Grid n k // Legal a} ≃ {a : Grid n k // Mixed a} where
  toFun a := ⟨checker a.1, (checker_iff a.1).mp a.2⟩
  invFun a := ⟨checker a.1, (checker_iff (checker a.1)).mpr (by rw [checker_involutive]; exact a.2)⟩
  left_inv a := Subtype.ext (checker_involutive a.1)
  right_inv a := Subtype.ext (checker_involutive a.1)

theorem fin_constant {n : ℕ} {α : Type} (f : Fin (n + 1) → α)
    (adj : ∀ i : Fin n, f i.castSucc = f i.succ) (i : Fin (n + 1)) : f i = f 0 := by
  by_cases hi : i = 0
  · subst i
    rfl
  · have h : f 0 = f i :=
      (Fin.liftFun_iff_succ (Eq : α → α → Prop) (f := f)).2 adj (Fin.pos_iff_ne_zero.mpr hi)
    exact h.symm

private theorem block_vertical {n k : ℕ} {a : Grid (n + 1) k} (h : Mixed a)
    (i : Fin n) (j : Fin k) : block a i.castSucc j = block a i.succ j := by
  have h1 := h i.castSucc j
  have h2 := h i.succ j
  have e : i.castSucc.succ = i.succ.castSucc := Fin.ext rfl
  have ha := (a i.castSucc.castSucc j.castSucc).isLt
  have hb := (a i.castSucc.castSucc j.succ).isLt
  have hc := (a i.succ.succ j.castSucc).isLt
  have hd := (a i.succ.succ j.succ).isLt
  simp only [block, e] at *
  omega

private theorem block_horizontal {n k : ℕ} {a : Grid n (k + 1)} (h : Mixed a)
    (i : Fin n) (j : Fin k) : block a i j.castSucc = block a i j.succ := by
  have h1 := h i j.castSucc
  have h2 := h i j.succ
  have e : j.castSucc.succ = j.succ.castSucc := Fin.ext rfl
  have ha := (a i.castSucc j.castSucc.castSucc).isLt
  have hb := (a i.succ j.castSucc.castSucc).isLt
  have hc := (a i.castSucc j.succ.succ).isLt
  have hd := (a i.succ j.succ.succ).isLt
  simp only [block, e] at *
  omega

/-- Shared edges force all blocks to have the same sum. -/
private theorem mixed_uniform {n k : ℕ} (a : Grid (n + 1) (k + 1)) (h : Mixed a) :
    Low a ∨ High a := by
  have eq (i : Fin (n + 1)) (j : Fin (k + 1)) :
      block a i j = block a 0 0 := by
    calc
      _ = block a 0 j := fin_constant (fun i => block a i j) (fun i => block_vertical h i j) i
      _ = _ := fin_constant (block a 0) (block_horizontal h 0) j
  rcases h 0 0 with h0 | h0
  · exact Or.inl fun i j => (eq i j).trans h0
  · exact Or.inr fun i j => (eq i j).trans h0

private def complement {n k : ℕ} (a : Grid n k) : Grid n k := fun i j => (a i j).rev

private theorem complement_involutive {n k : ℕ} (a : Grid n k) :
    complement (complement a) = a := by
  funext i j
  simp [complement]

private theorem complement_block {n k : ℕ} (a : Grid n k) (i : Fin n) (j : Fin k) :
    block (complement a) i j + block a i j = 12 := by
  have ha := (a i.castSucc j.castSucc).isLt
  have hb := (a i.castSucc j.succ).isLt
  have hc := (a i.succ j.castSucc).isLt
  have hd := (a i.succ j.succ).isLt
  simp only [block, complement, Fin.val_rev]
  omega

private def complementEquiv (n k : ℕ) :
    {a : Grid n k // Low a} ≃ {a : Grid n k // High a} where
  toFun a := ⟨complement a.1, fun i j => by
    have h := complement_block a.1 i j
    have h' := a.2 i j
    omega⟩
  invFun a := ⟨complement a.1, fun i j => by
    have h := complement_block a.1 i j
    have h' := a.2 i j
    omega⟩
  left_inv a := Subtype.ext (complement_involutive a.1)
  right_inv a := Subtype.ext (complement_involutive a.1)

private def mixedEquiv (n k : ℕ) : {a : Grid (n + 1) (k + 1) // Mixed a} ≃
    ({a : Grid (n + 1) (k + 1) // Low a} ⊕ {a : Grid (n + 1) (k + 1) // High a}) := by
  classical
  refine {
    toFun := fun a => if h : Low a.1 then Sum.inl ⟨a.1, h⟩
      else Sum.inr ⟨a.1, (mixed_uniform a.1 a.2).resolve_left h⟩
    invFun := fun a => match a with
      | .inl l => ⟨l.1, fun i j => Or.inl (l.2 i j)⟩
      | .inr r => ⟨r.1, fun i j => Or.inr (r.2 i j)⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro a
    by_cases h : Low a.1 <;> simp [h]
  · intro a
    cases a with
    | inl l => simp [l.2]
    | inr r =>
      have h : ¬ Low r.1 := by
        intro hl
        have h1 := hl 0 0
        have h2 := r.2 0 0
        omega
      simp [h]

/-- The checkerboard transform and global complement give the exact count. -/
theorem original_eq_twice_low (n k : ℕ) :
    T (n + 1) (k + 1) = 2 * (Nat.card {a : Grid (n + 1) (k + 1) // Low a} : ℤ) := by
  unfold T
  rw [Nat.card_congr (checkerEquiv _ _), Nat.card_congr (mixedEquiv _ _), Nat.card_sum,
    ← Nat.card_congr (complementEquiv (n + 1) (k + 1))]
  push_cast
  ring

private abbrev Row (k : ℕ) := Fin (k + 1) → Fin 4
abbrev Profile (k : ℕ) := Fin k → Fin 3

def edge {k : ℕ} (r : Row k) (j : Fin k) : ℕ :=
  (r j.castSucc).val + (r j.succ).val

def Fiber {k : ℕ} (p : Profile k) := {r : Row k // ∀ j, edge r j = (p j).val}

private instance {k : ℕ} (p : Profile k) : Finite (Fiber p) := by
  unfold Fiber
  infer_instance

def flip {k : ℕ} (p : Profile k) : Profile k := fun j => (p j).rev

private def profileAt {k : ℕ} (p : Profile k) (i : ℕ) : Profile k :=
  if i % 2 = 0 then p else flip p

@[local simp] private theorem profileAt_zero {k : ℕ} (p : Profile k) : profileAt p 0 = p := by
  simp [profileAt]

@[local simp] private theorem profileAt_one {k : ℕ} (p : Profile k) : profileAt p 1 = flip p := by
  simp [profileAt]

private theorem profileAt_add_two {k : ℕ} (p : Profile k) (i : ℕ) :
    profileAt p (i + 2) = profileAt p i := by
  unfold profileAt
  have e : (i + 2) % 2 = i % 2 := by omega
  rw [e]

private theorem profileAt_adj {k : ℕ} (p : Profile k) (i : ℕ) (j : Fin k) :
    (profileAt p i j).val + (profileAt p (i + 1) j).val = 2 := by
  have hj := (p j).isLt
  by_cases h : i % 2 = 0
  · have h' : (i + 1) % 2 ≠ 0 := by omega
    simp only [profileAt, h, h', ite_true, ite_false, flip, Fin.val_rev]
    omega
  · have h' : (i + 1) % 2 = 0 := by omega
    simp only [profileAt, h, h', ite_true, ite_false, flip, Fin.val_rev]
    omega

private theorem low_edges {n k : ℕ} {a : Grid n k} (h : Low a) (i : Fin n) (j : Fin k) :
    edge (a i.castSucc) j + edge (a i.succ) j = 2 := by
  simpa only [edge, block, Nat.add_assoc] using h i j

private def firstProfile {n k : ℕ} (a : {a : Grid (n + 1) k // Low a}) : Profile k :=
  fun j => ⟨edge (a.1 0) j, by
    have h := low_edges a.2 0 j
    have e : (0 : Fin (n + 1)).castSucc = 0 := rfl
    rw [e] at h
    omega⟩

private theorem low_profiles {n k : ℕ} (a : {a : Grid (n + 1) k // Low a})
    (i : Fin (n + 2)) (j : Fin k) :
    edge (a.1 i) j = (profileAt (firstProfile a) i.val j).val := by
  induction i using Fin.induction with
  | zero => simp [firstProfile]
  | succ i ih =>
    have h := low_edges a.2 i j
    have h' := profileAt_adj (firstProfile a) i.val j
    have e1 : i.castSucc.val = i.val := rfl
    have e2 : i.succ.val = i.val + 1 := rfl
    rw [e1] at ih
    rw [e2]
    omega

private abbrev AltRows {k : ℕ} (p : Profile k) (h : ℕ) :=
  (i : Fin h) → Fiber (profileAt p i.val)

private def rowsToLow (n k : ℕ) (s : Σ p : Profile k, AltRows p (n + 2)) :
    {a : Grid (n + 1) k // Low a} :=
  ⟨fun i => (s.2 i).1, fun i j => by
    have h1 := (s.2 i.castSucc).2 j
    have h2 := (s.2 i.succ).2 j
    have h := profileAt_adj s.1 i.val j
    simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
    simp only [block, edge] at *
    omega⟩

private theorem rowsToLow_first (n k : ℕ) (s : Σ p : Profile k, AltRows p (n + 2)) :
    firstProfile (rowsToLow n k s) = s.1 := by
  funext j
  apply Fin.ext
  change edge ((s.2 0).1) j = (s.1 j).val
  simpa only [Fin.val_zero, profileAt_zero] using (s.2 0).2 j

private theorem rowsToLow_injective (n k : ℕ) : Function.Injective (rowsToLow n k) := by
  rintro ⟨p, f⟩ ⟨q, g⟩ h
  have hp := congrArg firstProfile h
  rw [rowsToLow_first, rowsToLow_first] at hp
  change p = q at hp
  subst q
  congr 1
  funext i
  apply Subtype.ext
  exact congrFun (congrArg Subtype.val h) i

private theorem rowsToLow_surjective (n k : ℕ) : Function.Surjective (rowsToLow n k) := by
  intro a
  exact ⟨⟨firstProfile a, fun i => ⟨a.1 i, low_profiles a i⟩⟩, Subtype.ext rfl⟩

private def lowEquiv (n k : ℕ) :
    (Σ p : Profile k, AltRows p (n + 2)) ≃ {a : Grid (n + 1) k // Low a} :=
  Equiv.ofBijective (rowsToLow n k) ⟨rowsToLow_injective n k, rowsToLow_surjective n k⟩

def b {k : ℕ} (p : Profile k) : ℕ := Nat.card (Fiber p)

def profileCount {k : ℕ} (p : Profile k) (h : ℕ) : ℕ :=
  ∏ i : Fin h, b (profileAt p i.val)

private theorem card_altRows {k : ℕ} (p : Profile k) (h : ℕ) :
    Nat.card (AltRows p h) = profileCount p h := by
  rw [Nat.card_pi]
  rfl

/-- The low-array count is the sum of the alternating row-profile counts. -/
private theorem low_count (n k : ℕ) :
    Nat.card {a : Grid (n + 1) k // Low a} =
      ∑ p : Profile k, profileCount p (n + 2) := by
  rw [← Nat.card_congr (lowEquiv n k), Nat.card_sigma]
  simp_rw [card_altRows]

/-- The initial cell uniquely determines a row with prescribed edge sums. -/
private theorem fiber_bound {k : ℕ} (p : Profile (k + 1)) :
    b p ≤ (p 0).val + 1 := by
  let f (r : Fiber p) : Fin ((p 0).val + 1) :=
    ⟨(r.1 0).val, by
      have h := r.2 0
      change (r.1 (0 : Fin (k + 1)).castSucc).val +
        (r.1 (0 : Fin (k + 1)).succ).val = (p 0).val at h
      have e : (0 : Fin (k + 1)).castSucc = 0 := rfl
      rw [e] at h
      omega⟩
  have hf : Function.Injective f := by
    intro r s h
    apply Subtype.ext
    funext i
    apply Fin.ext
    induction i using Fin.induction with
    | zero => exact congrArg (fun x : Fin ((p 0).val + 1) => x.val) h
    | succ i ih =>
      have h1 := r.2 i
      have h2 := s.2 i
      change (r.1 i.castSucc).val + (r.1 i.succ).val = (p i).val at h1
      change (s.1 i.castSucc).val + (s.1 i.succ).val = (p i).val at h2
      omega
  have hb := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_fin] at hb

private theorem pair_bound {k : ℕ} (p : Profile (k + 1)) :
    b p + b (flip p) ≤ 4 := by
  have h1 := fiber_bound p
  have h2 := fiber_bound (flip p)
  have h3 := (p 0).isLt
  simp only [flip, Fin.val_rev] at h2
  omega

theorem profileCount_two_step {k : ℕ} (p : Profile k) (h : ℕ) :
    profileCount p (h + 2) = b p * b (flip p) * profileCount p h := by
  unfold profileCount
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, profileAt_zero, profileAt_add_two]
  rw [profileAt_one]
  ring

theorem profileCount_eq_pow {k : ℕ} (p : Profile k) (c : ℕ)
    (h1 : b p = c) (h2 : b (flip p) = c) (h : ℕ) :
    profileCount p h = c ^ h := by
  unfold profileCount
  have he (i : Fin h) : b (profileAt p i.val) = c := by
    unfold profileAt
    split <;> assumption
  simp_rw [he]
  simp

private def Six (f : ℕ → ℤ) (n : ℕ) : Prop :=
  f (n + 6) = 3 * f (n + 5) + 3 * f (n + 4) - 15 * f (n + 3) +
    4 * f (n + 2) + 18 * f (n + 1) - 12 * f n

private theorem first_step_six (f : ℕ → ℤ) (c : ℤ)
    (hc : c = 1 ∨ c = 2) (step : ∀ n, f (n + 1) = c * f n) (n : ℕ) :
    Six f n := by
  unfold Six
  have h0 : f (n + 1) = c * f n := step n
  have h1 : f (n + 2) = c * f (n + 1) := step (n + 1)
  have h2 : f (n + 3) = c * f (n + 2) := step (n + 2)
  have h3 : f (n + 4) = c * f (n + 3) := step (n + 3)
  have h4 : f (n + 5) = c * f (n + 4) := step (n + 4)
  have h5 : f (n + 6) = c * f (n + 5) := step (n + 5)
  rcases hc with h | h <;> subst c <;> omega

private theorem two_step_six (f : ℕ → ℤ) (c : ℤ)
    (hc : c = 2 ∨ c = 3) (step : ∀ n, f (n + 2) = c * f n) (n : ℕ) :
    Six f n := by
  unfold Six
  have h0 : f (n + 2) = c * f n := step n
  have h1 : f (n + 3) = c * f (n + 1) := step (n + 1)
  have h2 : f (n + 4) = c * f (n + 2) := step (n + 2)
  have h3 : f (n + 5) = c * f (n + 3) := step (n + 3)
  have h4 : f (n + 6) = c * f (n + 4) := step (n + 4)
  rcases hc with h | h <;> subst c <;> omega

/-- A nonzero alternating pair has first-order ratio 1 or 2, or two-step ratio 2 or 3. -/
private theorem pair_cases (a d : ℕ) (h : a + d ≤ 4) :
    a * d = 0 ∨ (a = 1 ∧ d = 1) ∨ a * d = 2 ∨ a * d = 3 ∨ (a = 2 ∧ d = 2) := by
  have ha : a ≤ 4 := by omega
  have hd : d ≤ 4 := by omega
  interval_cases a <;> interval_cases d <;> norm_num at *

private theorem profile_six {k : ℕ} (p : Profile (k + 1)) (n : ℕ) :
    Six (fun h => (profileCount p h : ℤ)) (n + 2) := by
  rcases pair_cases _ _ (pair_bound p) with h | ⟨h1, h2⟩ | h | h | ⟨h1, h2⟩
  · have hz (m : ℕ) : profileCount p (m + 2) = 0 := by
      rw [profileCount_two_step, h, zero_mul]
    unfold Six
    simp only [hz, Nat.cast_zero, mul_zero, add_zero, sub_zero]
  · apply first_step_six _ 1 (Or.inl rfl)
    intro m
    simp [profileCount_eq_pow p 1 h1 h2]
  · apply two_step_six _ 2 (Or.inl rfl)
    intro m
    rw [profileCount_two_step, h]
    push_cast
    rfl
  · apply two_step_six _ 3 (Or.inr rfl)
    intro m
    rw [profileCount_two_step, h]
    push_cast
    rfl
  · apply first_step_six _ 2 (Or.inr rfl)
    intro m
    simp [profileCount_eq_pow p 2 h1 h2, pow_succ, mul_comm]

theorem literal_sum (n k : ℕ) :
    T (n + 1) (k + 1) = ∑ p : Profile (k + 1), 2 * (profileCount p (n + 2) : ℤ) := by
  rw [original_eq_twice_low, low_count]
  push_cast
  rw [Finset.mul_sum]

private theorem six_sum {α : Type} [Fintype α] (f : α → ℕ → ℤ) (n : ℕ)
    (h : ∀ a, Six (f a) n) :
    Six (fun m => ∑ a, f a m) n := by
  unfold Six at *
  simp only
  calc
    _ = ∑ a, (3 * f a (n + 5) + 3 * f a (n + 4) - 15 * f a (n + 3) +
        4 * f a (n + 2) + 18 * f a (n + 1) - 12 * f a n) :=
      Finset.sum_congr rfl (fun a _ => h a)
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]

private theorem first_axis_shifted (n k : ℕ) : Six (fun m => T (m + 1) (k + 1)) n := by
  have h (p : Profile (k + 1)) : Six (fun m => 2 * (profileCount p (m + 2) : ℤ)) n := by
    have hp := profile_six p n
    unfold Six at hp ⊢
    dsimp at hp ⊢
    linear_combination 2 * hp
  have hsum := six_sum (fun p m => 2 * (profileCount p (m + 2) : ℤ)) n h
  unfold Six at hsum ⊢
  simpa only [literal_sum] using hsum

private def transpose {n k : ℕ} (a : Grid n k) : Grid k n := fun i j => a j i

private theorem transpose_legal {n k : ℕ} (a : Grid n k) : Legal (transpose a) ↔ Legal a := by
  constructor <;> intro h i j
  · have hh := h j i
    simpa only [transpose, add_comm] using hh
  · have hh := h j i
    simpa only [transpose, add_comm] using hh

private def transposeEquiv (n k : ℕ) : {a : Grid n k // Legal a} ≃ {a : Grid k n // Legal a} where
  toFun a := ⟨transpose a.1, (transpose_legal a.1).mpr a.2⟩
  invFun a := ⟨transpose a.1, (transpose_legal a.1).mpr a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem T_transpose (n k : ℕ) : T n k = T k n := by
  unfold T
  rw [Nat.card_congr (transposeEquiv n k)]

private theorem first_axis (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    T (n + 6) k = 3 * T (n + 5) k + 3 * T (n + 4) k - 15 * T (n + 3) k +
      4 * T (n + 2) k + 18 * T (n + 1) k - 12 * T n k := by
  cases n with
  | zero => omega
  | succ n =>
    cases k with
    | zero => omega
    | succ k => exact first_axis_shifted n k

private theorem second_axis (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    T n (k + 6) = 3 * T n (k + 5) + 3 * T n (k + 4) - 15 * T n (k + 3) +
      4 * T n (k + 2) + 18 * T n (k + 1) - 12 * T n k := by
  have h := first_axis k n hk hn
  simp_rw [show ∀ m, T m n = T n m from fun m => T_transpose m n] at h
  exact h

/-- The six-lag recurrence for either dimension of the literal rectangular count. -/
theorem result (d : ℕ × ℕ) (hn : 0 < d.1) (hk : 0 < d.2) :
    (T (d.1 + 6) d.2 = 3 * T (d.1 + 5) d.2 + 3 * T (d.1 + 4) d.2 -
      15 * T (d.1 + 3) d.2 + 4 * T (d.1 + 2) d.2 + 18 * T (d.1 + 1) d.2 -
      12 * T d.1 d.2) ∧
    (T d.1 (d.2 + 6) = 3 * T d.1 (d.2 + 5) + 3 * T d.1 (d.2 + 4) -
      15 * T d.1 (d.2 + 3) + 4 * T d.1 (d.2 + 2) + 18 * T d.1 (d.2 + 1) -
      12 * T d.1 d.2) :=
  ⟨first_axis d.1 d.2 hn hk, second_axis d.1 d.2 hn hk⟩

end

end D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Recurrence
