/- GID: D5/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/LongRangeSwap/LeeCollisionExit
   mirror-E: none(waiver:abstract-matrix-family)
   anchors: []
   utility: none
   digest: Collision ranks give uniformly bounded positive-weight exits. -/

/-
proof_shape: Path.exits: content.
proof_shape of calB_mulVec and calBprime_mulVec: bind-only; consumer lifted_harmonic.
proof_shape of weights_nonneg_sum: bind-only; consumer harmonic_chain_zero.
Those consumers belong to LeeReductionInvertibility.
escape_witness of calB_mulVec, calBprime_mulVec and weights_nonneg_sum: none.
Private helper exits_with_rank_bound: content.
All other private helpers: bind-only, with consumers on Path.exits or the row-action path.
escape_witness: Path.exits, via the strictly decreasing collision rank Path.rank_decreases.
admission_basis: escape-witness
Direct frozen dependencies: none (pinned Mathlib only).
Information-escape registration is paused under CLAUDE.md §3.9.
Utility: none; all parameters are arbitrary, with no finite-instance certificate or enumeration.
-/

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace D5.S3.StatisticalMechanics.LongRangeSwap.LeeCollisionExit
open Matrix
noncomputable section
variable {N n : ℕ}

def B {N : ℕ} (μ : Fin N → ℝ) : Matrix (Fin N × Fin N) (Fin N × Fin N) ℝ :=
  fun π ν => if π = ν ∧ ν.1 = ν.2 then μ ν.1
    else if π.1 = ν.2 ∧ π.2 = ν.1 ∧ ν.1 < ν.2 then 1 else 0

def Bprime {N : ℕ} (μ : Fin N → ℝ) : Matrix (Fin N × Fin N) (Fin N × Fin N) ℝ :=
  fun π ν => if π = ν ∧ ν.1 = ν.2 then 1 - μ ν.1
    else if π.1 = ν.2 ∧ π.2 = ν.1 ∧ ν.2 < ν.1 then 1 else 0

def adjacent {N n : ℕ} (M : Matrix (Fin N × Fin N) (Fin N × Fin N) ℝ)
    (s : ℕ) : Matrix (Fin n → Fin N) (Fin n → Fin N) ℝ := fun π ν =>
  if h : s + 1 < n then
    M (π ⟨s, by omega⟩, π ⟨s + 1, h⟩) (ν ⟨s, by omega⟩, ν ⟨s + 1, h⟩) *
    ∏ r : Fin n, if r.val = s ∨ r.val = s + 1 then 1 else if π r = ν r then 1 else 0
  else 0

def calB {N n : ℕ} (μ : Fin N → ℝ) (j i : ℕ) : Matrix (Fin n → Fin N) (Fin n → Fin N) ℝ :=
  adjacent (B μ) (j + i - 2)

def calBprime {N n : ℕ} (μ : Fin N → ℝ) (j i : ℕ) : Matrix (Fin n → Fin N) (Fin n → Fin N) ℝ :=
  adjacent (Bprime μ) (j + i - 2)

private theorem B_swap (μ : Fin N → ℝ) (π : Fin N × Fin N) :
    B μ π (π.2, π.1) = if π.1 = π.2 then μ π.1 else if π.2 < π.1 then 1 else 0 := by
  rcases π with ⟨a, b⟩
  by_cases h : a = b
  · subst b; simp [B]
  · simp [B, Prod.mk.injEq, h, Ne.symm h]

private theorem Bprime_swap (μ : Fin N → ℝ) (π : Fin N × Fin N) :
    Bprime μ π (π.2, π.1) = if π.1 = π.2 then 1-μ π.1 else if π.1 < π.2 then 1 else 0 := by
  rcases π with ⟨a, b⟩
  by_cases h : a = b
  · subst b; simp [Bprime]
  · simp [Bprime, Prod.mk.injEq, h, Ne.symm h]

def swapWord (s : ℕ) (h : s + 1 < n) (w : (Fin n → Fin N)) : (Fin n → Fin N) :=
  w ∘ Equiv.swap ⟨s, by omega⟩ ⟨s + 1, h⟩

@[simp]
private theorem swapWord_left (s : ℕ) (h : s + 1 < n) (w : (Fin n → Fin N)) :
    swapWord s h w ⟨s, by omega⟩ = w ⟨s + 1, h⟩ := by
  simp [swapWord]
@[simp]
private theorem swapWord_right (s : ℕ) (h : s + 1 < n) (w : (Fin n → Fin N)) :
    swapWord s h w ⟨s + 1, h⟩ = w ⟨s, by omega⟩ := by
  simp [swapWord]
private theorem swapWord_other (s : ℕ) (h : s + 1 < n) (w : (Fin n → Fin N)) (r : Fin n)
    (h₁ : r.val ≠ s) (h₂ : r.val ≠ s + 1) : swapWord s h w r = w r := by
  simp only [swapWord, Function.comp_apply]
  rw [Equiv.swap_apply_of_ne_of_ne]
  · exact fun hh => h₁ (congrArg Fin.val hh)
  · exact fun hh => h₂ (congrArg Fin.val hh)

private theorem B_row (μ : Fin N → ℝ) (π ν : Fin N × Fin N) :
    B μ π ν = if ν = (π.2, π.1) then (B μ π ((π).2, (π).1)) else 0 := by
  by_cases hν : ν = (π.2, π.1)
  · subst ν
    rcases π with ⟨a, b⟩
    by_cases he : a = b
    · subst b; simp [B]
    · simp [B, Prod.mk.injEq, he, Ne.symm he]
  · have hequal : ¬(π = ν ∧ ν.1 = ν.2) := by
      rintro ⟨rfl, he⟩
      apply hν
      exact Prod.ext he he.symm
    have hswap : ¬(π.1 = ν.2 ∧ π.2 = ν.1) := by
      rintro ⟨h₁, h₂⟩
      apply hν
      exact Prod.ext h₂.symm h₁.symm
    simp only [B, if_neg hequal, if_neg hν]
    split_ifs with hs
    · exact False.elim (hswap ⟨hs.1, hs.2.1⟩)
    · rfl

private theorem Bprime_row (μ : Fin N → ℝ) (π ν : Fin N × Fin N) :
    Bprime μ π ν = if ν = (π.2, π.1) then (Bprime μ π ((π).2, (π).1)) else 0 := by
  by_cases hν : ν = (π.2, π.1)
  · subst ν
    rcases π with ⟨a, b⟩
    by_cases he : a = b
    · subst b; simp [Bprime]
    · simp [Bprime, Prod.mk.injEq, he, Ne.symm he]
  · have hequal : ¬(π = ν ∧ ν.1 = ν.2) := by
      rintro ⟨rfl, he⟩
      apply hν
      exact Prod.ext he he.symm
    have hswap : ¬(π.1 = ν.2 ∧ π.2 = ν.1) := by
      rintro ⟨h₁, h₂⟩
      apply hν
      exact Prod.ext h₂.symm h₁.symm
    simp only [Bprime, if_neg hequal, if_neg hν]
    split_ifs with hs
    · exact False.elim (hswap ⟨hs.1, hs.2.1⟩)
    · rfl

private theorem adjacent_row (M : Matrix (Fin N × Fin N) (Fin N × Fin N) ℝ)
    (weight : (Fin N × Fin N) → ℝ)
    (hM : ∀ π ν, M π ν = if ν = (π.2, π.1) then weight π else 0)
    (s : ℕ) (h : s + 1 < n) (π ν : (Fin n → Fin N)) :
    adjacent M s π ν = if ν = swapWord s h π then
      weight (π ⟨s, by omega⟩, π ⟨s + 1, h⟩) else 0 := by
  classical
  let a : Fin n := ⟨s, by omega⟩
  let b : Fin n := ⟨s + 1, h⟩
  have ha : a.val = s := rfl
  have hb : b.val = s + 1 := rfl
  have hprod : (∏ r : Fin n, if r.val = s ∨ r.val = s + 1 then (1:ℝ)
      else if π r = ν r then 1 else 0) =
      if ∀ r : Fin n, r.val ≠ s → r.val ≠ s + 1 → π r = ν r then 1 else 0 := by
    have hh : ∀ r : Fin n, (if r.val = s ∨ r.val = s + 1 then (1:ℝ)
        else if π r = ν r then 1 else 0) =
        if r.val ≠ s → r.val ≠ s + 1 → π r = ν r then 1 else 0 := by
      intro r; split_ifs <;> simp_all
    simp_rw [hh, Fintype.prod_boole]
    split_ifs <;> rfl
  have heq : ν = swapWord s h π ↔
      (ν a, ν b) = (π b, π a) ∧ ∀ r : Fin n, r.val ≠ s → r.val ≠ s + 1 → π r = ν r := by
    constructor
    · intro he; subst ν
      refine ⟨?_, ?_⟩
      · simp [a, b]
      · intro r h₁ h₂; exact (swapWord_other s h π r h₁ h₂).symm
    · rintro ⟨hp, ho⟩
      have hp₁ := congrArg Prod.fst hp
      have hp₂ := congrArg Prod.snd hp
      apply funext
      intro r
      by_cases h₁ : r.val = s
      · have hr : r = a := Fin.ext h₁
        subst r; simpa [a, b] using hp₁
      · by_cases h₂ : r.val = s + 1
        · have hr : r = b := Fin.ext h₂
          subst r; simpa [a, b] using hp₂
        · rw [swapWord_other s h π r h₁ h₂]; exact (ho r h₁ h₂).symm
  simp only [adjacent, dif_pos h, hM, hprod]
  change (if (ν a, ν b) = (π b, π a) then weight (π a, π b) else 0) *
    (if ∀ r : Fin n, r.val ≠ s → r.val ≠ s + 1 → π r = ν r then 1 else 0) = _
  simp only [heq]
  split_ifs <;> simp_all <;> rfl

theorem calB_mulVec (μ : Fin N → ℝ) (j i : ℕ) (h : j + i-2 + 1 < n)
    (f : (Fin n → Fin N) → ℝ) (w : (Fin n → Fin N)) :
    (calB μ j i *ᵥ f) w =
      (B μ (w ⟨j + i-2, by omega⟩, w ⟨j + i-2 + 1, h⟩) (((w ⟨j + i-2, by omega⟩, w ⟨j + i-2 + 1, h⟩)).2, ((w ⟨j + i-2, by omega⟩, w ⟨j + i-2 + 1, h⟩)).1)) * f (swapWord (j + i-2) h w) := by
  classical
  simp only [calB, mulVec, dotProduct, adjacent_row _ _ (B_row μ) _ h]
  simp

theorem calBprime_mulVec (μ : Fin N → ℝ) (j i : ℕ) (h : j + i-2 + 1 < n)
    (f : (Fin n → Fin N) → ℝ) (w : (Fin n → Fin N)) :
    (calBprime μ j i *ᵥ f) w =
      (Bprime μ (w ⟨j + i-2, by omega⟩, w ⟨j + i-2 + 1, h⟩) (((w ⟨j + i-2, by omega⟩, w ⟨j + i-2 + 1, h⟩)).2, ((w ⟨j + i-2, by omega⟩, w ⟨j + i-2 + 1, h⟩)).1)) * f (swapWord (j + i-2) h w) := by
  classical
  simp only [calBprime, mulVec, dotProduct, adjacent_row _ _ (Bprime_row μ) _ h]
  simp

theorem weights_nonneg_sum (μ : Fin N → ℝ) (hμ : ∀ a, 0 ≤ μ a ∧ μ a ≤ 1)
    (π : Fin N × Fin N) :
    0 ≤ (B μ π ((π).2, (π).1)) ∧ 0 ≤ (Bprime μ π ((π).2, (π).1)) ∧
      (B μ π ((π).2, (π).1)) + (Bprime μ π ((π).2, (π).1)) = 1 := by
  rcases π with ⟨a, b⟩
  rw [B_swap μ (a, b), Bprime_swap μ (a, b)]
  split_ifs <;> simp_all <;> have := hμ a <;> omega

namespace Path

def swap (w : ℤ → Fin N) (i : ℤ) : ℤ → Fin N :=
  w ∘ Equiv.swap i (i + 1)

def left (pref : Fin N → Bool) (s : (ℤ × (ℤ → Fin N))) : Bool :=
  if s.2 (s.1 + 1) < s.2 s.1 then true
  else if s.2 s.1 < s.2 (s.1 + 1) then false else pref (s.2 s.1)

private def c (s : (ℤ × (ℤ → Fin N))) : Fin N := min (s.2 s.1) (s.2 (s.1 + 1))
def next (pref : Fin N → Bool) (s : (ℤ × (ℤ → Fin N))) : (ℤ × (ℤ → Fin N)) :=
  (if left pref s then s.1-1 else s.1 + 1, swap s.2 s.1)
def interior (m : ℕ) (s : (ℤ × (ℤ → Fin N))) : Prop := 0 ≤ s.1 ∧ s.1 < m

private def distance (m : ℕ) (d : Bool) (i : ℤ) : ℕ :=
  if d then (i + 1).toNat else ((m : ℤ)-i).toNat

private def rank (pref : Fin N → Bool) (m : ℕ) (s : (ℤ × (ℤ → Fin N))) : ℕ :=
  (c s).val * (2*m) + (if left pref s = pref (c s) then 0 else m) +
    distance m (left pref s) s.1

private theorem left_values (pref : Fin N → Bool) (s : (ℤ × (ℤ → Fin N))) (h : left pref s = true) :
    s.2 (s.1 + 1) ≤ s.2 s.1 ∧ c s = s.2 (s.1 + 1) := by
  have hh : s.2 (s.1 + 1) ≤ s.2 s.1 := by
    by_contra hn
    have hlt : s.2 s.1 < s.2 (s.1 + 1) := by omega
    simp [left, show ¬s.2 (s.1 + 1) < s.2 s.1 by omega, hlt] at h
  exact ⟨hh, min_eq_right hh⟩

private theorem right_values (pref : Fin N → Bool) (s : (ℤ × (ℤ → Fin N))) (h : left pref s = false) :
    s.2 s.1 ≤ s.2 (s.1 + 1) ∧ c s = s.2 s.1 := by
  have hh : s.2 s.1 ≤ s.2 (s.1 + 1) := by
    by_contra hn
    have hlt : s.2 (s.1 + 1) < s.2 s.1 := by omega
    simp [left, hlt] at h
  exact ⟨hh, min_eq_left hh⟩

private theorem next_left (pref : Fin N → Bool) (s : (ℤ × (ℤ → Fin N))) (h : left pref s = true) :
    (next pref s).1 = s.1-1 ∧
    (next pref s).2 ((next pref s).1) = s.2 (s.1-1) ∧
    (next pref s).2 ((next pref s).1 + 1) = s.2 (s.1 + 1) := by
  have h₁ : s.1-1 ≠ s.1 := by omega
  have h₂ : s.1-1 ≠ s.1 + 1 := by omega
  simp [next, h, swap, Function.comp_apply, Equiv.swap_apply_def, h₁, h₂]

private theorem next_right (pref : Fin N → Bool) (s : (ℤ × (ℤ → Fin N))) (h : left pref s = false) :
    (next pref s).1 = s.1 + 1 ∧
    (next pref s).2 ((next pref s).1) = s.2 s.1 ∧
    (next pref s).2 ((next pref s).1 + 1) = s.2 (s.1 + 2) := by
  have h₁ : s.1 + 1 ≠ s.1 := by omega
  have h₂ : s.1 + 1 + 1 ≠ s.1 := by omega
  have h₃ : s.1 + 1 + 1 ≠ s.1 + 1 := by omega
  simp [next, h, swap, Function.comp_apply, Equiv.swap_apply_def, h₁, h₂, h₃, show s.1 + 1 + 1 = s.1 + 2 by ring]

private theorem minimum_nonincreasing (pref : Fin N → Bool) (s : (ℤ × (ℤ → Fin N))) : c (next pref s) ≤ c s := by
  cases h : left pref s
  · obtain ⟨_, h₁, h₂⟩ := next_right pref s h
    rw [c, h₁, h₂, (right_values pref s h).2]
    exact min_le_left _ _
  · obtain ⟨_, h₁, h₂⟩ := next_left pref s h
    rw [c, h₁, h₂, (left_values pref s h).2]
    exact min_le_right _ _

private theorem direction_constant_minimum (pref : Fin N → Bool) (s : (ℤ × (ℤ → Fin N)))
    (hc : c (next pref s) = c s) :
    left pref (next pref s) = left pref s ∨ left pref (next pref s) = pref (c s) := by
  cases h : left pref s
  · obtain ⟨_, h₁, h₂⟩ := next_right pref s h
    have ha := (right_values pref s h).2
    have hh : s.2 s.1 ≤ s.2 (s.1 + 2) := by
      rw [c, h₁, h₂, ha] at hc
      exact hc.symm.trans_le (min_le_right _ _)
    unfold left
    rw [h₁, h₂]
    by_cases he : s.2 s.1 = s.2 (s.1 + 2)
    · right; simp [he, ha]
    · left; simp [h, show ¬s.2 (s.1 + 2) < s.2 s.1 by omega, show s.2 s.1 < s.2 (s.1 + 2) by omega]
  · obtain ⟨_, h₁, h₂⟩ := next_left pref s h
    have ha := (left_values pref s h).2
    have hh : s.2 (s.1 + 1) ≤ s.2 (s.1-1) := by
      rw [c, h₁, h₂, ha] at hc
      exact hc.symm.trans_le (min_le_left _ _)
    unfold left
    rw [h₁, h₂]
    by_cases he : s.2 (s.1-1) = s.2 (s.1 + 1)
    · right; simp [he, ha]
    · left; simp [h, show s.2 (s.1 + 1) < s.2 (s.1-1) by omega]

private theorem distance_bounds (m : ℕ) (d : Bool) (s : (ℤ × (ℤ → Fin N))) (hs : interior m s) :
    1 ≤ distance m d s.1 ∧ distance m d s.1 ≤ m := by
  unfold interior at hs
  cases d <;> simp only [distance, Bool.false_eq_true, ↓reduceIte] <;> omega

private theorem distance_step (pref : Fin N → Bool) (m : ℕ) (s : (ℤ × (ℤ → Fin N)))
    (hn : interior m (next pref s)) :
    distance m (left pref s) (next pref s).1 + 1 = distance m (left pref s) s.1 := by
  unfold interior at hn
  cases h : left pref s <;> simp [distance, next, h] at * <;> omega

private theorem rank_decreases (pref : Fin N → Bool) (m : ℕ) (s : (ℤ × (ℤ → Fin N)))
    (hs : interior m s) (hn : interior m (next pref s)) :
    rank pref m (next pref s) < rank pref m s := by
  have hmin := minimum_nonincreasing pref s
  have hd := distance_bounds m (left pref s) s hs
  have hdn := distance_bounds m (left pref (next pref s)) (next pref s) hn
  by_cases he : c (next pref s) = c s
  · obtain hdir | hpref := direction_constant_minimum pref s he
    · have hdist := distance_step pref m s hn
      unfold rank
      rw [he, hdir]
      omega
    · by_cases hdir : left pref (next pref s) = left pref s
      · have hdist := distance_step pref m s hn
        unfold rank
        rw [he, hdir]
        omega
      · have hne : left pref s ≠ pref (c s) := by
          intro hh; exact hdir (hpref.trans hh.symm)
        rw [hpref] at hdn
        simp only [rank, he, hpref, hne, ↓reduceIte]
        omega
  · have hlt : (c (next pref s)).val + 1 ≤ (c s).val := by omega
    have hmul := Nat.mul_le_mul_right (2*m) hlt
    rw [Nat.add_mul] at hmul
    simp only [one_mul] at hmul
    unfold rank
    split_ifs <;> omega

private theorem rank_bound (pref : Fin N → Bool) (m : ℕ) (s : (ℤ × (ℤ → Fin N)))
    (hs : interior m s) : rank pref m s ≤ 2*N*m := by
  have hd := distance_bounds m (left pref s) s hs
  have hc : (c s).val + 1 ≤ N := by have := (c s).isLt; omega
  have hmul := Nat.mul_le_mul_right (2*m) hc
  rw [Nat.add_mul] at hmul
  simp only [one_mul] at hmul
  have he : N*(2*m) = 2*N*m := by ring
  rw [he] at hmul
  unfold rank
  split_ifs <;> omega

private theorem exits_with_rank_bound (pref : Fin N → Bool) (m : ℕ) (s : (ℤ × (ℤ → Fin N))) :
    ∃ l, l ≤ rank pref m s ∧ ¬interior m ((next pref)^[l] s) ∧
      ∀ r, r < l → interior m ((next pref)^[r] s) := by
  generalize hr : rank pref m s = n
  induction n using Nat.strong_induction_on generalizing s with
  | h n ih =>
    by_cases hs : interior m s
    · have hd := distance_bounds m (left pref s) s hs
      have hpos : 1 ≤ rank pref m s := by unfold rank; omega
      by_cases hn : interior m (next pref s)
      · obtain ⟨l, hl, ht, hpath⟩ := ih (rank pref m (next pref s))
          (by rw [← hr]; exact rank_decreases pref m s hs hn) (next pref s) rfl
        have hdec := rank_decreases pref m s hs hn
        refine ⟨l + 1, by omega, ?_, ?_⟩
        · simpa only [Function.iterate_succ_apply] using ht
        · intro r hr
          cases r with
          | zero => simpa using hs
          | succ r => simpa only [Function.iterate_succ_apply] using hpath r (by omega)
      · refine ⟨1, by omega, by simpa using hn, ?_⟩
        intro r hr
        have : r = 0 := by omega
        subst r; simpa using hs
    · exact ⟨0, Nat.zero_le _, by simpa using hs, by intro r hr; omega⟩

def preferred (μ : Fin N → ℝ) (a : Fin N) : Bool := decide ((1:ℝ)/2 ≤ μ a)
def leftState (s : (ℤ × (ℤ → Fin N))) : (ℤ × (ℤ → Fin N)) := (s.1-1, swap s.2 s.1)
def rightState (s : (ℤ × (ℤ → Fin N))) : (ℤ × (ℤ → Fin N)) := (s.1 + 1, swap s.2 s.1)

private theorem selected_positive (μ : Fin N → ℝ) (s : (ℤ × (ℤ → Fin N))) :
    (left (preferred μ) s = true → 0 < (B μ (s.2 s.1, s.2 (s.1 + 1)) (s.2 (s.1 + 1), s.2 s.1))) ∧
    (left (preferred μ) s = false → 0 < (Bprime μ (s.2 s.1, s.2 (s.1 + 1)) (s.2 (s.1 + 1), s.2 s.1))) := by
  rw [B_swap μ (s.2 s.1, s.2 (s.1 + 1)), Bprime_swap μ (s.2 s.1, s.2 (s.1 + 1))]
  by_cases he : s.2 s.1 = s.2 (s.1 + 1)
  · simp only [he, ↓reduceIte, lt_self_iff_false]
    simp only [left, he, lt_self_iff_false, ↓reduceIte, preferred, decide_eq_true_eq,
      decide_eq_false_iff_not]
    constructor <;> intro h <;> linarith
  · by_cases hlt : s.2 s.1 < s.2 (s.1 + 1)
    · simp [left, he, hlt, not_lt.mpr hlt.le]
    · have hgt : s.2 (s.1 + 1) < s.2 s.1 := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm he)
      simp [left, he, hlt, hgt]

def chosenWeight (μ : Fin N → ℝ) (s : (ℤ × (ℤ → Fin N))) : ℝ :=
  if left (preferred μ) s then (B μ (s.2 s.1, s.2 (s.1 + 1)) (s.2 (s.1 + 1), s.2 s.1)) else (Bprime μ (s.2 s.1, s.2 (s.1 + 1)) (s.2 (s.1 + 1), s.2 s.1))

private theorem chosenWeight_pos (μ : Fin N → ℝ) (s : (ℤ × (ℤ → Fin N))) : 0 < chosenWeight μ s := by
  cases hd : left (preferred μ) s
  · simpa [chosenWeight, hd] using (selected_positive μ s).2 hd
  · simpa [chosenWeight, hd] using (selected_positive μ s).1 hd

/-- Every collision state has a positive-weight exit path of length at most `2*N*m`. -/
theorem exits (μ : Fin N → ℝ) (m : ℕ) (s : ℤ × (ℤ → Fin N)) :
    ∃ l, l ≤ 2*N*m ∧ ¬interior m ((next (preferred μ))^[l] s) ∧
      (∏ r : Fin l, chosenWeight μ ((next (preferred μ))^[r.val] s)) > 0 ∧
      (∀ r, r < l → interior m ((next (preferred μ))^[r] s)) ∧
      Relation.ReflTransGen (fun a b => interior m a ∧
        ((0 < B μ (a.2 a.1, a.2 (a.1 + 1)) (a.2 (a.1 + 1), a.2 a.1) ∧ leftState a = b) ∨
         (0 < Bprime μ (a.2 a.1, a.2 (a.1 + 1)) (a.2 (a.1 + 1), a.2 a.1) ∧ rightState a = b)))
        s ((next (preferred μ))^[l] s) := by
  obtain ⟨l, hl, ht, hp⟩ := exits_with_rank_bound (preferred μ) m s
  have hbound : l ≤ 2*N*m := by
    by_cases hs : interior m s
    · exact hl.trans (rank_bound (preferred μ) m s hs)
    · have : l = 0 := by
        by_contra hn
        exact hs (by simpa using hp 0 (Nat.pos_of_ne_zero hn))
      simp [this]
  refine ⟨l, hbound, ht, Finset.prod_pos (fun r _ => chosenWeight_pos μ _), hp, ?_⟩
  have hstep (r : ℕ) (hr : r < l) :
      interior m ((next (preferred μ))^[r] s) ∧
        ((0 < B μ (((next (preferred μ))^[r] s).2 (((next (preferred μ))^[r] s).1),
          ((next (preferred μ))^[r] s).2 (((next (preferred μ))^[r] s).1 + 1))
          (((next (preferred μ))^[r] s).2 (((next (preferred μ))^[r] s).1 + 1),
          ((next (preferred μ))^[r] s).2 (((next (preferred μ))^[r] s).1)) ∧
          leftState ((next (preferred μ))^[r] s) = (next (preferred μ))^[r + 1] s) ∨
         (0 < Bprime μ (((next (preferred μ))^[r] s).2 (((next (preferred μ))^[r] s).1),
          ((next (preferred μ))^[r] s).2 (((next (preferred μ))^[r] s).1 + 1))
          (((next (preferred μ))^[r] s).2 (((next (preferred μ))^[r] s).1 + 1),
          ((next (preferred μ))^[r] s).2 (((next (preferred μ))^[r] s).1)) ∧
          rightState ((next (preferred μ))^[r] s) = (next (preferred μ))^[r + 1] s)) := by
    refine ⟨hp r hr, ?_⟩
    rw [Function.iterate_succ_apply']
    cases hd : left (preferred μ) ((next (preferred μ))^[r] s)
    · right; exact ⟨(selected_positive μ _).2 hd, by simp [next, hd, rightState]⟩
    · left; exact ⟨(selected_positive μ _).1 hd, by simp [next, hd, leftState]⟩
  have hpath : ∀ r, r ≤ l → Relation.ReflTransGen
      (fun a b => interior m a ∧
        ((0 < B μ (a.2 a.1, a.2 (a.1 + 1)) (a.2 (a.1 + 1), a.2 a.1) ∧ leftState a = b) ∨
         (0 < Bprime μ (a.2 a.1, a.2 (a.1 + 1)) (a.2 (a.1 + 1), a.2 a.1) ∧ rightState a = b)))
      s ((next (preferred μ))^[r] s) := by
    intro r hr
    induction r with
    | zero => exact Relation.ReflTransGen.refl
    | succ r ih => exact (ih (by omega)).tail (hstep r (by omega))
  exact hpath l le_rfl

end Path
end
end D5.S3.StatisticalMechanics.LongRangeSwap.LeeCollisionExit
