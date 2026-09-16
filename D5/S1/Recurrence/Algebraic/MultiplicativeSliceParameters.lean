/- GID: D5/S1/Recurrence/Algebraic/MultiplicativeSliceParameters
   generality: G
   mirror-B: D5/B/S1/Recurrence/Algebraic/MultiplicativeSliceParameters
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two coefficient equations characterize a geometric real family and a constant unit family. -/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace D5.S1.Recurrence.Algebraic.MultiplicativeSliceParameters

/-- The two coefficient equations at every pair of positive indices. -/
def ForcedEquations (p : ℕ → ℝ) (c : ℕ → ℕ → ℝ) : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n →
    (1 - p m) * (1 - p n) * c m n = 1 - p (m + n) ∧
    p m * p n * c m n = -p (m + n)

/-- The real geometric parameter family, including the zero parameter. -/
def GeometricFamily (p : ℕ → ℝ) (c : ℕ → ℕ → ℝ) : Prop :=
  ∃ t : ℝ, t ≠ 1 ∧ t ≠ -1 ∧
    (∀ m : ℕ, 0 < m → p m = t ^ m / (t ^ m - 1)) ∧
    (∀ m n : ℕ, 0 < m → 0 < n →
      c m n = -((t ^ m - 1) * (t ^ n - 1)) / (t ^ (m + n) - 1))

/-- The constant unit coefficients on positive indices. -/
def UnitFamily (p : ℕ → ℝ) (c : ℕ → ℕ → ℝ) : Prop :=
  (∀ m : ℕ, 0 < m → p m = 1) ∧
    (∀ m n : ℕ, 0 < m → 0 < n → c m n = -1)

/-- The coefficient equations have exactly the geometric and unit families of solutions;
any zero or unit entry propagates to every positive index. -/
theorem result (p : ℕ → ℝ) (c : ℕ → ℕ → ℝ) :
    (ForcedEquations p c ↔ GeometricFamily p c ∨ UnitFamily p c) ∧
    (ForcedEquations p c →
      ((∃ m, 0 < m ∧ p m = 0) → ∀ n, 0 < n → p n = 0) ∧
      ((∃ m, 0 < m ∧ p m = 1) → ∀ n, 0 < n → p n = 1) ∧
      ((∀ m, 0 < m → p m ≠ 0) ∧ (∀ m, 0 < m → p m ≠ 1) ∨
        (∀ n, 0 < n → p n = 0) ∨ (∀ n, 0 < n → p n = 1))) := by
  have hsub (h : ForcedEquations p c) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
      (1 - p m - p n) * c m n = 1 := by
    obtain ⟨h₁, h₂⟩ := h m n hm hn
    nlinarith only [h₁, h₂]
  have hcnz (h : ForcedEquations p c) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
      c m n ≠ 0 := by
    intro hc
    simpa [hc] using hsub h m n hm hn
  have hzero (h : ForcedEquations p c) (hp : p 1 = 0) :
      ∀ n, 0 < n → p n = 0 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact hp
    | succ n hn _ =>
      have he := (h n 1 hn (by decide)).2
      simpa [hp] using he
  have hone (h : ForcedEquations p c) (hp : p 1 = 1) :
      ∀ n, 0 < n → p n = 1 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact hp
    | succ n hn _ =>
      have he := (h n 1 hn (by decide)).1
      simp only [hp, sub_self, mul_zero, zero_mul] at he
      linarith
  have havoid (h : ForcedEquations p c) (hp₀ : p 1 ≠ 0) (hp₁ : p 1 ≠ 1) :
      ∀ n, 0 < n → p n ≠ 0 ∧ p n ≠ 1 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact ⟨hp₀, hp₁⟩
    | succ n hn ih =>
      obtain ⟨h₁, h₂⟩ := h n 1 hn (by decide)
      have hc := hcnz h n 1 hn (by decide)
      constructor
      · intro hz
        have hprod := mul_ne_zero (mul_ne_zero ih.1 hp₀) hc
        exact hprod (by simpa [hz] using h₂)
      · intro ho
        have hprod := mul_ne_zero
          (mul_ne_zero (sub_ne_zero.mpr (Ne.symm ih.2))
            (sub_ne_zero.mpr (Ne.symm hp₁))) hc
        exact hprod (by simpa [ho] using h₁)
  have hnecessary (h : ForcedEquations p c) : GeometricFamily p c ∨ UnitFamily p c := by
    by_cases hp₀ : p 1 = 0
    · have hz := hzero h hp₀
      left
      refine ⟨0, by norm_num, by norm_num, ?_, ?_⟩
      · intro m hm
        simp [hz m hm, zero_pow (Nat.ne_of_gt hm)]
      · intro m n hm hn
        have hc := hsub h m n hm hn
        simp only [hz m hm, hz n hn, sub_zero, one_mul] at hc
        simpa [zero_pow (Nat.ne_of_gt hm), zero_pow (Nat.ne_of_gt hn),
          zero_pow (Nat.ne_of_gt (Nat.add_pos_left hm n))] using hc
    by_cases hp₁ : p 1 = 1
    · have ho := hone h hp₁
      right
      refine ⟨ho, ?_⟩
      intro m n hm hn
      have hc := hsub h m n hm hn
      rw [ho m hm, ho n hn] at hc
      linarith
    have ha := havoid h hp₀ hp₁
    left
    sorry
  have hsufficient : GeometricFamily p c ∨ UnitFamily p c → ForcedEquations p c := by
    sorry
  refine ⟨⟨hnecessary, hsufficient⟩, ?_⟩
  intro h
  by_cases hp₀ : p 1 = 0
  · have hz := hzero h hp₀
    refine ⟨fun _ => hz, ?_, Or.inr (Or.inl hz)⟩
    rintro ⟨m, hm, he⟩
    have := hz m hm
    exact False.elim (by linarith)
  by_cases hp₁ : p 1 = 1
  · have ho := hone h hp₁
    refine ⟨?_, fun _ => ho, Or.inr (Or.inr ho)⟩
    rintro ⟨m, hm, he⟩
    have := ho m hm
    exact False.elim (by linarith)
  have ha := havoid h hp₀ hp₁
  refine ⟨?_, ?_, Or.inl ⟨fun m hm => (ha m hm).1, fun m hm => (ha m hm).2⟩⟩
  · rintro ⟨m, hm, he⟩
    exact False.elim ((ha m hm).1 he)
  · rintro ⟨m, hm, he⟩
    exact False.elim ((ha m hm).2 he)

end D5.S1.Recurrence.Algebraic.MultiplicativeSliceParameters
