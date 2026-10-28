/- GID: D5/S3/PrimeForms/SternBrocot/UnimodularGeneration
   generality: I
   mirror-B: D5/B/S3/PrimeForms/SternBrocot/UnimodularGeneration
   mirror-E: none(waiver:uniform-symbolic-generation)
   anchors: []
   utility: none
   digest: Every natural determinant-one matrix is a finite left-right word. -/

import D5.S3.PrimeForms.SternBrocot.WordNodesAreReduced

/-!
The arithmetic descent is adapted from AxiomMath/HJO,
commit 6a58dfa6ab98bd35d841cb2cf8fd9081f62fad03,
HJO/Shuffle/SlopeActions.lean, blob e6ee7331c0c2d870b00de4feb6a866ab2c8287df,
and the IsUnimodular definition in HJO/Shuffle/BraidData.lean.
Copyright (c) 2026 Axiom Math. All rights reserved. Authors: Kenny Lau.
Released under Apache 2.0; full text and source attribution:
Library/PrimeForms/axiom2026unimodulardescent.md.
The adaptation changes visibility and namespace and omits unrelated declarations.
-/

namespace D5.S3.PrimeForms.SternBrocot.UnimodularGeneration

open D5.S3.PrimeForms.Crossing.ExactPropagation
open D5.S3.PrimeForms.SternBrocot.WordNodesAreReduced

private def IsUnimodular (p p' : ℕ × ℕ) : Prop := p'.1 * p.2 = p.1 * p'.2 + 1

private theorem IsUnimodular.right_pos {p p' : ℕ × ℕ}
    (h : IsUnimodular p p') : 1 ≤ p'.1 + p'.2 := by
  rcases Nat.eq_zero_or_pos (p'.1 + p'.2) with h0 | h0
  · exact absurd h (by
      have h1 : p'.1 = 0 := by omega
      have h2 : p'.2 = 0 := by omega
      simp only [IsUnimodular, h1, h2, Nat.zero_mul]
      omega)
  · exact h0

/-- **A unimodular pair is not the zero pair on either side**, the left-hand version. -/
private theorem IsUnimodular.left_pos {p p' : ℕ × ℕ} (h : IsUnimodular p p') : 1 ≤ p.1 + p.2 := by
  rcases Nat.eq_zero_or_pos (p.1 + p.2) with h0 | h0
  · exact absurd h (by
      have h1 : p.1 = 0 := by omega
      have h2 : p.2 = 0 := by omega
      simp only [IsUnimodular, h1, h2, Nat.mul_zero]
      omega)
  · exact h0



private theorem le_or_le_of_det {m₁ n₁ m₂ n₂ : ℕ} (h : m₂ * n₁ = m₁ * n₂ + 1)
    (hne : ¬(m₁ = 0 ∧ n₁ = 1 ∧ m₂ = 1 ∧ n₂ = 0)) :
    (m₂ ≤ m₁ ∧ n₂ ≤ n₁) ∨ (m₁ ≤ m₂ ∧ n₁ ≤ n₂) := by
  rcases le_or_gt m₂ m₁ with hm | hm
  · rcases le_or_gt n₂ n₁ with hn | hn
    · exact Or.inl ⟨hm, hn⟩
    · exact absurd h (by
        have : m₂ * n₁ ≤ m₁ * n₂ :=
          le_trans (Nat.mul_le_mul_right n₁ hm) (Nat.mul_le_mul_left m₁ hn.le)
        omega)
  · rcases le_or_gt n₁ n₂ with hn | hn
    · exact Or.inr ⟨hm.le, hn⟩
    · refine absurd ?_ hne
      obtain ⟨a, rfl⟩ : ∃ a, m₂ = a + 1 := ⟨m₂ - 1, by omega⟩
      obtain ⟨b, rfl⟩ : ∃ b, n₁ = b + 1 := ⟨n₁ - 1, by omega⟩
      have h1 : m₁ * n₂ ≤ a * b := Nat.mul_le_mul (by omega) (by omega)
      have h3 : (a + 1) * (b + 1) = a * b + a + b + 1 := by ring
      omega

/-- **Every unimodular pair other than `((0,1),(1,0))` has a componentwise comparison.** This is the
case split the descent runs on. -/
private theorem IsUnimodular.le_or_le {p p' : ℕ × ℕ} (h : IsUnimodular p p')
    (hne : ¬(p = (0, 1) ∧ p' = (1, 0))) :
    (p'.1 ≤ p.1 ∧ p'.2 ≤ p.2) ∨ (p.1 ≤ p'.1 ∧ p.2 ≤ p'.2) := by
  obtain ⟨m₁, n₁⟩ := p
  obtain ⟨m₂, n₂⟩ := p'
  refine le_or_le_of_det h ?_
  rintro ⟨rfl, rfl, rfl, rfl⟩
  exact hne ⟨rfl, rfl⟩

/-- **The Stern–Brocot descent**: a unimodular pair other than the root `((0,1),(1,0))` is a child
of a unimodular pair, the parent being obtained by subtracting the smaller member from the larger.

Both branches keep the determinant, the subtraction only cancelling the cross term:
`m_2(n_1-n_2) - (m_1-m_2)n_2 = m_2n_1 - m_1n_2`. Together with
`HJO.Mellit.IsUnimodular.left_pos` and `.right_pos` — which say the subtracted member is not the
zero pair — this is the induction principle `HJO.Sweep.exists_slopeActions` runs on. -/
private theorem IsUnimodular.descent {p p' : ℕ × ℕ} (h : IsUnimodular p p')
    (hne : ¬(p = (0, 1) ∧ p' = (1, 0))) :
    (∃ a : ℕ × ℕ, IsUnimodular a p' ∧ p.1 = a.1 + p'.1 ∧ p.2 = a.2 + p'.2) ∨
      (∃ b : ℕ × ℕ, IsUnimodular p b ∧ p'.1 = p.1 + b.1 ∧ p'.2 = p.2 + b.2) := by
  rcases h.le_or_le hne with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Or.inl ⟨(p.1 - p'.1, p.2 - p'.2), ?_, by omega, by omega⟩
    have : (p'.1 : ℤ) * (p.2 - p'.2) = ((p.1 : ℤ) - p'.1) * p'.2 + 1 := by
      have hz : (p'.1 : ℤ) * p.2 = (p.1 : ℤ) * p'.2 + 1 := by exact_mod_cast h
      linear_combination hz
    unfold IsUnimodular
    zify [h1, h2]
    exact this
  · refine Or.inr ⟨(p'.1 - p.1, p'.2 - p.2), ?_, by omega, by omega⟩
    have : ((p'.1 : ℤ) - p.1) * p.2 = (p.1 : ℤ) * ((p'.2 : ℤ) - p.2) + 1 := by
      have hz : (p'.1 : ℤ) * p.2 = (p.1 : ℤ) * p'.2 + 1 := by exact_mod_cast h
      linear_combination hz
    unfold IsUnimodular
    zify [h1, h2]
    exact this


private theorem matrix_ext {A B : PositiveMatrix}
    (ha : A.a = B.a) (hb : A.b = B.b) (hc : A.c = B.c) (hd : A.d = B.d) : A = B := by
  cases A; cases B; congr

/-- Subtracting a nonzero row yields a strictly smaller parent; reversing the
steps constructs a finite word, including the root with zero off-diagonals. -/
private theorem reconstruct (A : PositiveMatrix) (h : Unimodular A) :
    ∃ w : List Bool, wordMatrix w = A := by
  generalize hs : A.a + A.b + A.c + A.d = n
  induction n using Nat.strong_induction_on generalizing A with
  | h n ih =>
    by_cases hr : (A.c, A.d) = (0, 1) ∧ (A.a, A.b) = (1, 0)
    · refine ⟨[], ?_⟩
      apply matrix_ext <;> simp only [wordMatrix, rootMatrix]
      · exact (congrArg Prod.fst hr.2).symm
      · exact (congrArg Prod.snd hr.2).symm
      · exact (congrArg Prod.fst hr.1).symm
      · exact (congrArg Prod.snd hr.1).symm
    · have hp : IsUnimodular (A.c, A.d) (A.a, A.b) := by
        simpa [IsUnimodular, Unimodular, Nat.mul_comm] using h
      rcases hp.descent hr with ⟨p, hd, hc, he⟩ | ⟨p, hd, ha, hb⟩
      · let B : PositiveMatrix := ⟨A.a, A.b, p.1, p.2⟩
        have hb : Unimodular B := by
          simpa [IsUnimodular, Unimodular, B, Nat.mul_comm] using hd
        have hpos := hp.right_pos
        have hlt : B.a + B.b + B.c + B.d < n := by dsimp [B] at *; omega
        obtain ⟨w, hw⟩ := ih _ hlt B hb rfl
        refine ⟨false :: w, ?_⟩
        change leftStep.mul (wordMatrix w) = A
        rw [hw]
        apply matrix_ext <;> simp only [PositiveMatrix.mul, leftStep, B] <;> omega
      · let B : PositiveMatrix := ⟨p.1, p.2, A.c, A.d⟩
        have hb' : Unimodular B := by
          simpa [IsUnimodular, Unimodular, B, Nat.mul_comm] using hd
        have hpos := hp.left_pos
        have hlt : B.a + B.b + B.c + B.d < n := by dsimp [B] at *; omega
        obtain ⟨w, hw⟩ := ih _ hlt B hb' rfl
        refine ⟨true :: w, ?_⟩
        change rightStep.mul (wordMatrix w) = A
        rw [hw]
        apply matrix_ext <;> simp only [PositiveMatrix.mul, rightStep, B] <;> omega

/-- All natural determinant-one matrices, with no entry or word-length bound,
are precisely the matrices of finite words in L and U. -/
theorem unimodular_iff_wordMatrix (A : PositiveMatrix) :
    Unimodular A ↔ ∃ w : List Bool, wordMatrix w = A := by
  constructor
  · exact reconstruct A
  · rintro ⟨w, rfl⟩
    exact unimodular_wordMatrix w

end D5.S3.PrimeForms.SternBrocot.UnimodularGeneration
