/- GID: D5/S3/QuantumBounds/LocalPerceptionCHSH
   generality: I
   mirror-B: D5/B/S3/QuantumBounds/LocalPerceptionCHSH
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The termwise local-perception CHSH witness has sharp upper bound 2. -/

import Mathlib.Analysis.Matrix.Order
import D5.S3.Weil.ZetaLinear.RankTrace

noncomputable section

open Matrix
open scoped Kronecker ComplexOrder

namespace D5.S3.QuantumBounds.LocalPerceptionCHSH

/-- Dichotomic (±1-valued POVM) observables: both outcome effects (1 ± A)/2 are positive. -/
def IsDichotomic (A : Matrix (Fin 2) (Fin 2) ℂ) : Prop := (1 + A).PosSemidef ∧ (1 - A).PosSemidef
def meanA (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := (trace (ρ * (A ⊗ₖ 1))).re
def meanB (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (B : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := (trace (ρ * (1 ⊗ₖ B))).re
def correl (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := (trace (ρ * (A ⊗ₖ B))).re
def chshCoeff : Fin 2 → Fin 2 → ℝ := ![![1, 1], ![1, -1]]
def lpoCHSH (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (A B : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  ∑ x, ∑ y, chshCoeff x y * meanA ρ (A x) * meanB ρ (B y) * correl ρ (A x) (B y)
def claim : Prop :=
  (∀ ρ, ρ.PosSemidef → trace ρ = 1 → ∀ A B : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ x, IsDichotomic (A x)) → (∀ y, IsDichotomic (B y)) → lpoCHSH ρ A B ≤ 2) ∧
  (∃ ρ A B, ρ.PosSemidef ∧ trace ρ = 1 ∧ (∀ x, IsDichotomic (A x)) ∧ (∀ y, IsDichotomic (B y)) ∧
      lpoCHSH ρ A B = 2)

private theorem probability_expansion
    (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hρ : trace ρ = 1)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (ε η : ℝ) :
    (trace (ρ * (((1 / 2 : ℝ) • (1 + ε • A)) ⊗ₖ
      ((1 / 2 : ℝ) • (1 + η • B))))).re =
      (1 + ε * meanA ρ A + η * meanB ρ B + ε * η * correl ρ A B) / 4 := by
  rw [meanA, meanB, correl]
  simp only [smul_kronecker, kronecker_smul, add_kronecker, kronecker_add,
    mul_add, mul_smul_comm, trace_add, trace_smul, one_kronecker_one, mul_one, hρ,
    Complex.add_re, Complex.smul_re, smul_eq_mul, Complex.one_re]
  ring

private theorem effect_positive (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : IsDichotomic A)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    ((1 / 2 : ℝ) • (1 + ε • A)).PosSemidef := by
  rw [IsDichotomic] at hA
  apply PosSemidef.smul _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rcases hε with rfl | rfl
  · simpa only [one_smul] using hA.1
  · simpa only [neg_one_smul, sub_eq_add_neg] using hA.2

private theorem real_nonneg (a b : Fin 2 → ℝ) (C : Fin 2 → Fin 2 → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ y, 0 ≤ b y)
    (h : ∀ x y (ε η : ℝ), (ε = 1 ∨ ε = -1) → (η = 1 ∨ η = -1) →
      0 ≤ 1 + ε * a x + η * b y + ε * η * C x y) :
    a 0 * b 0 * C 0 0 + a 0 * b 1 * C 0 1 +
      a 1 * b 0 * C 1 0 - a 1 * b 1 * C 1 1 ≤ 2 := by
  have ha1 (x) : a x ≤ 1 := by
    linarith [h x 0 (-1) 1 (Or.inr rfl) (Or.inl rfl),
      h x 0 (-1) (-1) (Or.inr rfl) (Or.inr rfl)]
  have hb1 (y) : b y ≤ 1 := by
    linarith [h 0 y 1 (-1) (Or.inl rfl) (Or.inr rfl),
      h 0 y (-1) (-1) (Or.inr rfl) (Or.inr rfl)]
  have hc00 : C 0 0 ≤ 1 := by
    linarith [h 0 0 1 (-1) (Or.inl rfl) (Or.inr rfl),
      h 0 0 (-1) 1 (Or.inr rfl) (Or.inl rfl)]
  have hc01 : C 0 1 ≤ 1 - a 0 + b 1 := by
    linarith [h 0 1 (-1) 1 (Or.inr rfl) (Or.inl rfl)]
  have hc10 : C 1 0 ≤ 1 + a 1 - b 0 := by
    linarith [h 1 0 1 (-1) (Or.inl rfl) (Or.inr rfl)]
  have hc11 : a 1 + b 1 - 1 ≤ C 1 1 := by
    linarith [h 1 1 (-1) (-1) (Or.inr rfl) (Or.inr rfl)]
  have w00 := mul_le_mul_of_nonneg_left hc00 (mul_nonneg (ha 0) (hb 0))
  have w01 := mul_le_mul_of_nonneg_left hc01 (mul_nonneg (ha 0) (hb 1))
  have w10 := mul_le_mul_of_nonneg_left hc10 (mul_nonneg (ha 1) (hb 0))
  have w11 := mul_le_mul_of_nonneg_left hc11 (mul_nonneg (ha 1) (hb 1))
  have certificate : 0 ≤
      ((1 - a 0) / 2) * (b 0 + (b 1)^2 + (1 - b 1)^2) +
      b 1 * (1 - a 0)^2 +
      ((1 - b 0) / 2) * (a 0 + (a 1)^2 + (1 - a 1)^2) +
      a 1 * (1 - b 0)^2 + (1 - a 1) * (1 - b 1) * (1 + a 1 + b 1) := by
    exact add_nonneg (add_nonneg (add_nonneg (add_nonneg
      (mul_nonneg (div_nonneg (sub_nonneg.mpr (ha1 0)) (by norm_num))
        (add_nonneg (add_nonneg (hb 0) (sq_nonneg _)) (sq_nonneg _)))
      (mul_nonneg (hb 1) (sq_nonneg _)))
      (mul_nonneg (div_nonneg (sub_nonneg.mpr (hb1 0)) (by norm_num))
        (add_nonneg (add_nonneg (ha 0) (sq_nonneg _)) (sq_nonneg _))))
      (mul_nonneg (ha 1) (sq_nonneg _)))
      (mul_nonneg (mul_nonneg (sub_nonneg.mpr (ha1 1)) (sub_nonneg.mpr (hb1 1)))
        (add_nonneg (add_nonneg (by norm_num) (ha 1)) (hb 1)))
  nlinarith only [w00, w01, w10, w11, certificate]

private theorem real_bound (a b : Fin 2 → ℝ) (C : Fin 2 → Fin 2 → ℝ)
    (h : ∀ x y (ε η : ℝ), (ε = 1 ∨ ε = -1) → (η = 1 ∨ η = -1) →
      0 ≤ 1 + ε * a x + η * b y + ε * η * C x y) :
    a 0 * b 0 * C 0 0 + a 0 * b 1 * C 0 1 +
      a 1 * b 0 * C 1 0 - a 1 * b 1 * C 1 1 ≤ 2 := by
  let u : Fin 2 → ℝ := fun x => if 0 ≤ a x then 1 else -1
  let v : Fin 2 → ℝ := fun y => if 0 ≤ b y then 1 else -1
  have hu (x) : u x = 1 ∨ u x = -1 := ite_eq_or_eq _ _ _
  have hv (y) : v y = 1 ∨ v y = -1 := ite_eq_or_eq _ _ _
  have hau (x) : 0 ≤ u x * a x := by
    dsimp [u]; split
    · simpa only [one_mul] using ‹0 ≤ a x›
    · simpa only [neg_one_mul] using neg_nonneg.mpr (le_of_not_ge ‹¬0 ≤ a x›)
  have hbv (y) : 0 ≤ v y * b y := by
    dsimp [v]; split
    · simpa only [one_mul] using ‹0 ≤ b y›
    · simpa only [neg_one_mul] using neg_nonneg.mpr (le_of_not_ge ‹¬0 ≤ b y›)
  have signs (t w : ℝ) (ht : t = 1 ∨ t = -1) (hw : w = 1 ∨ w = -1) :
      t * w = 1 ∨ t * w = -1 := by
    rcases ht with rfl | rfl <;> rcases hw with rfl | rfl <;> norm_num
  have hh (x y) (ε η : ℝ) (hε : ε = 1 ∨ ε = -1) (hη : η = 1 ∨ η = -1) :
      0 ≤ 1 + ε * (u x * a x) + η * (v y * b y) +
        ε * η * (u x * v y * C x y) := by
    convert h x y (ε * u x) (η * v y) (signs ε (u x) hε (hu x))
      (signs η (v y) hη (hv y)) using 1; ring
  have term (x y) :
      (u x * a x) * (v y * b y) * (u x * v y * C x y) = a x * b y * C x y := by
    calc
      _ = (u x * u x) * (v y * v y) * (a x * b y * C x y) := by ring
      _ = _ := by rw [mul_self_eq_one_iff.mpr (hu x), mul_self_eq_one_iff.mpr (hv y)]; ring
  simpa only [term] using
    real_nonneg (fun x => u x * a x) (fun y => v y * b y)
      (fun x y => u x * v y * C x y) hau hbv hh

private theorem table_positive
    (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (hρ : ρ.PosSemidef) (htr : trace ρ = 1)
    (A B : Matrix (Fin 2) (Fin 2) ℂ) (hA : IsDichotomic A) (hB : IsDichotomic B)
    (ε η : ℝ) (hε : ε = 1 ∨ ε = -1) (hη : η = 1 ∨ η = -1) :
    0 ≤ 1 + ε * meanA ρ A + η * meanB ρ B + ε * η * correl ρ A B := by
  have hp := RHLinalg.trace_mul_nonneg_of_posSemidef hρ
    ((effect_positive A hA ε hε).kronecker (effect_positive B hB η hη))
  change 0 ≤ Complex.re _ at hp
  rw [probability_expansion ρ htr A B ε η] at hp
  linarith

theorem result : claim := by
  rw [claim]
  constructor
  · intro ρ hρ htr A B hA hB
    convert real_bound (fun x => meanA ρ (A x)) (fun y => meanB ρ (B y))
        (fun x y => correl ρ (A x) (B y))
        (fun x y ε η hε hη => table_positive ρ hρ htr (A x) (B y) (hA x) (hB y) ε η hε hη)
      using 1
    rw [lpoCHSH, chshCoeff]
    simp [Fin.sum_univ_two]
    ring
  · let ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      diagonal (fun i => if i = (0, 0) then 1 else 0)
    let Z : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![1, -1]
    have hZ : IsDichotomic Z := by
      rw [IsDichotomic]
      constructor
      · change ((1 : Matrix (Fin 2) (Fin 2) ℂ) + diagonal ![1, -1]).PosSemidef
        rw [← diagonal_one, diagonal_add]
        apply PosSemidef.diagonal
        exact Fin.forall_fin_two.mpr (by norm_num)
      · change ((1 : Matrix (Fin 2) (Fin 2) ℂ) - diagonal ![1, -1]).PosSemidef
        rw [← diagonal_one, diagonal_sub]
        apply PosSemidef.diagonal
        exact Fin.forall_fin_two.mpr (by norm_num)
    refine ⟨ρ, (fun _ => Z), (fun _ => Z), ?_, ?_, (fun _ => hZ), (fun _ => hZ), ?_⟩
    · apply PosSemidef.diagonal
      intro i
      change (0 : ℂ) ≤ if i = (0, 0) then 1 else 0
      split <;> norm_num
    · simp [ρ]
    · norm_num [lpoCHSH, chshCoeff, meanA, meanB, correl, ρ, Z, trace,
        mul_apply, kronecker_apply, diagonal, one_apply, Fintype.sum_prod_type,
        Fin.sum_univ_two]
end D5.S3.QuantumBounds.LocalPerceptionCHSH
