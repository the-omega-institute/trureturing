/- GID: D5/S3/Quantum/NormCompression/FinitePowerMetric
   generality: G
   mirror-B: none(waiver:ordinary-finite-power-supplier)
   mirror-E: none(waiver:ordinary-finite-power-supplier)
   anchors: []
   utility: none
   digest: Full symmetric inverse metric and differentiated trace acceleration identity. -/

import D5.S3.Quantum.NormCompression.FinitePowerSpectral
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

noncomputable section

namespace D5.S3.Quantum.NormCompression.FinitePowerConcavity

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.NormCompression.UpperBranchReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {m : Type*} [Fintype m] [DecidableEq m]

local instance {n : Type*} [Fintype n] [DecidableEq n] : Pow (Matrix n n ℂ) ℝ := ⟨CFC.rpow⟩

open private sinh_scaled_le scalar_metric_gap hyperbolic_metric_gap root_power_cancel boundary_det Fq_fromCols_zero scalar_gap_with_weights hessian_column_coefficients sym2 spectralTrace spectralTrace_hasDerivAt sym2_charpoly sym2_explicit_charpoly sym2_posDef_low_eigenvalue_pos trace_rpow_sym2 gramDiagonal gramOffDiagonal power_root_sq rowGram_sym2 exp_pair_sum exp_pair_sub eigenvalue_metric_gap gramDiagonalVelocity gramOffDiagonalVelocity gramDiagonal_hasDerivAt gramOffDiagonal_hasDerivAt Fq_affine_hasDerivAt spectralVelocity spectralVelocity_hasDerivAt from
  D5.S3.Quantum.NormCompression.FinitePowerSpectral
private theorem local_quadratic_duality {y₀ y₁ t : ℝ}
    (hn : 0 < y₀ ^ 2 + y₁ ^ 2) (ht : 0 < t) (p₀ p₁ r₀ r₁ : ℝ) :
    let n := y₀ ^ 2 + y₁ ^ 2
    let H := 1 + t * n
    let U := y₀ * (p₀ - r₀) + y₁ * (p₁ - r₁)
    let V := y₁ * r₀ - y₀ * r₁ - (y₁ * p₀ - y₀ * p₁) / H
    0 ≤ p₀ ^ 2 + p₁ ^ 2 - (y₁ * p₀ - y₀ * p₁) ^ 2 / (n + 1 / t) -
      2 * (p₀ * r₀ + p₁ * r₁) + r₀ ^ 2 + r₁ ^ 2 +
      t * (y₁ * r₀ - y₀ * r₁) ^ 2 ∧
    (p₀ ^ 2 + p₁ ^ 2 - (y₁ * p₀ - y₀ * p₁) ^ 2 / (n + 1 / t) -
      2 * (p₀ * r₀ + p₁ * r₁) + r₀ ^ 2 + r₁ ^ 2 +
      t * (y₁ * r₀ - y₀ * r₁) ^ 2 = 0 → U = 0 ∧ V = 0) := by
  dsimp only
  let n := y₀ ^ 2 + y₁ ^ 2
  let H := 1 + t * n
  let U := y₀ * (p₀ - r₀) + y₁ * (p₁ - r₁)
  let V := y₁ * r₀ - y₀ * r₁ - (y₁ * p₀ - y₀ * p₁) / H
  have hH : 0 < H := by dsimp only [H]; positivity
  have hd : 0 < n + 1 / t := by positivity
  have hid : p₀ ^ 2 + p₁ ^ 2 - (y₁ * p₀ - y₀ * p₁) ^ 2 / (n + 1 / t) -
      2 * (p₀ * r₀ + p₁ * r₁) + r₀ ^ 2 + r₁ ^ 2 +
      t * (y₁ * r₀ - y₀ * r₁) ^ 2 = (U ^ 2 + H * V ^ 2) / n := by
    dsimp only [U, V, H, n]
    field_simp [hn.ne', ht.ne', hd.ne', hH.ne']
    <;> ring
  rw [hid]
  refine ⟨div_nonneg (add_nonneg (sq_nonneg U) (mul_nonneg hH.le (sq_nonneg V))) hn.le, ?_⟩
  intro heq
  have hsum : U ^ 2 + H * V ^ 2 = 0 := (div_eq_zero_iff.mp heq).resolve_right hn.ne'
  have hu : U = 0 := by nlinarith [mul_nonneg hH.le (sq_nonneg V)]
  have hv : V = 0 := by
    have : H * V ^ 2 = 0 := by nlinarith [sq_nonneg U]
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp this).resolve_left hH.ne')
  exact ⟨hu, hv⟩

/- This is the strictness step in the ordered eigenbasis. Positive pairwise
inner products are supplied by the strictly positive off-diagonal power and
nonzero nonnegative columns, including axial columns. -/
private theorem diagonal_kernel_scalar (y₀ y₁ : m → ℝ) {A B d₀ d₁ : ℝ}
    (hd₀ : 0 < d₀) (hd₁ : 0 < d₁)
    (h₀ : ∑ j, y₀ j ^ 2 = d₀) (h₁ : ∑ j, y₁ j ^ 2 = d₁)
    (hpair : ∀ j k, 0 < y₀ j * y₀ k + y₁ j * y₁ k)
    (hg : ∀ j, (A - B) * y₀ j * y₁ j = 0) : A = B := by
  by_contra hAB
  have hne : A - B ≠ 0 := sub_ne_zero.mpr hAB
  have haxis (j : m) : y₀ j = 0 ∨ y₁ j = 0 := by
    have h := hg j
    rw [mul_assoc] at h
    exact mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hne)
  have hex₀ : ∃ j, y₀ j ≠ 0 := by
    by_contra h
    push_neg at h
    have : d₀ = 0 := by rw [← h₀]; simp [h]
    exact hd₀.ne' this
  have hex₁ : ∃ j, y₁ j ≠ 0 := by
    by_contra h
    push_neg at h
    have : d₁ = 0 := by rw [← h₁]; simp [h]
    exact hd₁.ne' this
  obtain ⟨j, hj⟩ := hex₀
  obtain ⟨k, hk⟩ := hex₁
  have hj' : y₁ j = 0 := (haxis j).resolve_left hj
  have hk' : y₀ k = 0 := (haxis k).resolve_right hk
  simpa only [hj', hk', mul_zero, zero_mul, add_zero, lt_self_iff_false] using hpair j k

private theorem rotated_gram_moments (a b : m → ℝ) (u v ξ η : ℝ)
    (huv : u ^ 2 + v ^ 2 = 1)
    (ha : ∑ j, a j ^ 2 = ξ * u ^ 2 + η * v ^ 2)
    (hb : ∑ j, b j ^ 2 = ξ * v ^ 2 + η * u ^ 2)
    (hab : ∑ j, a j * b j = (ξ - η) * u * v) :
    (∑ j, (u * a j + v * b j) ^ 2) = ξ ∧
    (∑ j, (-v * a j + u * b j) ^ 2) = η ∧
    (∑ j, (u * a j + v * b j) * (-v * a j + u * b j)) = 0 := by
  have h₀ : (∑ j, (u * a j + v * b j) ^ 2) =
      u ^ 2 * (∑ j, a j ^ 2) + 2 * u * v * (∑ j, a j * b j) +
        v ^ 2 * (∑ j, b j ^ 2) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h₁ : (∑ j, (-v * a j + u * b j) ^ 2) =
      v ^ 2 * (∑ j, a j ^ 2) - 2 * u * v * (∑ j, a j * b j) +
        u ^ 2 * (∑ j, b j ^ 2) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have h₂ : (∑ j, (u * a j + v * b j) * (-v * a j + u * b j)) =
      -u * v * (∑ j, a j ^ 2) + (u ^ 2 - v ^ 2) * (∑ j, a j * b j) +
        u * v * (∑ j, b j ^ 2) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [ha, hb, hab] at h₀ h₁ h₂
  have he₀ : u ^ 2 * (ξ * u ^ 2 + η * v ^ 2) +
      2 * u * v * ((ξ - η) * u * v) + v ^ 2 * (ξ * v ^ 2 + η * u ^ 2) =
      ξ * (u ^ 2 + v ^ 2) ^ 2 := by ring
  have he₁ : v ^ 2 * (ξ * u ^ 2 + η * v ^ 2) -
      2 * u * v * ((ξ - η) * u * v) + u ^ 2 * (ξ * v ^ 2 + η * u ^ 2) =
      η * (u ^ 2 + v ^ 2) ^ 2 := by ring
  rw [he₀, huv] at h₀
  rw [he₁, huv] at h₁
  refine ⟨by simpa using h₀, by simpa using h₁, ?_⟩
  rw [h₂]
  ring

private theorem whitened_gram_moments (a b : m → ℝ) (u v : ℝ) {ξ η : ℝ}
    (hξ : 0 < ξ) (hη : 0 < η) (s : ℝ)
    (huv : u ^ 2 + v ^ 2 = 1)
    (ha : ∑ j, a j ^ 2 = ξ * u ^ 2 + η * v ^ 2)
    (hb : ∑ j, b j ^ 2 = ξ * v ^ 2 + η * u ^ 2)
    (hab : ∑ j, a j * b j = (ξ - η) * u * v) :
    (∑ j, (ξ ^ (s / 2) * (u * a j + v * b j)) ^ 2) = ξ ^ (s + 1) ∧
    (∑ j, (η ^ (s / 2) * (-v * a j + u * b j)) ^ 2) = η ^ (s + 1) ∧
    (∑ j, (ξ ^ (s / 2) * (u * a j + v * b j)) *
      (η ^ (s / 2) * (-v * a j + u * b j))) = 0 := by
  obtain ⟨h₀, h₁, h₂⟩ := rotated_gram_moments a b u v ξ η huv ha hb hab
  have hp (x : ℝ) (hx : 0 < x) : (x ^ (s / 2)) ^ 2 * x = x ^ (s + 1) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hx.le,
      show s / 2 * 2 = s by ring, Real.rpow_add hx, Real.rpow_one]
  refine ⟨?_, ?_, ?_⟩
  · simp only [mul_pow, ← Finset.mul_sum, h₀]
    exact hp ξ hξ
  · simp only [mul_pow, ← Finset.mul_sum, h₁]
    exact hp η hη
  · have hterm (j : m) :
        ξ ^ (s / 2) * (u * a j + v * b j) *
          (η ^ (s / 2) * (-v * a j + u * b j)) =
        (ξ ^ (s / 2) * η ^ (s / 2)) *
          ((u * a j + v * b j) * (-v * a j + u * b j)) := by ring
    simp_rw [hterm]
    rw [← Finset.mul_sum, h₂, mul_zero]

/- The complete inverse metric on Sym₂, including its off-diagonal direction. -/
private theorem inverse_metric_from_moments {s ξ η : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hη : 0 < η) (hξη : η < ξ)
    (y₀ y₁ w : m → ℝ) (hw : ∀ j, 0 < w j)
    (h₀ : ∑ j, y₀ j ^ 2 = ξ ^ (s + 1))
    (h₁ : ∑ j, y₁ j ^ 2 = η ^ (s + 1))
    (hcross : ∑ j, y₀ j * y₁ j = 0)
    (hwsum : ∑ j, w j = ξ ^ (s + 1) + η ^ (s + 1) +
      (2 * s * (ξ * η) ^ s * (ξ - η) / (ξ ^ s - η ^ s)) / (2 * s + 1))
    (N₀₀ N₀₁ N₁₁ : ℝ) :
    let D := 2 * s * (ξ * η) ^ s * (ξ - η) / (ξ ^ s - η ^ s)
    let g := fun j => (N₀₀ - N₁₁) * y₀ j * y₁ j + N₀₁ * (y₁ j ^ 2 - y₀ j ^ 2)
    let G := (1 / s) * (ξ ^ (s + 1) * N₀₀ ^ 2 + η ^ (s + 1) * N₁₁ ^ 2 + D * N₀₁ ^ 2) -
      ∑ j, (1 / s) * ((N₀₀ * y₀ j + N₀₁ * y₁ j) ^ 2 +
        (N₀₁ * y₀ j + N₁₁ * y₁ j) ^ 2 - (g j) ^ 2 / w j)
    0 ≤ G ∧ (G = 0 → N₀₁ = 0 ∧ ∀ j, g j = 0) := by
  let T := ξ ^ (s + 1) + η ^ (s + 1)
  let D := 2 * s * (ξ * η) ^ s * (ξ - η) / (ξ ^ s - η ^ s)
  let d := ξ ^ (s + 1) - η ^ (s + 1)
  let g := fun j => (N₀₀ - N₁₁) * y₀ j * y₁ j + N₀₁ * (y₁ j ^ 2 - y₀ j ^ 2)
  have hξ : 0 < ξ := hη.trans hξη
  have hD : 0 < D := by
    dsimp only [D]
    exact div_pos (by positivity)
      (sub_pos.mpr (Real.rpow_lt_rpow hη.le hξη hs))
  have hden : 0 < T + D / (2 * s + 1) := by dsimp only [T]; positivity
  have hg : ∑ j, g j = -d * N₀₁ := by
    calc
      _ = (N₀₀ - N₁₁) * (∑ j, y₀ j * y₁ j) +
          N₀₁ * ((∑ j, y₁ j ^ 2) - (∑ j, y₀ j ^ 2)) := by
        dsimp only [g]
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = -d * N₀₁ := by rw [hcross, h₀, h₁]; dsimp only [d]; ring
  have hnorm : (∑ j, ((N₀₀ * y₀ j + N₀₁ * y₁ j) ^ 2 +
      (N₀₁ * y₀ j + N₁₁ * y₁ j) ^ 2)) =
      ξ ^ (s + 1) * N₀₀ ^ 2 + η ^ (s + 1) * N₁₁ ^ 2 + T * N₀₁ ^ 2 := by
    calc
      _ = (N₀₀ ^ 2 + N₀₁ ^ 2) * (∑ j, y₀ j ^ 2) +
          (N₁₁ ^ 2 + N₀₁ ^ 2) * (∑ j, y₁ j ^ 2) +
          2 * (N₀₀ + N₁₁) * N₀₁ * (∑ j, y₀ j * y₁ j) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [h₀, h₁, hcross]; dsimp only [T]; ring
  have hid : (1 / s) * (ξ ^ (s + 1) * N₀₀ ^ 2 + η ^ (s + 1) * N₁₁ ^ 2 + D * N₀₁ ^ 2) -
      (∑ j, (1 / s) * ((N₀₀ * y₀ j + N₀₁ * y₁ j) ^ 2 +
        (N₀₁ * y₀ j + N₁₁ * y₁ j) ^ 2 - (g j) ^ 2 / w j)) =
      (1 / s) * ((∑ j, (g j) ^ 2 / w j) - (T - D) * N₀₁ ^ 2) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hnorm]
    ring
  dsimp only
  change 0 ≤ _ ∧ (_ = 0 → N₀₁ = 0 ∧ ∀ j, g j = 0)
  rw [hid]
  exact scalar_gap_with_weights hs hden (eigenvalue_metric_gap hs hs1 hη hξη)
    g w hw hg hwsum

/- A complete quadratic bound in whitened coordinates, applied to arbitrary
velocity columns. The metric coefficient D is the actual power divided difference. -/
private theorem whitened_hessian_bound {s ξ η : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hη : 0 < η) (hξη : η < ξ)
    (y₀ y₁ v₀ v₁ t : m → ℝ) (ht : ∀ j, 0 < t j)
    (hn : ∀ j, 0 < y₀ j ^ 2 + y₁ j ^ 2)
    (h₀ : ∑ j, y₀ j ^ 2 = ξ ^ (s + 1))
    (h₁ : ∑ j, y₁ j ^ 2 = η ^ (s + 1))
    (hcross : ∑ j, y₀ j * y₁ j = 0)
    (hwsum : ∑ j, (y₀ j ^ 2 + y₁ j ^ 2 + 1 / t j) =
      ξ ^ (s + 1) + η ^ (s + 1) +
      (2 * s * (ξ * η) ^ s * (ξ - η) / (ξ ^ s - η ^ s)) / (2 * s + 1)) :
    let D := 2 * s * (ξ * η) ^ s * (ξ - η) / (ξ ^ s - η ^ s)
    let E₀₀ := ∑ j, y₀ j * v₀ j
    let E₁₁ := ∑ j, y₁ j * v₁ j
    let E₀₁ := (∑ j, (y₀ j * v₁ j + y₁ j * v₀ j)) / 2
    s / ξ ^ (s + 1) * E₀₀ ^ 2 + s / η ^ (s + 1) * E₁₁ ^ 2 +
      4 * s / D * E₀₁ ^ 2 ≤
      ∑ j, s * (v₀ j ^ 2 + v₁ j ^ 2 + t j * (y₁ j * v₀ j - y₀ j * v₁ j) ^ 2) := by
  let A := ξ ^ (s + 1)
  let B := η ^ (s + 1)
  let D := 2 * s * (ξ * η) ^ s * (ξ - η) / (ξ ^ s - η ^ s)
  let E₀₀ := ∑ j, y₀ j * v₀ j
  let E₁₁ := ∑ j, y₁ j * v₁ j
  let E₀₁ := (∑ j, (y₀ j * v₁ j + y₁ j * v₀ j)) / 2
  let N₀₀ := s / A * E₀₀
  let N₁₁ := s / B * E₁₁
  let N₀₁ := 2 * s / D * E₀₁
  let w := fun j => y₀ j ^ 2 + y₁ j ^ 2 + 1 / t j
  let g := fun j => (N₀₀ - N₁₁) * y₀ j * y₁ j + N₀₁ * (y₁ j ^ 2 - y₀ j ^ 2)
  let dual := fun j => (1 / s) * ((N₀₀ * y₀ j + N₀₁ * y₁ j) ^ 2 +
    (N₀₁ * y₀ j + N₁₁ * y₁ j) ^ 2 - (g j) ^ 2 / w j)
  let pair := fun j => (N₀₀ * y₀ j + N₀₁ * y₁ j) * v₀ j +
    (N₀₁ * y₀ j + N₁₁ * y₁ j) * v₁ j
  let cost := fun j => s * (v₀ j ^ 2 + v₁ j ^ 2 +
    t j * (y₁ j * v₀ j - y₀ j * v₁ j) ^ 2)
  let M := s / A * E₀₀ ^ 2 + s / B * E₁₁ ^ 2 + 4 * s / D * E₀₁ ^ 2
  have hξ : 0 < ξ := hη.trans hξη
  have hA : 0 < A := Real.rpow_pos_of_pos hξ _
  have hB : 0 < B := Real.rpow_pos_of_pos hη _
  have hD : 0 < D := by
    dsimp only [D]
    exact div_pos (by positivity) (sub_pos.mpr (Real.rpow_lt_rpow hη.le hξη hs))
  have hw (j : m) : 0 < w j := add_pos (hn j) (one_div_pos.mpr (ht j))
  have hmetric : (1 / s) * (A * N₀₀ ^ 2 + B * N₁₁ ^ 2 + D * N₀₁ ^ 2) = M := by
    dsimp only [N₀₀, N₁₁, N₀₁, M]
    field_simp [hs.ne', hA.ne', hB.ne', hD.ne']
    <;> ring
  have hpair : ∑ j, pair j = M := by
    have hsum : ∑ j, pair j = N₀₀ * E₀₀ + N₁₁ * E₁₁ + 2 * N₀₁ * E₀₁ := by
      dsimp only [pair, E₀₀, E₁₁, E₀₁]
      simp only [Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsum]
    dsimp only [N₀₀, N₁₁, N₀₁, M]
    ring
  have hgap := (inverse_metric_from_moments hs hs1 hη hξη y₀ y₁ w hw
    h₀ h₁ hcross hwsum N₀₀ N₀₁ N₁₁).1
  change 0 ≤ (1 / s) * (A * N₀₀ ^ 2 + B * N₁₁ ^ 2 + D * N₀₁ ^ 2) - ∑ j, dual j at hgap
  rw [hmetric] at hgap
  have hlocal (j : m) : 0 ≤ cost j - 2 * pair j + dual j := by
    have h := (local_quadratic_duality (hn j) (ht j)
      (N₀₀ * y₀ j + N₀₁ * y₁ j) (N₀₁ * y₀ j + N₁₁ * y₁ j)
      (s * v₀ j) (s * v₁ j)).1
    have hnum : y₁ j * (N₀₀ * y₀ j + N₀₁ * y₁ j) -
        y₀ j * (N₀₁ * y₀ j + N₁₁ * y₁ j) = g j := by dsimp only [g]; ring
    rw [hnum] at h
    have he : s * (cost j - 2 * pair j + dual j) =
        (N₀₀ * y₀ j + N₀₁ * y₁ j) ^ 2 + (N₀₁ * y₀ j + N₁₁ * y₁ j) ^ 2 -
        (g j) ^ 2 / w j -
        2 * ((N₀₀ * y₀ j + N₀₁ * y₁ j) * (s * v₀ j) +
          (N₀₁ * y₀ j + N₁₁ * y₁ j) * (s * v₁ j)) +
        (s * v₀ j) ^ 2 + (s * v₁ j) ^ 2 +
        t j * (y₁ j * (s * v₀ j) - y₀ j * (s * v₁ j)) ^ 2 := by
      dsimp only [cost, pair, dual]
      field_simp [hs.ne']
      <;> ring
    rw [← he] at h
    exact nonneg_of_mul_nonneg_right h hs
  have hsum := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hlocal j)
  have hsum' : 0 ≤ (∑ j, cost j) - 2 * M + ∑ j, dual j := by
    simpa only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hpair] using hsum
  change M ≤ ∑ j, cost j
  linarith

private def spectralAcceleration (q a b c da db dc dda ddb ddc : ℝ) : ℝ :=
  let δ := Real.sqrt ((a - c) ^ 2 + 4 * b ^ 2)
  let v := 2 * (a - c) * (da - dc) + 8 * b * db
  let dv := 2 * (da - dc) ^ 2 + 2 * (a - c) * (dda - ddc) + 8 * db ^ 2 + 8 * b * ddb
  let dδ := v / (2 * δ)
  let ddδ := (dv * (2 * δ) - v * (2 * dδ)) / (2 * δ) ^ 2
  let ξ := (a + c + δ) / 2
  let η := (a + c - δ) / 2
  let dξ := (da + dc + dδ) / 2
  let dη := (da + dc - dδ) / 2
  let ddξ := (dda + ddc + ddδ) / 2
  let ddη := (dda + ddc - ddδ) / 2
  q * (ddξ * ξ ^ (q - 1) + ddη * η ^ (q - 1)) +
    q * (q - 1) * (dξ ^ 2 * ξ ^ (q - 2) + dη ^ 2 * η ^ (q - 2))

private def gramDiagonalAcceleration (q : ℝ) (W V : Matrix (Fin 2) m ℝ) (b : Fin 2) : ℝ :=
  ∑ j, (V b j) ^ 2 * (1 / q) * (1 / q - 1) * W b j ^ (1 / q - 2)

private def gramOffDiagonalAcceleration (q : ℝ) (W V : Matrix (Fin 2) m ℝ) : ℝ :=
  ∑ j, (2 * V 0 j * V 1 j * (1 / (2 * q)) * (W 0 j * W 1 j) ^ (1 / (2 * q) - 1) +
    (V 0 j * W 1 j + W 0 j * V 1 j) ^ 2 * (1 / (2 * q)) * (1 / (2 * q) - 1) *
      (W 0 j * W 1 j) ^ (1 / (2 * q) - 2))

private theorem gramDiagonalVelocity_hasDerivAt {q t : ℝ}
    (W V : Matrix (Fin 2) m ℝ) (hW : ∀ b j, 0 < (W + t • V) b j) (b : Fin 2) :
    HasDerivAt (fun u : ℝ => gramDiagonalVelocity q (W + u • V) V b)
      (gramDiagonalAcceleration q (W + t • V) V b) t := by
  unfold gramDiagonalVelocity gramDiagonalAcceleration
  apply HasDerivAt.fun_sum
  intro j _
  have h := (((hasDerivAt_const t (W b j)).add
    ((hasDerivAt_id t).mul_const (V b j))).rpow_const
      (p := 1 / q - 1) (Or.inl (hW b j).ne')).const_mul (V b j * (1 / q))
  convert h using 1 <;>
    simp only [Matrix.add_apply, Matrix.smul_apply, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Pi.sub_apply, id_eq, smul_eq_mul, zero_add, one_mul,
    show 1 / q - 1 - 1 = 1 / q - 2 by ring] <;>
    first | (funext u; try dsimp; ring) | ring

private theorem gramOffDiagonalVelocity_hasDerivAt {q t : ℝ}
    (W V : Matrix (Fin 2) m ℝ) (hW : ∀ b j, 0 < (W + t • V) b j) :
    HasDerivAt (fun u : ℝ => gramOffDiagonalVelocity q (W + u • V) V)
      (gramOffDiagonalAcceleration q (W + t • V) V) t := by
  unfold gramOffDiagonalVelocity gramOffDiagonalAcceleration
  apply HasDerivAt.fun_sum
  intro j _
  have h0 := (hasDerivAt_const t (W 0 j)).add ((hasDerivAt_id t).mul_const (V 0 j))
  have h1 := (hasDerivAt_const t (W 1 j)).add ((hasDerivAt_id t).mul_const (V 1 j))
  have hp := h0.mul h1
  have hdp := (h1.const_mul (V 0 j)).add (h0.mul_const (V 1 j))
  have h := (hdp.mul_const (1 / (2 * q))).mul
    (hp.rpow_const (p := 1 / (2 * q) - 1) (Or.inl (mul_pos (hW 0 j) (hW 1 j)).ne'))
  convert! h using 1 <;>
    simp only [Matrix.add_apply, Matrix.smul_apply, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Pi.sub_apply, id_eq, smul_eq_mul, zero_add, one_mul,
    show 1 / (2 * q) - 1 - 1 = 1 / (2 * q) - 2 by ring] <;>
    first | rfl | (funext u; simp only [Pi.mul_apply, Pi.add_apply]; rfl) | ring

/-- The appended regularization preserves each affine segment exactly. -/
theorem regularizedTable_affine (ε t : ℝ) (W V : Matrix (Fin 2) m ℝ) :
    regularizedTable ε ((1 - t) • W + t • V) =
      (1 - t) • regularizedTable ε W + t • regularizedTable ε V := by
  ext b j
  cases j with
  | inl j =>
    change ((1 - t) * W b j + t * V b j) + ε =
      (1 - t) * (W b j + ε) + t * (V b j + ε)
    ring
  | inr j =>
    change boundaryTable ε b j = (1 - t) * boundaryTable ε b j + t * boundaryTable ε b j
    ring

/-- Actual second derivative of the Schatten trace power in the positive SPD
chart, derived from the two eigenvalues rather than a formal Hessian premise. -/
private theorem Fq_affine_second_hasDerivAt {q : ℝ} (hq : 0 < q)
    (W V : Matrix (Fin 2) m ℝ) (hW : ∀ b j, 0 < W b j)
    (hdisc : 0 < (gramDiagonal q W 0 - gramDiagonal q W 1) ^ 2 +
      4 * gramOffDiagonal q W ^ 2)
    (hlo : 0 < (gramDiagonal q W 0 + gramDiagonal q W 1 -
      Real.sqrt ((gramDiagonal q W 0 - gramDiagonal q W 1) ^ 2 +
        4 * gramOffDiagonal q W ^ 2)) / 2) :
    HasDerivAt (deriv (fun u : ℝ => Fq q (W + u • V)))
      (spectralAcceleration q (gramDiagonal q W 0) (gramOffDiagonal q W) (gramDiagonal q W 1)
        (gramDiagonalVelocity q W V 0) (gramOffDiagonalVelocity q W V)
        (gramDiagonalVelocity q W V 1) (gramDiagonalAcceleration q W V 0)
        (gramOffDiagonalAcceleration q W V) (gramDiagonalAcceleration q W V 1)) 0 := by
  let a := fun u : ℝ => gramDiagonal q (W + u • V) 0
  let b := fun u : ℝ => gramOffDiagonal q (W + u • V)
  let c := fun u : ℝ => gramDiagonal q (W + u • V) 1
  let da := fun u : ℝ => gramDiagonalVelocity q (W + u • V) V 0
  let db := fun u : ℝ => gramOffDiagonalVelocity q (W + u • V) V
  let dc := fun u : ℝ => gramDiagonalVelocity q (W + u • V) V 1
  have hdiag (k : Fin 2) : Continuous (fun u : ℝ => gramDiagonal q (W + u • V) k) := by
    unfold gramDiagonal
    apply continuous_finset_sum
    intro j _
    exact (continuous_const.add (continuous_id.mul_const (V k j))).rpow_const
      (fun _ => Or.inr (by positivity))
  have hb : Continuous b := by
    dsimp only [b, gramOffDiagonal]
    apply continuous_finset_sum
    intro j _
    exact ((continuous_const.add (continuous_id.mul_const (V 0 j))).mul
      (continuous_const.add (continuous_id.mul_const (V 1 j)))).rpow_const
        (fun _ => Or.inr (by positivity))
  have ha : Continuous a := hdiag 0
  have hc : Continuous c := hdiag 1
  have hdiscC : Continuous (fun u : ℝ => (a u - c u) ^ 2 + 4 * b u ^ 2) := by fun_prop
  have hloC : Continuous (fun u : ℝ => (a u + c u -
      Real.sqrt ((a u - c u) ^ 2 + 4 * b u ^ 2)) / 2) := by fun_prop
  have hpos : ∀ᶠ u : ℝ in nhds 0, ∀ k j, 0 < (W + u • V) k j := by
    apply Filter.eventually_all.mpr
    intro k
    apply Filter.eventually_all.mpr
    intro j
    have hC : Continuous (fun u : ℝ => (W + u • V) k j) := by fun_prop
    exact (hC.tendsto 0).eventually (Ioi_mem_nhds (by simpa using hW k j))
  have hdisc' : 0 < (a 0 - c 0) ^ 2 + 4 * b 0 ^ 2 := by simpa [a, b, c] using hdisc
  have hlo' : 0 < (a 0 + c 0 - Real.sqrt ((a 0 - c 0) ^ 2 + 4 * b 0 ^ 2)) / 2 := by
    simpa [a, b, c] using hlo
  have heq : deriv (fun u : ℝ => Fq q (W + u • V)) =ᶠ[nhds 0]
      (fun u => spectralVelocity q (a u) (b u) (c u) (da u) (db u) (dc u)) := by
    filter_upwards [hpos, (hdiscC.tendsto 0).eventually (Ioi_mem_nhds hdisc'),
      (hloC.tendsto 0).eventually (Ioi_mem_nhds hlo')] with u hu hd hl
    exact (Fq_affine_hasDerivAt hq W V hu hd hl).deriv
  have hW₀ : ∀ k j, 0 < (W + (0 : ℝ) • V) k j := by simpa using hW
  have h := spectralVelocity_hasDerivAt (q := q) (gramDiagonal_hasDerivAt W V hW₀ 0)
    (gramOffDiagonal_hasDerivAt W V hW₀) (gramDiagonal_hasDerivAt W V hW₀ 1)
    (gramDiagonalVelocity_hasDerivAt W V hW₀ 0)
    (gramOffDiagonalVelocity_hasDerivAt W V hW₀)
    (gramDiagonalVelocity_hasDerivAt W V hW₀ 1) hdisc' hlo'
  convert h.congr_of_eventuallyEq heq using 1 <;>
    simp only [spectralAcceleration, a, b, c, da, db, dc, zero_smul, add_zero]

/- Exact full trace Hessian in a two-eigenvalue chart. The third symmetric
coordinate is retained through K; it is the noncommuting direction. -/
private theorem spectralAcceleration_decomposition
    (s a b c ξ η d e A B C AA BB CC : ℝ)
    (hξη : η < ξ) (hsum : a + c = ξ + η)
    (hdiff : a - c = (ξ - η) * d) (hoff : 2 * b = (ξ - η) * e)
    (hunit : d ^ 2 + e ^ 2 = 1) :
    let E₀₀ := (A + C + d * (A - C) + 2 * e * B) / 2
    let E₁₁ := (A + C - d * (A - C) - 2 * e * B) / 2
    let K := e * (A - C) / 2 - d * B
    spectralAcceleration (s + 1) a b c A B C AA BB CC =
      (s + 1) * ((ξ ^ s * ((1 + d) / 2) + η ^ s * ((1 - d) / 2)) * AA +
        (ξ ^ s - η ^ s) * e * BB +
        (ξ ^ s * ((1 - d) / 2) + η ^ s * ((1 + d) / 2)) * CC) +
      (s + 1) * (s * ξ ^ (s - 1) * E₀₀ ^ 2 + s * η ^ (s - 1) * E₁₁ ^ 2 +
        2 * ((ξ ^ s - η ^ s) / (ξ - η)) * K ^ 2) := by
  let δ := ξ - η
  let V := d * (A - C) + 2 * e * B
  let L := d * (AA - CC) + 2 * e * BB
  let K := e * (A - C) / 2 - d * B
  have hδ : 0 < δ := sub_pos.mpr hξη
  have hdisc : (a - c) ^ 2 + 4 * b ^ 2 = δ ^ 2 := by
    calc
      _ = δ ^ 2 * (d ^ 2 + e ^ 2) := by
        have hb : b = δ * e / 2 := by dsimp only [δ]; linarith
        rw [hdiff, hb]
        dsimp only [δ]
        ring
      _ = δ ^ 2 := by rw [hunit, mul_one]
  have hsqrt : Real.sqrt ((a - c) ^ 2 + 4 * b ^ 2) = δ := by
    rw [hdisc, Real.sqrt_sq hδ.le]
  have hp : (a + c + δ) / 2 = ξ := by dsimp only [δ]; rw [hsum]; ring
  have hm : (a + c - δ) / 2 = η := by dsimp only [δ]; rw [hsum]; ring
  have hv : (2 * (a - c) * (A - C) + 8 * b * B) / (2 * δ) = V := by
    dsimp only [V, δ]
    rw [hdiff]
    have hb : b = (ξ - η) * e / 2 := by linarith
    rw [hb]
    field_simp [sub_ne_zero.mpr (ne_of_gt hξη)]
    <;> ring
  have hquad : (A - C) ^ 2 + 4 * B ^ 2 - V ^ 2 = 4 * K ^ 2 := by
    dsimp only [V, K]
    nlinarith [congrArg (fun z : ℝ => z * ((A - C) ^ 2 + 4 * B ^ 2)) hunit]
  have hacc : ((2 * (A - C) ^ 2 + 2 * (a - c) * (AA - CC) + 8 * B ^ 2 + 8 * b * BB) *
      (2 * δ) - (2 * (a - c) * (A - C) + 8 * b * B) * (2 * V)) / (2 * δ) ^ 2 =
      L + 4 * K ^ 2 / δ := by
    have hb : b = δ * e / 2 := by dsimp only [δ]; linarith
    have hnum : 2 * (a - c) * (A - C) + 8 * b * B = 2 * δ * V := by
      dsimp only [V, δ]
      rw [hdiff, hb]
      ring
    rw [hnum]
    calc
      _ = L + ((A - C) ^ 2 + 4 * B ^ 2 - V ^ 2) / δ := by
        dsimp only [L]
        rw [hdiff, hb]
        field_simp [hδ.ne']
        <;> ring
      _ = _ := by rw [hquad]
  dsimp only
  dsimp only [spectralAcceleration]
  rw [hsqrt, hp, hm, hv, hacc]
  simp only [show s + 1 - 1 = s by ring, show s + 1 - 2 = s - 1 by ring]
  dsimp only [V, L, K, δ]
  field_simp [sub_ne_zero.mpr (ne_of_gt hξη)]
  <;> ring


end D5.S3.Quantum.NormCompression.FinitePowerConcavity
