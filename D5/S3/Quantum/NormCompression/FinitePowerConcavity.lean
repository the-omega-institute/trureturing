/- GID: D5/S3/Quantum/NormCompression/FinitePowerConcavity
   generality: G
   mirror-B: none(waiver:ordinary-finite-power-supplier)
   mirror-E: none(waiver:ordinary-finite-power-supplier)
   anchors: []
   utility: none
   digest: Full-cone concavity of the actual trace power for every finite two-row table. -/

import D5.S3.Quantum.NormCompression.FinitePowerMetric
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
open private local_quadratic_duality diagonal_kernel_scalar rotated_gram_moments whitened_gram_moments inverse_metric_from_moments whitened_hessian_bound spectralAcceleration gramDiagonalAcceleration gramOffDiagonalAcceleration gramDiagonalVelocity_hasDerivAt gramOffDiagonalVelocity_hasDerivAt Fq_affine_second_hasDerivAt spectralAcceleration_decomposition from
  D5.S3.Quantum.NormCompression.FinitePowerMetric
/- Boundary support version: h is beta*a*b and may be zero at an axial
column. The zero-denominator branch uses the actual allowed support tangent. -/
private theorem local_quadratic_duality_support {y₀ y₁ h : ℝ}
    (hn : 0 < y₀ ^ 2 + y₁ ^ 2) (hh : 0 ≤ h) (p₀ p₁ r₀ r₁ : ℝ)
    (hsupport : h = 0 → y₁ * r₀ - y₀ * r₁ = 0) :
    0 ≤ p₀ ^ 2 + p₁ ^ 2 - (y₁ * p₀ - y₀ * p₁) ^ 2 / (y₀ ^ 2 + y₁ ^ 2 + h) -
      2 * (p₀ * r₀ + p₁ * r₁) + r₀ ^ 2 + r₁ ^ 2 +
      (y₁ * r₀ - y₀ * r₁) ^ 2 / h := by
  rcases eq_or_lt_of_le hh with heq | hpos
  · have hh0 : h = 0 := heq.symm
    have hr := hsupport hh0
    have hid : p₀ ^ 2 + p₁ ^ 2 - (y₁ * p₀ - y₀ * p₁) ^ 2 / (y₀ ^ 2 + y₁ ^ 2) -
        2 * (p₀ * r₀ + p₁ * r₁) + r₀ ^ 2 + r₁ ^ 2 =
        (y₀ * (p₀ - r₀) + y₁ * (p₁ - r₁)) ^ 2 / (y₀ ^ 2 + y₁ ^ 2) +
          ((y₁ * r₀ - y₀ * r₁) ^ 2 -
            2 * (y₁ * p₀ - y₀ * p₁) * (y₁ * r₀ - y₀ * r₁)) / (y₀ ^ 2 + y₁ ^ 2) := by
      field_simp [hn.ne']
      <;> ring
    simp only [hh0, add_zero, div_zero]
    rw [hid, hr]
    simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero, zero_div, add_zero]
    exact div_nonneg (sq_nonneg _) hn.le
  · simpa [div_eq_mul_inv, mul_comm] using
      (local_quadratic_duality hn (one_div_pos.mpr hpos) p₀ p₁ r₀ r₁).1

private theorem local_quadratic_radial_support {y₀ y₁ h τ r₀ r₁ : ℝ}
    (hh : 0 ≤ h)
    (heq : (τ * y₀) ^ 2 + (τ * y₁) ^ 2 -
      (y₁ * (τ * y₀) - y₀ * (τ * y₁)) ^ 2 / (y₀ ^ 2 + y₁ ^ 2 + h) -
      2 * ((τ * y₀) * r₀ + (τ * y₁) * r₁) + r₀ ^ 2 + r₁ ^ 2 +
      (y₁ * r₀ - y₀ * r₁) ^ 2 / h = 0) : r₀ = τ * y₀ ∧ r₁ = τ * y₁ := by
  have hp : y₁ * (τ * y₀) - y₀ * (τ * y₁) = 0 := by ring
  rw [hp, zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero] at heq
  have hd : 0 ≤ (y₁ * r₀ - y₀ * r₁) ^ 2 / h := div_nonneg (sq_nonneg _) hh
  constructor <;> nlinarith [sq_nonneg (r₀ - τ * y₀), sq_nonneg (r₁ - τ * y₁)]

/- A constructive oriented real eigenbasis for every positive-overlap SPD
row Gram. Distinctness follows from the actual positive off-diagonal entry. -/
private theorem positive_gram_rotation (a b c : ℝ) (hb : 0 < b)
    (hlo : 0 < (a + c - Real.sqrt ((a - c) ^ 2 + 4 * b ^ 2)) / 2) :
    ∃ u v ξ η : ℝ, 0 < u ∧ 0 < v ∧ 0 < η ∧ η < ξ ∧ u ^ 2 + v ^ 2 = 1 ∧
      a = ξ * u ^ 2 + η * v ^ 2 ∧ c = ξ * v ^ 2 + η * u ^ 2 ∧
      b = (ξ - η) * u * v := by
  let δ := Real.sqrt ((a - c) ^ 2 + 4 * b ^ 2)
  have hdisc : 0 < (a - c) ^ 2 + 4 * b ^ 2 := by positivity
  have hδ : 0 < δ := Real.sqrt_pos.mpr hdisc
  have hδsq : δ ^ 2 = (a - c) ^ 2 + 4 * b ^ 2 := Real.sq_sqrt hdisc.le
  have habs : |a - c| < δ := by
    rw [← Real.sqrt_sq_eq_abs (a - c)]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith [sq_pos_of_pos hb])
  have hplus : 0 < δ + (a - c) := by linarith [(abs_lt.mp habs).1]
  have hminus : 0 < δ - (a - c) := by linarith [(abs_lt.mp habs).2]
  let u := Real.sqrt ((δ + (a - c)) / (2 * δ))
  let v := Real.sqrt ((δ - (a - c)) / (2 * δ))
  let ξ := (a + c + δ) / 2
  let η := (a + c - δ) / 2
  have hu : 0 < u := Real.sqrt_pos.mpr (div_pos hplus (by positivity))
  have hv : 0 < v := Real.sqrt_pos.mpr (div_pos hminus (by positivity))
  have hu₂ : u ^ 2 = (δ + (a - c)) / (2 * δ) :=
    Real.sq_sqrt (div_nonneg hplus.le (by positivity))
  have hv₂ : v ^ 2 = (δ - (a - c)) / (2 * δ) :=
    Real.sq_sqrt (div_nonneg hminus.le (by positivity))
  have huv : u ^ 2 + v ^ 2 = 1 := by rw [hu₂, hv₂]; field_simp [hδ.ne'] <;> ring
  have hprod : δ * u * v = b := by
    have heq : (δ * u * v) ^ 2 = b ^ 2 := by
      rw [mul_pow, mul_pow, hu₂, hv₂]
      field_simp [hδ.ne']
      nlinarith [hδsq]
    nlinarith [mul_pos (mul_pos hδ hu) hv]
  have hξη : ξ - η = δ := by dsimp only [ξ, η]; ring
  refine ⟨u, v, ξ, η, hu, hv, hlo, by dsimp only [ξ, η]; linarith, huv, ?_, ?_, ?_⟩
  · rw [hu₂, hv₂]
    dsimp only [ξ, η]
    field_simp [hδ.ne']
    <;> ring
  · rw [hu₂, hv₂]
    dsimp only [ξ, η]
    field_simp [hδ.ne']
    <;> ring
  · rw [hξη]
    exact hprod.symm

/- Exact entrywise coefficient conversion from ordinary affine-table jets
to the correctly normalized velocity z=dotW/(q*x^(2q-1)). -/
private theorem normalized_diagonal_jets {q w : ℝ} (hq : 0 < q) (hw : 0 < w) (v : ℝ) :
    v * (1 / q) * w ^ (1 / q - 1) =
      w ^ (1 / (2 * q)) * (v / (q * (w ^ (1 / (2 * q))) ^ (2 * q - 1))) ∧
    v ^ 2 * (1 / q) * (1 / q - 1) * w ^ (1 / q - 2) =
      -(q - 1) * (v / (q * (w ^ (1 / (2 * q))) ^ (2 * q - 1))) ^ 2 := by
  have hx : w ^ (1 / (2 * q)) ≠ 0 := (Real.rpow_pos_of_pos hw _).ne'
  constructor
  · rw [Real.rpow_sub hw (1 / q) 1, Real.rpow_one,
      ← power_root_sq hq hw.le, root_power_cancel hq hw]
    field_simp [hq.ne', hw.ne', hx]
    <;> ring
  · rw [Real.rpow_sub hw (1 / q) 2, Real.rpow_two,
      ← power_root_sq hq hw.le, root_power_cancel hq hw]
    field_simp [hq.ne', hw.ne', hx]
    <;> ring

private theorem normalized_offDiagonal_jets {q w₀ w₁ : ℝ}
    (hq : 0 < q) (hw₀ : 0 < w₀) (hw₁ : 0 < w₁) (v₀ v₁ : ℝ) :
    let a := w₀ ^ (1 / (2 * q))
    let b := w₁ ^ (1 / (2 * q))
    let z₀ := v₀ / (q * a ^ (2 * q - 1))
    let z₁ := v₁ / (q * b ^ (2 * q - 1))
    (v₀ * w₁ + w₀ * v₁) * (1 / (2 * q)) * (w₀ * w₁) ^ (1 / (2 * q) - 1) =
      (a * z₁ + b * z₀) / 2 ∧
    2 * v₀ * v₁ * (1 / (2 * q)) * (w₀ * w₁) ^ (1 / (2 * q) - 1) +
      (v₀ * w₁ + w₀ * v₁) ^ 2 * (1 / (2 * q)) * (1 / (2 * q) - 1) *
        (w₀ * w₁) ^ (1 / (2 * q) - 2) =
      z₀ * z₁ / 2 - (2 * q - 1) / 4 * (b / a * z₀ ^ 2 + a / b * z₁ ^ 2) := by
  have ha : w₀ ^ (1 / (2 * q)) ≠ 0 := (Real.rpow_pos_of_pos hw₀ _).ne'
  have hb : w₁ ^ (1 / (2 * q)) ≠ 0 := (Real.rpow_pos_of_pos hw₁ _).ne'
  dsimp only
  constructor
  · rw [Real.rpow_sub (mul_pos hw₀ hw₁) (1 / (2 * q)) 1, Real.rpow_one,
      Real.mul_rpow hw₀.le hw₁.le, root_power_cancel hq hw₀, root_power_cancel hq hw₁]
    field_simp [hq.ne', hw₀.ne', hw₁.ne', ha, hb]
    <;> ring
  · rw [Real.rpow_sub (mul_pos hw₀ hw₁) (1 / (2 * q)) 1,
      Real.rpow_sub (mul_pos hw₀ hw₁) (1 / (2 * q)) 2, Real.rpow_one, Real.rpow_two,
      Real.mul_rpow hw₀.le hw₁.le, root_power_cancel hq hw₀, root_power_cancel hq hw₁]
    field_simp [hq.ne', hw₀.ne', hw₁.ne', ha, hb]
    <;> ring

private theorem rotated_velocity_moments (a b z w : m → ℝ) (u v r t : ℝ) :
    (∑ j, (r * (u * a j + v * b j)) * (r * (u * z j + v * w j))) =
      r ^ 2 * (u ^ 2 * (∑ j, a j * z j) +
        u * v * (∑ j, (a j * w j + b j * z j)) + v ^ 2 * (∑ j, b j * w j)) ∧
    (∑ j, (t * (-v * a j + u * b j)) * (t * (-v * z j + u * w j))) =
      t ^ 2 * (v ^ 2 * (∑ j, a j * z j) -
        u * v * (∑ j, (a j * w j + b j * z j)) + u ^ 2 * (∑ j, b j * w j)) ∧
    (∑ j, ((r * (u * a j + v * b j)) * (t * (-v * z j + u * w j)) +
      (t * (-v * a j + u * b j)) * (r * (u * z j + v * w j)))) =
      r * t * (-2 * u * v * (∑ j, a j * z j) +
        (u ^ 2 - v ^ 2) * (∑ j, (a j * w j + b j * z j)) +
        2 * u * v * (∑ j, b j * w j)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib] <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

/- The whitening map acts on both the actual columns and their normalized
   velocities. Its cross product has the full determinant factor. -/
private theorem whitening_column_cost (s u v r t k a b z w : ℝ)
    (huv : u ^ 2 + v ^ 2 = 1) :
    s * ((r * (u * z + v * w)) ^ 2 + (t * (-v * z + u * w)) ^ 2 +
      k * ((t * (-v * a + u * b)) * (r * (u * z + v * w)) -
        (r * (u * a + v * b)) * (t * (-v * z + u * w))) ^ 2) =
      s * ((r ^ 2 * u ^ 2 + t ^ 2 * v ^ 2) * z ^ 2 +
        2 * (r ^ 2 - t ^ 2) * u * v * z * w +
        (r ^ 2 * v ^ 2 + t ^ 2 * u ^ 2) * w ^ 2) +
      s * k * (r * t) ^ 2 * (b * z - a * w) ^ 2 := by
  have hc : (t * (-v * a + u * b)) * (r * (u * z + v * w)) -
      (r * (u * a + v * b)) * (t * (-v * z + u * w)) =
      r * t * (u ^ 2 + v ^ 2) * (b * z - a * w) := by ring
  rw [hc, huv]
  ring

private theorem positive_half_power_sq (x : ℝ) (hx : 0 < x) (s : ℝ) :
    (x ^ (s / 2)) ^ 2 = x ^ s := by
  rw [← Real.rpow_two, ← Real.rpow_mul hx.le]
  congr 1
  ring

/- Transforming the full spectral metric back to the original velocities.
   This retains the off-diagonal coordinate and is used by the actual trace
   Hessian calculation, rather than postulating its sign. -/
private theorem rotated_hessian_bound {s ξ η : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hη : 0 < η) (hξη : η < ξ)
    (a b z w : m → ℝ) (ha : ∀ j, 0 < a j) (hb : ∀ j, 0 < b j)
    (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (huv : u ^ 2 + v ^ 2 = 1)
    (h₀ : ∑ j, a j ^ 2 = ξ * u ^ 2 + η * v ^ 2)
    (h₁ : ∑ j, b j ^ 2 = ξ * v ^ 2 + η * u ^ 2)
    (hc : ∑ j, a j * b j = (ξ - η) * u * v) :
    let A := ∑ j, a j * z j
    let B := (∑ j, (a j * w j + b j * z j)) / 2
    let C := ∑ j, b j * w j
    let E₀₀ := u ^ 2 * A + 2 * u * v * B + v ^ 2 * C
    let E₁₁ := v ^ 2 * A - 2 * u * v * B + u ^ 2 * C
    let E₀₁ := -u * v * A + (u ^ 2 - v ^ 2) * B + u * v * C
    let ℓ := (ξ ^ s - η ^ s) * u * v
    s * ξ ^ (s - 1) * E₀₀ ^ 2 + s * η ^ (s - 1) * E₁₁ ^ 2 +
        2 * ((ξ ^ s - η ^ s) / (ξ - η)) * E₀₁ ^ 2 ≤
      ∑ j, (s * ((ξ ^ s * u ^ 2 + η ^ s * v ^ 2) * z j ^ 2 +
        2 * ℓ * z j * w j + (ξ ^ s * v ^ 2 + η ^ s * u ^ 2) * w j ^ 2) +
        (2 * s + 1) * ℓ / (2 * a j * b j) * (b j * z j - a j * w j) ^ 2) := by
  let r := ξ ^ (s / 2)
  let t := η ^ (s / 2)
  let L := (ξ ^ s - η ^ s) * u * v
  let k := fun j => (2 * s + 1) * L / (2 * s * a j * b j * (r * t) ^ 2)
  let y₀ := fun j => r * (u * a j + v * b j)
  let y₁ := fun j => t * (-v * a j + u * b j)
  let z₀ := fun j => r * (u * z j + v * w j)
  let z₁ := fun j => t * (-v * z j + u * w j)
  have hξ : 0 < ξ := hη.trans hξη
  have hr : 0 < r := Real.rpow_pos_of_pos hξ _
  have ht : 0 < t := Real.rpow_pos_of_pos hη _
  have hr₂ : r ^ 2 = ξ ^ s := positive_half_power_sq ξ hξ s
  have ht₂ : t ^ 2 = η ^ s := positive_half_power_sq η hη s
  have hrt : (r * t) ^ 2 = (ξ * η) ^ s := by
    rw [mul_pow, hr₂, ht₂, Real.mul_rpow hξ.le hη.le]
  have hL : 0 < L := by
    exact mul_pos (mul_pos (sub_pos.mpr (Real.rpow_lt_rpow hη.le hξη hs)) hu) hv
  have hk (j : m) : 0 < k j := by
    have haj := ha j
    have hbj := hb j
    dsimp only [k]
    positivity
  have hy (j : m) : 0 < y₀ j ^ 2 + y₁ j ^ 2 := by
    have h : 0 < y₀ j := mul_pos hr (add_pos (mul_pos hu (ha j)) (mul_pos hv (hb j)))
    exact add_pos_of_pos_of_nonneg (sq_pos_of_pos h) (sq_nonneg _)
  obtain ⟨hy₀, hy₁, hyc⟩ := whitened_gram_moments a b u v hξ hη s huv h₀ h₁ hc
  have hwsum : ∑ j, (y₀ j ^ 2 + y₁ j ^ 2 + 1 / k j) =
      ξ ^ (s + 1) + η ^ (s + 1) +
      (2 * s * (ξ * η) ^ s * (ξ - η) / (ξ ^ s - η ^ s)) / (2 * s + 1) := by
    have hkinv (j : m) : 1 / k j =
        (2 * s * (r * t) ^ 2 / ((2 * s + 1) * L)) * (a j * b j) := by
      dsimp only [k]
      field_simp [(ha j).ne', (hb j).ne', hs.ne', hr.ne', ht.ne', hL.ne',
        show 2 * s + 1 ≠ 0 by positivity]
      <;> ring
    simp_rw [hkinv]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hy₀, hy₁, ← Finset.mul_sum, hc, hrt]
    dsimp only [L]
    field_simp [hu.ne', hv.ne', (sub_pos.mpr (Real.rpow_lt_rpow hη.le hξη hs)).ne']
    <;> ring
  have h := whitened_hessian_bound hs hs1 hη hξη y₀ y₁ z₀ z₁ k hk hy
    hy₀ hy₁ hyc hwsum
  obtain ⟨hz₀, hz₁, hzc⟩ := rotated_velocity_moments a b z w u v r t
  dsimp only at h ⊢
  change _ ≤ ∑ j, _ at h
  have hcost (j : m) : s * (z₀ j ^ 2 + z₁ j ^ 2 +
      k j * (y₁ j * z₀ j - y₀ j * z₁ j) ^ 2) =
      s * ((ξ ^ s * u ^ 2 + η ^ s * v ^ 2) * z j ^ 2 +
        2 * L * z j * w j + (ξ ^ s * v ^ 2 + η ^ s * u ^ 2) * w j ^ 2) +
        (2 * s + 1) * L / (2 * a j * b j) * (b j * z j - a j * w j) ^ 2 := by
    dsimp only [z₀, z₁, y₀, y₁]
    rw [whitening_column_cost s u v r t (k j) (a j) (b j) (z j) (w j) huv, hr₂, ht₂]
    dsimp only [k, L]
    field_simp [hs.ne', hr.ne', ht.ne', (ha j).ne', (hb j).ne']
    <;> ring
  simp_rw [hcost] at h
  dsimp only [y₀, y₁, z₀, z₁] at h
  rw [hz₀, hz₁, hzc, hr₂, ht₂] at h
  have hp (x : ℝ) (hx : 0 < x) : x ^ (s + 1) = x ^ s * x := by
    rw [Real.rpow_add hx, Real.rpow_one]
  have hm (x : ℝ) (hx : 0 < x) : x ^ (s - 1) = x ^ s / x := by
    rw [Real.rpow_sub hx, Real.rpow_one]
  convert h using 1
  rw [hp ξ hξ, hp η hη, hm ξ hξ, hm η hη, Real.mul_rpow hξ.le hη.le]
  simp only [mul_pow, div_pow, hr₂, ht₂]
  field_simp [hξ.ne', hη.ne', (Real.rpow_pos_of_pos hξ s).ne',
      (Real.rpow_pos_of_pos hη s).ne',
      (sub_pos.mpr (Real.rpow_lt_rpow hη.le hξη hs)).ne',
      (sub_pos.mpr hξη).ne', hs.ne']
  <;> ring

set_option maxHeartbeats 800000 in
private theorem spectralAcceleration_nonpos_of_columns {s : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (a b z w : m → ℝ)
    (ha : ∀ j, 0 < a j) (hb : ∀ j, 0 < b j)
    (hoverlap : 0 < ∑ j, a j * b j)
    (hlo : 0 < ((∑ j, a j ^ 2) + (∑ j, b j ^ 2) -
      Real.sqrt (((∑ j, a j ^ 2) - (∑ j, b j ^ 2)) ^ 2 +
        4 * (∑ j, a j * b j) ^ 2)) / 2) :
    spectralAcceleration (s + 1) (∑ j, a j ^ 2) (∑ j, a j * b j) (∑ j, b j ^ 2)
      (∑ j, a j * z j) ((∑ j, (a j * w j + b j * z j)) / 2) (∑ j, b j * w j)
      (∑ j, -s * z j ^ 2)
      (∑ j, (z j * w j / 2 - (2 * s + 1) / 4 *
        (b j / a j * z j ^ 2 + a j / b j * w j ^ 2)))
      (∑ j, -s * w j ^ 2) ≤ 0 := by
  obtain ⟨u, v, ξ, η, hu, hv, hη, hξη, huv, h₀, h₁, hc⟩ :=
    positive_gram_rotation (∑ j, a j ^ 2) (∑ j, a j * b j) (∑ j, b j ^ 2)
      hoverlap hlo
  let A := ∑ j, a j * z j
  let B := (∑ j, (a j * w j + b j * z j)) / 2
  let C := ∑ j, b j * w j
  let d := u ^ 2 - v ^ 2
  let e := 2 * u * v
  let S₀ := ξ ^ s * u ^ 2 + η ^ s * v ^ 2
  let S₁ := ξ ^ s * v ^ 2 + η ^ s * u ^ 2
  let L := (ξ ^ s - η ^ s) * u * v
  let Q := ∑ j, (s * (S₀ * z j ^ 2 + 2 * L * z j * w j + S₁ * w j ^ 2) +
    (2 * s + 1) * L / (2 * a j * b j) * (b j * z j - a j * w j) ^ 2)
  let H := s * ξ ^ (s - 1) * (u ^ 2 * A + 2 * u * v * B + v ^ 2 * C) ^ 2 +
    s * η ^ (s - 1) * (v ^ 2 * A - 2 * u * v * B + u ^ 2 * C) ^ 2 +
    2 * ((ξ ^ s - η ^ s) / (ξ - η)) *
      (-u * v * A + (u ^ 2 - v ^ 2) * B + u * v * C) ^ 2
  have hbound : H ≤ Q := rotated_hessian_bound hs hs1 hη hξη a b z w ha hb
    u v hu hv huv h₀ h₁ hc
  have hsum : (∑ j, a j ^ 2) + (∑ j, b j ^ 2) = ξ + η := by
    rw [h₀, h₁]
    linear_combination (ξ + η) * huv
  have hdiff : (∑ j, a j ^ 2) - (∑ j, b j ^ 2) = (ξ - η) * d := by
    rw [h₀, h₁]; dsimp only [d]; ring
  have hoff : 2 * (∑ j, a j * b j) = (ξ - η) * e := by rw [hc]; dsimp only [e]; ring
  have hunit : d ^ 2 + e ^ 2 = 1 := by
    calc
      _ = (u ^ 2 + v ^ 2) ^ 2 := by dsimp only [d, e]; ring
      _ = 1 := by rw [huv]; norm_num
  have hd₀ : (1 + d) / 2 = u ^ 2 := by dsimp only [d]; linarith
  have hd₁ : (1 - d) / 2 = v ^ 2 := by dsimp only [d]; linarith
  have hE₀ : (A + C + d * (A - C) + 2 * e * B) / 2 =
      u ^ 2 * A + 2 * u * v * B + v ^ 2 * C := by
    dsimp only [d, e]
    linear_combination -(A + C) / 2 * huv
  have hE₁ : (A + C - d * (A - C) - 2 * e * B) / 2 =
      v ^ 2 * A - 2 * u * v * B + u ^ 2 * C := by
    dsimp only [d, e]
    linear_combination -(A + C) / 2 * huv
  have hK : (e * (A - C) / 2 - d * B) ^ 2 =
      (-u * v * A + (u ^ 2 - v ^ 2) * B + u * v * C) ^ 2 := by
    dsimp only [d, e]; ring
  have hcost : S₀ * (∑ j, -s * z j ^ 2) +
      (ξ ^ s - η ^ s) * e *
        (∑ j, (z j * w j / 2 - (2 * s + 1) / 4 *
          (b j / a j * z j ^ 2 + a j / b j * w j ^ 2))) +
      S₁ * (∑ j, -s * w j ^ 2) = -Q := by
    have he : (ξ ^ s - η ^ s) * e = 2 * L := by dsimp only [e, L]; ring
    rw [he]
    dsimp only [Q]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    linear_combination hessian_column_coefficients s S₀ S₁ L (a j) (b j) (z j) (w j)
      (ha j).ne' (hb j).ne'
  have heq := spectralAcceleration_decomposition s (∑ j, a j ^ 2) (∑ j, a j * b j)
    (∑ j, b j ^ 2) ξ η d e A B C
    (∑ j, -s * z j ^ 2)
    (∑ j, (z j * w j / 2 - (2 * s + 1) / 4 *
      (b j / a j * z j ^ 2 + a j / b j * w j ^ 2)))
    (∑ j, -s * w j ^ 2) hξη hsum hdiff hoff hunit
  dsimp only at heq
  rw [hd₀, hd₁, hE₀, hE₁, hK] at heq
  change _ = (s + 1) * _ + (s + 1) * H at heq
  rw [hcost] at heq
  change _ ≤ 0
  rw [heq]
  change (s + 1) * (-Q) + (s + 1) * H ≤ 0
  nlinarith [mul_nonneg (by linarith : 0 ≤ s + 1) (sub_nonneg.mpr hbound)]

/- Native differentiation of the actual Schatten trace is connected to the
   complete quadratic metric above; positivity describes only the SPD chart. -/
private theorem Fq_affine_second_nonpos {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2)
    (W V : Matrix (Fin 2) m ℝ) (hW : ∀ b j, 0 < W b j)
    (hoverlap : 0 < gramOffDiagonal q W)
    (hR : (Aq q W * (Aq q W)ᴴ).PosDef) :
    deriv (deriv (fun t : ℝ => Fq q (W + t • V))) 0 ≤ 0 := by
  have hq : 0 < q := by linarith
  let a := fun j => W 0 j ^ (1 / (2 * q))
  let b := fun j => W 1 j ^ (1 / (2 * q))
  let z := fun j => V 0 j / (q * (a j) ^ (2 * q - 1))
  let w := fun j => V 1 j / (q * (b j) ^ (2 * q - 1))
  have ha (j : m) : 0 < a j := Real.rpow_pos_of_pos (hW 0 j) _
  have hb (j : m) : 0 < b j := Real.rpow_pos_of_pos (hW 1 j) _
  have hd₀ : (∑ j, a j ^ 2) = gramDiagonal q W 0 := by
    unfold gramDiagonal
    apply Finset.sum_congr rfl
    intro j _
    exact power_root_sq hq (hW 0 j).le
  have hd₁ : (∑ j, b j ^ 2) = gramDiagonal q W 1 := by
    unfold gramDiagonal
    apply Finset.sum_congr rfl
    intro j _
    exact power_root_sq hq (hW 1 j).le
  have hc : (∑ j, a j * b j) = gramOffDiagonal q W := by
    unfold gramOffDiagonal
    apply Finset.sum_congr rfl
    intro j _
    exact (Real.mul_rpow (hW 0 j).le (hW 1 j).le).symm
  have hR' : (sym2 (gramDiagonal q W 0) (gramOffDiagonal q W) (gramDiagonal q W 1)).PosDef := by
    rw [← rowGram_sym2 hq W (fun b j => (hW b j).le)]
    exact hR
  have hlo := sym2_posDef_low_eigenvalue_pos _ _ _ hR'
  have hdisc : 0 < (gramDiagonal q W 0 - gramDiagonal q W 1) ^ 2 +
      4 * gramOffDiagonal q W ^ 2 := by positivity
  have hderiv := (Fq_affine_second_hasDerivAt hq W V hW hdisc hlo).deriv
  rw [hderiv]
  have hjet₀ (j : m) := normalized_diagonal_jets hq (hW 0 j) (V 0 j)
  have hjet₁ (j : m) := normalized_diagonal_jets hq (hW 1 j) (V 1 j)
  have hjet (j : m) := normalized_offDiagonal_jets hq (hW 0 j) (hW 1 j) (V 0 j) (V 1 j)
  have hv₀ : gramDiagonalVelocity q W V 0 = ∑ j, a j * z j := by
    unfold gramDiagonalVelocity
    exact Finset.sum_congr rfl (fun j _ => (hjet₀ j).1)
  have hv₁ : gramDiagonalVelocity q W V 1 = ∑ j, b j * w j := by
    unfold gramDiagonalVelocity
    exact Finset.sum_congr rfl (fun j _ => (hjet₁ j).1)
  have hv : gramOffDiagonalVelocity q W V = (∑ j, (a j * w j + b j * z j)) / 2 := by
    unfold gramOffDiagonalVelocity
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun j _ => (hjet j).1)
  have hvv₀ : gramDiagonalAcceleration q W V 0 = ∑ j, -(q - 1) * z j ^ 2 := by
    unfold gramDiagonalAcceleration
    exact Finset.sum_congr rfl (fun j _ => (hjet₀ j).2)
  have hvv₁ : gramDiagonalAcceleration q W V 1 = ∑ j, -(q - 1) * w j ^ 2 := by
    unfold gramDiagonalAcceleration
    exact Finset.sum_congr rfl (fun j _ => (hjet₁ j).2)
  have hvv : gramOffDiagonalAcceleration q W V =
      ∑ j, (z j * w j / 2 - (2 * (q - 1) + 1) / 4 *
        (b j / a j * z j ^ 2 + a j / b j * w j ^ 2)) := by
    unfold gramOffDiagonalAcceleration
    apply Finset.sum_congr rfl
    intro j _
    convert (hjet j).2 using 1 <;> dsimp only [a, b, z, w] <;> ring
  rw [hv₀, hv₁, hv, hvv₀, hvv₁, hvv]
  have h := spectralAcceleration_nonpos_of_columns (by linarith : 0 < q - 1)
    (by linarith : q - 1 < 1) a b z w ha hb (by rwa [hc])
    (by rwa [hd₀, hd₁, hc])
  rw [hd₀, hd₁, hc, sub_add_cancel] at h
  exact h

private theorem affine_table_shift (W V : Matrix (Fin 2) m ℝ) (t u : ℝ) :
    W + (u + t) • V = (W + t • V) + u • V := by
  ext b j
  change W b j + (u + t) * V b j = (W b j + t * V b j) + u * V b j
  ring

private theorem Fq_affine_concave {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2)
    (W V : Matrix (Fin 2) m ℝ)
    (hpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ b j, 0 < (W + t • V) b j)
    (hoverlap : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < gramOffDiagonal q (W + t • V))
    (hR : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (Aq q (W + t • V) * (Aq q (W + t • V))ᴴ).PosDef) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun t : ℝ => Fq q (W + t • V)) := by
  have hq : 0 < q := by linarith
  have hcont : Continuous (fun t : ℝ => Fq q (W + t • V)) :=
    (continuous_Fq hq).comp (by fun_prop)
  have hchart (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      0 < (gramDiagonal q (W + t • V) 0 - gramDiagonal q (W + t • V) 1) ^ 2 +
        4 * gramOffDiagonal q (W + t • V) ^ 2 ∧
      0 < (gramDiagonal q (W + t • V) 0 + gramDiagonal q (W + t • V) 1 -
        Real.sqrt ((gramDiagonal q (W + t • V) 0 - gramDiagonal q (W + t • V) 1) ^ 2 +
          4 * gramOffDiagonal q (W + t • V) ^ 2)) / 2 := by
    refine ⟨by have := hoverlap t ht; positivity, ?_⟩
    apply sym2_posDef_low_eigenvalue_pos
    rw [← rowGram_sym2 hq _ (fun b j => (hpos t ht b j).le)]
    exact hR t ht
  refine concaveOn_of_deriv2_nonpos (convex_Icc 0 1) hcont.continuousOn ?_ ?_ ?_
  · intro t ht
    have hc := hchart t (interior_subset ht)
    exact (Fq_affine_hasDerivAt hq W V (hpos t (interior_subset ht)) hc.1 hc.2).differentiableAt.differentiableWithinAt
  · intro t ht
    have hc := hchart t (interior_subset ht)
    have hd := (Fq_affine_second_hasDerivAt hq (W + t • V) V
      (hpos t (interior_subset ht)) hc.1 hc.2).differentiableAt
    have hfun : (fun u : ℝ => Fq q ((W + t • V) + u • V)) =
        (fun u : ℝ => Fq q (W + (u + t) • V)) := by
      funext u
      rw [affine_table_shift]
    rw [hfun] at hd
    have hshift : deriv (fun u : ℝ => Fq q (W + (u + t) • V)) =
        fun u : ℝ => deriv (fun r : ℝ => Fq q (W + r • V)) (u + t) :=
      funext (fun u => deriv_comp_add_const (fun r : ℝ => Fq q (W + r • V)) t u)
    rw [hshift] at hd
    have hd' := (differentiableAt_comp_add_const (a := (0 : ℝ)) (b := t)).mp hd
    have hd'' : DifferentiableAt ℝ (deriv (fun u : ℝ => Fq q (W + u • V))) t := by
      simpa only [zero_add] using hd'
    exact hd''.differentiableWithinAt
  · intro t ht
    have h := Fq_affine_second_nonpos hq1 hq2 (W + t • V) V
      (hpos t (interior_subset ht)) (hoverlap t (interior_subset ht)) (hR t (interior_subset ht))
    have hfun : (fun u : ℝ => Fq q ((W + t • V) + u • V)) =
        (fun u : ℝ => Fq q (W + (u + t) • V)) := by
      funext u
      rw [affine_table_shift]
    rw [hfun] at h
    have hshift : deriv (fun u : ℝ => Fq q (W + (u + t) • V)) =
        fun u : ℝ => deriv (fun r : ℝ => Fq q (W + r • V)) (u + t) :=
      funext (fun u => deriv_comp_add_const (fun r : ℝ => Fq q (W + r • V)) t u)
    rw [hshift, deriv_comp_add_const] at h
    change deriv (deriv (fun u : ℝ => Fq q (W + u • V))) t ≤ 0
    simpa only [zero_add] using h

private theorem regularized_concavity {q ε : ℝ} (hq1 : 1 < q) (hq2 : q < 2)
    (hε : 0 < ε) (W V : Matrix (Fin 2) m ℝ)
    (hW : ∀ b j, 0 ≤ W b j) (hV : ∀ b j, 0 ≤ V b j)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * Fq q (regularizedTable ε W) + t * Fq q (regularizedTable ε V) ≤
      Fq q (regularizedTable ε ((1 - t) • W + t • V)) := by
  have hq : 0 < q := by linarith
  let U := regularizedTable ε W
  let T := regularizedTable ε V
  have heq (u : ℝ) : U + u • (T - U) =
      regularizedTable ε ((1 - u) • W + u • V) := by
    rw [regularizedTable_affine]
    dsimp only [U, T]
    module
  have hnonneg (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      ∀ b j, 0 ≤ ((1 - u) • W + u • V) b j := by
    intro b j
    change 0 ≤ (1 - u) * W b j + u * V b j
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hu.2) (hW b j)) (mul_nonneg hu.1 (hV b j))
  have hpos (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) : ∀ b j, 0 < (U + u • (T - U)) b j := by
    rw [heq]
    exact regularizedTable_pos hε _ (hnonneg u hu)
  have hoverlap (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      0 < gramOffDiagonal q (U + u • (T - U)) := by
    unfold gramOffDiagonal
    apply Finset.sum_pos
    · intro j _
      exact Real.rpow_pos_of_pos (mul_pos (hpos u hu 0 j) (hpos u hu 1 j)) _
    · exact ⟨Sum.inr 0, Finset.mem_univ _⟩
  have hR (u : ℝ) (_hu : u ∈ Set.Icc (0 : ℝ) 1) :
      (Aq q (U + u • (T - U)) * (Aq q (U + u • (T - U)))ᴴ).PosDef := by
    rw [heq]
    exact regularized_gram_posDef hq hε _
  have hc := Fq_affine_concave hq1 hq2 U (T - U) hpos hoverlap hR
  have h := hc.2 (by simp : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (by simp : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (sub_nonneg.mpr ht1) ht0 (by ring)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, zero_smul, add_zero, one_smul,
    add_sub_cancel] at h
  simpa only [heq t] using h

/-- Full nonnegative-cone concavity for every finite column type and every
real 1 < q < 2, including singular, axial, zero and empty boundary tables. -/
theorem concaveOn_Fq {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2) :
    ConcaveOn ℝ {W : Matrix (Fin 2) m ℝ | ∀ b j, 0 ≤ W b j} (Fq q) := by
  have hq : 0 < q := by linarith
  refine ⟨?_, ?_⟩
  · intro W hW V hV a b ha hb _hab i j
    change 0 ≤ a * W i j + b * V i j
    exact add_nonneg (mul_nonneg ha (hW i j)) (mul_nonneg hb (hV i j))
  · intro W hW V hV a b ha hb hab
    have hb1 : b ≤ 1 := by linarith
    have haeq : a = 1 - b := by linarith
    subst a
    have hL : Filter.Tendsto (fun ε : ℝ =>
        (1 - b) * Fq q (regularizedTable ε W) + b * Fq q (regularizedTable ε V))
        (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
        (nhds ((1 - b) * Fq q W + b * Fq q V)) :=
      (((tendsto_regularized_Fq hq W).const_mul (1 - b)).add
        ((tendsto_regularized_Fq hq V).const_mul b)).mono_left nhdsWithin_le_nhds
    have hR : Filter.Tendsto
        (fun ε : ℝ => Fq q (regularizedTable ε ((1 - b) • W + b • V)))
        (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (Fq q ((1 - b) • W + b • V))) :=
      (tendsto_regularized_Fq hq ((1 - b) • W + b • V)).mono_left nhdsWithin_le_nhds
    have hineq : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
        (1 - b) * Fq q (regularizedTable ε W) + b * Fq q (regularizedTable ε V) ≤
          Fq q (regularizedTable ε ((1 - b) • W + b • V)) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact regularized_concavity hq1 hq2 hε W V hW hV hb hb1
    exact le_of_tendsto_of_tendsto hL hR hineq

theorem Fq_add_ge {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2)
    (W V : Matrix (Fin 2) m ℝ) (hW : ∀ b j, 0 ≤ W b j) (hV : ∀ b j, 0 ≤ V b j) :
    Fq q W + Fq q V ≤ Fq q (W + V) := by
  have hq : 0 < q := by linarith
  have h := (concaveOn_Fq hq1 hq2).2 hW hV
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have heq : (1 / 2 : ℝ) • W + (1 / 2 : ℝ) • V = (1 / 2 : ℝ) • (W + V) := by module
  rw [heq, Fq_smul hq (by norm_num) (W + V) (fun b j => add_nonneg (hW b j) (hV b j))] at h
  simp only [smul_eq_mul] at h
  linarith

theorem monotoneOn_Fq {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2)
    (W V : Matrix (Fin 2) m ℝ) (hW : ∀ b j, 0 ≤ W b j)
    (hWV : ∀ b j, W b j ≤ V b j) : Fq q W ≤ Fq q V := by
  have hdiff : ∀ b j, 0 ≤ (V - W) b j := fun b j => sub_nonneg.mpr (hWV b j)
  have h := Fq_add_ge hq1 hq2 W (V - W) hW hdiff
  rw [add_sub_cancel] at h
  exact (le_add_of_nonneg_right (Fq_nonneg q (V - W))).trans h

#print axioms concaveOn_Fq


end D5.S3.Quantum.NormCompression.FinitePowerConcavity
