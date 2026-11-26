/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/FourthEnergy
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coercivity of the leading four-copy spectral energy in a tracial C-star algebra. -/

import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Tactic.NoncommRing

/-! The leading trace energy and the dimensionless resolvent correction. -/

namespace RefinedBMV.Tracial

open scoped BigOperators ComplexOrder

variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private theorem trace_mul_re_nonneg
    (τ : A →P[ℂ] ℂ) (hτ : ∀ X Y : A, τ (X * Y) = τ (Y * X))
    {X Y : A} (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    0 ≤ (τ (X * Y)).re := by
  obtain ⟨S, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hX
  have h := τ.map_nonneg (star_right_conjugate_nonneg hY S)
  rw [← hτ (star S) (S * Y), ← mul_assoc] at h
  exact (Complex.nonneg_iff.mp h).1

/-- Retaining all diagonal pairings in a positive Gram sum costs no factor
depending on the number of blocks. -/
theorem trace_sum_squares_le_square_sum
    (τ : A →P[ℂ] ℂ) (hτ : ∀ X Y : A, τ (X * Y) = τ (Y * X))
    (s : Finset ι) (G : ι → A) (hG : ∀ i ∈ s, 0 ≤ G i) :
    ∑ i ∈ s, (τ (G i ^ 2)).re ≤ (τ ((∑ i ∈ s, G i) ^ 2)).re := by
  classical
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum, map_sum, Complex.re_sum]
  apply Finset.sum_le_sum
  intro i hi
  exact Finset.single_le_sum (f := fun j ↦ (τ (G j * G i)).re)
    (fun j hj ↦ trace_mul_re_nonneg τ hτ (hG j hj) (hG i hi)) hi

/-- The weighted fourth moments of the individual columns are controlled
by the fourth moment of the weighted Gram matrix. -/
theorem weighted_columns_fourth_le
    (τ : A →P[ℂ] ℂ) (hτ : ∀ X Y : A, τ (X * Y) = τ (Y * X))
    (s : Finset ι) (C : ι → A) (r : ι → ℝ) (hr : ∀ i ∈ s, 0 ≤ r i) :
    ∑ i ∈ s, r i ^ 2 * (τ ((C i * star (C i)) ^ 2)).re ≤
      (τ ((∑ i ∈ s, ((r i : ℝ) : ℂ) • (C i * star (C i))) ^ 2)).re := by
  have h := trace_sum_squares_le_square_sum τ hτ s
    (fun i ↦ ((r i : ℝ) : ℂ) • (C i * star (C i))) (fun i hi ↦ by
      have hpos := mul_star_self_nonneg ((Real.sqrt (r i) : ℂ) • C i)
      simpa only [star_smul, Complex.star_def, Complex.conj_ofReal, smul_mul_assoc,
        mul_smul_comm, smul_smul, ← Complex.ofReal_mul, Real.mul_self_sqrt (hr i hi)] using hpos)
  simpa only [pow_two, smul_mul_assoc, mul_smul_comm, map_smul, smul_eq_mul,
    Complex.re_ofReal_mul, mul_assoc] using h

/-- The adjacent two-slot pairing leaves a dimension-free positive margin
in the sum of the three leading trace energies. -/
theorem fourth_leading_energy_lower
    (τ : A →P[ℂ] ℂ) (X Y Q : A) {q : ℝ} (hq : 0 ≤ q) :
    (q ^ 2 * (τ (star X * X)).re + (τ (star Y * Y)).re +
      q * (τ (star Q * Q)).re) / 2 ≤
      2 * q ^ 2 * (τ (star X * X)).re + 4 * (τ (star Y * Y)).re +
      2 * q * (τ (star Q * Q)).re +
      2 * q * ((τ (star X * Y)).re + (τ (star Y * X)).re) := by
  let Z : A := (((3 * q : ℝ) : ℂ)) • X + (4 : ℂ) • Y
  have hZ := (Complex.nonneg_iff.mp (τ.map_nonneg (star_mul_self_nonneg Z))).1
  have hY := (Complex.nonneg_iff.mp (τ.map_nonneg (star_mul_self_nonneg Y))).1
  have hQ := mul_nonneg hq
    (Complex.nonneg_iff.mp (τ.map_nonneg (star_mul_self_nonneg Q))).1
  have hZ' : 0 ≤ (3 * q) ^ 2 * (τ (star X * X)).re +
      16 * (τ (star Y * Y)).re +
      12 * q * ((τ (star X * Y)).re + (τ (star Y * X)).re) := by
    have h4 : (4 : ℂ) = ((4 : ℝ) : ℂ) := by norm_num
    simp only [Z, h4, star_add, star_smul, Complex.star_def, Complex.conj_ofReal,
      add_mul, mul_add, smul_mul_assoc, mul_smul_comm, map_add, map_smul, smul_eq_mul,
      Complex.add_re, Complex.re_ofReal_mul] at hZ
    linarith only [hZ]
  linarith only [hZ', hY, hQ]

/-- The resolvent correction to a two-slot divided difference keeps a
copy of the lower spectral operator and can pair with either endpoint. -/
theorem adjacent_resolvent_sandwich_sub
    {𝕜 R : Type*} [CommRing 𝕜] [Ring R] [Algebra 𝕜 R]
    (a b u v : 𝕜) (T E Sₐ Sᵦ : R)
    (ha : Sₐ * (algebraMap 𝕜 R a - T) = 1)
    (hb : (algebraMap 𝕜 R b - T) * Sᵦ = 1) :
    let Rₐ := a • Sₐ
    let Rᵦ := b • Sᵦ
    let J := Sₐ * T * Sᵦ
    u • (Rₐ * E * Rₐ) - v • (Rᵦ * E * Rᵦ) =
      (u - v) • (Rₐ * E * Rₐ) +
        v • ((b - a) • (J * E * Rₐ + Rᵦ * E * J)) := by
  dsimp only
  have hleft : Sₐ * (a • (algebraMap 𝕜 R b - T)) * Sᵦ = a • Sₐ := by
    rw [mul_smul_comm, smul_mul_assoc, mul_assoc, hb, mul_one]
  have hright : Sₐ * (b • (algebraMap 𝕜 R a - T)) * Sᵦ = b • Sᵦ := by
    rw [mul_smul_comm, smul_mul_assoc, ha, one_mul]
  have hmid : a • (algebraMap 𝕜 R b - T) - b • (algebraMap 𝕜 R a - T) =
      (b - a) • T := by
    have hs : a • algebraMap 𝕜 R b = b • algebraMap 𝕜 R a := by
      simp only [Algebra.smul_def, ← map_mul, mul_comm]
    rw [smul_sub, smul_sub, hs, sub_smul]
    abel
  have hres : a • Sₐ - b • Sᵦ = (b - a) • (Sₐ * T * Sᵦ) := by
    rw [← hleft, ← hright, ← sub_mul, ← mul_sub, hmid, mul_smul_comm, smul_mul_assoc]
  calc
    _ = (u - v) • ((a • Sₐ) * E * (a • Sₐ)) +
        v • (((a • Sₐ) - (b • Sᵦ)) * E * (a • Sₐ) +
          (b • Sᵦ) * E * ((a • Sₐ) - (b • Sᵦ))) := by
      simp only [sub_smul, sub_mul, mul_sub, smul_add, smul_sub]
      abel
    _ = _ := by
      simp only [hres, smul_mul_assoc, mul_smul_comm, smul_add]
      rw [smul_comm a (b - a)]


/-- Cyclic transport through three commutators. The terms from commuting
past a resolvent are quartic once its commutator is expanded. The other
terms contain the commutator with the square of the second factor. -/
theorem trace_three_commutator_transport
    {𝕜 A : Type*} [CommRing 𝕜] [Ring A] [Module 𝕜 A]
    (τ : A →ₗ[𝕜] 𝕜) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    (H B U V W : A) :
    let C := H * B - B * H
    let J := H * B ^ 2 - B ^ 2 * H
    2 * τ (B * (C * U * C * V * C * W)) =
      τ (J * U * C * V * C * W - C * U * J * V * C * W +
        C * U * C * V * J * W +
        C * (U * B - B * U) * C * V * C * W -
        C * U * C * (V * B - B * V) * C * W +
        C * U * C * V * C * (W * B - B * W)) := by
  let C := H * B - B * H
  let J := H * B ^ 2 - B ^ 2 * H
  have hJ : J = B * C + C * B := by
    dsimp [J, C]
    noncomm_ring
  change _ = τ (J * U * C * V * C * W - C * U * J * V * C * W +
    C * U * C * V * J * W +
    C * (U * B - B * U) * C * V * C * W -
    C * U * C * (V * B - B * V) * C * W +
    C * U * C * V * C * (W * B - B * W))
  have htel :
      (B * C + C * B) * U * C * V * C * W -
        C * U * (B * C + C * B) * V * C * W +
        C * U * C * V * (B * C + C * B) * W +
        C * (U * B - B * U) * C * V * C * W -
        C * U * C * (V * B - B * V) * C * W +
        C * U * C * V * C * (W * B - B * W) =
      B * (C * U * C * V * C * W) + (C * U * C * V * C * W) * B := by
    noncomm_ring
  rw [hJ, htel, map_add, ← hτ]
  ring


end RefinedBMV.Tracial
