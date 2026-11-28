/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFullEnergySpectrum
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The exact point spectrum and exclusion of integral eigenvalues for P48q twisted state energy. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedStateEnergy

/-!
The algebraic point spectrum of the constructed P48q order-three energy
operator `P48qTwistedStateEnergy.totalLZero` on its state carrier.
-/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFullEnergySpectrum

open LatticeGeneratingFieldLocality (Charge bilinear lowerCocycleExponent)
open LatticeTwistedGroundRealization.SignQuotient (integral_cocycle_symmetrization)
open P48qThirdTwistedField (Mode State frequency)
open P48qTwistedChargeAction (Momentum lattice g g_cube g_isometry)
open P48qTwistedStateEnergy (Occupation momentumWeight momentumWeight_nonneg
  momentumWeight_zero occupationFrequency totalLZero totalLZero_eigenvalues totalWeight)
open ThirdTwistedChargeAction (N bShift q three_mul_bShift)

/-- The squared integral norm of each momentum numerator is divisible by six. -/
theorem six_dvd_momentumNorm (p : Momentum) : (6 : ℤ) ∣ bilinear lattice p.1 p.1 := by
  obtain ⟨a, ha⟩ : ∃ a : Charge lattice, N lattice g a = p.1 := p.2
  rw [← ha]
  let m := lowerCocycleExponent lattice a a
  have heven : bilinear lattice a a = m + m :=
    (integral_cocycle_symmetrization lattice a a).symm
  have hshift := three_mul_bShift lattice g g_cube g_isometry a
  simp only [bShift, heven, Int.cast_add] at hshift
  refine ⟨3 * m + q lattice g a, ?_⟩
  have hnorm : (bilinear lattice (N lattice g a) (N lattice g a) : ℚ) =
      6 * (3 * (m : ℚ) + (q lattice g a : ℚ)) := by
    linarith only [hshift]
  exact_mod_cast hnorm

/-- Each momentum weight is a nonnegative integral multiple of `1 / 3`. -/
theorem momentumWeight_eq_nat_div_three (p : Momentum) :
    ∃ n : ℕ, momentumWeight p = (n : ℝ) / 3 := by
  obtain ⟨k, hk⟩ := six_dvd_momentumNorm p
  have hweight : momentumWeight p = (k : ℝ) / 3 := by
    rw [momentumWeight, hk, Int.cast_mul, Int.cast_ofNat]
    ring
  have hkReal : (0 : ℝ) ≤ (k : ℝ) := by
    have hnonneg := momentumWeight_nonneg p
    rw [hweight] at hnonneg
    linarith only [hnonneg]
  have hkNonneg : 0 ≤ k := by exact_mod_cast hkReal
  refine ⟨k.toNat, ?_⟩
  rwa [← Int.cast_natCast, Int.toNat_of_nonneg hkNonneg]

/-- The point spectrum consists exactly of `16 / 9 + n / 3` for `n : ℕ`. -/
theorem totalLZero_exact_eigenvalues (a : ℂ) :
    (∃ v : State, v ≠ 0 ∧ totalLZero v = a • v) ↔
      ∃ n : ℕ, a = 16 / 9 + (n : ℂ) / 3 := by
  rw [totalLZero_eigenvalues]
  constructor
  · rintro ⟨p, d, ha⟩
    obtain ⟨m, hm⟩ := momentumWeight_eq_nat_div_three p
    have hweight : totalWeight p d =
        16 / 9 + ((occupationFrequency d + m : ℕ) : ℝ) / 3 := by
      rw [totalWeight, hm, Nat.cast_add]
      ring
    refine ⟨occupationFrequency d + m, ha.trans ?_⟩
    simpa only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_ofNat,
      Complex.ofReal_natCast] using congrArg (fun x : ℝ => (x : ℂ)) hweight
  · rintro ⟨n, rfl⟩
    let d : Occupation := Finsupp.single (0, 0) n
    have hd : occupationFrequency d = n := by
      calc
        occupationFrequency d = frequency ((0, 0) : Mode) * n :=
          Finsupp.sum_single_index (a := ((0, 0) : Mode)) (b := n)
            (h := fun j e => frequency j * e) (mul_zero _)
        _ = n := one_mul n
    refine ⟨0, d, ?_⟩
    simp only [totalWeight, hd, momentumWeight_zero, add_zero, Complex.ofReal_add,
      Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_natCast]

/-- The constructed operator has no eigenvalue in the image of `ℤ` in `ℂ`. -/
theorem totalLZero_no_integral_eigenvalue (z : ℤ) :
    ¬ ∃ v : State, v ≠ 0 ∧ totalLZero v = (z : ℂ) • v := by
  intro heigen
  obtain ⟨n, hn⟩ := (totalLZero_exact_eigenvalues (z : ℂ)).mp heigen
  have hreal : (z : ℝ) = 16 / 9 + (n : ℝ) / 3 := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_intCast, Complex.ofReal_add, Complex.ofReal_div,
      Complex.ofReal_ofNat, Complex.ofReal_natCast] using hn
  have hscaled : (9 : ℝ) * (z : ℝ) = 16 + 3 * (n : ℝ) := by
    linarith only [hreal]
  have hint : (9 : ℤ) * z = 16 + 3 * (n : ℤ) := by exact_mod_cast hscaled
  have hmod : (0 : ℤ) = 1 := calc
    0 = (9 * z) % 3 := by rw [show 9 * z = 3 * (3 * z) by ring, Int.mul_emod_right]
    _ = (16 + 3 * (n : ℤ)) % 3 := congrArg (fun k : ℤ => k % 3) hint
    _ = 1 := (Int.add_mul_emod_self_left 16 3 (n : ℤ)).trans (by decide)
  exact zero_ne_one hmod

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFullEnergySpectrum
