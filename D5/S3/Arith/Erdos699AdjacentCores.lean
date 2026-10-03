/- GID: D5/S3/Arith/Erdos699AdjacentCores
   generality: G
   mirror-B: D5/B/S3/Arith/Erdos699AdjacentCores
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Coprime adjacent cores satisfy a cubic necessary bound for Erdos 699. -/

/- adjacent_core_numerator_bound
   proof_shape: content
   escape_witness: adjacent_core_product_bound derives a cubic estimate from
     coprime divisibility and the nonnegative polynomial factorization.
   admission_basis: escape-witness
   Direct frozen dependencies: none.
-/

import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Erdos699AdjacentCores

private theorem adjacent_core_product_bound
    (M t R₁ R₂ : ℕ) (ht : 0 < t) (hhalf : 2 * t < M)
    (hcop : R₁.Coprime R₂)
    (hfirst : R₁ ∣ t * (M - t))
    (hsecond : R₂ ∣ t * (M - t) * (M - 2 * t)) :
    108 * (R₁ * R₂) ^ 2 ≤ M ^ 6 := by
  have hmt : 0 < M - t := by omega
  have hmt₂ : 0 < M - 2 * t := by omega
  have hpositive : 0 < t * (M - t) * (M - 2 * t) := by positivity
  have hfirst' : R₁ ∣ t * (M - t) * (M - 2 * t) :=
    dvd_mul_of_dvd_left hfirst _
  have hdiv : R₁ * R₂ ∣ t * (M - t) * (M - 2 * t) :=
    hcop.mul_dvd_of_dvd_of_dvd hfirst' hsecond
  have hle : R₁ * R₂ ≤ t * (M - t) * (M - 2 * t) :=
    Nat.le_of_dvd hpositive hdiv
  have hsub₁ : ((M - t : ℕ) : ℤ) = (M : ℤ) - t := by omega
  have hsub₂ : ((M - 2 * t : ℕ) : ℤ) = (M : ℤ) - 2 * t := by omega
  have hy : 0 ≤ (M : ℤ) - 2 * t := by omega
  have hy_le : (M : ℤ) - 2 * t ≤ M := by omega
  have hy_sq : ((M : ℤ) - 2 * t) ^ 2 ≤ (M : ℤ) ^ 2 :=
    (sq_le_sq₀ hy (by positivity)).2 hy_le
  have hfactor :
      0 ≤ 4 * (M : ℤ) ^ 2 - 3 * ((M : ℤ) - 2 * t) ^ 2 := by
    nlinarith only [hy_sq, sq_nonneg (M : ℤ)]
  -- The discriminant factorization certifies the exact cubic maximum.
  have hidentity :
      4 * ((M : ℤ) ^ 6 -
        108 * ((t : ℤ) * ((M : ℤ) - t) * ((M : ℤ) - 2 * t)) ^ 2) =
        ((M : ℤ) ^ 2 - 3 * ((M : ℤ) - 2 * t) ^ 2) ^ 2 *
          (4 * (M : ℤ) ^ 2 - 3 * ((M : ℤ) - 2 * t) ^ 2) := by ring
  have hsos :
      0 ≤ ((M : ℤ) ^ 2 - 3 * ((M : ℤ) - 2 * t) ^ 2) ^ 2 *
        (4 * (M : ℤ) ^ 2 - 3 * ((M : ℤ) - 2 * t) ^ 2) :=
    mul_nonneg (sq_nonneg _) hfactor
  have hscaled :
      0 ≤ 4 * ((M : ℤ) ^ 6 -
        108 * ((t : ℤ) * ((M : ℤ) - t) * ((M : ℤ) - 2 * t)) ^ 2) := by
    rw [hidentity]
    exact hsos
  have hpoly_int :
      108 * ((t : ℤ) * (((M - t : ℕ) : ℤ)) *
        (((M - 2 * t : ℕ) : ℤ))) ^ 2 ≤ (M : ℤ) ^ 6 := by
    rw [hsub₁, hsub₂]
    nlinarith only [hscaled]
  have hpoly :
      108 * (t * (M - t) * (M - 2 * t)) ^ 2 ≤ M ^ 6 := by
    exact_mod_cast hpoly_int
  calc
    108 * (R₁ * R₂) ^ 2 ≤
        108 * (t * (M - t) * (M - 2 * t)) ^ 2 :=
      Nat.mul_le_mul_left 108 (pow_le_pow_left' hle 2)
    _ ≤ M ^ 6 := hpoly

/-- The adjacent-core congruences force the square form of the `sqrt 3`
cubic bound on the original numerator. -/
theorem adjacent_core_numerator_bound
    (n M t R₁ R₂ δ₁ δ₂ : ℕ)
    (ht : 0 < t) (hhalf : 2 * t < M)
    (hcop : R₁.Coprime R₂)
    (hfirst : R₁ ∣ t * (M - t))
    (hsecond : R₂ ∣ t * (M - t) * (M - 2 * t))
    (hδ₁ : δ₁ ≤ 3) (hδ₂ : δ₂ ≤ 3)
    (hn₁ : n = δ₁ * R₁ + 1) (hn₂ : n = 2 * δ₂ * R₂ + 2) :
    ((n - 1) * (n - 2)) ^ 2 ≤ 3 * M ^ 6 := by
  have hcore := adjacent_core_product_bound M t R₁ R₂ ht hhalf hcop hfirst hsecond
  have hδ : δ₁ * δ₂ ≤ 9 := by
    calc
      δ₁ * δ₂ ≤ 3 * δ₂ := Nat.mul_le_mul_right δ₂ hδ₁
      _ ≤ 3 * 3 := Nat.mul_le_mul_left 3 hδ₂
      _ = 9 := by norm_num
  have hn₁' : n - 1 = δ₁ * R₁ := by omega
  have hn₂' : n - 2 = 2 * δ₂ * R₂ := by omega
  have hδprod : (δ₁ * δ₂) * (R₁ * R₂) ≤ 9 * (R₁ * R₂) :=
    Nat.mul_le_mul_right _ hδ
  have hnprod : (n - 1) * (n - 2) ≤ 18 * (R₁ * R₂) := by
    rw [hn₁', hn₂']
    calc
      δ₁ * R₁ * (2 * δ₂ * R₂) =
          2 * ((δ₁ * δ₂) * (R₁ * R₂)) := by ring
      _ ≤ 2 * (9 * (R₁ * R₂)) := Nat.mul_le_mul_left 2 hδprod
      _ = 18 * (R₁ * R₂) := by ring
  calc
    ((n - 1) * (n - 2)) ^ 2 ≤ (18 * (R₁ * R₂)) ^ 2 :=
      pow_le_pow_left' hnprod 2
    _ = 3 * (108 * (R₁ * R₂) ^ 2) := by ring
    _ ≤ 3 * M ^ 6 := Nat.mul_le_mul_left 3 hcore

#print axioms adjacent_core_numerator_bound

end D5.S3.Arith.Erdos699AdjacentCores
