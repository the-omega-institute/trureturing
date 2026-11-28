/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdCoverCurrentCoordinates
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Normalized integral and complementary oscillator coordinates for the third cover. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdCoverComplement

set_option autoImplicit false

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdCoverIntegerFactor

open MvPolynomial PolynomialFockSugawaraSupport
open scoped TensorProduct

/-- The normalized cover mode acts by the ordinary mode on every pure tensor. -/
theorem normalizedMode_join_tmul {s : ℂ} (hsq : s ^ 2 = 3) (r : ℤ)
    (P : Fock) (Q : ComplementFock) :
    Lattice.Orbifold.ThirdCoverVirasoro.current s⁻¹ (3 * r)
      (join s (ne_zero_of_sq_eq_three hsq) (P ⊗ₜ[ℂ] Q)) =
      join s (ne_zero_of_sq_eq_three hsq) (mode r P ⊗ₜ[ℂ] Q) := by
  rw [Lattice.Orbifold.ThirdCoverVirasoro.current, LinearMap.smul_apply, mode_join_tmul hsq,
    smul_smul, inv_mul_cancel₀ (ne_zero_of_sq_eq_three hsq), one_smul]

/-- The mode intertwiner as an equality of endomorphisms on the full tensor product. -/
theorem split_normalizedMode {s : ℂ} (hsq : s ^ 2 = 3) (r : ℤ) :
    (split s (ne_zero_of_sq_eq_three hsq)).toLinearEquiv.conj
      (Lattice.Orbifold.ThirdCoverVirasoro.current s⁻¹ (3 * r)) =
      TensorProduct.map (mode r) LinearMap.id := by
  apply TensorProduct.ext'
  intro P Q
  change split s _ (Lattice.Orbifold.ThirdCoverVirasoro.current s⁻¹ (3 * r)
    (join s _ (P ⊗ₜ[ℂ] Q))) = _
  rw [normalizedMode_join_tmul hsq, TensorProduct.map_tmul, LinearMap.id_apply]
  exact (join s _).symm_apply_apply _

end D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdCoverIntegerFactor

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdCoverComplement

open ThirdCoverIntegerFactor

/-- In normalized current coordinates the coefficient of the normal-ordered sum
is one half, and only pairs from the two complementary residue grids occur. -/
theorem fractionalVirasoro_apply (m : ℤ) (Q : ComplementFock) :
    fractionalVirasoro m Q =
      (2 : ℂ)⁻¹ • (∑ᶠ k ∈ {k : ℤ | ¬ (3 : ℤ) ∣ k},
        (if k ≤ 3 * m - k then fractionalCurrent k * fractionalCurrent (3 * m - k)
          else fractionalCurrent (3 * m - k) * fractionalCurrent k) Q) +
        (if m = 0 then (1 / 9 : ℂ) else 0) • Q := by
  have hterm (i j : ℤ) :
      (if j ≤ i then fractionalCurrent j * fractionalCurrent i
        else fractionalCurrent i * fractionalCurrent j) =
        (3 : ℂ)⁻¹ • complementPair i j := by
    by_cases h : j ≤ i
    · simp only [fractionalCurrent, complementPair, ite_eq_left h, Algebra.smul_mul_assoc,
        Algebra.mul_smul_comm, smul_smul, inverse_scale_sq, Module.End.mul_eq_comp]
    · simp only [fractionalCurrent, complementPair, ite_eq_right h, Algebra.smul_mul_assoc,
        Algebra.mul_smul_comm, smul_smul, inverse_scale_sq, Module.End.mul_eq_comp]
  change (3 : ℂ)⁻¹ • ((2 : ℂ)⁻¹ •
    ∑ᶠ k ∈ integerIndicesᶜ, complementPair (3 * m - k) k Q) +
      (if m = 0 then (1 / 9 : ℂ) else 0) • Q = _
  simp only [hterm, LinearMap.smul_apply]
  have hsum :
      (3 : ℂ)⁻¹ • (∑ᶠ k ∈ integerIndicesᶜ, complementPair (3 * m - k) k Q) =
        ∑ᶠ k ∈ integerIndicesᶜ, (3 : ℂ)⁻¹ • complementPair (3 * m - k) k Q := by
    simpa only [DistribSMul.toAddMonoidHom_apply] using
      (DistribSMul.toAddMonoidHom ComplementFock (3 : ℂ)⁻¹).map_finsum_mem'
        (complementPair_finiteSupport m Q)
  change _ = (2 : ℂ)⁻¹ • (∑ᶠ k ∈ integerIndicesᶜ, (3 : ℂ)⁻¹ •
    complementPair (3 * m - k) k Q) + (if m = 0 then (1 / 9 : ℂ) else 0) • Q
  rw [← hsum, smul_comm (3 : ℂ)⁻¹ (2 : ℂ)⁻¹]

end D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdCoverComplement
