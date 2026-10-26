/- GID: D5/S3/VertexAlgebra/LatticeHalfFockFiniteCurrentCorrection
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockFiniteCurrentCorrection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual negative-current insertion with every original-source finite triangle. -/

import D5.S3.VertexAlgebra.LatticeHalfFockNegativeCurrentResidue
import D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation

/-! Actual finite triangular correction on the two distinct lattice carriers. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField

open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFockNormalField LatticeHalfFockFiniteCorrection
open LatticeHalfFockOriginalTranslation LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open scoped BigOperators

noncomputable section

private theorem finite_current_triangle_exchange
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (m L : ℕ) (hm : 0 < m) (v : ℕ → V) :
    (∑ s ∈ Finset.range L, halfBinomial (m + s) •
      (∑ n ∈ Finset.range L, if s ≤ n then
        Ring.choose (1 / 2 : ℂ) (n - s) • v n else 0)) =
    ∑ n ∈ Finset.range L,
      ((m : ℂ) * halfBinomial m * halfBinomial n / ((m : ℂ) + (n : ℂ))) • v n := by
  classical
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  have within : n + 1 ≤ L := Finset.mem_range.mp hn
  calc
    _ = ∑ s ∈ Finset.range (n + 1),
        (halfBinomial (m + s) * Ring.choose (1 / 2 : ℂ) (n - s)) • v n := by
      rw [← Finset.sum_subset (Finset.range_mono within)]
      · apply Finset.sum_congr rfl
        intro s hs
        simp only [ite_eq_left (by have := Finset.mem_range.mp hs; omega : s ≤ n),
          smul_smul]
      · intro s hs outside
        have h : ¬ s ≤ n := by
          simp only [Finset.mem_range] at outside
          omega
        simp only [ite_eq_right h, smul_zero]
    _ = _ := by rw [← Finset.sum_smul, halfBinomial_positive_convolution m n hm]

/- proof_shape: correctedField_negative_current_insertion_finite_triangle: content
   admission_basis: escape-witness
   escape_witness: Original-source zero support extends the actual correction to
   every cutoff; finite triangular exchange consumes the scalar convolution and
   the whole-field insertion and complete negative residue identify its operators. -/
/-- Actual negative-current insertion, including zero modes, at every cutoff
    above the frequency bound of the original finite-charge source. -/
theorem correctedField_negative_current_insertion_finite_triangle
    (D : LatticeData) (hu : IsUnit D.G.det) (index : Index D) (b : Carrier D)
    (gamma k : ℤ) (x : ActualTensor D hu) (L : ℕ)
    (cutoff : vectorFrequencyBound D b + 1 ≤ L) :
    let m : ℕ := sourceWeight D index
    (correctedField D hu (neutralMode D index.1 (-(m : ℤ)) b)).coeff
        (-2 * k - gamma - 3) x =
      (∑ j ∈ Finset.range m, halfBinomial j •
        currentResidue D hu index.1 (correctedField D hu b) gamma
          (-(m : ℤ) + (j : ℤ)) (k - (j : ℤ)) x) +
      ∑ s ∈ Finset.range L, halfBinomial (m + s) •
        (∑ n ∈ Finset.range L, if s ≤ n then
          Ring.choose (1 / 2 : ℂ) (n - s) •
            (correctedField D hu (neutralMode D index.1 (n : ℤ) b)).coeff
              (-2 * (k - (m : ℤ) - (n : ℤ)) - gamma - 3) x else 0) := by
  classical
  dsimp only
  let m := sourceWeight D index
  let N := vectorFrequencyBound D b + 1
  let v : ℕ → ActualTensor D hu := fun n =>
    (correctedField D hu (neutralMode D index.1 (n : ℤ) b)).coeff
      (-2 * (k - (m : ℤ) - (n : ℤ)) - gamma - 3) x
  have positive : 0 < m := by simp [m, sourceWeight]
  have vanishes (n : ℕ) (hn : N ≤ n) : v n = 0 := by
    have high : (vectorFrequencyBound D b : ℤ) < (n : ℤ) := by
      dsimp [N] at hn
      omega
    dsimp only [v]
    rw [neutralMode_vanish D index.1 b (n : ℤ) high, map_zero]
    simp
  have extend :
      (∑ n ∈ Finset.range N,
        ((m : ℂ) * halfBinomial m * halfBinomial n / ((m : ℂ) + (n : ℂ))) • v n) =
      ∑ n ∈ Finset.range L,
        ((m : ℂ) * halfBinomial m * halfBinomial n / ((m : ℂ) + (n : ℂ))) • v n := by
    apply Finset.sum_subset (Finset.range_mono cutoff)
    intro n hn outside
    have high : N ≤ n := by simpa only [Finset.mem_range, not_lt] using outside
    rw [vanishes n high, smul_zero]
  have insertion := congrArg
    (fun F : NativeField D hu => F.coeff (-2 * k - gamma - 3) x)
    (correctedField_negative_current_insertion D hu index b)
  simp only [map_add, map_sum, map_smul, Finset.sum_apply, Pi.add_apply,
    Pi.smul_apply, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply] at insertion
  rw [singleton_negative_current_residue] at insertion
  have shifted (n : ℕ) :
      (shiftField D hu (m + n)
        (correctedField D hu (neutralMode D index.1 (n : ℤ) b))).coeff
          (-2 * k - gamma - 3) x = v n := by
    rw [shiftField_coefficient_public]
    dsimp only [v]
    congr 2
    push_cast
    ring
  simp_rw [show sourceWeight D index = m from rfl, shifted] at insertion
  rw [extend] at insertion
  rw [insertion, finite_current_triangle_exchange m L positive v]

end
end D5.S3.VertexAlgebra.LatticeHalfFockCorrectedField
