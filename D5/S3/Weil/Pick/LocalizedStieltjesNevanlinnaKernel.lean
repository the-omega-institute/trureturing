/- GID: D5/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel
   generality: G
   mirror-B: D5/B/S3/Weil/Pick/LocalizedStieltjesNevanlinnaKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Separate positive mass from signed support by comparing an atomic Stieltjes kernel with its coordinate-localized Nevanlinna kernel. -/

import D5.S3.Weil.Pick.HermitianKernelNegativeSquares
import Mathlib.Tactic

/-!
# Localized Stieltjes and Nevanlinna kernels

For a positive atomic mass at a real support coordinate, the ordinary
Nevanlinna kernel reads the mass, while multiplication of the Stieltjes
transform by the spectral coordinate inserts the support sign into the kernel.
-/

/- Library-search and literature audit trail (2026-09-02):
   * Repository searches for `LocalizedStieltjesNevanlinnaKernel`, atomic
     Stieltjes transforms, support-localized Nevanlinna kernels, and the exact
     `z * F(z)` kernel identity found no existing D5 owner.
   * `HermitianKernelNegativeSquares` supplies the repository's canonical
     Hermitian-kernel carrier and negative-squares vocabulary. It is imported
     rather than duplicated.
   * `CayleyNevanlinnaKernelEquivalence` concerns a different Cayley gauge and
     does not supply the Stieltjes support localizer proved here.
   * Pinned Mathlib supplies complex conjugation, totalized inverse, field
     simplification, and ordered-real arithmetic. No new positivity or
     negative-squares abstraction is introduced.
   * The mathematical split follows the generalized Stieltjes convention:
     the Nevanlinna class of `F` controls mass positivity, while the class of
     `z * F(z)` controls the support-localized index. This module proves the
     finite one-atom algebraic bridge only. It does not claim a completed-zeta
     Stieltjes representation or RH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex
open scoped ComplexConjugate

namespace D5.S3.Weil.Pick.LocalizedStieltjesNevanlinnaKernel

open D5.S3.Weil.Pick.HermitianKernelNegativeSquares

/-- The Cauchy feature of a real support coordinate. -/
def stieltjesFeature (support : ℝ) (z : ℂ) : ℂ :=
  ((support : ℂ) - z)⁻¹

/-- A positive-mass atomic Stieltjes transform in the upper-half-plane
normalization `mass / (support - z)`. -/
def atomicStieltjesTransform (mass support : ℝ) (z : ℂ) : ℂ :=
  (mass : ℂ) * stieltjesFeature support z

/-- Multiplication by the spectral coordinate is the first support localizer. -/
def localizedAtomicStieltjesTransform
    (mass support : ℝ) (z : ℂ) : ℂ :=
  z * atomicStieltjesTransform mass support z

/-- The three nonvanishing conditions needed by the literal difference
quotients under Lean's totalized division. -/
def regularStieltjesPair (support : ℝ) (z w : ℂ) : Prop :=
  (support : ℂ) - z ≠ 0 ∧
    (support : ℂ) - star w ≠ 0 ∧
    z - star w ≠ 0

/-- The Nevanlinna difference quotient of the atomic Stieltjes transform. -/
def rawNevanlinnaDifferenceQuotient
    (mass support : ℝ) (z w : ℂ) : ℂ :=
  (atomicStieltjesTransform mass support z -
      star (atomicStieltjesTransform mass support w)) /
    (z - star w)

/-- The Nevanlinna difference quotient after multiplying the transform by the
spectral coordinate. -/
def localizedNevanlinnaDifferenceQuotient
    (mass support : ℝ) (z w : ℂ) : ℂ :=
  (localizedAtomicStieltjesTransform mass support z -
      star (localizedAtomicStieltjesTransform mass support w)) /
    (z - star w)

/-- The rank-one kernel that records atomic mass but not support sign. -/
def atomicMassKernel (mass support : ℝ) : HermitianKernel ℂ where
  value := fun z w =>
    (mass : ℂ) * stieltjesFeature support z *
      star (stieltjesFeature support w)
  conj_symm := by
    intro z w
    simp [mul_comm, mul_left_comm, mul_assoc]

/-- The coordinate-localized rank-one kernel. Its scalar weight is
`mass * support`, so the support sign is visible. -/
def atomicSupportKernel (mass support : ℝ) : HermitianKernel ℂ where
  value := fun z w =>
    ((mass * support : ℝ) : ℂ) * stieltjesFeature support z *
      star (stieltjesFeature support w)
  conj_symm := by
    intro z w
    simp [mul_comm, mul_left_comm, mul_assoc]

/-- A canonical upper-half-plane sample one unit above the support atom. -/
def normalizedUpperSample (support : ℝ) : ℂ :=
  (support : ℂ) + I

/-- The support-localized kernel is exactly the support coordinate times the
ordinary mass kernel. -/
theorem atomic_support_kernel_eq_support_mul_mass_kernel
    (mass support : ℝ) (z w : ℂ) :
    (atomicSupportKernel mass support).value z w =
      (support : ℂ) * (atomicMassKernel mass support).value z w := by
  simp only [atomicSupportKernel, atomicMassKernel]
  push_cast
  ring

/-- The raw Nevanlinna difference quotient is the ordinary atomic mass kernel. -/
theorem raw_nevanlinna_difference_quotient_eq_mass_kernel
    (mass support : ℝ) (z w : ℂ)
    (hregular : regularStieltjesPair support z w) :
    rawNevanlinnaDifferenceQuotient mass support z w =
      (atomicMassKernel mass support).value z w := by
  rcases hregular with ⟨hz, hw, hcross⟩
  have hw' : (support : ℂ) - Complex.conj w ≠ 0 := by
    simpa [Complex.star_def] using hw
  have hcross' : z - Complex.conj w ≠ 0 := by
    simpa [Complex.star_def] using hcross
  simp only [rawNevanlinnaDifferenceQuotient, atomicStieltjesTransform,
    atomicMassKernel, stieltjesFeature, Complex.star_def, map_mul,
    map_inv₀, map_sub, Complex.conj_ofReal]
  field_simp [hz, hw', hcross']
  ring

/-- Multiplying the Stieltjes transform by `z` inserts the support coordinate
into the Nevanlinna kernel. -/
theorem localized_nevanlinna_difference_quotient_eq_support_kernel
    (mass support : ℝ) (z w : ℂ)
    (hregular : regularStieltjesPair support z w) :
    localizedNevanlinnaDifferenceQuotient mass support z w =
      (atomicSupportKernel mass support).value z w := by
  rcases hregular with ⟨hz, hw, hcross⟩
  have hw' : (support : ℂ) - Complex.conj w ≠ 0 := by
    simpa [Complex.star_def] using hw
  have hcross' : z - Complex.conj w ≠ 0 := by
    simpa [Complex.star_def] using hcross
  simp only [localizedNevanlinnaDifferenceQuotient,
    localizedAtomicStieltjesTransform, atomicStieltjesTransform,
    atomicSupportKernel, stieltjesFeature, Complex.star_def, map_mul,
    map_inv₀, map_sub, Complex.conj_ofReal]
  field_simp [hz, hw', hcross']
  ring

private theorem stieltjes_feature_normalized_upper_sample
    (support : ℝ) :
    stieltjesFeature support (normalizedUpperSample support) = I := by
  have hdiff :
      (support : ℂ) - normalizedUpperSample support = -I := by
    simp [normalizedUpperSample]
  rw [stieltjesFeature, hdiff]
  simp

/-- At the adapted upper-half-plane sample, the raw kernel reads exactly the
mass, while the localized kernel reads exactly mass times support. For positive
mass, the localized diagonal is negative exactly at negative support. -/
theorem normalized_diagonal_reads_mass_and_support
    (mass support : ℝ) (hmass : 0 < mass) :
    (atomicMassKernel mass support).value
        (normalizedUpperSample support) (normalizedUpperSample support) =
        (mass : ℂ) ∧
      (atomicSupportKernel mass support).value
        (normalizedUpperSample support) (normalizedUpperSample support) =
        ((mass * support : ℝ) : ℂ) ∧
      ((atomicSupportKernel mass support).value
        (normalizedUpperSample support) (normalizedUpperSample support)).re < 0 ↔
        support < 0 := by
  have hfeature := stieltjes_feature_normalized_upper_sample support
  have hmassValue :
      (atomicMassKernel mass support).value
          (normalizedUpperSample support) (normalizedUpperSample support) =
        (mass : ℂ) := by
    simp only [atomicMassKernel, hfeature]
    simp
  have hsupportValue :
      (atomicSupportKernel mass support).value
          (normalizedUpperSample support) (normalizedUpperSample support) =
        ((mass * support : ℝ) : ℂ) := by
    simp only [atomicSupportKernel, hfeature]
    simp
  refine ⟨hmassValue, hsupportValue, ?_⟩
  rw [hsupportValue]
  simp only [Complex.ofReal_re]
  constructor
  · intro hnegative
    by_contra hsupport
    have hsupportNonneg : 0 ≤ support := le_of_not_gt hsupport
    exact (not_lt_of_ge (mul_nonneg hmass.le hsupportNonneg)) hnegative
  · exact mul_neg_of_pos_of_neg hmass

/-- The hypotheses and both signs are inhabited at one normalized atom. -/
example :
    let mass : ℝ := 2
    let support : ℝ := -3
    ((atomicMassKernel mass support).value
        (normalizedUpperSample support) (normalizedUpperSample support)).re = 2 ∧
      ((atomicSupportKernel mass support).value
        (normalizedUpperSample support) (normalizedUpperSample support)).re < 0 := by
  dsimp only
  have hpackage := normalized_diagonal_reads_mass_and_support 2 (-3) (by norm_num)
  constructor
  · rw [hpackage.1]
    norm_num
  · exact (hpackage.2.2).2 (by norm_num)

#print axioms atomic_support_kernel_eq_support_mul_mass_kernel
#print axioms raw_nevanlinna_difference_quotient_eq_mass_kernel
#print axioms localized_nevanlinna_difference_quotient_eq_support_kernel
#print axioms normalized_diagonal_reads_mass_and_support

end D5.S3.Weil.Pick.LocalizedStieltjesNevanlinnaKernel
