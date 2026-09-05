/- GID: D5/S3/Weil/ZetaBridge/WeilFullGramUniformRemainder
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/WeilFullGramUniformRemainder
   mirror-E: none(waiver:actual-full-weil-gram-interface)
   anchors: []
   digest: Transport the derived all-coefficients remainder to the existing actual Gram and prove uniform coercivity and exact inertia at every sufficiently large common depth. -/

import D5.S3.Weil.ZetaBridge.WeilFullGramInertia

/-!
# Uniform remainder and eventual coercivity of the actual full Gram

The existing mixed form, actual matrix and spectral index are reused.
A fixed coefficient-uniform error budget below four yields the same strictly
negative margin at every sufficiently large depth. The threshold depends on
the fixed packet; no effective interpolation-conditioning bound is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaBridge.WeilFullGramUniformRemainder

open Filter Matrix
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.ZetaBridge.WeilEvaluationObservableSubspace
open D5.S3.Weil.ZetaBridge.FiniteMixedWeilMajorant
open D5.S3.Weil.ZetaBridge.FiniteEvenWeilOddInterpolation
open D5.S3.Weil.ZetaBridge.FiniteOrbitBurnolPacket
open D5.S3.Weil.ZetaBridge.QuantitativeMultiOrbitWeilNegativeCertificate
open D5.S3.Weil.ZetaBridge.MultiOrbitBurnolUniformRemainder
open D5.S3.Weil.ZetaBridge.SymmetricConvergentOfZetaSummable
open D5.S3.Weil.ZetaBridge.WeilFullGramInertia
open RHLinalg
open scoped BigOperators ComplexConjugate ComplexOrder Matrix Topology

variable {Z : ZeroData} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : FiniteEvenWeilOrbitFrame Z ι)

/-- The derived remainder controls the quadratic of the actual full Gram for
all coefficient vectors, including every cross term. -/
theorem burnol_actual_gram_uniform_remainder
    (P : OrbitBurnolPacket F) (N : ℕ) (a : ι → ℂ) :
    |(star a ⬝ᵥ ((fullWeilGram Z (burnolBasis F P N)) *ᵥ a)).re -
        frameOddTargetQuadratic F a| ≤
      ((1 / 4 : ℝ) ^ (N + 1) * finiteMixedMajorantTotal Z P.killer) *
        finiteComplexEnergy a := by
  rw [fullWeilGram_quadratic]
  exact multiOrbitBurnol_uniform_remainder F P N a

/-- A fixed positive error budget below four gives a uniform negative margin
at every sufficiently large common depth and for every coefficient vector.
The weight floor one is derived from actual analytic multiplicities. -/
theorem eventually_burnolGram_uniform_negative_margin
    (P : OrbitBurnolPacket F) (delta : ℝ)
    (hdelta : 0 < delta) (hdelta4 : delta < 4) :
    0 < 4 - delta ∧
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ a : ι → ℂ,
        (star a ⬝ᵥ ((fullWeilGram Z (burnolBasis F P N)) *ᵥ a)).re ≤
          -(4 - delta) * finiteComplexEnergy a := by
  have hsmall : ∀ᶠ N : ℕ in atTop,
      (1 / 4 : ℝ) ^ (N + 1) * finiteMixedMajorantTotal Z P.killer < delta :=
    (multiOrbitBurnol_error_tendsto_zero F P).eventually (gt_mem_nhds hdelta)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hsmall
  refine ⟨sub_pos.mpr hdelta4, N₀, ?_⟩
  intro N hN a
  have hm (i : ι) : (1 : ℝ) ≤ (Z.multiplicity (F.index i) : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Z.multiplicity_pos (F.index i)))
  have htarget : frameOddTargetQuadratic F a ≤ -4 * finiteComplexEnergy a := by
    simpa only [mul_one] using frameOddTargetQuadratic_le_massFloor F 1 hm a
  have hrem :
      (star a ⬝ᵥ ((fullWeilGram Z (burnolBasis F P N)) *ᵥ a)).re -
          frameOddTargetQuadratic F a ≤
        delta * finiteComplexEnergy a :=
    ((le_abs_self _).trans (burnol_actual_gram_uniform_remainder F P N a)).trans
      (mul_le_mul_of_nonneg_right (le_of_lt (hN₀ N hN))
        (finiteComplexEnergy_nonneg a))
  linarith

/-- After the common threshold, every actual full Gram remains strictly
negative with the exact finite inertia. No additional remainder is assumed. -/
theorem eventually_burnolGram_exact_negative_inertia
    (P : OrbitBurnolPacket F) (delta : ℝ)
    (hdelta : 0 < delta) (hdelta4 : delta < 4) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (-fullWeilGram Z (burnolBasis F P N)).PosDef ∧
      negIndex (fullWeilGram_isHermitian Z (burnolBasis F P N)) = Fintype.card ι := by
  obtain ⟨hmargin, N₀, hN₀⟩ :=
    eventually_burnolGram_uniform_negative_margin F P delta hdelta hdelta4
  refine ⟨N₀, ?_⟩
  intro N hN
  have hnegative : ∀ a : ι → ℂ, a ≠ 0 →
      (zeroSum Z (convolutionSquare
        (finiteWeilLinearCombination a (burnolBasis F P N)))
        (symmetricConvergent_of_zeroData Z (convolutionSquare
          (finiteWeilLinearCombination a (burnolBasis F P N))))).re < 0 := by
    intro a ha
    have hbound := hN₀ N hN a
    rw [fullWeilGram_quadratic] at hbound
    exact lt_of_le_of_lt hbound
      (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hmargin) (finiteComplexEnergy_pos ha))
  exact ⟨neg_fullWeilGram_posDef_of_strictNegative Z (burnolBasis F P N) hnegative,
    fullWeilGram_negIndex_of_strictNegative Z (burnolBasis F P N) hnegative⟩

#print axioms burnol_actual_gram_uniform_remainder
#print axioms eventually_burnolGram_uniform_negative_margin
#print axioms eventually_burnolGram_exact_negative_inertia

end D5.S3.Weil.ZetaBridge.WeilFullGramUniformRemainder
