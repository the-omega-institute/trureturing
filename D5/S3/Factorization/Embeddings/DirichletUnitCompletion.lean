/- GID: D5/S3/Factorization/Embeddings/DirichletUnitCompletion
   generality: G
   mirror-B: D5/B/S3/Factorization/Embeddings/DirichletUnitCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Dirichlet coordinates give rational sign degeneration and quadratic ranks. -/
/- Library-search audit trail (2026-08-25):
   * Repository searches for `NumberField.Units.dirichletUnitTheorem`, `Units.torsion`,
     `NumberField.InfinitePlace`, and `NumberField.mixedEmbedding` found no applicable D5 module.
   * `RationalValuationRecovery.lean` supplies the concrete finite profile, sign recovery, and
     named necessity witnesses; `RationalFiniteValuationKernel.lean` and
     `PositiveRationalGroup.lean` were inspected but are not needed by this module.
   * Pinned Mathlib's `Units/DirichletTheorem.lean` makes `dirichletUnitTheorem` a namespace,
     not one theorem. Its `rank`, `basisModTorsion`, `fundSystem`, `Module.Free` instance, and
     `exist_unique_eq_mul_prod` were exact hits; the last theorem is used for the group splitting.
   * Pinned Mathlib's `Units.torsion`, `torsion_eq_one_or_neg_one_of_odd_finrank`,
     `InfinitePlace.nrRealPlaces`, `nrComplexPlaces`, and the unique rational infinite place are
     reused. `mixedEmbedding` is not needed because `logEmbedding` and its lattice basis already
     expose the required archimedean integer coordinates. -/

import D5.S3.Factorization.Embeddings.RationalValuationRecovery
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators

open NumberField NumberField.InfinitePlace NumberField.Units
open D5.S3.Factorization.Embeddings.RationalValuationRecovery

namespace D5.S3.Factorization.Embeddings.DirichletUnitCompletion

/-- Integer coordinates in the logarithmic unit lattice. -/
abbrev ArchimedeanLatticeCoordinates (K : Type*) [Field K] [NumberField K] :=
  Fin (Units.rank K) → ℤ

/-- The two residual unit layers: root-of-unity torsion and archimedean lattice coordinates. -/
abbrev UnitCompletionCoordinates (K : Type*) [Field K] [NumberField K] :=
  Units.torsion K × Multiplicative (ArchimedeanLatticeCoordinates K)

/-- Reconstruct a unit from its torsion coordinate and fundamental-unit exponents. -/
noncomputable def unitCompletionReconstruction (K : Type*) [Field K] [NumberField K] :
    UnitCompletionCoordinates K →* (𝓞 K)ˣ where
  toFun coordinates :=
    coordinates.1 * ∏ i, (Units.fundSystem K i) ^ (coordinates.2.toAdd i)
  map_one' := by
    simp
  map_mul' first second := by
    change
      (first.1 * second.1) *
          ∏ i, (Units.fundSystem K i) ^ (first.2.toAdd i + second.2.toAdd i) =
        (first.1 * ∏ i, (Units.fundSystem K i) ^ (first.2.toAdd i)) *
          (second.1 * ∏ i, (Units.fundSystem K i) ^ (second.2.toAdd i))
    simp only [zpow_add, Finset.prod_mul_distrib]
    ac_rfl

/-- Dirichlet's unit rank is `r₁ + r₂ - 1`; prime distribution plays no role here. -/
theorem unit_rank_eq_real_add_complex_sub_one (K : Type*) [Field K] [NumberField K] :
    Units.rank K = nrRealPlaces K + nrComplexPlaces K - 1 := by
  rw [Units.rank, card_eq_nrRealPlaces_add_nrComplexPlaces]
#print axioms unit_rank_eq_real_add_complex_sub_one

/-- Dirichlet's unique unit decomposition makes two-layer reconstruction bijective. -/
theorem unitCompletionReconstruction_bijective (K : Type*) [Field K] [NumberField K] :
    Function.Bijective (unitCompletionReconstruction K) := by
  constructor
  · intro first second hsame
    let first' : Units.torsion K × (Fin (Units.rank K) → ℤ) :=
      (first.1, first.2.toAdd)
    let second' : Units.torsion K × (Fin (Units.rank K) → ℤ) :=
      (second.1, second.2.toAdd)
    have hfirst :
        unitCompletionReconstruction K first =
          first'.1 * ∏ i, (Units.fundSystem K i) ^ (first'.2 i) := by
      rfl
    have hsecond :
        unitCompletionReconstruction K first =
          second'.1 * ∏ i, (Units.fundSystem K i) ^ (second'.2 i) := by
      rw [hsame]
      rfl
    have hpairs : first' = second' :=
      (Units.exist_unique_eq_mul_prod K (unitCompletionReconstruction K first)).unique
        hfirst hsecond
    apply Prod.ext
    · exact congrArg Prod.fst hpairs
    · exact congrArg Prod.snd hpairs
  · intro unit
    obtain ⟨coordinates, hcoordinates, -⟩ := Units.exist_unique_eq_mul_prod K unit
    exact ⟨(coordinates.1, Multiplicative.ofAdd coordinates.2), hcoordinates.symm⟩
#print axioms unitCompletionReconstruction_bijective

/-- The unit group is the product of root-of-unity torsion and a free integer lattice. -/
noncomputable def unitCompletionMulEquiv (K : Type*) [Field K] [NumberField K] :
    (𝓞 K)ˣ ≃* UnitCompletionCoordinates K :=
  (MulEquiv.ofBijective (unitCompletionReconstruction K)
    (unitCompletionReconstruction_bijective K)).symm

/-- The rational number field has signature `(r₁, r₂) = (1, 0)`. -/
theorem rational_archimedean_signature :
    nrRealPlaces ℚ = 1 ∧ nrComplexPlaces ℚ = 0 := by
  constructor
  · exact nrRealPlaces_eq_one_of_finrank_eq_one (by simp)
  · exact nrComplexPlaces_eq_zero_of_finrank_eq_one (by simp)
#print axioms rational_archimedean_signature

/-- Consequently the free archimedean unit lattice of the rationals has rank zero. -/
theorem rational_unit_rank_zero : Units.rank ℚ = 0 := by
  rw [unit_rank_eq_real_add_complex_sub_one]
  norm_num [rational_archimedean_signature.1, rational_archimedean_signature.2]
#print axioms rational_unit_rank_zero

/-- Every rational root-of-unity coordinate is exactly `1` or `-1`. -/
theorem rational_torsion_unit_eq_one_or_neg_one (root : Units.torsion ℚ) :
    (root : (𝓞 ℚ)ˣ) = 1 ∨ (root : (𝓞 ℚ)ˣ) = -1 := by
  exact Units.torsion_eq_one_or_neg_one_of_odd_finrank (by simp) root
#print axioms rational_torsion_unit_eq_one_or_neg_one

/-- With a fixed finite-valuation profile, rational recovery is exactly one sign bit.

Unlike the profile-only kernel theorem, this full statement needs no nonzero hypotheses: the
zero sign already distinguishes zero from every nonzero rational.
-/
theorem rational_two_layer_recovery_iff_sign {x y : ℚ}
    (sameFiniteProfile : rationalFiniteValuationProfile x = rationalFiniteValuationProfile y) :
    x = y ↔ SignType.sign x = SignType.sign y := by
  constructor
  · intro hxy
    rw [hxy]
  · intro sameSign
    by_cases hx : x = 0
    · subst x
      have hy : y = 0 := sign_eq_zero_iff.mp (by simpa using sameSign.symm)
      exact hy.symm
    · by_cases hy : y = 0
      · subst y
        exact (hx (sign_eq_zero_iff.mp (by simpa using sameSign))).elim
      · exact rational_recovered_from_sign_and_finite_valuations hx hy
          sameFiniteProfile sameSign
#print axioms rational_two_layer_recovery_iff_sign

/-- A signature `(0, 1)` number field, hence an imaginary quadratic field, has unit rank zero. -/
theorem imaginary_quadratic_unit_rank_zero
    (K : Type*) [Field K] [NumberField K]
    (noRealPlaces : nrRealPlaces K = 0) (oneComplexPlace : nrComplexPlaces K = 1) :
    Units.rank K = 0 := by
  rw [unit_rank_eq_real_add_complex_sub_one, noRealPlaces, oneComplexPlace]
#print axioms imaginary_quadratic_unit_rank_zero

/-- In the imaginary quadratic case every unit lies in the root-of-unity torsion subgroup. -/
theorem imaginary_quadratic_units_are_torsion
    (K : Type*) [Field K] [NumberField K]
    (noRealPlaces : nrRealPlaces K = 0) (oneComplexPlace : nrComplexPlaces K = 1)
    (unit : (𝓞 K)ˣ) : unit ∈ Units.torsion K := by
  obtain ⟨coordinates, hunit, -⟩ := Units.exist_unique_eq_mul_prod K unit
  have hrank := imaginary_quadratic_unit_rank_zero K noRealPlaces oneComplexPlace
  have hproduct : ∏ i, (Units.fundSystem K i) ^ (coordinates.2 i) = 1 := by
    apply Finset.prod_eq_one
    intro i _
    have : i.val < 0 := by simpa [hrank] using i.isLt
    omega
  rw [hproduct] at hunit
  rw [hunit]
  simpa only [mul_one] using coordinates.1.property
#print axioms imaginary_quadratic_units_are_torsion

/-- A signature `(2, 0)` number field, hence a real quadratic field, has unit rank one. -/
theorem real_quadratic_unit_rank_one
    (K : Type*) [Field K] [NumberField K]
    (twoRealPlaces : nrRealPlaces K = 2) (noComplexPlaces : nrComplexPlaces K = 0) :
    Units.rank K = 1 := by
  rw [unit_rank_eq_real_add_complex_sub_one, twoRealPlaces, noComplexPlaces]
#print axioms real_quadratic_unit_rank_one

/-- The sole member of the fundamental system in a real quadratic field. -/
noncomputable def realQuadraticFundamentalUnit
    (K : Type*) [Field K] [NumberField K]
    (twoRealPlaces : nrRealPlaces K = 2) (noComplexPlaces : nrComplexPlaces K = 0) :
    (𝓞 K)ˣ :=
  Units.fundSystem K ⟨0, by
    rw [real_quadratic_unit_rank_one K twoRealPlaces noComplexPlaces]
    omega⟩

/-- Every real quadratic unit is torsion times an integer power of its fundamental unit. -/
theorem real_quadratic_unit_decomposition
    (K : Type*) [Field K] [NumberField K]
    (twoRealPlaces : nrRealPlaces K = 2) (noComplexPlaces : nrComplexPlaces K = 0)
    (unit : (𝓞 K)ˣ) :
    ∃ root : Units.torsion K, ∃ exponent : ℤ,
      unit = root * realQuadraticFundamentalUnit K twoRealPlaces noComplexPlaces ^ exponent := by
  obtain ⟨coordinates, hunit, -⟩ := Units.exist_unique_eq_mul_prod K unit
  let index : Fin (Units.rank K) :=
    ⟨0, by
      rw [real_quadratic_unit_rank_one K twoRealPlaces noComplexPlaces]
      omega⟩
  refine ⟨coordinates.1, coordinates.2 index, ?_⟩
  rw [hunit]
  congr 1
  have hindex : ∀ i : Fin (Units.rank K), i = index := by
    intro i
    apply Fin.ext
    change i.val = 0
    have hi : i.val < 1 := by
      simpa [real_quadratic_unit_rank_one K twoRealPlaces noComplexPlaces] using i.isLt
    omega
  rw [show (Finset.univ : Finset (Fin (Units.rank K))) = {index} by
    ext i
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact hindex i]
  simp only [Finset.prod_singleton]
  congr 2
#print axioms real_quadratic_unit_decomposition

end D5.S3.Factorization.Embeddings.DirichletUnitCompletion
