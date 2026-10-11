/- GID: D5/S3/VertexAlgebra/RationalCollision
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/RationalCollision
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full fixed-denominator collision for every integer and remaining exponent. -/

/-
Full fixed-denominator collision for every integer and remaining exponent.

The proof uses the native mathlib Hahn/Laurent and polynomial kernels.
LaurentSeries: Aaron Anderson, María Inés de Frutos-Fernández, Filippo A. E. Nuccio;
HahnSeries: Aaron Anderson; partial fractions: Kevin Buzzard, Sidharth Hariharan,
Aaron Liu. These library sources are released under Apache 2.0.
Actual HVertexOperator and VertexOperator composition: Scott Carnahan, Apache 2.0.
The imported normal-product supplier attributes its adaptation to Carnahan's
vertexAlg revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea (Apache 2.0).
No actual Monster carrier or fused-state identification is asserted.
-/

import D5.S3.VertexAlgebra.LabelledRationalClearing
import D5.S3.VertexAlgebra.OrderedCollisionCoordinates
import D5.S3.VertexAlgebra.OrderedCollisionResidues

noncomputable section
namespace D5.S3.VertexAlgebra

section
/- The derived normal form of the actual weighted global P/Q is expanded in
both complete Hahn orders. The same q and rational coefficient c are shared.
Division by Q always precedes any spectator coefficient extraction. -/
namespace RationalCollision.FullOrderNormalForm
open CollisionRationalExpansions.OrderedRationalExpansion LabelledRationalClearing.GlobalRationalCurry LabelledRationalClearing.PairDifferenceLocalization
open OrderedCollisionCoordinates.OrderedCoefficientCompatibility OrderedCollisionCoordinates.AdjacentFullOrders LabelledRationalClearing.ActualClearingPartialFractions
open LabelledRationalClearing.WeightedActualQ LabelledRationalClearing.WeightedNormalFormConstants LabelledRationalClearing.GlobalRationalUncurry
open CollisionRationalExpansions.HahnFiberScalar CollisionRationalExpansions.FullOrderSpectatorScalar
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable (K : Type*) [Field K] {N : ℕ} (z : Fin N)

theorem uncurry_constant (h : CoefficientField K z) :
    uncurryRational K z (RatFunc.C h) = LabelledRationalClearing.GlobalRationalUncurry.coefficient K z h := by
  rw [← RatFunc.algebraMap_C, uncurryRational, IsFractionRing.lift_algebraMap]
  simp [LabelledRationalClearing.GlobalRationalUncurry.polynomial]

def globalPole (p : LabelledPair N) : CommonRational K N :=
  uncurryRational K z (algebraMap _ (RatFunc (CoefficientField K z)) (pairPole K z p))

theorem global_weighted_normal_form (x : Remaining z) (P : LabelledPolynomial K N)
    (k : ℕ) (r : ℤ) (hP : ∀ e ∈ P.coeff.support, 0 ≤ e z) :
    ∃ (q : Polynomial (CoefficientField K z))
      (c : (p : LabelledPair N) → Fin (weightedOrders z x k r p) → CoefficientField K z),
      globalDiagonal K z x ^ r * (algebraMap _ (CommonRational K N) P /
        algebraMap _ (CommonRational K N) (clearingPolynomial K N k)) =
      uncurryRational K z (algebraMap _ (RatFunc (CoefficientField K z)) q) +
        ∑ p, ∑ j, LabelledRationalClearing.GlobalRationalUncurry.coefficient K z (c p j) *
          (globalPole K z p)⁻¹ ^ (j.val + 1) := by
  classical
  obtain ⟨q, c, he⟩ := weighted_actual_normal_form K z x P k r hP
  refine ⟨q, c, ?_⟩
  have hu := congrArg (uncurryRational K z) he
  simpa only [uncurry_curry, map_add, map_sum, map_mul, map_pow, map_inv₀,
    uncurry_constant, globalPole] using hu

variable (pre post : ℕ) (z : Fin ((pre + 2) + post))
  (tau : Fin ((pre + 1) + post) ≃ Remaining z)

theorem coefficient_models_agree (h : CoefficientField K z) :
    LabelledRationalClearing.GlobalRationalUncurry.coefficient K z h = coefficientGlobal K (pre + 1) post z h := rfl

theorem first_constant (h : CoefficientField K z) :
    firstRational K pre post z tau (LabelledRationalClearing.GlobalRationalUncurry.coefficient K z h) =
      firstEmbed pre post (coefficientHahn K (pre + 1) post z tau h) := by
  rw [coefficient_models_agree, first_coefficient_square]

theorem second_constant (h : CoefficientField K z) :
    secondRational K pre post z tau (LabelledRationalClearing.GlobalRationalUncurry.coefficient K z h) =
      embedRemaining (pre + 1) post (coefficientHahn K (pre + 1) post z tau h) := by
  rw [coefficient_models_agree]
  exact coefficient_expansion_square K (pre + 1) post z tau h

/-- Both genuine full expansions of the same weighted global correlator have
the derived allowed-pole normal form with fully ordered coefficient expansions. -/
theorem both_full_order_normal_forms (x : Remaining z)
    (P : LabelledPolynomial K ((pre + 2) + post)) (k : ℕ) (r : ℤ)
    (hP : ∀ e ∈ P.coeff.support, 0 ≤ e z) :
    ∃ (q : Polynomial (CoefficientField K z))
      (c : (p : LabelledPair ((pre + 2) + post)) → Fin (weightedOrders z x k r p) → CoefficientField K z),
      (firstRational K pre post z tau (globalDiagonal K z x ^ r * globalCorrelator K pre post P k) =
        firstRational K pre post z tau (uncurryRational K z (algebraMap _ (RatFunc (CoefficientField K z)) q)) +
          ∑ p, ∑ j, firstEmbed pre post (coefficientHahn K (pre + 1) post z tau (c p j)) *
            (firstRational K pre post z tau (globalPole K z p))⁻¹ ^ (j.val + 1)) ∧
      (secondRational K pre post z tau (globalDiagonal K z x ^ r * globalCorrelator K pre post P k) =
        secondRational K pre post z tau (uncurryRational K z (algebraMap _ (RatFunc (CoefficientField K z)) q)) +
          ∑ p, ∑ j, embedRemaining (pre + 1) post (coefficientHahn K (pre + 1) post z tau (c p j)) *
            (secondRational K pre post z tau (globalPole K z p))⁻¹ ^ (j.val + 1)) := by
  classical
  obtain ⟨q, c, he⟩ := global_weighted_normal_form K z x P k r hP
  refine ⟨q, c, ?_, ?_⟩
  · change firstRational K pre post z tau (globalDiagonal K z x ^ r *
      (algebraMap _ (CommonRational K _) P / algebraMap _ (CommonRational K _) (clearingPolynomial K _ k))) = _
    rw [he]
    simp only [map_add, map_sum, map_mul, map_pow, map_inv₀, first_constant]
  · change secondRational K pre post z tau (globalDiagonal K z x ^ r *
      (algebraMap _ (CommonRational K _) P / algebraMap _ (CommonRational K _) (clearingPolynomial K _ k))) = _
    rw [he]
    simp only [map_add, map_sum, map_mul, map_pow, map_inv₀, second_constant]

end RationalCollision.FullOrderNormalForm
end

section
/- The monic poles in the derived normal form are attached to actual labels.
The original i<j signs remain in clearingScalar and hence in q and c. -/
namespace RationalCollision.ActualGlobalPoleOrientation
open CollisionRationalExpansions.OrderedRationalExpansion LabelledRationalClearing.GlobalRationalCurry LabelledRationalClearing.PairDifferenceLocalization
open LabelledRationalClearing.ActualClearingPartialFractions RationalCollision.FullOrderNormalForm LabelledRationalClearing.GlobalRationalUncurry
set_option backward.isDefEq.respectTransparency false
variable (K : Type*) [Field K] {N : ℕ} (z : Fin N)

theorem globalPole_left (p : LabelledPair N) (h : p.val.1 = z) :
    globalPole K z p = algebraMap _ (CommonRational K N)
      (pairPolynomial K z p.val.2) := by
  apply (curryRational K z).injective
  rw [globalPole, curry_uncurry]
  simp only [curryRational, IsFractionRing.lift_algebraMap]
  rw [pairPole, dif_pos h]
  exact (curry_pair_left K z ⟨p.val.2, by simpa [← h] using p.property.ne.symm⟩).symm

theorem globalPole_right (p : LabelledPair N) (h : p.val.2 = z) :
    globalPole K z p = algebraMap _ (CommonRational K N)
      (pairPolynomial K z p.val.1) := by
  have h' : p.val.1 ≠ z := by simpa [← h] using p.property.ne
  apply (curryRational K z).injective
  rw [globalPole, curry_uncurry]
  simp only [curryRational, IsFractionRing.lift_algebraMap]
  rw [pairPole, dif_neg h', dif_pos h]
  exact (curry_pair_left K z ⟨p.val.1, h'⟩).symm

theorem globalPole_unit (p : LabelledPair N)
    (h : p.val.1 ≠ z) (h' : p.val.2 ≠ z) : globalPole K z p = 1 := by
  simp [globalPole, pairPole, h, h']

/-- Every monic pole is an actual z-s difference or the unit. This does not
discard fixed-orientation scalar factors from the original Q. -/
theorem globalPole_cases (p : LabelledPair N) :
    globalPole K z p = 1 ∨ ∃ s : Remaining z,
      globalPole K z p = algebraMap _ (CommonRational K N) (pairPolynomial K z s.val) := by
  by_cases h : p.val.1 = z
  · exact Or.inr ⟨⟨p.val.2, by simpa [← h] using p.property.ne.symm⟩,
      globalPole_left K z p h⟩
  · by_cases h' : p.val.2 = z
    · exact Or.inr ⟨⟨p.val.1, h⟩, globalPole_right K z p h'⟩
    · exact Or.inl (globalPole_unit K z p h h')

end RationalCollision.ActualGlobalPoleOrientation
end

section
/- Complete assembly for the exact fixed-labelled Q. All maps here act on
the already divided global rational, with all pre/post labels retained. -/
namespace RationalCollision.FullCollisionAssembly
open SupportedFieldWords.OrderedWords CollisionRationalExpansions.OrderedRationalExpansion LabelledRationalClearing.GlobalRationalCurry
open LabelledRationalClearing.GlobalRationalUncurry OrderedCollisionCoordinates.OrderedCoefficientCompatibility OrderedCollisionCoordinates.AdjacentFullOrders
open LabelledRationalClearing.PairDifferenceLocalization LabelledRationalClearing.ActualClearingPartialFractions LabelledRationalClearing.WeightedActualQ
open RationalCollision.FullOrderNormalForm RationalCollision.ActualGlobalPoleOrientation OrderedCollisionResidues.PolynomialResidueZero
open OrderedCollisionResidues.ActualDiagonalLocalResidue OrderedCollisionResidues.ActualSpectatorPoleCancellation OrderedCollisionResidues.AdjacentLabelledCoordinates
open OrderedCollisionResidues.CollisionResidueMaps OrderedCollisionCoordinates.LocalResidueCurrying OrderedCollisionResidues.LocalResidueLinear
open CollisionRationalExpansions.HahnFiberResidue CollisionRationalExpansions.FullOrderSpectatorPole
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable (K : Type*) [Field K] (pre post : ℕ)
  (z : Fin ((pre + 2) + post))
  (tau : Fin ((pre + 1) + post) ≃ Remaining z) (x : Remaining z)

theorem coefficient_collision (hx : tau (boundarySlot pre post) = x)
    (h : CoefficientField K z) :
    expandedLocal K pre post z tau x (coefficient K z h) =
      jump K pre post z tau (coefficient K z h) := by
  have he := coefficient_diagonal_collision K pre post z tau x hx h 0
  simpa only [zpow_zero, mul_one] using he

theorem spectator_collision (hx : tau (boundarySlot pre post) = x)
    (s : Remaining z) (hs : s ≠ x)
    (h : CoefficientField K z) (m : ℕ) :
    expandedLocal K pre post z tau x (coefficient K z h *
      (algebraMap _ (CommonRational K ((pre + 2) + post)) (pairPolynomial K z s.val)) ^ (-(m : ℤ))) =
    jump K pre post z tau (coefficient K z h *
      (algebraMap _ (CommonRational K ((pre + 2) + post)) (pairPolynomial K z s.val)) ^ (-(m : ℤ))) := by
  change coefficientHahn K (pre + 1) post z tau (localResidue K z x _) =
    pullFiber (firstEmbedding pre post (-1)) (firstRational K pre post z tau _) -
      residue (pre + 1) post (secondRational K pre post z tau _)
  rw [weighted_spectator_zero K z x s hs, map_zero]
  exact (actual_spectator_pole_cancel K pre post z tau x s hx hs h m).symm

/-- Every term of the derived normal form satisfies the actual collision.
The diagonal is handled by the scalar kernel; nonadjacent labels cancel;
the spectator-only unit is regular. No normal-form premise is assumed. -/
theorem pole_term_collision (hx : tau (boundarySlot pre post) = x)
    (p : LabelledPair ((pre + 2) + post))
    (h : CoefficientField K z) (m : ℕ) :
    expandedLocal K pre post z tau x (coefficient K z h * (globalPole K z p)⁻¹ ^ m) =
    jump K pre post z tau (coefficient K z h * (globalPole K z p)⁻¹ ^ m) := by
  have he : (globalPole K z p)⁻¹ ^ m = (globalPole K z p) ^ (-(m : ℤ)) := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  rw [he]
  rcases globalPole_cases K z p with hp | ⟨s, hp⟩
  · simpa only [hp, one_zpow, mul_one] using coefficient_collision K pre post z tau x hx h
  · rw [hp]
    by_cases hs : s = x
    · subst s
      exact coefficient_diagonal_collision K pre post z tau x hx h (-(m : ℤ))
    · exact spectator_collision K pre post z tau x hx s hs h m

/-- Equality of complete remaining Hahn series, before choosing any remaining
labelled exponent. The polynomial and all finite pole sums are combined by
the proved additive residue maps. -/
theorem full_collision_series (hx : tau (boundarySlot pre post) = x)
    (P : LabelledPolynomial K ((pre + 2) + post)) (k : ℕ)
    (hP : ∀ e ∈ P.coeff.support, 0 ≤ e z) (r : ℤ) :
    expandedLocal K pre post z tau x
      (globalDiagonal K z x ^ r * globalCorrelator K pre post P k) =
    jump K pre post z tau
      (globalDiagonal K z x ^ r * globalCorrelator K pre post P k) := by
  classical
  obtain ⟨q, c, he⟩ := global_weighted_normal_form K z x P k r hP
  change expandedLocal K pre post z tau x
      (globalDiagonal K z x ^ r * (algebraMap _ (CommonRational K _) P /
        algebraMap _ (CommonRational K _) (clearingPolynomial K _ k))) =
    jump K pre post z tau
      (globalDiagonal K z x ^ r * (algebraMap _ (CommonRational K _) P /
        algebraMap _ (CommonRational K _) (clearingPolynomial K _ k)))
  rw [he]
  simp only [map_add, map_sum]
  rw [polynomial_collision K pre post z tau x q]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro j _
  exact pole_term_collision K pre post z tau x hx p (c p j) (j.val + 1)

/-- The exact FULL target: every finite pre/post block, actual adjacent full
orders, all integer residue weights, and all remaining labelled exponents. -/
theorem required_proved
    (P : LabelledPolynomial K ((pre + 2) + post)) (k : ℕ) :
    OrderedCollisionCoordinates.RemainingCollisionGoal.required K pre post z tau x P k := by
  intro hx hP r e
  have he := full_collision_series K pre post z tau x hx P k hP r
  have hc := congrArg (fun F : HahnSeries (Indices ((pre + 1) + post)) K =>
    F.coeff (remainingExponents (pre + 1) post z tau e)) he
  exact hc

end RationalCollision.FullCollisionAssembly
end

section
/- Both sides expose complete supported expansions before residue. The left
uses the proved seriesMap square, not an assumed coefficient compatibility. -/
namespace RationalCollision.CompleteExpansionCollision
open SupportedFieldWords.OrderedWords CollisionRationalExpansions.OrderedRationalExpansion LabelledRationalClearing.GlobalRationalCurry
open LabelledRationalClearing.PairDifferenceLocalization OrderedCollisionCoordinates.OrderedCoefficientCompatibility OrderedCollisionCoordinates.AdjacentFullOrders
open OrderedCollisionCoordinates.LocalResidueCurrying LabelledRationalClearing.WeightedActualQ RationalCollision.FullCollisionAssembly
open CollisionRationalExpansions.HahnFiberResidue CollisionRationalExpansions.FullOrderSpectatorPole OrderedCollisionResidues.CollisionResidueMaps
variable (K : Type*) [Field K] (pre post : ℕ)
  (z : Fin ((pre + 2) + post))
  (tau : Fin ((pre + 1) + post) ≃ Remaining z) (x : Remaining z)

theorem complete_expansion_collision
    (hx : tau ⟨pre, by omega⟩ = x)
    (P : LabelledPolynomial K ((pre + 2) + post)) (k : ℕ)
    (hP : ∀ e ∈ P.coeff.support, 0 ≤ e z) (r : ℤ) :
    let R := globalDiagonal K z x ^ r * globalCorrelator K pre post P k
    (fusedLocalSeries K (pre + 1) post z x tau R).coeff (-1) =
      pullFiber (firstEmbedding pre post (-1)) (firstRational K pre post z tau R) -
        residue (pre + 1) post (secondRational K pre post z tau R) := by
  dsimp only
  rw [fused_residue_square]
  exact full_collision_series K pre post z tau x hx P k hP r

end RationalCollision.CompleteExpansionCollision
end

end D5.S3.VertexAlgebra
