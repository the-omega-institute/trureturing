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


section
namespace RationalCollision.LaurentNumerator
open SupportedFieldWords.OrderedWords
open CollisionRationalExpansions.OrderedRationalExpansion
open LabelledRationalClearing.GlobalRationalCurry
open LabelledRationalClearing.PairDifferenceLocalization
open LabelledRationalClearing.ActualClearingPartialFractions
open LabelledRationalClearing.WeightedNormalFormConstants
open LabelledRationalClearing.WeightedActualQ
open LabelledRationalClearing.GlobalRationalUncurry
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable (K : Type*) [Field K] {N : ℕ} (z : Fin N)

private theorem variable_nonzero (s : Remaining z) : remainingVariable K z s ≠ 0 := by
  unfold remainingVariable
  simpa only [map_zero] using
    (IsFractionRing.injective (CoefficientPolynomial K z) (CoefficientField K z)).ne
      (AddMonoidAlgebra.single_ne_zero.mpr (one_ne_zero : (1 : K) ≠ 0))

private def pole (p : Option (LabelledPair N)) : Polynomial (CoefficientField K z) :=
  match p with
  | none => Polynomial.X
  | some q => pairPole K z q

private theorem pole_monic (p : Option (LabelledPair N)) : (pole K z p).Monic := by
  cases p with
  | none => exact Polynomial.monic_X
  | some p => exact pairPole_monic K z p

private theorem origin_coprime (p : LabelledPair N) :
    IsCoprime (Polynomial.X : Polynomial (CoefficientField K z)) (pairPole K z p) := by
  have linear (t : Remaining z) :
      IsCoprime (Polynomial.X : Polynomial (CoefficientField K z)) (linearPole K z t) := by
    simpa only [linearPole, Polynomial.C_0, sub_zero] using
      (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        (a := (0 : CoefficientField K z)) (b := remainingVariable K z t)
        (sub_ne_zero.mpr (Ne.symm (variable_nonzero K z t))).isUnit)
  unfold pairPole
  split_ifs
  · exact linear _
  · exact linear _
  · exact isCoprime_one_right

private theorem pole_coprime : Pairwise (fun p q : Option (LabelledPair N) =>
    IsCoprime (pole K z p) (pole K z q)) := by
  intro p q hpq
  cases p <;> cases q
  · exact (hpq rfl).elim
  · exact origin_coprime K z _
  · exact (origin_coprime K z _).symm
  · exact pairPole_coprime K z (by simpa using hpq)

private def lowerShift (P : LabelledPolynomial K N) : ℕ :=
  ∑ e ∈ P.coeff.support, (-e z).toNat

private theorem lowerShift_bound (P : LabelledPolynomial K N)
    (e : Fin N → ℤ) (he : e ∈ P.coeff.support) : 0 ≤ e z + lowerShift K z P := by
  have h := Finset.single_le_sum (fun a _ => Nat.zero_le ((-a z).toNat)) he
  change (-e z).toNat ≤ lowerShift K z P at h
  omega

private def shiftedNumerator (P : LabelledPolynomial K N) :
    Polynomial (CoefficientField K z) :=
  ∑ e ∈ P.coeff.support, Polynomial.monomial (e z + lowerShift K z P).toNat
    (algebraMap (CoefficientPolynomial K z) (CoefficientField K z)
      (AddMonoidAlgebra.single (fun i : Remaining z => e i.val) (P.coeff e)))

private theorem shiftedNumerator_eq (P : LabelledPolynomial K N) :
    algebraMap _ (RatFunc (CoefficientField K z)) (shiftedNumerator K z P) *
      RatFunc.X ^ (-(lowerShift K z P : ℤ)) = curryPolynomial K z P := by
  classical
  conv_rhs => rw [← AddMonoidAlgebra.sum_coeff_single P]
  simp only [Finsupp.sum, shiftedNumerator, map_sum, RatFunc.algebraMap_monomial,
    Finset.sum_mul, curryPolynomial_single]
  apply Finset.sum_congr rfl
  intro e he
  rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ RatFunc.X_ne_zero,
    Int.toNat_of_nonneg (lowerShift_bound K z P e he)]
  congr 2
  omega

private def poleOrder (x : Remaining z) (orders : Fin N × Fin N → ℕ) (m : ℕ)
    (r : ℤ) (p : Option (LabelledPair N)) : ℕ :=
  match p with
  | none => m
  | some q => orders q.val + if q = collisionPair z x then (-r).toNat else 0

private def orientation (orders : Fin N × Fin N → ℕ) : CoefficientField K z :=
  ∏ p : LabelledPair N, pairScalar K z p ^ orders p.val

private theorem orientation_nonzero (orders : Fin N × Fin N → ℕ) :
    orientation K z orders ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun p _ => pow_ne_zero _ (pairScalar_ne_zero K z p))

private theorem curry_weighted_denominator (orders : Fin N × Fin N → ℕ) :
    curryPolynomial K z (∏ p ∈ labelledPairs N, pairPolynomial K p.1 p.2 ^ orders p) =
      RatFunc.C (orientation K z orders) *
        ∏ p : LabelledPair N,
          algebraMap _ (RatFunc (CoefficientField K z)) (pairPole K z p) ^ orders p.val := by
  have hprod : (∏ p ∈ labelledPairs N, pairPolynomial K p.1 p.2 ^ orders p) =
      ∏ p : LabelledPair N, pairPolynomial K p.val.1 p.val.2 ^ orders p.val := by
    exact Finset.prod_subtype (labelledPairs N) (by intro p; simp [labelledPairs]) _
  rw [hprod, map_prod]
  simp only [map_pow, curry_pair, mul_pow, Finset.prod_mul_distrib, orientation,
    map_prod, map_pow]

private theorem laurent_normal_form (x : Remaining z) (P : LabelledPolynomial K N)
    (orders : Fin N × Fin N → ℕ) (r : ℤ) :
    ∃ (q : Polynomial (CoefficientField K z))
      (c : (p : Option (LabelledPair N)) →
        Fin (poleOrder z x orders (lowerShift K z P) r p) → CoefficientField K z),
      curryRational K z (globalDiagonal K z x ^ r *
        (algebraMap _ (CommonRational K N) P /
          algebraMap _ (CommonRational K N)
            (∏ p ∈ labelledPairs N, pairPolynomial K p.1 p.2 ^ orders p))) =
      algebraMap _ (RatFunc (CoefficientField K z)) q +
        ∑ p, ∑ j, RatFunc.C (c p j) *
          (algebraMap _ (RatFunc (CoefficientField K z)) (pole K z p))⁻¹ ^ (j.val + 1) := by
  classical
  let f := Polynomial.C (orientation K z orders)⁻¹ * shiftedNumerator K z P *
    linearPole K z x ^ r.toNat
  obtain ⟨q, rem, hr, he⟩ := Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse
    (K := RatFunc (CoefficientField K z)) (s := Finset.univ) f
    (fun p _ => pole_monic K z p)
    (fun p _ q _ hpq => pole_coprime K z hpq) (poleOrder z x orders (lowerShift K z P) r)
    (fun p _ => inv_mul_cancel₀ (by
      simpa only [map_zero] using
        (IsFractionRing.injective (Polynomial (CoefficientField K z))
          (RatFunc (CoefficientField K z))).ne (pole_monic K z p).ne_zero))
  have constant (p : Option (LabelledPair N)) (j : Fin (poleOrder z x orders (lowerShift K z P) r p)) :
      rem p j = Polynomial.C ((rem p j).coeff 0) := by
    cases p with
    | none =>
      apply Polynomial.eq_C_of_degree_le_zero
      have degree := hr none (Finset.mem_univ _) j
      change (rem none j).degree < (Polynomial.X : Polynomial (CoefficientField K z)).degree at degree
      by_cases hz : rem none j = 0
      · simp [hz]
      · rw [Polynomial.degree_eq_natDegree hz] at degree ⊢
        have hn : (rem none j).natDegree < 1 := by simpa using degree
        have hn0 : (rem none j).natDegree = 0 := by omega
        simp [hn0]
    | some p => exact remainder_constant K z p _ (hr _ (Finset.mem_univ _) j)
  refine ⟨q, fun p j => (rem p j).coeff 0, ?_⟩
  have rhs : algebraMap _ (RatFunc (CoefficientField K z)) q +
      ∑ p, ∑ j, RatFunc.C ((rem p j).coeff 0) *
        (algebraMap _ (RatFunc (CoefficientField K z)) (pole K z p))⁻¹ ^ (j.val + 1) =
      algebraMap _ (RatFunc (CoefficientField K z)) f *
        ∏ p : Option (LabelledPair N),
          (algebraMap _ (RatFunc (CoefficientField K z)) (pole K z p))⁻¹ ^
            poleOrder z x orders (lowerShift K z P) r p := by
    rw [he]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro j _
    rw [constant, RatFunc.algebraMap_C, Polynomial.coeff_C_zero]
  have pairProduct :
      (∏ p : LabelledPair N, (algebraMap _ (RatFunc (CoefficientField K z))
        (pairPole K z p)) ^ (orders p.val + if p = collisionPair z x then (-r).toNat else 0)) =
      (∏ p : LabelledPair N, (algebraMap _ (RatFunc (CoefficientField K z))
        (pairPole K z p)) ^ orders p.val) *
        (algebraMap _ (RatFunc (CoefficientField K z)) (linearPole K z x)) ^ (-r).toNat := by
    simp only [pow_add, Finset.prod_mul_distrib]
    congr 1
    have term (p : LabelledPair N) :
        (algebraMap _ (RatFunc (CoefficientField K z)) (pairPole K z p)) ^
          (if p = collisionPair z x then (-r).toNat else 0) =
        if p = collisionPair z x then
          (algebraMap _ (RatFunc (CoefficientField K z)) (pairPole K z p)) ^ (-r).toNat
        else 1 := by split_ifs <;> simp
    simp only [term, Fintype.prod_ite_eq', collisionPair_pole]
  have allProduct :
      (∏ p : Option (LabelledPair N),
        (algebraMap _ (RatFunc (CoefficientField K z)) (pole K z p))⁻¹ ^
          poleOrder z x orders (lowerShift K z P) r p) =
      (RatFunc.X⁻¹) ^ lowerShift K z P *
        ((∏ p : LabelledPair N,
          (algebraMap _ (RatFunc (CoefficientField K z)) (pairPole K z p)) ^ orders p.val) *
          (algebraMap _ (RatFunc (CoefficientField K z)) (linearPole K z x)) ^ (-r).toNat)⁻¹ := by
    rw [Fintype.prod_option]
    simp only [pole, poleOrder, RatFunc.algebraMap_X]
    congr 1
    rw [← pairProduct]
    simp only [Finset.prod_inv_distrib, inv_pow]
  rw [rhs, allProduct, map_mul, map_zpow₀, curry_global_fraction, curry_weighted_denominator]
  have diagonal : curryRational K z (globalDiagonal K z x) =
      algebraMap _ (RatFunc (CoefficientField K z)) (linearPole K z x) := by
    simp only [globalDiagonal, curryRational, IsFractionRing.lift_algebraMap]
    exact curry_pair_left K z x
  rw [diagonal, integer_weight, ← shiftedNumerator_eq K z P]
  simp only [f, map_mul, map_pow, RatFunc.algebraMap_C, map_inv₀,
    div_eq_mul_inv, mul_inv_rev, zpow_neg, zpow_natCast, inv_pow]
  ring


open CollisionRationalExpansions.HahnFiberResidue
open OrderedCollisionCoordinates.OrderedCoefficientCompatibility
open OrderedCollisionCoordinates.AdjacentFullOrders
open OrderedCollisionCoordinates.LocalResidueCurrying
open OrderedCollisionCoordinates.ContextualLaurentKernel
open OrderedCollisionResidues.AdjacentLabelledCoordinates
open OrderedCollisionResidues.LabelledDiagonalResidue
open OrderedCollisionResidues.LocalSpectatorResidue
open OrderedCollisionResidues.CollisionResidueMaps
open OrderedCollisionResidues.LocalResidueLinear
open OrderedCollisionResidues.PolynomialResidueZero
open CollisionLaurentKernels.LaurentCollision
open RationalCollision.FullOrderNormalForm
open RationalCollision.FullCollisionAssembly

private theorem origin_local_zero (x : Remaining z) (m : ℕ) :
    localResidue K z x (globalZ K z ^ (-(m : ℤ))) = 0 := by
  have localZ : localRational K z x (globalZ K z) =
      algebraMap _ (RatFunc (CoefficientField K z))
        (Polynomial.X + Polynomial.C (remainingVariable K z x)) := by
    change translate K z x (curryRational K z (globalZ K z)) = _
    rw [curry_globalZ, ← RatFunc.algebraMap_X, translate,
      IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    congr 1
    change (Polynomial.algEquivAevalXAddC (remainingVariable K z x)) Polynomial.X = _
    simp only [Polynomial.algEquivAevalXAddC_apply, Polynomial.aeval_X]
  unfold localResidue
  rw [map_zpow₀, localZ, zpow_neg, zpow_natCast, ← inv_pow]
  exact regular_pole_residue _ (variable_nonzero K z x) m

private theorem origin_jump_zero (pre post : ℕ)
    (z : Fin ((pre + 2) + post))
    (tau : Fin ((pre + 1) + post) ≃ Remaining z) (m : ℕ) :
    jump K pre post z tau (globalZ K z ^ (-(m : ℤ))) = 0 := by
  change pullFiber _ (firstRational K pre post z tau _) -
    CollisionRationalExpansions.HahnFiberResidue.residue (pre + 1) post
      (secondRational K pre post z tau _) = 0
  have first : firstRational K pre post z tau (globalZ K z ^ (-(m : ℤ))) =
      contextPair K pre post
        (iotaZX K (CollisionLaurentKernels.LaurentCollision.z K) ^ (-(m : ℤ))) := by
    simp only [map_zpow₀, first_globalZ]
  have second : secondRational K pre post z tau (globalZ K z ^ (-(m : ℤ))) =
      contextPair K pre post
        (iotaXZ K (CollisionLaurentKernels.LaurentCollision.z K) ^ (-(m : ℤ))) := by
    simp only [map_zpow₀, second_globalZ]
  rw [first, second, context_first_residue, context_second_residue]
  have scalar : resZ_ZX K (iotaZX K (CollisionLaurentKernels.LaurentCollision.z K) ^ (-(m : ℤ))) =
      resZ_XZ K (iotaXZ K (CollisionLaurentKernels.LaurentCollision.z K) ^ (-(m : ℤ))) := by
    ext e
    simp only [iotaZX_z, iotaXZ_z, HahnSeries.C_apply, zpow_neg, zpow_natCast,
      HahnSeries.inv_single, inv_one, HahnSeries.single_pow, nsmul_zero,
      resZ_ZX, HahnSeries.map_coeff, HahnSeries.coeff.linearMap_apply, resZ_XZ]
    by_cases hm : m = 1 <;> by_cases he : e = 0 <;>
      simp [T, HahnSeries.inv_single, HahnSeries.single_pow, HahnSeries.coeff_single,
        hm, he, show (1 : ℤ) = (m : ℤ) ↔ m = 1 by omega]
  rw [scalar, sub_self]

private theorem origin_collision (pre post : ℕ)
    (z : Fin ((pre + 2) + post))
    (tau : Fin ((pre + 1) + post) ≃ Remaining z) (x : Remaining z)
    (h : CoefficientField K z) (m : ℕ) :
    expandedLocal K pre post z tau x (coefficient K z h * globalZ K z ^ (-(m : ℤ))) =
      jump K pre post z tau (coefficient K z h * globalZ K z ^ (-(m : ℤ))) := by
  rw [expandedLocal_coefficient_mul, jump_coefficient_mul, origin_jump_zero, mul_zero]
  change coefficientHahn K (pre + 1) post z tau h *
    coefficientHahn K (pre + 1) post z tau (localResidue K z x _) = 0
  rw [origin_local_zero, map_zero, mul_zero]

/- proof_shape: weighted_laurent_collision: content
   admission_basis: escape-witness
   escape_witness: a finite support lower bound clears negative eliminated
   coordinates. Partial fractions include the origin pole and every actual
   pair pole with its own order. The origin residues cancel between complete
   orders; its local residue vanishes at the nonzero retained variable. -/
/-- Complete adjacent collision for an unrestricted finite Laurent numerator
and independent pairwise denominator orders. No numerator positivity is used. -/
theorem weighted_laurent_collision (pre post : ℕ)
    (z : Fin ((pre + 2) + post))
    (tau : Fin ((pre + 1) + post) ≃ Remaining z) (x : Remaining z)
    (hx : tau (boundarySlot pre post) = x)
    (P : LabelledPolynomial K ((pre + 2) + post))
    (orders : Fin ((pre + 2) + post) × Fin ((pre + 2) + post) → ℕ) (r : ℤ) :
    let R : CommonRational K ((pre + 2) + post) :=
      globalDiagonal K z x ^ r *
        (algebraMap _ _ P /
          algebraMap _ _ (∏ p ∈ labelledPairs ((pre + 2) + post),
            pairPolynomial K p.1 p.2 ^ orders p))
    (fusedLocalSeries K (pre + 1) post z x tau R).coeff (-1) =
      CollisionRationalExpansions.HahnFiberResidue.pullFiber
        (CollisionRationalExpansions.FullOrderSpectatorPole.firstEmbedding pre post (-1))
        (firstRational K pre post z tau R) -
      CollisionRationalExpansions.HahnFiberResidue.residue (pre + 1) post
        (secondRational K pre post z tau R) := by
  classical
  dsimp only
  rw [fused_residue_square]
  change expandedLocal K pre post z tau x _ = jump K pre post z tau _
  obtain ⟨q, c, form⟩ := laurent_normal_form K z x P orders r
  have form' := congrArg (uncurryRational K z) form
  rw [uncurry_curry] at form'
  simp only [map_add, map_sum, map_mul, map_pow, map_inv₀, uncurry_constant] at form'
  rw [form']
  simp only [map_add, map_sum]
  rw [polynomial_collision K pre post z tau x q]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro j _
  cases p with
  | none =>
    have origin : uncurryRational K z
        (algebraMap _ (RatFunc (CoefficientField K z)) (pole K z none)) = globalZ K z := by
      rw [uncurryRational, IsFractionRing.lift_algebraMap]
      simp [pole, LabelledRationalClearing.GlobalRationalUncurry.polynomial]
    rw [origin]
    simpa only [zpow_neg, zpow_natCast, inv_pow] using
      origin_collision K pre post z tau x (c none j) (j.val + 1)
  | some p =>
    change expandedLocal K pre post z tau x
      (coefficient K z (c (some p) j) * (globalPole K z p)⁻¹ ^ (j.val + 1)) = _
    exact pole_term_collision K pre post z tau x hx p (c (some p) j) (j.val + 1)

end RationalCollision.LaurentNumerator
end

end D5.S3.VertexAlgebra
