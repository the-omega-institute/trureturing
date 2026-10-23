/- GID: D5/S3/VertexAlgebra/RationalCollision/LaurentNumerator
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/RationalCollision/LaurentNumerator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete adjacent collision with unrestricted Laurent numerators and independent pair orders. -/

/-
Source: lexa-ms <50111876+AlyciaBHZ@users.noreply.github.com>,
D5/S3/VertexAlgebra/RationalCollision.lean, RationalCollision.LaurentNumerator,
immutable checkpoint 6c8682a64921b8f8d2f059c80e395b2af30c9a13
(original proof checkpoint cda001f75ea0ca217d1230c9abbefd62265d44aa).
The source proof and its complete telescope are preserved here.

The proof reuses mathlib polynomial partial fractions by Kevin Buzzard,
Sidharth Hariharan and Aaron Liu; HahnSeries by Aaron Anderson; and
LaurentSeries by Aaron Anderson, María Inés de Frutos-Fernández and
Filippo A. E. Nuccio (Apache 2.0). See the imported rational collision owner
for its remaining upstream source attribution.
-/

import D5.S3.VertexAlgebra.RationalCollision

noncomputable section
namespace D5.S3.VertexAlgebra

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
