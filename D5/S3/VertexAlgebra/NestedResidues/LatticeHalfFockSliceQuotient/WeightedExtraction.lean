/- GID: D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSliceQuotient/WeightedExtraction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSliceQuotient/WeightedExtraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Signed Laurent collision and weighted actual local extraction. -/
import D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSliceQuotient.SupportedReadouts

/-! Signed Laurent collision and weighted actual local extraction.
The finite-slice, two-branch extraction and signed-collision proofs retain their
original research substance at e7115cf0e88dde8f45861e42cd51d8a39473c0fe.
Classical local-field calculus: Matsuo--Nagatomo; twisted lattice setting:
Bakalov--Kac, math/0402315. No literature novelty or final Taylor bridge is claimed.
Hahn/Laurent kernels: mathlib, Apache 2.0 (Aaron Anderson, María Inés de
Frutos-Fernández, Filippo A. E. Nuccio); partial fractions: Kevin Buzzard,
Sidharth Hariharan, Aaron Liu. Actual field composition: Scott Carnahan,
vertexAlg 4453e34ec390e82a0c789c731ada8f9a6e86bdea, Apache 2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable section
namespace D5.S3.VertexAlgebra
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
private theorem weighted_laurent_collision (pre post : ℕ)
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
end D5.S3.VertexAlgebra
end

namespace D5.S3.VertexAlgebra.LatticeHalfFockNestedQReadout
open LatticeHalfFockLeftCurrentTransport LatticeHalfFockClearedTaylorReadout
open UniformGradedLocalCorrelator
open LatticeHalfFockChargedCollision.WeightedLocalCorrelator
open SupportedFieldWords.OrderedWords SupportedFieldWords.OrderedDistribution
open CollisionRationalExpansions.OrderedRationalExpansion
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open scoped BigOperators VertexOperator
noncomputable section

open CollisionLaurentKernels.LaurentCollision
open OrderedCollisionCoordinates.ContextualLaurentKernel
open CollisionRationalExpansions.HahnFiberResidue
open CollisionRationalExpansions.FullOrderSpectatorPole

def currentSourceTau (reverse : Bool) :
    Fin 2 ≃ LabelledRationalClearing.GlobalRationalCurry.Remaining (0 : Fin 3) :=
  if reverse then (Equiv.swap 0 1).trans (finSuccAboveEquiv (0 : Fin 3))
  else finSuccAboveEquiv (0 : Fin 3)

/-- The complete current/source local residue, with the spectator retained
on its actual side of the pair. All diagonal weights are signed. -/
def currentSourceLocalQ (reverse : Bool) (s d : ℤ) (K : ℕ) (k l : ℤ)
    (R : CommonRational ℂ 3) : ℂ :=
  ∑ ell ∈ Finset.range ((K : ℤ) - d).toNat,
    Ring.choose (-(s : ℂ) / 2) ell *
      (if reverse then
        ((OrderedCollisionCoordinates.LocalResidueCurrying.fusedLocalSeries ℂ 2 0
          (0 : Fin 3) ⟨1, by decide⟩ (currentSourceTau true)
          (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (0 : Fin 3)
            ⟨1, by decide⟩ ^ (d + ell) * R)).coeff (-1)).coeff
          (exponents 2 ![-l - 1, -k + ell - 1])
      else
        ((OrderedCollisionCoordinates.LocalResidueCurrying.fusedLocalSeries ℂ 1 1
          (0 : Fin 3) ⟨1, by decide⟩ (currentSourceTau false)
          (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ (0 : Fin 3)
            ⟨1, by decide⟩ ^ (d + ell) * R)).coeff (-1)).coeff
          (exponents 2 ![-k + ell - 1, -l - 1]))

theorem weighted_local_fiber (pre post : ℕ)
    (z : Fin ((pre + 2) + post))
    (tau : Fin ((pre + 1) + post) ≃ LabelledRationalClearing.GlobalRationalCurry.Remaining z)
    (x : LabelledRationalClearing.GlobalRationalCurry.Remaining z)
    (hx : tau (OrderedCollisionResidues.AdjacentLabelledCoordinates.boundarySlot pre post) = x)
    (P : LabelledPolynomial ℂ ((pre + 2) + post))
    (orders : Fin ((pre + 2) + post) × Fin ((pre + 2) + post) → ℕ)
    (r : ℤ) (g : Indices ((pre + 1) + post)) :
    let R := algebraMap _ (CommonRational ℂ ((pre + 2) + post)) P /
      algebraMap _ (CommonRational ℂ ((pre + 2) + post))
        (∏ p ∈ LabelledRationalClearing.PairDifferenceLocalization.labelledPairs ((pre + 2) + post),
          LabelledRationalClearing.PairDifferenceLocalization.pairPolynomial ℂ p.1 p.2 ^ orders p)
    (pullFiber (firstEmbedding pre post (-1))
      (contextPair ℂ pre post (kernelZX ℂ r) *
        OrderedCollisionCoordinates.AdjacentFullOrders.firstRational ℂ pre post z tau R)).coeff g -
    (residue (pre + 1) post
      (contextPair ℂ pre post (kernelXZ ℂ r) *
        OrderedCollisionCoordinates.AdjacentFullOrders.secondRational ℂ pre post z tau R)).coeff g =
    ((OrderedCollisionCoordinates.LocalResidueCurrying.fusedLocalSeries ℂ (pre + 1) post z x tau
      (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ z x ^ r * R)).coeff (-1)).coeff g := by
  dsimp only
  have equality := RationalCollision.LaurentNumerator.weighted_laurent_collision
    ℂ pre post z tau x hx P orders r
  have first : ∀ R : CommonRational ℂ ((pre + 2) + post),
      OrderedCollisionCoordinates.AdjacentFullOrders.firstRational ℂ pre post z tau
        (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ z x ^ r * R) =
      contextPair ℂ pre post (kernelZX ℂ r) *
        OrderedCollisionCoordinates.AdjacentFullOrders.firstRational ℂ pre post z tau R := by
    intro R
    simp only [LabelledRationalClearing.WeightedActualQ.globalDiagonal, map_mul, map_zpow₀,
      OrderedCollisionResidues.LabelledDiagonalResidue.first_diagonal ℂ pre post z tau x hx,
      iotaZX_diagonal, kernelZX_zpow]
  have second : ∀ R : CommonRational ℂ ((pre + 2) + post),
      OrderedCollisionCoordinates.AdjacentFullOrders.secondRational ℂ pre post z tau
        (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ z x ^ r * R) =
      contextPair ℂ pre post (kernelXZ ℂ r) *
        OrderedCollisionCoordinates.AdjacentFullOrders.secondRational ℂ pre post z tau R := by
    intro R
    simp only [LabelledRationalClearing.WeightedActualQ.globalDiagonal, map_mul, map_zpow₀,
      OrderedCollisionResidues.LabelledDiagonalResidue.second_diagonal ℂ pre post z tau x hx,
      iotaXZ_diagonal, kernelXZ_zpow]
  dsimp only at equality
  rw [first, second] at equality
  exact congrArg (fun F : HahnSeries (Indices ((pre + 1) + post)) ℂ => F.coeff g) equality.symm

private theorem currentSourceLocalQ_eq (D : LatticeData) (a b : Carrier D) (K : ℕ)
    (P : LabelledPolynomial ℂ 3) (s d k l : ℤ) :
    let W := rationalTripleCarriers D a b K P
    let R := algebraMap _ (CommonRational ℂ 3) P /
      algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))
    leftPairFiberQ s d (vectorFrequencyBound D a + 1) k l (W 0) (W 2) =
      currentSourceLocalQ false s d (vectorFrequencyBound D a + 1) k l R ∧
    rightPairFiberQ s d (vectorFrequencyBound D a + 1) k l (W 4) (W 5) =
      currentSourceLocalQ true s d (vectorFrequencyBound D a + 1) k l R := by
  dsimp only
  have f₀ : SupportedWordRationalCollision.ActualOrderedCoordinates.firstOrder
      0 1 (0 : Fin 3) (currentSourceTau false) = triplePermutation 0 := by
    ext j; fin_cases j <;> rfl
  have g₀ : SupportedWordRationalCollision.ActualOrderedCoordinates.secondOrder
      0 1 (0 : Fin 3) (currentSourceTau false) = triplePermutation 2 := by
    ext j; fin_cases j <;> rfl
  have f₁ : SupportedWordRationalCollision.ActualOrderedCoordinates.firstOrder
      1 0 (0 : Fin 3) (currentSourceTau true) = triplePermutation 4 := by
    ext j; fin_cases j <;> rfl
  have g₁ : SupportedWordRationalCollision.ActualOrderedCoordinates.secondOrder
      1 0 (0 : Fin 3) (currentSourceTau true) = triplePermutation 5 := by
    ext j; fin_cases j <;> rfl
  constructor
  · unfold leftPairFiberQ currentSourceLocalQ
    simp only [Bool.false_eq_true, ite_false]
    apply Finset.sum_congr rfl
    intro ell hell
    congr 1
    have eq := weighted_local_fiber 0 1 (0 : Fin 3) (currentSourceTau false)
      ⟨1, by decide⟩ (by rfl) P (threeOrders D a b K) (d + ell)
      (exponents 2 ![-k + ell - 1, -l - 1])
    rw [← SupportedWordRationalCollision.ActualOrderedCoordinates.firstOrder_rational,
      ← SupportedWordRationalCollision.ActualOrderedCoordinates.secondOrder_rational,
      f₀, g₀] at eq
    exact eq
  · unfold rightPairFiberQ currentSourceLocalQ
    simp only [Bool.true_eq, ite_true]
    apply Finset.sum_congr rfl
    intro ell hell
    congr 1
    have eq := weighted_local_fiber 1 0 (0 : Fin 3) (currentSourceTau true)
      ⟨1, by decide⟩ (by rfl) P (threeOrders D a b K) (d + ell)
      (exponents 2 ![-l - 1, -k + ell - 1])
    rw [← SupportedWordRationalCollision.ActualOrderedCoordinates.firstOrder_rational,
      ← SupportedWordRationalCollision.ActualOrderedCoordinates.secondOrder_rational,
      f₁, g₁] at eq
    exact eq

/-- The current/source pair is collided locally inside each supported outer
fiber; its two spectator positions retain their respective complete orders. -/
def nestedLeftLocalReadout (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (R : CommonRational ℂ 3) : ℂ :=
  supportedQReadout outerLift r H n
    (fun k l => currentSourceLocalQ false innerLift d K k l R)
    (fun k l => currentSourceLocalQ true innerLift d K l k R)

private theorem nestedLeftLocalReadout_eq (D : LatticeData) (a b : Carrier D) (K : ℕ)
    (P : LabelledPolynomial ℂ 3) (outerLift innerLift d r n : ℤ) (H : ℕ) :
    nestedLeftFiberReadout outerLift innerLift d r n (vectorFrequencyBound D a + 1) H
      (rationalTripleCarriers D a b K P) =
    nestedLeftLocalReadout outerLift innerLift d r n (vectorFrequencyBound D a + 1) H
      (algebraMap _ (CommonRational ℂ 3) P /
        algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))) := by
  unfold nestedLeftFiberReadout nestedLeftLocalReadout
  apply supportedQReadout_congr
  · intro k l _
    exact (currentSourceLocalQ_eq D a b K P innerLift d k l).1
  · intro k l _
    exact (currentSourceLocalQ_eq D a b K P innerLift d l k).2

def lastSourceTau (z : Fin 2) (spectatorLeft : Bool) :
    Fin 2 ≃ LabelledRationalClearing.GlobalRationalCurry.Remaining z.castSucc :=
  if spectatorLeft then finSuccAboveEquiv z.castSucc
  else (Equiv.swap 0 1).trans (finSuccAboveEquiv z.castSucc)

/-- A complete inner collision with the second source, retaining the actual
spectator side and the original current/source labels. -/
def lastSourceLocalQ (z : Fin 2) (spectatorLeft : Bool) (s d : ℤ) (K : ℕ) (k l : ℤ)
    (R : CommonRational ℂ 3) : ℂ :=
  let x : LabelledRationalClearing.GlobalRationalCurry.Remaining z.castSucc :=
    ⟨2, by fin_cases z <;> decide⟩
  ∑ ell ∈ Finset.range ((K : ℤ) - d).toNat,
    Ring.choose (-(s : ℂ) / 2) ell *
      (if spectatorLeft then
        ((OrderedCollisionCoordinates.LocalResidueCurrying.fusedLocalSeries ℂ 2 0
          z.castSucc x (lastSourceTau z true)
          (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ z.castSucc x ^
            (d + ell) * R)).coeff (-1)).coeff
          (exponents 2 ![-l - 1, -k + ell - 1])
      else
        ((OrderedCollisionCoordinates.LocalResidueCurrying.fusedLocalSeries ℂ 1 1
          z.castSucc x (lastSourceTau z false)
          (LabelledRationalClearing.WeightedActualQ.globalDiagonal ℂ z.castSucc x ^
            (d + ell) * R)).coeff (-1)).coeff
          (exponents 2 ![-k + ell - 1, -l - 1]))

private theorem currentSecondSourceLocalQ_eq (D : LatticeData) (a b : Carrier D) (K I : ℕ)
    (P : LabelledPolynomial ℂ 3) (s d k l : ℤ) :
    let W := swapCurrentSourceCarriers (rationalTripleCarriers D a b K P)
    let R := algebraMap _ (CommonRational ℂ 3) P /
      algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))
    rightPairFiberQ s d I k l (W 0) (W 1) =
      lastSourceLocalQ 0 true s d I k l R ∧
    leftPairFiberQ s d I k l (W 3) (W 5) =
      lastSourceLocalQ 0 false s d I k l R := by
  dsimp only
  have f_left : SupportedWordRationalCollision.ActualOrderedCoordinates.firstOrder
      1 0 (0 : Fin 3) (lastSourceTau 0 true) = triplePermutation 2 := by
    ext j; fin_cases j <;> rfl
  have g_left : SupportedWordRationalCollision.ActualOrderedCoordinates.secondOrder
      1 0 (0 : Fin 3) (lastSourceTau 0 true) = triplePermutation 3 := by
    ext j; fin_cases j <;> rfl
  have f_right : SupportedWordRationalCollision.ActualOrderedCoordinates.firstOrder
      0 1 (0 : Fin 3) (lastSourceTau 0 false) = triplePermutation 1 := by
    ext j; fin_cases j <;> rfl
  have g_right : SupportedWordRationalCollision.ActualOrderedCoordinates.secondOrder
      0 1 (0 : Fin 3) (lastSourceTau 0 false) = triplePermutation 4 := by
    ext j; fin_cases j <;> rfl
  constructor
  · unfold rightPairFiberQ lastSourceLocalQ
    simp only [Bool.true_eq, Bool.false_eq_true, ite_true, ite_false]
    apply Finset.sum_congr rfl
    intro ell hell
    congr 1
    have eq := weighted_local_fiber 1 0 (0 : Fin 3) (lastSourceTau 0 true)
      ⟨2, by decide⟩ (by rfl) P (threeOrders D a b K) (d + ell)
      (exponents 2 ![-l - 1, -k + ell - 1])
    rw [← SupportedWordRationalCollision.ActualOrderedCoordinates.firstOrder_rational,
      ← SupportedWordRationalCollision.ActualOrderedCoordinates.secondOrder_rational,
      f_left, g_left] at eq
    exact eq
  · unfold leftPairFiberQ lastSourceLocalQ
    simp only [Bool.true_eq, Bool.false_eq_true, ite_true, ite_false]
    apply Finset.sum_congr rfl
    intro ell hell
    congr 1
    have eq := weighted_local_fiber 0 1 (0 : Fin 3) (lastSourceTau 0 false)
      ⟨2, by decide⟩ (by rfl) P (threeOrders D a b K) (d + ell)
      (exponents 2 ![-k + ell - 1, -l - 1])
    rw [← SupportedWordRationalCollision.ActualOrderedCoordinates.firstOrder_rational,
      ← SupportedWordRationalCollision.ActualOrderedCoordinates.secondOrder_rational,
      f_right, g_right] at eq
    exact eq

/-- A supported outer Q readout whose complete inner collision is local.
The eliminated label distinguishes A/B from J/B, without relabelling the numerator. -/
def nestedRightLocalReadout (z : Fin 2) (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (R : CommonRational ℂ 3) : ℂ :=
  supportedQReadout outerLift r H n
    (fun k l => lastSourceLocalQ z true innerLift d K l k R)
    (fun k l => lastSourceLocalQ z false innerLift d K k l R)

private theorem nestedRightLocalReadout_currentSecondSource (D : LatticeData) (a b : Carrier D) (K I : ℕ)
    (P : LabelledPolynomial ℂ 3) (outerLift innerLift d r n : ℤ) (H : ℕ) :
    nestedRightFiberReadout outerLift innerLift d r n I H
      (swapCurrentSourceCarriers (rationalTripleCarriers D a b K P)) =
    nestedRightLocalReadout 0 outerLift innerLift d r n I H
      (algebraMap _ (CommonRational ℂ 3) P /
        algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))) := by
  unfold nestedRightFiberReadout nestedRightLocalReadout
  apply supportedQReadout_congr
  · intro k l _
    exact (currentSecondSourceLocalQ_eq D a b K I P innerLift d l k).1
  · intro k l _
    exact (currentSecondSourceLocalQ_eq D a b K I P innerLift d k l).2

theorem actual_two_branch_supplier (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (a b : Carrier D) :
    ∃ K : ℕ, ∀ (gamma delta d r n : ℤ) (x : ActualTensor D hu)
      (phi : ActualTensor D hu →ₗ[ℂ] ℂ),
      ∃ P : LabelledPolynomial ℂ 3,
        (∀ e : Exponent 3, P.coeff e =
          if totalExponent e =
              (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3
          then phi (actualNumerator D hu i a b gamma delta K x e) else 0) ∧
        ∀ (H₁ H₃ : ℕ) (j : ℤ),
          phi (((qField (gamma + 1) r H₁
            (targetSlice D hu (neutralMode D i d a) (gamma + 1))
            (targetSlice D hu b delta))[[n]]) x) =
            nestedLeftLocalReadout (gamma + 1) 1 d r n
              (vectorFrequencyBound D a + 1) H₁
              (algebraMap _ (CommonRational ℂ 3) P /
                algebraMap _ (CommonRational ℂ 3)
                  (weightedClearingPolynomial (threeOrders D a b K))) ∧
          phi (((qField gamma (d + r - j) H₃ (targetSlice D hu a gamma)
            (targetSlice D hu (neutralMode D i j b) (delta + 1)))[[n]]) x) =
            nestedRightLocalReadout 0 gamma 1 j (d + r - j) n
              (vectorFrequencyBound D b + 1) H₃
              (algebraMap _ (CommonRational ℂ 3) P /
                algebraMap _ (CommonRational ℂ 3)
                  (weightedClearingPolynomial (threeOrders D a b K))) := by
  obtain ⟨K, carriers⟩ := actual_finite_laurent_carriers D hu i a b
  refine ⟨K, ?_⟩
  intro gamma delta d r n x phi
  let total := (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3
  obtain ⟨P, coefficients, words⟩ := carriers gamma delta x phi total
  refine ⟨P, coefficients, ?_⟩
  let J := targetCurrent D hu i
  let A := targetSlice D hu a gamma
  let B := targetSlice D hu b delta
  have same (order : Fin 6) (modes : Exponent 3)
      (degree : (∑ k, modes k) = d + r + n) :
      tripleScalar J A B x phi order modes = rationalTripleReadout D a b K P order modes := by
    have index : totalExponent (fun k => -modes k - 1) =
        total - ∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ) := by
      simp only [totalExponent, Fin.sum_univ_three] at degree ⊢
      dsimp [total]
      omega
    have readout := words (triplePermutation order) (fun k => -modes k - 1)
    rw [if_pos index] at readout
    exact readout.symm
  have swapped (j : ℤ) (order : Fin 6) (modes : Exponent 3)
      (degree : (∑ k, modes k) = j + (d + r - j) + n) :
      tripleScalar A J B x phi order modes =
        swapCurrentSourceReadout (rationalTripleReadout D a b K P) order modes := by
    rw [tripleScalar_swap]
    apply same
    simp [Fin.sum_univ_three] at degree ⊢
    omega
  intro H₁ H₃ j
  constructor
  · rw [← nestedLeftLocalReadout_eq D a b K P (gamma + 1) 1 d r n H₁,
      (show targetSlice D hu (neutralMode D i d a) (gamma + 1) =
        qField 1 d (vectorFrequencyBound D a + 1) (targetCurrent D hu i) (targetSlice D hu a gamma) from
        LatticeHalfFockGroundRightCurrentTransport.native_current_inverse D hu i a gamma d),
      supportedNestedLeftReadout_eq, nestedLeftFiberReadout_eq]
    exact supportedNestedLeftReadout_congr _ _ _ _ _ _ _ _ _ same
  · rw [← nestedRightLocalReadout_currentSecondSource D a b K
      (vectorFrequencyBound D b + 1) P gamma 1 j (d + r - j) n H₃,
      (show targetSlice D hu (neutralMode D i j b) (delta + 1) =
        qField 1 j (vectorFrequencyBound D b + 1) (targetCurrent D hu i) (targetSlice D hu b delta) from
        LatticeHalfFockGroundRightCurrentTransport.native_current_inverse D hu i b delta j),
      supportedNestedRightReadout_eq, nestedRightFiberReadout_eq, hahnTripleScalar_swap]
    exact supportedNestedRightReadout_congr _ _ _ _ _ _ _ _ _ (swapped j)

end
end D5.S3.VertexAlgebra.LatticeHalfFockNestedQReadout
