import D5.S3.VertexAlgebra.FormalDeltaDistribution
import D5.S3.VertexAlgebra.BcGhostSuperJacobi

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi

open FormalDeltaDistribution BcGhostFockSupport BcGhostSuperGenerators
open BcGhostSuperStateField BcGhostSuperBorcherdsTerms BcGhostSuperJacobi SuperFieldProducts
open scoped VertexOperator

noncomputable section

def atomOperator (region : Region) (left right : Carrier) (atom : Atom) : Module.End ℂ Carrier :=
  deltaDistribution region (deltaExponent region atom.power atom.offset) •
    match region with
    | .forward => ((Y left)[[atom.inner]]) * ((Y right)[[atom.outer]])
    | .reverse => ((Y right)[[atom.outer]]) * ((Y left)[[atom.inner]])
    | .iterate => ((Y (((Y left)[[atom.inner]]) right))[[atom.outer]])

def regionDistribution (region : Region) (left right vector : Carrier) : Distribution Carrier :=
  coefficientAction region (fun atom => atomOperator region left right atom vector)

theorem forward_resolved (parameter first last : ℤ) (left right vector : Carrier) (offset : ℕ) :
    atomOperator .forward left right
      (resolvedAtom .forward (modeExponent parameter first last) offset) vector =
        jacobiRightFirstTerm first last parameter left right vector offset := by
  rw [resolved_forward]
  simp only [atomOperator, delta_coefficient]
  rfl

theorem reverse_resolved (parameter first last : ℤ) (left right vector : Carrier) (offset : ℕ) :
    atomOperator .reverse left right
      (resolvedAtom .reverse (modeExponent parameter first last) offset) vector =
        jacobiRightSecondTerm 1 first last parameter left right vector offset := by
  rw [resolved_reverse]
  simp [atomOperator, delta_coefficient, deltaWeight, epsilon_neg,
    jacobiRightSecondTerm, exchangeEpsilon, mu,
    LinearMap.smul_apply, Module.End.mul_apply, smul_smul, mul_comm]

theorem iterate_resolved (parameter first last : ℤ) (left right vector : Carrier) (offset : ℕ) :
    atomOperator .iterate left right
      (resolvedAtom .iterate (modeExponent parameter first last) offset) vector =
        borcherdsLeftTerm first parameter last left right vector offset := by
  rw [resolved_iterate]
  simp only [atomOperator, delta_coefficient, deltaWeight,
    LinearMap.smul_apply, signed_negative_binomial]
  rfl

theorem region_finite_modes (region : Region) (parameter first last : ℤ)
    (left right vector : Carrier) :
    Function.HasFiniteSupport (fun offset => atomOperator region left right
      (resolvedAtom region (modeExponent parameter first last) offset) vector) := by
  cases region
  · simpa only [forward_resolved] using firstTerm_finite first last parameter left right vector
  · simpa only [reverse_resolved] using secondTerm_finite 1 first last parameter left right vector
  · simpa only [iterate_resolved] using borcherds_left_finite first parameter last left right vector

theorem region_finite (region : Region) (exponent : Exponent) (left right vector : Carrier) :
    Function.HasFiniteSupport (fun offset => atomOperator region left right
      (resolvedAtom region exponent offset) vector) := by
  obtain ⟨indices, rfl⟩ := modeExponent_surjective exponent
  exact region_finite_modes region indices.1 indices.2.1 indices.2.2 left right vector

theorem region_fiber_finite (region : Region) (exponent : Exponent) (left right vector : Carrier) :
    Function.HasFiniteSupport (fun atom : coefficientFiber region exponent =>
      atomOperator region left right atom.val vector) :=
  coefficient_support region (fun atom => atomOperator region left right atom vector)
    exponent (region_finite region exponent left right vector)

theorem forward_coefficient (parameter first last : ℤ) (left right vector : Carrier) :
    regionDistribution .forward left right vector (modeExponent parameter first last) =
      ∑ᶠ offset : ℕ, jacobiRightFirstTerm first last parameter left right vector offset := by
  rw [regionDistribution, coefficient_extract .forward _ _
    (region_finite_modes .forward parameter first last left right vector)]
  simp only [forward_resolved]

theorem reverse_coefficient (parameter first last : ℤ) (left right vector : Carrier) :
    regionDistribution .reverse left right vector (modeExponent parameter first last) =
      ∑ᶠ offset : ℕ, jacobiRightSecondTerm 1 first last parameter left right vector offset := by
  rw [regionDistribution, coefficient_extract .reverse _ _
    (region_finite_modes .reverse parameter first last left right vector)]
  simp only [reverse_resolved]

theorem iterate_coefficient (parameter first last : ℤ) (left right vector : Carrier) :
    regionDistribution .iterate left right vector (modeExponent parameter first last) =
      borcherdsLeft first parameter last left right vector := by
  rw [regionDistribution, coefficient_extract .iterate _ _
    (region_finite_modes .iterate parameter first last left right vector)]
  simp only [iterate_resolved, borcherdsLeft]

theorem regionDistribution_add (region : Region) (left right firstVector secondVector : Carrier) :
    regionDistribution region left right (firstVector + secondVector) =
      regionDistribution region left right firstVector + regionDistribution region left right secondVector := by
  funext exponent
  change (∑ᶠ atom : coefficientFiber region exponent,
      atomOperator region left right atom.val (firstVector + secondVector)) = _
  simp only [map_add]
  exact finsum_add_distrib (region_fiber_finite region exponent left right firstVector)
    (region_fiber_finite region exponent left right secondVector)

theorem regionDistribution_smul (region : Region) (left right vector : Carrier) (scalar : ℂ) :
    regionDistribution region left right (scalar • vector) =
      scalar • regionDistribution region left right vector := by
  funext exponent
  change (∑ᶠ atom : coefficientFiber region exponent,
      atomOperator region left right atom.val (scalar • vector)) = _
  simp only [map_smul]
  exact (smul_finsum' scalar (region_fiber_finite region exponent left right vector)).symm

def operatorDistribution (region : Region) (left right : Carrier) :
    Distribution (Module.End ℂ Carrier) := fun exponent =>
  { toFun := fun vector => regionDistribution region left right vector exponent
    map_add' := fun firstVector secondVector =>
      congrFun (regionDistribution_add region left right firstVector secondVector) exponent
    map_smul' := fun scalar vector =>
      congrFun (regionDistribution_smul region left right vector scalar) exponent }

def signedProductDistribution (leftParity rightParity : ℕ) (left right vector : Carrier) :
    Distribution Carrier :=
  regionDistribution .forward left right vector -
    koszul leftParity rightParity • regionDistribution .reverse left right vector

theorem signed_product_coefficient (leftParity rightParity : ℕ) (parameter first last : ℤ)
    (left right vector : Carrier) :
    signedProductDistribution leftParity rightParity left right vector
      (modeExponent parameter first last) =
        borcherdsRight leftParity rightParity first parameter last left right vector := by
  rw [signedProductDistribution, Pi.sub_apply, Pi.smul_apply,
    forward_coefficient, reverse_coefficient, right_split]
  congr 1
  rw [smul_finsum' (koszul leftParity rightParity)
    (secondTerm_finite 1 first last parameter left right vector)]
  apply finsum_congr
  intro offset
  simp only [jacobiRightSecondTerm, exchangeEpsilon, mul_one, smul_smul]
  congr 1
  ring

theorem distribution_jacobi_iff_borcherds (leftParity rightParity : ℕ) (left right vector : Carrier) :
    regionDistribution .iterate left right vector =
      signedProductDistribution leftParity rightParity left right vector ↔
        ∀ first parameter last : ℤ,
          BorcherdsEquation leftParity rightParity first parameter last left right vector := by
  rw [distribution_eq_iff_modes]
  simp only [iterate_coefficient, signed_product_coefficient, BorcherdsEquation]
  constructor <;> intro identity first parameter last <;> exact identity parameter first last

theorem homogeneous_formal_delta_jacobi (leftParity rightParity : ℕ) (left right vector : Carrier)
    (leftHomogeneous : left ∈ homogeneous leftParity)
    (rightHomogeneous : right ∈ homogeneous rightParity) :
    regionDistribution .iterate left right vector =
      signedProductDistribution leftParity rightParity left right vector := by
  apply (distribution_jacobi_iff_borcherds leftParity rightParity left right vector).mpr
  intro first parameter last
  exact borcherds leftParity rightParity left right vector leftHomogeneous rightHomogeneous
    first last parameter

def mixedProductDistribution (left right vector : Carrier) : Distribution Carrier :=
  ∑ leftParity ∈ Finset.range 2, ∑ rightParity ∈ Finset.range 2,
    signedProductDistribution leftParity rightParity
      (parityPart leftParity left) (parityPart rightParity right) vector

def signedResolvedTerm (leftParity rightParity : ℕ) (exponent : Exponent)
    (left right vector : Carrier) (offset : ℕ) : Carrier :=
  atomOperator .forward left right (resolvedAtom .forward exponent offset) vector -
    koszul leftParity rightParity •
      atomOperator .reverse left right (resolvedAtom .reverse exponent offset) vector

theorem signed_resolved_finite (leftParity rightParity : ℕ) (exponent : Exponent)
    (left right vector : Carrier) :
    Function.HasFiniteSupport (signedResolvedTerm leftParity rightParity exponent left right vector) :=
  (region_finite .forward exponent left right vector).sub
    ((region_finite .reverse exponent left right vector).smul_right
      (fun _ => koszul leftParity rightParity))

theorem signed_coefficient_resolved_sum (leftParity rightParity : ℕ) (exponent : Exponent)
    (left right vector : Carrier) :
    signedProductDistribution leftParity rightParity left right vector exponent =
      ∑ᶠ offset : ℕ, signedResolvedTerm leftParity rightParity exponent left right vector offset := by
  have forwardFinite := region_finite .forward exponent left right vector
  have reverseFinite := region_finite .reverse exponent left right vector
  rw [signedProductDistribution, Pi.sub_apply, Pi.smul_apply, regionDistribution,
    regionDistribution, coefficient_extract .forward _ _ forwardFinite,
    coefficient_extract .reverse _ _ reverseFinite,
    smul_finsum' (koszul leftParity rightParity) reverseFinite]
  exact (finsum_sub_distrib forwardFinite
    (reverseFinite.smul_right (fun _ => koszul leftParity rightParity))).symm

def mixedResolvedTerm (exponent : Exponent) (left right vector : Carrier) (offset : ℕ) : Carrier :=
  ∑ leftParity ∈ Finset.range 2, ∑ rightParity ∈ Finset.range 2,
    signedResolvedTerm leftParity rightParity exponent
      (parityPart leftParity left) (parityPart rightParity right) vector offset

theorem mixed_resolved_finite (exponent : Exponent) (left right vector : Carrier) :
    Function.HasFiniteSupport (mixedResolvedTerm exponent left right vector) := by
  unfold mixedResolvedTerm
  apply Function.HasFiniteSupport.sum
  intro leftParity
  apply Function.HasFiniteSupport.sum
  intro rightParity
  exact signed_resolved_finite leftParity rightParity exponent
    (parityPart leftParity left) (parityPart rightParity right) vector

theorem mixed_coefficient_resolved_sum (exponent : Exponent) (left right vector : Carrier) :
    mixedProductDistribution left right vector exponent =
      ∑ᶠ offset : ℕ, mixedResolvedTerm exponent left right vector offset := by
  simp only [mixedProductDistribution, Finset.sum_apply, signed_coefficient_resolved_sum]
  simp only [mixedResolvedTerm]
  rw [finsum_sum_comm (Finset.range 2)]
  · apply Finset.sum_congr rfl
    intro leftParity member
    exact (finsum_sum_comm (Finset.range 2) _ (fun rightParity _ =>
      signed_resolved_finite leftParity rightParity exponent
        (parityPart leftParity left) (parityPart rightParity right) vector)).symm
  · intro leftParity member
    exact Function.HasFiniteSupport.sum (fun rightParity =>
      signed_resolved_finite leftParity rightParity exponent
        (parityPart leftParity left) (parityPart rightParity right) vector) (Finset.range 2)

theorem mixed_product_coefficient (parameter first last : ℤ) (left right vector : Carrier) :
    mixedProductDistribution left right vector (modeExponent parameter first last) =
      mixedBorcherdsRight first parameter last left right vector := by
  simp only [mixedProductDistribution, Finset.sum_apply, signed_product_coefficient,
    mixedBorcherdsRight]

theorem mixed_distribution_jacobi_iff_borcherds (left right vector : Carrier) :
    regionDistribution .iterate left right vector = mixedProductDistribution left right vector ↔
      ∀ first parameter last : ℤ, MixedBorcherdsEquation first parameter last left right vector := by
  rw [distribution_eq_iff_modes]
  simp only [iterate_coefficient, mixed_product_coefficient, MixedBorcherdsEquation]
  constructor <;> intro identity first parameter last <;> exact identity parameter first last

theorem mixed_formal_delta_jacobi (left right vector : Carrier) :
    regionDistribution .iterate left right vector = mixedProductDistribution left right vector := by
  apply (mixed_distribution_jacobi_iff_borcherds left right vector).mpr
  exact fun first parameter last => mixed_borcherds first parameter last left right vector

theorem homogeneous_operator_formal_delta_jacobi (leftParity rightParity : ℕ) (left right : Carrier)
    (leftHomogeneous : left ∈ homogeneous leftParity)
    (rightHomogeneous : right ∈ homogeneous rightParity) :
    operatorDistribution .iterate left right = operatorDistribution .forward left right -
      koszul leftParity rightParity • operatorDistribution .reverse left right := by
  funext exponent
  apply LinearMap.ext
  intro vector
  exact congrFun (homogeneous_formal_delta_jacobi leftParity rightParity left right vector
    leftHomogeneous rightHomogeneous) exponent

theorem mixed_operator_formal_delta_jacobi (left right : Carrier) :
    operatorDistribution .iterate left right =
      ∑ leftParity ∈ Finset.range 2, ∑ rightParity ∈ Finset.range 2,
        (operatorDistribution .forward (parityPart leftParity left) (parityPart rightParity right) -
          koszul leftParity rightParity • operatorDistribution .reverse
            (parityPart leftParity left) (parityPart rightParity right)) := by
  funext exponent
  apply LinearMap.ext
  intro vector
  have identity := congrFun (mixed_formal_delta_jacobi left right vector) exponent
  simpa only [mixedProductDistribution, signedProductDistribution, Finset.sum_apply,
    LinearMap.sum_apply, LinearMap.sub_apply, LinearMap.smul_apply, operatorDistribution,
    LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, Pi.smul_apply] using identity

end

end D5.S3.VertexAlgebra.BcGhostFormalDeltaJacobi
