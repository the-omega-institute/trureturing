/- GID: D5/S3/VertexAlgebra/LatticeHalfFockClearedTaylorReadout
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockClearedTaylorReadout
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Homogeneous slices of actual binary cleared words. -/

import D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport

/-! Total-exponent restriction acts on the genuine supported Hahn carriers.
No energy projection or creative vector is introduced. The Hahn operations
and ordered field composition are from mathlib and Scott Carnahan, Apache 2.0. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace D5.S3.VertexAlgebra.LatticeHalfFockClearedTaylorReadout
open LatticeHalfFockLeftCurrentTransport UniformGradedLocalCorrelator
open SupportedFieldWords.OrderedWords SupportedFieldWords.OrderedDistribution
open SupportedFieldWords.ActualFieldWordAdapter
open SupportedWordRationalCollision.ActualPolynomialBridge
open CollisionRationalExpansions.OrderedRationalExpansion
open CollisionLaurentKernels.LaurentCollision
open OrderedCollisionCoordinates.ContextualLaurentKernel
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open scoped BigOperators VertexOperator
noncomputable section

private def degree (n : ℕ) (g : Indices n) : ℤ :=
  totalExponent ((exponentAddEquiv n).symm g)

private theorem degree_add (n : ℕ) (g h : Indices n) :
    degree n (g + h) = degree n g + degree n h := by
  simp only [degree, map_add, totalExponent, Pi.add_apply, Finset.sum_add_distrib]

private def degreeSlice (n : ℕ) (t : ℤ) (F : HahnSeries (Indices n) ℂ) :
    HahnSeries (Indices n) ℂ where
  coeff g := if degree n g = t then F.coeff g else 0
  isPWO_support' := F.isPWO_support.mono (by
    intro g hg
    change (if degree n g = t then F.coeff g else 0) ≠ 0 at hg
    split_ifs at hg
    · exact hg
    · contradiction)

private theorem degreeSlice_support (n : ℕ) (t : ℤ) (F : HahnSeries (Indices n) ℂ) :
    (degreeSlice n t F).support ⊆ F.support := by
  intro g hg
  change (if degree n g = t then F.coeff g else 0) ≠ 0 at hg
  split_ifs at hg
  · exact hg
  · contradiction

private theorem degreeSlice_mul (n : ℕ) (t d : ℤ)
    (H F : HahnSeries (Indices n) ℂ)
    (homogeneous : ∀ g, H.coeff g ≠ 0 → degree n g = d) :
    degreeSlice n (t + d) (H * F) = H * degreeSlice n t F := by
  classical
  ext g
  change (if degree n g = t + d then (H * F).coeff g else 0) = _
  rw [HahnSeries.coeff_mul_right' F.isPWO_support (degreeSlice_support n t F)]
  by_cases target : degree n g = t + d
  · rw [if_pos target, HahnSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro pair hp
    obtain ⟨hH, hF, total⟩ := Finset.mem_antidiagonal.mp hp
    have dp := degree_add n pair.1 pair.2
    rw [total, homogeneous pair.1 hH, target] at dp
    have remaining : degree n pair.2 = t := by omega
    simp only [degreeSlice, remaining, ite_true]
  · rw [if_neg target]
    symm
    apply Finset.sum_eq_zero
    intro pair hp
    obtain ⟨hH, hF, total⟩ := Finset.mem_antidiagonal.mp hp
    have dp := degree_add n pair.1 pair.2
    rw [total, homogeneous pair.1 hH] at dp
    have remaining : degree n pair.2 ≠ t := by omega
    simp only [degreeSlice, remaining, ite_false, mul_zero]

private theorem degree_order (n : ℕ) (sigma : Equiv.Perm (Fin n)) (e : Exponent n) :
    degree n (orderExponents n sigma e) = totalExponent e := by
  rw [degree, orderExponents, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
  change (∑ i, e (sigma i)) = ∑ i, e i
  exact Equiv.sum_comp sigma e

private def slicePolynomial {n : ℕ} (F : Distribution n ℂ) (t : ℤ)
    (finite : {e : Exponent n | totalExponent e = t ∧ F e ≠ 0}.Finite) :
    LabelledPolynomial ℂ n :=
  AddMonoidAlgebra.ofCoeff (Finsupp.ofSupportFinite
    (fun e => if totalExponent e = t then F e else 0) (by
      apply finite.subset
      intro e he
      change (if totalExponent e = t then F e else 0) ≠ 0 at he
      split_ifs at he with ht
      · exact ⟨ht, he⟩
      · contradiction))

private theorem slicePolynomial_coeff {n : ℕ} (F : Distribution n ℂ) (t : ℤ)
    (finite : {e : Exponent n | totalExponent e = t ∧ F e ≠ 0}.Finite)
    (e : Exponent n) :
    (slicePolynomial F t finite).coeff e = if totalExponent e = t then F e else 0 := rfl

private theorem slicePolynomial_carrier {n : ℕ} (F : Distribution n ℂ) (t : ℤ)
    (finite : {e : Exponent n | totalExponent e = t ∧ F e ≠ 0}.Finite)
    (sigma : Equiv.Perm (Fin n)) (H : HahnSeries (Indices n) ℂ)
    (coefficients : ∀ e, H.coeff (orderExponents n sigma e) = F e) :
    orderedPolynomialFor ℂ n sigma (slicePolynomial F t finite) = degreeSlice n t H := by
  ext g
  obtain ⟨e, rfl⟩ := (orderExponents n sigma).surjective g
  rw [ordered_polynomial_coeff, slicePolynomial_coeff]
  change _ = if degree n (orderExponents n sigma e) = t then
    H.coeff (orderExponents n sigma e) else 0
  rw [degree_order, coefficients]

private theorem homogeneous_mul {n : ℕ} (H F : HahnSeries (Indices n) ℂ) (d e : ℤ)
    (hH : ∀ g, H.coeff g ≠ 0 → degree n g = d)
    (hF : ∀ g, F.coeff g ≠ 0 → degree n g = e) :
    ∀ g, (H * F).coeff g ≠ 0 → degree n g = d + e := by
  intro g hg
  obtain ⟨a, ha, b, hb, rfl⟩ := HahnSeries.support_mul_subset hg
  rw [degree_add, hH a ha, hF b hb]

private theorem homogeneous_one (n : ℕ) :
    ∀ g, (1 : HahnSeries (Indices n) ℂ).coeff g ≠ 0 → degree n g = 0 := by
  intro g hg
  have zero : g = 0 := by
    by_contra hn
    exact hg (by simp [HahnSeries.coeff_one, hn])
  subst g
  simp [degree, totalExponent]

private theorem embedded_variable_degree (n : ℕ) (sigma : Equiv.Perm (Fin n)) (i : Fin n) :
    ∀ g, (orderedPolynomialFor ℂ n sigma (variablePolynomial i)).coeff g ≠ 0 →
      degree n g = 1 := by
  intro g hg
  obtain ⟨e, rfl⟩ := (orderExponents n sigma).surjective g
  rw [ordered_polynomial_coeff] at hg
  have same : e = Pi.single i 1 := by
    by_contra different
    exact hg (by simp [variablePolynomial, different])
  rw [degree_order, same]
  simp [totalExponent]

private theorem embedded_pair_degree (n : ℕ) (sigma : Equiv.Perm (Fin n)) (i j : Fin n) :
    ∀ g, (orderedPolynomialFor ℂ n sigma (pairPolynomial i j)).coeff g ≠ 0 →
      degree n g = 1 := by
  intro g hg
  have member : g ∈ (orderedPolynomialFor ℂ n sigma (variablePolynomial i) -
      orderedPolynomialFor ℂ n sigma (variablePolynomial j)).support := by
    change (orderedPolynomialFor ℂ n sigma (variablePolynomial i) -
      orderedPolynomialFor ℂ n sigma (variablePolynomial j)).coeff g ≠ 0
    simpa only [pairPolynomial, map_sub] using hg
  rcases HahnSeries.support_sub_subset _ _ member with first | second
  · exact embedded_variable_degree n sigma i g first
  · exact embedded_variable_degree n sigma j g second

private theorem homogeneous_pow {n : ℕ} (F : HahnSeries (Indices n) ℂ)
    (d : ℤ) (homogeneous : ∀ g, F.coeff g ≠ 0 → degree n g = d) (k : ℕ) :
    ∀ g, (F ^ k).coeff g ≠ 0 → degree n g = (k : ℤ) * d := by
  induction k with
  | zero => simpa only [pow_zero, Nat.cast_zero, zero_mul] using homogeneous_one n
  | succ k ih =>
    simpa only [pow_succ, Nat.cast_succ, add_mul, one_mul] using
      homogeneous_mul (F ^ k) F ((k : ℤ) * d) d ih homogeneous

private theorem clearing_homogeneous {n : ℕ} (sigma : Equiv.Perm (Fin n))
    (orders : Fin n × Fin n → ℕ) :
    ∀ g, (orderedPolynomialFor ℂ n sigma (weightedClearingPolynomial orders)).coeff g ≠ 0 →
      degree n g = ∑ p ∈ labelledPairs n, (orders p : ℤ) := by
  have general (s : Finset (Fin n × Fin n)) :
      ∀ g, (orderedPolynomialFor ℂ n sigma
        (∏ p ∈ s, pairPolynomial p.1 p.2 ^ orders p)).coeff g ≠ 0 →
        degree n g = ∑ p ∈ s, (orders p : ℤ) := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using homogeneous_one n
    | @insert p s hp ih =>
      simp only [Finset.prod_insert hp, map_mul, map_pow, Finset.sum_insert hp]
      exact homogeneous_mul _ _ (orders p) (∑ q ∈ s, (orders q : ℤ))
        (by
          have h := homogeneous_pow _ 1 (embedded_pair_degree n sigma p.1 p.2) (orders p)
          simpa only [mul_one] using h) ih
  simpa only [weightedClearingPolynomial] using general (labelledPairs n)

/-- Every finite total-exponent window of the same actual six-order numerator
is a Laurent polynomial. Its divided ordered expansion gives exactly the
corresponding homogeneous coefficients of each genuine actual word. -/
theorem actual_finite_laurent_carriers (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (a b : Carrier D) :
    ∃ K : ℕ, ∀ (gamma delta : ℤ) (x : ActualTensor D hu)
      (phi : ActualTensor D hu →ₗ[ℂ] ℂ) (total : ℤ),
      ∃ P : LabelledPolynomial ℂ 3,
        (∀ e : Exponent 3, P.coeff e = if totalExponent e = total then
          phi (actualNumerator D hu i a b gamma delta K x e) else 0) ∧
        ∀ (sigma : Equiv.Perm (Fin 3)) (e : Exponent 3),
          (orderedRationalFor ℂ 3 sigma
            (algebraMap _ (CommonRational ℂ 3) P /
              algebraMap _ (CommonRational ℂ 3)
                (weightedClearingPolynomial (threeOrders D a b K)))).coeff
              (orderExponents 3 sigma e) =
            if totalExponent e = total - ∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)
            then phi (coefficientDistribution (threeFields D hu i a b gamma delta)
              x 1 (List.ofFn sigma) e) else 0 := by
  obtain ⟨K, checkpoint⟩ := actual_three_field_numerator D hu i a b
  refine ⟨K, ?_⟩
  intro gamma delta x phi total
  obtain ⟨_, _, _, _, _, arrays⟩ := checkpoint gamma delta
  obtain ⟨permutations, _, finite, carriers⟩ := arrays x
  let F : Distribution 3 ℂ := fun e => phi (actualNumerator D hu i a b gamma delta K x e)
  have scalarFinite : {e : Exponent 3 | totalExponent e = total ∧ F e ≠ 0}.Finite := by
    apply (finite total).subset
    intro e he
    refine ⟨he.1, ?_⟩
    intro hz
    exact he.2 (by simp [F, hz])
  let P := slicePolynomial F total scalarFinite
  refine ⟨P, (fun e => slicePolynomial_coeff F total scalarFinite e), ?_⟩
  intro sigma e
  obtain ⟨C, coefficients, division⟩ := carriers phi sigma
  let Q := weightedClearingPolynomial (threeOrders D a b K)
  let H := orderedPolynomialFor ℂ 3 sigma Q
  let W := scalarWordCarrier 3 (threeFields D hu i a b gamma delta) sigma x phi
  let d : ℤ := ∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)
  have Qnonzero : Q ≠ 0 := by
    have uniformNonzero : UniformGradedLocalCorrelator.clearingPolynomial 3 1 ≠ 0 :=
      SupportedWordRationalCollision.ActualRationalReconstruction.originalQ_ne_zero 3 0 1
    have pairs : ∀ p ∈ labelledPairs 3, pairPolynomial p.1 p.2 ≠ 0 := by
      simpa only [UniformGradedLocalCorrelator.clearingPolynomial, pow_one] using
        Finset.prod_ne_zero_iff.mp uniformNonzero
    exact Finset.prod_ne_zero_iff.mpr (fun p hp => pow_ne_zero _ (pairs p hp))
  have Hnonzero : H ≠ 0 := by
    simpa only [map_zero] using (orderedPolynomialFor_injective ℂ 3 sigma).ne Qnonzero
  have multiplication : H * W = C := by
    change H * W = C
    rw [show W = H⁻¹ * C from division, ← mul_assoc, mul_inv_cancel₀ Hnonzero, one_mul]
  have sliceCarrier := slicePolynomial_carrier F total scalarFinite sigma C coefficients
  have sliced : orderedPolynomialFor ℂ 3 sigma P = H * degreeSlice 3 (total - d) W := by
    rw [sliceCarrier, ← multiplication]
    convert degreeSlice_mul 3 (total - d) d H W (clearing_homogeneous sigma _) using 1 <;>
      simp only [sub_add_cancel]
  have expansion : orderedRationalFor ℂ 3 sigma
      (algebraMap _ (CommonRational ℂ 3) P / algebraMap _ (CommonRational ℂ 3) Q) =
      degreeSlice 3 (total - d) W := by
    rw [map_div₀]
    simp only [orderedRationalFor, IsFractionRing.lift_algebraMap]
    change orderedPolynomialFor ℂ 3 sigma P / H = _
    rw [sliced, mul_div_cancel_left₀ _ Hnonzero]
  change (orderedRationalFor ℂ 3 sigma
    (algebraMap _ (CommonRational ℂ 3) P / algebraMap _ (CommonRational ℂ 3) Q)).coeff
      (orderExponents 3 sigma e) = _
  rw [expansion]
  change (if degree 3 (orderExponents 3 sigma e) = total - d then
    W.coeff (orderExponents 3 sigma e) else 0) = _
  rw [degree_order]
  have wordCoefficient : W.coeff (orderExponents 3 sigma e) =
      phi (coefficientDistribution (threeFields D hu i a b gamma delta)
        x 1 (List.ofFn sigma) e) := by
    rw [show orderExponents 3 sigma e = exponents 3 (fun j => e (sigma j)) by rfl,
      scalarWordCarrier_coeff]
    rfl
  rw [wordCoefficient]

private theorem negative_kernel_choose (k j : ℕ) :
    BinomialKernelDelta.chooseSign (-(k : ℤ) - 1) j = ((k + j).choose k : ℂ) := by
  rw [BinomialKernelDelta.chooseSign,
    show -(k : ℤ) - 1 = -((k : ℤ) + 1) by omega, Ring.choose_neg,
    show (k : ℤ) + 1 + j - 1 = ((k + j : ℕ) : ℤ) by omega,
    Ring.choose_natCast]
  simp only [Units.smul_def, smul_eq_mul, Int.cast_mul,
    Int.cast_negOnePow_natCast, Int.cast_natCast]
  rw [← mul_assoc, ← mul_pow]
  norm_num only [neg_mul_neg, one_mul, one_pow]
  rw [Nat.choose_symm_add]

theorem signed_kernel_choose (k : ℕ) (a : ℤ) :
    (if 0 ≤ a - k then
      BinomialKernelDelta.chooseSign (-(k : ℤ) - 1) (a - k).toNat else 0) -
    StateFieldResidueReconstruction.epsilon (-(k : ℤ) - 1) *
      (if 0 ≤ -a - 1 then
        BinomialKernelDelta.chooseSign (-(k : ℤ) - 1) (-a - 1).toNat else 0) =
    ((Ring.choose a k : ℤ) : ℂ) := by
  by_cases positive : (k : ℤ) ≤ a
  · rw [if_pos (by omega), if_neg (by omega), mul_zero, sub_zero,
      negative_kernel_choose]
    have nonnegative : 0 ≤ a := by omega
    have total : k + (a - k).toNat = a.toNat := by omega
    rw [total, ← Int.toNat_of_nonneg nonnegative, Ring.choose_natCast]
    rfl
  · by_cases nonnegative : 0 ≤ a
    · rw [if_neg (by omega), if_neg (by omega), mul_zero, sub_zero,
        ← Int.toNat_of_nonneg nonnegative, Ring.choose_natCast,
        Nat.choose_eq_zero_of_lt (by omega)]
      simp
    · rw [if_neg (by omega), if_pos (by omega), zero_sub, negative_kernel_choose]
      have aform : a = -(((-a - 1).toNat : ℤ) + 1) := by omega
      conv_rhs => rw [aform, Ring.choose_neg,
        show (((-a - 1).toNat : ℤ) + 1) + k - 1 =
          ((k + (-a - 1).toNat : ℕ) : ℤ) by omega,
        Ring.choose_natCast]
      simp only [Units.smul_def, smul_eq_mul, Int.cast_mul,
        Int.cast_negOnePow_natCast, Int.cast_natCast]
      have sign : -StateFieldResidueReconstruction.epsilon (-(k : ℤ) - 1) =
          (-1 : ℂ) ^ k := by
        unfold StateFieldResidueReconstruction.epsilon
        rw [show -(k : ℤ) - 1 = -((k + 1 : ℕ) : ℤ) by omega,
          zpow_neg, zpow_natCast, ← inv_pow, inv_neg_one, pow_succ]
        ring
      rw [← neg_mul, sign]

private def binarySwap : Equiv.Perm (Fin 2) := Equiv.swap 0 1

private def polynomialTaylor (P : LabelledPolynomial ℂ 2) (k : ℕ) (t : ℤ) : ℂ :=
  Finsupp.linearCombination ℂ (fun e : Exponent 2 =>
    if totalExponent e = t then ((Ring.choose (e 0) k : ℤ) : ℂ) else 0) P.coeff

private theorem backward_kernel_coefficient (r a b : ℤ) :
    (contextPair ℂ 0 0 (kernelXZ ℂ r)).coeff (pairIndex 0 0 (toLex (a, b))) =
      StateFieldResidueReconstruction.epsilon r *
      (if 0 ≤ a then if b = r - a then
        BinomialKernelDelta.chooseSign r a.toNat else 0 else 0) := by
  have constant : contextPair ℂ 0 0
      (HahnSeries.C (HahnSeries.C (StateFieldResidueReconstruction.epsilon r))) =
      HahnSeries.C (StateFieldResidueReconstruction.epsilon r) := by
    simp only [StateFieldResidueReconstruction.epsilon, map_zpow₀, map_neg, map_one]
  rw [D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport.reverse_kernel, map_mul, constant, HahnSeries.C_apply,
    HahnSeries.coeff_single_zero_mul, D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport.binary_kernel_coeff]

private theorem ordered_single (sigma : Equiv.Perm (Fin 2)) (e : Exponent 2) (c : ℂ) :
    orderedPolynomialFor ℂ 2 sigma (AddMonoidAlgebra.single e c) =
      HahnSeries.single (orderExponents 2 sigma e) c := by
  change SupportedFieldWords.FiniteConvolution.scalarPolynomial
    ((AddMonoidAlgebra.domCongr ℂ ℂ (orderExponents 2 sigma))
      (AddMonoidAlgebra.single e c)) = _
  rw [AddMonoidAlgebra.domCongr_single,
    SupportedFieldWords.FiniteConvolution.scalarPolynomial_single]

private theorem finite_polynomial_jump (P : LabelledPolynomial ℂ 2) (k : ℕ) (n : ℤ) :
    (contextPair ℂ 0 0 (kernelZX ℂ (-(k : ℤ) - 1)) *
      orderedPolynomialFor ℂ 2 (Equiv.refl _) P).coeff
        (pairIndex 0 0 (toLex (-n - 1, -1))) -
    (contextPair ℂ 0 0 (kernelXZ ℂ (-(k : ℤ) - 1)) *
      orderedPolynomialFor ℂ 2 binarySwap P).coeff
        (pairIndex 0 0 (toLex (-1, -n - 1))) =
      polynomialTaylor P k ((k : ℤ) - n - 1) := by
  classical
  induction P using AddMonoidAlgebra.induction_linear with
  | zero => simp [polynomialTaylor]
  | add P Q hP hQ =>
    simp only [map_add, mul_add, HahnSeries.coeff_add, polynomialTaylor,
      AddMonoidAlgebra.coeff_add] at hP hQ ⊢
    linear_combination hP + hQ
  | single e c =>
    rw [ordered_single, ordered_single, HahnSeries.coeff_mul_single,
      HahnSeries.coeff_mul_single]
    have first : pairIndex 0 0 (toLex (-n - 1, -1)) -
        orderExponents 2 (Equiv.refl _) e =
        pairIndex 0 0 (toLex (-n - 1 - e 1, -1 - e 0)) := rfl
    have second : pairIndex 0 0 (toLex (-1, -n - 1)) -
        orderExponents 2 binarySwap e =
        pairIndex 0 0 (toLex (-1 - e 0, -n - 1 - e 1)) := by
      simp only [orderExponents, AddEquiv.trans_apply, labelPermutation,
        binarySwap, Equiv.swap_apply_left, Equiv.swap_apply_right]
      rfl
    rw [first, second, D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport.binary_kernel_coeff, backward_kernel_coefficient]
    simp only [polynomialTaylor, AddMonoidAlgebra.coeff_single,
      Finsupp.linearCombination_single, smul_eq_mul]
    have degreeTwo : totalExponent e = e 0 + e 1 := by
      simp [totalExponent, Fin.sum_univ_two]
    by_cases homogeneous : totalExponent e = (k : ℤ) - n - 1
    · rw [if_pos homogeneous]
      rw [degreeTwo] at homogeneous
      have leftIndex : -n - 1 - e 1 = e 0 - k := by omega
      rw [leftIndex]
      have diagonal : -n - 1 - e 1 = -(k : ℤ) - 1 - (-1 - e 0) := by omega
      simp only [if_pos (show -1 - e 0 = -(k : ℤ) - 1 - (e 0 - k) by omega),
        if_pos (show e 0 - k = -(k : ℤ) - 1 - (-1 - e 0) by omega)]
      have signed := signed_kernel_choose k (e 0)
      rw [show -1 - e 0 = -(e 0) - 1 by omega]
      linear_combination c * signed
    · rw [if_neg homogeneous, mul_zero]
      have leftDiagonal : -1 - e 0 ≠ -(k : ℤ) - 1 - (-n - 1 - e 1) := by
        rw [degreeTwo] at homogeneous
        omega
      have rightDiagonal : -n - 1 - e 1 ≠ -(k : ℤ) - 1 - (-1 - e 0) := by
        rw [degreeTwo] at homogeneous
        omega
      simp only [if_neg leftDiagonal, if_neg rightDiagonal, ite_self, mul_zero, sub_self]

private def binaryOrder (reverse : Bool) : Equiv.Perm (Fin 2) :=
  if reverse then binarySwap else Equiv.refl _

private def binaryKernel (reverse : Bool) (r : ℤ) : HahnSeries (Indices 2) ℂ :=
  contextPair ℂ 0 0 (if reverse then kernelXZ ℂ r else kernelZX ℂ r)

private theorem binaryKernel_add (reverse : Bool) (r s : ℤ) :
    binaryKernel reverse (r + s) = binaryKernel reverse r * binaryKernel reverse s := by
  cases reverse <;> simp only [binaryKernel, Bool.false_eq_true, ite_false, ite_true]
  · rw [kernelZX_zpow, kernelZX_zpow, kernelZX_zpow,
      zpow_add₀ (deltaZX_ne_zero ℂ), map_mul]
  · rw [kernelXZ_zpow, kernelXZ_zpow, kernelXZ_zpow,
      zpow_add₀ (deltaXZ_ne_zero ℂ), map_mul]

private theorem binaryKernel_degree (reverse : Bool) (r : ℤ) :
    ∀ g, (binaryKernel reverse r).coeff g ≠ 0 → degree 2 g = r := by
  intro g hg
  let a := (ofLex g).1
  let b := (ofLex (ofLex g).2).1
  have rep : g = pairIndex 0 0 (toLex (a, b)) := rfl
  have deg : degree 2 g = a + b := by
    rw [rep]
    change (∑ j : Fin 2, inverseExponents 2 (pairIndex 0 0 (toLex (a, b))) j) = _
    rw [Fin.sum_univ_two]
    change b + a = a + b
    omega
  rw [deg]
  rw [rep] at hg
  cases reverse <;> simp only [binaryKernel, Bool.false_eq_true, ite_false, ite_true] at hg
  · rw [D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport.binary_kernel_coeff] at hg
    split_ifs at hg with ha hb
    · omega
    all_goals contradiction
  · rw [backward_kernel_coefficient] at hg
    split_ifs at hg with ha hb
    · omega
    all_goals simp_all

private theorem binary_pair_kernel (reverse : Bool) (K : ℕ) :
    orderedPolynomialFor ℂ 2 (binaryOrder reverse) (pairPolynomial 0 1 ^ K) =
      binaryKernel reverse K := by
  have base : orderedPolynomialFor ℂ 2 (binaryOrder reverse) (pairPolynomial 0 1) =
      binaryKernel reverse 1 := by
    cases reverse <;>
      simp only [binaryOrder, binaryKernel, Bool.false_eq_true, ite_false, ite_true,
        kernelZX_zpow, kernelXZ_zpow, zpow_one, pairPolynomial, variablePolynomial,
        map_sub, ordered_single, deltaZX, deltaXZ, T, HahnSeries.C_apply]
    · change _ = contextPair ℂ 0 0 (HahnSeries.single 0 (HahnSeries.single 1 1)) -
        contextPair ℂ 0 0 (HahnSeries.single 1 (HahnSeries.single 0 1))
      rw [OrderedCollisionResidues.LabelledDiagonalResidue.context_single,
        OrderedCollisionResidues.LabelledDiagonalResidue.context_single]
      rfl
    · change _ = contextPair ℂ 0 0 (HahnSeries.single 1 (HahnSeries.single 0 1)) -
        contextPair ℂ 0 0 (HahnSeries.single 0 (HahnSeries.single 1 1))
      rw [OrderedCollisionResidues.LabelledDiagonalResidue.context_single,
        OrderedCollisionResidues.LabelledDiagonalResidue.context_single]
      rfl
  rw [map_pow, base]
  cases reverse <;>
    simp only [binaryKernel, Bool.false_eq_true, ite_false, ite_true,
      kernelZX_zpow, kernelXZ_zpow, zpow_one, zpow_natCast, map_pow]

/-- The labelled binary array is cleared on the same actual input in both orders. -/
def binaryNumerator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B : VertexOperator ℂ V) (K : ℕ) (x : V) : Distribution 2 V :=
  polynomialAction (pairPolynomial 0 1 ^ K)
    (coefficientDistribution ![A, B] x 1 [0, 1])

private theorem binary_finite_carrier {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B : VertexOperator ℂ V) (K : ℕ)
    (locality : (FieldNormalProductLocality.deltaEnd ^ K)
      (FieldNormalProductLocality.commutator A B) = 0)
    (x : V) (phi : V →ₗ[ℂ] ℂ) (t : ℤ) :
    ∃ P : LabelledPolynomial ℂ 2,
      (∀ e, P.coeff e = if totalExponent e = t then
        phi (binaryNumerator A B K x e) else 0) ∧
      ∀ reverse : Bool,
        orderedPolynomialFor ℂ 2 (binaryOrder reverse) P =
          binaryKernel reverse K * degreeSlice 2 (t - K)
            (scalarWordCarrier 2 ![A, B] (binaryOrder reverse) x phi) := by
  classical
  have pairClear : weightedClearingPolynomial (N := 2) (fun _ => K) =
      pairPolynomial 0 1 ^ K := by
    have pairs : labelledPairs 2 = {(0, 1)} := by decide
    simp [weightedClearingPolynomial, pairs]
  have localPairs : ∀ i j : Fin 2, i < j →
      (FieldNormalProductLocality.deltaEnd ^ K)
        (FieldNormalProductLocality.commutator (![A, B] i) (![A, B] j)) = 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at hij
    exact locality
  obtain ⟨permutations, _, finite⟩ := common_cleared_fields ![A, B] x 1
    (fun _ => K) localPairs [0, 1] (by decide) (by intro j; fin_cases j <;> simp)
  simp only [pairClear] at permutations finite
  let F : Distribution 2 ℂ := fun e => phi (binaryNumerator A B K x e)
  have scalarFinite : {e : Exponent 2 | totalExponent e = t ∧ F e ≠ 0}.Finite := by
    apply (finite t).subset
    intro e he
    refine ⟨he.1, ?_⟩
    intro hz
    apply he.2
    change phi ((polynomialAction (pairPolynomial 0 1 ^ K))
      (coefficientDistribution ![A, B] x 1 [0, 1]) e) = 0
    rw [hz, map_zero]
  let P := slicePolynomial F t scalarFinite
  refine ⟨P, (fun e => slicePolynomial_coeff F t scalarFinite e), ?_⟩
  intro reverse
  let sigma := binaryOrder reverse
  let W := scalarWordCarrier 2 ![A, B] sigma x phi
  let H := binaryKernel reverse K
  have coefficients : ∀ e, (H * W).coeff (orderExponents 2 sigma e) = F e := by
    intro e
    have hp : [0, 1].Perm (List.ofFn sigma) :=
      SupportedWordRationalCollision.ActualRationalReconstruction.supplier_order_perm
        [0, 1] (by decide) (by intro j; fin_cases j <;> simp) sigma
    have words : (fun e' => W.coeff (orderExponents 2 sigma e')) =
        (fun e' => phi (coefficientDistribution ![A, B] x 1 (List.ofFn sigma) e')) := by
      funext e'
      change (scalarWordCarrier 2 ![A, B] sigma x phi).coeff
        (exponents 2 (fun j => e' (sigma j))) = _
      rw [scalarWordCarrier_coeff]
      rfl
    rw [show H = orderedPolynomialFor ℂ 2 sigma (pairPolynomial 0 1 ^ K) from
      (binary_pair_kernel reverse K).symm, ordered_mul_coeff, words, ← scalar_action]
    exact congrArg phi (congrFun (permutations _ hp).symm e)
  rw [show orderedPolynomialFor ℂ 2 sigma P = degreeSlice 2 t (H * W) from
    slicePolynomial_carrier F t scalarFinite sigma (H * W) coefficients]
  convert degreeSlice_mul 2 (t - K) K H W (binaryKernel_degree reverse K) using 1 <;>
    simp only [sub_add_cancel]

private theorem binary_extraction {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B : VertexOperator ℂ V) (K : ℕ) (x : V) (phi : V →ₗ[ℂ] ℂ)
    (t r n : ℤ) (reverse : Bool) (P : LabelledPolynomial ℂ 2)
    (carrier : orderedPolynomialFor ℂ 2 (binaryOrder reverse) P =
      binaryKernel reverse K * degreeSlice 2 (t - K)
        (scalarWordCarrier 2 ![A, B] (binaryOrder reverse) x phi))
    (total : t = (K : ℤ) - r - n - 2) :
    (binaryKernel reverse (r - K) * orderedPolynomialFor ℂ 2 (binaryOrder reverse) P).coeff
      (if reverse then pairIndex 0 0 (toLex (-1, -n - 1))
        else pairIndex 0 0 (toLex (-n - 1, -1))) =
    (binaryKernel reverse r *
      scalarWordCarrier 2 ![A, B] (binaryOrder reverse) x phi).coeff
      (if reverse then pairIndex 0 0 (toLex (-1, -n - 1))
        else pairIndex 0 0 (toLex (-n - 1, -1))) := by
  let W := scalarWordCarrier 2 ![A, B] (binaryOrder reverse) x phi
  -- The cleared polynomial itself has degree t. The inverse kernel removes K;
  -- the output exponent of the residue is -n-2 in either chamber.
  have correct : binaryKernel reverse (r - K) *
      orderedPolynomialFor ℂ 2 (binaryOrder reverse) P =
      degreeSlice 2 (t - K + r) (binaryKernel reverse r * W) := by
    rw [carrier, ← mul_assoc, ← binaryKernel_add, sub_add_cancel]
    exact (degreeSlice_mul 2 (t - K) r _ W (binaryKernel_degree reverse r)).symm
  rw [correct]
  change (if degree 2 _ = t - K + r then _ else 0) = _
  rw [if_pos]
  cases reverse
  · change (∑ j : Fin 2, inverseExponents 2
        (pairIndex 0 0 (toLex (-n - 1, -1))) j) = t - K + r
    rw [Fin.sum_univ_two]
    change -1 + (-n - 1) = t - K + r
    omega
  · change (∑ j : Fin 2, inverseExponents 2
        (pairIndex 0 0 (toLex (-1, -n - 1))) j) = t - K + r
    rw [Fin.sum_univ_two]
    change (-n - 1) + -1 = t - K + r
    omega

private theorem binary_residue_taylor {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B : VertexOperator ℂ V) (K : ℕ) (x : V) (phi : V →ₗ[ℂ] ℂ)
    (t r n : ℤ) (k : ℕ) (P : LabelledPolynomial ℂ 2)
    (carrier : ∀ reverse : Bool,
      orderedPolynomialFor ℂ 2 (binaryOrder reverse) P =
        binaryKernel reverse K * degreeSlice 2 (t - K)
          (scalarWordCarrier 2 ![A, B] (binaryOrder reverse) x phi))
    (total : t = (K : ℤ) - r - n - 2) (index : (k : ℤ) = K - r - 1) :
    phi (((ordinaryResidue r A B)[[n]]) x) = polynomialTaylor P k t := by
  have forward := binary_extraction A B K x phi t r n false P (carrier false) total
  have backward := binary_extraction A B K x phi t r n true P (carrier true) total
  have reverseFields : scalarWordCarrier 2 ![A, B] binarySwap x phi =
      scalarWordCarrier 2 ![B, A] id x phi := by
    unfold scalarWordCarrier
    congr 1
    funext j
    fin_cases j <;> rfl
  simp only [binaryKernel, binaryOrder, Bool.false_eq_true, ite_false, ite_true] at forward backward
  change _ = (contextPair ℂ 0 0 (kernelZX ℂ r) *
    scalarWordCarrier 2 ![A, B] id x phi).coeff
      (pairIndex 0 0 (toLex (-n - 1, -1))) at forward
  rw [reverseFields] at backward
  rw [D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport.binary_residue_readout, ← forward, ← backward,
    show r - K = -(k : ℤ) - 1 by omega,
    finite_polynomial_jump P k n, show (k : ℤ) - n - 1 = t by omega]

/-- The complete fractional residue is the finite Taylor readout of its
actual cleared binary array, on every actual tensor input and signed lift. -/
theorem actual_binary_taylor_readout (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (a b : Carrier D) :
    ∃ K : ℕ, ∀ (gamma delta r n : ℤ), r < K →
      ∀ (x : ActualTensor D hu) (phi : ActualTensor D hu →ₗ[ℂ] ℂ),
      ∃ P : LabelledPolynomial ℂ 2,
        (∀ e, P.coeff e = if totalExponent e = (K : ℤ) - r - n - 2 then
          phi (binaryNumerator (targetSlice D hu a gamma)
            (targetSlice D hu b delta) K x e) else 0) ∧
        ∀ s : ℤ, phi (((qField s r K (targetSlice D hu a gamma)
            (targetSlice D hu b delta))[[n]]) x) =
          Finsupp.linearCombination ℂ (fun e : Exponent 2 =>
            if totalExponent e = (K : ℤ) - r - n - 2 then
              Ring.choose ((e 0 : ℂ) - (s : ℂ) / 2) ((K : ℤ) - r - 1).toNat else 0)
            P.coeff := by
  obtain ⟨K, checkpoint⟩ := actual_three_field_numerator D hu i a b
  refine ⟨K, ?_⟩
  intro gamma delta r n below x phi
  let A := targetSlice D hu a gamma
  let B := targetSlice D hu b delta
  let t : ℤ := K - r - n - 2
  let k := ((K : ℤ) - r - 1).toNat
  have kindex : (k : ℤ) = K - r - 1 := by dsimp [k]; omega
  obtain ⟨P, coefficients, carriers⟩ := binary_finite_carrier A B K
    (checkpoint gamma delta).1 x phi t
  refine ⟨P, coefficients, ?_⟩
  intro s
  rw [D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport.qField_mode, map_sum]
  have cutoff : ((K : ℤ) - r).toNat = k + 1 := by omega
  rw [cutoff]
  have residual (ell : ℕ) (member : ell ∈ Finset.range (k + 1)) :
      phi (StateFieldResidueReconstruction.fieldResidueCoefficient
        (r + ell) (n - ell) A B x) = polynomialTaylor P (k - ell) t := by
    have ellBound : ell ≤ k := by simpa using Finset.mem_range.mp member
    rw [← (StateFieldResidueReconstruction.fieldResidue (r + ell) A B).coefficient]
    exact binary_residue_taylor A B K x phi t (r + ell) (n - ell) (k - ell) P
      carriers (by dsimp [t]; omega) (by omega)
  simp only [map_smul, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun ell member =>
    congrArg (Ring.choose (-(s : ℂ) / 2) ell * ·) (residual ell member))]
  -- Equality of linear forms reduces the finite Vandermonde to each monomial.
  have combination (Q : LabelledPolynomial ℂ 2) :
      (∑ ell ∈ Finset.range (k + 1), Ring.choose (-(s : ℂ) / 2) ell *
        polynomialTaylor Q (k - ell) t) =
      Finsupp.linearCombination ℂ (fun e : Exponent 2 =>
        if totalExponent e = t then
          Ring.choose ((e 0 : ℂ) - (s : ℂ) / 2) k else 0) Q.coeff := by
    induction Q using AddMonoidAlgebra.induction_linear with
    | zero => simp [polynomialTaylor]
    | add P Q hP hQ =>
      simp only [polynomialTaylor, AddMonoidAlgebra.coeff_add, map_add, mul_add,
        Finset.sum_add_distrib] at hP hQ ⊢
      rw [hP, hQ]
    | single e c =>
      simp only [polynomialTaylor, AddMonoidAlgebra.coeff_single,
        Finsupp.linearCombination_single, smul_eq_mul]
      by_cases homogeneous : totalExponent e = t
      · simp only [if_pos homogeneous]
        simp_rw [show ∀ j, ((Ring.choose (e 0) j : ℤ) : ℂ) = Ring.choose (e 0 : ℂ) j from
          fun j => Ring.map_choose (Int.castRingHom ℂ) (e 0) j]
        have vandermonde := Ring.add_choose_eq (R := ℂ)
          (r := -(s : ℂ) / 2) (s := (e 0 : ℂ)) k (Commute.all _ _)
        rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at vandermonde
        rw [show (e 0 : ℂ) - (s : ℂ) / 2 = -(s : ℂ) / 2 + (e 0 : ℂ) by ring,
          vandermonde]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ell member
        ring
      · simp only [if_neg homogeneous, mul_zero, Finset.sum_const_zero]
  exact combination P

end
end D5.S3.VertexAlgebra.LatticeHalfFockClearedTaylorReadout
