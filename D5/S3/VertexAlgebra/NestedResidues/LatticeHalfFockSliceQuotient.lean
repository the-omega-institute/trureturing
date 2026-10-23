/- GID: D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSliceQuotient
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSliceQuotient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arbitrary-cutoff compatibility of actual homogeneous Laurent quotients. -/

import D5.S3.VertexAlgebra.LatticeHalfFockNestedQReadout

/-! Finite polynomial actions compare slices of the same actual distribution.
No locality assumption is made on either supplied source/source cutoff.
The slice telescope is that of CollisionTaylor.sameNumeratorCollisionBridge.
The actual supplier and its inherited attribution remain in their source owners. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSliceQuotient
open UniformGradedLocalCorrelator LatticeHalfFockLeftCurrentTransport
open LatticeHalfFockNestedQReadout LatticeHalfFockClearedTaylorReadout
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients LatticeSugawaraCurrents LatticeFiniteNegativeGeneration
open CollisionRationalExpansions.OrderedRationalExpansion
open SupportedFieldWords.FiniteConvolution
open SupportedWordRationalCollision.ActualPolynomialBridge
open scoped BigOperators VertexOperator
noncomputable section

private theorem pair_slice_mul {N : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (i j : Fin N) (F : Distribution N V) (phi : V →ₗ[ℂ] ℂ)
    (P : LaurentPolynomial N) (E : ℤ)
    (coefficients : ∀ e, P.coeff e = if totalExponent e = E then phi (F e) else 0)
    (e : Exponent N) :
    (pairPolynomial i j * P).coeff e =
      if totalExponent e = E + 1 then phi (polynomialAction (pairPolynomial i j) F e)
      else 0 := by
  classical
  have degree (k : Fin N) : totalExponent (e - Pi.single k 1) = totalExponent e - 1 := by
    simp [totalExponent, Finset.sum_sub_distrib]
  have action : phi (polynomialAction (pairPolynomial i j) F e) =
      phi (F (e - Pi.single i 1)) - phi (F (e - Pi.single j 1)) := by
    rw [scalar_action]
    simp [pairPolynomial, variablePolynomial, distributionAction_single]
  rw [action]
  simp only [pairPolynomial, variablePolynomial, sub_mul, AddMonoidAlgebra.coeff_sub,
    Finsupp.sub_apply, AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
  rw [show -Pi.single i (1 : ℤ) + e = e - Pi.single i 1 by abel,
    show -Pi.single j (1 : ℤ) + e = e - Pi.single j 1 by abel, coefficients, coefficients]
  by_cases h : totalExponent e = E + 1
  · rw [ite_eq_left h, ite_eq_left (by rw [degree]; omega), ite_eq_left (by rw [degree]; omega)]
  · rw [ite_eq_right h, ite_eq_right (by rw [degree]; omega), ite_eq_right (by rw [degree]; omega)]
    simp

private theorem pair_pow_slice_mul {N : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (i j : Fin N) (F : Distribution N V) (phi : V →ₗ[ℂ] ℂ)
    (P : LaurentPolynomial N) (E : ℤ)
    (coefficients : ∀ e, P.coeff e = if totalExponent e = E then phi (F e) else 0)
    (p : ℕ) (e : Exponent N) :
    (pairPolynomial i j ^ p * P).coeff e =
      if totalExponent e = E + p then
        phi (polynomialAction (pairPolynomial i j ^ p) F e) else 0 := by
  induction p generalizing e with
  | zero => simpa using coefficients e
  | succ p ih =>
    have step := pair_slice_mul i j (polynomialAction (pairPolynomial i j ^ p) F)
      phi (pairPolynomial i j ^ p * P) (E + p) (fun e => ih e) e
    simpa only [pow_succ', mul_assoc, map_mul, Module.End.mul_apply,
      Nat.cast_succ, add_assoc] using step

private theorem pairs_three : labelledPairs 3 = {(0, 1), (0, 2), (1, 2)} := by
  decide

private theorem clearing_three (D : LatticeData) (a b : Carrier D) (K : ℕ) :
    weightedClearingPolynomial (threeOrders D a b K) =
      pairPolynomial (0 : Fin 3) 1 ^ (vectorFrequencyBound D a + 1) *
      pairPolynomial (0 : Fin 3) 2 ^ (vectorFrequencyBound D b + 1) *
      pairPolynomial (1 : Fin 3) 2 ^ K := by
  simp [weightedClearingPolynomial, pairs_three, threeOrders, mul_assoc]

private theorem orders_three (D : LatticeData) (a b : Carrier D) (K : ℕ) :
    (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) =
      (vectorFrequencyBound D a + 1 : ℕ) + (vectorFrequencyBound D b + 1 : ℕ) + K := by
  simp [pairs_three, threeOrders, add_assoc]

private theorem clearing_pad (D : LatticeData) (a b : Carrier D) (K T : ℕ) (le : K ≤ T) :
    pairPolynomial (1 : Fin 3) 2 ^ (T - K) *
        weightedClearingPolynomial (threeOrders D a b K) =
      weightedClearingPolynomial (threeOrders D a b T) := by
  have exponent : pairPolynomial (1 : Fin 3) 2 ^ T =
      pairPolynomial (1 : Fin 3) 2 ^ K * pairPolynomial (1 : Fin 3) 2 ^ (T - K) := by
    rw [← pow_add, Nat.add_sub_of_le le]
  rw [clearing_three, clearing_three, exponent]
  ring

private theorem pair_ne_zero {N : ℕ} (i j : Fin N) (different : i ≠ j) :
    pairPolynomial i j ≠ 0 := by
  classical
  have exponents : (Pi.single i (1 : ℤ) : Exponent N) ≠ Pi.single j 1 := by
    intro h
    have bad := congrFun h i
    simp [different] at bad
  intro h
  have bad := congrArg (fun Q : LaurentPolynomial N => Q.coeff (Pi.single i 1)) h
  simp [pairPolynomial, variablePolynomial, exponents] at bad

private theorem rational_ne_zero (Q : LabelledPolynomial ℂ 3) (nonzero : Q ≠ 0) :
    algebraMap _ (CommonRational ℂ 3) Q ≠ 0 := by
  intro h
  apply nonzero
  apply IsFractionRing.injective (LabelledPolynomial ℂ 3) (CommonRational ℂ 3)
  simpa only [map_zero] using h

private theorem clearing_ne_zero (D : LatticeData) (a b : Carrier D) (K : ℕ) :
    algebraMap _ (CommonRational ℂ 3)
      (weightedClearingPolynomial (threeOrders D a b K)) ≠ 0 := by
  apply rational_ne_zero
  rw [clearing_three]
  exact mul_ne_zero (mul_ne_zero
    (pow_ne_zero _ (pair_ne_zero 0 1 (by decide)))
    (pow_ne_zero _ (pair_ne_zero 0 2 (by decide))))
    (pow_ne_zero _ (pair_ne_zero 1 2 (by decide)))

/- proof_shape: actual_slice_comparison: content
   admission_basis: escape-witness
   escape_witness: Multiplication by each labelled difference transports the
   exact scalar homogeneous slice by one signed total degree. Iteration and
   commuting polynomial actions on the same actual JAB distribution identify
   the two padded finite numerators, hence their rational quotients. -/
/-- The two original coefficient equations suffice to compare arbitrary
supplied cutoffs. Both padded numerators are the same slice at max K K₀.
Signed Laurent exponents, negative slice degree and zero slices are retained;
neither cutoff is assumed to witness locality. -/
private theorem actual_slice_comparison
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (a b : Carrier D) (K K₀ : ℕ) (gamma delta d r n : ℤ)
    (x : ActualTensor D hu) (phi : ActualTensor D hu →ₗ[ℂ] ℂ)
    (P P₀ : LabelledPolynomial ℂ 3)
    (coefficients : ∀ e : Exponent 3, P.coeff e =
      if totalExponent e =
          (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3
      then phi (actualNumerator D hu i a b gamma delta K x e) else 0)
    (coefficients₀ : ∀ e : Exponent 3, P₀.coeff e =
      if totalExponent e =
          (∑ p ∈ labelledPairs 3, (threeOrders D a b K₀ p : ℤ)) - d - r - n - 3
      then phi (actualNumerator D hu i a b gamma delta K₀ x e) else 0) :
    (pairPolynomial (1 : Fin 3) 2 ^ (max K K₀ - K) * P =
      pairPolynomial (1 : Fin 3) 2 ^ (max K K₀ - K₀) * P₀) ∧
    (algebraMap _ (CommonRational ℂ 3) P /
        algebraMap _ (CommonRational ℂ 3)
          (weightedClearingPolynomial (threeOrders D a b K)) =
      algebraMap _ (CommonRational ℂ 3) P₀ /
        algebraMap _ (CommonRational ℂ 3)
          (weightedClearingPolynomial (threeOrders D a b K₀))) := by
  let T := max K K₀
  have pad_action (k : ℕ) (le : k ≤ T) :
      polynomialAction (pairPolynomial (1 : Fin 3) 2 ^ (T - k))
        (actualNumerator D hu i a b gamma delta k x) =
      actualNumerator D hu i a b gamma delta T x := by
    unfold actualNumerator
    rw [← Module.End.mul_apply, ← map_mul, clearing_pad D a b k T le]
  have slice (k : ℕ) (le : k ≤ T) (Q : LabelledPolynomial ℂ 3)
      (hQ : ∀ e, Q.coeff e =
        if totalExponent e =
            (∑ p ∈ labelledPairs 3, (threeOrders D a b k p : ℤ)) - d - r - n - 3
        then phi (actualNumerator D hu i a b gamma delta k x e) else 0)
      (e : Exponent 3) :
      (pairPolynomial (1 : Fin 3) 2 ^ (T - k) * Q).coeff e =
        if totalExponent e =
            (∑ p ∈ labelledPairs 3, (threeOrders D a b T p : ℤ)) - d - r - n - 3
        then phi (actualNumerator D hu i a b gamma delta T x e) else 0 := by
    have h := pair_pow_slice_mul 1 2 (actualNumerator D hu i a b gamma delta k x)
      phi Q _ hQ (T - k) e
    rw [pad_action k le] at h
    have aligned :
        (∑ p ∈ labelledPairs 3, (threeOrders D a b k p : ℤ)) - d - r - n - 3 +
          (T - k : ℕ) =
        (∑ p ∈ labelledPairs 3, (threeOrders D a b T p : ℤ)) - d - r - n - 3 := by
      rw [orders_three, orders_three]
      omega
    simpa only [aligned] using h
  have numerator : pairPolynomial (1 : Fin 3) 2 ^ (T - K) * P =
      pairPolynomial (1 : Fin 3) 2 ^ (T - K₀) * P₀ := by
    ext e
    rw [slice K (Nat.le_max_left _ _) P coefficients,
      slice K₀ (Nat.le_max_right _ _) P₀ coefficients₀]
  refine ⟨numerator, ?_⟩
  have first : algebraMap _ (CommonRational ℂ 3) P /
        algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K)) =
      algebraMap _ (CommonRational ℂ 3)
          (pairPolynomial (1 : Fin 3) 2 ^ (T - K) * P) /
        algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b T)) := by
    apply (div_eq_div_iff (clearing_ne_zero D a b K) (clearing_ne_zero D a b T)).mpr
    rw [← clearing_pad D a b K T (Nat.le_max_left _ _), map_mul, map_mul]
    ring
  have second : algebraMap _ (CommonRational ℂ 3) P₀ /
        algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K₀)) =
      algebraMap _ (CommonRational ℂ 3)
          (pairPolynomial (1 : Fin 3) 2 ^ (T - K₀) * P₀) /
        algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b T)) := by
    apply (div_eq_div_iff (clearing_ne_zero D a b K₀) (clearing_ne_zero D a b T)).mpr
    rw [← clearing_pad D a b K₀ T (Nat.le_max_right _ _), map_mul, map_mul]
    ring
  rw [first, second, numerator]


/- proof_shape: actual_slice_quotient_compat: content
   admission_basis: escape-witness
   escape_witness: The finite signed slice comparison is consumed by the
   actual complete-field local readouts and outer-support laws. The supplied
   numerator and cutoff are kept; only the rational quotient is transported. -/
/-- Arbitrary-cutoff homogeneous quotient compatibility, with actual complete
left and current/second-source readouts and their complete-field padding laws.
The numerator comparison uses the same JAB distribution at both cutoffs.
The local readouts consume the comparison with the actual locality supplier;
no supplier cutoff replaces K and no Taylor identification is assumed. -/
theorem actual_slice_quotient_compat
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (a b : Carrier D) (K K₀ : ℕ) (gamma delta d r n : ℤ)
    (x : ActualTensor D hu) (phi : ActualTensor D hu →ₗ[ℂ] ℂ)
    (P P₀ : LabelledPolynomial ℂ 3)
    (coefficients : ∀ e : Exponent 3, P.coeff e =
      if totalExponent e =
          (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3
      then phi (actualNumerator D hu i a b gamma delta K x e) else 0)
    (coefficients₀ : ∀ e : Exponent 3, P₀.coeff e =
      if totalExponent e =
          (∑ p ∈ labelledPairs 3, (threeOrders D a b K₀ p : ℤ)) - d - r - n - 3
      then phi (actualNumerator D hu i a b gamma delta K₀ x e) else 0) :
    (pairPolynomial (1 : Fin 3) 2 ^ (max K K₀ - K) * P =
      pairPolynomial (1 : Fin 3) 2 ^ (max K K₀ - K₀) * P₀) ∧
    (algebraMap _ (CommonRational ℂ 3) P /
        algebraMap _ (CommonRational ℂ 3)
          (weightedClearingPolynomial (threeOrders D a b K)) =
      algebraMap _ (CommonRational ℂ 3) P₀ /
        algebraMap _ (CommonRational ℂ 3)
          (weightedClearingPolynomial (threeOrders D a b K₀))) ∧
    ∀ (H₁ H₃ : ℕ) (j : ℤ),
      (phi (((qField (gamma + 1) r H₁
          (targetSlice D hu (neutralMode D i d a) (gamma + 1))
          (targetSlice D hu b delta))[[n]]) x) =
        nestedLeftLocalReadout (gamma + 1) 1 d r n (vectorFrequencyBound D a + 1) H₁
          (algebraMap _ (CommonRational ℂ 3) P /
            algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))) ∧
       ((FieldNormalProductLocality.deltaEnd ^ H₁)
          (FieldNormalProductLocality.commutator
            (targetSlice D hu (neutralMode D i d a) (gamma + 1))
            (targetSlice D hu b delta)) = 0 →
        OuterQCompletion (gamma + 1) r n H₁
          (fun k l => currentSourceLocalQ false 1 d (vectorFrequencyBound D a + 1) k l
            (algebraMap _ (CommonRational ℂ 3) P /
              algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))))
          (fun k l => currentSourceLocalQ true 1 d (vectorFrequencyBound D a + 1) l k
            (algebraMap _ (CommonRational ℂ 3) P /
              algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K)))))) ∧
      (phi (((qField gamma (d + r - j) H₃ (targetSlice D hu a gamma)
          (targetSlice D hu (neutralMode D i j b) (delta + 1)))[[n]]) x) =
        nestedRightLocalReadout 0 gamma 1 j (d + r - j) n (vectorFrequencyBound D b + 1) H₃
          (algebraMap _ (CommonRational ℂ 3) P /
            algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))) ∧
       ((FieldNormalProductLocality.deltaEnd ^ H₃)
          (FieldNormalProductLocality.commutator (targetSlice D hu a gamma)
            (targetSlice D hu (neutralMode D i j b) (delta + 1))) = 0 →
        OuterQCompletion gamma (d + r - j) n H₃
          (fun k l => lastSourceLocalQ 0 true 1 j (vectorFrequencyBound D b + 1) l k
            (algebraMap _ (CommonRational ℂ 3) P /
              algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K))))
          (fun k l => lastSourceLocalQ 0 false 1 j (vectorFrequencyBound D b + 1) k l
            (algebraMap _ (CommonRational ℂ 3) P /
              algebraMap _ (CommonRational ℂ 3) (weightedClearingPolynomial (threeOrders D a b K)))))) := by
  have comparison := actual_slice_comparison D hu i a b K K₀ gamma delta d r n x phi
    P P₀ coefficients coefficients₀
  obtain ⟨K₁, supplier⟩ := actual_nested_outer_completion D hu i a b
  obtain ⟨P₁, coefficients₁, readouts, completions⟩ := supplier gamma delta d r n x phi
  have same := (actual_slice_comparison D hu i a b K K₁ gamma delta d r n x phi
    P P₁ coefficients coefficients₁).2
  refine ⟨comparison.1, comparison.2, ?_⟩
  intro H₁ H₃ j
  rw [same]
  obtain ⟨_, _, _, _, _, _, _, _, _, left, _, right⟩ := readouts H₁ 0 H₃ j
  obtain ⟨leftCompletion, _, rightCompletion⟩ := completions H₁ 0 H₃ j
  exact ⟨⟨left, leftCompletion⟩, ⟨right, rightCompletion⟩⟩

end
end D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSliceQuotient
