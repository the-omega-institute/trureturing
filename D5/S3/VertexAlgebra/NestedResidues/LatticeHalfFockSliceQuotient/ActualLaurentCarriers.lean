/- GID: D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSliceQuotient/ActualLaurentCarriers
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSliceQuotient/ActualLaurentCarriers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite homogeneous Laurent carriers for the three-field distribution. -/
import D5.S3.VertexAlgebra.LatticeHalfFockChargedCollision.WeightedLocalCorrelator
import D5.S3.VertexAlgebra.ChargedResidue.Locality
import D5.S3.VertexAlgebra.GroundRightCurrentTransport.NativeDefect
import D5.S3.VertexAlgebra.NestedResidues.ContextualKernelExtraction
import D5.S3.VertexAlgebra.RationalCollision

/-! Actual finite homogeneous Laurent carriers for the three-field distribution.
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

namespace D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFockNormalField LatticeHalfFockCorrectedField
open LatticeHalfFockPhysicalRescaling LatticeHalfFockCurrentBorcherds
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open FieldNormalProductLocality UniformGradedLocalCorrelator
open LatticeHalfFockChargedCollision.WeightedLocalCorrelator
open SupportedFieldWords.OrderedWords
open SupportedFieldWords.ActualFieldWordAdapter
open SupportedWordRationalCollision.ActualPolynomialBridge
open CollisionRationalExpansions.OrderedRationalExpansion
open scoped BigOperators VertexOperator
noncomputable section

/-- An actual original-source slice; the signed lift is unreduced. -/
def targetSlice (D : LatticeData) (hu : IsUnit D.G.det) (a : Carrier D) (s : ℤ) :
    VertexOperator ℂ (ActualTensor D hu) := physicalSlice D hu (correctedField D hu a) s

/-- The physical current with the exact half-frequency normalization. -/
def targetCurrent (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank) :
    VertexOperator ℂ (ActualTensor D hu) := physicalJet D hu (i, 0)

private theorem target_current_mode (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (n : ℤ) :
    (targetCurrent D hu i)[[n]] = LatticeHalfFock.tensorCurrent D (ActualGround D hu) i n := by
  simp [targetCurrent, physicalJet_mode, jetCurrent, jetScalar]

section Residues
universe v
variable {M : Type v} [AddCommGroup M] [Module ℂ M]

/-- The original finite fractional product, using the lawful complete residue. -/
def qField (s r : ℤ) (K : ℕ) (A B : VertexOperator ℂ M) : VertexOperator ℂ M :=
  LatticeHalfFockGroundRightCurrentTransport.Calculus.Q A B s r K

end Residues

private theorem current_slice_locality (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (b : Carrier D) (delta : ℤ) :
    (deltaEnd ^ (vectorFrequencyBound D b + 1))
      (FieldNormalProductLocality.commutator (targetCurrent D hu i) (targetSlice D hu b delta)) = 0 := by
  classical
  let J := targetCurrent D hu i
  let B := targetSlice D hu b delta
  let N := vectorFrequencyBound D b + 1
  funext p q
  apply LinearMap.ext
  intro x
  let A := LatticeHalfFockGroundRightCurrentTransport.Calculus.Z (-p) J
  have shifted (m : ℤ) : A[[m]] = J[[m + p]] := by
    change (LatticeHalfFockGroundRightCurrentTransport.Calculus.Z (-p) J)[[m]] = J[[m + p]]
    rw [LatticeHalfFockGroundRightCurrentTransport.Calculus.Z,
      VertexOperator.ncoeff_of_coeff, VertexOperator.coeff_eq_ncoeff]
    rw [show -(-m - 1 + -p) - 1 = m + p by omega]
  have zero : (∑ᶠ j : ℕ, currentLeftTerm D hu i b delta p q N x j) = 0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro j
    have vanishes := neutralMode_vanish D i b ((N : ℤ) + j) (by dsimp [N]; omega)
    simp [currentLeftTerm, vanishes]
  have law := (current_borcherds D hu i b delta p q N x).2.2.2
  have choose (j : ℕ) : ((Ring.choose (N : ℤ) j : ℤ) : ℂ) = Ring.choose (N : ℂ) j :=
    Ring.map_choose (Int.castRingHom ℂ) (N : ℤ) j
  have first : (∑ᶠ j : ℕ, currentRightFirstTerm D hu i b delta p q N x j) =
      LatticeHalfFockChargedResidue.physicalResidueLeft A B N q x := by
    unfold LatticeHalfFockChargedResidue.physicalResidueLeft
    apply finsum_congr
    intro j
    simp only [LatticeHalfFockChargedResidue.physicalResidueWeight,
      StateFieldResidueReconstruction.integerBinomial, choose, shifted,
      J, B, target_current_mode, targetSlice, physicalSlice_mode, currentRightFirstTerm]
    rw [show p + (N : ℤ) - j = (N : ℤ) - j + p by omega]
    simp only [Int.cast_natCast]
  have second : (∑ᶠ j : ℕ, currentRightSecondTerm D hu i b delta p q N x j) =
      (-1 : ℂ) ^ (N : ℤ) • LatticeHalfFockChargedResidue.physicalResidueRight A B N q x := by
    unfold LatticeHalfFockChargedResidue.physicalResidueRight
    rw [smul_finsum' _ (LatticeHalfFockChargedResidue.physicalResidueRight_finite A B N q x)]
    apply finsum_congr
    intro j
    simp only [LatticeHalfFockChargedResidue.physicalResidueWeight,
      StateFieldResidueReconstruction.integerBinomial, choose, shifted,
      J, B, target_current_mode, targetSlice, physicalSlice_mode, currentRightSecondTerm]
    rw [smul_comm]
    rw [show q + (N : ℤ) - j = (N : ℤ) + q - j by omega,
      add_comm p (j : ℤ)]
    simp only [Int.cast_natCast]
  have residueZero : ((LatticeHalfFockGroundRightCurrentTransport.Calculus.R A B N)[[q]]) x = 0 := by
    rw [← LatticeHalfFockChargedResidue.physicalResidueCoefficient_eq_R,
      LatticeHalfFockChargedResidue.physicalResidueCoefficient, ← first, ← second, ← law, zero]
  rw [LatticeHalfFockGroundRightCurrentTransport.Calculus.R_nat] at residueZero
  have translate : ((deltaEnd ^ N) (FieldNormalProductLocality.commutator A B)) 0 q x =
      ((deltaEnd ^ N) (FieldNormalProductLocality.commutator J B)) p q x := by
    rw [FieldDeltaBinomial.delta_binomial, FieldDeltaBinomial.delta_binomial]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply,
      FieldNormalProductLocality.commutator, LinearMap.sub_apply, Module.End.mul_apply,
      shifted]
    apply Finset.sum_congr rfl
    intro offset member
    rw [show (0 : ℤ) + (N : ℤ) - offset + p = p + (N : ℤ) - offset by omega]
  change ((deltaEnd ^ N) (FieldNormalProductLocality.commutator J B)) p q x = 0
  exact translate.symm.trans residueZero

private theorem source_slice_locality (D : LatticeData) (hu : IsUnit D.G.det)
    (a b : Carrier D) : ∃ order : ℕ, ∀ gamma delta : ℤ,
      (deltaEnd ^ order) (FieldNormalProductLocality.commutator (targetSlice D hu a gamma)
        (targetSlice D hu b delta)) = 0 := by
  obtain ⟨order, law⟩ :=
    LatticeHalfFockAllStatePhysicalLocality.correctedField_physical_locality D hu a b
  refine ⟨order, ?_⟩
  intro gamma delta
  funext left right
  apply LinearMap.ext
  intro x
  rw [FieldDeltaBinomial.delta_binomial]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, FieldNormalProductLocality.commutator,
    targetSlice, physicalSlice_mode, LinearMap.sub_apply, Module.End.mul_apply,
    Pi.zero_apply, LinearMap.zero_apply]
  convert law (-2 * left - gamma - 2) (-2 * right - delta - 2) x using 1
  apply Finset.sum_congr rfl
  intro offset member
  have bound : offset ≤ order := Nat.le_of_lt_succ (Finset.mem_range.mp member)
  rw [Int.natCast_sub bound]
  rw [show -2 * (left + (order : ℤ) - (offset : ℤ)) - gamma - 2 =
      -2 * left - gamma - 2 - 2 * ((order : ℤ) - offset) by omega,
    show -2 * (right + (offset : ℤ)) - delta - 2 =
      -2 * right - delta - 2 - 2 * (offset : ℤ) by omega]

def threeFields (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (a b : Carrier D) (gamma delta : ℤ) : Fin 3 → VertexOperator ℂ (ActualTensor D hu) :=
  ![targetCurrent D hu i, targetSlice D hu a gamma, targetSlice D hu b delta]

/-- Independent current/source, current/source and source/source locality orders. -/
def threeOrders (D : LatticeData) (a b : Carrier D) (K : ℕ) (pair : Fin 3 × Fin 3) : ℕ :=
  if pair.1 = 0 then if pair.2 = 1 then vectorFrequencyBound D a + 1
    else vectorFrequencyBound D b + 1 else K

/-- The common array is an actual polynomial action on the JAB ordering. -/
def actualNumerator (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (a b : Carrier D) (gamma delta : ℤ) (K : ℕ) (x : ActualTensor D hu) :
    Distribution 3 (ActualTensor D hu) :=
  polynomialAction (weightedClearingPolynomial (threeOrders D a b K))
    (coefficientDistribution (threeFields D hu i a b gamma delta) x 1 [0, 1, 2])

private theorem actual_arrays (D : LatticeData) (hu : IsUnit D.G.det)
    (i : Fin D.rank) (a b : Carrier D) :
    ∃ K : ℕ, ∀ gamma delta : ℤ,
    ∀ x : ActualTensor D hu,
        (∀ order : List (Fin 3), [0, 1, 2].Perm order →
          polynomialAction (weightedClearingPolynomial (threeOrders D a b K))
            (coefficientDistribution (threeFields D hu i a b gamma delta) x 1 order) =
          actualNumerator D hu i a b gamma delta K x) ∧
        (∀ label : Fin 3, LowerBoundIn (actualNumerator D hu i a b gamma delta K x) label
          (((HahnModule.of ℂ).symm (threeFields D hu i a b gamma delta label x)).order)) ∧
        (∀ total : ℤ, {e : Exponent 3 | totalExponent e = total ∧
          actualNumerator D hu i a b gamma delta K x e ≠ 0}.Finite) ∧
        (∀ (phi : ActualTensor D hu →ₗ[ℂ] ℂ) (sigma : Equiv.Perm (Fin 3)),
          ∃ cleared : HahnSeries (Indices 3) ℂ,
            (∀ e : Exponent 3, cleared.coeff (orderExponents 3 sigma e) =
              phi (actualNumerator D hu i a b gamma delta K x e)) ∧
            scalarWordCarrier 3 (threeFields D hu i a b gamma delta) sigma x phi =
              (orderedPolynomialFor ℂ 3 sigma
                (weightedClearingPolynomial (threeOrders D a b K)))⁻¹ * cleared) := by
  obtain ⟨K, pairLocal⟩ := source_slice_locality D hu a b
  refine ⟨K, ?_⟩
  intro gamma delta x
  have locality : ∀ first second : Fin 3, first < second →
      (deltaEnd ^ threeOrders D a b K (first, second))
        (FieldNormalProductLocality.commutator (threeFields D hu i a b gamma delta first)
          (threeFields D hu i a b gamma delta second)) = 0 := by
    intro first second less
    fin_cases first <;> fin_cases second <;> norm_num at less
    · exact current_slice_locality D hu i a gamma
    · exact current_slice_locality D hu i b delta
    · exact pairLocal gamma delta
  obtain ⟨permutations, lower, finite⟩ :=
    LatticeHalfFockChargedCollision.WeightedLocalCorrelator.common_cleared_fields
    (threeFields D hu i a b gamma delta) x 1 (threeOrders D a b K) locality
      [0, 1, 2] (by decide) (by intro label; fin_cases label <;> simp)
  refine ⟨(fun order hp => (permutations order hp).symm), lower, finite, ?_⟩
  intro phi sigma
  let Q := weightedClearingPolynomial (threeOrders D a b K)
  let W := scalarWordCarrier 3 (threeFields D hu i a b gamma delta) sigma x phi
  have uniformNonzero : UniformGradedLocalCorrelator.clearingPolynomial 3 1 ≠ 0 :=
    SupportedWordRationalCollision.ActualRationalReconstruction.originalQ_ne_zero 3 0 1
  have pairNonzero : ∀ p ∈ labelledPairs 3, pairPolynomial p.1 p.2 ≠ 0 := by
    simpa only [UniformGradedLocalCorrelator.clearingPolynomial, pow_one] using
      (Finset.prod_ne_zero_iff.mp uniformNonzero)
  have Qnonzero : Q ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact pow_ne_zero _ (pairNonzero p hp)
  have embeddedNonzero : orderedPolynomialFor ℂ 3 sigma Q ≠ 0 := by
    simpa only [map_zero] using (orderedPolynomialFor_injective ℂ 3 sigma).ne Qnonzero
  refine ⟨orderedPolynomialFor ℂ 3 sigma Q * W, ?_, ?_⟩
  · intro e
    have hp : [0, 1, 2].Perm (List.ofFn sigma) :=
      SupportedWordRationalCollision.ActualRationalReconstruction.supplier_order_perm
        [0, 1, 2] (by decide) (by intro label; fin_cases label <;> simp) sigma
    have coefficients : (fun e' => W.coeff (orderExponents 3 sigma e')) =
        (fun e' => phi (coefficientDistribution (threeFields D hu i a b gamma delta)
          x 1 (List.ofFn sigma) e')) := by
      funext e'
      change (scalarWordCarrier 3 (threeFields D hu i a b gamma delta) sigma x phi).coeff
        (exponents 3 (fun label => e' (sigma label))) = _
      rw [scalarWordCarrier_coeff]
      rfl
    rw [ordered_mul_coeff, coefficients, ← scalar_action]
    exact congrArg phi (congrFun (permutations _ hp).symm e)
  · rw [← mul_assoc, inv_mul_cancel₀ embeddedNonzero, one_mul]


end
end D5.S3.VertexAlgebra.LatticeHalfFockLeftCurrentTransport

namespace D5.S3.VertexAlgebra.LatticeHalfFockClearedTaylorReadout
open LatticeHalfFockLeftCurrentTransport UniformGradedLocalCorrelator
open LatticeHalfFockChargedCollision.WeightedLocalCorrelator
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
  obtain ⟨K, checkpoint⟩ := actual_arrays D hu i a b
  refine ⟨K, ?_⟩
  intro gamma delta x phi total
  obtain ⟨permutations, _, finite, carriers⟩ := checkpoint gamma delta x
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

end
end D5.S3.VertexAlgebra.LatticeHalfFockClearedTaylorReadout
