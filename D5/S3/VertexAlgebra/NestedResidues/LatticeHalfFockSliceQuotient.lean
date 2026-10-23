/- GID: D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSliceQuotient
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSliceQuotient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Arbitrary-cutoff compatibility of actual homogeneous Laurent quotients. -/
import D5.S3.VertexAlgebra.LatticeHalfFockChargedCollision.WeightedLocalCorrelator
import D5.S3.VertexAlgebra.ChargedResidue.Locality
import D5.S3.VertexAlgebra.GroundRightCurrentTransport.NativeDefect
import D5.S3.VertexAlgebra.NestedResidues.ContextualKernelExtraction
import D5.S3.VertexAlgebra.RationalCollision

/-! Arbitrary-cutoff actual homogeneous Laurent quotients. The privately consumed
finite-slice, two-branch extraction and signed-collision proofs retain their
original research substance at e7115cf0e88dde8f45861e42cd51d8a39473c0fe.
Classical local-field calculus: Matsuo--Nagatomo; twisted lattice setting:
Bakalov--Kac, math/0402315. No literature novelty or final Taylor bridge is claimed.
Hahn/Laurent kernels: mathlib, Apache 2.0 (Aaron Anderson, María Inés de
Frutos-Fernández, Filippo A. E. Nuccio); partial fractions: Kevin Buzzard,
Sidharth Hariharan, Aaron Liu. Actual field composition: Scott Carnahan,
vertexAlg 4453e34ec390e82a0c789c731ada8f9a6e86bdea, Apache 2.0.
Only actual_slice_quotient_compat is a public mathematical result of this owner.
The other public names are the original data required by its full telescope. -/

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

private theorem actual_finite_laurent_carriers (D : LatticeData) (hu : IsUnit D.G.det)
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

namespace D5.S3.VertexAlgebra.LatticeHalfFockNestedQReadout
open LatticeHalfFockLeftCurrentTransport LatticeHalfFockClearedTaylorReadout
open NestedResidues.ContextualKernelExtraction
open UniformGradedLocalCorrelator
open LatticeHalfFockChargedCollision.WeightedLocalCorrelator
open SupportedFieldWords.OrderedWords SupportedFieldWords.OrderedDistribution
open CollisionRationalExpansions.OrderedRationalExpansion
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeFiniteNegativeGeneration LatticeSugawaraCurrents
open scoped BigOperators VertexOperator
noncomputable section

section NestedReadout
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
open StateFieldResidueReconstruction
def supportedQReadout (s r : ℤ) (K : ℕ) (n : ℤ)
    (forward backward : ℤ → ℤ → ℂ) : ℂ :=
  ∑ ell ∈ Finset.range ((K : ℤ) - r).toNat,
    Ring.choose (-(s : ℂ) / 2) ell *
      ((∑ᶠ u : ℕ, BinomialKernelDelta.chooseSign (r + ell) u *
          forward (r + ell - u) (n - ell + u)) -
       epsilon (r + ell) *
        ∑ᶠ u : ℕ, BinomialKernelDelta.chooseSign (r + ell) u *
          backward (r + n - u) u)

private theorem supportedQReadout_eq (s r : ℤ) (K : ℕ)
    (A B : VertexOperator ℂ V) (x : V) (n : ℤ) (phi : V →ₗ[ℂ] ℂ) :
    phi (((qField s r K A B)[[n]]) x) = supportedQReadout s r K n
      (fun m k => phi ((A[[m]]) ((B[[k]]) x)))
      (fun m k => phi ((B[[m]]) ((A[[k]]) x))) := by
  rw [qField, LatticeHalfFockGroundRightCurrentTransport.Calculus.Q_mode, map_sum]
  apply Finset.sum_congr rfl
  intro ell hell
  rw [map_smul, ← LatticeHalfFockChargedResidue.physicalResidueCoefficient_eq_R]
  congr 1
  unfold LatticeHalfFockChargedResidue.physicalResidueCoefficient
    LatticeHalfFockChargedResidue.physicalResidueLeft
    LatticeHalfFockChargedResidue.physicalResidueRight
  rw [map_sub, map_smul,
    map_finsum phi (LatticeHalfFockChargedResidue.physicalResidueLeft_finite A B (r + ell) (n - ell) x),
    map_finsum phi (LatticeHalfFockChargedResidue.physicalResidueRight_finite A B (r + ell) (n - ell) x)]
  simp only [map_smul, smul_eq_mul, BinomialKernelDelta.chooseSign,
    LatticeHalfFockChargedResidue.physicalResidueWeight, integerBinomial,
    StateFieldResidueReconstruction.epsilon,
    show r + (ell : ℤ) + (n - ell) = r + n by omega]

/-- The complete ordinary outer residue at fractional offset ell. The two
ordered contributions are combined before any outer support assertion. -/
def completeOuterResidue (r n : ℤ) (f g : ℤ → ℤ → ℂ) (ell : ℕ) : ℂ :=
  (∑ᶠ u : ℕ, BinomialKernelDelta.chooseSign (r + ell) u *
    f (r + ell - u) (n - ell + u)) -
  epsilon (r + ell) * ∑ᶠ u : ℕ,
    BinomialKernelDelta.chooseSign (r + ell) u * g (r + n - u) u

/-- The fractional series is summed only after forming each complete residue. -/
def completeOuterQReadout (s r n : ℤ) (f g : ℤ → ℤ → ℂ) : ℂ :=
  ∑ᶠ ell : ℕ, Ring.choose (-(s : ℂ) / 2) ell * completeOuterResidue r n f g ell

/-- A locality order bounds the support of the complete residue, and every
larger fractional cutoff computes its unrestricted, finitely supported sum. -/
def OuterQCompletion (s r n : ℤ) (H : ℕ) (f g : ℤ → ℤ → ℂ) : Prop :=
  Function.support (completeOuterResidue r n f g) ⊆
    (Finset.range ((H : ℤ) - r).toNat : Set ℕ) ∧
  ∀ H' : ℕ, H ≤ H' →
    supportedQReadout s r H' n f g = completeOuterQReadout s r n f g

private theorem qField_high (s r : ℤ) (A B : VertexOperator ℂ V) (H H' : ℕ)
    (locality : (FieldNormalProductLocality.deltaEnd ^ H)
      (FieldNormalProductLocality.commutator A B) = 0)
    (high : (H : ℤ) ≤ r) : qField s r H' A B = 0 := by
  classical
  unfold qField LatticeHalfFockGroundRightCurrentTransport.Calculus.Q
  apply Finset.sum_eq_zero
  intro ell member
  have valid := LatticeHalfFockGroundRightCurrentTransport.Calculus.valid_of_locality A B H locality
  rw [valid (r + ell) (by omega)]
  suffices LatticeHalfFockGroundRightCurrentTransport.Calculus.Z (ell : ℤ)
      (0 : VertexOperator ℂ V) = 0 by simp [this]
  apply HVertexOperator.coeff_inj
  funext e
  apply LinearMap.ext
  intro x
  rw [VertexOperator.coeff_eq_ncoeff, VertexOperator.coeff_eq_ncoeff]
  rw [LatticeHalfFockGroundRightCurrentTransport.Calculus.Z, VertexOperator.ncoeff_of_coeff]
  rfl

private theorem completeOuterResidue_single (s r n : ℤ)
    (f g : ℤ → ℤ → ℂ) (ell : ℕ) (nonnegative : 0 ≤ r + ell) :
    completeOuterResidue r n f g ell =
      supportedQReadout s (r + ell) ((r + ell).toNat + 1) (n - ell) f g := by
  have cutoff : (((r + ell).toNat + 1 : ℕ) : ℤ) - (r + ell) = 1 := by omega
  simp only [supportedQReadout, cutoff, Int.toNat_one, Finset.sum_range_one,
    Ring.choose_zero_right, one_mul]
  unfold completeOuterResidue
  simp only [Nat.cast_zero, add_zero, sub_zero,
    show r + (ell : ℤ) + (n - ell) = r + n by omega]

private theorem completeOuterQReadout_of_support (s r n : ℤ) (H : ℕ)
    (f g : ℤ → ℤ → ℂ)
    (support : Function.support (completeOuterResidue r n f g) ⊆
      (Finset.range ((H : ℤ) - r).toNat : Set ℕ)) :
    OuterQCompletion s r n H f g := by
  classical
  refine ⟨support, ?_⟩
  intro H' larger
  unfold completeOuterQReadout
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range ((H' : ℤ) - r).toNat) (by
    intro ell nonzero
    have original : ell ∈ Finset.range ((H : ℤ) - r).toNat :=
      support (Function.mem_support.mpr (fun zero => nonzero (by simp [zero])))
    apply Finset.mem_range.mpr
    have bound := Finset.mem_range.mp original
    omega)]
  rfl

private theorem completeOuterQReadout_of_locality (s r n : ℤ) (H : ℕ)
    (A B : VertexOperator ℂ V) (x : V) (phi : V →ₗ[ℂ] ℂ)
    (f g : ℤ → ℤ → ℂ)
    (locality : (FieldNormalProductLocality.deltaEnd ^ H)
      (FieldNormalProductLocality.commutator A B) = 0)
    (matched : ∀ ell : ℕ, (H : ℤ) ≤ r + ell →
      supportedQReadout s (r + ell) ((r + ell).toNat + 1) (n - ell) f g =
        phi (((qField s (r + ell) ((r + ell).toNat + 1) A B)[[n - ell]]) x)) :
    OuterQCompletion s r n H f g := by
  apply completeOuterQReadout_of_support
  intro ell nonzero
  apply Finset.mem_range.mpr
  by_contra outside
  have high : (H : ℤ) ≤ r + ell := by omega
  apply nonzero
  rw [completeOuterResidue_single s r n f g ell (by omega), matched ell high,
    qField_high s (r + ell) A B H _ locality high]
  simp

private theorem supportedQReadout_congr (s r : ℤ) (K : ℕ) (n : ℤ)
    (f g f' g' : ℤ → ℤ → ℂ)
    (hf : ∀ m k, m + k = r + n → f m k = f' m k)
    (hg : ∀ m k, m + k = r + n → g m k = g' m k) :
    supportedQReadout s r K n f g = supportedQReadout s r K n f' g' := by
  unfold supportedQReadout
  apply Finset.sum_congr rfl
  intro ell hell
  congr 2
  · apply finsum_congr
    intro u
    rw [hf _ _ (by omega)]
  · congr 1
    apply finsum_congr
    intro u
    rw [hg _ _ (by omega)]

open CollisionLaurentKernels.LaurentCollision
open OrderedCollisionCoordinates.ContextualLaurentKernel
private theorem reverse_kernel (r : ℤ) :
    kernelXZ ℂ r = (HahnSeries.C (HahnSeries.C (StateFieldResidueReconstruction.epsilon r))) * kernelZX ℂ r := by
  unfold kernelXZ kernelZX StateFieldResidueReconstruction.epsilon
  rw [neg_eq_neg_one_mul, mul_zpow, map_mul]
  simp only [map_zpow₀, map_neg, map_one]
  ring


private def triplePermutation (order : Fin 6) : Equiv.Perm (Fin 3) :=
  ![Equiv.refl _, Equiv.swap 1 2, Equiv.swap 0 1,
    Equiv.ofBijective ![1, 2, 0] (by decide),
    Equiv.ofBijective ![2, 0, 1] (by decide), Equiv.swap 0 2] order

private def tripleScalar (A B C : VertexOperator ℂ V) (x : V)
    (phi : V →ₗ[ℂ] ℂ) (order : Fin 6) (modes : Exponent 3) : ℂ :=
  phi (coefficientDistribution ![A, B, C] x 1
    (List.ofFn (triplePermutation order)) (fun j => -modes j - 1))
private def supportedNestedLeftReadout (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (R : Fin 6 → Exponent 3 → ℂ) : ℂ :=
  supportedQReadout outerLift r H n
    (fun k l => supportedQReadout innerLift d K k
      (fun m p => R 0 ![m, p, l]) (fun m p => R 2 ![p, m, l]))
    (fun k l => supportedQReadout innerLift d K l
      (fun m p => R 4 ![m, p, k]) (fun m p => R 5 ![p, m, k]))

/-- The right nesting retains both complete inner differences before taking
the outer supported residue. -/
private def supportedNestedRightReadout (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (R : Fin 6 → Exponent 3 → ℂ) : ℂ :=
  supportedQReadout outerLift r H n
    (fun k l => supportedQReadout innerLift d K l
      (fun m p => R 0 ![k, m, p]) (fun m p => R 1 ![k, p, m]))
    (fun k l => supportedQReadout innerLift d K k
      (fun m p => R 3 ![l, m, p]) (fun m p => R 5 ![l, p, m]))
open CollisionLaurentKernels.LaurentCollision
open OrderedCollisionCoordinates.ContextualLaurentKernel
open CollisionRationalExpansions.HahnFiberResidue
open CollisionRationalExpansions.FullOrderSpectatorPole
private def leftPairFiberQ (s d : ℤ) (K : ℕ) (k l : ℤ)
    (F G : HahnSeries (Indices 3) ℂ) : ℂ :=
  ∑ ell ∈ Finset.range ((K : ℤ) - d).toNat,
    Ring.choose (-(s : ℂ) / 2) ell *
      ((pullFiber (firstEmbedding 0 1 (-1))
        (contextPair ℂ 0 1 (kernelZX ℂ (d + ell)) * F)).coeff
          (exponents 2 ![-k + ell - 1, -l - 1]) -
       (residue 1 1 (contextPair ℂ 0 1 (kernelXZ ℂ (d + ell)) * G)).coeff
          (exponents 2 ![-k + ell - 1, -l - 1]))

/-- The adjacent fractional residue with the spectator on the left. -/
private def rightPairFiberQ (s d : ℤ) (K : ℕ) (k l : ℤ)
    (F G : HahnSeries (Indices 3) ℂ) : ℂ :=
  ∑ ell ∈ Finset.range ((K : ℤ) - d).toNat,
    Ring.choose (-(s : ℂ) / 2) ell *
      ((pullFiber (firstEmbedding 1 0 (-1))
        (contextPair ℂ 1 0 (kernelZX ℂ (d + ell)) * F)).coeff
          (exponents 2 ![-l - 1, -k + ell - 1]) -
       (residue 2 0 (contextPair ℂ 1 0 (kernelXZ ℂ (d + ell)) * G)).coeff
          (exponents 2 ![-l - 1, -k + ell - 1]))

private theorem leftPairFiberQ_eq (s d : ℤ) (K : ℕ) (k l : ℤ)
    (F G : HahnSeries (Indices 3) ℂ) :
    leftPairFiberQ s d K k l F G = supportedQReadout s d K k
      (fun m p => F.coeff (exponents 3 ![-m - 1, -p - 1, -l - 1]))
      (fun m p => G.coeff (exponents 3 ![-m - 1, -p - 1, -l - 1])) := by
  unfold leftPairFiberQ supportedQReadout
  apply Finset.sum_congr rfl
  intro ell hell
  congr 2
  · change (contextPair ℂ 0 1 (kernelZX ℂ (d + ell)) * F).coeff _ = _
    rw [(contextual_kernel_extraction ℂ 0 1 (d + ell) F _).2]
    apply finsum_congr
    intro u
    congr 1
    congr 1
    have kernelIndex : pairIndex 0 1 (toLex ((u : ℤ), d + ell - u)) =
        (exponentAddEquiv 3) ![d + ell - u, (u : ℤ), 0] := by
      have base : (0 : Indices 0) = () := by
        change (0 : Unit) = ()
        exact Subsingleton.elim _ _
      change toLex ((0 : ℤ), toLex ((u : ℤ), toLex (d + ell - u, (0 : Indices 0)))) =
        toLex ((0 : ℤ), toLex ((u : ℤ), toLex (d + ell - u, ())))
      rw [base]
      rfl
    rw [kernelIndex]
    change (exponentAddEquiv 3) ![-1, -k + ell - 1, -l - 1] - (exponentAddEquiv 3) ![d + ell - u, (u : ℤ), 0] =
      (exponentAddEquiv 3) ![-(d + ell - u) - 1, -(k - ell + u) - 1, -l - 1]
    rw [← map_sub]
    congr 1
    funext j
    fin_cases j <;> simp <;> omega
  · have constant : contextPair ℂ 0 1
        (HahnSeries.C (HahnSeries.C (epsilon (d + ell)))) =
        HahnSeries.C (epsilon (d + ell)) := by
      simp only [StateFieldResidueReconstruction.epsilon, map_zpow₀, map_neg, map_one]
    change (contextPair ℂ 0 1 (kernelXZ ℂ (d + ell)) * G).coeff _ = _
    rw [reverse_kernel,
      map_mul, constant, mul_assoc, HahnSeries.C_apply,
      HahnSeries.coeff_single_zero_mul,
      (contextual_kernel_extraction ℂ 0 1 (d + ell) G _).2]
    congr 1
    apply finsum_congr
    intro u
    congr 1
    congr 1
    have kernelIndex : pairIndex 0 1 (toLex ((u : ℤ), d + ell - u)) =
        (exponentAddEquiv 3) ![d + ell - u, (u : ℤ), 0] := by
      have base : (0 : Indices 0) = () := by
        change (0 : Unit) = ()
        exact Subsingleton.elim _ _
      change toLex ((0 : ℤ), toLex ((u : ℤ), toLex (d + ell - u, (0 : Indices 0)))) =
        toLex ((0 : ℤ), toLex ((u : ℤ), toLex (d + ell - u, ())))
      rw [base]
      rfl
    rw [kernelIndex]
    change (exponentAddEquiv 3) ![-k + ell - 1, -1, -l - 1] - (exponentAddEquiv 3) ![d + ell - u, (u : ℤ), 0] =
      (exponentAddEquiv 3) ![-(d + k - u) - 1, -(u : ℤ) - 1, -l - 1]
    rw [← map_sub]
    congr 1
    funext j
    fin_cases j <;> simp <;> omega

private theorem rightPairFiberQ_eq (s d : ℤ) (K : ℕ) (k l : ℤ)
    (F G : HahnSeries (Indices 3) ℂ) :
    rightPairFiberQ s d K k l F G = supportedQReadout s d K k
      (fun m p => F.coeff (exponents 3 ![-l - 1, -m - 1, -p - 1]))
      (fun m p => G.coeff (exponents 3 ![-l - 1, -m - 1, -p - 1])) := by
  unfold rightPairFiberQ supportedQReadout
  apply Finset.sum_congr rfl
  intro ell hell
  congr 2
  · change (contextPair ℂ 1 0 (kernelZX ℂ (d + ell)) * F).coeff _ = _
    rw [(contextual_kernel_extraction ℂ 1 0 (d + ell) F _).2]
    apply finsum_congr
    intro u
    congr 1
    congr 1
    have kernelIndex : pairIndex 1 0 (toLex ((u : ℤ), d + ell - u)) =
        (exponentAddEquiv 3) ![0, d + ell - u, (u : ℤ)] := by
      have base : (0 : Indices 0) = () := by
        change (0 : Unit) = ()
        exact Subsingleton.elim _ _
      change toLex ((u : ℤ), toLex (d + ell - u, toLex ((0 : ℤ), (0 : Indices 0)))) =
        toLex ((u : ℤ), toLex (d + ell - u, toLex ((0 : ℤ), ())))
      rw [base]
      rfl
    rw [kernelIndex]
    change (exponentAddEquiv 3) ![-l - 1, -1, -k + ell - 1] - (exponentAddEquiv 3) ![0, d + ell - u, (u : ℤ)] =
      (exponentAddEquiv 3) ![-l - 1, -(d + ell - u) - 1, -(k - ell + u) - 1]
    rw [← map_sub]
    congr 1
    funext j
    fin_cases j <;> simp <;> omega
  · have constant : contextPair ℂ 1 0
        (HahnSeries.C (HahnSeries.C (epsilon (d + ell)))) =
        HahnSeries.C (epsilon (d + ell)) := by
      simp only [StateFieldResidueReconstruction.epsilon, map_zpow₀, map_neg, map_one]
    change (contextPair ℂ 1 0 (kernelXZ ℂ (d + ell)) * G).coeff _ = _
    rw [reverse_kernel,
      map_mul, constant, mul_assoc, HahnSeries.C_apply,
      HahnSeries.coeff_single_zero_mul,
      (contextual_kernel_extraction ℂ 1 0 (d + ell) G _).2]
    congr 1
    apply finsum_congr
    intro u
    congr 1
    congr 1
    have kernelIndex : pairIndex 1 0 (toLex ((u : ℤ), d + ell - u)) =
        (exponentAddEquiv 3) ![0, d + ell - u, (u : ℤ)] := by
      have base : (0 : Indices 0) = () := by
        change (0 : Unit) = ()
        exact Subsingleton.elim _ _
      change toLex ((u : ℤ), toLex (d + ell - u, toLex ((0 : ℤ), (0 : Indices 0)))) =
        toLex ((u : ℤ), toLex (d + ell - u, toLex ((0 : ℤ), ())))
      rw [base]
      rfl
    rw [kernelIndex]
    change (exponentAddEquiv 3) ![-l - 1, -k + ell - 1, -1] - (exponentAddEquiv 3) ![0, d + ell - u, (u : ℤ)] =
      (exponentAddEquiv 3) ![-l - 1, -(d + k - u) - 1, -(u : ℤ) - 1]
    rw [← map_sub]
    congr 1
    funext j
    fin_cases j <;> simp <;> omega

/-- Scalar readouts from six genuinely supported, globally labelled carriers. -/
private def hahnTripleScalar (W : Fin 6 → HahnSeries (Indices 3) ℂ)
    (order : Fin 6) (modes : Exponent 3) : ℂ :=
  (W order).coeff (orderExponents 3 (triplePermutation order) (fun j => -modes j - 1))

/-- Left nested supported fibers. The complete inner difference is kept
inside each of the two outer residue fibers. -/
private def nestedLeftFiberReadout (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (W : Fin 6 → HahnSeries (Indices 3) ℂ) : ℂ :=
  supportedQReadout outerLift r H n
    (fun k l => leftPairFiberQ innerLift d K k l (W 0) (W 2))
    (fun k l => rightPairFiberQ innerLift d K l k (W 4) (W 5))

/-- Right nested supported fibers, with the actual left and right spectator
positions retained in the respective complete orders. -/
private def nestedRightFiberReadout (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (W : Fin 6 → HahnSeries (Indices 3) ℂ) : ℂ :=
  supportedQReadout outerLift r H n
    (fun k l => rightPairFiberQ innerLift d K l k (W 0) (W 1))
    (fun k l => leftPairFiberQ innerLift d K k l (W 3) (W 5))

private theorem nestedLeftFiberReadout_eq (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (W : Fin 6 → HahnSeries (Indices 3) ℂ) :
    nestedLeftFiberReadout outerLift innerLift d r n K H W =
      supportedNestedLeftReadout outerLift innerLift d r n K H (hahnTripleScalar W) := by
  unfold nestedLeftFiberReadout supportedNestedLeftReadout
  apply supportedQReadout_congr
  · intro k l hkl
    rw [leftPairFiberQ_eq]
    rfl
  · intro k l hkl
    rw [rightPairFiberQ_eq]
    rfl

private theorem nestedRightFiberReadout_eq (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (W : Fin 6 → HahnSeries (Indices 3) ℂ) :
    nestedRightFiberReadout outerLift innerLift d r n K H W =
      supportedNestedRightReadout outerLift innerLift d r n K H (hahnTripleScalar W) := by
  unfold nestedRightFiberReadout supportedNestedRightReadout
  apply supportedQReadout_congr
  · intro k l hkl
    rw [rightPairFiberQ_eq]
    rfl
  · intro k l hkl
    rw [leftPairFiberQ_eq]
    rfl


private theorem supportedNestedLeftReadout_congr (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (R S : Fin 6 → Exponent 3 → ℂ)
    (same : ∀ order modes, (∑ j, modes j) = d + r + n → R order modes = S order modes) :
    supportedNestedLeftReadout outerLift innerLift d r n K H R =
      supportedNestedLeftReadout outerLift innerLift d r n K H S := by
  unfold supportedNestedLeftReadout
  apply supportedQReadout_congr <;> intro k l hkl <;> apply supportedQReadout_congr <;>
    intro m p hmp <;> apply same <;> simp [Fin.sum_univ_three] <;> omega

private theorem supportedNestedRightReadout_congr (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (R S : Fin 6 → Exponent 3 → ℂ)
    (same : ∀ order modes, (∑ j, modes j) = d + r + n → R order modes = S order modes) :
    supportedNestedRightReadout outerLift innerLift d r n K H R =
      supportedNestedRightReadout outerLift innerLift d r n K H S := by
  unfold supportedNestedRightReadout
  apply supportedQReadout_congr <;> intro k l hkl <;> apply supportedQReadout_congr <;>
    intro m p hmp <;> apply same <;> simp [Fin.sum_univ_three] <;> omega

private theorem supportedNestedLeftReadout_eq (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (A B C : VertexOperator ℂ V) (x : V) (phi : V →ₗ[ℂ] ℂ) :
    phi (((qField outerLift r H (qField innerLift d K A B) C)[[n]]) x) =
      supportedNestedLeftReadout outerLift innerLift d r n K H (tripleScalar A B C x phi) := by
  rw [supportedQReadout_eq]
  unfold supportedNestedLeftReadout
  apply supportedQReadout_congr
  · intro k l hkl
    rw [supportedQReadout_eq]
    congr 1 <;> funext m p <;>
      simp [tripleScalar, triplePermutation, coefficientDistribution, word,
        Module.End.mul_apply, Equiv.swap_apply_def]
  · intro k l hkl
    change (phi.comp (C[[k]])) (((qField innerLift d K A B)[[l]]) x) = _
    rw [supportedQReadout_eq]
    congr 1 <;> funext m p <;>
      simp [tripleScalar, triplePermutation, coefficientDistribution, word,
        Module.End.mul_apply, LinearMap.comp_apply, Equiv.swap_apply_def]

private theorem supportedNestedRightReadout_eq (outerLift innerLift d r n : ℤ) (K H : ℕ)
    (A B C : VertexOperator ℂ V) (x : V) (phi : V →ₗ[ℂ] ℂ) :
    phi (((qField outerLift r H A (qField innerLift d K B C))[[n]]) x) =
      supportedNestedRightReadout outerLift innerLift d r n K H (tripleScalar A B C x phi) := by
  rw [supportedQReadout_eq]
  unfold supportedNestedRightReadout
  apply supportedQReadout_congr
  · intro k l hkl
    change (phi.comp (A[[k]])) (((qField innerLift d K B C)[[l]]) x) = _
    rw [supportedQReadout_eq]
    congr 1 <;> funext m p <;>
      simp [tripleScalar, triplePermutation, coefficientDistribution, word,
        Module.End.mul_apply, LinearMap.comp_apply, Equiv.swap_apply_def]
  · intro k l hkl
    rw [supportedQReadout_eq]
    congr 1 <;> funext m p <;>
      simp [tripleScalar, triplePermutation, coefficientDistribution, word,
        Module.End.mul_apply, Equiv.swap_apply_def]

end NestedReadout

private def rationalTripleReadout (D : LatticeData) (a b : Carrier D) (K : ℕ)
    (P : LabelledPolynomial ℂ 3) (order : Fin 6) (modes : Exponent 3) : ℂ :=
  (orderedRationalFor ℂ 3 (triplePermutation order)
    (algebraMap _ (CommonRational ℂ 3) P /
      algebraMap _ (CommonRational ℂ 3)
        (weightedClearingPolynomial (threeOrders D a b K)))).coeff
    (orderExponents 3 (triplePermutation order) (fun j => -modes j - 1))

/-- Exchange the current and first-source labels without changing the
numerator, its clearing factors, or the six supported orders. -/
private def swapCurrentSourceReadout (R : Fin 6 → Exponent 3 → ℂ)
    (order : Fin 6) (modes : Exponent 3) : ℂ :=
  R (![2, 3, 0, 1, 5, 4] order) ![modes 1, modes 0, modes 2]

/-- The six supported Hahn expansions of the unchanged common rational. -/
private def rationalTripleCarriers (D : LatticeData) (a b : Carrier D) (K : ℕ)
    (P : LabelledPolynomial ℂ 3) (order : Fin 6) : HahnSeries (Indices 3) ℂ :=
  orderedRationalFor ℂ 3 (triplePermutation order)
    (algebraMap _ (CommonRational ℂ 3) P /
      algebraMap _ (CommonRational ℂ 3)
        (weightedClearingPolynomial (threeOrders D a b K)))

/-- Relabel the current and first source while retaining the actual word
positions of every supported coefficient. -/
private def swapCurrentSourceCarriers (W : Fin 6 → HahnSeries (Indices 3) ℂ)
    (order : Fin 6) : HahnSeries (Indices 3) ℂ :=
  W (![2, 3, 0, 1, 5, 4] order)

private theorem hahnTripleScalar_swap (W : Fin 6 → HahnSeries (Indices 3) ℂ) :
    hahnTripleScalar (swapCurrentSourceCarriers W) =
      swapCurrentSourceReadout (hahnTripleScalar W) := by
  funext order modes
  fin_cases order <;>
    simp [hahnTripleScalar, swapCurrentSourceCarriers, swapCurrentSourceReadout,
      triplePermutation, orderExponents, labelPermutation, Equiv.swap_apply_def] <;>
    congr 1 <;> congr 1 <;> funext j <;> fin_cases j <;>
    simp [Equiv.swap_apply_def]

private theorem tripleScalar_swap {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B C : VertexOperator ℂ V) (x : V) (phi : V →ₗ[ℂ] ℂ) :
    tripleScalar B A C x phi = swapCurrentSourceReadout (tripleScalar A B C x phi) := by
  funext order modes
  fin_cases order <;>
    simp [tripleScalar, swapCurrentSourceReadout, triplePermutation,
      coefficientDistribution, word, Module.End.mul_apply, Equiv.swap_apply_def]

end
end D5.S3.VertexAlgebra.LatticeHalfFockNestedQReadout

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

private def currentSourceTau (reverse : Bool) :
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

private theorem weighted_local_fiber (pre post : ℕ)
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

private def lastSourceTau (z : Fin 2) (spectatorLeft : Bool) :
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

private theorem actual_two_branch_supplier (D : LatticeData) (hu : IsUnit D.G.det)
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

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSliceQuotient
open UniformGradedLocalCorrelator LatticeHalfFockLeftCurrentTransport
open LatticeHalfFockChargedCollision.WeightedLocalCorrelator
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

private theorem clearing_ne_zero (D : LatticeData) (a b : Carrier D) (K : ℕ) :
    algebraMap _ (CommonRational ℂ 3)
      (weightedClearingPolynomial (threeOrders D a b K)) ≠ 0 := by
  have uniformNonzero : UniformGradedLocalCorrelator.clearingPolynomial 3 1 ≠ 0 :=
    SupportedWordRationalCollision.ActualRationalReconstruction.originalQ_ne_zero 3 0 1
  have pairs : ∀ p ∈ labelledPairs 3, pairPolynomial p.1 p.2 ≠ 0 := by
    simpa only [UniformGradedLocalCorrelator.clearingPolynomial, pow_one] using
      Finset.prod_ne_zero_iff.mp uniformNonzero
  have nonzero : weightedClearingPolynomial (threeOrders D a b K) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun p hp => pow_ne_zero _ (pairs p hp))
  simpa only [map_zero] using
    (IsFractionRing.injective (LabelledPolynomial ℂ 3) (CommonRational ℂ 3)).ne nonzero

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
  classical
  have comparison := actual_slice_comparison D hu i a b K K₀ gamma delta d r n x phi
    P P₀ coefficients coefficients₀
  obtain ⟨K₁, actual⟩ := actual_two_branch_supplier D hu i a b
  obtain ⟨P₁, coefficients₁, readouts⟩ := actual gamma delta d r n x phi
  have same := (actual_slice_comparison D hu i a b K K₁ gamma delta d r n x phi
    P P₁ coefficients coefficients₁).2
  refine ⟨comparison.1, comparison.2, ?_⟩
  intro H₁ H₃ j
  rw [same]
  have identify (d' r' n' : ℤ) (degree : d' + r' + n' = d + r + n)
      (P' : LabelledPolynomial ℂ 3)
      (coefficients' : ∀ e : Exponent 3, P'.coeff e =
        if totalExponent e =
            (∑ p ∈ labelledPairs 3, (threeOrders D a b K₁ p : ℤ)) - d' - r' - n' - 3
        then phi (actualNumerator D hu i a b gamma delta K₁ x e) else 0) : P' = P₁ := by
    apply AddMonoidAlgebra.coeff_injective
    ext e
    rw [coefficients', coefficients₁,
      show (∑ p ∈ labelledPairs 3, (threeOrders D a b K₁ p : ℤ)) - d' - r' - n' - 3 =
        (∑ p ∈ labelledPairs 3, (threeOrders D a b K₁ p : ℤ)) - d - r - n - 3 by omega]
  refine ⟨⟨(readouts H₁ H₃ j).1, ?_⟩, ⟨(readouts H₁ H₃ j).2, ?_⟩⟩
  · intro locality
    apply completeOuterQReadout_of_locality (gamma + 1) r n H₁
      (targetSlice D hu (neutralMode D i d a) (gamma + 1))
      (targetSlice D hu b delta) x phi _ _ locality
    intro ell high
    obtain ⟨P', coefficients', shifted⟩ := actual gamma delta d (r + ell) (n - ell) x phi
    have identical := identify d (r + ell) (n - ell) (by omega) P' coefficients'
    subst P'
    exact (shifted ((r + ell).toNat + 1) 0 0).1.symm
  · intro locality
    apply completeOuterQReadout_of_locality gamma (d + r - j) n H₃
      (targetSlice D hu a gamma)
      (targetSlice D hu (neutralMode D i j b) (delta + 1)) x phi _ _ locality
    intro ell high
    obtain ⟨P', coefficients', shifted⟩ := actual gamma delta (d + ell) r (n - ell) x phi
    have identical := identify (d + ell) r (n - ell) (by omega) P' coefficients'
    subst P'
    have equation := (shifted 0 ((d + r - j + ell).toNat + 1) j).2.symm
    simpa only [show d + (ell : ℤ) + r - j = d + r - j + ell by omega,
      nestedRightLocalReadout] using equation

end
end D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSliceQuotient
