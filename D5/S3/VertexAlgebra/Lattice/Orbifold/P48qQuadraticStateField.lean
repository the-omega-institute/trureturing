/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qQuadraticStateField
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The normal-ordered quadratic field with its diagonal contraction correction. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qConformalVectorDecomposition
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedCurrentDiagonal
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedGeneratorVacuum

/-!
The P48q twisted field on the neutral span of the vacuum, currents, and their
actual lattice `(-1)`-products. The quadratic coefficients are the
pointwise finite normal order plus the diagonally regularized contraction.
The coefficient of `x^(-M-6)` uses total signed current index `M`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qQuadraticStateField

open LatticeGeneratingFieldLocality (Carrier Oscillator)
open LatticeAllStateField (vacuum)
open LatticeAllStateReconstruction (mu)
open LatticeActualConformalState (currentState)
open P48qTwistedChargeAction (lattice)
open P48qThirdTwistedField (Cartan State concreteChargedField)
open P48qTwistedHeisenberg
open P48qFixedCurrentIterate (coverBound normalOrderedTerm)
open P48qTwistedGeneratorVacuum (concreteChargedField_zero_coeff)
open P48qConformalVectorDecomposition (currentPair)
open ThirdEigenspacePairing (p48qAction p48qForm)
open ThirdTwistedIterate (currentAlong)
open MvPolynomial
open scoped BigOperators

open private project_adjoint cube_square from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedHeisenberg
open private formSymmetric from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField
open private currentPair_eq_sum from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qConformalVectorDecomposition
open private current_product from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMovingPairIterate

attribute [local instance] LieRing.ofAssociativeRing

noncomputable section

local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)

private theorem zetaPrimitive : IsPrimitiveRoot ζ 3 :=
  IsPrimitiveRoot.coe_units_iff.mpr ThirdTwistedChargeCocycle.zeta_primitive

private theorem root_cube (r : ℕ) : (ζ ^ r) ^ 3 = 1 := by
  rw [pow_right_comm, zetaPrimitive.pow_eq_one, one_pow]

/-- The all-residue normal order at total signed current index `M`. -/
abbrev orderedTerm (M : ℤ) (u v : Cartan) (k : ℤ) : Module.End ℂ State :=
  normalOrderedTerm (mode u) (mode v) M k

theorem orderedTerm_currentField (M : ℤ) (u v : Cartan) (k : ℤ) :
    orderedTerm M u v k = normalOrderedTerm
      (fun j => HVertexOperator.coeff (currentField u) (-j - 3))
      (fun j => HVertexOperator.coeff (currentField v) (-j - 3)) M k := by
  have h (j : ℤ) : -(-j - 3) - 3 = j := by omega
  simp only [orderedTerm, normalOrderedTerm, currentField_coeff, h]

private theorem mode_mul_comm_of_sign (u v : Cartan) (k l : ℤ)
    (h : (k < 0 ∧ l < 0) ∨ (0 ≤ k ∧ 0 ≤ l)) :
    mode u k * mode v l = mode v l * mode u k := by
  have hz : ⁅mode u k, mode v l⁆ = 0 := by
    rw [mode_commutator]
    by_cases hs : k + l = 0
    · have hk : k = 0 := by rcases h with h | h <;> omega
      simp [hs, hk]
    · rw [if_neg hs]
  exact sub_eq_zero.mp (by simpa only [Ring.lie_def] using hz)

theorem orderedTerm_swap (M : ℤ) (u v : Cartan) (k : ℤ) :
    orderedTerm M u v k = orderedTerm M v u (M - k) := by
  simp only [orderedTerm, normalOrderedTerm, show M - (M - k) = k by omega]
  by_cases hk : k < 0 <;> by_cases hl : M - k < 0
  · simp only [hk, hl, if_true]
    exact mode_mul_comm_of_sign u v k (M - k) (Or.inl ⟨hk, hl⟩)
  · simp only [hk, hl, if_true, if_false]
  · simp only [hk, hl, if_true, if_false]
  · simp only [hk, hl, if_false]
    exact mode_mul_comm_of_sign v u (M - k) k (Or.inr ⟨le_of_not_gt hl, le_of_not_gt hk⟩)

private theorem orderedTerm_zero_of_bound (M : ℤ) (u v : Cartan) (k : ℤ) (w : State)
    (hk : (coverBound w : ℤ) < k) : orderedTerm M u v k w = 0 := by
  have hneg : ¬ k < 0 := by omega
  simp only [orderedTerm, normalOrderedTerm, if_neg hneg, Module.End.mul_apply,
    mode_eq_zero_above_coverBound w u k hk, map_zero]

theorem orderedTerm_support (M : ℤ) (u v : Cartan) (w : State) :
    Function.support (fun k => orderedTerm M u v k w) ⊆
      (Finset.Icc (M - (coverBound w : ℤ)) (coverBound w : ℤ) : Set ℤ) := by
  intro k hk
  change orderedTerm M u v k w ≠ 0 at hk
  change k ∈ Finset.Icc (M - (coverBound w : ℤ)) (coverBound w : ℤ)
  apply Finset.mem_Icc.mpr
  refine ⟨le_of_not_gt ?_, le_of_not_gt ?_⟩
  · intro h
    apply hk
    rw [orderedTerm_swap]
    exact orderedTerm_zero_of_bound M v u (M - k) w (by omega)
  · exact fun h => hk (orderedTerm_zero_of_bound M u v k w h)

private theorem orderedTerm_finite (M : ℤ) (u v : Cartan) (w : State) :
    Function.HasFiniteSupport (fun k => orderedTerm M u v k w) :=
  (Finset.finite_toSet _).subset (orderedTerm_support M u v w)

/-- The pointwise finite normal-order coefficient at cover exponent `-M-6`. -/
def orderedMode (M : ℤ) (u v : Cartan) : Module.End ℂ State where
  toFun w := ∑ᶠ k : ℤ, orderedTerm M u v k w
  map_add' w w' := by
    simp only [map_add]
    exact finsum_add_distrib (orderedTerm_finite M u v w) (orderedTerm_finite M u v w')
  map_smul' c w := by
    simp only [map_smul, RingHom.id_apply]
    exact (smul_finsum' c (orderedTerm_finite M u v w)).symm

theorem orderedMode_swap (M : ℤ) (u v : Cartan) :
    orderedMode M u v = orderedMode M v u := by
  apply LinearMap.ext
  intro w
  change (∑ᶠ k : ℤ, orderedTerm M u v k w) = ∑ᶠ k : ℤ, orderedTerm M v u k w
  have hinv : Function.Involutive (fun k : ℤ => M - k) := by
    intro k
    dsimp
    omega
  exact finsum_eq_of_bijective _ hinv.bijective fun k =>
    DFunLike.congr_fun (orderedTerm_swap M u v k) w

private theorem mode_add_cartan (k : ℤ) (u v : Cartan) :
    mode (u + v) k = mode u k + mode v k := (modeLinear k).map_add u v

private theorem mode_smul_cartan (k : ℤ) (c : ℂ) (u : Cartan) :
    mode (c • u) k = c • mode u k := (modeLinear k).map_smul c u

private theorem orderedMode_add (M : ℤ) (u v b : Cartan) :
    orderedMode M (u + v) b = orderedMode M u b + orderedMode M v b := by
  apply LinearMap.ext
  intro w
  change (∑ᶠ k : ℤ, orderedTerm M (u + v) b k w) =
    (∑ᶠ k : ℤ, orderedTerm M u b k w) + ∑ᶠ k : ℤ, orderedTerm M v b k w
  rw [← finsum_add_distrib (orderedTerm_finite M u b w) (orderedTerm_finite M v b w)]
  apply finsum_congr
  intro k
  simp only [orderedTerm, normalOrderedTerm, mode_add_cartan]
  split <;> simp only [add_mul, mul_add, LinearMap.add_apply]

private theorem orderedMode_smul (M : ℤ) (c : ℂ) (u b : Cartan) :
    orderedMode M (c • u) b = c • orderedMode M u b := by
  apply LinearMap.ext
  intro w
  change (∑ᶠ k : ℤ, orderedTerm M (c • u) b k w) = c • ∑ᶠ k : ℤ, orderedTerm M u b k w
  rw [smul_finsum' c (orderedTerm_finite M u b w)]
  apply finsum_congr
  intro k
  simp only [orderedTerm, normalOrderedTerm, mode_smul_cartan]
  split <;> simp only [smul_mul_assoc, mul_smul_comm, LinearMap.smul_apply]

private def orderedBilinear (M : ℤ) : Cartan →ₗ[ℂ] Cartan →ₗ[ℂ] Module.End ℂ State :=
  LinearMap.mk₂ ℂ (orderedMode M) (orderedMode_add M) (orderedMode_smul M)
    (fun a b c => by rw [orderedMode_swap M a (b + c), orderedMode_add,
      orderedMode_swap M b a, orderedMode_swap M c a])
    (fun c a b => by rw [orderedMode_swap M a (c • b), orderedMode_smul,
      orderedMode_swap M b a])

private def projection (k : ℤ) : Module.End ℂ Cartan :=
  let z := ζ ^ ((k % 3).toNat)
  (3 : ℂ)⁻¹ • (1 + z • p48qAction + z ^ 2 • (p48qAction * p48qAction))

private theorem projection_apply (k : ℤ) (a : Cartan) :
    projection k a = projectAt k a := by
  rw [projectAt_eq_fourier] <;> rfl

/-- The sum of the two moving-residue diagonal corrections. -/
def correction : LinearMap.BilinForm ℂ Cartan :=
  (9 : ℂ)⁻¹ •
    (p48qForm.comp (projection 1) LinearMap.id + p48qForm.comp (projection 2) LinearMap.id)

theorem correction_eq (a b : Cartan) :
    correction a b = (movingGram 1 a b + movingGram 2 a b) / 9 := by
  change (9 : ℂ)⁻¹ * (p48qForm (projection 1 a) b + p48qForm (projection 2 a) b) = _
  simp only [projection_apply, movingGram, div_eq_mul_inv, mul_comm ((9 : ℂ)⁻¹)]
  norm_num

theorem movingGram_swap (a b : Cartan) : movingGram 1 a b = movingGram 2 b a := by
  unfold movingGram
  rw [projectAt_eq_fourier, projectAt_eq_fourier]
  change p48qForm (project (ζ ^ (1 : ℕ)) a) b = p48qForm (project (ζ ^ (2 : ℕ)) b) a
  calc
    _ = p48qForm a (project (ζ ^ (2 : ℕ)) b) := by
      simpa only [pow_one] using project_adjoint (ζ ^ (1 : ℕ)) (root_cube 1) a b
    _ = _ := formSymmetric.eq _ _

theorem correction_swap (a b : Cartan) : correction a b = correction b a := by
  rw [correction_eq, correction_eq, movingGram_swap a b, ← movingGram_swap b a, add_comm]

/-- The scalar for either moving component is the regular part at the
normalized diagonal. Restoring the physical second coordinate contributes `w⁻²`. -/
theorem correction_diagonal (r : ℕ) (hr : r = 1 ∨ r = 2) (a b : Cartan) :
    ∃ R : PowerSeries ℂ,
      contractionAtRatio r (movingGram r a b) diagonalCoverRatio -
          HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (movingGram r a b)) /
            HahnSeries.ofPowerSeries ℤ ℂ ((PowerSeries.X : PowerSeries ℂ) ^ 2) =
          HahnSeries.ofPowerSeries ℤ ℂ R ∧
      PowerSeries.constantCoeff R = movingGram r a b / 9 := by
  simpa only [one_pow, inv_one, one_mul] using
    movingContraction_diagonal_regularization r hr a b (1 : ℂ)

private theorem correction_add (u v b : Cartan) :
    correction (u + v) b = correction u b + correction v b := by
  rw [map_add, LinearMap.add_apply]

private theorem correction_smul (c : ℂ) (u b : Cartan) :
    correction (c • u) b = c • correction u b := by
  rw [map_smul, LinearMap.smul_apply]

private def pairCoeff (M : ℤ) : Cartan →ₗ[ℂ] Cartan →ₗ[ℂ] Module.End ℂ State :=
  orderedBilinear M +
    if M = 0 then
      LinearMap.mk₂ ℂ (fun a b => correction a b • (1 : Module.End ℂ State))
        (fun a b c => by rw [correction_add, add_smul])
        (fun c a b => by rw [correction_smul, smul_assoc])
        (fun a b c => by rw [map_add, add_smul])
        (fun c a b => by rw [map_smul, smul_assoc])
    else 0

private theorem pairCoeff_apply (M : ℤ) (u v : Cartan) :
    pairCoeff M u v = orderedMode M u v +
      if M = 0 then correction u v • (1 : Module.End ℂ State) else 0 := by
  by_cases h : M = 0
  · simp only [pairCoeff, if_pos h, LinearMap.add_apply, orderedBilinear, LinearMap.mk₂_apply]
  · simp only [pairCoeff, if_neg h, LinearMap.add_apply, LinearMap.zero_apply, orderedBilinear,
      LinearMap.mk₂_apply]

private theorem pairCoeff_swap (M : ℤ) (u v : Cartan) : pairCoeff M u v = pairCoeff M v u := by
  rw [pairCoeff_apply, pairCoeff_apply, orderedMode_swap M u v, correction_swap u v]

private def pairField (u v : Cartan) : VertexOperator ℂ State :=
  VertexOperator.of_coeff (fun e => pairCoeff (-e - 6) u v) (by
    intro w
    refine ⟨-(2 * (coverBound w : ℤ)) - 6, ?_⟩
    intro e he
    change pairCoeff (-e - 6) u v w ≠ 0 at he
    apply le_of_not_gt
    intro h
    have hm : 2 * (coverBound w : ℤ) < -e - 6 := by omega
    rw [pairCoeff_apply, if_neg (by omega : -e - 6 ≠ 0), add_zero] at he
    apply he
    change (∑ᶠ k : ℤ, orderedTerm (-e - 6) u v k w) = 0
    apply finsum_eq_zero_of_forall_eq_zero
    intro k
    by_contra hk
    have hmem := orderedTerm_support (-e - 6) u v w
      (show k ∈ Function.support (fun j => orderedTerm (-e - 6) u v j w) from hk)
    have hs := Finset.mem_Icc.mp (show k ∈ Finset.Icc _ _ from hmem)
    omega)

private theorem pairField_coeff (u v : Cartan) (e : ℤ) :
    HVertexOperator.coeff (pairField u v) e = pairCoeff (-e - 6) u v :=
  rfl

private abbrev Coord := Fin lattice.rank

private def basisDirection (i : Coord) : Cartan := Pi.single i 1

private theorem sum_basisDirection (u : Cartan) :
    ∑ i : Coord, u i • basisDirection i = u := by
  classical
  apply funext
  intro j
  simp only [basisDirection, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem pairCoeff_sum (M : ℤ) (u v : Cartan) :
    pairCoeff M u v = ∑ i : Coord, ∑ j : Coord,
      (u i * v j) • pairCoeff M (basisDirection i) (basisDirection j) := by
  calc
    _ = pairCoeff M (∑ i : Coord, u i • basisDirection i)
          (∑ j : Coord, v j • basisDirection j) := by
      rw [sum_basisDirection, sum_basisDirection]
    _ = _ := by
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
        Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm]

private def currentPolynomial (u : Cartan) : Oscillator lattice :=
  ∑ i : Coord, u i • X (i, 0)

private theorem currentAlong_eq_polynomial (u : Cartan) :
    currentAlong lattice u = Finsupp.single 0 (currentPolynomial u) := by
  change currentAlong lattice u =
    (Finsupp.lsingle 0 : Oscillator lattice →ₗ[ℂ] Carrier lattice) (currentPolynomial u)
  simp only [currentAlong, currentState, currentPolynomial, map_sum, map_smul,
    Finsupp.lsingle_apply]

private theorem currentPair_eq_polynomial (u v : Cartan) :
    currentPair u v = Finsupp.single 0 (currentPolynomial u * currentPolynomial v) := by
  change currentPair u v =
    (Finsupp.lsingle 0 : Oscillator lattice →ₗ[ℂ] Carrier lattice)
      (currentPolynomial u * currentPolynomial v)
  rw [currentPair_eq_sum, currentPolynomial, currentPolynomial, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, map_smul, Finsupp.lsingle_apply]

private def derivative (i : Coord) : Module.End ℂ (Oscillator lattice) :=
  (pderiv (i, 0)).toLinearMap

private theorem derivative_current (i : Coord) (u : Cartan) :
    derivative i (currentPolynomial u) = C (u i) := by
  classical
  simp only [currentPolynomial, map_sum, map_smul, derivative, Derivation.coeFn_coe,
    pderiv_X, Pi.single_apply, Prod.mk.injEq, eq_self, and_true, smul_ite, smul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, C_eq_smul_one]

private def constant : Oscillator lattice →ₗ[ℂ] ℂ := lcoeff ℂ 0

private theorem constant_current (u : Cartan) : constant (currentPolynomial u) = 0 := by
  simp only [currentPolynomial, map_sum, map_smul, constant, lcoeff_apply,
    ← constantCoeff_eq, constantCoeff_X, smul_zero, Finset.sum_const_zero]

private def polynomialField : Oscillator lattice →ₗ[ℂ] VertexOperator ℂ State :=
  constant.smulRight (concreteChargedField 0) +
    (∑ i : Coord, (constant.comp (derivative i)).smulRight (currentField (basisDirection i))) +
    (2 : ℂ)⁻¹ • ∑ i : Coord, ∑ j : Coord,
      (constant.comp ((derivative i).comp (derivative j))).smulRight
        (pairField (basisDirection i) (basisDirection j))

private theorem polynomialField_apply (p : Oscillator lattice) :
    polynomialField p = constant p • concreteChargedField 0 +
      (∑ i : Coord, constant (derivative i p) • currentField (basisDirection i)) +
      (2 : ℂ)⁻¹ • ∑ i : Coord, ∑ j : Coord,
        constant (derivative i (derivative j p)) • pairField (basisDirection i) (basisDirection j) := by
  simp only [polynomialField, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.comp_apply]

private theorem constant_mul (p q : Oscillator lattice) :
    constant (p * q) = constant p * constant q :=
  (MvPolynomial.constantCoeff (σ := LatticeGeneratingFieldLocality.Index lattice)
    (R := ℂ)).map_mul p q

private theorem derivative_mul (i : Coord) (p q : Oscillator lattice) :
    derivative i (p * q) = derivative i p * q + p * derivative i q :=
  pderiv_mul

private theorem derivative_C (i : Coord) (c : ℂ) : derivative i (C c) = 0 :=
  pderiv_C

private theorem constant_C (c : ℂ) : constant (C c) = c := MvPolynomial.constantCoeff_C _ c

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
private theorem polynomialField_pair_coeff (u v : Cartan) (e : ℤ) :
    HVertexOperator.coeff (polynomialField (currentPolynomial u * currentPolynomial v)) e =
      pairCoeff (-e - 6) u v := by
  have hconst : constant (currentPolynomial u * currentPolynomial v) = 0 := by
    rw [constant_mul, constant_current, zero_mul]
  have hlinear (i : Coord) :
      constant (derivative i (currentPolynomial u * currentPolynomial v)) = 0 := by
    rw [derivative_mul, map_add, constant_mul, constant_mul, constant_current, constant_current,
      mul_zero, zero_mul, add_zero]
  have hquad (i j : Coord) :
      constant (derivative i (derivative j (currentPolynomial u * currentPolynomial v))) =
        u i * v j + v i * u j := by
    simp only [derivative_mul, derivative_current, map_add, derivative_C, zero_mul,
      mul_zero, zero_add, add_zero, constant_mul, constant_C] <;> ring
  rw [polynomialField_apply, hconst]
  simp only [hlinear, hquad, zero_smul, Finset.sum_const_zero, add_zero, zero_add,
    map_smul, map_sum, Pi.smul_apply, Finset.sum_apply, pairField_coeff, add_smul,
    Finset.sum_add_distrib]
  let M : ℤ := -e - 6
  have hswap : (∑ i : Coord, ∑ j : Coord,
      (v i * u j) • pairCoeff M (basisDirection i) (basisDirection j)) = pairCoeff M u v := by
    rw [← pairCoeff_sum, pairCoeff_swap M v u]
  change (2 : ℂ)⁻¹ •
    ((∑ i : Coord, ∑ j : Coord, (u i * v j) • pairCoeff M (basisDirection i) (basisDirection j)) +
      ∑ i : Coord, ∑ j : Coord, (v i * u j) • pairCoeff M (basisDirection i) (basisDirection j)) = _
  rw [← pairCoeff_sum, hswap, ← two_smul ℂ, smul_smul,
    inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]

/-- The subspace of the actual lattice carrier generated by the symmetric
products of two weight-one currents. -/
def quadraticStates : Submodule ℂ (Carrier lattice) :=
  Submodule.span ℂ (Set.range fun uv : Cartan × Cartan => currentPair uv.1 uv.2)

/-- The same neutral space with the already constructed generators included. -/
def neutralStates : Submodule ℂ (Carrier lattice) :=
  Submodule.span ℂ (({vacuum lattice} : Set (Carrier lattice)) ∪
    (Set.range (currentAlong lattice) ∪ Set.range (fun uv : Cartan × Cartan =>
      currentPair uv.1 uv.2)))

private def neutralFieldOnCarrier : Carrier lattice →ₗ[ℂ] VertexOperator ℂ State :=
  polynomialField.comp (Finsupp.lapply 0)

def neutralStateField : neutralStates →ₗ[ℂ] VertexOperator ℂ State :=
  neutralFieldOnCarrier.comp neutralStates.subtype

def quadraticStateField : quadraticStates →ₗ[ℂ] VertexOperator ℂ State :=
  neutralFieldOnCarrier.comp quadraticStates.subtype

set_option maxHeartbeats 1000000 in
-- Unfolding the subtype field to extract the charge-zero coefficient needs extra elaboration budget.
set_option maxRecDepth 100000 in
/-- Evaluation at the charge-zero oscillator polynomial makes the field
independent of every linear expression of the state in products of currents. -/
theorem quadraticStateField_pair (u v : Cartan) (M : ℤ) :
    HVertexOperator.coeff
      (quadraticStateField ⟨currentPair u v, Submodule.subset_span ⟨(u, v), rfl⟩⟩)
      (-M - 6) =
        orderedMode M u v + if M = 0 then correction u v • (1 : Module.End ℂ State) else 0 := by
  rw [← pairCoeff_apply]
  simp only [quadraticStateField, neutralFieldOnCarrier, LinearMap.comp_apply,
    Submodule.subtype_apply, Finsupp.lapply_apply]
  rw [currentPair_eq_polynomial, Finsupp.single_eq_same, polynomialField_pair_coeff,
    show -(-M - 6) - 6 = M by omega]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
private theorem field_current (u : Cartan) :
    neutralFieldOnCarrier (currentAlong lattice u) = currentField u := by
  apply HVertexOperator.coeff_inj
  funext e
  change HVertexOperator.coeff (polynomialField (currentAlong lattice u 0)) e = _
  rw [currentAlong_eq_polynomial, Finsupp.single_eq_same, polynomialField_apply, constant_current]
  simp only [derivative_current, derivative_C, constant_C, map_zero, zero_smul, smul_zero,
    Finset.sum_const_zero, zero_add, add_zero, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    currentField_coeff]
  change (∑ i : Coord, u i • modeLinear (-e - 3) (basisDirection i)) = modeLinear (-e - 3) u
  calc
    _ = modeLinear (-e - 3) (∑ i : Coord, u i • basisDirection i) := by
      simp only [map_sum, map_smul]
    _ = _ := by rw [sum_basisDirection]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
private theorem field_vacuum : neutralFieldOnCarrier (vacuum lattice) = concreteChargedField 0 := by
  change polynomialField ((Finsupp.single 0 (1 : Oscillator lattice) : Carrier lattice) 0) = _
  rw [Finsupp.single_eq_same, polynomialField_apply]
  have h (i : Coord) : derivative i 1 = 0 := pderiv_one
  have h₀ : constant (1 : Oscillator lattice) = 1 := MvPolynomial.constantCoeff.map_one
  simp only [h, h₀, map_zero, zero_smul, smul_zero, Finset.sum_const_zero, one_smul, add_zero]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem neutralStateField_current (u : Cartan) :
    neutralStateField ⟨currentAlong lattice u, Submodule.subset_span (Or.inr (Or.inl ⟨u, rfl⟩))⟩ =
      currentField u := field_current u

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem neutralStateField_vacuum :
    neutralStateField ⟨vacuum lattice, Submodule.subset_span (Or.inl rfl)⟩ =
      concreteChargedField 0 := field_vacuum

private theorem projection_comm (k : ℤ) (a : Cartan) :
    p48qAction (projection k a) = projection k (p48qAction a) := by
  simp only [projection, LinearMap.smul_apply, LinearMap.add_apply, Module.End.one_apply,
    Module.End.mul_apply, map_add, map_smul]

private theorem projectAt_off_residue (a : Cartan) (r : ℕ) (hr : r < 3)
    (ha : p48qAction a = (ζ ^ r) ^ 2 • a) (k : ℤ) (hk : k % 3 ≠ (r : ℤ)) :
    projectAt k a = 0 := by
  let s := (k % 3).toNat
  have hs : (s : ℤ) = k % 3 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  have hslt : s < 3 := by omega
  have hsr : s ≠ r := by
    intro h
    apply hk
    rw [← hs, h]
  have hroot : (ζ ^ s) ^ 2 ≠ (ζ ^ r) ^ 2 := by
    intro h
    apply hsr
    apply zetaPrimitive.pow_inj hslt hr
    calc
      ζ ^ s = ((ζ ^ s) ^ 2) ^ 2 := (cube_square (root_cube s)).symm
      _ = ((ζ ^ r) ^ 2) ^ 2 := by rw [h]
      _ = ζ ^ r := cube_square (root_cube r)
  have h₁ : p48qAction (projectAt k a) = (ζ ^ s) ^ 2 • projectAt k a := by
    rw [projectAt_eq_fourier]
    exact project_action _ (root_cube s) _
  have h₂ : p48qAction (projectAt k a) = (ζ ^ r) ^ 2 • projectAt k a := by
    rw [← projection_apply k a, projection_comm, ha, map_smul]
  have hzero : ((ζ ^ s) ^ 2 - (ζ ^ r) ^ 2) • projectAt k a = 0 := by
    rw [sub_smul, ← h₁, ← h₂, sub_self]
  exact (smul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hroot)

private theorem normal_order_on_residue (M : ℤ) (a b : Cartan) (r : ℕ) (hr : r < 3)
    (ha : p48qAction a = (ζ ^ r) ^ 2 • a) (w : State) :
    (∑ᶠ k ∈ {k : ℤ | k % 3 = (r : ℤ)}, orderedTerm M a b k w) = orderedMode M a b w := by
  let f := fun k => orderedTerm M a b k w
  let I := Finset.Icc (M - (coverBound w : ℤ)) (coverBound w : ℤ)
  have hI : Function.support f ⊆ (I : Set ℤ) := orderedTerm_support M a b w
  have hr' : Function.support f ⊆ {k : ℤ | k % 3 = (r : ℤ)} := by
    intro k hk
    change k % 3 = (r : ℤ)
    by_contra hoff
    change orderedTerm M a b k w ≠ 0 at hk
    apply hk
    have hm : mode a k = 0 := by
      rw [← mode_projectAt a k, projectAt_off_residue a r hr ha k hoff]
      exact (modeLinear k).map_zero
    simp [orderedTerm, normalOrderedTerm, hm]
  change (∑ᶠ k ∈ {k : ℤ | k % 3 = (r : ℤ)}, f k) = ∑ᶠ k : ℤ, f k
  rw [finsum_eq_sum_of_support_subset f hI]
  apply finsum_mem_eq_sum_of_inter_support_eq
  rw [Set.inter_eq_right.mpr hr', Set.inter_eq_right.mpr hI]

private theorem choose_two (t : ℂ) : Ring.choose t 2 = t * (t - 1) / 2 := by
  apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).2
  rw [mul_comm (Ring.choose t 2) 2]
  simpa only [Nat.choose_one_right, nsmul_eq_mul, Nat.cast_ofNat, Nat.cast_one,
    show (2 : ℕ) - 1 = 1 by decide, Ring.choose_one_right] using
    (Ring.choose_smul_choose t (n := 2) (k := 1) (by decide))

private theorem correction_on_residue (a b : Cartan) (r : ℕ) (hr : r < 3)
    (ha : p48qAction a = (ζ ^ r) ^ 2 • a) :
    correction a b = -(Ring.choose ((r : ℂ) / 3) 2 * p48qForm a b) := by
  have hoff (s : ℕ) (hs : (s : ℤ) % 3 ≠ (r : ℤ)) : movingGram s a b = 0 := by
    rw [movingGram, projectAt_off_residue a r hr ha (s : ℤ) hs, map_zero, LinearMap.zero_apply]
  rw [correction_eq, choose_two]
  interval_cases r
  · rw [hoff 1 (by decide), hoff 2 (by decide)]
    norm_num
  · rw [movingGram_eq_pairing 1 (Or.inl rfl) a b ha, hoff 2 (by decide)]
    norm_num <;> ring
  · rw [hoff 1 (by decide), movingGram_eq_pairing 2 (Or.inr rfl) a b ha]
    norm_num <;> ring

private theorem native_current_product (u v : Cartan) (n : ℤ) (hn : 0 ≤ n) :
    mu lattice (currentAlong lattice u) n (currentAlong lattice v) =
      if n = 1 then p48qForm u v • vacuum lattice else 0 :=
  current_product lattice u v n hn

/-- The actual source product entering the `j`-th term of BK (3.13)
at product index `-1`. Each product lies in the neutral span. -/
def currentProduct (u v : Cartan) (j : ℕ) : neutralStates :=
  ⟨mu lattice (currentAlong lattice u) ((j : ℤ) - 1) (currentAlong lattice v), by
    by_cases hj : j = 0
    · subst j
      change currentPair u v ∈ neutralStates
      exact Submodule.subset_span (Or.inr (Or.inr ⟨(u, v), rfl⟩))
    · rw [native_current_product u v _ (by omega)]
      split
      · exact neutralStates.smul_mem _ (Submodule.subset_span (Or.inl rfl))
      · exact neutralStates.zero_mem⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
private theorem field_product_positive (u v : Cartan) (j : ℕ) (hj : 0 < j) :
    neutralStateField (currentProduct u v j) =
      if j = 2 then p48qForm u v • concreteChargedField 0 else 0 := by
  change neutralFieldOnCarrier
    (mu lattice (currentAlong lattice u) ((j : ℤ) - 1) (currentAlong lattice v)) = _
  rw [native_current_product u v _ (by omega)]
  have hindex : (j : ℤ) - 1 = 1 ↔ j = 2 := by omega
  by_cases h : j = 2
  · rw [ite_eq_left (hindex.mpr h), ite_eq_left h, map_smul, field_vacuum]
  · rw [ite_eq_right (fun he => h (hindex.mp he)), ite_eq_right h, map_zero]

set_option maxHeartbeats 1000000 in
-- The two subtype fields reduce to the same evaluation on the carrier.
set_option maxRecDepth 100000 in
/-- The neutral field uses the quadratic extension at the actual `(-1)`-product. -/
theorem neutralStateField_pair_coeff (u v : Cartan) (M : ℤ) :
    HVertexOperator.coeff (neutralStateField (currentProduct u v 0)) (-M - 6) =
      orderedMode M u v + if M = 0 then correction u v • (1 : Module.End ℂ State) else 0 := by
  exact quadraticStateField_pair u v M

set_option maxHeartbeats 1000000 in
-- Extracting the neutral and vacuum coefficients requires extra elaboration budget.
set_option maxRecDepth 100000 in
/-- BK (3.13) at `-1` for each of the three first-current residues. The
second current can be arbitrary. The only higher source product is the
vacuum at `j = 2`, and its binomial coefficient cancels the diagonal
correction. All coefficients here are in the cover coordinate `z = x³`. -/
theorem current_pair_BK_iterate (u v : Cartan) (r : ℕ) (hr : r < 3)
    (hu : p48qAction u = (ζ ^ r) ^ 2 • u) (M : ℤ) (w : State) :
    (∑ᶠ k ∈ {k : ℤ | k % 3 = (r : ℤ)}, orderedTerm M u v k w) =
      ∑ᶠ j : ℕ, Ring.choose ((r : ℂ) / 3) j •
        HVertexOperator.coeff (neutralStateField (currentProduct u v j))
          (-M - 6 + 3 * (j : ℤ)) w := by
  let term (j : ℕ) : State := Ring.choose ((r : ℂ) / 3) j •
    HVertexOperator.coeff (neutralStateField (currentProduct u v j))
      (-M - 6 + 3 * (j : ℤ)) w
  have hsupport : Function.support term ⊆ (↑({0, 2} : Finset ℕ) : Set ℕ) := by
    intro j hj
    by_contra hout
    have h₀ : j ≠ 0 := fun h => hout (by simp [h])
    have h₂ : j ≠ 2 := fun h => hout (by simp [h])
    apply hj
    simp only [term, field_product_positive u v j (Nat.pos_of_ne_zero h₀),
      if_neg h₂, map_zero, Pi.zero_apply, LinearMap.zero_apply, smul_zero]
  have h₀ : term 0 =
      (orderedMode M u v + if M = 0 then correction u v • (1 : Module.End ℂ State) else 0) w := by
    simp only [term, Ring.choose_zero_right, one_smul, Nat.cast_zero, mul_zero, add_zero,
      neutralStateField_pair_coeff]
  have h₂ : term 2 = if M = 0 then
        (Ring.choose ((r : ℂ) / 3) 2 * p48qForm u v) • w else 0 := by
    simp only [term, field_product_positive u v 2 (by decide), if_true, map_smul,
      Pi.smul_apply, LinearMap.smul_apply, concreteChargedField_zero_coeff,
      show -M - 6 + 3 * ((2 : ℕ) : ℤ) = 0 ↔ M = 0 by omega]
    by_cases h : M = 0
    · subst M
      simp [concreteChargedField_zero_coeff, smul_smul]
    · simp [h, concreteChargedField_zero_coeff]
  change _ = ∑ᶠ j : ℕ, term j
  rw [normal_order_on_residue M u v r hr hu w, finsum_eq_sum_of_support_subset term hsupport,
    Finset.sum_pair (by decide : (0 : ℕ) ≠ 2), h₀, h₂]
  rw [correction_on_residue u v r hr hu]
  by_cases h : M = 0 <;> simp [h, neg_smul]

end

#print axioms current_pair_BK_iterate

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qQuadraticStateField
