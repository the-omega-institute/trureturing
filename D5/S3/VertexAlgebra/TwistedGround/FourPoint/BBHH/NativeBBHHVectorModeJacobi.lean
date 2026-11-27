import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedCrossedProductToIterate
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedBProductUpperDisk

/-! Finite mode sums for the actual BBHH fields lift homogeneous scalar
identities to arbitrary even twisted output vectors. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBBHHVectorModeJacobi

open ActualChargedAdjoint (actualForm actualForm_nondegenerate)
open ActualEnergyRestrictedDual (maxOddWeight)
open ActualLeechHyperbolic (leechData)
open ActualOddGradeOrthogonality (actualForm_oddGrade_orthogonal)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open LatticeHalfFockCorrectedField (correctedField)
open LatticeHalfFockGradedTrace (actualAmbientBasis actualGrade oddWeight)
open LatticeHalfFockParityT (actualParity_on_actualGrade)
open NativeFixedCrossedProductToIterate (aJointTerm)
open NativeMixedUpperProductCusp (bJointTerm)
open Orbifold.NativeFixedPairField (nu nu_lower_truncation)
open Orbifold.NativeMixedPairField (mu mu_lower_truncation)
open Orbifold.NativeOddTwistedIntertwiner (TwistedEven TwistedOdd leechUnit paritySign)
open Orbifold.NativeOddUpperRightSkew (rightField)

open private fixed_parity_preserved from
  D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockParityField
open private actualGrade_eigen from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew
open private parity_repr from
  D5.S3.VertexAlgebra.TwistedGround.MixedTranslation
open private basis_mem_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHHomogeneousExtension
open private basisComponent basisComponent_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedBProductUpperDisk
open private sum_projectedBasis from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairField
open private aModeLinear aModeLinear_apply from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFixedCrossedProductToIterate
open private bModeLinear bModeLinear_apply from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedBProductInversion

local notation "ℒ" => leechData

/-- The actual form with even tests in its first slot separates the even
twisted space. Coordinates of an even state have even grade, and tests at
odd grades vanish by grade orthogonality. -/
theorem actualForm_twistedEven_separates (x : TwistedEven)
    (h : ∀ S : TwistedEven, actualForm ℒ leechUnit S.val x.val = 0) : x = 0 := by
  classical
  let basis := actualAmbientBasis ℒ leechUnit
  have hsupport (i) (hi : i ∈ (basis.repr x.val).support) : oddWeight ℒ i.1 % 2 = 0 := by
    have hp := x.property
    simp only [paritySign, Bool.false_eq_true, ite_false, paritySpace, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.id_apply, one_smul, sub_eq_zero] at hp
    have hc := congrArg (fun y => (actualAmbientBasis ℒ leechUnit).repr y i) hp
    rw [parity_repr] at hc
    by_contra hn
    have ho : oddWeight ℒ i.1 % 2 = 1 := by omega
    rw [neg_one_pow_eq_pow_mod_two, ho, pow_one] at hc
    exact Finsupp.mem_support_iff.mp hi (by linear_combination hc / (-2 : ℂ))
  have hzero : (actualForm ℒ leechUnit).flip x.val = 0 := by
    apply basis.ext
    intro i
    change actualForm ℒ leechUnit (basis i) x.val = 0
    by_cases hi : oddWeight ℒ i.1 % 2 = 0
    · have hp := actualParity_on_actualGrade ℒ leechUnit _ ⟨basis i, basis_mem_grade i⟩
      rw [neg_one_pow_eq_pow_mod_two, hi, pow_zero] at hp
      have hm : basis i ∈ paritySpace ℒ leechUnit (paritySign false) := by
        simpa only [paritySign, Bool.false_eq_true, ite_false, paritySpace, LinearMap.mem_ker,
          LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] using hp
      exact h ⟨basis i, hm⟩
    · rw [← basis.linearCombination_repr x.val]
      simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul]
      apply Finset.sum_eq_zero
      intro j hj
      have hne : (oddWeight ℒ i.1 : ℤ) ≠ (oddWeight ℒ j.1 : ℤ) := by
        intro he
        exact hi ((Int.ofNat.inj he).symm ▸ hsupport j hj)
      rw [actualForm_oddGrade_orthogonal ℒ leechUnit _ _ (basis i) (basis j)
        (by simpa only [Int.cast_natCast] using
          (actualGrade_eigen ℒ leechUnit _ _).mp (basis_mem_grade i))
        (by simpa only [Int.cast_natCast] using
          (actualGrade_eigen ℒ leechUnit _ _).mp (basis_mem_grade j))
        hne, smul_zero]
  exact Subtype.ext ((actualForm_nondegenerate ℒ leechUnit).2 x.val
    (LinearMap.congr_fun hzero))

/-- The literal vector behind the product in order `(R, Q, P, S)`.
Swapping `P` and `R` gives the other product. The pair records the inner
and outer doubled Hahn exponents. -/
def bbhhBVectorTerm (P R : TwistedOdd) (Q : TwistedEven) (p : ℤ × ℤ) : TwistedEven :=
  (rightField ℒ leechUnit true P).coeff p.2 ((mu true R).coeff p.1 Q)

/-- The literal fixed iterate in order `(P, R, Q, S)`, with fixed-source
parity preservation supplying the even output subtype. -/
def bbhhAVectorTerm (P R : TwistedOdd) (Q : TwistedEven) (p : ℤ × ℤ) : TwistedEven :=
  ⟨(correctedField ℒ leechUnit ((nu true P).coeff p.1 R).val).coeff p.2 Q.val,
    fixed_parity_preserved ℒ leechUnit (paritySign false) _ p.2 Q.val Q.property⟩

/-- The selectors and signed binomial weights of a channel. For every inner
cutoff, only finitely many nonzero weights may select modes above it. This
also permits finite binomial sums with the opposite shift. -/
structure BBHHModeSum where
  modes : ℕ → ℤ × ℤ
  weight : ℕ → ℂ
  eventually_below : ∀ bound : ℤ, ∃ N : ℕ, ∀ j ≥ N, weight j = 0 ∨ (modes j).1 ≤ bound

/-- On a fixed total doubled degree, the inner exponent falls by `2*j`
while the outer exponent rises by `2*j`. -/
def BBHHModeSum.downshift (inner outer : ℤ) (weight : ℕ → ℂ) : BBHHModeSum where
  modes j := (inner - 2 * (j : ℤ), outer + 2 * (j : ℤ))
  weight := weight
  eventually_below bound := ⟨(inner - bound).toNat, fun j hj => Or.inr (by omega)⟩

/-- Finite weights allow any selectors, including an upward inner shift. -/
def BBHHModeSum.ofFiniteSupport (modes : ℕ → ℤ × ℤ) (weight : ℕ → ℂ)
    (h : Function.HasFiniteSupport weight) : BBHHModeSum where
  modes := modes
  weight := weight
  eventually_below _ := by
    obtain ⟨N, hN⟩ := Set.Finite.bddAbove h
    refine ⟨N + 1, fun j hj => Or.inl ?_⟩
    by_contra hw
    have hle : j ≤ N := hN hw
    omega

/-- The product has odd doubled exponents `-2*m-3` in both fields. -/
def BBHHModeSum.product (inner outer : ℤ) (weight : ℕ → ℂ) : BBHHModeSum :=
  downshift (-2 * inner - 3) (-2 * outer - 3) weight

/-- The fixed iterate has even doubled exponents `-2*m-2` in both fields. -/
def BBHHModeSum.iterate (inner outer : ℤ) (weight : ℕ → ℂ) : BBHHModeSum :=
  downshift (-2 * inner - 2) (-2 * outer - 2) weight

private theorem BBHHModeSum.finiteSupport (C : BBHHModeSum) {V : Type*}
    [AddCommMonoid V] [Module ℂ V] (term : ℤ × ℤ → V) (bound : ℤ)
    (hz : ∀ p, p.1 ≤ bound → term p = 0) :
    Function.HasFiniteSupport (fun j => C.weight j • term (C.modes j)) := by
  obtain ⟨N, hN⟩ := C.eventually_below bound
  refine (Set.finite_lt_nat N).subset ?_
  intro j hj
  change j < N
  by_contra! hlarge
  apply hj
  change C.weight j • term (C.modes j) = 0
  rcases hN j hlarge with hw | hm
  · rw [hw, zero_smul]
  · rw [hz _ hm, smul_zero]

/-- Both literal BBHH products and the literal fixed iterate have finite
weighted vector support, even on inhomogeneous external states. -/
theorem bbhh_mode_finite_support (B D A : BBHHModeSum) (P R : TwistedOdd) (Q : TwistedEven) :
    Function.HasFiniteSupport (fun j => B.weight j • bbhhBVectorTerm P R Q (B.modes j)) ∧
    Function.HasFiniteSupport (fun j => D.weight j • bbhhBVectorTerm R P Q (D.modes j)) ∧
    Function.HasFiniteSupport (fun j => A.weight j • bbhhAVectorTerm P R Q (A.modes j)) := by
  let p : ℤ := maxOddWeight ℒ leechUnit P.val
  let r : ℤ := maxOddWeight ℒ leechUnit R.val
  let q : ℤ := maxOddWeight ℒ leechUnit Q.val
  refine ⟨B.finiteSupport _ (-r - q - 6) ?_, D.finiteSupport _ (-p - q - 6) ?_,
    A.finiteSupport _ (-p - r - 7) ?_⟩
  · intro i hi
    rw [bbhhBVectorTerm, mu_lower_truncation true R Q i.1 hi, map_zero]
  · intro i hi
    rw [bbhhBVectorTerm, mu_lower_truncation true P Q i.1 hi, map_zero]
  · intro i hi
    have hz := nu_lower_truncation true P R i.1 (show i.1 < -p - r - 6 by omega)
    apply Subtype.ext
    simp only [bbhhAVectorTerm, hz, Submodule.coe_zero, map_zero, Pi.zero_apply,
      LinearMap.zero_apply]

private def pairEven (S : TwistedEven) : TwistedEven →ₗ[ℂ] ℂ :=
  (actualForm ℒ leechUnit S.val).comp (paritySpace ℒ leechUnit (paritySign false)).subtype

private theorem pairEven_bVector (P R : TwistedOdd) (Q S : TwistedEven) (i : ℤ × ℤ) :
    pairEven S (bbhhBVectorTerm P R Q i) = bJointTerm true true R Q P S 1 1 i := by
  simp only [pairEven, bbhhBVectorTerm, bJointTerm, LinearMap.comp_apply,
    Submodule.subtype_apply, one_zpow, mul_one]

private theorem pairEven_aVector (P R : TwistedOdd) (Q S : TwistedEven) (i : ℤ × ℤ) :
    pairEven S (bbhhAVectorTerm P R Q i) = aJointTerm true false P R Q S 1 1 i := by
  simp only [pairEven, bbhhAVectorTerm, aJointTerm, LinearMap.comp_apply,
    Submodule.subtype_apply, one_zpow, mul_one]

private theorem pairEven_finiteSupport (S : TwistedEven) (f : ℕ → TwistedEven)
    (hf : Function.HasFiniteSupport f) : Function.HasFiniteSupport (fun j => pairEven S (f j)) :=
  hf.subset fun j hj hz => hj (show pairEven S (f j) = 0 by rw [hz, map_zero])

/-- The signed scalar mode equation, with one weight for each channel.
Any orientation sign from a residue convention can enter its weight. -/
def bbhhScalarModeIdentity (B D A : BBHHModeSum) (P R : TwistedOdd) (Q S : TwistedEven) : Prop :=
  -(∑ᶠ j, B.weight j * bJointTerm true true R Q P S 1 1 (B.modes j)) -
    (∑ᶠ j, D.weight j * bJointTerm true true P Q R S 1 1 (D.modes j)) =
    ∑ᶠ j, A.weight j * aJointTerm true false P R Q S 1 1 (A.modes j)

private abbrev BBHHLinear :=
  TwistedOdd →ₗ[ℂ] TwistedOdd →ₗ[ℂ] TwistedEven →ₗ[ℂ] TwistedEven →ₗ[ℂ] ℂ

private def bLinear (i : ℤ × ℤ) : BBHHLinear :=
  (LinearMap.lflip.toLinearMap.comp (bModeLinear true true 1 1 i)).flip

private theorem bLinear_apply (i : ℤ × ℤ) (P R : TwistedOdd) (Q S : TwistedEven) :
    bLinear i P R Q S = bJointTerm true true R Q P S 1 1 i :=
  bModeLinear_apply true true 1 1 i R Q P S

private def defectTerm (B D A : BBHHModeSum) (j : ℕ) : BBHHLinear :=
  let product : BBHHLinear := (-B.weight j) • bLinear (B.modes j)
  let swapped : BBHHLinear := (-D.weight j) • (bLinear (D.modes j)).flip
  let iterate : BBHHLinear := (-A.weight j) • aModeLinear true false 1 1 (A.modes j)
  product + swapped + iterate

private theorem defectTerm_apply (B D A : BBHHModeSum) (j : ℕ)
    (P R : TwistedOdd) (Q S : TwistedEven) :
    defectTerm B D A j P R Q S =
      -(B.weight j * bJointTerm true true R Q P S 1 1 (B.modes j)) -
      D.weight j * bJointTerm true true P Q R S 1 1 (D.modes j) -
      A.weight j * aJointTerm true false P R Q S 1 1 (A.modes j) := by
  simp only [defectTerm, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.flip_apply,
    smul_eq_mul, bLinear_apply, aModeLinear_apply, neg_mul, sub_eq_add_neg]

private theorem scalar_finite_support (B D A : BBHHModeSum) (P R : TwistedOdd)
    (Q S : TwistedEven) :
    Function.HasFiniteSupport (fun j => B.weight j * bJointTerm true true R Q P S 1 1 (B.modes j)) ∧
    Function.HasFiniteSupport (fun j => D.weight j * bJointTerm true true P Q R S 1 1 (D.modes j)) ∧
    Function.HasFiniteSupport (fun j => A.weight j * aJointTerm true false P R Q S 1 1 (A.modes j)) := by
  obtain ⟨hB, hD, hA⟩ := bbhh_mode_finite_support B D A P R Q
  simpa only [map_smul, smul_eq_mul, pairEven_bVector, pairEven_aVector] using
    And.intro (pairEven_finiteSupport S _ hB)
      (And.intro (pairEven_finiteSupport S _ hD) (pairEven_finiteSupport S _ hA))

private theorem defectTerm_finite_support (B D A : BBHHModeSum)
    (P R : TwistedOdd) (Q S : TwistedEven) :
    Function.HasFiniteSupport (fun j => defectTerm B D A j P R Q S) := by
  obtain ⟨hB, hD, hA⟩ := scalar_finite_support B D A P R Q S
  simpa only [defectTerm_apply] using (hB.fun_neg.fun_sub hD).fun_sub hA

private def modeDefect (B D A : BBHHModeSum) : BBHHLinear := by
  refine {
    toFun := fun P => {
      toFun := fun R => {
        toFun := fun Q => {
          toFun := fun S => ∑ᶠ j, defectTerm B D A j P R Q S
          map_add' := ?_
          map_smul' := ?_ }
        map_add' := ?_
        map_smul' := ?_ }
      map_add' := ?_
      map_smul' := ?_ }
    map_add' := ?_
    map_smul' := ?_ }
  all_goals
    intros
    repeat' (apply LinearMap.ext; intro)
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, LinearMap.smul_apply,
      RingHom.id_apply, map_add, map_smul]
    first
    | exact finsum_add_distrib (defectTerm_finite_support B D A _ _ _ _)
        (defectTerm_finite_support B D A _ _ _ _)
    | exact (smul_finsum _ _).symm

private theorem scalarModeIdentity_iff (B D A : BBHHModeSum) (P R : TwistedOdd)
    (Q S : TwistedEven) :
    bbhhScalarModeIdentity B D A P R Q S ↔ modeDefect B D A P R Q S = 0 := by
  obtain ⟨hB, hD, hA⟩ := scalar_finite_support B D A P R Q S
  change _ ↔ (∑ᶠ j, defectTerm B D A j P R Q S) = 0
  simp only [defectTerm_apply]
  rw [finsum_sub_distrib (hB.fun_neg.fun_sub hD) hA, finsum_sub_distrib hB.fun_neg hD,
    finsum_neg_distrib, sub_eq_zero]
  rfl

/-- The literal scalar equation extends from homogeneous inputs and tests to
all twisted inputs and tests by finite expansion in the projected native basis. -/
theorem bbhh_scalar_mode_identity_of_homogeneous (B D A : BBHHModeSum)
    (h : ∀ (M H K J : ℕ) (P R : TwistedOdd) (Q S : TwistedEven),
      P.val ∈ actualGrade ℒ leechUnit M → R.val ∈ actualGrade ℒ leechUnit H →
      Q.val ∈ actualGrade ℒ leechUnit K → S.val ∈ actualGrade ℒ leechUnit J →
      bbhhScalarModeIdentity B D A P R Q S)
    (P R : TwistedOdd) (Q S : TwistedEven) : bbhhScalarModeIdentity B D A P R Q S := by
  classical
  apply (scalarModeIdentity_iff B D A P R Q S).mpr
  conv_lhs =>
    rw [← sum_projectedBasis true P]
    simp only [map_sum, LinearMap.sum_apply]
    rw [← sum_projectedBasis true R]
    simp only [map_sum, LinearMap.sum_apply]
    rw [← sum_projectedBasis false Q]
    simp only [map_sum, LinearMap.sum_apply]
    rw [← sum_projectedBasis false S]
    simp only [map_sum]
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun r _ =>
    Finset.sum_eq_zero fun q _ => Finset.sum_eq_zero fun s _ => ?_
  exact (scalarModeIdentity_iff B D A _ _ _ _).mp
    (h _ _ _ _ (basisComponent true P p) (basisComponent true R r)
      (basisComponent false Q q) (basisComponent false S s)
      (basisComponent_grade true P p) (basisComponent_grade true R r)
      (basisComponent_grade false Q q) (basisComponent_grade false S s))

/-- The literal scalar equations for all even tests determine equality of
the three actual even-twisted vector sums. -/
theorem bbhh_vector_mode_identity_of_scalar (B D A : BBHHModeSum)
    (P R : TwistedOdd) (Q : TwistedEven)
    (h : ∀ S : TwistedEven, bbhhScalarModeIdentity B D A P R Q S) :
    -(∑ᶠ j, B.weight j • bbhhBVectorTerm P R Q (B.modes j)) -
      (∑ᶠ j, D.weight j • bbhhBVectorTerm R P Q (D.modes j)) =
      ∑ᶠ j, A.weight j • bbhhAVectorTerm P R Q (A.modes j) := by
  obtain ⟨hB, hD, hA⟩ := bbhh_mode_finite_support B D A P R Q
  refine sub_eq_zero.mp (actualForm_twistedEven_separates _ (fun S => ?_))
  change pairEven S (_ - _) = 0
  rw [map_sub (pairEven S), sub_eq_zero, map_sub (pairEven S), map_neg (pairEven S),
    map_finsum (pairEven S) hB, map_finsum (pairEven S) hD, map_finsum (pairEven S) hA]
  simpa only [bbhhScalarModeIdentity, map_smul, smul_eq_mul, pairEven_bVector,
    pairEven_aVector] using h S

/-- A homogeneous raw scalar equation with state-independent selectors and
weights gives the corresponding arbitrary-state vector identity. -/
theorem bbhh_vector_mode_identity_of_homogeneous (B D A : BBHHModeSum)
    (h : ∀ (M H K J : ℕ) (P R : TwistedOdd) (Q S : TwistedEven),
      P.val ∈ actualGrade ℒ leechUnit M → R.val ∈ actualGrade ℒ leechUnit H →
      Q.val ∈ actualGrade ℒ leechUnit K → S.val ∈ actualGrade ℒ leechUnit J →
      bbhhScalarModeIdentity B D A P R Q S)
    (P R : TwistedOdd) (Q : TwistedEven) :
    -(∑ᶠ j, B.weight j • bbhhBVectorTerm P R Q (B.modes j)) -
      (∑ᶠ j, D.weight j • bbhhBVectorTerm R P Q (D.modes j)) =
      ∑ᶠ j, A.weight j • bbhhAVectorTerm P R Q (A.modes j) :=
  bbhh_vector_mode_identity_of_scalar B D A P R Q
    (bbhh_scalar_mode_identity_of_homogeneous B D A h P R Q)

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeBBHHVectorModeJacobi
