import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBAllStateModeJacobi

/-! The actual vector-valued raw HHBB mode identity on the odd twisted sector. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBModeResidue

open ActualChargedAdjoint (actualForm actualForm_nondegenerate)
open ActualEnergyRestrictedDual (maxOddWeight)
open ActualLeechHyperbolic (leechData)
open ActualOddGradeOrthogonality (actualForm_oddGrade_orthogonal)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open LatticeHalfFockCorrectedField (correctedField)
open LatticeHalfFockGradedTrace (actualAmbientBasis actualGrade actual_basis_eigenvalue oddWeight)
open LatticeHalfFockParityT (actualParity_on_actualGrade)
open NativeMixedArbitrarySewing (hhbb_raw_scalar_mode_jacobi)
open NativeMixedComplexSewing (aJointTerm)
open NativeMixedUpperProductCusp (bJointTerm)
open Orbifold.NativeFixedPairField (nu nu_lower_truncation)
open Orbifold.NativeMixedPairField (mu mu_lower_truncation)
open Orbifold.NativeOddTwistedIntertwiner (TwistedEven TwistedOdd leechUnit paritySign)
open Orbifold.NativeOddUpperRightSkew (rightField)

open private actualGrade_eigen from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew
open private negative_support from
  D5.S3.VertexAlgebra.TwistedGround.MixedTranslation
open private fixed_parity_preserved from
  D5.S3.VertexAlgebra.HalfFock.LatticeHalfFockParityField

local notation "ℒ" => leechData

/-- The native form separates arbitrary odd twisted states using odd tests
in the first slot. -/
theorem actualForm_twistedOdd_separates (x : TwistedOdd)
    (h : ∀ b : TwistedOdd, actualForm ℒ leechUnit b.val x.val = 0) : x = 0 := by
  classical
  let B := actualAmbientBasis ℒ leechUnit
  have hgrade (i) : B i ∈ actualGrade ℒ leechUnit (oddWeight ℒ i.1) :=
    (actualGrade_eigen ℒ leechUnit _ _).mpr (actual_basis_eigenvalue ℒ leechUnit i.1 i.2)
  have hzero : (actualForm ℒ leechUnit).flip x.val = 0 := by
    apply B.ext
    intro i
    change actualForm ℒ leechUnit (B i) x.val = 0
    by_cases hi : oddWeight ℒ i.1 % 2 = 1
    · have hp := actualParity_on_actualGrade ℒ leechUnit _ ⟨B i, hgrade i⟩
      rw [neg_one_pow_eq_pow_mod_two, hi, pow_one] at hp
      have hmem : B i ∈ paritySpace ℒ leechUnit (paritySign true) := by
        simpa only [paritySign, ite_true, paritySpace, LinearMap.mem_ker, LinearMap.sub_apply,
          LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] using hp
      exact h ⟨B i, hmem⟩
    · rw [← B.linearCombination_repr x.val]
      simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul]
      apply Finset.sum_eq_zero
      intro j hj
      have hjOdd := negative_support ℒ leechUnit x j hj
      have hne : (oddWeight ℒ i.1 : ℤ) ≠ (oddWeight ℒ j.1 : ℤ) := by
        intro he
        exact hi ((Int.ofNat.inj he).symm ▸ hjOdd)
      rw [actualForm_oddGrade_orthogonal ℒ leechUnit _ _ (B i) (B j)
        (by simpa only [Int.cast_natCast] using (actualGrade_eigen ℒ leechUnit _ _).mp (hgrade i))
        (by simpa only [Int.cast_natCast] using (actualGrade_eigen ℒ leechUnit _ _).mp (hgrade j))
        hne, smul_zero]
  apply Subtype.ext
  exact (actualForm_nondegenerate ℒ leechUnit).2 x.val (LinearMap.congr_fun hzero)

/-- The vector coefficient of the native mixed product at independent doubled modes.
Swapping the two even inputs gives the product used in the D channel. -/
def hhbbBVectorTerm (u v : TwistedEven) (w : TwistedOdd) (p : ℤ × ℤ) : TwistedOdd :=
  (rightField ℒ leechUnit false u).coeff p.2 ((mu false v).coeff p.1 w)

/-- The vector coefficient of the native fixed iterate at independent doubled modes. -/
def hhbbAVectorTerm (u v : TwistedEven) (w : TwistedOdd) (p : ℤ × ℤ) : TwistedOdd :=
  ⟨(correctedField ℒ leechUnit ((nu false u).coeff p.1 v).val).coeff p.2 w.val,
    fixed_parity_preserved ℒ leechUnit (paritySign true) _ p.2 w.val w.property⟩

private theorem finite_support_of_int_bound {f : ℕ → TwistedOdd} (bound : ℤ)
    (h : ∀ j : ℕ, bound < (j : ℤ) → f j = 0) : Function.HasFiniteSupport f := by
  refine (Set.finite_lt_nat (bound.toNat + 1)).subset ?_
  intro j hj
  change j < bound.toNat + 1
  by_contra! hlarge
  exact hj (h j (by omega))

private theorem hhbb_vector_terms_finite (u v : TwistedEven) (w : TwistedOdd)
    (W q r : ℤ) (weightB weightD weightA : ℕ → ℂ) :
    Function.HasFiniteSupport (fun j => weightB j • hhbbBVectorTerm u v w (bModes W q r j)) ∧
    Function.HasFiniteSupport (fun j => weightD j • hhbbBVectorTerm v u w (dModes W q j)) ∧
    Function.HasFiniteSupport (fun j => weightA j • hhbbAVectorTerm u v w (aModes W r j)) := by
  let U : ℤ := maxOddWeight ℒ leechUnit u.val
  let V : ℤ := maxOddWeight ℒ leechUnit v.val
  let H : ℤ := maxOddWeight ℒ leechUnit w.val
  refine ⟨finite_support_of_int_bound (2 * (W + q + r + 1) + V + H + 6) ?_,
    finite_support_of_int_bound (-2 * q + U + H + 6) ?_,
    finite_support_of_int_bound (-2 * (r + 1) + U + V + 6) ?_⟩
  · intro j hj
    have hz := mu_lower_truncation false v w (bModes W q r j).1
      (show (bModes W q r j).1 ≤ -V - H - 6 by dsimp only [bModes]; omega)
    simp only [hhbbBVectorTerm, hz, map_zero, smul_zero]
  · intro j hj
    have hz := mu_lower_truncation false u w (dModes W q j).1
      (show (dModes W q j).1 ≤ -U - H - 6 by dsimp only [dModes]; omega)
    simp only [hhbbBVectorTerm, hz, map_zero, smul_zero]
  · intro j hj
    have hz := nu_lower_truncation false u v (aModes W r j).1
      (show (aModes W r j).1 < -U - V - 6 by dsimp only [aModes]; omega)
    have hz' : hhbbAVectorTerm u v w (aModes W r j) = 0 := by
      apply Subtype.ext
      simp only [hhbbAVectorTerm, hz, Submodule.coe_zero, map_zero, Pi.zero_apply,
        LinearMap.zero_apply]
    rw [hz', smul_zero]

private def pairOdd (b : TwistedOdd) : TwistedOdd →ₗ[ℂ] ℂ :=
  (actualForm ℒ leechUnit b.val).comp (paritySpace ℒ leechUnit (paritySign true)).subtype

private theorem pairOdd_bVector (u v : TwistedEven) (w b : TwistedOdd) (p : ℤ × ℤ) :
    pairOdd b (hhbbBVectorTerm u v w p) = bJointTerm false false v w u b 1 1 p := by
  simp only [pairOdd, hhbbBVectorTerm, bJointTerm, LinearMap.comp_apply, Submodule.subtype_apply,
    one_zpow, mul_one]

private theorem pairOdd_aVector (u v : TwistedEven) (w b : TwistedOdd) (p : ℤ × ℤ) :
    pairOdd b (hhbbAVectorTerm u v w p) = aJointTerm u v w b 1 1 p := by
  simp only [pairOdd, hhbbAVectorTerm, aJointTerm, LinearMap.comp_apply, Submodule.subtype_apply,
    one_zpow, mul_one]

private theorem vector_eq_of_paired_sums (B D A : ℕ → TwistedOdd)
    (hB : Function.HasFiniteSupport B) (hD : Function.HasFiniteSupport D)
    (hA : Function.HasFiniteSupport A)
    (h : ∀ b : TwistedOdd, -(∑ᶠ j, pairOdd b (B j)) - (∑ᶠ j, pairOdd b (D j)) =
      ∑ᶠ j, pairOdd b (A j)) :
    -(∑ᶠ j, B j) - (∑ᶠ j, D j) = ∑ᶠ j, A j := by
  refine sub_eq_zero.mp (actualForm_twistedOdd_separates _ (fun b => ?_))
  change pairOdd b (-(∑ᶠ j, B j) - (∑ᶠ j, D j) - (∑ᶠ j, A j)) = 0
  rw [map_sub (pairOdd b), sub_eq_zero, map_sub (pairOdd b), map_neg (pairOdd b),
    map_finsum (pairOdd b) hB, map_finsum (pairOdd b) hD, map_finsum (pairOdd b) hA]
  exact h b

/-- Raw HHBB mode Jacobi on the actual Leech twisted vectors, with the
generalized binomial exponent `q - 1/2` and arbitrary integer selectors. -/
theorem hhbb_raw_vector_mode_jacobi (u v : TwistedEven) (w : TwistedOdd) (W q r : ℤ) :
    -(∑ᶠ j : ℕ, ((-1 : ℂ) ^ j * ((Ring.choose r j : ℤ) : ℂ)) •
        hhbbBVectorTerm u v w (bModes W q r j)) -
      (∑ᶠ j : ℕ, ((-1 : ℂ) ^ (r + (j : ℤ)) * ((Ring.choose r j : ℤ) : ℂ)) •
        hhbbBVectorTerm v u w (dModes W q j)) =
      ∑ᶠ j : ℕ, Ring.choose ((q : ℂ) - 1 / 2) j • hhbbAVectorTerm u v w (aModes W r j) := by
  obtain ⟨hB, hD, hA⟩ := hhbb_vector_terms_finite u v w W q r
    (fun j => (-1 : ℂ) ^ j * ((Ring.choose r j : ℤ) : ℂ))
    (fun j => (-1 : ℂ) ^ (r + (j : ℤ)) * ((Ring.choose r j : ℤ) : ℂ))
    (fun j => Ring.choose ((q : ℂ) - 1 / 2) j)
  refine vector_eq_of_paired_sums _ _ _ hB hD hA ?_
  intro b
  simp only [map_smul, smul_eq_mul, pairOdd_bVector, pairOdd_aVector]
  exact hhbb_raw_scalar_mode_jacobi u v w b W q r

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBModeResidue
