/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeFixedPairField
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeFixedPairField
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual same-parity Leech twisted-pair field and its orbifold normalization. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeFixedPairState
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairField

/-!
The upper-branch homogeneous states of Huang, hep-th/9406190v7, §3.4
assemble on the finite actual tensor coordinates. Fixed lattice energy
bounds the doubled exponents from below for each pair of inputs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeFixedPairField

open ActualLeechHyperbolic (leechData leech_spec)
open NativeOddTwistedIntertwiner (Twisted TwistedEven TwistedOdd leechUnit paritySign)
open LatticeInvolution (FixedCarrier fixedVacuum fixedSpace)
open LatticeHalfFockChargedTensorCoefficients (ActualTensor groundRank)
open LatticeTwistedGroundRealization (Half)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open LatticeHalfFockParityT (actualParity_preserves_grade)
open LatticeHalfFockCorrectedField (correctedField)
open LatticeHalfFockGradedTrace
open ActualChargedAdjoint (actualForm)
open ActualEnergyRestrictedDual (maxOddWeight)
open CorrectedInversion (K_R)
open FixedGradedDuality (fixedGradeSubmodule)
open NativeFullMixedField (project)
open NativeFixedPairState
open OriginalFourMChargeCoset (originalI)
open private T from D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private fixedPairStateInGrade leechFixedGradeDual from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeFixedPairState
open private project_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeFullMixedField
open private sum_projectedBasis from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairField

local notation "ℒ" => leechData
private abbrev ambientBasis := actualAmbientBasis ℒ leechUnit
private abbrev TwistedState (s : Bool) := Twisted ℒ leechUnit s
private abbrev LatticeFixed := FixedCarrier ℒ

private def rightKernel (e : ℤ) :
    ActualTensor ℒ leechUnit →ₗ[ℂ] ActualTensor ℒ leechUnit →ₗ[ℂ]
      Module.Dual ℂ (LatticeGeneratingFieldLocality.Carrier ℒ) where
  toFun u :=
    { toFun := fun v => K_R ℒ leechUnit e v u
      map_add' v w := LinearMap.ext fun a =>
        LinearMap.congr_fun ((actualForm ℒ leechUnit).map_add v w)
          ((correctedField ℒ leechUnit a).coeff e u)
      map_smul' c v := LinearMap.ext fun a =>
        LinearMap.congr_fun ((actualForm ℒ leechUnit).map_smul c v)
          ((correctedField ℒ leechUnit a).coeff e u) }
  map_add' u w := LinearMap.ext fun v => LinearMap.ext fun a => by
    change actualForm ℒ leechUnit v ((correctedField ℒ leechUnit a).coeff e (u + w)) = _
    exact ((actualForm ℒ leechUnit v).comp ((correctedField ℒ leechUnit a).coeff e)).map_add u w
  map_smul' c u := LinearMap.ext fun v => LinearMap.ext fun a => by
    change actualForm ℒ leechUnit v ((correctedField ℒ leechUnit a).coeff e (c • u)) = _
    exact ((actualForm ℒ leechUnit v).comp ((correctedField ℒ leechUnit a).coeff e)).map_smul c u

private def homogeneousCoefficient (s : Bool) (M K : ℕ) (m : ℤ) :
    TwistedState s →ₗ[ℂ] TwistedState s →ₗ[ℂ] LatticeFixed :=
  let h := fixedPairWeight M K m
  let restrict := LinearMap.lcomp ℂ ℂ ((fixedSpace ℒ).subtype.comp
    (fixedGradeSubmodule ℒ h).subtype)
  let realize := ((fixedGradeSubmodule ℒ h).subtype.comp
    (leechFixedGradeDual h).symm.toLinearMap).comp restrict
  let lower := fun j : ℕ =>
    (T ℒ leechUnit ^ j).comp (paritySpace ℒ leechUnit (paritySign s)).subtype
  let pairing := Complex.I ^ (-(3 + (M : ℤ))) •
    ∑ j ∈ Finset.range (M / 2 + 1), ∑ ell ∈ Finset.range (K / 2 + 1),
      (((-1 : ℂ) ^ ((M : ℤ) - m - (j : ℤ) + (ell : ℤ) + 2)) /
        ((j.factorial : ℂ) * (ell.factorial : ℂ))) •
      ((rightKernel (2 * (m + (j : ℤ) - (ell : ℤ) - (M : ℤ) - 2))).compl₁₂
        (lower j) (lower ell))
  pairing.compr₂ realize

private theorem homogeneousCoefficient_apply (s : Bool) (M K : ℕ) (m : ℤ)
    (u v : TwistedState s) :
    homogeneousCoefficient s M K m u v = fixedPairState s M K m u v := by
  simp only [homogeneousCoefficient, fixedPairState, fixedPairStateInGrade, fixedPairing,
    LinearMap.compr₂_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.compl₁₂_apply, Submodule.subtype_apply]
  apply congrArg (fun f => ((leechFixedGradeDual (fixedPairWeight M K m)).symm f).val)
  apply LinearMap.ext
  intro a
  simp only [LinearMap.lcomp_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sum_apply]
  rfl

private def coefficient (s : Bool) (m : ℤ) :
    TwistedState s →ₗ[ℂ] TwistedState s →ₗ[ℂ] LatticeFixed :=
  let ambient := ambientBasis.constr ℂ fun i =>
    ambientBasis.constr ℂ fun j =>
      fixedPairState s (oddWeight ℒ i.1) (oddWeight ℒ j.1) m
        (project s (ambientBasis i)) (project s (ambientBasis j))
  ambient.domRestrict₁₂ _ _

private theorem coefficient_sum (s : Bool) (m : ℤ) (u v : TwistedState s) :
    coefficient s m u v =
      ∑ i ∈ (ambientBasis.repr u.val).support, ambientBasis.repr u.val i •
        ∑ j ∈ (ambientBasis.repr v.val).support, ambientBasis.repr v.val j •
          fixedPairState s (oddWeight ℒ i.1) (oddWeight ℒ j.1) m
            (project s (ambientBasis i)) (project s (ambientBasis j)) := by
  simp only [coefficient, LinearMap.domRestrict₁₂_apply, Module.Basis.constr_apply, Finsupp.sum,
    LinearMap.sum_apply, LinearMap.smul_apply]

private theorem expand_on_projectedBasis (s : Bool)
    (C : TwistedState s →ₗ[ℂ] TwistedState s →ₗ[ℂ] LatticeFixed) (u v : TwistedState s) :
    C u v =
      ∑ i ∈ (ambientBasis.repr u.val).support, ambientBasis.repr u.val i •
        ∑ j ∈ (ambientBasis.repr v.val).support, ambientBasis.repr v.val j •
          C (project s (ambientBasis i)) (project s (ambientBasis j)) := by
  calc
    C u v = C
        (∑ i ∈ (ambientBasis.repr u.val).support,
          ambientBasis.repr u.val i • project s (ambientBasis i))
        (∑ j ∈ (ambientBasis.repr v.val).support,
          ambientBasis.repr v.val j • project s (ambientBasis j)) :=
      congrArg₂ (fun x y => C x y) (sum_projectedBasis s u).symm (sum_projectedBasis s v).symm
    _ = ∑ i ∈ (ambientBasis.repr u.val).support, ambientBasis.repr u.val i •
        C (project s (ambientBasis i))
          (∑ j ∈ (ambientBasis.repr v.val).support,
            ambientBasis.repr v.val j • project s (ambientBasis j)) := by
      rw [LinearMap.map_sum₂]
      simp only [map_smul, LinearMap.smul_apply]
    _ = _ := by simp only [map_sum, map_smul]

private theorem coefficient_of_grade (s : Bool) (M K : ℕ) (m : ℤ)
    (u v : TwistedState s)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K) :
    coefficient s m u v = fixedPairState s M K m u v := by
  have hu' := (actual_grade_mem_iff_repr_support ℒ leechUnit M u.val).mp hu
  have hv' := (actual_grade_mem_iff_repr_support ℒ leechUnit K v.val).mp hv
  rw [coefficient_sum, ← homogeneousCoefficient_apply, expand_on_projectedBasis]
  apply Finset.sum_congr rfl
  intro i hi
  apply congrArg (fun a : LatticeFixed => ambientBasis.repr u.val i • a)
  apply Finset.sum_congr rfl
  intro j hj
  rw [homogeneousCoefficient_apply, hu' i hi, hv' j hj]

private theorem coefficient_truncation (s : Bool) (m : ℤ) (u v : TwistedState s)
    (hm : (maxOddWeight ℒ leechUnit u.val : ℤ) + (maxOddWeight ℒ leechUnit v.val : ℤ) + 4 <
      2 * m) :
    coefficient s m u v = 0 := by
  rw [coefficient_sum]
  refine Finset.sum_eq_zero fun i hi => smul_eq_zero.mpr (Or.inr ?_)
  refine Finset.sum_eq_zero fun j hj => smul_eq_zero.mpr (Or.inr ?_)
  have hi' : oddWeight ℒ i.1 ≤ maxOddWeight ℒ leechUnit u.val :=
    Finset.le_sup (f := fun k => oddWeight ℒ k.1) hi
  have hj' : oddWeight ℒ j.1 ≤ maxOddWeight ℒ leechUnit v.val :=
    Finset.le_sup (f := fun k => oddWeight ℒ k.1) hj
  exact fixedPairState_truncation s _ _ m _ _ (by omega)

private def doubledCoefficient (s : Bool) (e : ℤ) :
    TwistedState s →ₗ[ℂ] TwistedState s →ₗ[ℂ] LatticeFixed :=
  if Even e then coefficient s ((-e - 2) / 2) else 0

private theorem doubledCoefficient_truncation (s : Bool) (e : ℤ) (u v : TwistedState s)
    (he : e < -(maxOddWeight ℒ leechUnit u.val : ℤ) -
      (maxOddWeight ℒ leechUnit v.val : ℤ) - 6) :
    doubledCoefficient s e u v = 0 := by
  by_cases h : Even e
  · rw [doubledCoefficient, ite_eq_left h]
    obtain ⟨k, hk⟩ := h
    exact coefficient_truncation s _ u v (by omega)
  · simp [doubledCoefficient, h]

private theorem doubledCoefficient_support (s : Bool) (u v : TwistedState s) :
    (Function.support (fun e => doubledCoefficient s e u v)).IsPWO := by
  apply Set.isPWO_iff_isWF.mpr
  apply BddBelow.isWF
  refine ⟨-(maxOddWeight ℒ leechUnit u.val : ℤ) -
    (maxOddWeight ℒ leechUnit v.val : ℤ) - 6, ?_⟩
  intro e he
  exact le_of_not_gt fun h => he (doubledCoefficient_truncation s e u v h)

/-- The actual same-parity twisted-pair field. Its Hahn index is twice the
physical exponent, and its values lie in the fixed lattice carrier. -/
def nu (s : Bool) : Twisted ℒ leechUnit s →ₗ[ℂ]
    HVertexOperator ℤ ℂ (Twisted ℒ leechUnit s) (FixedCarrier ℒ) where
  toFun u := HVertexOperator.of_coeff (fun e => doubledCoefficient s e u)
    (doubledCoefficient_support s u)
  map_add' u v := by
    apply HVertexOperator.coeff_inj
    funext e
    rw [map_add, Pi.add_apply]
    exact (doubledCoefficient s e).map_add u v
  map_smul' c u := by
    apply HVertexOperator.coeff_inj
    funext e
    rw [map_smul, Pi.smul_apply]
    exact (doubledCoefficient s e).map_smul c u

private theorem nu_coeff_mode (s : Bool) (m : ℤ) (u v : TwistedState s) :
    (nu s u).coeff (-2 * m - 2) v = coefficient s m u v := by
  have he : Even (-2 * m - 2) := ⟨-m - 1, by omega⟩
  change doubledCoefficient s (-2 * m - 2) u v = _
  rw [doubledCoefficient, ite_eq_left he, show (-(-2 * m - 2) - 2) / 2 = m by omega]

/-- Every homogeneous pair recovers the upper-branch reconstructed state at
each physical exponent `-m-1`. -/
theorem nu_coeff_of_grade (s : Bool) (M K : ℕ) (m : ℤ) (u v : Twisted ℒ leechUnit s)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K) :
    (nu s u).coeff (-2 * m - 2) v = fixedPairState s M K m u v := by
  rw [nu_coeff_mode, coefficient_of_grade s M K m u v hu hv]

/-- The fixed channel has only even doubled exponents. -/
theorem nu_coeff_odd_zero (s : Bool) (e : ℤ) (u v : Twisted ℒ leechUnit s) (he : Odd e) :
    (nu s u).coeff e v = 0 := by
  change doubledCoefficient s e u v = 0
  rw [doubledCoefficient, ite_eq_right (Int.not_even_iff_odd.mpr he)]
  rfl

/-- The minimum possible doubled exponent is minus the sum of the two maximal
actual excitations minus six. The bound includes the zero vector. -/
theorem nu_lower_truncation (s : Bool) (u v : Twisted ℒ leechUnit s) :
    ∀ e < -(maxOddWeight ℒ leechUnit u.val : ℤ) - (maxOddWeight ℒ leechUnit v.val : ℤ) - 6,
      (nu s u).coeff e v = 0 :=
  fun e he => doubledCoefficient_truncation s e u v he

private theorem projectedBasis_mem_grade (s : Bool)
    (i : OddMonomial ℒ × Half (groundRank ℒ leechUnit)) :
    (project s (ambientBasis i)).val ∈ actualGrade ℒ leechUnit (oddWeight ℒ i.1) := by
  have hi : ambientBasis i ∈ actualGrade ℒ leechUnit (oddWeight ℒ i.1) := by
    simpa only [actualGrade, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero, Prod.eta] using actual_basis_eigenvalue ℒ leechUnit i.1 i.2
  rw [project_val]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ hi (Submodule.smul_mem _ _
    (actualParity_preserves_grade ℒ leechUnit _ _ hi)))

/-- The negative-parity channel agrees with the original orbifold field on
arbitrary inputs, including inhomogeneous states. -/
theorem nu_coeff_eq_originalI (m : ℤ) (u v : TwistedOdd) :
    (nu true u).coeff (-2 * m - 2) v = originalI ℒ leechUnit leech_spec.2.2.1 m u v := by
  let original : TwistedState true →ₗ[ℂ] TwistedState true →ₗ[ℂ] LatticeFixed :=
    originalI ℒ leechUnit leech_spec.2.2.1 m
  change (nu true u).coeff (-2 * m - 2) v = original u v
  rw [nu_coeff_mode, coefficient_sum, expand_on_projectedBasis true original u v]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun a : LatticeFixed => ambientBasis.repr u.val i • a)
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun a : LatticeFixed => ambientBasis.repr v.val j • a)
    (fixedPairState_eq_originalI _ _ m _ _
      (projectedBasis_mem_grade true i) (projectedBasis_mem_grade true j))

/-- At doubled exponent `-6`, two actual half-integral twisted ground states
produce `I` times the ordered twisted pairing times the fixed vacuum. -/
theorem nu_ground_vacuum (u v : TwistedEven)
    (hu : u.val ∈ actualGrade ℒ leechUnit 0) (hv : v.val ∈ actualGrade ℒ leechUnit 0) :
    (nu false u).coeff (-6) v =
      (Complex.I * actualForm ℒ leechUnit v.val u.val) • fixedVacuum ℒ := by
  rw [show (-6 : ℤ) = -2 * 2 - 2 by decide, nu_coeff_of_grade false 0 0 2 u v hu hv]
  exact fixedPairState_ground u v hu hv

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeFixedPairField
