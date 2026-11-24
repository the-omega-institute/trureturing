/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeMixedPairField
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeMixedPairField
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bilinear mixed twisted-pair field for four-point sewing on the actual Leech extension. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairState
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeFullMixedField

/-!
Four-point sewing on the actual extension `V_L ⊕ V_L^T` requires an
odd-lattice-valued field on arbitrary inputs of opposite twisted parities.
The actual tensor basis has finite coordinate support on each input.
The resulting field extends the homogeneous BPZ reconstruction in Huang,
hep-th/9406190v7, §3.4, with doubled Hahn exponent `-2 * m - 3`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairField

open ActualLeechHyperbolic (leechData)
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockGradedTrace LatticeHalfFockCorrectedField
open LatticeHalfFockParityT LatticePositiveEnergy ActualChargedAdjoint
open HalfFock.LatticeHalfFockParityField (paritySpace)
open NativeOddTwistedIntertwiner NativeOddUpperRightSkew NativeMixedPairState
open NativeFullMixedField (project)
open ActualEnergyRestrictedDual (maxOddWeight)
open SourceBPZ.OriginalSourcePairing (sourcePairing)
open private oddGradeDualEquiv oddGradeInclusion from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairState
open private project_on from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeFullMixedField
open private groundBasis_energy oddCurrent_grade_one from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner

private abbrev ambientBasis := actualAmbientBasis leechData leechUnit
private abbrev TwistedState (s : Bool) := Twisted leechData leechUnit s
private abbrev LatticeOdd := OddCarrier leechData

private def mixedPairingBilinear (s : Bool) (M : ℕ) (m : ℤ) :
    TwistedState s →ₗ[ℂ] TwistedState (!s) →ₗ[ℂ] Module.Dual ℂ LatticeOdd :=
  let p := paritySpace leechData leechUnit (paritySign (!s))
  let metric := (actualForm leechData leechUnit).domRestrict₁₂ p p
  let evaluate := ((LinearMap.llcomp ℂ LatticeOdd (TwistedState (!s)) ℂ).comp metric).flip
  Complex.I ^ (-(3 + (M : ℤ))) •
    ∑ j ∈ Finset.range (M / 2 + 1),
      (j.factorial : ℂ)⁻¹ • evaluate.comp
        ((R leechData leechUnit s ((M : ℤ) - m - (j : ℤ))).comp
          (lowering leechData leechUnit s ^ j))

private def homogeneousCoefficient (s : Bool) (M K : ℕ) (m : ℤ) :
    TwistedState s →ₗ[ℂ] TwistedState (!s) →ₗ[ℂ] LatticeOdd :=
  let h := mixedPairWeight M K m
  let realize := (oddGradeInclusion h).comp
    ((oddGradeDualEquiv h).symm.toLinearMap.comp
      (LinearMap.lcomp ℂ ℂ (oddGradeInclusion h)))
  (mixedPairingBilinear s M m).compr₂ realize

private theorem homogeneousCoefficient_apply (s : Bool) (M K : ℕ) (m : ℤ)
    (u : TwistedState s) (v : TwistedState (!s)) :
    homogeneousCoefficient s M K m u v = mixedPairState s M K m u v := by
  have hp : mixedPairingBilinear s M m u v = mixedPairing s M m u v := by
    simp only [mixedPairingBilinear, mixedPairing, LinearMap.smul_apply, LinearMap.sum_apply,
      LinearMap.comp_apply, LinearMap.flip_apply, LinearMap.llcomp_apply', LinearMap.domRestrict₁₂,
      LinearMap.domRestrict₂, LinearMap.domRestrict_apply]
    rfl
  change oddGradeInclusion _ ((oddGradeDualEquiv _).symm
    ((mixedPairingBilinear s M m u v).comp (oddGradeInclusion _))) = _
  rw [hp]
  rfl

private def coefficient (s : Bool) (m : ℤ) :
    TwistedState s →ₗ[ℂ] TwistedState (!s) →ₗ[ℂ] LatticeOdd :=
  let ambient := ambientBasis.constr ℂ fun i =>
    ambientBasis.constr ℂ fun j =>
      mixedPairState s (oddWeight leechData i.1) (oddWeight leechData j.1) m
        (project s (ambientBasis i)) (project (!s) (ambientBasis j))
  ambient.domRestrict₁₂ _ _

private theorem coefficient_sum (s : Bool) (m : ℤ)
    (u : TwistedState s) (v : TwistedState (!s)) :
    coefficient s m u v =
      ∑ i ∈ (ambientBasis.repr u.val).support, ambientBasis.repr u.val i •
        ∑ j ∈ (ambientBasis.repr v.val).support, ambientBasis.repr v.val j •
          mixedPairState s (oddWeight leechData i.1) (oddWeight leechData j.1) m
            (project s (ambientBasis i)) (project (!s) (ambientBasis j)) := by
  simp only [coefficient, LinearMap.domRestrict₁₂_apply, Module.Basis.constr_apply, Finsupp.sum,
    LinearMap.sum_apply, LinearMap.smul_apply]

private theorem sum_projectedBasis (s : Bool) (u : TwistedState s) :
    (∑ i ∈ (ambientBasis.repr u.val).support,
      ambientBasis.repr u.val i • project s (ambientBasis i)) = u := by
  have hp : project s u.val = u :=
    Subtype.ext (by simpa using project_on s s u)
  calc
    _ = project s (Finsupp.linearCombination ℂ ambientBasis (ambientBasis.repr u.val)) := by
      simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul]
    _ = u := by rw [ambientBasis.linearCombination_repr, hp]

private theorem coefficient_of_grade (s : Bool) (M K : ℕ) (m : ℤ)
    (u : TwistedState s) (v : TwistedState (!s))
    (hu : u.val ∈ actualGrade leechData leechUnit M)
    (hv : v.val ∈ actualGrade leechData leechUnit K) :
    coefficient s m u v = mixedPairState s M K m u v := by
  have hu' := (actual_grade_mem_iff_repr_support leechData leechUnit M u.val).mp hu
  have hv' := (actual_grade_mem_iff_repr_support leechData leechUnit K v.val).mp hv
  let C := homogeneousCoefficient s M K m
  have hexpand : C u v =
      ∑ i ∈ (ambientBasis.repr u.val).support, ambientBasis.repr u.val i •
        ∑ j ∈ (ambientBasis.repr v.val).support, ambientBasis.repr v.val j •
          C (project s (ambientBasis i)) (project (!s) (ambientBasis j)) := by
    calc
      C u v = C
          (∑ i ∈ (ambientBasis.repr u.val).support,
            ambientBasis.repr u.val i • project s (ambientBasis i))
          (∑ j ∈ (ambientBasis.repr v.val).support,
            ambientBasis.repr v.val j • project (!s) (ambientBasis j)) :=
        congrArg₂ (fun x y => C x y) (sum_projectedBasis s u).symm
          (sum_projectedBasis (!s) v).symm
      _ = ∑ i ∈ (ambientBasis.repr u.val).support, ambientBasis.repr u.val i •
          C (project s (ambientBasis i))
            (∑ j ∈ (ambientBasis.repr v.val).support,
              ambientBasis.repr v.val j • project (!s) (ambientBasis j)) := by
        rw [LinearMap.map_sum₂]
        simp only [map_smul, LinearMap.smul_apply]
      _ = _ := by simp only [map_sum, map_smul]
  refine (coefficient_sum s m u v).trans (Eq.trans ?_
    (hexpand.symm.trans (homogeneousCoefficient_apply s M K m u v)))
  apply Finset.sum_congr rfl
  intro i hi
  apply congrArg (fun a : LatticeOdd => ambientBasis.repr u.val i • a)
  apply Finset.sum_congr rfl
  intro j hj
  apply congrArg (fun a : LatticeOdd => ambientBasis.repr v.val j • a)
  rw [hu' i hi, hv' j hj]
  exact (homogeneousCoefficient_apply s M K m _ _).symm

private theorem coefficient_truncation (s : Bool) (m : ℤ)
    (u : TwistedState s) (v : TwistedState (!s))
    (hm : (maxOddWeight leechData leechUnit u.val : ℤ) +
      (maxOddWeight leechData leechUnit v.val : ℤ) + 3 ≤ 2 * m) :
    coefficient s m u v = 0 := by
  rw [coefficient_sum]
  refine Finset.sum_eq_zero fun i hi => smul_eq_zero.mpr (Or.inr ?_)
  refine Finset.sum_eq_zero fun j hj => smul_eq_zero.mpr (Or.inr ?_)
  have hi' : oddWeight leechData i.1 ≤ maxOddWeight leechData leechUnit u.val :=
    Finset.le_sup (f := fun k => oddWeight leechData k.1) hi
  have hj' : oddWeight leechData j.1 ≤ maxOddWeight leechData leechUnit v.val :=
    Finset.le_sup (f := fun k => oddWeight leechData k.1) hj
  exact mixedPairState_truncation s _ _ m _ _ (by omega)

private def doubledCoefficient (s : Bool) (e : ℤ) :
    TwistedState s →ₗ[ℂ] TwistedState (!s) →ₗ[ℂ] LatticeOdd :=
  if Even e then 0 else coefficient s ((-e - 3)/2)

private theorem doubledCoefficient_truncation (s : Bool) (e : ℤ)
    (u : TwistedState s) (v : TwistedState (!s))
    (he : e ≤ -(maxOddWeight leechData leechUnit u.val : ℤ) -
      (maxOddWeight leechData leechUnit v.val : ℤ) - 6) :
    doubledCoefficient s e u v = 0 := by
  by_cases h : Even e
  · simp [doubledCoefficient, h]
  · rw [doubledCoefficient, ite_eq_right h]
    have hodd := Int.not_even_iff.mp h
    exact coefficient_truncation s _ u v (by omega)

private theorem doubledCoefficient_support (s : Bool)
    (u : TwistedState s) (v : TwistedState (!s)) :
    (Function.support (fun e => doubledCoefficient s e u v)).IsPWO := by
  apply Set.isPWO_iff_isWF.mpr
  apply BddBelow.isWF
  refine ⟨-(maxOddWeight leechData leechUnit u.val : ℤ) -
    (maxOddWeight leechData leechUnit v.val : ℤ) - 6, ?_⟩
  intro e he
  exact le_of_not_gt fun h => he (doubledCoefficient_truncation s e u v h.le)

/-- The actual bilinear mixed twisted-pair field in both orders. Its Hahn
index is twice the physical exponent. -/
def mu (s : Bool) :
    Twisted leechData leechUnit s →ₗ[ℂ]
      HVertexOperator ℤ ℂ (Twisted leechData leechUnit (!s)) (OddCarrier leechData) where
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

/-- Exact restriction at every homogeneous pair and every half-integer
physical exponent of the mixed field. -/
theorem mu_coeff_of_grade (s : Bool) (M K : ℕ) (m : ℤ)
    (u : Twisted leechData leechUnit s) (v : Twisted leechData leechUnit (!s))
    (hu : u.val ∈ actualGrade leechData leechUnit M)
    (hv : v.val ∈ actualGrade leechData leechUnit K) :
    (mu s u).coeff (-2 * m - 3) v = mixedPairState s M K m u v := by
  have he : ¬ Even (-2 * m - 3) := by
    rintro ⟨k, hk⟩
    omega
  change doubledCoefficient s (-2 * m - 3) u v = _
  rw [doubledCoefficient, ite_eq_right he, show (-(-2 * m - 3) - 3)/2 = m by omega]
  exact coefficient_of_grade s M K m u v hu hv

/-- The mixed channel is supported on odd doubled exponents. -/
theorem mu_coeff_even_zero (s : Bool) (e : ℤ)
    (u : Twisted leechData leechUnit s) (v : Twisted leechData leechUnit (!s))
    (he : Even e) :
    (mu s u).coeff e v = 0 := by
  change doubledCoefficient s e u v = 0
  simp [doubledCoefficient, he]

/-- A pointwise lower bound for the doubled Hahn support from the two finite
actual coordinate supports. -/
theorem mu_lower_truncation (s : Bool)
    (u : Twisted leechData leechUnit s) (v : Twisted leechData leechUnit (!s)) :
    ∀ e ≤ -(maxOddWeight leechData leechUnit u.val : ℤ) -
      (maxOddWeight leechData leechUnit v.val : ℤ) - 6, (mu s u).coeff e v = 0 :=
  fun e he => doubledCoefficient_truncation s e u v he

/-- The normalized bottom coefficients of the two orders carry the relative
phase `I` in the same original lattice source pairing. -/
theorem leech_mu_normalization (i : Fin leechData.rank) :
    let t := leechGroundVector
    ∃ c : ℂ, c^2 * (leechData.G i i : ℂ) = 2 ∧
    let h := c • oddCurrent leechData i
    let b := Jplus (-1) h t
    ∃ (bDual : TwistedOdd) (tDual : TwistedEven),
      bDual.val ∈ actualGrade leechData leechUnit 1 ∧
      tDual.val ∈ actualGrade leechData leechUnit 0 ∧
      actualForm leechData leechUnit b.val bDual.val = 1 ∧
      actualForm leechData leechUnit t.val tDual.val = 1 ∧
      Jminus 0 h b = t ∧
      sourcePairing leechData ((mu false t).coeff (-5) bDual).val h.val = 1 ∧
      sourcePairing leechData ((mu true b).coeff (-5) tDual).val h.val = Complex.I := by
  dsimp only
  obtain ⟨c, hc, bDual, tDual, hbDual, htDual, hbd, htd, hret, hp, hm, _⟩ :=
    leech_mixedPairState_normalization i
  let t := leechGroundVector
  let h := c • oddCurrent leechData i
  let b := Jplus (-1) h t
  have ht : t.val ∈ actualGrade leechData leechUnit 0 := groundBasis_energy
  have ha : h.val ∈ grade leechData 1 :=
    (grade leechData 1).smul_mem c (oddCurrent_grade_one leechData i)
  have hb : b.val ∈ actualGrade leechData leechUnit 1 :=
    J_grade leechData leechUnit false (-1) 1 0 1 h t ha ht (by norm_num)
  have hp' := mu_coeff_of_grade false 0 1 1 t bDual ht hbDual
  have hm' := mu_coeff_of_grade true 1 0 1 b tDual hb htDual
  change (mu false t).coeff (-5) bDual = _ at hp'
  change (mu true b).coeff (-5) tDual = _ at hm'
  refine ⟨c, hc, bDual, tDual, hbDual, htDual, hbd, htd, hret, ?_, ?_⟩
  · rw [hp']
    exact hp
  · rw [hm']
    exact hm

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairField
