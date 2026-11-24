/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeMixedPairState
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeMixedPairState
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Realization of homogeneous mixed twisted-pair coefficients in the actual odd Leech carrier. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew
import D5.S3.VertexAlgebra.Lattice.FixedGradedDuality
import D5.S3.VertexAlgebra.SourceBPZ.SourcePairingLaws
import D5.S3.VertexAlgebra.SourceBPZ.ThetaReflectionAction
import Batteries.Tactic.OpenPrivate

/-!
The mixed twisted-pair coefficient in the odd lattice channel of Huang,
hep-th/9406190v7, §3.4, at physical exponent `-m-3/2`. Its matrix
coefficients are evaluated with the original lattice BPZ form.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairState

open LatticeGeneratingFieldLocality LatticeInvolution LatticePositiveEnergy
open LatticeAllStateField (vacuum)
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockGradedTrace ActualChargedAdjoint ActualOddGradeOrthogonality
open ActualLeechHyperbolic (leechData leech_spec)
open NativeOddTwistedIntertwiner NativeOddUpperRightSkew
open SourceBPZ.OriginalSourcePairing (sourcePairing sourcePairing_symmetric
  sourcePairing_nondegenerate)
open SourceBPZ.SourcePairingLaws (sourcePairing_theta sourcePairing_grade)
open private T lowering_eigen negative_eigen_zero from
  D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private actualGrade_eigen lowering_pow_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew
open private J_val oddCurrent_grade_one groundBasis_energy from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
open private left_grade_projection_pairing from
  D5.S3.VertexAlgebra.Lattice.FixedGradedDuality

/-- The mixed BPZ functional is supported on the exact signed lattice degree.
Both lowering orders cancel from the equality of the two tested degrees. -/
theorem mixedPairing_off_grade (s : Bool) (M K : ℕ) (m h : ℤ)
    (u : Twisted leechData leechUnit s) (v : Twisted leechData leechUnit (!s))
    (hu : u.val ∈ actualGrade leechData leechUnit M)
    (hv : v.val ∈ actualGrade leechData leechUnit K)
    (a : OddCarrier leechData) (ha : a.val ∈ grade leechData h)
    (hne : 2*h ≠ (M : ℤ) + (K : ℤ) + 3 - 2*m) :
    mixedPairing s M m u v a = 0 := by
  rw [mixedPairing_finite s M K m u v hv a]
  have huE := (actualGrade_eigen leechData leechUnit M u.val).mp hu
  have hvE := (actualGrade_eigen leechData leechUnit K v.val).mp hv
  apply mul_eq_zero.mpr
  right
  apply Finset.sum_eq_zero
  intro j _
  apply mul_eq_zero.mpr
  right
  apply Finset.sum_eq_zero
  intro ell _
  let n : ℤ := (M : ℤ) - m - (j : ℤ) + (ell : ℤ)
  let w := (lowering leechData leechUnit s ^ j) u
  let y := (J leechData leechUnit s n a w).val
  let E : ℤ := 2*h - (M : ℤ) + 2*m - 2*(ell : ℤ) - 3
  have hwE : actualTensorL0 leechData leechUnit w.val =
      ((leechData.rank : ℂ) / 16 + (((M : ℤ) - 2*(j : ℤ) : ℤ) : ℂ) / 2) • w.val := by
    simpa only [w, lowering_pow_val] using
      lowering_eigen leechData leechUnit (M : ℤ) u.val
        (by simpa only [Int.cast_natCast] using huE) j
  have hdegree : (M : ℤ) - 2*(j : ℤ) + (-2*n-3) + 2*h = E := by
    dsimp [n, E]
    omega
  have hyE : actualTensorL0 leechData leechUnit y =
      ((leechData.rank : ℂ) / 16 + (E : ℂ) / 2) • y := by
    simpa only [y, J_val, hdegree] using
      HalfFock.ActualEnergyCovariance.correctedField_signed_output leechData leechUnit h
        ((M : ℤ) - 2*(j : ℤ)) (-2*n-3) a.val ha w.val hwE
  have hzero : actualForm leechData leechUnit ((T leechData leechUnit ^ ell) v.val) y = 0 := by
    by_cases hneg : E < 0
    · rw [negative_eigen_zero leechData leechUnit E hneg y hyE, map_zero]
    · refine actualForm_oddGrade_orthogonal leechData leechUnit
        ((K : ℤ) - 2*(ell : ℤ)) E _ y ?_ hyE ?_
      · exact lowering_eigen leechData leechUnit (K : ℤ) v.val
          (by simpa only [Int.cast_natCast] using hvE) ell
      · dsimp [E]
        omega
  exact mul_eq_zero.mpr (Or.inr hzero)

/-- The full odd eigenspace at lattice energy `h`. -/
def oddGrade (h : ℤ) : Submodule ℂ (Carrier leechData) :=
  grade leechData h ⊓ minusSpace leechData

private def oddGradeInclusion (h : ℤ) : oddGrade h →ₗ[ℂ] OddCarrier leechData :=
  Submodule.inclusion (show oddGrade h ≤ minusSpace leechData from inf_le_right)

private theorem oddGrade_finiteDimensional (h : ℤ) : FiniteDimensional ℂ (oddGrade h) := by
  letI : FiniteDimensional ℂ (grade leechData h) :=
    grade_finiteDimensional leechData leech_spec.2.2.1 h
  exact FiniteDimensional.of_injective
    (Submodule.inclusion (show oddGrade h ≤ grade leechData h from inf_le_left))
    (Submodule.inclusion_injective _)

private theorem theta_gradeProjection (h : ℤ) (x : Carrier leechData) :
    theta leechData (gradeProjection leechData h x) =
      gradeProjection leechData h (theta leechData x) := by
  simpa only [SourceBPZ.ThetaReflectionAction.thetaRep_apply_one] using
    SourceBPZ.ThetaReflectionAction.thetaRep_gradeProjection_commute leechData h x

private def oddGradeProjection (h : ℤ) (a : OddCarrier leechData) : oddGrade h :=
  ⟨gradeProjection leechData h a.val, gradeProjection_mem leechData h a.val, by
    change gradeProjection leechData h a.val ∈ eigenspace leechData (-1)
    rw [mem_eigenspace, theta_gradeProjection,
      (mem_eigenspace leechData (-1) a.val).mp a.property, map_smul]⟩

private theorem sum_oddGradeProjections (a : OddCarrier leechData) :
    (∑ h ∈ stateEnergies leechData a.val,
      oddGradeInclusion h (oddGradeProjection h a)) = a := by
  apply Subtype.ext
  change (minusSpace leechData).subtype
    (∑ h ∈ stateEnergies leechData a.val, oddGradeInclusion h (oddGradeProjection h a)) = a.val
  rw [map_sum]
  exact sum_gradeProjections leechData a.val

private theorem minusPart_mem (a : Carrier leechData) :
    minusPart leechData a ∈ minusSpace leechData := by
  change minusPart leechData a ∈ eigenspace leechData (-1)
  rw [mem_eigenspace, neg_one_smul]
  have hi : theta leechData (theta leechData a) = a := theta_involutive leechData a
  simp only [minusPart, map_smul, map_sub, hi]
  rw [← smul_neg, neg_sub]

private theorem sourcePairing_minusPart_right (x a : Carrier leechData)
    (hx : x ∈ minusSpace leechData) :
    sourcePairing leechData x (minusPart leechData a) = sourcePairing leechData x a := by
  have htheta := sourcePairing_theta leechData x a
  rw [show theta leechData x = -x from by
    simpa only [neg_one_smul] using (mem_eigenspace leechData (-1) x).mp hx,
    map_neg, LinearMap.neg_apply] at htheta
  have hneg := neg_eq_iff_eq_neg.mp htheta
  rw [minusPart, map_smul, map_sub, hneg, sub_neg_eq_add, smul_eq_mul,
    ← two_mul, ← mul_assoc, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_mul]

private def oddGradeWitness (h : ℤ) (a : Carrier leechData) : oddGrade h := by
  let p : grade leechData h := ⟨gradeProjection leechData h a, gradeProjection_mem leechData h a⟩
  have hp :=
    SourceBPZ.ThetaReflectionAction.thetaRep_grade_plus_minus_decomposition leechData h p
  exact ⟨minusPart leechData p.val, hp.2.2.1, hp.2.2.2.2⟩

/-- The restriction of the original source pairing to the full odd grade. -/
def oddGradePairing (h : ℤ) : LinearMap.BilinForm ℂ (oddGrade h) :=
  (sourcePairing leechData).comp (oddGrade h).subtype (oddGrade h).subtype

/-- Every odd homogeneous state can be detected within its own grade by the
actual source pairing. Symmetry gives detection in both slots. -/
theorem oddGradePairing_nondegenerate (h : ℤ) : (oddGradePairing h).Nondegenerate := by
  have hleft (x : oddGrade h) (hx : ∀ y, oddGradePairing h x y = 0) : x = 0 := by
    apply Subtype.ext
    apply (sourcePairing_nondegenerate leechData leechUnit).1
    intro a
    calc
      sourcePairing leechData x.val a =
          sourcePairing leechData x.val (gradeProjection leechData h a) :=
        (left_grade_projection_pairing leechData (sourcePairing leechData)
          (fun m n u v hu hv hmn => sourcePairing_grade leechData m n hmn u v hu hv)
          h x.val x.property.1 a).symm
      _ = sourcePairing leechData x.val (oddGradeWitness h a).val :=
        (sourcePairing_minusPart_right x.val _ x.property.2).symm
      _ = 0 := hx (oddGradeWitness h a)
  refine ⟨hleft, fun y hy => hleft y fun x => ?_⟩
  exact (sourcePairing_symmetric leechData y.val x.val).trans (hy x)

private def oddGradeDualEquiv (h : ℤ) : oddGrade h ≃ₗ[ℂ] Module.Dual ℂ (oddGrade h) := by
  letI := oddGrade_finiteDimensional h
  exact (oddGradePairing h).toDual (oddGradePairing_nondegenerate h)

/-- The candidate integral lattice weight, obtained by Euclidean division.
The functional vanishes if the doubled weight is odd. -/
def mixedPairWeight (M K : ℕ) (m : ℤ) : ℤ := ((M : ℤ) + (K : ℤ) + 3 - 2*m) / 2

private def mixedPairStateInGrade (s : Bool) (M K : ℕ) (m : ℤ)
    (u : Twisted leechData leechUnit s) (v : Twisted leechData leechUnit (!s)) :
    oddGrade (mixedPairWeight M K m) :=
  (oddGradeDualEquiv (mixedPairWeight M K m)).symm
    ((mixedPairing s M m u v).comp (oddGradeInclusion (mixedPairWeight M K m)))

/-- The actual odd lattice state at physical exponent `-m-3/2` of the mixed
twisted-pair field for homogeneous inputs of doubled excitation grades `M`
and `K`. -/
def mixedPairState (s : Bool) (M K : ℕ) (m : ℤ)
    (u : Twisted leechData leechUnit s) (v : Twisted leechData leechUnit (!s)) :
    OddCarrier leechData :=
  oddGradeInclusion (mixedPairWeight M K m) (mixedPairStateInGrade s M K m u v)

theorem mixedPairState_grade (s : Bool) (M K : ℕ) (m : ℤ)
    (u : Twisted leechData leechUnit s) (v : Twisted leechData leechUnit (!s)) :
    (mixedPairState s M K m u v).val ∈ grade leechData (mixedPairWeight M K m) :=
  (mixedPairStateInGrade s M K m u v).property.1

private theorem mixedPairState_pairing_in_grade (s : Bool) (M K : ℕ) (m : ℤ)
    (u : Twisted leechData leechUnit s) (v : Twisted leechData leechUnit (!s))
    (a : oddGrade (mixedPairWeight M K m)) :
    sourcePairing leechData (mixedPairState s M K m u v).val a.val =
      mixedPairing s M m u v (oddGradeInclusion (mixedPairWeight M K m) a) := by
  let h := mixedPairWeight M K m
  letI := oddGrade_finiteDimensional h
  exact LinearMap.BilinForm.apply_toDual_symm_apply (B := oddGradePairing h)
    (hB := oddGradePairing_nondegenerate h)
    ((mixedPairing s M m u v).comp (oddGradeInclusion h)) a

/-- Evaluation against any odd source recovers the upper-branch mixed BPZ
functional, including for sources with several lattice grades. -/
theorem mixedPairState_pairing (s : Bool) (M K : ℕ) (m : ℤ)
    (u : Twisted leechData leechUnit s) (v : Twisted leechData leechUnit (!s))
    (hu : u.val ∈ actualGrade leechData leechUnit M)
    (hv : v.val ∈ actualGrade leechData leechUnit K) (a : OddCarrier leechData) :
    sourcePairing leechData (mixedPairState s M K m u v).val a.val =
      mixedPairing s M m u v a := by
  have heval (k : ℤ) (b : oddGrade k) :
      sourcePairing leechData (mixedPairState s M K m u v).val b.val =
        mixedPairing s M m u v (oddGradeInclusion k b) := by
    by_cases hk : k = mixedPairWeight M K m
    · subst k
      exact mixedPairState_pairing_in_grade s M K m u v b
    · have hne : 2*k ≠ (M : ℤ) + (K : ℤ) + 3 - 2*m := by
        intro he
        apply hk
        unfold mixedPairWeight
        omega
      exact (sourcePairing_grade leechData (mixedPairWeight M K m) k (Ne.symm hk) _ _
        (mixedPairState_grade s M K m u v) b.property.1).trans
        (mixedPairing_off_grade s M K m k u v hu hv (oddGradeInclusion k b)
          b.property.1 hne).symm
  let f := (sourcePairing leechData (mixedPairState s M K m u v).val).comp
    (minusSpace leechData).subtype
  change f a = mixedPairing s M m u v a
  rw [← sum_oddGradeProjections a]
  simp only [map_sum]
  exact Finset.sum_congr rfl (fun k _ => heval k (oddGradeProjection k a))

/-- The coefficient state is unique among all odd lattice states. -/
theorem existsUnique_mixedPairState (s : Bool) (M K : ℕ) (m : ℤ)
    (u : Twisted leechData leechUnit s) (v : Twisted leechData leechUnit (!s))
    (hu : u.val ∈ actualGrade leechData leechUnit M)
    (hv : v.val ∈ actualGrade leechData leechUnit K) :
    ∃! x : OddCarrier leechData, ∀ a : OddCarrier leechData,
      sourcePairing leechData x.val a.val = mixedPairing s M m u v a := by
  refine ⟨mixedPairState s M K m u v, mixedPairState_pairing s M K m u v hu hv, ?_⟩
  intro x hx
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply (sourcePairing_nondegenerate leechData leechUnit).1
  intro a
  let b : OddCarrier leechData := ⟨minusPart leechData a, minusPart_mem a⟩
  have he := (hx b).trans (mixedPairState_pairing s M K m u v hu hv b).symm
  rw [map_sub, LinearMap.sub_apply]
  exact sub_eq_zero.mpr ((sourcePairing_minusPart_right x.val a x.property).symm.trans
    (he.trans (sourcePairing_minusPart_right (mixedPairState s M K m u v).val a
      (mixedPairState s M K m u v).property)))

/-- If the signed doubled weight fails the integral grade condition, the
coefficient obtained from the restricted functional is zero. -/
theorem mixedPairState_nonintegral_zero (s : Bool) (M K : ℕ) (m : ℤ)
    (u : Twisted leechData leechUnit s) (v : Twisted leechData leechUnit (!s))
    (hu : u.val ∈ actualGrade leechData leechUnit M)
    (hv : v.val ∈ actualGrade leechData leechUnit K)
    (hne : 2 * mixedPairWeight M K m ≠ (M : ℤ) + (K : ℤ) + 3 - 2*m) :
    mixedPairState s M K m u v = 0 := by
  let h := mixedPairWeight M K m
  have hz : (mixedPairing s M m u v).comp (oddGradeInclusion h) = 0 := by
    apply LinearMap.ext
    intro a
    exact mixedPairing_off_grade s M K m h u v hu hv (oddGradeInclusion h a)
      a.property.1 hne
  change oddGradeInclusion h ((oddGradeDualEquiv h).symm
    ((mixedPairing s M m u v).comp (oddGradeInclusion h))) = 0
  rw [hz, map_zero, map_zero]

/-- The coefficient vanishes at negative lattice weight and at weight zero.
This gives homogeneous lower truncation in the physical exponent. -/
theorem mixedPairState_truncation (s : Bool) (M K : ℕ) (m : ℤ)
    (u : Twisted leechData leechUnit s) (v : Twisted leechData leechUnit (!s))
    (hnonpos : (M : ℤ) + (K : ℤ) + 3 - 2*m ≤ 0) :
    mixedPairState s M K m u v = 0 := by
  let a := (mixedPairState s M K m u v).val
  have ha : a ∈ grade leechData (mixedPairWeight M K m) := mixedPairState_grade s M K m u v
  have hwt : mixedPairWeight M K m ≤ 0 := by
    unfold mixedPairWeight
    omega
  apply Subtype.ext
  change a = 0
  rcases lt_or_eq_of_le hwt with hneg | hzero
  · rw [← sum_gradeProjections leechData a]
    apply Finset.sum_eq_zero
    intro k hk
    exact gradeProjection_zero_of_mem_grade_ne leechData k (mixedPairWeight M K m)
      (by have := stateEnergies_nonneg leech_spec.2.2.1 a k hk; omega) a ha
  · have hfixed : theta leechData a = a := by
      rw [hzero, grade_zero leechData leech_spec.2.2.1, Submodule.mem_span_singleton] at ha
      obtain ⟨c, hc⟩ := ha
      rw [← hc, map_smul, theta_vacuum]
    have hodd : theta leechData a = -a := by
      simpa only [neg_one_smul] using (mem_eigenspace leechData (-1) a).mp
        (mixedPairState s M K m u v).property
    have ha0 : (2 : ℂ) • a = 0 := by
      rw [two_smul]
      exact eq_neg_iff_add_eq_zero.mp (hfixed.symm.trans hodd)
    exact (smul_eq_zero.mp ha0).resolve_left (by norm_num)

/-- The two normalized mixed coefficients at physical exponent `-5/2`
give nonzero actual lattice states in weight one. -/
theorem leech_mixedPairState_normalization (i : Fin leechData.rank) :
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
      sourcePairing leechData (mixedPairState false 0 1 1 t bDual).val h.val = 1 ∧
      sourcePairing leechData (mixedPairState true 1 0 1 b tDual).val h.val = Complex.I ∧
      (mixedPairState false 0 1 1 t bDual).val ∈ grade leechData 1 ∧
      (mixedPairState true 1 0 1 b tDual).val ∈ grade leechData 1 ∧
      mixedPairState false 0 1 1 t bDual ≠ 0 ∧
      mixedPairState true 1 0 1 b tDual ≠ 0 := by
  dsimp only
  obtain ⟨c, hc, bDual, tDual, hbDual, htDual, hbd, htd, hret, hp, hm⟩ :=
    leech_mixed_pairing_normalization i
  let t := leechGroundVector
  let h := c • oddCurrent leechData i
  let b := Jplus (-1) h t
  have ht : t.val ∈ actualGrade leechData leechUnit 0 := groundBasis_energy
  have ha : h.val ∈ grade leechData 1 :=
    (grade leechData 1).smul_mem c (oddCurrent_grade_one leechData i)
  have hb : b.val ∈ actualGrade leechData leechUnit 1 :=
    J_grade leechData leechUnit false (-1) 1 0 1 h t ha ht (by norm_num)
  have hp' := (mixedPairState_pairing false 0 1 1 t bDual ht hbDual h).trans hp
  have hm' := (mixedPairState_pairing true 1 0 1 b tDual hb htDual h).trans hm
  refine ⟨c, hc, bDual, tDual, hbDual, htDual, hbd, htd, hret, hp', hm', ?_, ?_, ?_, ?_⟩
  · simpa only [show mixedPairWeight 0 1 1 = 1 by decide] using
      mixedPairState_grade false 0 1 1 t bDual
  · simpa only [show mixedPairWeight 1 0 1 = 1 by decide] using
      mixedPairState_grade true 1 0 1 b tDual
  · intro hz
    change mixedPairState false 0 1 1 t bDual = 0 at hz
    rw [hz] at hp'
    exact zero_ne_one (by simpa only [Submodule.coe_zero, map_zero, LinearMap.zero_apply] using hp')
  · intro hz
    change mixedPairState true 1 0 1 b tDual = 0 at hz
    rw [hz] at hm'
    exact Complex.I_ne_zero (by
      simpa only [Submodule.coe_zero, map_zero, LinearMap.zero_apply] using hm'.symm)

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairState
