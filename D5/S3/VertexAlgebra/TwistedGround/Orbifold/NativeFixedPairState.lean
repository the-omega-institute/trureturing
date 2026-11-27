/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeFixedPairState
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeFixedPairState
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Upper-branch same-parity Leech twisted-pair coefficients in the fixed lattice carrier. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalMixedBPZ
import D5.S3.VertexAlgebra.Lattice.FixedGradedDuality
import D5.S3.VertexAlgebra.SourceBPZ.ThetaReflectionAction
import Batteries.Tactic.OpenPrivate

/-!
Huang, hep-th/9406190v7, §3.4, pp. 22–23. For first input of weight
`(3+M)/2`, the upper branch of the inversion contributes
`I^(-(3+M)) z^(-(3+M))`. The two lowering exponentials supply
`z^j / j!` and `z^(-ell) / ell!`. The TT term of physical degree `t`
at the inverted upper-branch argument supplies `(-1)^t z^(-t)`.
Thus `j - ell - (3+M) - t = -m-1`, so
`t = m+j-ell-M-2`. The upper-branch sign can be written as `(-1)^(-t)`
and the actual field reads the doubled exponent `2*t`. The test slot
of the original right kernel is the first argument of the actual form.

The twisted Virasoro operator `L(1)` lowers doubled excitation by two.
The positive-energy bound in `MixedIntertwiner.lowering_killed` kills
orders beyond `M/2` and `K/2`, respectively. On the original negative
parity sector, integral weight `H` means `M = 2*H-3`. The inversion phase
then equals `(-1)^H`, and the two signs combine to the
`(-1)^(H+t)` of `MixedIntertwiner.normalizedCoefficient_pairing`.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeFixedPairState

open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeInvolution FixedGradedDuality
open LatticeAllStateField (vacuum)
open LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockGradedTrace LatticeHalfFockParityT
open HalfFock.LatticeHalfFockParityField
open ActualLeechHyperbolic (leechData leech_spec)
open NativeOddTwistedIntertwiner (Twisted TwistedEven TwistedOdd leechUnit)
open ActualChargedAdjoint (actualForm)
open ActualOddGradeOrthogonality (actualForm_oddGrade_orthogonal)
open CorrectedInversion (K_R)
open OriginalFourMChargeCoset (originalI)
open SourceBPZ.OriginalSourcePairing
  (sourcePairing sourcePairing_nondegenerate sourcePairing_vacuum)
open SourceBPZ.SourcePairingLaws (sourcePairing_theta sourcePairing_grade)
open private T kernel lowering_eigen from
  D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private originalI_pairing_kernel from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalMixedBPZ
open private phase_even_shift from
  D5.S3.VertexAlgebra.TwistedGround.MixedJacobiCommonCube
open private pairing_plusPart_right_of_fixed_left from
  D5.S3.VertexAlgebra.Lattice.FixedGradedDuality
open private vacuum_coeff from
  D5.S3.VertexAlgebra.LatticeHalfFockCurrentBorcherds

local notation "ℒ" => leechData

/-- The actual fixed-source linear functional of the coefficient at physical
exponent `-m-1` on two twisted inputs of the same oscillator parity. -/
def fixedPairing (s : Bool) (M K : ℕ) (m : ℤ) (u v : Twisted ℒ leechUnit s) :
    Module.Dual ℂ (FixedCarrier ℒ) :=
  Complex.I ^ (-(3 + (M : ℤ))) •
    ∑ j ∈ Finset.range (M / 2 + 1), ∑ ell ∈ Finset.range (K / 2 + 1),
      (((-1 : ℂ) ^ ((M : ℤ) - m - (j : ℤ) + (ell : ℤ) + 2)) /
          ((j.factorial : ℂ) * (ell.factorial : ℂ))) •
        (K_R ℒ leechUnit (2 * (m + (j : ℤ) - (ell : ℤ) - (M : ℤ) - 2))
          ((T ℒ leechUnit ^ ell) v.val) ((T ℒ leechUnit ^ j) u.val)).comp
            (fixedSpace ℒ).subtype

/-- Evaluation on a fixed source uses the original TT field and the original
twisted bilinear form with the test vector in its first slot. -/
theorem fixedPairing_apply (s : Bool) (M K : ℕ) (m : ℤ)
    (u v : Twisted ℒ leechUnit s) (a : FixedCarrier ℒ) :
    fixedPairing s M K m u v a =
      Complex.I ^ (-(3 + (M : ℤ))) *
        ∑ j ∈ Finset.range (M / 2 + 1), ∑ ell ∈ Finset.range (K / 2 + 1),
          (((-1 : ℂ) ^ ((M : ℤ) - m - (j : ℤ) + (ell : ℤ) + 2)) /
              ((j.factorial : ℂ) * (ell.factorial : ℂ))) *
            actualForm ℒ leechUnit ((T ℒ leechUnit ^ ell) v.val)
              ((correctedField ℒ leechUnit a.val).coeff
                (2 * (m + (j : ℤ) - (ell : ℤ) - (M : ℤ) - 2))
                ((T ℒ leechUnit ^ j) u.val)) := by
  simp only [fixedPairing, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    Submodule.subtype_apply, smul_eq_mul, K_R, LinearMap.coe_mk, AddHom.coe_mk]

private theorem excitation_eigen {N : ℕ} {x : ActualTensor ℒ leechUnit}
    (hx : x ∈ actualGrade ℒ leechUnit N) :
    actualTensorL0 ℒ leechUnit x =
      ((leechData.rank : ℂ) / 16 + ((N : ℤ) : ℂ) / 2) • x := by
  simpa only [actualGrade, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero, Int.cast_natCast] using hx

/-- The sum is supported at doubled fixed-source weight `M+K+4-2*m`. -/
theorem fixedPairing_off_grade (s : Bool) (M K : ℕ) (m h : ℤ)
    (u v : Twisted ℒ leechUnit s)
    (hu : u.val ∈ actualGrade ℒ leechUnit M)
    (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (a : FixedCarrier ℒ) (ha : a.val ∈ grade ℒ h)
    (hne : 2 * h ≠ (M : ℤ) + (K : ℤ) + 4 - 2 * m) :
    fixedPairing s M K m u v a = 0 := by
  rw [fixedPairing_apply]
  apply mul_eq_zero.mpr
  right
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro ell _
  let e : ℤ := 2 * (m + (j : ℤ) - (ell : ℤ) - (M : ℤ) - 2)
  have hx := lowering_eigen ℒ leechUnit (K : ℤ) v.val (excitation_eigen hv) ell
  have hy := HalfFock.ActualEnergyCovariance.correctedField_signed_output ℒ leechUnit
    h ((M : ℤ) - 2 * (j : ℤ)) e a.val ha ((T ℒ leechUnit ^ j) u.val)
    (lowering_eigen ℒ leechUnit (M : ℤ) u.val (excitation_eigen hu) j)
  have hz := actualForm_oddGrade_orthogonal ℒ leechUnit
    ((K : ℤ) - 2 * (ell : ℤ)) ((M : ℤ) - 2 * (j : ℤ) + e + 2 * h)
    ((T ℒ leechUnit ^ ell) v.val)
    ((correctedField ℒ leechUnit a.val).coeff e ((T ℒ leechUnit ^ j) u.val))
    hx hy (by dsimp [e]; omega)
  exact mul_eq_zero.mpr (Or.inr hz)

private theorem theta_gradeProjection (h : ℤ) (a : Carrier ℒ) :
    theta ℒ (gradeProjection ℒ h a) = gradeProjection ℒ h (theta ℒ a) := by
  simpa only [SourceBPZ.ThetaReflectionAction.thetaRep_apply_one] using
    SourceBPZ.ThetaReflectionAction.thetaRep_gradeProjection_commute ℒ h a

private theorem source_grade_orthogonal (h k : ℤ) (x y : Carrier ℒ)
    (hx : x ∈ grade ℒ h) (hy : y ∈ grade ℒ k) (hne : h ≠ k) :
    sourcePairing ℒ x y = 0 :=
  sourcePairing_grade ℒ h k hne x y hx hy

private abbrev leechFixedGradeDual (h : ℤ) :=
  fixedGradeDualEquiv ℒ (sourcePairing ℒ) (sourcePairing_nondegenerate ℒ leechUnit)
    theta_gradeProjection (sourcePairing_theta ℒ) source_grade_orthogonal leech_spec.2.2.1 h

/-- The candidate integral fixed-source weight. The state vanishes when the
doubled weight is odd. -/
def fixedPairWeight (M K : ℕ) (m : ℤ) : ℤ := ((M : ℤ) + (K : ℤ) + 4 - 2 * m) / 2

private def fixedPairStateInGrade (s : Bool) (M K : ℕ) (m : ℤ)
    (u v : Twisted ℒ leechUnit s) : FixedGrade ℒ (fixedPairWeight M K m) :=
  (leechFixedGradeDual (fixedPairWeight M K m)).symm
    ((fixedPairing s M K m u v).comp (fixedGradeSubmodule ℒ (fixedPairWeight M K m)).subtype)

/-- The same-parity coefficient as a state in the whole actual fixed carrier. -/
def fixedPairState (s : Bool) (M K : ℕ) (m : ℤ) (u v : Twisted ℒ leechUnit s) :
    FixedCarrier ℒ :=
  (fixedPairStateInGrade s M K m u v).val

theorem fixedPairState_grade (s : Bool) (M K : ℕ) (m : ℤ) (u v : Twisted ℒ leechUnit s) :
    (fixedPairState s M K m u v).val ∈ grade ℒ (fixedPairWeight M K m) :=
  (fixedPairStateInGrade s M K m u v).property

/-- Evaluation against every fixed source recovers the finite TT pairing,
including for inhomogeneous lattice tests. -/
theorem fixedPairState_pairing (s : Bool) (M K : ℕ) (m : ℤ)
    (u v : Twisted ℒ leechUnit s)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (a : FixedCarrier ℒ) :
    sourcePairing ℒ (fixedPairState s M K m u v).val a.val = fixedPairing s M K m u v a := by
  let h := fixedPairWeight M K m
  have heval (k : ℤ) (b : FixedGrade ℒ k) :
      sourcePairing ℒ (fixedPairState s M K m u v).val (fixedGradeToCarrier ℒ k b) =
        fixedPairing s M K m u v ((fixedGradeSubmodule ℒ k).subtype b) := by
    by_cases hk : k = h
    · subst k
      exact fixedGradeDualEquiv_ambient_evaluation ℒ (sourcePairing ℒ)
        (sourcePairing_nondegenerate ℒ leechUnit) theta_gradeProjection
        (sourcePairing_theta ℒ) source_grade_orthogonal leech_spec.2.2.1 h
        ((fixedPairing s M K m u v).comp (fixedGradeSubmodule ℒ h).subtype) b
    · have hne : 2 * k ≠ (M : ℤ) + (K : ℤ) + 4 - 2 * m := by
        intro he
        apply hk
        dsimp [h, fixedPairWeight]
        omega
      exact (sourcePairing_grade ℒ h k (Ne.symm hk) _ _
        (fixedPairState_grade s M K m u v) b.property).trans
        (fixedPairing_off_grade s M K m k u v hu hv
          ((fixedGradeSubmodule ℒ k).subtype b) b.property hne).symm
  let f : Module.Dual ℂ (FixedCarrier ℒ) :=
    (sourcePairing ℒ (fixedPairState s M K m u v).val).comp (fixedSpace ℒ).subtype
  change f a = fixedPairing s M K m u v a
  rw [← fixedGradeProjection_sum ℒ theta_gradeProjection a]
  simp only [map_sum]
  exact Finset.sum_congr rfl (fun k _ => heval k (fixedGradeProjection ℒ theta_gradeProjection k a))

private theorem fixed_source_ext {x y : FixedCarrier ℒ}
    (h : ∀ a : FixedCarrier ℒ, sourcePairing ℒ x.val a.val = sourcePairing ℒ y.val a.val) :
    x = y := by
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply (sourcePairing_nondegenerate ℒ leechUnit).1
  intro a
  let b : FixedCarrier ℒ := ⟨plusPart ℒ a, plusPart_mem_fixedSpace ℒ a⟩
  have hx := pairing_plusPart_right_of_fixed_left ℒ (sourcePairing ℒ)
    (sourcePairing_theta ℒ) x.val x.property a
  have hy := pairing_plusPart_right_of_fixed_left ℒ (sourcePairing ℒ)
    (sourcePairing_theta ℒ) y.val y.property a
  rw [map_sub, LinearMap.sub_apply]
  exact sub_eq_zero.mpr (hx.symm.trans ((h b).trans hy))

/-- The coefficient is unique in the entire fixed carrier under the actual
source pairing. -/
theorem existsUnique_fixedPairState (s : Bool) (M K : ℕ) (m : ℤ)
    (u v : Twisted ℒ leechUnit s)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K) :
    ∃! x : FixedCarrier ℒ, ∀ a : FixedCarrier ℒ,
      sourcePairing ℒ x.val a.val = fixedPairing s M K m u v a := by
  refine ⟨fixedPairState s M K m u v, fixedPairState_pairing s M K m u v hu hv, ?_⟩
  intro x hx
  apply fixed_source_ext
  intro a
  exact (hx a).trans (fixedPairState_pairing s M K m u v hu hv a).symm

/-- A nonintegral candidate lattice weight gives a zero coefficient. -/
theorem fixedPairState_nonintegral_zero (s : Bool) (M K : ℕ) (m : ℤ)
    (u v : Twisted ℒ leechUnit s)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (hne : 2 * fixedPairWeight M K m ≠ (M : ℤ) + (K : ℤ) + 4 - 2 * m) :
    fixedPairState s M K m u v = 0 := by
  let h := fixedPairWeight M K m
  have hz : (fixedPairing s M K m u v).comp (fixedGradeSubmodule ℒ h).subtype = 0 := by
    apply LinearMap.ext
    intro a
    exact fixedPairing_off_grade s M K m h u v hu hv
      ((fixedGradeSubmodule ℒ h).subtype a) a.property hne
  have hstate : fixedPairStateInGrade s M K m u v = 0 := by
    change (leechFixedGradeDual h).symm
      ((fixedPairing s M K m u v).comp (fixedGradeSubmodule ℒ h).subtype) = 0
    rw [hz, map_zero]
  exact congrArg Subtype.val hstate

/-- Negative output weight gives a zero coefficient by positive lattice
energy, yielding homogeneous lower truncation. -/
theorem fixedPairState_truncation (s : Bool) (M K : ℕ) (m : ℤ)
    (u v : Twisted ℒ leechUnit s) (hneg : (M : ℤ) + (K : ℤ) + 4 - 2 * m < 0) :
    fixedPairState s M K m u v = 0 := by
  let a := (fixedPairState s M K m u v).val
  have ha := fixedPairState_grade s M K m u v
  have hw : fixedPairWeight M K m < 0 := by
    unfold fixedPairWeight
    omega
  apply Subtype.ext
  change a = 0
  rw [← sum_gradeProjections ℒ a]
  apply Finset.sum_eq_zero
  intro k hk
  exact gradeProjection_zero_of_mem_grade_ne ℒ k (fixedPairWeight M K m)
    (by have := stateEnergies_nonneg leech_spec.2.2.1 a k hk; omega) a ha

private theorem I_zpow_two : Complex.I ^ (2 : ℤ) = -1 :=
  (zpow_natCast Complex.I 2).trans Complex.I_sq

/-- A coefficient in weight zero is its vacuum evaluation times the actual
fixed vacuum. -/
theorem fixedPairState_zero_weight (s : Bool) (M K : ℕ) (m : ℤ)
    (u v : Twisted ℒ leechUnit s)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (h : fixedPairWeight M K m = 0) :
    fixedPairState s M K m u v =
      fixedPairing s M K m u v (fixedVacuum ℒ) • fixedVacuum ℒ := by
  let x := fixedPairState s M K m u v
  have hx : x.val ∈ grade ℒ 0 := h ▸ fixedPairState_grade s M K m u v
  rw [grade_zero ℒ leech_spec.2.2.1] at hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
  have hp := fixedPairState_pairing s M K m u v hu hv (fixedVacuum ℒ)
  change sourcePairing ℒ x.val (vacuum ℒ) = _ at hp
  rw [← hc, map_smul, LinearMap.smul_apply, sourcePairing_vacuum, smul_eq_mul, mul_one] at hp
  apply Subtype.ext
  change x.val = fixedPairing s M K m u v (fixedVacuum ℒ) • vacuum ℒ
  rw [← hp, hc]

/-- On the two actual half-integral twisted ground vectors the weight-zero
coefficient at mode two is `I` times the ordered original form, times the
original fixed vacuum. -/
theorem fixedPairState_ground (u v : TwistedEven)
    (hu : u.val ∈ actualGrade ℒ leechUnit 0) (hv : v.val ∈ actualGrade ℒ leechUnit 0) :
    fixedPairState false 0 0 2 u v =
      (Complex.I * actualForm ℒ leechUnit v.val u.val) • fixedVacuum ℒ := by
  have hI4 : Complex.I ^ (4 : ℤ) = 1 := by
    rw [show (4 : ℤ) = 2 * 2 by decide, zpow_mul, I_zpow_two]
    norm_num
  have hI : Complex.I ^ (-3 : ℤ) = Complex.I := by
    rw [show (-3 : ℤ) = 1 + -(4 : ℤ) by decide, zpow_add₀ Complex.I_ne_zero,
      zpow_one, zpow_neg, hI4, inv_one, mul_one]
  have hnormalized : fixedPairing false 0 0 2 u v (fixedVacuum ℒ) =
      Complex.I * actualForm ℒ leechUnit v.val u.val := by
    simp only [fixedPairing_apply, Nat.zero_div, zero_add, Finset.sum_range_one,
      pow_zero, Module.End.one_apply, Nat.factorial_zero, Nat.cast_one]
    change Complex.I ^ (-3 : ℤ) * (((-1 : ℂ) ^ (0 : ℤ) / (1 * 1)) *
      actualForm ℒ leechUnit v.val ((correctedField ℒ leechUnit (vacuum ℒ)).coeff 0 u.val)) = _
    rw [hI, vacuum_coeff]
    norm_num
  rw [fixedPairState_zero_weight false 0 0 2 u v hu hv (by decide), hnormalized]

private theorem odd_excitation {N : ℕ} {u : TwistedOdd} (hu0 : u ≠ 0)
    (hu : u.val ∈ actualGrade ℒ leechUnit N) : N % 2 = 1 := by
  have hn := u.property
  change u.val ∈ paritySpace ℒ leechUnit (-1) at hn
  have hneg : actualParity ℒ leechUnit u.val = -u.val := by
    simpa only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, LinearMap.neg_apply, sub_eq_zero, neg_one_smul] using hn
  by_contra h
  have hmod : N % 2 = 0 := by omega
  have hpos := actualParity_on_actualGrade ℒ leechUnit N ⟨u.val, hu⟩
  change actualParity ℒ leechUnit u.val = ((-1 : ℂ) ^ N) • u.val at hpos
  rw [neg_one_pow_eq_pow_mod_two, hmod, pow_zero, one_smul] at hpos
  have hz : (2 : ℂ) • u.val = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp (hpos.symm.trans hneg)
  exact hu0 (Subtype.ext ((smul_eq_zero.mp hz).resolve_left (by norm_num)))

private theorem integer_energy {N H : ℕ} {u : ActualTensor ℒ leechUnit}
    (hu : u ∈ actualGrade ℒ leechUnit N) (hN : (N : ℤ) + 3 = 2 * (H : ℤ)) :
    actualTensorL0 ℒ leechUnit u = (H : ℂ) • u := by
  have hcast : (N : ℂ) + 3 = 2 * (H : ℂ) := by exact_mod_cast hN
  have hrank : (leechData.rank : ℂ) = 24 := by exact_mod_cast leech_spec.1
  have hscalar : (leechData.rank : ℂ) / 16 + ((N : ℤ) : ℂ) / 2 = (H : ℂ) := by
    rw [hrank, Int.cast_natCast]
    linear_combination (1 / 2 : ℂ) * hcast
  rw [excitation_eigen hu, hscalar]

/-- For arbitrary homogeneous inputs in the original negative twisted sector,
the new coefficient is exactly the original orbifold coefficient. -/
theorem fixedPairState_eq_originalI (M K : ℕ) (m : ℤ) (u v : TwistedOdd)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K) :
    fixedPairState true M K m u v = originalI ℒ leechUnit leech_spec.2.2.1 m u v := by
  apply fixed_source_ext
  intro a
  rw [fixedPairState_pairing true M K m u v hu hv a]
  by_cases hu0 : u = 0
  · subst u
    simp [fixedPairing_apply]
  by_cases hv0 : v = 0
  · subst v
    simp [fixedPairing_apply]
  have hModM := odd_excitation hu0 hu
  have hModK := odd_excitation hv0 hv
  let H := (M + 3) / 2
  let W := (K + 3) / 2
  have hM : (M : ℤ) + 3 = 2 * (H : ℤ) := by dsimp [H]; omega
  have hK : (K : ℤ) + 3 = 2 * (W : ℤ) := by dsimp [W]; omega
  have hMrange : M / 2 + 1 = H - 1 := by omega
  have hKrange : K / 2 + 1 = W - 1 := by omega
  have hI : Complex.I ^ (-(3 + (M : ℤ))) = (-1 : ℂ) ^ (H : ℤ) := by
    rw [show -(3 + (M : ℤ)) = 2 * (-(H : ℤ)) by omega, zpow_mul, I_zpow_two,
      show -(H : ℤ) = (H : ℤ) + 2 * (-(H : ℤ)) by ring, phase_even_shift]
  rw [originalI_pairing_kernel ℒ leechUnit leech_spec.2.2.1 leech_spec.1 H W m u v
    (integer_energy hu hM) (integer_energy hv hK) a, fixedPairing_apply]
  simp only [kernel, K_R, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
  rw [hMrange, hKrange, hI, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ell _
  let t : ℤ := m + 1 - (ell : ℤ) - 2 * (H : ℤ) + (j : ℤ)
  have he : 2 * (m + (j : ℤ) - (ell : ℤ) - (M : ℤ) - 2) = 2 * t := by
    dsimp [t]
    omega
  have hbranch : (-1 : ℂ) ^ ((M : ℤ) - m - (j : ℤ) + (ell : ℤ) + 2) =
      (-1 : ℂ) ^ t := by
    rw [show (M : ℤ) - m - (j : ℤ) + (ell : ℤ) + 2 = t + 2 * (-t) by
      dsimp [t]; omega, phase_even_shift]
  rw [he, hbranch, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0) (H : ℤ) t]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeFixedPairState
