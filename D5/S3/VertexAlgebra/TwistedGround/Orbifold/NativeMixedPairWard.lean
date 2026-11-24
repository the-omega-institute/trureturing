/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeMixedPairWard
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeMixedPairWard
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original lattice mode-one Ward identity for the actual mixed Leech pair. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairField
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalSkewAdjoints

/-!
Testing the actual mixed pair against the translated odd lattice detector
produces the sum of two finite lowering contributions and the shifted
coefficient. The signs of the lowering contributions come from the
upper-branch phase and the factorial reindexing.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairWard

open ActualLeechHyperbolic (leechData)
open LatticeGeneratingFieldLocality LatticeInvolution
open LatticeAllStateField (vacuum)
open LatticeHalfFockCorrectedField LatticeHalfFockGradedTrace
open ActualChargedAdjoint (actualForm)
open LatticeSugawaraCurrents (sugawaraMode gramComplex)
open NativeOddTwistedIntertwiner (Twisted OddCarrier leechUnit oddTranslation)
open NativeOddUpperRightSkew (lowering mixedPairing_finite mixedPairing_lowering_tail)
open NativeMixedPairState (mixedPairState_pairing)
open NativeMixedPairField (mu mu_coeff_of_grade mu_coeff_even_zero)
open SourceBPZ.OriginalSourcePairing
  (sourcePairing sourcePairing_symmetric sourcePairing_nondegenerate)
open OriginalSkewAdjoints (sourcePairing_translation)

open private J_val from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
open private lowering_pow_val actualGrade_eigen from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddUpperRightSkew
open private T lowering_eigen from
  D5.S3.VertexAlgebra.TwistedGround.MixedIntertwiner
open private minusPart_mem sourcePairing_minusPart_right from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairState

private abbrev LeechTwisted (s : Bool) := Twisted leechData leechUnit s
private abbrev LeechOdd := OddCarrier leechData
local notation "P" => sourcePairing leechData

private def modeExponent (k : ℤ) : ℤ := -2*k-3

private def fieldExponent (M : ℕ) (k : ℤ) : ℤ := -2*(M : ℤ) + 2*k - 3

private def phase (M : ℕ) (k : ℤ) : ℂ :=
  Complex.I ^ (-(3 + (M : ℤ)) + fieldExponent M k)

private def signedFactorial (q : ℕ) : ℂ := (-1 : ℂ)^q * (q.factorial : ℂ)⁻¹

private def matrixEntry (s : Bool) (b : ℤ) (u : LeechTwisted s) (v : LeechTwisted (!s)) (a : LeechOdd)
    (q ell : ℕ) : ℂ :=
  actualForm leechData leechUnit ((lowering leechData leechUnit (!s) ^ ell) v).val
    ((correctedField leechData leechUnit a.val).coeff (b + 2*(q : ℤ) - 2*(ell : ℤ))
      ((lowering leechData leechUnit s ^ q) u).val)

private def matrixTerm (s : Bool) (b : ℤ) (u : LeechTwisted s) (v : LeechTwisted (!s)) (a : LeechOdd)
    (q ell : ℕ) : ℂ :=
  (signedFactorial q * signedFactorial ell) * matrixEntry s b u v a q ell

private def rectangle (Q E : ℕ) (f : ℕ → ℕ → ℂ) : ℂ :=
  ∑ q ∈ Finset.range Q, ∑ ell ∈ Finset.range E, f q ell

private def pairCoeff (s : Bool) (k : ℤ) (u : LeechTwisted s) (v : LeechTwisted (!s)) (a : LeechOdd) : ℂ :=
  P ((mu s u).coeff (modeExponent k) v).val a.val

private theorem i_pow_two : Complex.I ^ (2 : ℤ) = -1 :=
  (zpow_natCast Complex.I 2).trans Complex.I_sq

private theorem i_pow_neg_two : Complex.I ^ (-2 : ℤ) = -1 := by
  rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) by decide, zpow_neg, zpow_natCast,
    Complex.I_sq, inv_neg, inv_one]

private theorem phase_mode_succ (M : ℕ) (k : ℤ) : phase M (k+1) = -phase M k := by
  unfold phase fieldExponent
  rw [show -(3 + (M : ℤ)) + (-2*(M : ℤ) + 2*(k+1) - 3) =
      (-(3 + (M : ℤ)) + (-2*(M : ℤ) + 2*k - 3)) + 2 by omega,
    zpow_add₀ Complex.I_ne_zero, i_pow_two, mul_neg_one]

private theorem phase_lower_left (M : ℕ) (k : ℤ) (hM : 2 ≤ M) :
    phase (M-2) k = -phase M k := by
  have hSix : Complex.I ^ (6 : ℤ) = -1 := by
    rw [show (6 : ℤ) = 2*3 by decide, zpow_mul, i_pow_two]
    norm_num
  unfold phase fieldExponent
  rw [show -(3 + ((M-2 : ℕ) : ℤ)) + (-2*((M-2 : ℕ) : ℤ) + 2*k - 3) =
      (-(3 + (M : ℤ)) + (-2*(M : ℤ) + 2*k - 3)) + 6 by omega,
    zpow_add₀ Complex.I_ne_zero, hSix, mul_neg_one]

private theorem fieldExponent_succ (M : ℕ) (k : ℤ) :
    fieldExponent M (k+1) = fieldExponent M k + 2 := by
  unfold fieldExponent
  omega

private theorem fieldExponent_lower_left (M : ℕ) (k : ℤ) (hM : 2 ≤ M) :
    fieldExponent (M-2) k = fieldExponent M (k+1) + 2 := by
  unfold fieldExponent
  omega

private theorem coefficient_phase (M : ℕ) (k : ℤ) (q ell : ℕ) :
    Complex.I ^ (-(3 + (M : ℤ))) *
      Complex.I ^ (-2*((M : ℤ) - k - (q : ℤ) + (ell : ℤ))-3) =
      phase M k * ((-1 : ℂ)^q * (-1 : ℂ)^ell) := by
  have h : -2*((M : ℤ) - k - (q : ℤ) + (ell : ℤ))-3 =
      fieldExponent M k + 2*(q : ℤ) + (-2)*(ell : ℤ) := by
    unfold fieldExponent
    omega
  rw [h, zpow_add₀ Complex.I_ne_zero, zpow_add₀ Complex.I_ne_zero,
    zpow_mul Complex.I 2, zpow_mul Complex.I (-2), i_pow_two, i_pow_neg_two,
    phase, zpow_add₀ Complex.I_ne_zero]
  simp only [zpow_natCast]
  ring

private theorem pairCoeff_finite (s : Bool) (M K : ℕ) (k : ℤ)
    (u : LeechTwisted s) (v : LeechTwisted (!s))
    (hu : u.val ∈ actualGrade leechData leechUnit M)
    (hv : v.val ∈ actualGrade leechData leechUnit K) (a : LeechOdd) :
    pairCoeff s k u v a =
      phase M k * rectangle (M/2+1) (K/2+1) (matrixTerm s (fieldExponent M k) u v a) := by
  unfold pairCoeff modeExponent
  rw [mu_coeff_of_grade s M K k u v hu hv, mixedPairState_pairing s M K k u v hu hv,
    mixedPairing_finite s M K k u v hv a]
  unfold rectangle
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro ell _
  have he : -2*((M : ℤ) - k - (q : ℤ) + (ell : ℤ))-3 =
      fieldExponent M k + 2*(q : ℤ) - 2*(ell : ℤ) := by
    unfold fieldExponent
    omega
  have hscalar (w : ℂ) :
      Complex.I ^ (-(3 + (M : ℤ))) *
        ((q.factorial : ℂ)⁻¹ *
          ((Complex.I ^ (fieldExponent M k + 2*(q : ℤ) - 2*(ell : ℤ)) *
            (ell.factorial : ℂ)⁻¹) * w)) =
        phase M k * ((signedFactorial q * signedFactorial ell) * w) := by
    have hp := coefficient_phase M k q ell
    rw [he] at hp
    calc
      _ = (Complex.I ^ (-(3 + (M : ℤ))) *
            Complex.I ^ (fieldExponent M k + 2*(q : ℤ) - 2*(ell : ℤ))) *
          ((q.factorial : ℂ)⁻¹ * (ell.factorial : ℂ)⁻¹) * w := by ring
      _ = _ := by
        rw [hp]
        unfold signedFactorial
        ring
  simp only [matrixTerm, matrixEntry, J_val, he, lowering_pow_val]
  exact hscalar _

private theorem lowering_grade (s : Bool) (M : ℕ) (u : LeechTwisted s)
    (hu : u.val ∈ actualGrade leechData leechUnit M) (hM : 2 ≤ M) :
    (lowering leechData leechUnit s u).val ∈ actualGrade leechData leechUnit (M-2) := by
  apply (actualGrade_eigen leechData leechUnit (M-2) _).mpr
  have h := lowering_eigen leechData leechUnit (M : ℤ) u.val
    (by simpa only [Int.cast_natCast] using
      (actualGrade_eigen leechData leechUnit M u.val).mp hu) 1
  have hcast : (M : ℤ) - 2*((1 : ℕ) : ℤ) = ((M-2 : ℕ) : ℤ) := by omega
  rw [hcast, Int.cast_natCast, pow_one] at h
  have hval := lowering_pow_val leechData leechUnit s 1 u
  simp only [pow_one] at hval
  simpa only [hval] using h

private theorem lowering_small (s : Bool) (M : ℕ) (u : LeechTwisted s)
    (hu : u.val ∈ actualGrade leechData leechUnit M) (hM : M < 2) :
    lowering leechData leechUnit s u = 0 := by
  simpa only [pow_one] using mixedPairing_lowering_tail s M u hu 1 (by omega)

private theorem signedFactorial_succ (q : ℕ) :
    ((q+1 : ℕ) : ℂ) * signedFactorial (q+1) = -signedFactorial q := by
  have hq : ((q+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero q
  unfold signedFactorial
  rw [Nat.factorial_succ, Nat.cast_mul, mul_inv_rev, pow_succ]
  calc
    _ = (((q+1 : ℕ) : ℂ) * (((q+1 : ℕ) : ℂ)⁻¹)) *
        -((-1 : ℂ)^q * (q.factorial : ℂ)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hq, one_mul]

private theorem matrixTerm_lower_left (s : Bool) (b : ℤ) (u : LeechTwisted s) (v : LeechTwisted (!s))
    (a : LeechOdd) (q ell : ℕ) :
    matrixTerm s (b+2) (lowering leechData leechUnit s u) v a q ell =
      -(((q+1 : ℕ) : ℂ) * matrixTerm s b u v a (q+1) ell) := by
  have hentry : matrixEntry s (b+2) (lowering leechData leechUnit s u) v a q ell =
      matrixEntry s b u v a (q+1) ell := by
    have he : b+2 + 2*(q : ℤ) - 2*(ell : ℤ) =
        b + 2*((q+1 : ℕ) : ℤ) - 2*(ell : ℤ) := by omega
    unfold matrixEntry
    rw [he, pow_succ (lowering leechData leechUnit s) q, Module.End.mul_apply]
  simp only [matrixTerm, hentry]
  calc
    _ = -(((q+1 : ℕ) : ℂ) * signedFactorial (q+1)) *
        signedFactorial ell * matrixEntry s b u v a (q+1) ell := by
      rw [signedFactorial_succ, neg_neg]
    _ = _ := by ring

private theorem matrixTerm_lower_right (s : Bool) (b : ℤ) (u : LeechTwisted s) (v : LeechTwisted (!s))
    (a : LeechOdd) (q ell : ℕ) :
    matrixTerm s (b-2) u (lowering leechData leechUnit (!s) v) a q ell =
      -(((ell+1 : ℕ) : ℂ) * matrixTerm s b u v a q (ell+1)) := by
  have hentry : matrixEntry s (b-2) u (lowering leechData leechUnit (!s) v) a q ell =
      matrixEntry s b u v a q (ell+1) := by
    have he : b-2 + 2*(q : ℤ) - 2*(ell : ℤ) =
        b + 2*(q : ℤ) - 2*((ell+1 : ℕ) : ℤ) := by omega
    unfold matrixEntry
    rw [he, pow_succ (lowering leechData leechUnit (!s)) ell, Module.End.mul_apply]
  simp only [matrixTerm, hentry]
  calc
    _ = signedFactorial q * -(((ell+1 : ℕ) : ℂ) * signedFactorial (ell+1)) *
        matrixEntry s b u v a q (ell+1) := by
      rw [signedFactorial_succ, neg_neg]
    _ = _ := by ring

private theorem rectangle_shift_left (Q E : ℕ) (f : ℕ → ℕ → ℂ) :
    rectangle (Q+1) E (fun q ell => (q : ℂ) * f q ell) =
      rectangle Q E (fun q ell => ((q+1 : ℕ) : ℂ) * f (q+1) ell) := by
  unfold rectangle
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, Finset.sum_const_zero, add_zero]

private theorem rectangle_shift_right (Q E : ℕ) (f : ℕ → ℕ → ℂ) :
    rectangle Q (E+1) (fun q ell => (ell : ℂ) * f q ell) =
      rectangle Q E (fun q ell => ((ell+1 : ℕ) : ℂ) * f q (ell+1)) := by
  unfold rectangle
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, add_zero]

private theorem pairCoeff_lower_left (s : Bool) (M K : ℕ) (k : ℤ)
    (u : LeechTwisted s) (v : LeechTwisted (!s))
    (hu : u.val ∈ actualGrade leechData leechUnit M)
    (hv : v.val ∈ actualGrade leechData leechUnit K) (a : LeechOdd) :
    pairCoeff s k (lowering leechData leechUnit s u) v a =
      phase M k * rectangle (M/2+1) (K/2+1)
        (fun q ell => (q : ℂ) * matrixTerm s (fieldExponent M (k+1)) u v a q ell) := by
  by_cases hM : 2 ≤ M
  · rw [pairCoeff_finite s (M-2) K k _ v (lowering_grade s M u hu hM) hv a,
      phase_lower_left M k hM, fieldExponent_lower_left M k hM,
      show (M-2)/2+1 = M/2 by omega]
    let f := matrixTerm s (fieldExponent M (k+1)) u v a
    have hsum : rectangle (M/2) (K/2+1)
        (matrixTerm s (fieldExponent M (k+1)+2) (lowering leechData leechUnit s u) v a) =
        -rectangle (M/2) (K/2+1) (fun q ell => ((q+1 : ℕ) : ℂ) * f (q+1) ell) := by
      simp only [rectangle, matrixTerm_lower_left, f, Finset.sum_neg_distrib]
    rw [hsum, ← rectangle_shift_left (M/2) (K/2+1) f, neg_mul_neg]
  · rw [lowering_small s M u hu (by omega), show M/2+1 = 1 by omega]
    simp only [pairCoeff, map_zero, Pi.zero_apply, LinearMap.zero_apply, Submodule.coe_zero,
      rectangle, Finset.sum_range_one, Nat.cast_zero, zero_mul, Finset.sum_const_zero, mul_zero]

private theorem pairCoeff_lower_right (s : Bool) (M K : ℕ) (k : ℤ)
    (u : LeechTwisted s) (v : LeechTwisted (!s))
    (hu : u.val ∈ actualGrade leechData leechUnit M)
    (hv : v.val ∈ actualGrade leechData leechUnit K) (a : LeechOdd) :
    pairCoeff s k u (lowering leechData leechUnit (!s) v) a =
      -(phase M k * rectangle (M/2+1) (K/2+1)
        (fun q ell => (ell : ℂ) * matrixTerm s (fieldExponent M (k+1)) u v a q ell)) := by
  by_cases hK : 2 ≤ K
  · rw [pairCoeff_finite s M (K-2) k u _ hu (lowering_grade (!s) K v hv hK) a,
      show (K-2)/2+1 = K/2 by omega,
      show fieldExponent M k = fieldExponent M (k+1)-2 by rw [fieldExponent_succ]; omega]
    let f := matrixTerm s (fieldExponent M (k+1)) u v a
    have hsum : rectangle (M/2+1) (K/2)
        (matrixTerm s (fieldExponent M (k+1)-2) u (lowering leechData leechUnit (!s) v) a) =
        -rectangle (M/2+1) (K/2) (fun q ell => ((ell+1 : ℕ) : ℂ) * f q (ell+1)) := by
      simp only [rectangle, matrixTerm_lower_right, f, Finset.sum_neg_distrib]
    rw [hsum, ← rectangle_shift_right (M/2+1) (K/2) f, mul_neg]
  · rw [lowering_small (!s) K v hv (by omega), show K/2+1 = 1 by omega]
    simp only [pairCoeff, map_zero, Pi.zero_apply, LinearMap.zero_apply, Submodule.coe_zero,
      rectangle, Finset.sum_range_one, Nat.cast_zero, zero_mul, Finset.sum_const_zero,
      mul_zero, neg_zero]

private theorem matrixTerm_translate (s : Bool) (b : ℤ) (u : LeechTwisted s) (v : LeechTwisted (!s))
    (a : LeechOdd) (q ell : ℕ) :
    matrixTerm s b u v (oddTranslation leechData a) q ell =
      ((((b+2 : ℤ) : ℂ)/2) + (q : ℂ) - (ell : ℂ)) * matrixTerm s (b+2) u v a q ell := by
  have hidx : b + 2*(q : ℤ) - 2*(ell : ℤ) + 2 =
      (b+2) + 2*(q : ℤ) - 2*(ell : ℤ) := by omega
  have hcast : (((b+2 + 2*(q : ℤ) - 2*(ell : ℤ) : ℤ) : ℂ)/2) =
      (((b+2 : ℤ) : ℂ)/2) + (q : ℂ) - (ell : ℂ) := by
    push_cast
    ring
  have hval : (oddTranslation leechData a).val =
      LatticeSugawaraConformal.translation leechData a.val := rfl
  simp only [matrixTerm, matrixEntry, hval,
    LatticeHalfFockOriginalTranslation.correctedField_translation_physical,
    hidx, hcast, map_smul, smul_eq_mul]
  ring

private theorem pairCoeff_translate (s : Bool) (M K : ℕ) (k : ℤ)
    (u : LeechTwisted s) (v : LeechTwisted (!s))
    (hu : u.val ∈ actualGrade leechData leechUnit M)
    (hv : v.val ∈ actualGrade leechData leechUnit K) (a : LeechOdd) :
    pairCoeff s k u v (oddTranslation leechData a) =
      phase M k * rectangle (M/2+1) (K/2+1) (fun q ell =>
        ((k : ℂ) - (M : ℂ) - 1/2 + (q : ℂ) - (ell : ℂ)) *
          matrixTerm s (fieldExponent M (k+1)) u v a q ell) := by
  have hc : (((fieldExponent M k + 2 : ℤ) : ℂ) / 2) =
      (k : ℂ) - (M : ℂ) - 1/2 := by
    unfold fieldExponent
    push_cast
    ring
  rw [pairCoeff_finite s M K k u v hu hv (oddTranslation leechData a)]
  unfold rectangle
  simp only [matrixTerm_translate, hc, fieldExponent_succ]

private theorem rectangle_ward (Q E : ℕ) (c : ℂ) (f : ℕ → ℕ → ℂ) :
    rectangle Q E (fun q ell => (c + (q : ℂ) - (ell : ℂ)) * f q ell) =
      rectangle Q E (fun q ell => (q : ℂ) * f q ell) -
        rectangle Q E (fun q ell => (ell : ℂ) * f q ell) +
        c * rectangle Q E f := by
  simp only [rectangle, sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.mul_sum]
  abel

private theorem paired_mode_ward (s : Bool) (M K : ℕ) (k : ℤ)
    (u : LeechTwisted s) (v : LeechTwisted (!s))
    (hu : u.val ∈ actualGrade leechData leechUnit M)
    (hv : v.val ∈ actualGrade leechData leechUnit K) (a : LeechOdd) :
    pairCoeff s k u v (oddTranslation leechData a) =
      pairCoeff s k (lowering leechData leechUnit s u) v a +
        pairCoeff s k u (lowering leechData leechUnit (!s) v) a +
        ((M : ℂ) - (k : ℂ) + 1/2) * pairCoeff s (k+1) u v a := by
  rw [pairCoeff_translate s M K k u v hu hv a,
    pairCoeff_lower_left s M K k u v hu hv a, pairCoeff_lower_right s M K k u v hu hv a,
    pairCoeff_finite s M K (k+1) u v hu hv a, phase_mode_succ, rectangle_ward]
  ring

private theorem transpose_source_mode_one (x a : Carrier leechData) :
    P (sugawaraMode leechData (gramComplex leechData)⁻¹ 1 x) a =
      P x (LatticeSugawaraConformal.translation leechData a) := by
  rw [sourcePairing_symmetric leechData _ a]
  exact (sourcePairing_translation leechData leechUnit a x).symm.trans
    (sourcePairing_symmetric leechData _ _)

private theorem translate_minusPart (a : Carrier leechData) :
    LatticeSugawaraConformal.translation leechData (minusPart leechData a) =
      minusPart leechData (LatticeSugawaraConformal.translation leechData a) := by
  have hc : theta leechData (LatticeSugawaraConformal.translation leechData a) =
      LatticeSugawaraConformal.translation leechData (theta leechData a) := by
    simp only [LatticeActualVertexAlgebra.translation_as_mode, stateField_theta, theta_vacuum]
  simp only [minusPart, map_smul, map_sub, hc]

private theorem source_mode_one_eq_of_pairing (x y : LeechOdd)
    (h : ∀ a : LeechOdd, P x.val (oddTranslation leechData a).val = P y.val a.val) :
    sugawaraMode leechData (gramComplex leechData)⁻¹ 1 x.val = y.val := by
  apply sub_eq_zero.mp
  apply (sourcePairing_nondegenerate leechData leechUnit).1
  intro a
  let b : LeechOdd := ⟨minusPart leechData a, minusPart_mem a⟩
  have hb : (oddTranslation leechData b).val =
      minusPart leechData (LatticeSugawaraConformal.translation leechData a) :=
    translate_minusPart a
  have ha : P (sugawaraMode leechData (gramComplex leechData)⁻¹ 1 x.val) a =
      P y.val a := calc
    _ = P x.val (LatticeSugawaraConformal.translation leechData a) :=
      transpose_source_mode_one x.val a
    _ = P x.val (oddTranslation leechData b).val := by
      rw [hb, sourcePairing_minusPart_right x.val _ x.property]
    _ = P y.val b.val := h b
    _ = P y.val a := sourcePairing_minusPart_right y.val a y.property
  rw [map_sub, LinearMap.sub_apply, ha, sub_self]

/-- The original lattice lowering mode on every doubled coefficient of the
native mixed Leech pair. The two twisted lowerings act in their respective
parity spaces, and the shifted coefficient has the physical Ward scalar. -/
theorem mu_coeff_L1_ward (s : Bool) (M K : ℕ) (e : ℤ)
    (u : Twisted leechData leechUnit s) (v : Twisted leechData leechUnit (!s))
    (hu : u.val ∈ actualGrade leechData leechUnit M)
    (hv : v.val ∈ actualGrade leechData leechUnit K) :
    sugawaraMode leechData (gramComplex leechData)⁻¹ 1 ((mu s u).coeff e v).val =
      ((mu s (lowering leechData leechUnit s u)).coeff e v).val +
        ((mu s u).coeff e (lowering leechData leechUnit (!s) v)).val +
        (3 + (M : ℂ) + (e : ℂ)/2 - 1) • ((mu s u).coeff (e-2) v).val := by
  by_cases he : Even e
  · have he' : Even (e-2) := by
      obtain ⟨j, hj⟩ := he
      exact ⟨j-1, by omega⟩
    simp only [mu_coeff_even_zero s e u v he,
      mu_coeff_even_zero s e (lowering leechData leechUnit s u) v he,
      mu_coeff_even_zero s e u (lowering leechData leechUnit (!s) v) he,
      mu_coeff_even_zero s (e-2) u v he', Submodule.coe_zero, map_zero, zero_add, smul_zero]
  · obtain ⟨j, hj⟩ := Int.not_even_iff_odd.mp he
    let k : ℤ := -j-2
    have hk : modeExponent k = e := by
      dsimp only [modeExponent, k]
      omega
    have hshift : modeExponent k - 2 = modeExponent (k+1) := by
      unfold modeExponent
      omega
    have hc : 3 + (M : ℂ) + (modeExponent k : ℂ)/2 - 1 = (M : ℂ) - (k : ℂ) + 1/2 := by
      unfold modeExponent
      push_cast
      ring
    rw [← hk, hshift, hc]
    let y : LeechOdd := (mu s (lowering leechData leechUnit s u)).coeff (modeExponent k) v +
      (mu s u).coeff (modeExponent k) (lowering leechData leechUnit (!s) v) +
        ((M : ℂ) - (k : ℂ) + 1/2) • (mu s u).coeff (modeExponent (k+1)) v
    change sugawaraMode leechData (gramComplex leechData)⁻¹ 1
      ((mu s u).coeff (modeExponent k) v).val = y.val
    apply source_mode_one_eq_of_pairing
    intro a
    simpa only [pairCoeff, y, Submodule.coe_add, Submodule.coe_smul,
      map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul] using
      paired_mode_ward s M K k u v hu hv a

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeMixedPairWard
