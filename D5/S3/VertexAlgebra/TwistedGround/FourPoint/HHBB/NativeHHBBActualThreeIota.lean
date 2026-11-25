import D5.S3.VertexAlgebra.TwistedGround.FourPoint.HHBB.NativeHHBBFormalExchangedIota
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.HHBB.NativeHHBBFormalFusedIota
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.HHBB.NativeHHBBFormalProductIota

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBActualThreeIota

open ActualLeechHyperbolic (leechData)
open CollisionLaurentKernels.LaurentCollision
open LatticeHalfFockChargedTensorCoefficients (ActualGround)
open NativeFixedPairAIterate (fixedAExponent fixedAIterateCoeff)
open NativeHHBBFormalChannels (hhbb_marked_formal_channels)
open NativeHHBBFormalExchangedIota
  (hhbb_marked_iotaZX_native_d_of_product iotaXZ_swapped_poles_coeff
    iotaZX_eq_iotaXZ_swap paddedReverse_eq_reflect)
open NativeHHBBFormalFusedIota
  (fusedLaurent_coeff_below hhbb_marked_fusedLaurent_coeff swapRational)
open NativeHHBBFormalInfinityExpansion (paddedReverse)
open NativeHHBBFormalProductIota
  (hhbb_marked_iotaXZ_bProductCoeff iotaXZ_commonRational_coeff iotaXZ_commonRational_coeff_of_lt)
open NativeHHBBTwoVariableRational (commonRational homogenizedNumerator)
open NativeMixedUpperDLip (dProductCoeff)
open NativeMixedUpperProductCusp (bProductCoeff bSewnNumerator)
open NativeMixedWickChartTransport (MixedParity doubledOccupation)
open Orbifold.NativeOddTwistedIntertwiner (TwistedEven TwistedOdd leechUnit)
open OriginalFourMActualChart (Puncture)
open OriginalFourMVariableSupport (wordAt)
open OriginalGaussianSewnAnalytic (coefficient)

private noncomputable def swapEquiv : Rational ℂ ≃+* Rational ℂ :=
  IsFractionRing.ringEquivOfRingEquiv (Polynomial.Bivariate.swap (R := ℂ)).toRingEquiv

private theorem swapRational_eq_swapEquiv : swapRational = swapEquiv.toRingHom := by
  apply IsFractionRing.ringHom_ext (A := Bivariate ℂ)
  intro f
  change swapRational (algebraMap (Bivariate ℂ) (Rational ℂ) f) =
    swapEquiv (algebraMap (Bivariate ℂ) (Rational ℂ) f)
  rw [swapRational, IsFractionRing.lift_algebraMap, swapEquiv,
    IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  rfl

private theorem iotaXZ_swapRational (F : Rational ℂ) :
    iotaXZ ℂ (swapRational F) = iotaZX ℂ F := by
  rw [swapRational_eq_swapEquiv, iotaZX_eq_iotaXZ_swap, RingHom.comp_apply]
  rfl

private theorem iotaZX_swapRational (F : Rational ℂ) :
    iotaZX ℂ (swapRational F) = iotaXZ ℂ F := by
  have h : swapRational.comp swapRational = RingHom.id (Rational ℂ) := by
    apply IsFractionRing.ringHom_ext (A := Bivariate ℂ)
    intro f
    change swapRational (swapRational (algebraMap (Bivariate ℂ) (Rational ℂ) f)) =
      algebraMap (Bivariate ℂ) (Rational ℂ) f
    rw [swapRational_eq_swapEquiv]
    change swapEquiv (swapEquiv (algebraMap (Bivariate ℂ) (Rational ℂ) f)) =
      algebraMap (Bivariate ℂ) (Rational ℂ) f
    unfold swapEquiv
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap,
      IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    exact congrArg (algebraMap (Bivariate ℂ) (Rational ℂ))
      (Polynomial.Bivariate.swap_swap_apply f)
  rw [← iotaXZ_swapRational]
  exact congrArg (iotaXZ ℂ) (DFunLike.congr_fun h F)

/-- The physical D expansion in collision coordinates. Its on-grid outer
coefficients are single inner monomials with the native D scalar. -/
theorem hhbb_marked_iotaXZ_native_d {ι : Type*} [Finite ι]
    (slot : ι → Puncture) (colour : ι → Fin leechData.rank) (n : ι → ℕ) (l : List ι)
    (hl : l.Nodup) (hpar : MixedParity slot n l)
    (u v : TwistedEven) (w bState : TwistedOdd) (p q r s : ActualGround leechData leechUnit)
    (hu : u.val = wordAt leechData slot colour n l .P ⊗ₜ[ℂ] p)
    (hv : v.val = wordAt leechData slot colour n l .Q ⊗ₜ[ℂ] q)
    (hw : w.val = wordAt leechData slot colour n l .R ⊗ₜ[ℂ] r)
    (hb : bState.val = wordAt leechData slot colour n l .S ⊗ₜ[ℂ] s) :
    let grade (i : Puncture) := (doubledOccupation slot n l i).toNat
    let V := wordAt leechData slot colour n l
    let M := grade .P
    let K := grade .Q
    let L := grade .R
    let N := grade .S
    let b := (6 + M + K) / 2
    let c := (M + L + 7) / 2
    let degree := (12 + M + K + L + N) / 2
    let GInf (t : ℂ) := Complex.I ^ ((L : ℤ) + N - K - 2 * (M : ℤ) - 3) *
      bSewnNumerator M L N (V .Q) (V .P) (V .R) (V .S) q p r s t
    let P : Polynomial ℂ := ∑ j ∈ Finset.range (degree + 1),
      Polynomial.C (coefficient j (fun t => (t - 1) ^ b * GInf t)) *
        Polynomial.X ^ (degree - j)
    let F := swapRational (commonRational P degree M K L)
    (∀ E : ℕ, (iotaXZ ℂ F).coeff ((E : ℤ) - c) =
      HahnSeries.single ((1 + (N : ℤ) - K) / 2 - E)
        (dProductCoeff false false M K L N u w v bState E)) ∧
    (∀ k : ℤ, k < -(c : ℤ) → (iotaXZ ℂ F).coeff k = 0) := by
  intro grade V M K L N b c degree GInf P F
  let a : ℕ := (5 + K + L) / 2
  have hP : P.natDegree ≤ degree :=
    (hhbb_marked_formal_channels slot colour n l hl hpar u v w bState p q r s hu hv hw hb).1
  let Q := Polynomial.C ((-1 : ℂ) ^ b) * paddedReverse degree P
  have hQ : Q.natDegree ≤ degree := by
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    rw [paddedReverse_eq_reflect P degree hP]
    exact Polynomial.natDegree_reflect_le.trans (max_le le_rfl hP)
  have hc : (c : ℤ) = (((5 + M + L) / 2 : ℕ) : ℤ) + 1 := by
    dsimp only [c]
    push_cast
    omega
  simp only [F, iotaXZ_swapRational]
  refine hhbb_marked_iotaZX_native_d_of_product slot colour n l hl hpar
    u v w bState p q r s hu hv hw hb ?_ ?_
  · intro E
    change (iotaXZ ℂ (algebraMap (Bivariate ℂ) (Rational ℂ)
        (homogenizedNumerator Q degree) / (x ℂ ^ a * z ℂ ^ c * (x ℂ - z ℂ) ^ b))).coeff
          ((E : ℤ) - c) = HahnSeries.single ((degree : ℤ) - a - b - E)
        (PowerSeries.coeff E (Q.toPowerSeries * (PowerSeries.invOneSubPow ℂ b).val))
    have hIndex : (E : ℤ) - c + 1 = (E : ℤ) - (((5 + M + L) / 2 : ℕ) : ℤ) := by
      omega
    have hb' : (6 + K + M) / 2 = b := by dsimp only [b]; omega
    have ha' : (((K + L + 7) / 2 : ℕ) : ℤ) = (a : ℤ) + 1 := by
      dsimp only [a]
      push_cast
      omega
    have hWeight : 1 + ((degree : ℤ) - ((a : ℤ) + 1) - b - E) =
        (degree : ℤ) - a - b - E := by omega
    rw [iotaXZ_swapped_poles_coeff Q degree M K L, hIndex,
      iotaXZ_commonRational_coeff Q degree K M L hQ E,
      T, HahnSeries.single_mul_single, one_mul, hb', ha', hWeight]
  · intro k hk
    change k < -(c : ℤ) at hk
    have hIndex : k + 1 < -(((5 + M + L) / 2 : ℕ) : ℤ) := by omega
    rw [iotaXZ_swapped_poles_coeff Q degree M K L,
      iotaXZ_commonRational_coeff_of_lt Q degree K M L hQ (k + 1) hIndex, mul_zero]

/-- In collision coordinates, x is physical z and z is physical x. The
embeddings iotaZX, iotaXZ, and iotaFused give the physical B, D, and A charts
respectively. Their outer powers are physical z, physical x, and physical
x minus physical z, respectively. The B scalar carries the native minus sign. -/
theorem hhbb_marked_three_iota_coefficients {ι : Type*} [Finite ι]
    (slot : ι → Puncture) (colour : ι → Fin leechData.rank) (n : ι → ℕ) (l : List ι)
    (hl : l.Nodup) (hpar : MixedParity slot n l)
    (u v : TwistedEven) (w bState : TwistedOdd) (p q r s : ActualGround leechData leechUnit)
    (hu : u.val = wordAt leechData slot colour n l .P ⊗ₜ[ℂ] p)
    (hv : v.val = wordAt leechData slot colour n l .Q ⊗ₜ[ℂ] q)
    (hw : w.val = wordAt leechData slot colour n l .R ⊗ₜ[ℂ] r)
    (hb : bState.val = wordAt leechData slot colour n l .S ⊗ₜ[ℂ] s) :
    let grade (i : Puncture) := (doubledOccupation slot n l i).toNat
    let V := wordAt leechData slot colour n l
    let M := grade .P
    let K := grade .Q
    let L := grade .R
    let N := grade .S
    let a := (5 + K + L) / 2
    let b := (6 + M + K) / 2
    let c := (M + L + 7) / 2
    let degree := (12 + M + K + L + N) / 2
    let GInf (t : ℂ) := Complex.I ^ ((L : ℤ) + N - K - 2 * (M : ℤ) - 3) *
      bSewnNumerator M L N (V .Q) (V .P) (V .R) (V .S) q p r s t
    let P : Polynomial ℂ := ∑ j ∈ Finset.range (degree + 1),
      Polynomial.C (coefficient j (fun t => (t - 1) ^ b * GInf t)) *
        Polynomial.X ^ (degree - j)
    let F := swapRational (commonRational P degree M K L)
    let A (E : ℕ) := fixedAIterateCoeff false M K L N (fixedAExponent M K E)
      u v w.val bState.val
    ((∀ E : ℕ, (iotaZX ℂ F).coeff ((E : ℤ) - a) =
      HahnSeries.single ((degree : ℤ) - c - b - E)
        (-bProductCoeff false false M K L N v w u bState E)) ∧
      (∀ k : ℤ, k < -(a : ℤ) → (iotaZX ℂ F).coeff k = 0)) ∧
    ((∀ E : ℕ, (iotaXZ ℂ F).coeff ((E : ℤ) - c) =
      HahnSeries.single ((1 + (N : ℤ) - K) / 2 - E)
        (dProductCoeff false false M K L N u w v bState E)) ∧
      (∀ k : ℤ, k < -(c : ℤ) → (iotaXZ ℂ F).coeff k = 0)) ∧
    ((∀ E : ℕ, (iotaFused ℂ F).coeff ((E : ℤ) - b) =
      HahnSeries.single (((N : ℤ) - L) / 2 - E)
        (PowerSeries.coeff E
          (PowerSeries.binomialSeries ℂ (-1 / 2 : ℂ) * PowerSeries.mk A))) ∧
      (∀ k : ℤ, k < -(b : ℤ) → (iotaFused ℂ F).coeff k = 0)) := by
  intro grade V M K L N a b c degree GInf P F A
  have hP : P.natDegree ≤ degree :=
    (hhbb_marked_formal_channels slot colour n l hl hpar u v w bState p q r s hu hv hw hb).1
  have hB : iotaZX ℂ F = iotaXZ ℂ (commonRational P degree M K L) := iotaZX_swapRational _
  refine ⟨⟨?_, ?_⟩,
    hhbb_marked_iotaXZ_native_d slot colour n l hl hpar u v w bState p q r s hu hv hw hb,
    ⟨hhbb_marked_fusedLaurent_coeff slot colour n l hl hpar
      u v w bState p q r s hu hv hw hb, fusedLaurent_coeff_below P degree M K L⟩⟩
  · intro E
    rw [hB]
    exact hhbb_marked_iotaXZ_bProductCoeff slot colour n l hl hpar
      u v w bState p q r s hu hv hw hb E
  · intro k hk
    rw [hB]
    exact iotaXZ_commonRational_coeff_of_lt P degree M K L hP k hk

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBActualThreeIota
