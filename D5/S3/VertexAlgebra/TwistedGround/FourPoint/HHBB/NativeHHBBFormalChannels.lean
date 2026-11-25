import D5.S3.VertexAlgebra.TwistedGround.FourPoint.HHBB.NativeHHBBFormalZeroExpansion
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.HHBB.NativeHHBBFormalInfinityExpansion
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.HHBB.NativeHHBBFusedNormalizedSeries

/-! The common polynomial determines all three actual marked HHBB energy series. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators TensorProduct Topology
open Filter

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBFormalChannels

open ActualLeechHyperbolic (leechData)
open Complex (I)
open LatticeHalfFockChargedTensorCoefficients (ActualGround)
open NativeFixedPairAIterate (fixedAExponent fixedAIterateCoeff fixedASlitSewn)
open NativeHHBBFormalInfinityExpansion (hhbb_marked_native_d_infinity_powerSeries paddedReverse)
open NativeHHBBFormalIterateExpansion (hhbb_marked_iterate_energy_expansion)
open NativeHHBBFormalZeroExpansion (hhbb_marked_b_zero_powerSeries)
open NativeHHBBFusedNormalizedSeries (hhbb_marked_iterate_normalized_powerSeries)
open NativeHHBBNormalizedGlobalMeromorphic (hhbb_marked_normalized_global_meromorphic)
open NativeHHBBPolynomialFromInfinity (hhbb_marked_upper_common_rational)
open NativeMixedUpperDLip (dProductCoeff)
open NativeMixedUpperProductCusp (bProductCoeff bSewnNumerator)
open NativeMixedWickChartTransport (MixedParity doubledOccupation)
open Orbifold.NativeOddTwistedIntertwiner (TwistedEven TwistedOdd leechUnit)
open OriginalFourMActualChart (Puncture)
open OriginalFourMVariableSupport (wordAt)
open OriginalGaussianSewnAnalytic (coefficient)

set_option maxHeartbeats 4000000 in
/-- The signed B expansion at zero, the A expansion in the energy variable
`s = (1 - y) / y`, and the exchanged D expansion at infinity use the same
explicit numerator. Multiplying the A series by the formal root ratio
`(1 + s)^(-1/2)` gives the integer-exponent fused coefficients. -/
theorem hhbb_marked_formal_channels {X : Type*} [Finite X]
    (slot : X → Puncture) (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X)
    (hl : l.Nodup) (hpar : MixedParity slot n l)
    (u v : TwistedEven) (w b : TwistedOdd) (p q r d : ActualGround leechData leechUnit)
    (hu : u.val = wordAt leechData slot colour n l .P ⊗ₜ[ℂ] p)
    (hv : v.val = wordAt leechData slot colour n l .Q ⊗ₜ[ℂ] q)
    (hw : w.val = wordAt leechData slot colour n l .R ⊗ₜ[ℂ] r)
    (hb : b.val = wordAt leechData slot colour n l .S ⊗ₜ[ℂ] d) :
    let grade (i : Puncture) := (doubledOccupation slot n l i).toNat
    let V := wordAt leechData slot colour n l
    let M := grade .P
    let K := grade .Q
    let L := grade .R
    let N := grade .S
    let a₀ : ℕ := (5 + K + L) / 2
    let a₁ : ℕ := (6 + M + K) / 2
    let degree := (12 + M + K + L + N) / 2
    let GInf (z : ℂ) := I ^ ((L : ℤ) + N - K - 2 * (M : ℤ) - 3) *
      bSewnNumerator M L N (V .Q) (V .P) (V .R) (V .S) q p r d z
    let G (z : ℂ) := (z - 1) ^ a₁ * GInf z
    let P : Polynomial ℂ := ∑ j ∈ Finset.range (degree + 1),
      Polynomial.C (coefficient j G) * Polynomial.X ^ (degree - j)
    let c (E : ℕ) := fixedAIterateCoeff false M K L N (fixedAExponent M K E)
      u v w.val b.val
    let α : ℂ := (a₀ : ℂ) + ((N : ℂ) - L + 1) / 2
    let k : ℤ := (a₀ : ℤ) + ((N : ℤ) - L) / 2
    let fused := PowerSeries.binomialSeries ℂ (-1 / 2 : ℂ) * PowerSeries.mk c
    P.natDegree ≤ degree ∧
    (PowerSeries.mk (fun E => -(bProductCoeff false false M K L N v w u b E)) =
      P.toPowerSeries * (↑(PowerSeries.invOneSubPow ℂ a₁) : PowerSeries ℂ)) ∧
    (PowerSeries.mk c =
      ∑ j ∈ P.support, PowerSeries.C (P.coeff j) * PowerSeries.binomialSeries ℂ (α - j)) ∧
    (∀ E : ℕ, c E = ∑ j ∈ P.support, P.coeff j * Ring.choose (α - j) E) ∧
    (fused = ∑ j ∈ P.support,
      PowerSeries.C (P.coeff j) * PowerSeries.binomialSeries ℂ ((k : ℂ) - j)) ∧
    (∀ E : ℕ, PowerSeries.coeff E fused =
      ∑ j ∈ P.support, P.coeff j * Ring.choose ((k : ℂ) - j) E) ∧
    (∀ᶠ z in 𝓝 (0 : ℂ), GInf z * (z - 1) ^ a₁ = (paddedReverse degree P).eval z) ∧
    PowerSeries.mk (dProductCoeff false false M K L N u w v b) =
      (Polynomial.C ((-1 : ℂ) ^ a₁) * paddedReverse degree P).toPowerSeries *
        (↑(PowerSeries.invOneSubPow ℂ a₁) : PowerSeries ℂ) := by
  intro grade V M K L N a₀ a₁ degree GInf G P c α k fused
  obtain ⟨hDegree, ⟨H, _, hUpper, hRational⟩, _⟩ :=
    hhbb_marked_upper_common_rational slot colour n l hl hpar u v w b p q r d hu hv hw hb
  obtain ⟨H', _, _, _, hUpper', ⟨_, ⟨hCuspAnalytic, hCusp⟩, _⟩, _⟩ :=
    hhbb_marked_normalized_global_meromorphic slot colour n l hl hpar u v w b p q r d hu hv hw hb
  let A (s : ℂ) := fixedASlitSewn M K (V .P) (V .Q) (V .R) (V .S) p q r d (-s)
  let C (y : ℂ) := Complex.sqrt y * (Complex.sqrt y ^ ((N : ℤ) - L) * A ((1 - y) / y))
  let U : Set ℂ := {y | (1 / 2 : ℝ) < y.re}
  have hRight (y : ℂ) (hy : y ∈ U) : y ≠ 0 := by
    rintro rfl
    norm_num [U] at hy
  have hCast : (a₁ : ℤ) = (6 + (M : ℤ) + K) / 2 := by
    simp only [a₁, Int.natCast_div, Nat.cast_add, Nat.cast_ofNat]
  have hCleared (y : ℂ) (hy : y ∈ U) (hy₁ : y ≠ 1) :
      y ^ a₀ * C y = (y ^ a₀ * (1 - y) ^ a₁) * H' y := by
    have hCuspAt : H' y = (1 - y) ^ (-((6 + (M : ℤ) + K) / 2)) * C y :=
      hCusp y hy hy₁
    rw [hCuspAt, ← hCast, mul_assoc, ← mul_assoc ((1 - y) ^ a₁), ← zpow_natCast _ a₁,
      ← zpow_add₀ (sub_ne_zero.mpr hy₁.symm), add_neg_cancel, zpow_zero, one_mul]
  have hPoly : Set.EqOn (fun y => y ^ a₀ * C y) P.eval U := by
    have hAnalytic : AnalyticOnNhd ℂ (fun y => y ^ a₀ * C y) U :=
      fun y hy => (analyticAt_id.pow a₀).mul (hCuspAnalytic y hy)
    have hPolyAnalytic : AnalyticOnNhd ℂ P.eval U :=
      (AnalyticOnNhd.eval_polynomial P).mono (Set.subset_univ _)
    have hOpen : IsOpen (U ∩ {y : ℂ | 0 < y.im}) :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt continuous_const Complex.continuous_im)
    have hPoint : 1 + I ∈ U ∩ {y : ℂ | 0 < y.im} := by
      norm_num [U, Complex.add_re, Complex.add_im]
    apply hAnalytic.eqOn_of_preconnected_of_eventuallyEq hPolyAnalytic
      (convex_halfSpace_re_gt (1 / 2 : ℝ)).isPreconnected hPoint.1
    filter_upwards [hOpen.eventually_mem hPoint] with y hy
    have hy₁ : y ≠ 1 := by
      rintro rfl
      have := hy.2
      norm_num at this
    have hAgree : H' y = H y := (hUpper' y hy.2).trans (hUpper y hy.2).symm
    have hDenom : y ^ a₀ * (1 - y) ^ a₁ ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (hRight y hy.1)) (pow_ne_zero _ (sub_ne_zero.mpr hy₁.symm))
    rw [hCleared y hy.1 hy₁, hAgree, mul_comm]
    exact (eq_div_iff hDenom).mp (hRational y (hRight y hy.1) hy₁)
  have hRightNear : ∀ᶠ y in 𝓝 (1 : ℂ), y ∈ U :=
    (isOpen_lt continuous_const Complex.continuous_re).eventually_mem
      (show (1 : ℂ) ∈ U by norm_num [U])
  have hRationalNear : ∀ᶠ y : ℂ in 𝓝[≠] (1 : ℂ),
      H' y = P.eval y / (y ^ a₀ * (1 - y) ^ a₁) := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hRightNear, self_mem_nhdsWithin]
      with y hy hy₁
    have hy₁' : y ≠ 1 := by simpa using hy₁
    have hDenom : y ^ a₀ * (1 - y) ^ a₁ ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (hRight y hy)) (pow_ne_zero _ (sub_ne_zero.mpr hy₁'.symm))
    apply (eq_div_iff hDenom).mpr
    rw [mul_comm, ← hCleared y hy hy₁']
    exact hPoly hy
  obtain ⟨hA, hACoeff⟩ := hhbb_marked_iterate_energy_expansion
    slot colour n l hl hpar u v w b p q r d hu hv hw hb H' P hRationalNear hCusp
  have hFused := hhbb_marked_iterate_normalized_powerSeries
    slot colour n l hl hpar u v w b p q r d hu hv hw hb H' P hRationalNear hCusp
  refine ⟨hDegree, hhbb_marked_b_zero_powerSeries slot colour n l hl hpar
    u v w b p q r d hu hv hw hb, hA, hACoeff, hFused, ?_,
    hhbb_marked_native_d_infinity_powerSeries slot colour n l hl hpar
      u v w b p q r d hu hv hw hb⟩
  intro E
  simpa only [map_sum, PowerSeries.coeff_C_mul, PowerSeries.binomialSeries_coeff, smul_eq_mul,
    mul_one] using congrArg (PowerSeries.coeff (R := ℂ) E) hFused

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBFormalChannels
