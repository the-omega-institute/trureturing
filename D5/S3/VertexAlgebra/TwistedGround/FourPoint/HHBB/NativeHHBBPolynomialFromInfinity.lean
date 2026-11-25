import D5.S3.VertexAlgebra.TwistedGround.FourPoint.HHBB.NativeHHBBNormalizedGlobalMeromorphic
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSewnAnalytic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Analysis.Complex.Liouville

/-! The polynomial numerator of the normalized marked HHBB amplitude. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators TensorProduct Topology
open Bornology Filter Metric

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBPolynomialFromInfinity

open NativeMixedWickChartTransport (MixedParity doubledOccupation)
open OriginalFourMActualChart (Puncture)
open OriginalGaussianSewnAnalytic (coefficient)

private theorem entire_eq_reversed_taylor {E G : ℂ → ℂ} {d : ℕ}
    (hE : Differentiable ℂ E) (hG : AnalyticAt ℂ G 0)
    (hInf : ∀ᶠ y in cobounded ℂ, E y = y ^ d * G y⁻¹) (y : ℂ) :
    E y = ∑ n ∈ Finset.range (d + 1), coefficient n G * y ^ (d - n) := by
  let p := FormalMultilinearSeries.ofScalars ℂ (fun n => coefficient n G)
  have hp : HasFPowerSeriesAt G p 0 := hG.hasFPowerSeriesAt
  let P (z : ℂ) := ∑ n ∈ Finset.range (d + 1), coefficient n G * z ^ (d - n)
  have hP : Differentiable ℂ P := by
    dsimp only [P]
    fun_prop
  have hPartial (z : ℂ) (hz : z ≠ 0) :
      z ^ d * p.partialSum (d + 1) z⁻¹ = P z := by
    simp only [FormalMultilinearSeries.partialSum, FormalMultilinearSeries.apply_eq_pow_smul_coeff,
      p, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, P, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hnd : n ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    have hpow : z ^ d * (z⁻¹) ^ n = z ^ (d - n) := by
      conv_lhs => rw [← Nat.sub_add_cancel hnd, pow_add]
      rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hz, one_pow, mul_one]
    rw [← mul_assoc, hpow, mul_comm]
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp (hp.isBigO_sub_partialSum_pow (d + 1))
  have hInv : Tendsto (fun z : ℂ => z⁻¹) (cobounded ℂ) (𝓝 0) :=
    Filter.tendsto_inv₀_cobounded
  have hBound : ∀ᶠ z in cobounded ℂ, ‖E z - P z‖ ≤ C * ‖z⁻¹‖ := by
    filter_upwards [hInf, hInv.eventually hC, eventually_cobounded_le_norm (E := ℂ) 1]
      with z hIz hR hzNorm
    have hz : z ≠ 0 := by
      rintro rfl
      norm_num at hzNorm
    have hR' : ‖G z⁻¹ - p.partialSum (d + 1) z⁻¹‖ ≤ C * ‖z⁻¹‖ ^ (d + 1) := by
      simpa only [zero_add, Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)] using hR
    have hCancel : ‖z‖ ^ d * ‖z⁻¹‖ ^ d = 1 := by
      rw [← mul_pow, ← norm_mul, mul_inv_cancel₀ hz, norm_one, one_pow]
    calc
      ‖E z - P z‖ = ‖z‖ ^ d * ‖G z⁻¹ - p.partialSum (d + 1) z⁻¹‖ := by
        rw [hIz, ← hPartial z hz, ← mul_sub, norm_mul, norm_pow]
      _ ≤ ‖z‖ ^ d * (C * ‖z⁻¹‖ ^ (d + 1)) :=
        mul_le_mul_of_nonneg_left hR' (pow_nonneg (norm_nonneg _) _)
      _ = C * ((‖z‖ ^ d * ‖z⁻¹‖ ^ d) * ‖z⁻¹‖) := by
        rw [pow_succ]
        ring
      _ = C * ‖z⁻¹‖ := by
        rw [hCancel, one_mul]
  have hLimit : Tendsto (fun z => E z - P z) (cocompact ℂ) (𝓝 0) := by
    rw [← Metric.cobounded_eq_cocompact]
    apply squeeze_zero_norm' hBound
    simpa only [norm_zero, mul_zero] using tendsto_const_nhds.mul hInv.norm
  exact sub_eq_zero.mp ((hE.sub hP).apply_eq_of_tendsto_cocompact y hLimit)

/-- For the marked HHBB normalization, the cleared entire amplitude is the polynomial
obtained by reversing the first Taylor coefficients of the cleared infinity germ. -/
theorem hhbb_marked_cleared_polynomial {X : Type*}
    (slot : X → Puncture) (mode : X → ℕ) (marks : List X)
    (hpar : MixedParity slot mode marks) {E H Ginf : ℂ → ℂ}
    (hE : Differentiable ℂ E) (hGinf : AnalyticAt ℂ Ginf 0) :
    let M := (doubledOccupation slot mode marks .P).toNat
    let K := (doubledOccupation slot mode marks .Q).toNat
    let L := (doubledOccupation slot mode marks .R).toNat
    let N := (doubledOccupation slot mode marks .S).toNat
    let a := (5 + K + L) / 2
    let b := (6 + M + K) / 2
    let d := (12 + M + K + L + N) / 2
    let G (z : ℂ) := (z - 1) ^ b * Ginf z
    (∀ y : ℂ, 1 < ‖y‖ → E y = y ^ a * (1 - y) ^ b * H y) →
    (∀ y : ℂ, 1 < ‖y‖ → H y = y ^ ((1 + (N : ℤ) - K) / 2) * Ginf y⁻¹) →
    let P := ∑ n ∈ Finset.range (d + 1), Polynomial.C (coefficient n G) * Polynomial.X ^ (d - n)
    P.natDegree ≤ d ∧ ∀ y : ℂ, E y = P.eval y := by
  intro M K L N a b d G hClear hInf P
  constructor
  · dsimp only [P]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro n _
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le ..)
  have hNonneg (i : Puncture) : 0 ≤ doubledOccupation slot mode marks i := by
    classical
    unfold doubledOccupation
    apply List.sum_nonneg
    intro x hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    split <;> omega
  rcases hpar with ⟨hM, hK, hL, hN⟩
  have ha : ((a + b : ℕ) : ℤ) + (1 + (N : ℤ) - K) / 2 = d := by
    simp only [a, b, d, M, K, L, N, Int.natCast_add,
      Int.natCast_ediv, Int.toNat_of_nonneg (hNonneg _)]
    omega
  have hG : AnalyticAt ℂ G 0 :=
    (((analyticAt_id (𝕜 := ℂ)).sub analyticAt_const).pow b).mul hGinf
  have hExterior : ∀ᶠ y in cobounded ℂ, E y = y ^ d * G y⁻¹ := by
    filter_upwards [tendsto_norm_cobounded_atTop (E := ℂ) |>.eventually_gt_atTop 1]
      with y hy
    have hy₀ : y ≠ 0 := by
      rintro rfl
      norm_num at hy
    have hFactor : 1 - y = y * (y⁻¹ - 1) := by
      rw [mul_sub, mul_inv_cancel₀ hy₀, mul_one]
    have hPower : y ^ a * y ^ b * y ^ ((1 + (N : ℤ) - K) / 2) = y ^ d := by
      rw [← pow_add, ← zpow_natCast, ← zpow_add₀ hy₀, ha, zpow_natCast]
    rw [hClear y hy, hInf y hy, hFactor, mul_pow]
    change _ = y ^ d * ((y⁻¹ - 1) ^ b * Ginf y⁻¹)
    calc
      _ = (y ^ a * y ^ b * y ^ ((1 + (N : ℤ) - K) / 2)) *
          ((y⁻¹ - 1) ^ b * Ginf y⁻¹) := by ring
      _ = _ := by rw [hPower]
  intro y
  simpa only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X] using entire_eq_reversed_taylor hE hG hExterior y

open Complex (I)
open ActualLeechHyperbolic (leechData)
open LatticeHalfFockChargedTensorCoefficients (ActualGround)
open Orbifold.NativeOddTwistedIntertwiner (TwistedEven TwistedOdd leechUnit)
open OriginalFourMVariableSupport (wordAt)
open NativeFixedPairAIterate (fixedASlitSewn)
open NativeMixedUpperProductCusp (bJointTerm bSewnNumerator)
open NativeHHBBNormalizedGlobalMeromorphic (hhbb_marked_normalized_global_meromorphic)
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod (ball_subset_slitDomain)

open private sqrt_square from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedComplexSewing

local notation "ℒ" => leechData

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
/-- The marked native HHBB channels sum to one expression with a finite polynomial
numerator. The principal square root carries the upper-half-plane branch. After
normalization by that root, the rational formula holds on the whole punctured plane.
The raw B sum has the opposite sign to the physical A and exchanged D sums. -/
theorem hhbb_marked_upper_common_rational {X : Type*} [Finite X]
    (slot : X → Puncture) (colour : X → Fin leechData.rank) (n : X → ℕ) (l : List X)
    (hl : l.Nodup) (hpar : MixedParity slot n l)
    (u v : TwistedEven) (w b : TwistedOdd) (p q r d : ActualGround ℒ leechUnit)
    (hu : u.val = wordAt ℒ slot colour n l .P ⊗ₜ[ℂ] p)
    (hv : v.val = wordAt ℒ slot colour n l .Q ⊗ₜ[ℂ] q)
    (hw : w.val = wordAt ℒ slot colour n l .R ⊗ₜ[ℂ] r)
    (hb : b.val = wordAt ℒ slot colour n l .S ⊗ₜ[ℂ] d) :
    let grade (i : Puncture) := (doubledOccupation slot n l i).toNat
    let V := wordAt ℒ slot colour n l
    let M := grade .P
    let K := grade .Q
    let L := grade .R
    let N := grade .S
    let a₀ : ℕ := (5 + K + L) / 2
    let a₁ : ℕ := (6 + M + K) / 2
    let degree := (12 + M + K + L + N) / 2
    let Z := Complex.sqrt
    let GInf (z : ℂ) := I ^ ((L : ℤ) + N - K - 2 * (M : ℤ) - 3) *
      bSewnNumerator M L N (V .Q) (V .P) (V .R) (V .S) q p r d z
    let G (z : ℂ) := (z - 1) ^ a₁ * GInf z
    let P := ∑ j ∈ Finset.range (degree + 1),
      Polynomial.C (coefficient j G) * Polynomial.X ^ (degree - j)
    let F (y : ℂ) := -(Z y ^ (-(6 + (K : ℤ) + L)) *
      I ^ ((L : ℤ) + N - M - 2 * (K : ℤ) - 3) *
      bSewnNumerator K L N (V .P) (V .Q) (V .R) (V .S) p q r d y)
    let R (y : ℂ) := P.eval y / (Z y * y ^ a₀ * (1 - y) ^ a₁)
    P.natDegree ≤ degree ∧
    (∃ H : ℂ → ℂ, Meromorphic H ∧
      (∀ y : ℂ, 0 < y.im → H y = Z y * F y) ∧
      ∀ y : ℂ, y ≠ 0 → y ≠ 1 → H y = P.eval y / (y ^ a₀ * (1 - y) ^ a₁)) ∧
    (∀ y : ℂ, 0 < y.im → F y = R y) ∧
    (∀ y ∈ ball (0 : ℂ) 1, 0 < y.im →
      HasSum (bJointTerm false false v w u b 1 (Z y)) (-(R y))) ∧
    (∀ y : ℂ, 0 < y.im → (1 / 2 : ℝ) < y.re →
      HasSum (NativeMixedComplexSewing.aJointTerm u v w b (Z (1 - y)) (Z y)) (R y)) ∧
    (∀ y : ℂ, 0 < y.im → 1 < ‖y‖ →
      HasSum (bJointTerm false false u w v b (Z y) 1) (R y)) := by
  intro grade V M K L N a₀ a₁ degree Z GInf G P F R
  obtain ⟨H, hHol, hMer, _, hUpper, ⟨⟨hG₀, hH₀⟩, ⟨hG₁, hH₁⟩, ⟨hGInf, hHInf⟩⟩,
    _, _, ⟨hB, hA, hD⟩⟩ :=
    hhbb_marked_normalized_global_meromorphic slot colour n l hl hpar u v w b p q r d hu hv hw hb
  let G₀ (y : ℂ) := -(I ^ ((L : ℤ) + N - M - 2 * (K : ℤ) - 3) *
    bSewnNumerator K L N (V .P) (V .Q) (V .R) (V .S) p q r d y)
  let G₁ (y : ℂ) := Z y ^ ((N : ℤ) - L) *
    fixedASlitSewn M K (V .P) (V .Q) (V .R) (V .S) p q r d (-((1 - y) / y))
  classical
  let E (y : ℂ) := if y = 0 then G₀ 0 else if y = 1 then Z 1 * G₁ 1
    else y ^ a₀ * (1 - y) ^ a₁ * H y
  have hClear {y : ℂ} (hy₀ : y ≠ 0) (hy₁ : y ≠ 1) :
      E y = y ^ a₀ * (1 - y) ^ a₁ * H y := by
    simp only [E, ite_eq_right hy₀, ite_eq_right hy₁]
  have ha₀ : (a₀ : ℤ) = (5 + (K : ℤ) + L) / 2 := by
    norm_num only [a₀, Int.natCast_ediv, Int.natCast_add, Nat.cast_ofNat]
  have ha₁ : (a₁ : ℤ) = (6 + (M : ℤ) + K) / 2 := by
    norm_num only [a₁, Int.natCast_ediv, Int.natCast_add, Nat.cast_ofNat]
  have hCancel (z : ℂ) (e : ℕ) (hz : z ≠ 0) : z ^ e * z ^ (-(e : ℤ)) = 1 := by
    rw [← zpow_natCast, ← zpow_add₀ hz, add_neg_cancel, zpow_zero]
  have hBall₀ : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self zero_lt_one
  have hRight₁ : (1 : ℂ) ∈ {y : ℂ | (1 / 2 : ℝ) < y.re} := by norm_num
  have hRightOpen : IsOpen {y : ℂ | (1 / 2 : ℝ) < y.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hOneSub (y : ℂ) : AnalyticAt ℂ (fun z : ℂ => 1 - z) y :=
    analyticAt_const.sub analyticAt_id
  have hE₀ : AnalyticAt ℂ E 0 := by
    refine (((hOneSub 0).pow a₁).mul (hG₀ 0 (ball_subset_slitDomain hBall₀))).congr ?_
    filter_upwards [isOpen_ball.eventually_mem hBall₀] with y hy
    change (1 - y) ^ a₁ * G₀ y = E y
    by_cases hy₀ : y = 0
    · subst y
      simp [E]
    have hy₁ : y ≠ 1 := by
      rintro rfl
      norm_num [mem_ball, dist_eq_norm] at hy
    rw [hClear hy₀ hy₁, hH₀ y (ball_subset_slitDomain hy) hy₀, ← ha₀]
    calc
      _ = (y ^ a₀ * y ^ (-(a₀ : ℤ))) * ((1 - y) ^ a₁ * G₀ y) := by
        rw [hCancel _ _ hy₀, one_mul]
      _ = _ := by ring
  have hE₁ : AnalyticAt ℂ E 1 := by
    refine ((analyticAt_id.pow a₀).mul (hG₁ 1 hRight₁)).congr ?_
    filter_upwards [hRightOpen.eventually_mem hRight₁] with y hy
    change y ^ a₀ * (Z y * G₁ y) = E y
    have hy₀ : y ≠ 0 := by
      rintro rfl
      norm_num at hy
    by_cases hy₁ : y = 1
    · subst y
      simp [E]
    rw [hClear hy₀ hy₁, hH₁ y hy hy₁, ← ha₁]
    calc
      _ = ((1 - y) ^ a₁ * (1 - y) ^ (-(a₁ : ℤ))) * (y ^ a₀ * (Z y * G₁ y)) := by
        rw [hCancel _ _ (sub_ne_zero.mpr (Ne.symm hy₁)), one_mul]
      _ = _ := by ring
  have hEntire : Differentiable ℂ E := by
    intro y
    by_cases hy₀ : y = 0
    · exact hy₀ ▸ hE₀.differentiableAt
    by_cases hy₁ : y = 1
    · exact hy₁ ▸ hE₁.differentiableAt
    have hOpen : IsOpen ({0, 1} : Set ℂ)ᶜ :=
      (isClosed_singleton.union isClosed_singleton).isOpen_compl
    have hy : y ∈ ({0, 1} : Set ℂ)ᶜ := by simp [hy₀, hy₁]
    apply AnalyticAt.differentiableAt
    refine (((analyticAt_id.pow a₀).mul ((hOneSub y).pow a₁)).mul (hHol y hy)).congr ?_
    filter_upwards [hOpen.eventually_mem hy] with z hz
    have hz' : z ≠ 0 ∧ z ≠ 1 := by simpa using hz
    exact (hClear hz'.1 hz'.2).symm
  have hExterior (y : ℂ) (hy : 1 < ‖y‖) : E y = y ^ a₀ * (1 - y) ^ a₁ * H y := by
    apply hClear
    · rintro rfl
      norm_num at hy
    · rintro rfl
      norm_num at hy
  have hPolynomial : P.natDegree ≤ degree ∧ ∀ y : ℂ, E y = P.eval y :=
    hhbb_marked_cleared_polynomial slot n l hpar hEntire (hGInf 0 hBall₀) hExterior hHInf
  have hCleared (y : ℂ) (hy₀ : y ≠ 0) (hy₁ : y ≠ 1) :
      y ^ a₀ * (1 - y) ^ a₁ * H y = P.eval y :=
    (hClear hy₀ hy₁).symm.trans (hPolynomial.2 y)
  have hDenom (y : ℂ) (hy₀ : y ≠ 0) (hy₁ : y ≠ 1) :
      y ^ a₀ * (1 - y) ^ a₁ ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hy₀) (pow_ne_zero _ (sub_ne_zero.mpr hy₁.symm))
  have hNormalized (y : ℂ) (hy₀ : y ≠ 0) (hy₁ : y ≠ 1) :
      H y = P.eval y / (y ^ a₀ * (1 - y) ^ a₁) := by
    exact (eq_div_iff (hDenom y hy₀ hy₁)).mpr (by rw [mul_comm, hCleared y hy₀ hy₁])
  have hPhysical (y : ℂ) (hy : 0 < y.im) : F y = R y := by
    have hy₀ : y ≠ 0 := by
      rintro rfl
      simp at hy
    have hy₁ : y ≠ 1 := by
      rintro rfl
      simp at hy
    have hZ : Z y ≠ 0 := by
      intro hz
      have hs : Z y ^ (2 : ℕ) = y := sqrt_square y
      rw [hz, zero_pow (by decide)] at hs
      exact hy₀ hs.symm
    change F y = P.eval y / (Z y * y ^ a₀ * (1 - y) ^ a₁)
    have hDenomUpper : Z y * y ^ a₀ * (1 - y) ^ a₁ ≠ 0 := by
      rw [mul_assoc]
      exact mul_ne_zero hZ (hDenom y hy₀ hy₁)
    refine (eq_div_iff hDenomUpper).mpr ?_
    calc
      _ = y ^ a₀ * (1 - y) ^ a₁ * (Z y * F y) := by ring
      _ = P.eval y := by rw [← hUpper y hy, hCleared y hy₀ hy₁]
  exact ⟨hPolynomial.1, ⟨H, hMer, hUpper, hNormalized⟩, hPhysical,
    fun y hy him => hPhysical y him ▸ hB y hy him,
    fun y him hre => hPhysical y him ▸ hA y him hre,
    fun y him hy => hPhysical y him ▸ hD y him hy⟩

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBPolynomialFromInfinity
