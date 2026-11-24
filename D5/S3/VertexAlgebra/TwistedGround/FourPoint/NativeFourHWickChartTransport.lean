/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeFourHWickChartTransport
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/NativeFourHWickChartTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Upper-branch phases and normalized Gaussian occupation transport for four even occupations. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedWickChartTransport

/-! The all-even Gaussian occupation comparison on the real overlap.
The identification of the physical fixed-source sewing with these normalized
occupations is a separate step. -/

set_option autoImplicit false

noncomputable section
open scoped BigOperators Matrix

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHWickChartTransport

open Complex (I)
open LatticeGeneratingFieldLocality
open LatticeDiscriminantTheta (gramReal)
open LatticeTwistedGroundRealization.SignQuotient (ModTwoCharge)
open OriginalFourMChargeCoset (fourierSign quadraticSign)
open OriginalFourMActualChart
open OriginalFourMVariableSupport (native_occupation_fourier_overlap)
open NativeMixedWickChartTransport
  (bpzPhase chartMultiplier doubledOccupation gaussian_eq_normalized gaussianOccupation
    laurentPower laurentRoot laurentRoot_values liftedProduct liftedProduct_phases
    normalizedOccupation readoutMultiplier sigma upper_sewing_root)
open private i_pow_three i_zpow_congr periodRoot_A_factor sign_zpow sqrtY sqrtY_ne
  sqrtY_evenPower sqrtOneSubY sqrtOneSubY_ne sqrtOneSubY_sixthPower from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedWickChartTransport

variable {X : Type*}

/-- Each of the four physical punctures has even doubled excitation. -/
def FourHParity (slot : X → Puncture) (n : X → ℕ) (l : List X) : Prop :=
  doubledOccupation slot n l .P % 2 = 0 ∧ doubledOccupation slot n l .Q % 2 = 0 ∧
    doubledOccupation slot n l .R % 2 = 0 ∧ doubledOccupation slot n l .S % 2 = 0

private theorem upper_right_phase (U V O N : ℤ) (E ell : ℕ) (t : ℂ) :
    I ^ (N - O - 2 * ((E : ℤ) + ell)) * (-1 : ℂ) ^ (E : ℤ) * I ^ (V - 2 * U - 3) *
        t ^ (-(6 + U + V)) =
      (-1 : ℂ) ^ (ell : ℤ) * I ^ (3 + 2 * V + N - O - U) * (I * t) ^ (-(6 + U + V)) := by
  simp only [sign_zpow, mul_zpow]
  simp only [← mul_assoc, ← zpow_add₀ Complex.I_ne_zero]
  congr 1
  apply i_zpow_congr
  omega

/-- For B the upper right exponent uses outer grade M and the fixed-source BPZ
pair uses K,L. For D the respective grades are K and M,L. The energy sign
cancels and the output-lowering sign remains when the negative Laurent power
is moved to the actual upper root in each chart. The remaining BPZ exponent
is `3 + 2*L + N - M - K` in both charts. -/
theorem bpzPhase_upper_right {y : ℝ} (hy₁ : y < 1) (M K L N : ℤ) (E ell : ℕ) :
    I ^ (N - M - 2 * ((E : ℤ) + ell)) * (-1 : ℂ) ^ (E : ℤ) * bpzPhase K L M N .A *
        (Real.sqrt y : ℂ) ^ (-laurentPower M K L .B) =
      (-1 : ℂ) ^ (ell : ℤ) * bpzPhase M K L N .B *
        laurentRoot .B y ^ (-laurentPower M K L .B) ∧
    I ^ (N - K - 2 * ((E : ℤ) + ell)) * (-1 : ℂ) ^ (E : ℤ) * bpzPhase M L K N .A *
        ((Real.sqrt y : ℂ)⁻¹) ^ (-laurentPower M K L .D) =
      (-1 : ℂ) ^ (ell : ℤ) * bpzPhase M K L N .D *
        laurentRoot .D y ^ (-laurentPower M K L .D) := by
  obtain ⟨_, hB, hD⟩ := laurentRoot_values hy₁
  constructor
  · rw [hB]
    exact upper_right_phase K L M N E ell (sqrtY y)
  · rw [hD, div_eq_mul_inv]
    simpa only [bpzPhase, laurentPower, sub_right_comm (3+2*L+N) K M] using
      upper_right_phase M L K N E ell (sqrtY y)⁻¹

/-- The all-even conversion factors from normalized occupations to the original
Gaussian Fourier units. The D cubic contributes an extra minus sign. -/
theorem chartMultiplier_eq {y : ℝ} (hy : 0 < y) (hy₁ : y < 1)
    (slot : X → Puncture) (n : X → ℕ) (l : List X) (hpar : FourHParity slot n l) :
    let s := sigma (doubledOccupation slot n l .P) (doubledOccupation slot n l .Q)
      (doubledOccupation slot n l .R) (doubledOccupation slot n l .S)
    let z : ℂ := y
    chartMultiplier slot n l .A y = -I * (1-z)^3 * z^(-s-3) ∧
    chartMultiplier slot n l .B y = -I * (1-z)^3 * z^(3 : ℤ) ∧
    chartMultiplier slot n l .D y = I * (1-z)^3 * z^(-s-3) := by
  let M := doubledOccupation slot n l .P
  let K := doubledOccupation slot n l .Q
  let L := doubledOccupation slot n l .R
  let N := doubledOccupation slot n l .S
  let s := sigma M K L N
  let z : ℂ := y
  let t := sqrtY y
  let u := sqrtOneSubY y
  have hz : z ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have ht : t ≠ 0 := sqrtY_ne hy
  have hu : u ≠ 0 := sqrtOneSubY_ne hy₁
  have hi := Complex.I_ne_zero
  change M % 2 = 0 ∧ K % 2 = 0 ∧ L % 2 = 0 ∧ N % 2 = 0 at hpar
  obtain ⟨hM, hK, hL, hN⟩ := hpar
  have hs : 2*s = 6 + M + K + L - N := by
    change 2 * (3 + (M + K + L - N) / 2) = _
    omega
  have hpA : I ^ (2*M-2*K+3) = -I :=
    (i_zpow_congr (b := 3) (by omega)).trans i_pow_three
  have hpB : I ^ (3+2*K-2*L) = -I :=
    (i_zpow_congr (b := 3) (by omega)).trans i_pow_three
  have hpD : I ^ (3+2*M+2*K-2*N) = -I :=
    (i_zpow_congr (b := 3) (by omega)).trans i_pow_three
  obtain ⟨hprodA, hprodB, hprodD⟩ := liftedProduct_phases hy hy₁ slot n l
  have hA : liftedProduct slot n l .A y * readoutMultiplier M K L N .A y =
      -I * (1-z)^3 * z^(-s) := by
    rw [hprodA]
    change (I^(-K) * u^(-(M+K)) * t^(N-L)) *
      ((u/t)^(6+M+K) * (I^(K-2*M-3))⁻¹) = _
    simp only [div_eq_mul_inv, mul_zpow, inv_zpow', ← zpow_neg]
    calc
      _ = (I^(-K) * I^(-(K-2*M-3))) * (u^(-(M+K)) * u^(6+M+K)) *
          (t^(N-L) * t^(-(6+M+K))) := by ring
      _ = _ := by
        rw [← zpow_add₀ hi, ← zpow_add₀ hu, ← zpow_add₀ ht]
        rw [show -K + -(K-2*M-3) = 2*M-2*K+3 by ring, hpA,
          show -(M+K) + (6+M+K) = 6 by ring, sqrtOneSubY_sixthPower hy₁,
          show N-L + -(6+M+K) = 2*(-s) by omega, sqrtY_evenPower hy]
  have hB : liftedProduct slot n l .B y * readoutMultiplier M K L N .B y =
      -I * z^(3 : ℤ) := by
    rw [hprodB]
    change ((-1 : ℂ)^N * I^(-(M+L+N)) * t^(-(K+L))) *
      ((I*t)^(6+K+L) * (I^(3+2*L+N-M-K))⁻¹) = _
    simp only [sign_zpow, mul_zpow, ← zpow_neg]
    calc
      _ = (I^(2*N) * I^(-(M+L+N)) * I^(6+K+L) * I^(-(3+2*L+N-M-K))) *
          (t^(-(K+L)) * t^(6+K+L)) := by ring
      _ = _ := by
        simp only [← zpow_add₀ hi, ← zpow_add₀ ht]
        rw [show 2*N + -(M+L+N) + (6+K+L) + -(3+2*L+N-M-K) = 3+2*K-2*L by ring,
          hpB, show -(K+L) + (6+K+L) = 2*3 by ring, sqrtY_evenPower hy]
  have hD : liftedProduct slot n l .D y * readoutMultiplier M K L N .D y =
      -I * z^(-s) := by
    rw [hprodD]
    change ((-1 : ℂ)^(K+L) * I^(-(K+L+N)) * t^(N-K)) *
      ((I/t)^(6+M+L) * (I^(3+2*L+N-M-K))⁻¹) = _
    simp only [sign_zpow, div_eq_mul_inv, mul_zpow, inv_zpow', ← zpow_neg]
    calc
      _ = (I^(2*(K+L)) * I^(-(K+L+N)) * I^(6+M+L) * I^(-(3+2*L+N-M-K))) *
          (t^(N-K) * t^(-(6+M+L))) := by ring
      _ = _ := by
        simp only [← zpow_add₀ hi, ← zpow_add₀ ht]
        rw [show 2*(K+L) + -(K+L+N) + (6+M+L) + -(3+2*L+N-M-K) =
            3+2*M+2*K-2*N by ring, hpD,
          show N-K + -(6+M+L) = 2*(-s) by omega, sqrtY_evenPower hy]
  have hzpow : z^(-s) * (z⁻¹)^(3 : ℕ) = z^(-s-3) := by
    rw [← zpow_natCast, inv_zpow', ← zpow_add₀ hz, sub_eq_add_neg]
    rfl
  have dCube : (1 - parameter .D z) ^ (3 : ℕ) = -((1-z)^3 * (z⁻¹)^3) := by
    have hd : 1 - parameter .D z = -((1-z)*z⁻¹) := by
      change 1 - z⁻¹ = _
      field_simp
      ring
    rw [hd]
    ring
  change chartMultiplier slot n l .A y = -I * (1-z)^3 * z^(-s-3) ∧
    chartMultiplier slot n l .B y = -I * (1-z)^3 * z^(3 : ℤ) ∧
    chartMultiplier slot n l .D y = I * (1-z)^3 * z^(-s-3)
  refine ⟨?_, ?_, ?_⟩
  · rw [chartMultiplier, mul_assoc, hA]
    change (1-(1-z⁻¹))^3 * (-I * (1-z)^3 * z^(-s)) = _
    rw [sub_sub_cancel]
    calc
      _ = -I * (1-z)^3 * (z^(-s) * (z⁻¹)^(3 : ℕ)) := by ring
      _ = _ := by rw [hzpow]
  · rw [chartMultiplier, mul_assoc, hB]
    change (1-z)^3 * (-I * z^(3 : ℤ)) = _
    ring
  · rw [chartMultiplier, mul_assoc, hD, dCube]
    calc
      _ = I * (1-z)^3 * (z^(-s) * (z⁻¹)^(3 : ℕ)) := by ring
      _ = _ := by rw [hzpow]

/-- The normalized four-H Gaussian occupation overlap. The B chart has the
quadratic Fourier sum and the D chart has the negative Fourier sum. -/
theorem normalized_occupation_fourier_overlap {X : Type*} [Fintype X] [DecidableEq X]
    (D : LatticeData) (hu : IsUnit D.G.det) (hD : (gramReal D).PosDef) (h24 : D.rank = 24)
    (slot : X → Puncture) (colour : X → Fin D.rank) (n : X → ℕ) (l : List X)
    (hl : l.Nodup) (hpar : FourHParity slot n l)
    {y : ℝ} (hy : (1 / 2 : ℝ) < y) (hy₁ : y < 1) (a : ModTwoCharge D) :
    let s := sigma (doubledOccupation slot n l .P) (doubledOccupation slot n l .Q)
      (doubledOccupation slot n l .R) (doubledOccupation slot n l .S)
    let F := fun c b => normalizedOccupation D slot colour n l c y b
    (2 : ℂ)^(12 : ℕ) * (y : ℂ)^s * F .B a =
      (∑ b, fourierSign D a b * quadraticSign D b * F .A b) ∧
    (2 : ℂ)^(12 : ℕ) * F .D a = -(∑ b, fourierSign D a b * F .A b) := by
  classical
  let s := sigma (doubledOccupation slot n l .P) (doubledOccupation slot n l .Q)
    (doubledOccupation slot n l .R) (doubledOccupation slot n l .S)
  let F := fun c b => normalizedOccupation D slot colour n l c y b
  let V := fun c b =>
    ((1 - parameter c (y : ℂ)) ^ (3 : ℕ) * liftedProduct slot n l c y) *
      gaussianOccupation D slot colour n l c y b
  let z : ℂ := y
  let k : ℂ := (2 : ℂ)^(12 : ℕ)
  let u : ℂ := -I * (1-z)^3 * z^(-s-3)
  let v : ℂ := -I * (1-z)^3 * z^(3 : ℤ)
  let sumB : ℂ := ∑ b, fourierSign D a b * quadraticSign D b * F .A b
  let sumD : ℂ := ∑ b, fourierSign D a b * F .A b
  have hy₀ : 0 < y := by linarith
  have hz : z ≠ 0 := Complex.ofReal_ne_zero.mpr hy₀.ne'
  have hz₁ : 1-z ≠ 0 := by
    change (1 : ℂ) - (y : ℂ) ≠ 0
    exact_mod_cast (sub_pos.mpr hy₁).ne'
  have hk : k ≠ 0 := pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)
  have hu₀ : u ≠ 0 :=
    mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (pow_ne_zero _ hz₁))
      (zpow_ne_zero _ hz)
  have hv₀ : v ≠ 0 :=
    mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (pow_ne_zero _ hz₁))
      (zpow_ne_zero _ hz)
  obtain ⟨_, hwA, hw, _⟩ := upper_sewing_root hy hy₁
  have hover := native_occupation_fourier_overlap D hu hD h24 slot colour
    hy₀ hy₁ hwA hw a n l hl
  change V .D a = k⁻¹ * (∑ b, fourierSign D a b * V .A b) ∧
    V .B a = (periodRoot .A y ^ (12 : ℕ))⁻¹ *
      (k⁻¹ * ∑ b, fourierSign D a b * quadraticSign D b * V .A b) at hover
  have hV (c : Chart) (b : ModTwoCharge D) :
      V c b = chartMultiplier slot n l c y * F c b := by
    dsimp only [V, chartMultiplier, F]
    rw [gaussian_eq_normalized D slot colour n l c hy₀ hy₁ b]
    ring
  obtain ⟨hA, hB, hD'⟩ := chartMultiplier_eq hy₀ hy₁ slot n l hpar
  have sum_A_B : (∑ b, fourierSign D a b * quadraticSign D b * V .A b) = u * sumB := by
    unfold sumB
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hV .A b, hA]
    change _ * (u * F .A b) = u * (_ * F .A b)
    ring
  have sum_A_D : (∑ b, fourierSign D a b * V .A b) = u * sumD := by
    unfold sumD
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hV .A b, hA]
    change _ * (u * F .A b) = u * (_ * F .A b)
    ring
  have hDover : (-u) * F .D a = k⁻¹ * (u * sumD) := by
    have h := hover.1
    rw [hV .D a, hD', sum_A_D] at h
    simpa only [u, neg_mul, neg_neg] using h
  have hBover : v * F .B a = z^(6 : ℤ) * (k⁻¹ * (u * sumB)) := by
    have h := hover.2
    rw [hV .B a, hB, periodRoot_A_factor hy₀, sum_A_B] at h
    exact h
  have hRatio : z^(6 : ℤ) * u = v * z^(-s) := by
    have hpow : z^(6 : ℤ) * z^(-s-3) = z^(3 : ℤ) * z^(-s) := by
      rw [← zpow_add₀ hz, ← zpow_add₀ hz, show (6 : ℤ) + (-s-3) = 3 + -s by ring]
    dsimp only [u, v]
    calc
      _ = (-I * (1-z)^3) * (z^(6 : ℤ) * z^(-s-3)) := by ring
      _ = _ := by rw [hpow]; ring
  change k * z^s * F .B a = sumB ∧ k * F .D a = -sumD
  constructor
  · apply mul_left_cancel₀ (mul_ne_zero hv₀ (zpow_ne_zero (-s) hz))
    have hinv : z^(-s) * z^s = 1 := zpow_neg_mul_zpow_self s hz
    calc
      _ = (z^(-s) * z^s) * (k * (v * F .B a)) := by ring
      _ = k * (v * F .B a) := by rw [hinv, one_mul]
      _ = (k*k⁻¹) * ((z^(6 : ℤ) * u) * sumB) := by rw [hBover]; ac_rfl
      _ = _ := by rw [mul_inv_cancel₀ hk, one_mul, hRatio]
  · apply mul_left_cancel₀ (neg_ne_zero.mpr hu₀)
    calc
      _ = k * ((-u) * F .D a) := by ring
      _ = (k*k⁻¹) * (u * sumD) := by rw [hDover]; ac_rfl
      _ = _ := by rw [mul_inv_cancel₀ hk, one_mul, mul_neg, neg_mul, neg_neg]

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHWickChartTransport
