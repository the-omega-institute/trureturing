/- GID: D5/S3/Weil/Analytic/NymanSignedPrimeBootstrap
   generality: I
   mirror-B: D5/B/S3/Weil/Analytic/NymanSignedPrimeBootstrap
   mirror-E: none(waiver:nyman-signed-prime)
   anchors: []
   utility: none
   digest: An eventual one-sided bound on the centered prime dilation sum characterizes RH. -/

import D5.S3.Weil.Analytic.NymanPrimeDilations
import D5.S3.Weil.Analytic.NymanFixedScalarUpper
import D5.S3.Weil.Analytic.NymanLogCorrectionEnvelope

/-! A signed prime-dilation bound controls the growth of the fixed Nyman scalar. -/

set_option autoImplicit false

noncomputable section

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius

namespace NymanSignedPrimeBootstrap

open NymanPrimeDilations
open NymanFixedRationalKernel (A_pos one_lt_A b b_zero_left b_zero_right continuous_b)

/-- Orient the prime feedback by the sign of the current scalar. -/
def orientation (x : ℝ) : ℝ := if shell x = 0 then 0 else if shell x < 0 then -1 else 1

private theorem orientation_mul_shell (x : ℝ) : orientation x * shell x = |shell x| := by
  unfold orientation
  split_ifs with hz hs
  · simp [hz]
  · rw [neg_one_mul, abs_of_neg hs]
  · rw [one_mul, abs_of_nonneg (le_of_not_gt hs)]

private theorem abs_orientation_le (x : ℝ) : |orientation x| ≤ 1 := by
  unfold orientation
  split_ifs <;> norm_num

/-- The normalized scalar is bounded on every initial segment of the positive ray. -/
private theorem shell_envelope_until (β T : ℝ) (hβ : 0 ≤ β) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, 0 < x → x ≤ T → |shell x| ≤ M * x ^ β := by
  have hB : 0 < B := pow_pos A_pos _
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := B)).bddAbove_image
    continuous_b.abs.continuousOn
  have hb (u : ℝ) : |b u| ≤ max 0 C := by
    by_cases h₁ : u ≤ 1
    · simp [b_zero_left h₁]
    by_cases h₂ : B ≤ u
    · simp [b_zero_right h₂]
    exact (hC ⟨u, ⟨le_of_not_ge h₁, le_of_not_ge h₂⟩, rfl⟩).trans (le_max_right _ _)
  let K : ℝ := (⌊B * T⌋₊ : ℝ) * max 0 C
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K / (1 / B) ^ β, by positivity, fun x hx hxT => ?_⟩
  by_cases hBx : B * x ≤ 1
  · rw [shell_eq_zero_below hx hBx, abs_zero]
    positivity
  have hscale : (1 / B) ^ β ≤ x ^ β :=
    Real.rpow_le_rpow (by positivity) ((div_le_iff₀ hB).mpr (by
      simpa [mul_comm] using (le_of_not_ge hBx : 1 ≤ B * x))) hβ
  have hdiv : 0 < (1 / B) ^ β := Real.rpow_pos_of_pos (by positivity) _
  calc
    |shell x| ≤ ∑ n ∈ Ioc 0 ⌊B * x⌋₊, |(μ n : ℝ) * b ((n : ℝ) / x)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Ioc 0 ⌊B * x⌋₊, max 0 C := by
      refine sum_le_sum fun n _ => ?_
      rw [abs_mul]
      have hμ : |(μ n : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := n)
      simpa using mul_le_mul hμ (hb ((n : ℝ) / x)) (abs_nonneg _) zero_le_one
    _ ≤ K := by
      rw [sum_const, nsmul_eq_mul, Nat.card_Ioc, Nat.sub_zero]
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast Nat.floor_mono (mul_le_mul_of_nonneg_left hxT hB.le))
        (le_max_left _ _)
    _ = (K / (1 / B) ^ β) * (1 / B) ^ β := (div_mul_cancel₀ K hdiv.ne').symm
    _ ≤ (K / (1 / B) ^ β) * x ^ β :=
      mul_le_mul_of_nonneg_left hscale (div_nonneg hK hdiv.le)

/-- The adverse sign of the prime contribution suffices for square-root growth.
The kernel correction needs only a uniform bound relative to the earlier envelope. -/
theorem shell_bound_of_signed_prime {β D A₀ X₀ : ℝ} (hβ : 1 / 2 ≤ β)
    (hD : 0 ≤ D) (hA : 0 ≤ A₀) (hX : 1 ≤ X₀)
    (hP : ∀ x ≥ X₀, -(orientation x * centeredPrimeDilations x) ≤ A₀ * x ^ β * Real.log x)
    (hL : ∀ x ≥ (1 : ℝ), ∀ M ≥ (0 : ℝ),
      (∀ y : ℝ, 0 < y → y ≤ x → |shell y| ≤ M * y ^ β) →
      |logCorrection x| ≤ D * M * x ^ β) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, 0 < x → |shell x| ≤ M * x ^ β := by
  obtain ⟨C, hC, hpower⟩ := abs_higherPowerDilations_le_half_log_add
  let X := max X₀ (Real.exp (4 * (C + D + 1) + 1))
  obtain ⟨K, hK, hsmall⟩ := shell_envelope_until β X (by linarith)
  refine ⟨max K (4 * A₀), hK.trans (le_max_left _ _), fun T hT => ?_⟩
  obtain ⟨J, _, hbound⟩ := shell_envelope_until β T (by linarith)
  let r (x : ℝ) := |shell x| / x ^ β
  let s := r '' (Set.Ioc 0 T)
  have hs : s.Nonempty := ⟨r T, T, ⟨hT, le_rfl⟩, rfl⟩
  have hsJ : BddAbove s := ⟨J, by
    rintro _ ⟨x, hx, rfl⟩
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hx.1 β)).mpr (hbound x hx.1 hx.2)⟩
  let M := sSup s
  have hr (x : ℝ) (hx : 0 < x) (hxT : x ≤ T) : r x ≤ M :=
    le_csSup hsJ ⟨x, ⟨hx, hxT⟩, rfl⟩
  have hM : 0 ≤ M := (div_nonneg (abs_nonneg _) (Real.rpow_nonneg hT.le _)).trans
    (hr T hT le_rfl)
  have hsup : M ≤ max K (A₀ + (3 / 4 : ℝ) * M) := by
    apply csSup_le hs
    rintro _ ⟨x, hx, rfl⟩
    have hxp := Real.rpow_pos_of_pos hx.1 β
    by_cases hxX : x ≤ X
    · exact ((div_le_iff₀ hxp).mpr (hsmall x hx.1 hxX)).trans (le_max_left _ _)
    have hXx := le_of_not_ge hxX
    have hx₁ : 1 ≤ x := hX.trans ((le_max_left _ _).trans hXx)
    have hx₀ : X₀ ≤ x := (le_max_left _ _).trans hXx
    have hlog : 4 * (C + D + 1) + 1 ≤ Real.log x := by
      rw [← Real.log_exp (4 * (C + D + 1) + 1)]
      exact Real.log_le_log (Real.exp_pos _) ((le_max_right _ _).trans hXx)
    have hlogpos : 0 < Real.log x := by linarith
    have hfeedback : C + D + 1 ≤ Real.log x / 4 := by linarith
    have henvelope (y : ℝ) (hy : 0 < y) (hyx : y ≤ x) : |shell y| ≤ M * y ^ β :=
      (div_le_iff₀ (Real.rpow_pos_of_pos hy β)).mp (hr y hy (hyx.trans hx.2))
    have hsplit := congrArg (fun z : ℝ => orientation x * z) (moebius_log_split hx.1)
    have hidentity : Real.log x * |shell x| =
        -(orientation x * centeredPrimeDilations x) - orientation x * higherPowerDilations x -
          orientation x * logCorrection x + |shell x| := by
      calc
        _ = orientation x * (Real.log x * shell x + logCorrection x) -
              orientation x * logCorrection x := by rw [← orientation_mul_shell]; ring
        _ = _ := by
          rw [hsplit, ← primeDilations_add_shell_eq_centered hx₁, ← orientation_mul_shell]
          ring
    have hf (u : ℝ) : -(orientation x * u) ≤ |u| := by
      calc
        _ ≤ |orientation x * u| := neg_le_abs _
        _ ≤ _ := by
          rw [abs_mul]
          exact mul_le_of_le_one_left (abs_nonneg _) (abs_orientation_le x)
    have hpow := (hf (higherPowerDilations x)).trans (hpower x hx₁ β hβ M hM henvelope)
    have hcor := (hf (logCorrection x)).trans (hL x hx₁ M hM henvelope)
    have hadd := add_le_add (add_le_add (add_le_add (hP x hx₀) hpow) hcor)
      (henvelope x hx.1 le_rfl)
    have hsum : Real.log x * |shell x| ≤
        (A₀ + (3 / 4 : ℝ) * M) * x ^ β * Real.log x := by
      calc
        _ ≤ A₀ * x ^ β * Real.log x + M * x ^ β * (Real.log x / 2 + C) +
              D * M * x ^ β + M * x ^ β := by
          rw [hidentity]
          linarith only [hadd]
        _ = A₀ * x ^ β * Real.log x + M * x ^ β * (Real.log x / 2 + (C + D + 1)) := by
          ring
        _ ≤ A₀ * x ^ β * Real.log x + M * x ^ β * (Real.log x / 2 + Real.log x / 4) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add le_rfl hfeedback)
            (mul_nonneg hM hxp.le))
        _ = _ := by ring
    have hlocal : r x ≤ A₀ + (3 / 4 : ℝ) * M := by
      apply (div_le_iff₀ hxp).mpr
      apply le_of_mul_le_mul_right _ hlogpos
      simpa only [mul_comm (Real.log x) |shell x|] using hsum
    exact hlocal.trans (le_max_right _ _)
  have hfinal : M ≤ max K (4 * A₀) := by
    by_cases hMK : M ≤ K
    · exact hMK.trans (le_max_left _ _)
    · exact (show M ≤ 4 * A₀ by
        have hm : M ≤ A₀ + (3 / 4 : ℝ) * M := by
          rcases le_max_iff.mp hsup with h | h
          · exact False.elim (hMK h)
          · exact h
        linarith).trans (le_max_right _ _)
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hT β)).mp ((hr T hT le_rfl).trans hfinal)

private theorem shell_eq_scaled {x : ℝ} (hx : 0 < x) :
    (shell x : ℂ) = NymanShellMellin.scaled (fun u => (b u : ℂ)) x⁻¹ := by
  unfold NymanShellMellin.scaled
  rw [tsum_eq_sum (s := Ioc 0 ⌊B * x⌋₊)]
  · unfold shell
    push_cast
    <;> simp only [div_eq_mul_inv]
  · intro n hn
    have hb : b ((n : ℝ) * x⁻¹) = 0 := by
      by_cases hn₀ : n = 0
      · exact b_zero_left (by simp [hn₀])
      have hcut : ⌊B * x⌋₊ < n := lt_of_not_ge fun hle =>
        hn (mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hn₀, hle⟩)
      rw [← div_eq_mul_inv]
      exact b_zero_right ((le_div_iff₀ hx).mpr (Nat.lt_of_floor_lt hcut).le)
    simp [hb]

private theorem shell_envelope_of_scalar
    (hS : NymanFixedRationalScalar.ScalarSquareRoot) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, 0 < x → |shell x| ≤ M * x ^ (1 / 2 + ε) := by
  obtain ⟨C, hC, hCbound⟩ := hS ε hε
  obtain ⟨K, hK, hKlip⟩ := NymanFixedRationalKernel.b_lipschitz
  have hβ : 0 ≤ (1 / 2 : ℝ) + ε := by linarith
  obtain ⟨D, hD, hSmall⟩ := shell_envelope_until (1 / 2 + ε) 1 hβ
  refine ⟨max D (C + 10 * K), hD.trans (le_max_left _ _), fun x hx => ?_⟩
  have hxp : 0 ≤ x ^ ((1 / 2 : ℝ) + ε) := Real.rpow_nonneg hx.le _
  by_cases hx₁ : x ≤ 1
  · exact (hSmall x hx hx₁).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hxp)
  have hxOne : 1 ≤ x := le_of_not_ge hx₁
  let N := ⌊x⌋₊
  have hN : 0 < N := Nat.le_floor (by simpa using hxOne)
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hNlo : (N : ℝ) ≤ x := Nat.floor_le hx.le
  have hNhi : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  have hW : ∀ u ∉ Set.Ioo (1 : ℝ) 2, (b u : ℂ) = 0 := by
    intro u hu
    simp [NymanFixedRationalKernel.b_zero_off u hu]
  have hLip : ∀ u v : ℝ, ‖(b u : ℂ) - (b v : ℂ)‖ ≤ K * |u - v| := by
    intro u v
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hKlip u v
  have hdiff := NymanShellScale.scale_difference hW hK hLip hN
    ((inv_le_inv₀ (by positivity : 0 < (N : ℝ) + 1) hx).2 hNhi.le)
    ((inv_le_inv₀ hx hNpos).2 hNlo)
  rw [← shell_eq_scaled hx, ← NymanFixedRationalScalar.scalar_eq_scaled hN,
    ← Complex.ofReal_ratCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hdiff
  have hpow := Real.rpow_le_rpow hNpos.le hNlo hβ
  have hpowOne := Real.one_le_rpow hxOne hβ
  calc
    |shell x| ≤ |shell x - (NymanFixedRationalScalar.scalar N : ℝ)| +
        |(NymanFixedRationalScalar.scalar N : ℝ)| := by
      simpa only [sub_add_cancel] using
        (abs_add_le (shell x - (NymanFixedRationalScalar.scalar N : ℝ))
          (NymanFixedRationalScalar.scalar N : ℝ))
    _ ≤ 10 * K + C * (N : ℝ) ^ (1 / 2 + ε) := add_le_add hdiff (hCbound N hN)
    _ ≤ (10 * K) * x ^ (1 / 2 + ε) + C * x ^ (1 / 2 + ε) := by
      apply add_le_add
      · simpa only [mul_one] using mul_le_mul_of_nonneg_left hpowOne (by positivity : 0 ≤ 10 * K)
      · exact mul_le_mul_of_nonneg_left hpow hC
    _ = (C + 10 * K) * x ^ (1 / 2 + ε) := by ring
    _ ≤ max D (C + 10 * K) * x ^ (1 / 2 + ε) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hxp

/-- Only the part of the prime feedback adverse to the sign of the shell enters
the square-root criterion. -/
def SignedPrimeSquareRoot : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ A₀ X₀ : ℝ, 0 ≤ A₀ ∧ 1 ≤ X₀ ∧ ∀ x ≥ X₀,
    -(orientation x * centeredPrimeDilations x) ≤ A₀ * x ^ (1 / 2 + ε) * Real.log x

private theorem signedPrimeSquareRoot_of_rh (hRH : RiemannHypothesis) : SignedPrimeSquareRoot := by
  intro ε hε
  let β : ℝ := 1 / 2 + ε
  have hβ : 1 / 2 ≤ β := by dsimp [β]; linarith
  obtain ⟨M, hM, hEnv⟩ := shell_envelope_of_scalar
    (NymanFixedScalarUpper.rh_iff_scalar.mp hRH) hε
  obtain ⟨C, hC, hPow⟩ := abs_higherPowerDilations_le_half_log_add
  let D : ℝ := 4 * NymanKernelConvolution.h + 16
  have hD : 0 ≤ D := by dsimp [D]; linarith [NymanKernelConvolution.h_pos]
  refine ⟨(3 / 2 + C + D) * M, Real.exp 1, by positivity, Real.one_le_exp (by norm_num),
    fun x hx => ?_⟩
  have hxOne : 1 ≤ x := (Real.one_le_exp (by norm_num)).trans hx
  have hx₀ : 0 < x := zero_lt_one.trans_le hxOne
  have hlog : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _) hx
  have hEnvAt (y : ℝ) (hy : 0 < y) (_ : y ≤ x) : |shell y| ≤ M * y ^ β :=
    hEnv y hy
  have horient (u : ℝ) : orientation x * u ≤ |u| := by
    calc
      _ ≤ |orientation x * u| := le_abs_self _
      _ ≤ _ := by
        rw [abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) (abs_orientation_le x)
  have hident : -(orientation x * primeDilations x) = Real.log x * |shell x| +
      orientation x * higherPowerDilations x + orientation x * logCorrection x := by
    have hs := congrArg (fun z : ℝ => orientation x * z) (moebius_log_split hx₀)
    calc
      _ = orientation x * (-(primeDilations x + higherPowerDilations x)) +
          orientation x * higherPowerDilations x := by ring
      _ = orientation x * (Real.log x * shell x + logCorrection x) +
          orientation x * higherPowerDilations x := by rw [← hs]
      _ = _ := by rw [← orientation_mul_shell]; ring
  have hp := (horient _).trans (hPow x hxOne β hβ M hM hEnvAt)
  have hc := (horient _).trans (NymanLogCorrection.abs_logCorrection_le_envelope hx₀ hβ hM hEnvAt)
  have hCD : C + D ≤ (C + D) * Real.log x := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hlog (add_nonneg hC hD)
  calc
    -(orientation x * centeredPrimeDilations x) ≤ -(orientation x * primeDilations x) := by
      rw [← primeDilations_add_shell_eq_centered hxOne, mul_add, orientation_mul_shell]
      linarith [abs_nonneg (shell x)]
    _ = Real.log x * |shell x| +
      orientation x * higherPowerDilations x + orientation x * logCorrection x := hident
    _ ≤ Real.log x * (M * x ^ β) + M * x ^ β * (Real.log x / 2 + C) +
        D * M * x ^ β := add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left (hEnvAt x hx₀ le_rfl) (by linarith)) hp) hc
    _ = Real.log x * (M * x ^ β) + (M * x ^ β) * (Real.log x / 2 + (C + D)) := by ring
    _ ≤ Real.log x * (M * x ^ β) +
        (M * x ^ β) * (Real.log x / 2 + (C + D) * Real.log x) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add le_rfl hCD)
        (mul_nonneg hM (Real.rpow_nonneg hx₀.le _)))
    _ = _ := by ring

/-- The fixed kernel gives an exact Riemann hypothesis criterion involving the
adverse signed prime feedback at real scales. -/
theorem rh_iff_signedPrimeSquareRoot : RiemannHypothesis ↔ SignedPrimeSquareRoot := by
  refine ⟨signedPrimeSquareRoot_of_rh, fun hP => NymanFixedRationalScalar.rh_of_scalar ?_⟩
  intro ε hε
  obtain ⟨A₀, X₀, hA, hX, hPX⟩ := hP ε hε
  have hβ : (1 / 2 : ℝ) ≤ 1 / 2 + ε := by linarith
  let D : ℝ := 4 * NymanKernelConvolution.h + 16
  have hD : 0 ≤ D := by dsimp [D]; linarith [NymanKernelConvolution.h_pos]
  obtain ⟨M, hM, hShell⟩ := shell_bound_of_signed_prime hβ hD hA hX hPX
    (fun x hx M hM hEnv => NymanLogCorrection.abs_logCorrection_le_envelope
      (zero_lt_one.trans_le hx) hβ hM hEnv)
  refine ⟨M, hM, fun N hN => ?_⟩
  rw [← shell_nat_eq_scalar hN]
  exact hShell N (by exact_mod_cast hN)

end NymanSignedPrimeBootstrap

#print axioms NymanSignedPrimeBootstrap.rh_iff_signedPrimeSquareRoot
