/- GID: D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation
   generality: I
   mirror-B: D5/B/S3/Estimation/TransmissivityBetaPriorProbeRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.claim; result=D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.result; claim=D5/S3/Estimation/TransmissivityBetaPriorProbeRefutation.claim
   digest: Refute phased in-between-state optimality for beta-prior transmissivity sensing. -/

import D5.S3.Estimation.TransmissivityTwoPointProbeRefutation
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Matrix MeasureTheory
open scoped BigOperators ComplexOrder
open D5.S3.Estimation.TransmissivityTwoPointProbeRefutation
open D5.S3.Quantum.PureState.PureStateHandshake
open D5.S3.Quantum.QuantumChannels.TruncatedLossDephasingOptimizerRefutation

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation

noncomputable def betaDensity (α β τ : ℝ) : ℝ :=
  τ ^ (α - 1) * (1 - τ) ^ (β - 1) /
    (Real.Gamma α * Real.Gamma β / Real.Gamma (α + β))

noncomputable def momentBeta {N : ℕ} (α β : ℝ) (ψ : Fin (N + 1) → ℂ)
    (k : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  fun i j => ∫ τ in (0 : ℝ)..1,
    ((betaDensity α β τ * τ ^ k : ℝ) : ℂ) * outputState τ ψ i j

noncomputable def bayesianRiskBeta {N m : ℕ} (α β : ℝ) (ψ : Fin (N + 1) → ℂ)
    (E : Fin m → Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (x : Fin m → ℝ) : ℝ :=
  ∑ k, (E k * (((x k ^ 2 : ℝ) : ℂ) • momentBeta α β ψ 0 -
    (((2 * x k : ℝ) : ℂ) • momentBeta α β ψ 1) + momentBeta α β ψ 2)).trace.re

noncomputable def MMSEBeta {N : ℕ} (α β : ℝ) (ψ : Fin (N + 1) → ℂ) : ℝ :=
  sInf {r : ℝ | ∃ (m : ℕ) (E : Fin m → Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (x : Fin m → ℝ), finitePOVM E ∧ r = bayesianRiskBeta α β ψ E x}

def claim : Prop :=
  ∀ (α β nbar : ℝ), 0 < α → 0 < β → 0 < nbar →
    ∀ (N : ℕ) (ψ : Fin (N + 1) → ℂ), ‖WithLp.toLp 2 ψ‖ = 1 → meanPhoton ψ = nbar →
      ∃ φ : ℝ, MMSEBeta α β (inBetween nbar φ) ≤ MMSEBeta α β ψ

theorem result : ¬ claim := by
  classical
  have density (τ : ℝ) : betaDensity 3 1 τ = 3 * τ ^ 2 := by
    have g3 : Real.Gamma 3 = 2 := by
      convert Real.Gamma_nat_eq_factorial 2 using 1 <;> norm_num
    have g4 : Real.Gamma 4 = 6 := by
      convert Real.Gamma_nat_eq_factorial 3 using 1 <;> norm_num
    unfold betaDensity
    simp only [show (3 : ℝ) - 1 = 2 by norm_num,
      show (1 : ℝ) - 1 = 0 by norm_num, show (3 : ℝ) + 1 = 4 by norm_num,
      Real.rpow_zero, Real.Gamma_one, g3, g4, mul_one]
    rw [show τ ^ (2 : ℝ) = τ ^ (2 : ℕ) from Real.rpow_natCast τ 2]
    ring
  have ipow (n : ℕ) : (∫ τ in (0 : ℝ)..1, (τ : ℂ)^n) = 1 / (n + 1 : ℂ) := by
    simp only [← Complex.ofReal_pow, intervalIntegral.integral_ofReal,
      integral_pow, one_pow, zero_pow (Nat.succ_ne_zero n), sub_zero]
    push_cast
    rfl
  have cpow (n : ℕ) (a : ℂ) :
      IntervalIntegrable (fun τ : ℝ => a * (τ : ℂ)^n) volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have poly (a b c : ℂ) (n : ℕ) :
      (∫ τ in (0 : ℝ)..1,
        a * (τ : ℂ)^(n+2) + b * (τ : ℂ)^(n+3) + c * (τ : ℂ)^(n+4)) =
      a / (n+3 : ℂ) + b / (n+4 : ℂ) + c / (n+5 : ℂ) := by
    rw [intervalIntegral.integral_add ((cpow _ _).add (cpow _ _)) (cpow _ _),
      intervalIntegral.integral_add (cpow _ _) (cpow _ _)]
    simp only [intervalIntegral.integral_const_mul, ipow]
    push_cast
    ring
  have halfpow (n : ℕ) (a : ℂ) :
      (∫ τ in (0 : ℝ)..1, a * (τ : ℂ)^(n+2) * (Real.sqrt τ : ℂ)) =
        a / ((n : ℂ) + 7/2) := by
    have h : (∫ τ in (0 : ℝ)..1, (τ : ℂ)^(n+2) * (Real.sqrt τ : ℂ)) =
        ∫ τ in (0 : ℝ)..1, ((τ ^ ((n : ℝ) + 5/2) : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro τ hτ
      have ht : 0 ≤ τ := by simpa using hτ.1
      dsimp only
      rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Real.sqrt_eq_rpow,
        ← Real.rpow_natCast, ← Real.rpow_add_of_nonneg ht (by positivity) (by norm_num)]
      congr 2
      push_cast
      ring
    simp_rw [mul_assoc a]
    rw [intervalIntegral.integral_const_mul, h, intervalIntegral.integral_ofReal,
      integral_rpow (Or.inl (by linarith [Nat.cast_nonneg (α := ℝ) n] : -1 < (n : ℝ) + 5/2))]
    rw [Real.one_rpow, Real.zero_rpow (by positivity : (n : ℝ) + 5/2 + 1 ≠ 0)]
    push_cast
    ring
  have chi_moments (z : ℂ) (hz : z * star z = 1) (k : ℕ) :
      let χ : Fin 2 → ℂ := ![(Real.sqrt 3 : ℂ)/2, z/2]
      momentBeta 3 1 χ k =
        !![3/(k+3 : ℂ) - 3/(4*(k+4 : ℂ)),
           (3*(Real.sqrt 3 : ℂ)/(4*(k : ℂ)+14)) * star z;
           (3*(Real.sqrt 3 : ℂ)/(4*(k : ℂ)+14)) * z, 3/(4*(k+4 : ℂ))] := by
    dsimp only
    let χ : Fin 2 → ℂ := ![(Real.sqrt 3 : ℂ)/2, z/2]
    have h3 : (Real.sqrt 3 : ℂ)^2 = 3 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
    have hz₁ : z * (starRingEnd ℂ) z = 1 := hz
    have hz₂ : (starRingEnd ℂ) z * z = 1 := by simpa only [mul_comm] using hz₁
    have rho (τ : ℝ) (hτ : τ ∈ Set.Icc 0 1) : outputState τ χ =
        !![1-(τ : ℂ)/4, (Real.sqrt 3 : ℂ)*(Real.sqrt τ : ℂ)/4 * star z;
           (Real.sqrt 3 : ℂ)*(Real.sqrt τ : ℂ)/4 * z, (τ : ℂ)/4] := by
      have ht : (Real.sqrt τ : ℂ)^2 = (τ : ℂ) := by
        rw [← Complex.ofReal_pow, Real.sq_sqrt hτ.1]
      have htm : (Real.sqrt (1-τ) : ℂ)^2 = 1-(τ : ℂ) := by
        rw [← Complex.ofReal_pow, Real.sq_sqrt (sub_nonneg.mpr hτ.2)]
        push_cast
        rfl
      simp only [outputState, sourceKraus _ _ hτ, source_coefficient _ _ _ hτ]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.of_apply, χ, Matrix.mul_apply, Fin.sum_univ_succ,
          vecMulVec_apply, rankOneDensity, conjTranspose_apply, Pi.star_apply,
          RCLike.star_def, Complex.conj_ofReal, map_mul, map_ofNat, map_div₀] <;>
        (try ring_nf) <;> (try simp only [h3, ht, htm]) <;> (try ring_nf) <;>
        (try simp only [mul_assoc (τ : ℂ) z, hz₁, hz₂, mul_one]) <;>
        (first | rfl | ring)
    have diag0 : momentBeta 3 1 χ k 0 0 = 3/(k+3 : ℂ)-3/(4*(k+4 : ℂ)) := by
      unfold momentBeta
      trans ∫ τ in (0 : ℝ)..1,
        3*(τ : ℂ)^(k+2) + (-3/4)*(τ : ℂ)^(k+3) + 0*(τ : ℂ)^(k+4)
      · apply intervalIntegral.integral_congr
        intro τ hτ
        have ht : τ ∈ Set.Icc 0 1 := by simpa using hτ
        dsimp only
        rw [density, rho τ ht]
        norm_num <;> push_cast <;> simp only [pow_add] <;> (first | rfl | ring)
      · rw [poly]
        simp only [div_mul_eq_div_div]
        ring
    have diag1 : momentBeta 3 1 χ k 1 1 = 3/(4*(k+4 : ℂ)) := by
      unfold momentBeta
      trans ∫ τ in (0 : ℝ)..1,
        0*(τ : ℂ)^(k+2) + (3/4)*(τ : ℂ)^(k+3) + 0*(τ : ℂ)^(k+4)
      · apply intervalIntegral.integral_congr
        intro τ hτ
        have ht : τ ∈ Set.Icc 0 1 := by simpa using hτ
        dsimp only
        rw [density, rho τ ht]
        norm_num <;> push_cast <;> simp only [pow_add] <;> (first | rfl | ring)
      · rw [poly]
        simp only [div_mul_eq_div_div]
        ring
    have off (i j : Fin 2) (w : ℂ)
        (hr : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
          outputState τ χ i j = (Real.sqrt 3 : ℂ)*(Real.sqrt τ : ℂ)/4*w) :
        momentBeta 3 1 χ k i j = (3*(Real.sqrt 3 : ℂ)/(4*(k : ℂ)+14))*w := by
      unfold momentBeta
      trans ∫ τ in (0 : ℝ)..1,
        (3*(Real.sqrt 3 : ℂ)*w/4) * (τ : ℂ)^(k+2) * (Real.sqrt τ : ℂ)
      · apply intervalIntegral.integral_congr
        intro τ hτ
        have ht : τ ∈ Set.Icc 0 1 := by simpa using hτ
        dsimp only
        rw [density, hr τ ht]
        push_cast
        simp only [pow_add]
        ring
      · rw [halfpow]
        rw [show 4*(k : ℂ)+14 = 4*((k : ℂ)+7/2) by ring]
        simp only [div_mul_eq_div_div]
        ring
    ext i j
    fin_cases i <;> fin_cases j
    · exact diag0
    · exact off 0 1 (star z) (by intro τ hτ; rw [rho τ hτ]; rfl)
    · exact off 1 0 z (by intro τ hτ; rw [rho τ hτ]; rfl)
    · exact diag1
  have psi_moments (k : ℕ) :
      let ψ : Fin 3 → ℂ := ![(Real.sqrt 14 : ℂ)/4, 0, (Real.sqrt 2 : ℂ)/4]
      momentBeta 3 1 ψ k =
        !![3/(k+3 : ℂ)-3/(4*(k+4 : ℂ))+3/(8*(k+5 : ℂ)), 0,
             3*(Real.sqrt 7 : ℂ)/(8*(k+4 : ℂ));
           0, 3/(4*(k+4 : ℂ))-3/(4*(k+5 : ℂ)), 0;
           3*(Real.sqrt 7 : ℂ)/(8*(k+4 : ℂ)), 0, 3/(8*(k+5 : ℂ))] := by
    dsimp only
    let ψ : Fin 3 → ℂ := ![(Real.sqrt 14 : ℂ)/4, 0, (Real.sqrt 2 : ℂ)/4]
    have h14 : (Real.sqrt 14 : ℂ)^2 = 14 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 14)]
      norm_num
    have h2 : (Real.sqrt 2 : ℂ)^2 = 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have hFin12 : (1 : Fin 3) ≤ 2 := by decide
    have h24 : (Real.sqrt 2 : ℂ)^4 = 4 := by
      calc (Real.sqrt 2 : ℂ)^4 = ((Real.sqrt 2 : ℂ)^2)^2 := by ring
           _ = 4 := by rw [h2]; norm_num
    have hprod : (Real.sqrt 14 : ℂ)*(Real.sqrt 2 : ℂ) = 2*(Real.sqrt 7 : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 14),
        show (14 : ℝ)*2 = 4*7 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    have rho (τ : ℝ) (hτ : τ ∈ Set.Icc 0 1) : outputState τ ψ =
        !![1-(τ : ℂ)/4+(τ : ℂ)^2/8, 0, (Real.sqrt 7 : ℂ)*(τ : ℂ)/8;
           0, (τ : ℂ)/4-(τ : ℂ)^2/4, 0;
           (Real.sqrt 7 : ℂ)*(τ : ℂ)/8, 0, (τ : ℂ)^2/8] := by
      have ht : (Real.sqrt τ : ℂ)^2 = (τ : ℂ) := by
        rw [← Complex.ofReal_pow, Real.sq_sqrt hτ.1]
      have htm : (Real.sqrt (1-τ) : ℂ)^2 = 1-(τ : ℂ) := by
        rw [← Complex.ofReal_pow, Real.sq_sqrt (sub_nonneg.mpr hτ.2)]
        push_cast
        rfl
      have ht4 : (Real.sqrt τ : ℂ)^4 = (τ : ℂ)^2 := by
        calc (Real.sqrt τ : ℂ)^4 = ((Real.sqrt τ : ℂ)^2)^2 := by ring
             _ = (τ : ℂ)^2 := by rw [ht]
      have htm4 : (Real.sqrt (1-τ) : ℂ)^4 = (1-(τ : ℂ))^2 := by
        calc (Real.sqrt (1-τ) : ℂ)^4 = ((Real.sqrt (1-τ) : ℂ)^2)^2 := by ring
             _ = (1-(τ : ℂ))^2 := by rw [htm]
      simp only [outputState, sourceKraus _ _ hτ, source_coefficient _ _ _ hτ]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.of_apply, ψ, Matrix.mul_apply, Fin.sum_univ_succ,
          vecMulVec_apply, rankOneDensity, conjTranspose_apply, Pi.star_apply,
          RCLike.star_def, Complex.conj_ofReal, map_mul, map_ofNat, map_div₀, hFin12] <;>
        (try ring_nf) <;> (try simp only [h14, h2, h24, ht, htm, ht4, htm4]) <;> (try ring_nf) <;>
        (try ring) <;> linear_combination hprod * ((τ : ℂ)/16)
    ext i j
    fin_cases i <;> fin_cases j
    · unfold momentBeta
      trans ∫ τ in (0 : ℝ)..1,
        (3)*(τ : ℂ)^(k+2) + (-3/4)*(τ : ℂ)^(k+3) + (3/8)*(τ : ℂ)^(k+4)
      · apply intervalIntegral.integral_congr
        intro τ hτ
        have ht : τ ∈ Set.Icc 0 1 := by simpa using hτ
        dsimp only
        rw [density, rho τ ht]
        norm_num <;> push_cast <;> simp only [pow_add] <;> ring
      · rw [poly]
        norm_num <;> simp only [div_mul_eq_div_div] <;> ring
    · unfold momentBeta
      trans ∫ τ in (0 : ℝ)..1,
        (0)*(τ : ℂ)^(k+2) + (0)*(τ : ℂ)^(k+3) + (0)*(τ : ℂ)^(k+4)
      · apply intervalIntegral.integral_congr
        intro τ hτ
        have ht : τ ∈ Set.Icc 0 1 := by simpa using hτ
        dsimp only
        rw [density, rho τ ht]
        norm_num <;> push_cast <;> simp only [pow_add] <;> ring
      · rw [poly]
        norm_num <;> simp only [div_mul_eq_div_div] <;> ring
    · unfold momentBeta
      trans ∫ τ in (0 : ℝ)..1,
        (0)*(τ : ℂ)^(k+2) + (3*(Real.sqrt 7 : ℂ)/8)*(τ : ℂ)^(k+3) + (0)*(τ : ℂ)^(k+4)
      · apply intervalIntegral.integral_congr
        intro τ hτ
        have ht : τ ∈ Set.Icc 0 1 := by simpa using hτ
        dsimp only
        rw [density, rho τ ht]
        norm_num <;> push_cast <;> simp only [pow_add] <;> ring
      · rw [poly]
        norm_num <;> simp only [div_mul_eq_div_div] <;> ring
    · unfold momentBeta
      trans ∫ τ in (0 : ℝ)..1,
        (0)*(τ : ℂ)^(k+2) + (0)*(τ : ℂ)^(k+3) + (0)*(τ : ℂ)^(k+4)
      · apply intervalIntegral.integral_congr
        intro τ hτ
        have ht : τ ∈ Set.Icc 0 1 := by simpa using hτ
        dsimp only
        rw [density, rho τ ht]
        norm_num <;> push_cast <;> simp only [pow_add] <;> ring
      · rw [poly]
        norm_num <;> simp only [div_mul_eq_div_div] <;> ring
    · unfold momentBeta
      trans ∫ τ in (0 : ℝ)..1,
        (0)*(τ : ℂ)^(k+2) + (3/4)*(τ : ℂ)^(k+3) + (-3/4)*(τ : ℂ)^(k+4)
      · apply intervalIntegral.integral_congr
        intro τ hτ
        have ht : τ ∈ Set.Icc 0 1 := by simpa using hτ
        dsimp only
        rw [density, rho τ ht]
        norm_num <;> push_cast <;> simp only [pow_add] <;> ring
      · rw [poly]
        norm_num <;> simp only [div_mul_eq_div_div] <;> ring
    · unfold momentBeta
      trans ∫ τ in (0 : ℝ)..1,
        (0)*(τ : ℂ)^(k+2) + (0)*(τ : ℂ)^(k+3) + (0)*(τ : ℂ)^(k+4)
      · apply intervalIntegral.integral_congr
        intro τ hτ
        have ht : τ ∈ Set.Icc 0 1 := by simpa using hτ
        dsimp only
        rw [density, rho τ ht]
        norm_num <;> push_cast <;> simp only [pow_add] <;> ring
      · rw [poly]
        norm_num <;> simp only [div_mul_eq_div_div] <;> ring
    · unfold momentBeta
      trans ∫ τ in (0 : ℝ)..1,
        (0)*(τ : ℂ)^(k+2) + (3*(Real.sqrt 7 : ℂ)/8)*(τ : ℂ)^(k+3) + (0)*(τ : ℂ)^(k+4)
      · apply intervalIntegral.integral_congr
        intro τ hτ
        have ht : τ ∈ Set.Icc 0 1 := by simpa using hτ
        dsimp only
        rw [density, rho τ ht]
        norm_num <;> push_cast <;> simp only [pow_add] <;> ring
      · rw [poly]
        norm_num <;> simp only [div_mul_eq_div_div] <;> ring
    · unfold momentBeta
      trans ∫ τ in (0 : ℝ)..1,
        (0)*(τ : ℂ)^(k+2) + (0)*(τ : ℂ)^(k+3) + (0)*(τ : ℂ)^(k+4)
      · apply intervalIntegral.integral_congr
        intro τ hτ
        have ht : τ ∈ Set.Icc 0 1 := by simpa using hτ
        dsimp only
        rw [density, rho τ ht]
        norm_num <;> push_cast <;> simp only [pow_add] <;> ring
      · rw [poly]
        norm_num <;> simp only [div_mul_eq_div_div] <;> ring
    · unfold momentBeta
      trans ∫ τ in (0 : ℝ)..1,
        (0)*(τ : ℂ)^(k+2) + (0)*(τ : ℂ)^(k+3) + (3/8)*(τ : ℂ)^(k+4)
      · apply intervalIntegral.integral_congr
        intro τ hτ
        have ht : τ ∈ Set.Icc 0 1 := by simpa using hτ
        dsimp only
        rw [density, rho τ ht]
        norm_num <;> push_cast <;> simp only [pow_add] <;> ring
      · rw [poly]
        norm_num <;> simp only [div_mul_eq_div_div] <;> ring
  have bounds {N : ℕ} (ψ : Fin (N+1) → ℂ)
      (B : Matrix (Fin (N+1)) (Fin (N+1)) ℂ)
      (hA : (momentBeta 3 1 ψ 0).PosSemidef) (hB : B.IsHermitian)
      (hsol : momentBeta 3 1 ψ 0 * B + B * momentBeta 3 1 ψ 0 =
        (2 : ℂ) • momentBeta 3 1 ψ 1) :
      ((momentBeta 3 1 ψ 2).trace - (B * momentBeta 3 1 ψ 1).trace).re ≤
          MMSEBeta 3 1 ψ ∧
        MMSEBeta 3 1 ψ ≤
          ((momentBeta 3 1 ψ 2).trace - (B * momentBeta 3 1 ψ 1).trace).re := by
    let L := ((momentBeta 3 1 ψ 2).trace - (B * momentBeta 3 1 ψ 1).trace).re
    have bound {m : ℕ} (E : Fin m → Matrix (Fin (N+1)) (Fin (N+1)) ℂ)
        (x : Fin m → ℝ) (hE : finitePOVM E) : L ≤ bayesianRiskBeta 3 1 ψ E x :=
      risk_lower_bound _ _ _ B hA hB hsol E x hE
    have nonempty : {r : ℝ | ∃ (m : ℕ)
        (E : Fin m → Matrix (Fin (N+1)) (Fin (N+1)) ℂ)
        (x : Fin m → ℝ), finitePOVM E ∧ r = bayesianRiskBeta 3 1 ψ E x}.Nonempty := by
      let E : Fin 1 → Matrix (Fin (N+1)) (Fin (N+1)) ℂ := fun _ => 1
      let x : Fin 1 → ℝ := fun _ => 0
      refine ⟨bayesianRiskBeta 3 1 ψ E x, 1, E, x, ?_, rfl⟩
      exact ⟨fun _ => PosSemidef.one, by simp [E]⟩
    constructor
    · unfold MMSEBeta
      apply le_csInf nonempty
      rintro r ⟨m, E, x, hE, rfl⟩
      exact bound E x hE
    · unfold MMSEBeta
      apply csInf_le
      · refine ⟨L, ?_⟩
        rintro r ⟨m, E, x, hE, rfl⟩
        exact bound E x hE
      · obtain ⟨E, x, hE, heq⟩ := spectral_attainment
          (momentBeta 3 1 ψ 0) (momentBeta 3 1 ψ 1) (momentBeta 3 1 ψ 2) B hB hsol
        exact ⟨N+1, E, x, hE, heq.symm⟩

  have chi_lower (φ : ℝ) : 167/4575 ≤ MMSEBeta 3 1 (inBetween (1/4) φ) := by
    let z := Complex.exp (Complex.I * (φ : ℂ))
    let χ : Fin 2 → ℂ := ![(Real.sqrt 3 : ℂ)/2, z/2]
    let B : Matrix (Fin 2) (Fin 2) ℂ :=
      !![216/305, 7*(Real.sqrt 3 : ℂ)/183 * star z;
         7*(Real.sqrt 3 : ℂ)/183 * z, 204/305]
    have hz : z * star z = 1 := by
      dsimp [z]
      rw [← Complex.exp_conj, ← Complex.exp_add]
      have he : Complex.I * (φ : ℂ) + star (Complex.I * (φ : ℂ)) = 0 := by simp
      simpa [he]
    have hz₁ : z * (starRingEnd ℂ) z = 1 := hz
    have hz₂ : (starRingEnd ℂ) z * z = 1 := by simpa only [mul_comm] using hz₁
    have h3 : (Real.sqrt 3 : ℂ)^2 = 3 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
    have g0 : momentBeta 3 1 χ 0 =
        !![13/16, 3*(Real.sqrt 3 : ℂ)/14*star z;
           3*(Real.sqrt 3 : ℂ)/14*z, 3/16] := by
      convert chi_moments z hz 0 using 1 <;> norm_num <;> (first | left; ring | ring)
    have g1 : momentBeta 3 1 χ 1 =
        !![3/5, (Real.sqrt 3 : ℂ)/6*star z;
           (Real.sqrt 3 : ℂ)/6*z, 3/20] := by
      convert chi_moments z hz 1 using 1 <;> norm_num <;> (first | left; ring | ring)
    have g2 : momentBeta 3 1 χ 2 =
        !![19/40, 3*(Real.sqrt 3 : ℂ)/22*star z;
           3*(Real.sqrt 3 : ℂ)/22*z, 1/8] := by
      convert chi_moments z hz 2 using 1 <;> norm_num <;> (first | left; ring | ring)
    have hA : (momentBeta 3 1 χ 0).PosSemidef := by
      let v : Fin 2 → ℂ := ![8*(Real.sqrt 3 : ℂ)/7, z]
      have heq : momentBeta 3 1 χ 0 =
          (3/16 : ℂ) • vecMulVec v (star v) + diagonal ![(61/784 : ℂ), 0] := by
        rw [g0]
        ext i j
        fin_cases i <;> fin_cases j <;>
          norm_num [v, Matrix.add_apply, Matrix.smul_apply, diagonal_apply,
            vecMulVec_apply, Pi.star_apply, RCLike.star_def, Complex.conj_ofReal,
            map_mul, map_div₀, map_ofNat] <;>
          (try ring_nf) <;> (try simp only [h3, hz₁, hz₂]) <;> (try ring_nf) <;> (try simp only [hz₁, hz₂]) <;> ring
      rw [heq]
      apply ((posSemidef_vecMulVec_self_star v).smul
        (show (0 : ℂ) ≤ 3/16 by norm_num [Complex.le_def])).add
      apply posSemidef_diagonal_iff.mpr
      intro i
      fin_cases i <;> norm_num [Complex.le_def]
    have hB : B.IsHermitian := by
      change Bᴴ = B
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [B, conjTranspose_apply, RCLike.star_def, Complex.conj_ofReal]
    have hsol : momentBeta 3 1 χ 0 * B + B * momentBeta 3 1 χ 0 =
        (2 : ℂ) • momentBeta 3 1 χ 1 := by
      rw [g0, g1]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [B, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.add_apply,
          Matrix.smul_apply] <;> (try ring_nf) <;>
        (try simp only [h3, hz₁, hz₂]) <;> (try ring_nf) <;> (try simp only [hz₁, hz₂]) <;> ring
    have hv : ((momentBeta 3 1 χ 2).trace -
        (B * momentBeta 3 1 χ 1).trace).re = 167/4575 := by
      rw [g1, g2]
      have hc : ((!![19/40, 3*(Real.sqrt 3 : ℂ)/22*star z;
          3*(Real.sqrt 3 : ℂ)/22*z, 1/8] : Matrix (Fin 2) (Fin 2) ℂ).trace -
          (B * !![3/5, (Real.sqrt 3 : ℂ)/6*star z;
            (Real.sqrt 3 : ℂ)/6*z, 3/20]).trace) = (167/4575 : ℂ) := by
        norm_num [B, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ]
        ring_nf
        (try simp only [h3, hz₁, hz₂]) <;> (try ring_nf) <;> (try simp only [hz₁, hz₂])
        ring
      rw [hc]
      norm_num
    have hl := (bounds χ B hA hB hsol).1
    rw [hv] at hl
    have phase : MMSEBeta 3 1 (inBetween (1/4) φ) = MMSEBeta 3 1 χ := by
      have hc : ⌈(1/4 : ℝ)⌉₊ = 1 := by norm_num
      have hs : (Real.sqrt (1/4))^2 = (1/4 : ℝ) := Real.sq_sqrt (by norm_num)
      unfold inBetween
      rw [hc]
      simp only [Nat.cast_one, Nat.sub_self, sub_self, zero_add, hs]
      apply congrArg (MMSEBeta (N:=1) 3 1)
      ext n
      fin_cases n <;> norm_num [χ, z, Real.sqrt_div] <;> ring
    rw [phase]
    exact hl
  intro h
  let ψ : Fin 3 → ℂ := ![(Real.sqrt 14 : ℂ)/4, 0, (Real.sqrt 2 : ℂ)/4]
  let B : Matrix (Fin 3) (Fin 3) ℂ :=
    !![8/11, 0, 2*(Real.sqrt 7 : ℂ)/77;
       0, 2/3, 0;
       2*(Real.sqrt 7 : ℂ)/77, 0, 20/33]
  have h7 : (Real.sqrt 7 : ℂ)^2 = 7 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7)]
    norm_num
  have g0 : momentBeta 3 1 ψ 0 =
      !![71/80, 0, 3*(Real.sqrt 7 : ℂ)/32;
         0, 3/80, 0;
         3*(Real.sqrt 7 : ℂ)/32, 0, 3/40] := by
    convert psi_moments 0 using 1 <;> norm_num <;> ring
  have g1 : momentBeta 3 1 ψ 1 =
      !![53/80, 0, 3*(Real.sqrt 7 : ℂ)/40;
         0, 1/40, 0;
         3*(Real.sqrt 7 : ℂ)/40, 0, 1/16] := by
    convert psi_moments 1 using 1 <;> norm_num <;> ring
  have g2 : momentBeta 3 1 ψ 2 =
      !![37/70, 0, (Real.sqrt 7 : ℂ)/16;
         0, 1/56, 0;
         (Real.sqrt 7 : ℂ)/16, 0, 3/56] := by
    convert psi_moments 2 using 1 <;> norm_num <;> ring
  have hA : (momentBeta 3 1 ψ 0).PosSemidef := by
    let v : Fin 3 → ℂ := ![5*(Real.sqrt 7 : ℂ)/4, 0, 1]
    have heq : momentBeta 3 1 ψ 0 =
        (3/40 : ℂ) • vecMulVec v (star v) + diagonal ![(43/640 : ℂ), 3/80, 0] := by
      rw [g0]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [v, Matrix.add_apply, Matrix.smul_apply, diagonal_apply,
          vecMulVec_apply, Pi.star_apply, RCLike.star_def, Complex.conj_ofReal,
          map_mul, map_div₀, map_ofNat] <;>
        (try ring_nf) <;> (try simp only [h7]) <;> ring
    rw [heq]
    apply ((posSemidef_vecMulVec_self_star v).smul
      (show (0 : ℂ) ≤ 3/40 by norm_num [Complex.le_def])).add
    apply posSemidef_diagonal_iff.mpr
    intro i
    fin_cases i <;> norm_num [Complex.le_def]
  have hB : B.IsHermitian := by
    change Bᴴ = B
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [B, conjTranspose_apply, RCLike.star_def, Complex.conj_ofReal]
  have hsol : momentBeta 3 1 ψ 0 * B + B * momentBeta 3 1 ψ 0 =
      (2 : ℂ) • momentBeta 3 1 ψ 1 := by
    rw [g0, g1]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [B, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.add_apply,
        Matrix.smul_apply] <;> (try ring_nf) <;> (try simp only [h7]) <;> ring
  have hv : ((momentBeta 3 1 ψ 2).trace -
      (B * momentBeta 3 1 ψ 1).trace).re = 2/55 := by
    rw [g1, g2]
    have hc : ((!![37/70, 0, (Real.sqrt 7 : ℂ)/16;
        0, 1/56, 0; (Real.sqrt 7 : ℂ)/16, 0, 3/56] : Matrix (Fin 3) (Fin 3) ℂ).trace -
        (B * !![53/80, 0, 3*(Real.sqrt 7 : ℂ)/40;
          0, 1/40, 0; 3*(Real.sqrt 7 : ℂ)/40, 0, 1/16]).trace) = (2/55 : ℂ) := by
      norm_num [B, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ]
      ring_nf
      rw [h7]
      norm_num
    rw [hc]
    norm_num
  have hnorm : ‖WithLp.toLp 2 ψ‖ = 1 := by
    have hs : ‖WithLp.toLp 2 ψ‖^2 = 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      norm_num [ψ, Fin.sum_univ_succ, norm_div, Complex.norm_real,
        abs_of_nonneg (Real.sqrt_nonneg 14), abs_of_nonneg (Real.sqrt_nonneg 2)]
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 14),
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [norm_nonneg (WithLp.toLp 2 ψ)]
  have hmean : meanPhoton ψ = 1/4 := by
    unfold meanPhoton
    norm_num [ψ, Complex.normSq, Fin.sum_univ_succ, Real.sq_sqrt]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  obtain ⟨φ, hle⟩ := h 3 1 (1/4) (by norm_num) (by norm_num) (by norm_num)
    2 ψ hnorm hmean
  have hup := (bounds ψ B hA hB hsol).2
  rw [hv] at hup
  have hlow := chi_lower φ
  linarith

end D5.S3.Estimation.TransmissivityBetaPriorProbeRefutation
