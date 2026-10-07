/- GID: D5/S3/Estimation/TransmissivityTwoPointProbeRefutation
   generality: I
   mirror-B: D5/B/S3/Estimation/TransmissivityTwoPointProbeRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Estimation/TransmissivityTwoPointProbeRefutation.claim; result=D5/S3/Estimation/TransmissivityTwoPointProbeRefutation.result; claim=D5/S3/Estimation/TransmissivityTwoPointProbeRefutation.claim
   digest: Refute phased in-between-state optimality for two-point transmissivity sensing. -/

/-
result: proof_shape: bind-only; escape_witness: none;
admission_basis: open-problem-resolution (#11653; Refuted)
Direct frozen dependencies:
  D5/S3/Quantum/QuantumChannels/TruncatedLossDephasingOptimizerRefutation.amplitudeKraus,
  statement_id: sha256:df905a936771b44cd43f36036fe86b519c1e74230454ea6b19e70d563f2788fb;
  D5/S3/Quantum/PureState/PureStateHandshake.rankOneDensity,
  statement_id: sha256:e18ab4fd557d4917e344a15c06172fc321b99eb187307a88fe4c7fa4f8a28bf3;
  D5/S3/Weil/ZetaLinear/RankTrace.trace_mul_nonneg_of_posSemidef,
  statement_id: sha256:fefc8a0805a2b6dd7fcf96418c2412c83986c84d51c5d1731ed8d1cea0a88ca3.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S3.Quantum.QuantumChannels.TruncatedLossDephasingOptimizerRefutation
import D5.S3.Weil.ZetaLinear.RankTrace

open Matrix
open scoped BigOperators ComplexOrder
open D5.S3.Quantum.PureState.PureStateHandshake
open D5.S3.Quantum.QuantumChannels.TruncatedLossDephasingOptimizerRefutation

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.Estimation.TransmissivityTwoPointProbeRefutation

noncomputable def meanPhoton {N : ℕ} (ψ : Fin (N + 1) → ℂ) : ℝ :=
  ∑ n, (n.val : ℝ) * Complex.normSq (ψ n)

noncomputable def outputState {N : ℕ} (τ : ℝ) (ψ : Fin (N + 1) → ℂ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  ∑ l, amplitudeKraus l (1 - τ) * rankOneDensity ψ * (amplitudeKraus l (1 - τ))ᴴ

noncomputable def momentState {N : ℕ} (q τ₀ τ₁ : ℝ) (ψ : Fin (N + 1) → ℂ)
    (k : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  ((q * τ₀ ^ k : ℝ) : ℂ) • outputState τ₀ ψ +
    (((1 - q) * τ₁ ^ k : ℝ) : ℂ) • outputState τ₁ ψ

def finitePOVM {N m : ℕ} (E : Fin m → Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) : Prop :=
  (∀ k, (E k).PosSemidef) ∧ ∑ k, E k = 1

noncomputable def bayesianRisk {N m : ℕ} (q τ₀ τ₁ : ℝ) (ψ : Fin (N + 1) → ℂ)
    (E : Fin m → Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (x : Fin m → ℝ) : ℝ :=
  ∑ k, (E k * (((x k ^ 2 : ℝ) : ℂ) • momentState q τ₀ τ₁ ψ 0 -
    (((2 * x k : ℝ) : ℂ) • momentState q τ₀ τ₁ ψ 1) +
      momentState q τ₀ τ₁ ψ 2)).trace.re

noncomputable def MMSE {N : ℕ} (q τ₀ τ₁ : ℝ) (ψ : Fin (N + 1) → ℂ) : ℝ :=
  sInf {r : ℝ | ∃ (m : ℕ) (E : Fin m → Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (x : Fin m → ℝ), finitePOVM E ∧ r = bayesianRisk q τ₀ τ₁ ψ E x}

noncomputable def inBetween (nbar φ : ℝ) : Fin (⌈nbar⌉₊ + 1) → ℂ :=
  let c := Real.sqrt (1 - (⌈nbar⌉₊ : ℝ) + nbar)
  let a := Real.sqrt (1 - c ^ 2)
  fun n => Complex.exp (Complex.I * ((φ * n.val : ℝ) : ℂ)) *
    (if n.val = ⌈nbar⌉₊ - 1 then (a : ℂ)
      else if n.val = ⌈nbar⌉₊ then (c : ℂ) else 0)

def claim : Prop :=
  ∀ (q τ₀ τ₁ nbar : ℝ), q ∈ Set.Icc 0 1 → τ₀ ∈ Set.Icc 0 1 →
    τ₁ ∈ Set.Icc 0 1 → 0 < nbar →
      ∀ (N : ℕ) (ψ : Fin (N + 1) → ℂ), ‖WithLp.toLp 2 ψ‖ = 1 → meanPhoton ψ = nbar →
        ∃ φ : ℝ, MMSE q τ₀ τ₁ (inBetween nbar φ) ≤ MMSE q τ₀ τ₁ ψ

theorem result : ¬ claim := by
  have sqrt_power (t : ℝ) (ht : 0 ≤ t) (k : ℕ) :
      Real.sqrt (t ^ k) = Real.sqrt t ^ k := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg ht k), ih, pow_succ]
  have source_coefficient (n l : ℕ) (τ : ℝ) (hτ : τ ∈ Set.Icc 0 1) :
      Real.sqrt ((Nat.choose n l : ℝ) * τ ^ (n - l) * (1 - τ) ^ l) =
        Real.sqrt (Nat.choose n l) * Real.sqrt τ ^ (n - l) * Real.sqrt (1 - τ) ^ l := by
    rw [Real.sqrt_mul (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hτ.1 _)),
      Real.sqrt_mul (Nat.cast_nonneg _), sqrt_power τ hτ.1,
      sqrt_power (1 - τ) (sub_nonneg.mpr hτ.2)]
  have sourceKraus {N : ℕ} (l : Fin (N + 1)) (τ : ℝ) (hτ : τ ∈ Set.Icc 0 1) :
      amplitudeKraus l (1 - τ) = Matrix.of (fun r c : Fin (N + 1) =>
        if r.val + l.val = c.val then
          if l.val ≤ c.val then
            (Real.sqrt ((Nat.choose c.val l.val : ℝ) *
              τ ^ (c.val - l.val) * (1 - τ) ^ l.val) : ℂ)
          else 0
        else 0) := by
    ext r c
    simp only [amplitudeKraus, Matrix.of_apply, sub_sub_cancel, source_coefficient _ _ τ hτ]

  have phase_MMSE (φ : ℝ) :
      MMSE (1/2) (4/9) 1 (inBetween (1/2) φ) =
        MMSE (N:=1) (1/2) (4/9) 1 ![(Real.sqrt (1/2) : ℂ),
          (Real.sqrt (1/2) : ℂ) * Complex.exp (Complex.I * (φ : ℂ))] := by
    have hc : ⌈(1/2 : ℝ)⌉₊ = 1 := by norm_num
    have hs : (Real.sqrt (1/2))^2 = (1/2 : ℝ) := Real.sq_sqrt (by norm_num)
    unfold inBetween
    rw [hc]
    simp only [Nat.cast_one, Nat.sub_self, sub_self, zero_add, hs,
      show (1 - (1/2 : ℝ)) = 1/2 by norm_num]
    apply congrArg (MMSE (N:=1) (1/2) (4/9) 1)
    ext n
    fin_cases n <;> norm_num <;> ring

  have moment_variance {d m : ℕ} (E : Fin m → Matrix (Fin d) (Fin d) ℂ)
      (x : Fin m → ℝ) (hE : (∀ k, (E k).PosSemidef) ∧ ∑ k, E k = 1) :
      let M₁ := ∑ k, (x k : ℂ) • E k
      let M₂ := ∑ k, ((x k ^ 2 : ℝ) : ℂ) • E k
      (M₂ - M₁ * M₁).PosSemidef := by
    classical
    dsimp only
    let M₁ := ∑ k, (x k : ℂ) • E k
    have hM₁ : M₁.IsHermitian := by
      change M₁ᴴ = M₁
      simp only [M₁, conjTranspose_sum]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [conjTranspose_smul, RCLike.star_def,
        Complex.conj_ofReal, (hE.1 k).isHermitian.eq]
    have identity :
        (∑ k, (((x k : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - M₁)ᴴ * E k *
          ((x k : ℂ) • 1 - M₁))) =
          (∑ k, ((x k ^ 2 : ℝ) : ℂ) • E k) - M₁ * M₁ := by
      simp only [conjTranspose_sub, conjTranspose_smul, conjTranspose_one,
        RCLike.star_def, Complex.conj_ofReal, hM₁.eq, sub_mul, mul_sub, Matrix.smul_mul,
        Matrix.mul_smul, one_mul, mul_one, smul_smul]
      have sum_right : (∑ k, (x k : ℂ) • (E k * M₁)) = M₁ * M₁ := by
        simp only [← Matrix.smul_mul, ← Matrix.sum_mul]
        rfl
      have sum_left : (∑ k, (x k : ℂ) • (M₁ * E k)) = M₁ * M₁ := by
        simp only [← Matrix.mul_smul, ← Matrix.mul_sum]
        rfl
      have sum_sandwich : (∑ k, M₁ * E k * M₁) = M₁ * M₁ := by
        rw [← Matrix.sum_mul, ← Matrix.mul_sum, hE.2, mul_one]
      simp only [Finset.sum_sub_distrib, sum_right, sum_left, sum_sandwich,
        Complex.ofReal_pow, Complex.ofReal_mul, pow_two]
      abel
    rw [← identity]
    exact posSemidef_sum _ fun k _ => (hE.1 k).conjTranspose_mul_mul_same _

  have risk_lower_bound {d m : ℕ}
      (A C D B : Matrix (Fin d) (Fin d) ℂ)
      (hA : A.PosSemidef) (hB : B.IsHermitian)
      (hsol : A * B + B * A = (2 : ℂ) • C)
      (E : Fin m → Matrix (Fin d) (Fin d) ℂ) (x : Fin m → ℝ)
      (hE : (∀ k, (E k).PosSemidef) ∧ ∑ k, E k = 1) :
      (D.trace - (B * C).trace).re ≤
        ∑ k, (E k * (((x k ^ 2 : ℝ) : ℂ) • A -
          (((2 * x k : ℝ) : ℂ) • C) + D)).trace.re := by
    classical
    let M₁ := ∑ k, (x k : ℂ) • E k
    let M₂ := ∑ k, ((x k ^ 2 : ℝ) : ℂ) • E k
    let V := M₂ - M₁ * M₁
    have hV : V.PosSemidef := moment_variance E x hE
    have hM₁ : M₁.IsHermitian := by
      change M₁ᴴ = M₁
      simp only [M₁, conjTranspose_sum]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [conjTranspose_smul, RCLike.star_def,
        Complex.conj_ofReal, (hE.1 k).isHermitian.eq]
    have hS : ((M₁ - B) * (M₁ - B)).PosSemidef := by
      have hHerm := hM₁.sub hB
      simpa only [hHerm.eq] using posSemidef_conjTranspose_mul_self (M₁ - B)
    have total :
        (∑ k, E k * (((x k ^ 2 : ℝ) : ℂ) • A -
          (((2 * x k : ℝ) : ℂ) • C) + D)) =
        M₂ * A - (2 : ℂ) • (M₁ * C) + D := by
      simp only [mul_add, mul_sub, Matrix.mul_smul, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, Complex.ofReal_mul, Complex.ofReal_ofNat]
      have second : (∑ k, ((2 : ℂ) * (x k : ℂ)) • (E k * C)) =
          (2 : ℂ) • (M₁ * C) := by
        simp only [← smul_smul, ← Finset.smul_sum, ← Matrix.smul_mul,
          ← Matrix.sum_mul]
        rfl
      have first : (∑ k, ((x k ^ 2 : ℝ) : ℂ) • (E k * A)) = M₂ * A := by
        simp only [← Matrix.smul_mul, ← Matrix.sum_mul]
        rfl
      have third : (∑ k, E k * D) = D := by
        rw [← Matrix.sum_mul, hE.2, one_mul]
      rw [first, second, third]
    have hcross : (A * M₁ * B).trace + (A * B * M₁).trace =
        (2 : ℂ) * (M₁ * C).trace := by
      have h := congrArg (fun Z => (M₁ * Z).trace) hsol
      simp only [mul_add, trace_add, Matrix.mul_smul, trace_smul, smul_eq_mul] at h
      rw [← mul_assoc, ← mul_assoc, trace_mul_cycle M₁ A B,
        trace_mul_cycle B M₁ A, trace_mul_cycle M₁ B A] at h
      simpa only [add_comm] using h
    have hbb : (A * B * B).trace = (B * C).trace := by
      have h := congrArg (fun Z => (B * Z).trace) hsol
      simp only [mul_add, trace_add, Matrix.mul_smul, trace_smul, smul_eq_mul,
        ← mul_assoc] at h
      rw [trace_mul_cycle B A B, trace_mul_cycle B B A] at h
      linear_combination h / 2
    have hcomplete :
        (∑ k, (E k * (((x k ^ 2 : ℝ) : ℂ) • A -
          (((2 * x k : ℝ) : ℂ) • C) + D)).trace) -
          (D.trace - (B * C).trace) =
        (A * V).trace + (A * ((M₁ - B) * (M₁ - B))).trace := by
      rw [← trace_sum, total]
      simp only [V, mul_sub, sub_mul, trace_add, trace_sub, trace_smul, ← mul_assoc]
      rw [trace_mul_comm M₂ A]
      linear_combination hcross - hbb
    have hnV := RHLinalg.trace_mul_nonneg_of_posSemidef hA hV
    have hnS := RHLinalg.trace_mul_nonneg_of_posSemidef hA hS
    have h := congrArg Complex.re hcomplete
    simp only [Complex.sub_re, Complex.add_re] at h ⊢
    have hreSum : (∑ k, (E k * (((x k ^ 2 : ℝ) : ℂ) • A -
        (((2 * x k : ℝ) : ℂ) • C) + D)).trace).re =
        ∑ k, (E k * (((x k ^ 2 : ℝ) : ℂ) • A -
        (((2 * x k : ℝ) : ℂ) • C) + D)).trace.re :=
      map_sum Complex.reAddGroupHom _ _
    rw [hreSum] at h
    change 0 ≤ (A * V).trace.re at hnV
    change 0 ≤ (A * ((M₁ - B) * (M₁ - B))).trace.re at hnS
    linarith

  have spectral_attainment {d : ℕ}
      (A C D B : Matrix (Fin d) (Fin d) ℂ) (hB : B.IsHermitian)
      (hsol : A * B + B * A = (2 : ℂ) • C) :
      ∃ (E : Fin d → Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℝ),
        ((∀ k, (E k).PosSemidef) ∧ ∑ k, E k = 1) ∧
        (∑ k, (E k * (((x k ^ 2 : ℝ) : ℂ) • A -
          (((2 * x k : ℝ) : ℂ) • C) + D)).trace.re) =
            (D.trace - (B * C).trace).re := by
    classical
    let U : Matrix (Fin d) (Fin d) ℂ := hB.eigenvectorUnitary
    let P (k : Fin d) : Matrix (Fin d) (Fin d) ℂ := diagonal (Pi.single k 1)
    let E (k : Fin d) := U * P k * Uᴴ
    let x := hB.eigenvalues
    have hUU : U * Uᴴ = 1 := Unitary.coe_mul_star_self hB.eigenvectorUnitary
    have hUstarU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hB.eigenvectorUnitary
    have hP : ∀ k, (P k).PosSemidef := by
      intro k
      change (diagonal (Pi.single k (1 : ℂ))).PosSemidef
      rw [posSemidef_diagonal_iff]
      intro i
      simp only [Pi.single_apply]
      split_ifs <;> simp
    have hPsum : ∑ k, P k = 1 := by
      ext i j
      simp [P, Matrix.sum_apply, diagonal_apply, Matrix.one_apply, Pi.single_apply]
    have hEsum : ∑ k, E k = 1 := by
      simp only [E, ← Matrix.sum_mul, ← Matrix.mul_sum, hPsum, mul_one, hUU]
    have hE : (∀ k, (E k).PosSemidef) ∧ ∑ k, E k = 1 :=
      ⟨fun k => (hP k).mul_mul_conjTranspose_same U, hEsum⟩
    have hdiag (r : Fin d → ℂ) : ∑ k, r k • P k = diagonal r := by
      ext i j
      simp [P, diagonal_apply, Matrix.sum_apply, Matrix.smul_apply, Pi.single_apply]
    have hBdiag : B = U * diagonal (fun k => (x k : ℂ)) * Uᴴ := by
      convert hB.spectral_theorem using 1 <;>
        simp [U, x, Unitary.conjStarAlgAut_apply, RCLike.ofReal, star_eq_conjTranspose, Function.comp_def]
    have sum_conj (r : Fin d → ℂ) :
        ∑ k, r k • E k = U * (∑ k, r k • P k) * Uᴴ := by
      rw [Matrix.mul_sum, Matrix.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [E, Matrix.mul_smul, Matrix.smul_mul]
    have hM₁ : ∑ k, (x k : ℂ) • E k = B := by
      rw [sum_conj, hdiag, ← hBdiag]
    have hM₂ : ∑ k, ((x k ^ 2 : ℝ) : ℂ) • E k = B * B := by
      rw [sum_conj, hdiag, hBdiag]
      simp only [mul_assoc, ← mul_assoc Uᴴ U, hUstarU, one_mul,
        Complex.ofReal_pow, pow_two]
      rw [← mul_assoc (diagonal _) (diagonal _), diagonal_mul_diagonal]
      simp only [Complex.ofReal_mul]
    have total :
        (∑ k, E k * (((x k ^ 2 : ℝ) : ℂ) • A -
          (((2 * x k : ℝ) : ℂ) • C) + D)) =
          (B * B) * A - (2 : ℂ) • (B * C) + D := by
      simp only [mul_add, mul_sub, Matrix.mul_smul, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, Complex.ofReal_mul, Complex.ofReal_ofNat]
      have first : (∑ k, ((x k ^ 2 : ℝ) : ℂ) • (E k * A)) = (B * B) * A := by
        simp only [← Matrix.smul_mul, ← Matrix.sum_mul, hM₂]
      have second : (∑ k, ((2 : ℂ) * (x k : ℂ)) • (E k * C)) =
          (2 : ℂ) • (B * C) := by
        simp only [← smul_smul, ← Finset.smul_sum, ← Matrix.smul_mul,
          ← Matrix.sum_mul, hM₁]
      have third : (∑ k, E k * D) = D := by
        rw [← Matrix.sum_mul, hEsum, one_mul]
      rw [first, second, third]
    have hbb : (B * B * A).trace = (B * C).trace := by
      have h := congrArg (fun Z => (B * Z).trace) hsol
      simp only [mul_add, trace_add, Matrix.mul_smul, trace_smul, smul_eq_mul,
        ← mul_assoc] at h
      rw [trace_mul_cycle B A B] at h
      linear_combination h / 2
    refine ⟨E, x, hE, ?_⟩
    rw [← Complex.re_sum, ← trace_sum, total]
    simp only [trace_add, trace_sub, trace_smul, smul_eq_mul, hbb]
    congr 1
    ring

  have chi_certificate (z : ℂ) (hz : z * star z = 1) :
      let s : ℝ := Real.sqrt (1 / 2)
      let χ : Fin 2 → ℂ := ![(s : ℂ), (s : ℂ) * z]
      let B : Matrix (Fin 2) (Fin 2) ℂ :=
        !![787 / 1332, 145 / 1332 * star z; 145 / 1332 * z, 937 / 1332]
      B.IsHermitian ∧
        momentState (1/2) (4/9) 1 χ 0 * B + B * momentState (1/2) (4/9) 1 χ 0 =
          (2 : ℂ) • momentState (1/2) (4/9) 1 χ 1 ∧
        ((momentState (1/2) (4/9) 1 χ 2).trace -
          (B * momentState (1/2) (4/9) 1 χ 1).trace).re = 1625 / 23976 := by
    classical
    have hz₁ : z * (starRingEnd ℂ) z = 1 := hz
    have hz₂ : (starRingEnd ℂ) z * z = 1 := by simpa only [mul_comm] using hz₁
    dsimp only
    let s : ℝ := Real.sqrt (1 / 2)
    let χ : Fin 2 → ℂ := ![(s : ℂ), (s : ℂ) * z]
    let B : Matrix (Fin 2) (Fin 2) ℂ :=
      !![787 / 1332, 145 / 1332 * star z; 145 / 1332 * z, 937 / 1332]
    have hs : (s : ℂ) ^ 2 = 1 / 2 := by
      change (Real.sqrt (1/2) : ℂ)^2 = 1/2
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1/2)]
      norm_num
    have hl : (Real.sqrt 5 : ℂ) ^ 2 = 5 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
      norm_num
    have ht : Real.sqrt (4 / 9) = (2 / 3 : ℝ) := by
      norm_num [Real.sqrt_div]
    have rho0 : outputState (4/9) χ =
        !![7/9, (1/3) * star z; (1/3) * z, 2/9] := by
      have hτ : (4/9 : ℝ) ∈ Set.Icc 0 1 := by norm_num
      simp only [outputState, sourceKraus _ _ hτ, source_coefficient _ _ _ hτ]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.of_apply, outputState, amplitudeKraus, rankOneDensity, χ, Matrix.mul_apply,
          Fin.sum_univ_succ, vecMulVec_apply, conjTranspose_apply, Pi.star_apply,
          ht, RCLike.star_def, Complex.conj_ofReal, map_mul] <;>
        ring_nf <;> norm_num [hs, hl, map_ofNat, map_inv₀] <;> ring_nf <;>
        (try simp only [← mul_assoc, hz₁, hz₂]) <;> ring
    have rho1 : outputState 1 χ =
        !![1/2, (1/2) * star z; (1/2) * z, 1/2] := by
      have hτ : (1 : ℝ) ∈ Set.Icc 0 1 := by norm_num
      simp only [outputState, sourceKraus _ _ hτ, source_coefficient _ _ _ hτ]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.of_apply, outputState, amplitudeKraus, rankOneDensity, χ, Matrix.mul_apply,
          Fin.sum_univ_succ, vecMulVec_apply, conjTranspose_apply, Pi.star_apply,
          RCLike.star_def, Complex.conj_ofReal, map_mul] <;>
        ring_nf <;> norm_num [hs, map_ofNat, map_inv₀] <;> ring_nf <;>
        (try simp only [← mul_assoc, hz₁, hz₂]) <;> ring
    have g0 : momentState (1/2) (4/9) 1 χ 0 =
        !![23/36, (5/12) * star z; (5/12) * z, 13/36] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [momentState, rho0, rho1, Matrix.add_apply, Matrix.smul_apply] <;> ring
    have g1 : momentState (1/2) (4/9) 1 χ 1 =
        !![137/324, (35/108) * star z; (35/108) * z, 97/324] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [momentState, rho0, rho1, Matrix.add_apply, Matrix.smul_apply] <;> ring
    have g2 : momentState (1/2) (4/9) 1 χ 2 =
        !![953/2916, (275/972) * star z; (275/972) * z, 793/2916] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [momentState, rho0, rho1, Matrix.add_apply, Matrix.smul_apply] <;> ring
    refine ⟨?_, ?_, ?_⟩
    · change Bᴴ = B
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [B, conjTranspose_apply, RCLike.star_def]
    · rw [g0, g1]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [B, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.add_apply,
          Matrix.smul_apply] <;> ring_nf <;>
          (try simp only [← mul_assoc, hz₁, hz₂]) <;> ring
    · rw [g1, g2]
      have valueC :
          ( (!![953/2916, (275/972) * star z; (275/972) * z, 793/2916] : Matrix (Fin 2) (Fin 2) ℂ).trace -
            (B * !![137/324, (35/108) * star z; (35/108) * z, 97/324]).trace) =
            (1625/23976 : ℂ) := by
        norm_num [B, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ]
        ring_nf
        (try simp only [← mul_assoc, hz₁, hz₂])
        ring
      rw [valueC]
      norm_num

  have psi_certificate :
      let ψ : Fin 3 → ℂ := ![(Real.sqrt 3 : ℂ) / 2, 0, 1 / 2]
      let B : Matrix (Fin 3) (Fin 3) ℂ :=
        !![62971/93024, 0, 4293/93024 * (Real.sqrt 3 : ℂ);
           0, 41344/93024, 0;
           4293/93024 * (Real.sqrt 3 : ℂ), 0, 68965/93024]
      ‖WithLp.toLp 2 ψ‖ = 1 ∧ meanPhoton ψ = 1/2 ∧ B.IsHermitian ∧
        momentState (1/2) (4/9) 1 ψ 0 * B + B * momentState (1/2) (4/9) 1 ψ 0 =
          (2 : ℂ) • momentState (1/2) (4/9) 1 ψ 1 ∧
        ((momentState (1/2) (4/9) 1 ψ 2).trace -
          (B * momentState (1/2) (4/9) 1 ψ 1).trace).re = 110575 / 1674432 := by
    classical
    dsimp only
    let ψ : Fin 3 → ℂ := ![(Real.sqrt 3 : ℂ) / 2, 0, 1 / 2]
    let B : Matrix (Fin 3) (Fin 3) ℂ :=
      !![62971/93024, 0, 4293/93024 * (Real.sqrt 3 : ℂ);
         0, 41344/93024, 0;
         4293/93024 * (Real.sqrt 3 : ℂ), 0, 68965/93024]
    have h3 : (Real.sqrt 3 : ℂ)^2 = 3 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
    have h2 : (Real.sqrt 2 : ℂ)^2 = 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have h5 : (Real.sqrt 5 : ℂ)^2 = 5 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
      norm_num
    have h54 : (Real.sqrt 5 : ℂ)^4 = 25 := by
      calc (Real.sqrt 5 : ℂ)^4 = ((Real.sqrt 5 : ℂ)^2)^2 := by ring
        _ = 25 := by rw [h5]; norm_num
    have hFin12 : (1 : Fin 3) ≤ 2 := by decide
    have ht : Real.sqrt (4/9) = (2/3 : ℝ) := by norm_num [Real.sqrt_div]
    have rho0 : outputState (4/9) ψ =
        !![67/81, 0, (Real.sqrt 3 : ℂ)/9;
           0, 10/81, 0;
           (Real.sqrt 3 : ℂ)/9, 0, 4/81] := by
      have hτ : (4/9 : ℝ) ∈ Set.Icc 0 1 := by norm_num
      simp only [outputState, sourceKraus _ _ hτ, source_coefficient _ _ _ hτ]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.of_apply, outputState, amplitudeKraus, rankOneDensity, ψ,
          Matrix.mul_apply, Fin.sum_univ_succ, vecMulVec_apply, conjTranspose_apply,
          Pi.star_apply, ht, RCLike.star_def, Complex.conj_ofReal, map_mul,
          map_ofNat, map_inv₀, hFin12] <;>
        ring_nf <;> norm_num [h2, h3, h5, h54, map_ofNat, map_inv₀, hFin12,
          map_mul, Complex.conj_ofReal] <;> ring_nf <;> norm_num [h2, h5]
    have rho1 : outputState 1 ψ =
        !![3/4, 0, (Real.sqrt 3 : ℂ)/4;
           0, 0, 0;
           (Real.sqrt 3 : ℂ)/4, 0, 1/4] := by
      have hτ : (1 : ℝ) ∈ Set.Icc 0 1 := by norm_num
      simp only [outputState, sourceKraus _ _ hτ, source_coefficient _ _ _ hτ]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.of_apply, outputState, amplitudeKraus, rankOneDensity, ψ,
          Matrix.mul_apply, Fin.sum_univ_succ, vecMulVec_apply, conjTranspose_apply,
          Pi.star_apply, RCLike.star_def, Complex.conj_ofReal, map_mul,
          map_ofNat, map_inv₀] <;> ring_nf <;> norm_num [h3] <;> ring
    have g0 : momentState (1/2) (4/9) 1 ψ 0 =
        !![511/648, 0, 13/72 * (Real.sqrt 3 : ℂ);
           0, 5/81, 0;
           13/72 * (Real.sqrt 3 : ℂ), 0, 97/648] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [momentState, rho0, rho1, Matrix.add_apply, Matrix.smul_apply] <;> ring
    have g1 : momentState (1/2) (4/9) 1 ψ 1 =
        !![3259/5832, 0, 97/648 * (Real.sqrt 3 : ℂ);
           0, 20/729, 0;
           97/648 * (Real.sqrt 3 : ℂ), 0, 793/5832] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [momentState, rho0, rho1, Matrix.add_apply, Matrix.smul_apply] <;> ring
    have g2 : momentState (1/2) (4/9) 1 ψ 2 =
        !![23971/52488, 0, 793/5832 * (Real.sqrt 3 : ℂ);
           0, 80/6561, 0;
           793/5832 * (Real.sqrt 3 : ℂ), 0, 6817/52488] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [momentState, rho0, rho1, Matrix.add_apply, Matrix.smul_apply] <;> ring
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have hs : ‖WithLp.toLp 2 ψ‖^2 = 1 := by
        rw [EuclideanSpace.norm_sq_eq]
        norm_num [ψ, Fin.sum_univ_succ, norm_div, Complex.norm_real,
          abs_of_nonneg (Real.sqrt_nonneg 3), Real.sq_sqrt]
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      nlinarith [norm_nonneg (WithLp.toLp 2 ψ)]
    · norm_num [meanPhoton, ψ, Complex.normSq, Fin.sum_univ_succ]
    · change Bᴴ = B
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [B, conjTranspose_apply, RCLike.star_def, map_ofNat, map_inv₀]
    · rw [g0, g1]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [B, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.add_apply,
          Matrix.smul_apply] <;> ring_nf <;> norm_num [h3] <;> ring
    · rw [g1, g2]
      have hv :
          ((!![23971/52488, 0, 793/5832 * (Real.sqrt 3 : ℂ);
           0, 80/6561, 0;
           793/5832 * (Real.sqrt 3 : ℂ), 0, 6817/52488] : Matrix (Fin 3) (Fin 3) ℂ).trace -
          (B * !![3259/5832, 0, 97/648 * (Real.sqrt 3 : ℂ);
           0, 20/729, 0;
           97/648 * (Real.sqrt 3 : ℂ), 0, 793/5832]).trace) = (110575/1674432 : ℂ) := by
        norm_num [B, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ]
        ring_nf
        norm_num [h3]
      rw [hv]
      norm_num

  have zeroMoment_pos {N : ℕ} (ψ : Fin (N+1) → ℂ) :
      (momentState (1/2) (4/9) 1 ψ 0).PosSemidef := by
    have hout (τ : ℝ) : (outputState τ ψ).PosSemidef := by
      exact posSemidef_sum _ fun l _ =>
        (posSemidef_vecMulVec_self_star ψ).mul_mul_conjTranspose_same
          (amplitudeKraus l (1-τ))
    simp only [momentState, pow_zero, mul_one]
    exact ((hout (4/9)).smul (Complex.zero_le_real.mpr (by norm_num))).add
      ((hout 1).smul (Complex.zero_le_real.mpr (by norm_num)))

  have MMSE_bounds {N : ℕ} (q τ₀ τ₁ : ℝ) (ψ : Fin (N+1) → ℂ)
      (B : Matrix (Fin (N+1)) (Fin (N+1)) ℂ)
      (hA : (momentState q τ₀ τ₁ ψ 0).PosSemidef) (hB : B.IsHermitian)
      (hsol : momentState q τ₀ τ₁ ψ 0 * B + B * momentState q τ₀ τ₁ ψ 0 =
        (2 : ℂ) • momentState q τ₀ τ₁ ψ 1) :
      ((momentState q τ₀ τ₁ ψ 2).trace - (B * momentState q τ₀ τ₁ ψ 1).trace).re ≤
          MMSE q τ₀ τ₁ ψ ∧
        MMSE q τ₀ τ₁ ψ ≤
          ((momentState q τ₀ τ₁ ψ 2).trace - (B * momentState q τ₀ τ₁ ψ 1).trace).re := by
    classical
    let L := ((momentState q τ₀ τ₁ ψ 2).trace -
      (B * momentState q τ₀ τ₁ ψ 1).trace).re
    have bound {m : ℕ} (E : Fin m → Matrix (Fin (N+1)) (Fin (N+1)) ℂ)
        (x : Fin m → ℝ) (hE : finitePOVM E) : L ≤ bayesianRisk q τ₀ τ₁ ψ E x :=
      risk_lower_bound _ _ _ B hA hB hsol E x hE
    have nonempty : {r : ℝ | ∃ (m : ℕ)
        (E : Fin m → Matrix (Fin (N+1)) (Fin (N+1)) ℂ)
        (x : Fin m → ℝ), finitePOVM E ∧ r = bayesianRisk q τ₀ τ₁ ψ E x}.Nonempty := by
      let E : Fin 1 → Matrix (Fin (N+1)) (Fin (N+1)) ℂ := fun _ => 1
      let x : Fin 1 → ℝ := fun _ => 0
      refine ⟨bayesianRisk q τ₀ τ₁ ψ E x, 1, E, x, ?_, rfl⟩
      exact ⟨fun _ => PosSemidef.one, by simp [E]⟩
    constructor
    · unfold MMSE
      apply le_csInf nonempty
      rintro r ⟨m, E, x, hE, rfl⟩
      exact bound E x hE
    · unfold MMSE
      apply csInf_le
      · refine ⟨L, ?_⟩
        rintro r ⟨m, E, x, hE, rfl⟩
        exact bound E x hE
      · obtain ⟨E, x, hE, heq⟩ := spectral_attainment
          (momentState q τ₀ τ₁ ψ 0) (momentState q τ₀ τ₁ ψ 1)
          (momentState q τ₀ τ₁ ψ 2) B hB hsol
        exact ⟨N+1, E, x, hE, heq.symm⟩

  have chi_lower (φ : ℝ) :
      1625/23976 ≤ MMSE (1/2) (4/9) 1 (inBetween (1/2) φ) := by
    classical
    let z := Complex.exp (Complex.I * (φ : ℂ))
    let s : ℝ := Real.sqrt (1/2)
    let χ : Fin 2 → ℂ := ![(s : ℂ), (s : ℂ) * z]
    let B : Matrix (Fin 2) (Fin 2) ℂ :=
      !![787 / 1332, 145 / 1332 * star z; 145 / 1332 * z, 937 / 1332]
    have hz : z * star z = 1 := by
      dsimp [z]
      rw [← Complex.exp_conj, ← Complex.exp_add]
      have he : Complex.I * (φ : ℂ) + star (Complex.I * (φ : ℂ)) = 0 := by simp
      simpa [he]
    obtain ⟨hB, hsol, hvalue⟩ := chi_certificate z hz
    have hboth := MMSE_bounds (1/2) (4/9) 1 χ B (zeroMoment_pos χ) hB hsol
    have heq := le_antisymm hboth.2 hboth.1
    rw [hvalue] at heq
    have hbound := heq.ge
    rw [phase_MMSE φ]
    exact hbound

  intro h
  let ψ : Fin 3 → ℂ := ![(Real.sqrt 3 : ℂ)/2, 0, 1/2]
  let B : Matrix (Fin 3) (Fin 3) ℂ :=
    !![62971/93024, 0, 4293/93024 * (Real.sqrt 3 : ℂ);
       0, 41344/93024, 0;
       4293/93024 * (Real.sqrt 3 : ℂ), 0, 68965/93024]
  obtain ⟨hnorm, hmean, hB, hsol, hvalue⟩ := psi_certificate
  obtain ⟨φ, hle⟩ := h (1/2) (4/9) 1 (1/2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) 2 ψ hnorm hmean
  have hboth := MMSE_bounds (1/2) (4/9) 1 ψ B (zeroMoment_pos ψ) hB hsol
  have heq := le_antisymm hboth.2 hboth.1
  rw [hvalue] at heq
  have hup := heq.le
  have hlow := chi_lower φ
  linarith

end D5.S3.Estimation.TransmissivityTwoPointProbeRefutation
