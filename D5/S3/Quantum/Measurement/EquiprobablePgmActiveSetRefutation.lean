/- GID: D5/S3/Quantum/Measurement/EquiprobablePgmActiveSetRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/EquiprobablePgmActiveSetRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurement/EquiprobablePgmActiveSetRefutation.claim; result=D5/S3/Quantum/Measurement/EquiprobablePgmActiveSetRefutation.result; claim=D5/S3/Quantum/Measurement/EquiprobablePgmActiveSetRefutation.claim
   digest: For equal priors, the pretty good measurement on the active set can score too high. -/

/-
proof_shape: success, pgmScore: definition (the success probability
  Σ_i tr(σ̃_i E_i) with σ̃_i = ρ_i / N, and the pretty-good-measurement score Σ_{i ∈ A}
  tr(σ̃_i S_A^{-1/2} σ̃_i S_A^{-1/2}) with S_A = Σ_{i ∈ A} σ̃_i)
proof_shape: claim: definition (published conjecture, arXiv:2507.05778v2, journal Eq. (18), read
  for N ≥ 1 positive definite states of dimension k + 1, with the frozen finitePOVM and the active
  set of some optimal POVM)
proof_shape: rho: definition (the counterexample)
proof_shape: result: bind-only (as local steps: positive definiteness of the three states; a dual
  certificate Γ with Γ − σ̃_i ⪰ 0; complementary slackness forcing the active set {0, 1};
  S^{-1/2} of the two diagonal matrices S through CFC.sqrt_eq_iff and CFC.rpow_add; and rational
  evaluations)
escape_witness: none (the settlement of the external named conjecture is the new content)
admission_basis: open-problem-resolution (issue #12997; Refuted)
Direct frozen dependencies (GID, statement_id):
  D5/S3/Estimation/TransmissivityTwoPointProbeRefutation.finitePOVM
    sha256:0b88a0915c1837bdeb3bfc687e64c00b7e396fa7146ab78e6d9d731f378c3cae
  D5/S3/Weil/ZetaLinear/RankTrace.trace_mul_nonneg_of_posSemidef (namespace RHLinalg)
    sha256:fefc8a0805a2b6dd7fcf96418c2412c83986c84d51c5d1731ed8d1cea0a88ca3
-/

import D5.S3.Estimation.TransmissivityTwoPointProbeRefutation
import D5.S3.Weil.ZetaLinear.RankTrace
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace D5.S3.Quantum.Measurement.EquiprobablePgmActiveSetRefutation

open Matrix
open D5.S3.Estimation.TransmissivityTwoPointProbeRefutation (finitePOVM)

/-- The success probability `∑_i tr(σ̃_i E_i)` of the equiprobable ensemble `σ̃_i = ρ_i / N`. -/
noncomputable def success {d N : ℕ} (ρ E : Fin N → Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ∑ i, (trace ((1 / (N : ℂ)) • ρ i * E i)).re

/-- The pretty-good-measurement score on the labels `A`: `∑_{i ∈ A} tr(σ̃_i S_A^{-1/2} σ̃_i
S_A^{-1/2})` with `S_A = ∑_{i ∈ A} σ̃_i`. -/
noncomputable def pgmScore {d N : ℕ} (ρ : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (A : Finset (Fin N)) : ℝ :=
  ∑ i ∈ A, (trace ((1 / (N : ℂ)) • ρ i *
    ((∑ j ∈ A, (1 / (N : ℂ)) • ρ j) ^ (-(1 / 2) : ℝ) * ((1 / (N : ℂ)) • ρ i) *
      (∑ j ∈ A, (1 / (N : ℂ)) • ρ j) ^ (-(1 / 2) : ℝ)))).re

/-- The conjecture: for `N ≥ 1` equiprobable positive definite states, some optimal POVM has
active set `A = {i | E_i ≠ 0}` with `(|A| - 1)(P^PGM_A - 1/N) ≤ (N - 1)(P^PGM - 1/N)`. -/
def claim : Prop :=
  ∀ (k N : ℕ) (ρ : Fin N → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), 0 < N →
    (∀ i, (ρ i).PosDef) → (∀ i, trace (ρ i) = 1) →
      ∃ E : Fin N → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, finitePOVM E ∧
        (∀ F, finitePOVM F → success ρ F ≤ success ρ E) ∧
        (((Finset.univ.filter fun i => E i ≠ 0).card : ℝ) - 1) *
            (pgmScore ρ (Finset.univ.filter fun i => E i ≠ 0) - 1 / N) ≤
          ((N : ℝ) - 1) * (pgmScore ρ Finset.univ - 1 / N)

/-- The three states. -/
noncomputable def rho : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![400 / 401, 18 / 401; 18 / 401, 1 / 401], !![400 / 401, -18 / 401; -18 / 401, 1 / 401],
    !![47963 / 48922, 0; 0, 959 / 48922]]

theorem result : ¬ claim := by
  intro h
  have hdiag : ∀ (a b : ℂ), 0 < a → 0 < b → (diagonal ![a, b]).PosDef := by
    intro a b ha hb
    refine Matrix.posDef_diagonal_iff.2 fun i => ?_
    fin_cases i
    · simpa using ha
    · simpa using hb
  have hrank : ∀ v : Fin 2 → ℂ, (vecMulVec v (star v)).PosSemidef :=
    fun v => Matrix.posSemidef_vecMulVec_self_star v
  have hPD : ∀ i, (rho i).PosDef := by
    intro i
    fin_cases i
    · have he : rho 0 = (1 / 401 : ℂ) • (diagonal ![(39 : ℂ), 37 / 361] +
          vecMulVec ![(19 : ℂ), 18 / 19] (star ![(19 : ℂ), 18 / 19])) := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp [rho, vecMulVec, map_ofNat] <;> norm_num
      rw [show (⟨0, by norm_num⟩ : Fin 3) = 0 from rfl, he]
      exact ((hdiag _ _ (by norm_num) (by norm_num)).add_posSemidef (hrank _)).smul
        (by norm_num)
    · have he : rho 1 = (1 / 401 : ℂ) • (diagonal ![(39 : ℂ), 37 / 361] +
          vecMulVec ![(19 : ℂ), -18 / 19] (star ![(19 : ℂ), -18 / 19])) := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp [rho, vecMulVec, map_ofNat] <;> norm_num
      rw [show (⟨1, by norm_num⟩ : Fin 3) = 1 from rfl, he]
      exact ((hdiag _ _ (by norm_num) (by norm_num)).add_posSemidef (hrank _)).smul
        (by norm_num)
    · have he : rho 2 = diagonal ![(47963 / 48922 : ℂ), 959 / 48922] := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp [rho]
      rw [show (⟨2, by norm_num⟩ : Fin 3) = 2 from rfl, he]
      exact hdiag _ _ (by norm_num) (by norm_num)
  have htr : ∀ i, trace (rho i) = 1 := by
    intro i
    fin_cases i <;> simp [rho, trace, Fin.sum_univ_two] <;> norm_num
  obtain ⟨E, hE, hopt, hineq⟩ := h 1 3 rho (by norm_num) hPD htr
  set Γ : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![(418 / 1203 : ℂ), 19 / 1203] with hΓ
  have hslack : ∀ i, (Γ - (1 / 3 : ℂ) • rho i).PosSemidef := by
    intro i
    fin_cases i
    · have he : Γ - (1 / 3 : ℂ) • rho 0 =
          (6 / 401 : ℂ) • vecMulVec ![(1 : ℂ), -1] (star ![(1 : ℂ), -1]) := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp [hΓ, rho, vecMulVec] <;> norm_num
      rw [show (⟨0, by norm_num⟩ : Fin 3) = 0 from rfl, he]
      exact (hrank _).smul (by norm_num [Complex.nonneg_iff])
    · have he : Γ - (1 / 3 : ℂ) • rho 1 =
          (6 / 401 : ℂ) • vecMulVec ![(1 : ℂ), 1] (star ![(1 : ℂ), 1]) := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp [hΓ, rho, vecMulVec] <;> norm_num
      rw [show (⟨1, by norm_num⟩ : Fin 3) = 1 from rfl, he]
      exact (hrank _).smul (by norm_num [Complex.nonneg_iff])
    · have he : Γ - (1 / 3 : ℂ) • rho 2 = diagonal ![(1011 / 48922 : ℂ), 453 / 48922] := by
        ext a b
        fin_cases a <;> fin_cases b <;> simp [hΓ, rho] <;> norm_num
      rw [show (⟨2, by norm_num⟩ : Fin 3) = 2 from rfl, he]
      exact (hdiag _ _ (by norm_num) (by norm_num)).posSemidef
  have hsucc : ∀ F : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ, ∑ i, F i = 1 →
      success rho F = (trace Γ).re - ∑ i, (trace ((Γ - (1 / 3 : ℂ) • rho i) * F i)).re := by
    intro F hF
    have hΓF : ∑ i, (trace (Γ * F i)).re = (trace Γ).re := by
      rw [← Complex.re_sum, ← trace_sum, ← Finset.mul_sum, hF, mul_one]
    simp only [success, sub_mul, trace_sub, Complex.sub_re, Finset.sum_sub_distrib, hΓF]
    norm_num
  have htrΓ : (trace Γ).re = 437 / 1203 := by
    simp [hΓ, trace, Fin.sum_univ_two]
    norm_num
  set Q : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
    ![(1 / 2 : ℂ) • vecMulVec ![(1 : ℂ), 1] (star ![(1 : ℂ), 1]),
      (1 / 2 : ℂ) • vecMulVec ![(1 : ℂ), -1] (star ![(1 : ℂ), -1]), 0] with hQdef
  have hQsum : ∑ i, Q i = 1 := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [hQdef, Fin.sum_univ_three, vecMulVec] <;> norm_num
  have hQ : finitePOVM Q := by
    refine ⟨fun i => ?_, hQsum⟩
    fin_cases i
    · exact (hrank _).smul (by norm_num [Complex.nonneg_iff])
    · exact (hrank _).smul (by norm_num [Complex.nonneg_iff])
    · exact PosSemidef.zero
  have hQ0 : Q 0 = !![(1 / 2 : ℂ), 1 / 2; 1 / 2, 1 / 2] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [hQdef, vecMulVec]
  have hQ1 : Q 1 = !![(1 / 2 : ℂ), -1 / 2; -1 / 2, 1 / 2] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [hQdef, vecMulVec] <;> norm_num
  have hQ2 : Q 2 = 0 := rfl
  have hr0 : rho 0 = !![(400 / 401 : ℂ), 18 / 401; 18 / 401, 1 / 401] := rfl
  have hr1 : rho 1 = !![(400 / 401 : ℂ), -18 / 401; -18 / 401, 1 / 401] := rfl
  have hQval : success rho Q = 437 / 1203 := by
    rw [success, Fin.sum_univ_three, hQ0, hQ1, hQ2, hr0, hr1]
    simp only [mul_zero, trace_zero, Complex.zero_re, add_zero, Matrix.smul_of,
      Matrix.mul_fin_two, Matrix.trace_fin_two, Matrix.smul_cons, Matrix.smul_empty]
    norm_num
  have hnn : ∀ i, 0 ≤ (trace ((Γ - (1 / 3 : ℂ) • rho i) * E i)).re := fun i =>
    RHLinalg.trace_mul_nonneg_of_posSemidef (hslack i) (hE.1 i)
  have hle := hopt Q hQ
  rw [hQval, hsucc E hE.2, htrΓ, Fin.sum_univ_three] at hle
  have hn0 := hnn 0
  have hn1 := hnn 1
  have hn2 := hnn 2
  have hz0 : (trace ((Γ - (1 / 3 : ℂ) • rho 0) * E 0)).re = 0 := by linarith
  have hz1 : (trace ((Γ - (1 / 3 : ℂ) • rho 1) * E 1)).re = 0 := by linarith
  have hz2 : (trace ((Γ - (1 / 3 : ℂ) • rho 2) * E 2)).re = 0 := by linarith
  have hE2 : E 2 = 0 := by
    have hsplit : Γ - (1 / 3 : ℂ) • rho 2 =
        (453 / 48922 : ℂ) • 1 + diagonal ![(558 / 48922 : ℂ), 0] := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp [hΓ, rho] <;> norm_num
    have hD : (diagonal ![(558 / 48922 : ℂ), 0]).PosSemidef := by
      refine Matrix.posSemidef_diagonal_iff.2 fun i => ?_
      fin_cases i <;> (simp [Complex.nonneg_iff]; try norm_num)
    have hDE := RHLinalg.trace_mul_nonneg_of_posSemidef hD (hE.1 2)
    have h2 := hz2
    rw [hsplit, add_mul, trace_add, Complex.add_re, smul_mul_assoc, one_mul, trace_smul,
      smul_eq_mul] at h2
    have htr0 : 0 ≤ trace (E 2) := (hE.1 2).trace_nonneg
    rw [Complex.nonneg_iff] at htr0
    have hre : (trace (E 2)).re = 0 := by
      have : ((453 / 48922 : ℂ) * trace (E 2)).re = 453 / 48922 * (trace (E 2)).re := by
        simp [Complex.mul_re, htr0.2.symm]
      rw [this] at h2
      change 0 ≤ (trace (diagonal ![(558 / 48922 : ℂ), 0] * E 2)).re at hDE
      nlinarith [htr0.1]
    have htrz : trace (E 2) = 0 := Complex.ext hre htr0.2.symm
    exact ((hE.1 2).trace_eq_zero_iff).1 htrz
  have hsum3 : E 0 + E 1 + E 2 = 1 := by
    have := hE.2
    rwa [Fin.sum_univ_three] at this
  have hE0 : E 0 ≠ 0 := by
    intro h0
    have h1 : E 1 = 1 := by
      rw [h0, hE2, zero_add, add_zero] at hsum3
      exact hsum3
    have hz := hz1
    rw [h1, mul_one] at hz
    simp [hΓ, rho, trace, Fin.sum_univ_two] at hz
    norm_num at hz
  have hE1 : E 1 ≠ 0 := by
    intro h1
    have h0 : E 0 = 1 := by
      rw [h1, hE2, add_zero, add_zero] at hsum3
      exact hsum3
    have hz := hz0
    rw [h0, mul_one] at hz
    simp [hΓ, rho, trace, Fin.sum_univ_two] at hz
    norm_num at hz
  have hA : (Finset.univ.filter fun i => E i ≠ 0) = {0, 1} := by
    ext i
    fin_cases i <;> simp [hE0, hE1, hE2]
  rw [hA] at hineq
  have hX : ∀ u v : ℝ, 0 < u → 0 < v → (diagonal ![(u : ℂ), (v : ℂ)]) ^ (-(1 / 2) : ℝ) =
      diagonal ![(((Real.sqrt u)⁻¹ : ℝ) : ℂ), (((Real.sqrt v)⁻¹ : ℝ) : ℂ)] := by
    intro u v hu hv
    set S : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![(u : ℂ), (v : ℂ)] with hS
    set T : Matrix (Fin 2) (Fin 2) ℂ :=
      diagonal ![((Real.sqrt u : ℝ) : ℂ), ((Real.sqrt v : ℝ) : ℂ)] with hT
    have hT0 : 0 ≤ T := by
      rw [Matrix.nonneg_iff_posSemidef, hT]
      refine Matrix.posSemidef_diagonal_iff.2 fun i => ?_
      fin_cases i <;> simp [Complex.nonneg_iff, Real.sqrt_nonneg]
    have hTT : T * T = S := by
      rw [hT, hS, diagonal_mul_diagonal]
      congr 1
      funext i
      fin_cases i
      · simp [← Complex.ofReal_mul, Real.mul_self_sqrt hu.le]
      · simp [← Complex.ofReal_mul, Real.mul_self_sqrt hv.le]
    have hS0 : 0 ≤ S := by
      rw [← hTT, Matrix.nonneg_iff_posSemidef]
      have h1 := Matrix.nonneg_iff_posSemidef.mp hT0
      have := Matrix.posSemidef_conjTranspose_mul_self T
      rwa [h1.1.eq] at this
    have hsqrt : CFC.sqrt S = T := (CFC.sqrt_eq_iff S T hS0 hT0).2 hTT
    have hunit : IsUnit S := by
      rw [Matrix.isUnit_iff_isUnit_det, hS, det_diagonal, Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      exact (mul_ne_zero (Complex.ofReal_ne_zero.2 hu.ne') (Complex.ofReal_ne_zero.2 hv.ne')).isUnit
    have h1 : S ^ (-(1 / 2) : ℝ) * T = 1 := by
      rw [← hsqrt, CFC.sqrt_eq_rpow, ← CFC.rpow_add hunit]
      norm_num
      exact CFC.rpow_zero S hS0
    have hTinv : T * diagonal ![(((Real.sqrt u)⁻¹ : ℝ) : ℂ), (((Real.sqrt v)⁻¹ : ℝ) : ℂ)] = 1 := by
      rw [hT, diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      fin_cases i
      · simp [(Real.sqrt_pos.2 hu).ne']
      · simp [(Real.sqrt_pos.2 hv).ne']
    calc S ^ (-(1 / 2) : ℝ) = S ^ (-(1 / 2) : ℝ) * (T *
          diagonal ![(((Real.sqrt u)⁻¹ : ℝ) : ℂ), (((Real.sqrt v)⁻¹ : ℝ) : ℂ)]) := by
          rw [hTinv, mul_one]
      _ = _ := by rw [← mul_assoc, h1, one_mul]
  have hq : ∀ a b c x y : ℝ, (trace (!![(a : ℂ), (b : ℂ); (b : ℂ), (c : ℂ)] *
      (diagonal ![(x : ℂ), (y : ℂ)] * !![(a : ℂ), (b : ℂ); (b : ℂ), (c : ℂ)] *
        diagonal ![(x : ℂ), (y : ℂ)]))).re =
      a ^ 2 * x ^ 2 + 2 * b ^ 2 * (x * y) + c ^ 2 * y ^ 2 := by
    intro a b c x y
    have hd : diagonal ![(x : ℂ), (y : ℂ)] = !![(x : ℂ), 0; 0, (y : ℂ)] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [hd]
    simp [Matrix.trace_fin_two, Complex.add_re, Complex.mul_re]
    ring
  have hσ0 : (1 / 3 : ℂ) • rho 0 = !![((400 / 1203 : ℝ) : ℂ), ((18 / 1203 : ℝ) : ℂ);
      ((18 / 1203 : ℝ) : ℂ), ((1 / 1203 : ℝ) : ℂ)] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [rho] <;> norm_num
  have hσ1 : (1 / 3 : ℂ) • rho 1 = !![((400 / 1203 : ℝ) : ℂ), ((-18 / 1203 : ℝ) : ℂ);
      ((-18 / 1203 : ℝ) : ℂ), ((1 / 1203 : ℝ) : ℂ)] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [rho] <;> norm_num
  have hσ2 : (1 / 3 : ℂ) • rho 2 = !![((47963 / 146766 : ℝ) : ℂ), ((0 : ℝ) : ℂ);
      ((0 : ℝ) : ℂ), ((959 / 146766 : ℝ) : ℂ)] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [rho] <;> norm_num
  have hinv : ∀ u v w : ℝ, 0 < u → 0 < v → 0 < w → u * v = w ^ 2 →
      (Real.sqrt u)⁻¹ * (Real.sqrt v)⁻¹ = w⁻¹ := by
    intro u v w hu hv hw huv
    rw [← mul_inv, ← Real.sqrt_mul hu.le, huv, Real.sqrt_sq hw.le]
  have hsq : ∀ u : ℝ, 0 < u → ((Real.sqrt u)⁻¹) ^ 2 = u⁻¹ := by
    intro u hu
    rw [inv_pow, Real.sq_sqrt hu.le]
  have hPA : pgmScore rho {0, 1} = 2167 / 6015 := by
    have hSA : ∑ j ∈ ({0, 1} : Finset (Fin 3)), (1 / ((3 : ℕ) : ℂ)) • rho j =
        diagonal ![((800 / 1203 : ℝ) : ℂ), ((2 / 1203 : ℝ) : ℂ)] := by
      rw [Finset.sum_pair (by decide)]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [rho] <;> norm_num
    simp only [pgmScore]
    rw [hSA, hX _ _ (by norm_num) (by norm_num), Finset.sum_pair (by decide)]
    simp only [Nat.cast_ofNat]
    rw [hσ0, hσ1, hq, hq]
    have hx := hsq (800 / 1203) (by norm_num)
    have hy := hsq (2 / 1203) (by norm_num)
    have hxy := hinv (800 / 1203) (2 / 1203) (40 / 1203) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    rw [hx, hy, hxy]
    norm_num
  have hP : pgmScore rho Finset.univ = 20192347 / 58370763 := by
    have hS : ∑ j : Fin 3, (1 / ((3 : ℕ) : ℂ)) • rho j =
        diagonal ![((121 / 122 : ℝ) : ℂ), ((1 / 122 : ℝ) : ℂ)] := by
      rw [Fin.sum_univ_three]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [rho] <;> norm_num
    simp only [pgmScore]
    rw [hS, hX _ _ (by norm_num) (by norm_num), Fin.sum_univ_three]
    simp only [Nat.cast_ofNat]
    rw [hσ0, hσ1, hσ2, hq, hq, hq]
    have hx := hsq (121 / 122) (by norm_num)
    have hy := hsq (1 / 122) (by norm_num)
    have hxy := hinv (121 / 122) (1 / 122) (11 / 122) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    rw [hx, hy, hxy]
    norm_num
  rw [hPA, hP, Finset.card_pair (by decide)] at hineq
  norm_num at hineq

end D5.S3.Quantum.Measurement.EquiprobablePgmActiveSetRefutation
