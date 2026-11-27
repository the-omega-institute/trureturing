/- GID: D5/S3/Quantum/Divergence/TraceEntropy/GibbsCubicTranslationEntropy
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/TraceEntropy/GibbsCubicTranslationEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual noncommuting cubic entropy derivative along Gibbs translation. -/

import D5.S3.Quantum.Divergence.TraceEntropyCalculus
import D5.S3.Quantum.Recovery.BKMSpectralVariance
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Matrix Filter
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Divergence.TraceEntropy.GibbsCubicTranslationEntropy

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Literal cubic entropy with the fixed reference cube and variable trace normalization. -/
def cubicEntropy (B M : Matrix n n ℂ) : ℝ :=
  (M ^ 3 * cfc Real.log (M ^ 3)).trace.re -
    (M ^ 3).trace.re * Real.log (M ^ 3).trace.re -
    (M ^ 3 * cfc Real.log (B ^ 3)).trace.re

/-- The correction due to the middle term in the noncommuting cube derivative. -/
def correction (B M : Matrix n n ℂ) : ℝ :=
  (B * M ^ 2 * cfc Real.log B - M * B * M * cfc Real.log B).trace.re

private theorem log_cube {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    cfc Real.log (A ^ 3) = (3 : ℝ) • cfc Real.log A := by
  have hc (f : ℝ → ℝ) := A.finite_real_spectrum.continuousOn f
  have hp : ContinuousOn Real.log ((fun x : ℝ => x ^ 3) '' spectrum ℝ A) :=
    (A.finite_real_spectrum.image _).continuousOn _
  rw [← cfc_comp_pow Real.log 3 A hp hA.isSelfAdjoint, ← cfc_const_mul 3 Real.log A (hc _)]
  exact cfc_congr (fun z _ => by simpa only [Nat.cast_ofNat] using Real.log_pow z 3)

private theorem commute_log {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    Commute A (cfc Real.log A) := by
  simpa only [cfc_id ℝ A hA.isSelfAdjoint] using (cfc_commute_cfc (id : ℝ → ℝ) Real.log A)

private def cubeVariation (B M : Matrix n n ℂ) : Matrix n n ℂ :=
  (B * M + M * B) * M + M ^ 2 * B

private theorem trace_middle (B M L : Matrix n n ℂ) (h : Commute M L) :
    (M * B * M * L).trace = (B * M ^ 2 * L).trace := by
  calc
    _ = (M * (B * M * L)).trace := by simp only [mul_assoc]
    _ = ((B * M * L) * M).trace := trace_mul_comm _ _
    _ = _ := by simp only [mul_assoc, ← h.eq, pow_two]

private theorem trace_last (B M L : Matrix n n ℂ) (h : Commute M L) :
    (M ^ 2 * B * L).trace = (B * M ^ 2 * L).trace := by
  calc
    _ = (M ^ 2 * (B * L)).trace := by rw [mul_assoc]
    _ = ((B * L) * M ^ 2).trace := trace_mul_comm _ _
    _ = _ := by rw [mul_assoc, ← (h.pow_left 2).eq, ← mul_assoc]

private theorem trace_last_ref (B M L : Matrix n n ℂ) (h : Commute B L) :
    (M ^ 2 * B * L).trace = (B * M ^ 2 * L).trace := by
  calc
    _ = (M ^ 2 * (B * L)).trace := by rw [mul_assoc]
    _ = ((B * L) * M ^ 2).trace := trace_mul_comm _ _
    _ = ((L * B) * M ^ 2).trace := by rw [h.eq]
    _ = (L * (B * M ^ 2)).trace := by rw [mul_assoc]
    _ = _ := trace_mul_comm _ _

private theorem trace_variation (B M L : Matrix n n ℂ) :
    (cubeVariation B M * L).trace =
      (B * M ^ 2 * L).trace + (M * B * M * L).trace +
        (M ^ 2 * B * L).trace := by
  simp only [cubeVariation, add_mul, Matrix.trace_add, pow_two, mul_assoc]

private theorem trace_variation_self (B M L : Matrix n n ℂ) (h : Commute M L) :
    (cubeVariation B M * L).trace.re = 3 * (B * M ^ 2 * L).trace.re := by
  rw [trace_variation, trace_middle B M L h, trace_last B M L h]
  simp only [Complex.add_re]
  ring

private theorem trace_variation_ref (B M : Matrix n n ℂ) (hB : B.IsHermitian) :
    (cubeVariation B M * cfc Real.log B).trace.re =
      3 * (B * M ^ 2 * cfc Real.log B).trace.re - correction B M := by
  rw [trace_variation, trace_last_ref B M _ (commute_log hB)]
  simp only [correction, Matrix.trace_sub, Complex.sub_re, Complex.add_re]
  ring

private theorem hasDerivAt_reTrace {f : ℝ → Matrix n n ℂ} {V : Matrix n n ℂ}
    (hf : HasDerivAt f V 0) : HasDerivAt (fun t => (f t).trace.re) V.trace.re 0 := by
  let T : Matrix n n ℂ →L[ℝ] ℝ :=
    Complex.reCLM.comp (Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap
  exact T.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hf

set_option maxHeartbeats 1000000 in
/-- The actual two-sided entropy derivative, with both the trace-normalization term
and the noncommuting correction. No normalization assumption on B is needed. -/
theorem hasDerivAt_cubicEntropy (B M : Matrix n n ℂ) (hB : B.PosDef) (hM : M.PosDef) :
    HasDerivAt (fun s : ℝ => cubicEntropy B (M + s • B))
      (9 * (B * M ^ 2 * (cfc Real.log M - cfc Real.log B)).trace.re -
        3 * (B * M ^ 2).trace.re * Real.log (M ^ 3).trace.re +
        3 * correction B M) 0 := by
  cases isEmpty_or_nonempty n with
  | inl hi =>
    letI := hi
    simpa [cubicEntropy, correction, Matrix.trace] using
      (hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ℝ)))
  | inr hi =>
    letI := hi
    let F : ℝ → Matrix n n ℂ := fun s => M + s • B
    let V := cubeVariation B M
    have hF : HasDerivAt F B 0 := by
      simpa [F] using ((hasDerivAt_id (0 : ℝ)).smul_const B).const_add M
    have hpow : HasDerivAt (fun s => F s ^ 3) V 0 := by
      simpa only [F, V, cubeVariation, zero_smul, add_zero,
        show (3 : ℕ) = 2 + 1 by decide, pow_succ, pow_zero, one_mul] using
        (hF.fun_mul hF).fun_mul hF
    have hPD : (F 0 ^ 3).PosDef := by
      simpa only [F, zero_smul, add_zero] using
        ((hM.posSemidef.pow 3).posDef_iff_isUnit).mpr (hM.isUnit.pow 3)
    have hLog := TraceEntropyCalculus.hasDerivAt_trace_mul_log
      (fun s => F s ^ 3) V 0 hpow
      (Eventually.of_forall fun s =>
        (hM.isHermitian.add (hB.isHermitian.smul (star_trivial s))).pow 3) hPD
    have hRef := hasDerivAt_reTrace (hpow.mul_const (cfc Real.log (B ^ 3)))
    have hMass := hasDerivAt_reTrace hpow
    have hMassPos : 0 < (F 0 ^ 3).trace.re := (Complex.lt_def.mp hPD.trace_pos).1
    have hMassLog := hMass.fun_mul ((Real.hasDerivAt_log hMassPos.ne').comp 0 hMass)
    have hd := (hLog.fun_sub hMassLog).fun_sub hRef
    simp only [Function.comp_apply] at hd
    have hmass : V.trace.re = 3 * (B * M ^ 2).trace.re := by
      simpa only [V, mul_one] using
        trace_variation_self B M 1 (Commute.one_right M)
    have hself : (V * cfc Real.log (M ^ 3)).trace.re =
        9 * (B * M ^ 2 * cfc Real.log M).trace.re := by
      rw [log_cube hM.isHermitian, Matrix.mul_smul, Matrix.trace_smul,
        Complex.smul_re, smul_eq_mul, trace_variation_self B M _ (commute_log hM.isHermitian)]
      ring
    have href : (V * cfc Real.log (B ^ 3)).trace.re =
        9 * (B * M ^ 2 * cfc Real.log B).trace.re - 3 * correction B M := by
      rw [log_cube hB.isHermitian, Matrix.mul_smul, Matrix.trace_smul,
        Complex.smul_re, smul_eq_mul, trace_variation_ref B M hB.isHermitian]
      ring
    have hcancel :
        (V * (cfc Real.log (F 0 ^ 3) + 1)).trace.re -
          (V.trace.re * Real.log (F 0 ^ 3).trace.re +
            (F 0 ^ 3).trace.re * ((F 0 ^ 3).trace.re⁻¹ * V.trace.re)) -
            (V * cfc Real.log (B ^ 3)).trace.re =
          9 * (B * M ^ 2 * (cfc Real.log M - cfc Real.log B)).trace.re -
            3 * (B * M ^ 2).trace.re * Real.log (M ^ 3).trace.re +
            3 * correction B M := by
      rw [← mul_assoc (F 0 ^ 3).trace.re, mul_inv_cancel₀ hMassPos.ne', one_mul]
      simp only [F, zero_smul, add_zero, mul_add, Matrix.trace_add, Complex.add_re,
        mul_one, mul_sub, Matrix.trace_sub, Complex.sub_re, hself, href, hmass]
      ring
    rw [hcancel] at hd
    simpa only [cubicEntropy, F] using hd

#print axioms hasDerivAt_cubicEntropy

private theorem pow_mul_log_cfc {A : Matrix n n ℂ} (hA : A.IsHermitian) (k : ℕ) :
    A ^ k * cfc Real.log A = cfc (fun x : ℝ => x ^ k * Real.log x) A := by
  rw [cfc_mul (fun x : ℝ => x ^ k) Real.log A
    (A.finite_real_spectrum.continuousOn _) (A.finite_real_spectrum.continuousOn _),
    cfc_pow_id A k hA.isSelfAdjoint]

private theorem continuous_pow_mul_log (k : ℕ) :
    Continuous (fun x : ℝ => x ^ (k + 1) * Real.log x) := by
  simpa only [pow_succ, mul_assoc] using
    (continuous_pow k).fun_mul Real.continuous_mul_log

private theorem continuous_reTrace : Continuous (fun A : Matrix n n ℂ => A.trace.re) :=
  (Complex.reCLM.comp (Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap).continuous

private theorem continuous_cfc_hermitian {A : ℝ → Matrix n n ℂ} (hA : Continuous A)
    (hH : ∀ t, (A t).IsHermitian) {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (fun t => cfc f (A t)) :=
  Continuous.cfc_of_mem_nhdsSet (s := Set.univ) (p := IsSelfAdjoint) f Filter.univ_mem hA
    (fun t => (hH t).isSelfAdjoint) hf.continuousOn

private theorem continuous_cubicEntropy_line (B M : Matrix n n ℂ)
    (hB : B.IsHermitian) (hM : M.IsHermitian) :
    Continuous (fun s : ℝ => cubicEntropy B (M + s • B)) := by
  let A : ℝ → Matrix n n ℂ := fun s => M + s • B
  have hA : Continuous A := continuous_const.add (continuous_id.smul continuous_const)
  have hH (s : ℝ) : (A s).IsHermitian :=
    hM.add (hB.smul (star_trivial s))
  have hCube : Continuous (fun s => A s ^ 3) := hA.pow 3
  have hSelf : Continuous (fun s => (A s ^ 3 * cfc Real.log (A s ^ 3)).trace.re) := by
    simp_rw [log_cube (hH _), Matrix.mul_smul, pow_mul_log_cfc (hH _)]
    have hc : Continuous (fun s => cfc (fun x : ℝ => x ^ 3 * Real.log x) (A s)) :=
      continuous_cfc_hermitian hA hH (continuous_pow_mul_log 2)
    exact continuous_reTrace.comp (hc.const_smul (3 : ℝ))
  exact (hSelf.sub (Real.continuous_mul_log.comp (continuous_reTrace.comp hCube))).sub
    (continuous_reTrace.comp (hCube.mul continuous_const))

private theorem cubic_trace_pos {M : Matrix n n ℂ} (hM : M.PosSemidef) (hM₀ : M ≠ 0) :
    0 < (M ^ 3).trace.re := by
  have hne : hM.isHermitian.eigenvalues ≠ 0 :=
    fun h => hM₀ (hM.isHermitian.eigenvalues_eq_zero_iff.mp h)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  rw [← cfc_pow_id (R := ℝ) M 3 hM.isHermitian.isSelfAdjoint,
    D5.S3.Resource.LogDet.PathSpectralClassical.trace_cfc_eq_sum M hM.isHermitian]
  exact Finset.sum_pos' (fun j _ => pow_nonneg (hM.eigenvalues_nonneg j) 3)
    ⟨i, Finset.mem_univ i, pow_pos (lt_of_le_of_ne (hM.eigenvalues_nonneg i) hi.symm) 3⟩

private theorem cubicEntropy_gibbs_ray (B : Matrix n n ℂ) (hB : B.PosDef)
    {s : ℝ} (hs : 0 ≤ s) :
    cubicEntropy B (s • B) = s ^ 3 * cubicEntropy B B := by
  rcases hs.eq_or_lt with rfl | hs
  · simp [cubicEntropy]
  cases isEmpty_or_nonempty n with
  | inl hi =>
    letI := hi
    simp [cubicEntropy, Matrix.trace]
  | inr hi =>
    letI := hi
    have hB3 : (B ^ 3).PosDef :=
      ((hB.posSemidef.pow 3).posDef_iff_isUnit).mpr (hB.isUnit.pow 3)
    have htrace : 0 < (B ^ 3).trace.re := (Complex.lt_def.mp hB3.trace_pos).1
    have hlog : cfc Real.log (s ^ 3 • B ^ 3) =
        Real.log (s ^ 3) • (1 : Matrix n n ℂ) + cfc Real.log (B ^ 3) := by
      change CFC.log (s ^ 3 • B ^ 3) =
        Real.log (s ^ 3) • (1 : Matrix n n ℂ) + CFC.log (B ^ 3)
      rw [CFC.log_smul' _ (pow_pos hs 3) hB3.isStrictlyPositive,
        Algebra.algebraMap_eq_smul_one]
    unfold cubicEntropy
    rw [smul_pow, hlog]
    simp only [Matrix.smul_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one,
      Matrix.trace_smul, Matrix.trace_add, Complex.smul_re, Complex.add_re, smul_eq_mul]
    rw [Real.log_mul (pow_pos hs 3).ne' htrace.ne']
    ring

set_option maxHeartbeats 1500000 in
/-- The right derivative of the actual cubic entropy at every positive semidefinite
matrix, with the logarithmic term at a zero eigenvalue killed by the square. -/
theorem hasDerivWithinAt_cubicEntropy (B M : Matrix n n ℂ)
    (hB : B.PosDef) (hM : M.PosSemidef) :
    HasDerivWithinAt (fun s : ℝ => cubicEntropy B (M + s • B))
      (9 * (B * M ^ 2 * (cfc Real.log M - cfc Real.log B)).trace.re -
        3 * (B * M ^ 2).trace.re * Real.log (M ^ 3).trace.re +
        3 * correction B M) (Set.Ici 0) 0 := by
  by_cases hM₀ : M = 0
  · subst M
    have h := (((hasDerivAt_id (0 : ℝ)).pow 3).mul_const (cubicEntropy B B))
    have h₀ : HasDerivWithinAt (fun s : ℝ => s ^ 3 * cubicEntropy B B)
        0 (Set.Ici 0) 0 := by simpa using h.hasDerivWithinAt (s := Set.Ici 0)
    have heq (s : ℝ) (hs : s ∈ Set.Ici (0 : ℝ)) :
        cubicEntropy B (0 + s • B) = s ^ 3 * cubicEntropy B B := by
      rw [zero_add, cubicEntropy_gibbs_ray B hB hs]
    simpa [correction] using h₀.congr_of_mem heq (Set.mem_Ici.mpr le_rfl)
  let A : ℝ → Matrix n n ℂ := fun s => M + s • B
  let G : ℝ → ℝ := fun s =>
    9 * (B * A s ^ 2 * (cfc Real.log (A s) - cfc Real.log B)).trace.re -
      3 * (B * A s ^ 2).trace.re * Real.log (A s ^ 3).trace.re +
      3 * correction B (A s)
  have hA : Continuous A := continuous_const.add (continuous_id.smul continuous_const)
  have hH (s : ℝ) : (A s).IsHermitian :=
    hM.isHermitian.add (hB.isHermitian.smul (star_trivial s))
  have hD (s : ℝ) (hs : 0 < s) : HasDerivAt (fun t => cubicEntropy B (A t)) (G s) s := by
    have hpos : (A s).PosDef := Matrix.PosDef.posSemidef_add hM (hB.smul hs)
    have hshift : HasDerivAt (fun t : ℝ => t - s) 1 s := (hasDerivAt_id s).sub_const s
    have h := (hasDerivAt_cubicEntropy B (A s) hB hpos).comp_of_eq s hshift (sub_self s).symm
    have heq : (fun t => cubicEntropy B (A s + t • B)) ∘ (fun t => t - s) =
        fun t => cubicEntropy B (A t) := by
      funext t
      dsimp only [Function.comp_apply, A]
      congr 1
      rw [sub_smul]
      abel
    rwa [heq, mul_one] at h
  have hMass : Continuous (fun s => (A s ^ 3).trace.re) :=
    continuous_reTrace.comp (hA.pow 3)
  have hMass₀ : 0 < (A 0 ^ 3).trace.re := by
    simpa only [A, zero_smul, add_zero] using cubic_trace_pos hM hM₀
  have hLog : ContinuousAt (fun s => Real.log (A s ^ 3).trace.re) 0 :=
    (Real.continuousAt_log hMass₀.ne').comp (f := fun s => (A s ^ 3).trace.re) hMass.continuousAt
  have hSelf : Continuous (fun s => (B * (A s ^ 2 * cfc Real.log (A s))).trace.re) := by
    simp_rw [pow_mul_log_cfc (hH _)]
    exact continuous_reTrace.comp (continuous_const.mul
      (continuous_cfc_hermitian hA hH (continuous_pow_mul_log 1)))
  have hRef : Continuous (fun s => (B * A s ^ 2 * cfc Real.log B).trace.re) :=
    continuous_reTrace.comp ((continuous_const.mul (hA.pow 2)).mul continuous_const)
  have hS : Continuous (fun s => (B * A s ^ 2).trace.re) :=
    continuous_reTrace.comp (continuous_const.mul (hA.pow 2))
  have hJ : Continuous (fun s => correction B (A s)) :=
    continuous_reTrace.comp (((continuous_const.mul (hA.pow 2)).mul continuous_const).sub
      (((hA.mul continuous_const).mul hA).mul continuous_const))
  have hG : ContinuousAt G 0 := by
    have hc : ContinuousAt
        (fun s => 9 * ((B * (A s ^ 2 * cfc Real.log (A s))).trace.re -
          (B * A s ^ 2 * cfc Real.log B).trace.re) -
          (3 * (B * A s ^ 2).trace.re) * Real.log (A s ^ 3).trace.re +
          3 * correction B (A s)) 0 :=
      (((hSelf.fun_sub hRef).continuousAt.const_mul 9).fun_sub
        ((hS.continuousAt.const_mul 3).fun_mul hLog)).fun_add (hJ.continuousAt.const_mul 3)
    simpa only [G, mul_sub, Matrix.trace_sub, Complex.sub_re, mul_assoc] using hc
  have hlim : Tendsto (fun s => deriv (fun t => cubicEntropy B (A t)) s)
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (G 0)) := by
    apply (hG.continuousWithinAt (s := Set.Ioi 0)).tendsto.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hD s hs).deriv.symm
  have hBoundary := hasDerivWithinAt_Ici_of_tendsto_deriv
    (fun s hs => (hD s hs).differentiableAt.differentiableWithinAt)
    (continuous_cubicEntropy_line B M hB.isHermitian hM.isHermitian).continuousWithinAt
    (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ))) hlim
  simpa only [G, A, zero_smul, add_zero] using hBoundary

#print axioms hasDerivWithinAt_cubicEntropy

private theorem trace_diagonal_three {U : Matrix n n ℂ} (hU : U.IsHermitian)
    (a b c : n → ℝ) :
    (diagonal (fun i => (a i : ℂ)) * U * diagonal (fun i => (b i : ℂ)) * U *
      diagonal (fun i => (c i : ℂ))).trace.re =
      ∑ i, ∑ j, a i * b j * c i * Complex.normSq (U i j) := by
  simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.mul_diagonal, Matrix.mul_apply, Finset.sum_mul, Complex.re_sum]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← hU.apply j i, Complex.star_def]
  rw [show (a i : ℂ) * U i j * (b j : ℂ) * starRingEnd ℂ (U i j) * (c i : ℂ) =
    ((a i : ℂ) * (b j : ℂ) * (c i : ℂ)) * (U i j * starRingEnd ℂ (U i j)) by ring]
  simp only [Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- The correction in the actual spectral basis of B, allowing repeated eigenvalues. -/
theorem correction_spectral (B M : Matrix n n ℂ) (hB : B.IsHermitian)
    (hM : M.IsHermitian) :
    let b := hB.eigenvalues
    let Q := (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hB.eigenvectorUnitary).symm
    let U := Q M
    correction B M = (1 / 2 : ℝ) *
      ∑ i, ∑ j, (b i - b j) * (Real.log (b i) - Real.log (b j)) *
        Complex.normSq (U i j) := by
  dsimp only
  let b := hB.eigenvalues
  let W := hB.eigenvectorUnitary
  let Q := (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) W).symm
  let U := Q M
  have hU : U.IsHermitian := hM.isSelfAdjoint.map Q
  have htrace (A : Matrix n n ℂ) : (Q A).trace = A.trace := by
    simp only [Q, Unitary.conjStarAlgAut_symm_apply]
    rw [Matrix.trace_mul_cycle, ← Unitary.coe_star, Unitary.coe_mul_star_self, Matrix.one_mul]
  have hD : Q B = diagonal (fun i => (b i : ℂ)) := by
    calc
      Q B = Q (Unitary.conjStarAlgAut ℂ _ W (diagonal (RCLike.ofReal ∘ b))) :=
        congrArg Q hB.spectral_theorem
      _ = _ := by simp only [Q, StarAlgEquiv.symm_apply_apply, Function.comp_apply,
        RCLike.ofReal_eq_complex_ofReal] <;> rfl
  have hlog : Q (cfc Real.log B) = diagonal (fun i => (Real.log (b i) : ℂ)) := by
    rw [hB.cfc_eq, Matrix.IsHermitian.cfc]
    simp only [Q, W, b, StarAlgEquiv.symm_apply_apply, Function.comp_apply,
      RCLike.ofReal_eq_complex_ofReal] <;> rfl
  have hfirst : (B * M ^ 2 * cfc Real.log B).trace.re =
      ∑ i, ∑ j, b i * Real.log (b i) * Complex.normSq (U i j) := by
    rw [← htrace (B * M ^ 2 * cfc Real.log B), map_mul, map_mul, map_pow, hD, hlog]
    simpa only [U, pow_two, Complex.ofReal_one, Matrix.diagonal_one, mul_one, mul_assoc]
      using trace_diagonal_three hU b (fun _ => 1) (fun i => Real.log (b i))
  have hsecond : (M * B * M * cfc Real.log B).trace.re =
      ∑ i, ∑ j, b j * Real.log (b i) * Complex.normSq (U i j) := by
    rw [← htrace (M * B * M * cfc Real.log B), map_mul, map_mul, map_mul, hD, hlog]
    simpa only [U, Complex.ofReal_one, Matrix.diagonal_one, one_mul]
      using trace_diagonal_three hU (fun _ => 1) b (fun i => Real.log (b i))
  let N : n → n → ℝ := fun i j => Complex.normSq (U i j)
  let f : n → n → ℝ := fun i j => (b i - b j) * Real.log (b i)
  have hN (i j : n) : N i j = N j i := by
    change Complex.normSq (U i j) = Complex.normSq (U j i)
    rw [← hU.apply i j, Complex.star_def, Complex.normSq_conj]
  have hswap : (∑ i, ∑ j, f j i * N i j) = ∑ i, ∑ j, f i j * N i j := by
    calc
      _ = ∑ i, ∑ j, f j i * N j i := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        rw [hN i j]
      _ = _ := Finset.sum_comm
  have hdiff : correction B M = ∑ i, ∑ j, f i j * N i j := by
    rw [correction, Matrix.trace_sub, Complex.sub_re, hfirst, hsecond]
    simp only [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    dsimp [f, N]
    ring
  have hsum :
      (∑ i, ∑ j, (b i - b j) * (Real.log (b i) - Real.log (b j)) * N i j) =
      (∑ i, ∑ j, f i j * N i j) + ∑ i, ∑ j, f j i * N i j := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    dsimp [f]
    ring
  change correction B M = (1 / 2 : ℝ) *
    ∑ i, ∑ j, (b i - b j) * (Real.log (b i) - Real.log (b j)) * N i j
  rw [hdiff, hsum, hswap]
  ring

open D5.S3.Quantum.Recovery in
open BKMSpectralVariance (logMean) in
/-- The correction is half the Petz BKM pairing of the logarithmic commutator. -/
theorem correction_eq_bkm (B M : Matrix n n ℂ) (hB : B.PosDef) (hM : M.IsHermitian) :
    let C := cfc Real.log B * M - M * cfc Real.log B
    correction B M = (1 / 2 : ℝ) * (Cᴴ * BKMRelativeDensity.omega B C).trace.re := by
  let C := cfc Real.log B * M - M * cfc Real.log B
  let ΩC := BKMRelativeDensity.omega B C
  let b := hB.isHermitian.eigenvalues
  let W := hB.isHermitian.eigenvectorUnitary
  let Q := (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) W).symm
  let U := Q M
  have hlog : Q (cfc Real.log B) = diagonal (fun i => (Real.log (b i) : ℂ)) := by
    rw [hB.isHermitian.cfc_eq, Matrix.IsHermitian.cfc]
    simp only [Q, W, b, StarAlgEquiv.symm_apply_apply, Function.comp_apply,
      RCLike.ofReal_eq_complex_ofReal] <;> rfl
  have hC (i j : n) : (Q C) i j = ((Real.log (b i) - Real.log (b j) : ℝ) : ℂ) * U i j := by
    simp only [C, U, map_sub, map_mul, hlog, Matrix.sub_apply, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Complex.ofReal_sub]
    ring
  have homega (i j : n) : (Q ΩC) i j = (logMean (b i) (b j) : ℂ) * (Q C) i j :=
    BKMSpectralVariance.omega_eigenbasis_entry hB C i j
  have hpair : (Cᴴ * ΩC).trace.re =
      ∑ i, ∑ j, ((starRingEnd ℂ) ((Q C) i j) * (Q ΩC) i j).re := by
    rw [← BKMSpectralVariance.trace_conjStarAlgAut_symm W (Cᴴ * ΩC)]
    change (Q (star C * ΩC)).trace.re = _
    rw [map_mul, map_star, Matrix.star_eq_conjTranspose]
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.star_def, Complex.re_sum]
    exact Finset.sum_comm
  have hspectral : correction B M = (1 / 2 : ℝ) *
      ∑ i, ∑ j, (b i - b j) * (Real.log (b i) - Real.log (b j)) *
        Complex.normSq (U i j) :=
    correction_spectral B M hB.isHermitian hM
  change correction B M = (1 / 2 : ℝ) * (Cᴴ * ΩC).trace.re
  rw [hspectral, hpair]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [homega i j]
  have hmean := BKMSpectralVariance.logMean_mul_logRatio
    (hB.eigenvalues_pos i) (hB.eigenvalues_pos j)
  rw [Real.log_div (hB.eigenvalues_pos i).ne' (hB.eigenvalues_pos j).ne'] at hmean
  change logMean (b i) (b j) * (Real.log (b i) - Real.log (b j)) = b i - b j at hmean
  calc
    _ = logMean (b i) (b j) * Complex.normSq ((Q C) i j) := by
      rw [hC, Complex.normSq_mul, Complex.normSq_ofReal, ← hmean]
      ring
    _ = _ := by
      rw [← Complex.ofReal_re (logMean (b i) (b j) * Complex.normSq ((Q C) i j)),
        Complex.ofReal_mul, ← Complex.mul_conj]
      congr 1 <;> ring

private theorem logKernel_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ (a - b) * (Real.log a - Real.log b) := by
  rcases le_total a b with hab | hab
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hab)
      (sub_nonpos.mpr (Real.log_le_log ha hab))
  · exact mul_nonneg (sub_nonneg.mpr hab)
      (sub_nonneg.mpr (Real.log_le_log hb hab))

private theorem logKernel_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    0 < (a - b) * (Real.log a - Real.log b) := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact mul_pos_of_neg_of_neg (sub_neg.mpr h) (sub_neg.mpr (Real.log_lt_log ha h))
  · exact mul_pos (sub_pos.mpr h) (sub_pos.mpr (Real.log_lt_log hb h))

/-- The commutator correction is nonnegative even for noncommuting Hermitian M. -/
theorem correction_nonneg (B M : Matrix n n ℂ) (hB : B.PosDef) (hM : M.IsHermitian) :
    0 ≤ correction B M := by
  rw [correction_spectral B M hB.isHermitian hM]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => mul_nonneg
      (logKernel_nonneg (hB.eigenvalues_pos i) (hB.eigenvalues_pos j))
      (Complex.normSq_nonneg _))

/-- The zero correction permits arbitrary matrix entries within an eigenspace of B.
Only entries between distinct eigenvalues are required to vanish. -/
theorem correction_eq_zero_iff_commute (B M : Matrix n n ℂ)
    (hB : B.PosDef) (hM : M.IsHermitian) :
    correction B M = 0 ↔ Commute B M := by
  let b := hB.isHermitian.eigenvalues
  let Q := (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hB.isHermitian.eigenvectorUnitary).symm
  let U := Q M
  let f := fun i j : n => (b i - b j) * (Real.log (b i) - Real.log (b j)) *
    Complex.normSq (U i j)
  have hf (i j : n) : 0 ≤ f i j :=
    mul_nonneg (logKernel_nonneg (hB.eigenvalues_pos i) (hB.eigenvalues_pos j))
      (Complex.normSq_nonneg _)
  have hsum : correction B M = (1 / 2 : ℝ) * ∑ i, ∑ j, f i j :=
    correction_spectral B M hB.isHermitian hM
  have hD : Q B = diagonal (fun i => (b i : ℂ)) := by
    simpa only [Q, b, Unitary.conjStarAlgAut_symm, RCLike.ofReal_eq_complex_ofReal,
      Function.comp_def] using hB.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  constructor
  · intro h
    have hz : (∑ i, ∑ j, f i j) = 0 := by
      rw [hsum] at h
      linarith
    have hentry (i j : n) : f i j = 0 := by
      have hi := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => Finset.sum_nonneg fun j _ => hf i j)).mp hz i (Finset.mem_univ i)
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hf i j)).mp hi j (Finset.mem_univ j)
    change B * M = M * B
    apply Q.injective
    rw [map_mul, map_mul]
    change Q B * U = U * Q B
    rw [hD]
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases he : b i = b j
    · rw [he, mul_comm]
    · have hk := logKernel_pos (hB.eigenvalues_pos i) (hB.eigenvalues_pos j) he
      have hzero : Complex.normSq (U i j) = 0 :=
        (mul_eq_zero.mp (hentry i j)).resolve_left hk.ne'
      rw [Complex.normSq_eq_zero.mp hzero, mul_zero, zero_mul]
  · intro h
    have hc : Q B * U = U * Q B := by
      simpa only [map_mul, U] using congrArg Q h.eq
    rw [hD] at hc
    have hzero (i j : n) : f i j = 0 := by
      have he := congrArg (fun A : Matrix n n ℂ => A i j) hc
      simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at he
      by_cases hb : b i = b j
      · simp [f, hb]
      · have hdiff : ((b i - b j : ℝ) : ℂ) * U i j = 0 := by
          rw [Complex.ofReal_sub, sub_mul, mul_comm (b j : ℂ), he, sub_self]
        have hcast : ((b i - b j : ℝ) : ℂ) ≠ 0 := by
          exact_mod_cast (sub_ne_zero.mpr hb : b i - b j ≠ 0)
        have hU0 := (mul_eq_zero.mp hdiff).resolve_left hcast
        simp [f, hU0]
    rw [hsum]
    simp only [hzero, Finset.sum_const_zero, mul_zero]

open SpectralCeilingRelativeEntropy (overlap trace_cfc_product overlap_weighted_row
  overlap_weighted_column)

/-- The Nussbaum–Szkoła reference weight of the actual spectral pair (B³,M³). -/
def spectralWeight {B M : Matrix n n ℂ} (hB : B.IsHermitian) (hM : M.IsHermitian)
    (p : n × n) : ℝ :=
  hB.eigenvalues p.1 ^ 3 * overlap hB hM p.1 p.2

/-- Ratio of the positive cube roots of the two eigenvalues. -/
def spectralRatio {B M : Matrix n n ℂ} (hB : B.IsHermitian) (hM : M.IsHermitian)
    (p : n × n) : ℝ :=
  hM.eigenvalues p.2 / hB.eigenvalues p.1

private theorem spectral_moments (B M : Matrix n n ℂ) (hB : B.PosDef)
    (hM : M.IsHermitian) :
    let pi := spectralWeight hB.isHermitian hM
    let x := spectralRatio hB.isHermitian hM
    (∑ p, pi p) = (B ^ 3).trace.re ∧
    (∑ p, pi p * x p ^ 2) = (B * M ^ 2).trace.re ∧
    (∑ p, pi p * x p ^ 3) = (M ^ 3).trace.re ∧
    (∑ p, pi p * x p ^ 2 * Real.log (x p)) =
      (B * M ^ 2 * (cfc Real.log M - cfc Real.log B)).trace.re := by
  dsimp only
  let b := hB.isHermitian.eigenvalues
  let m := hM.eigenvalues
  let w := overlap hB.isHermitian hM
  let pi := spectralWeight hB.isHermitian hM
  let x := spectralRatio hB.isHermitian hM
  have hb (i : n) : 0 < b i := hB.eigenvalues_pos i
  have hB3 : (B ^ 3).trace.re = ∑ i, b i ^ 3 := by
    rw [← cfc_pow_id (R := ℝ) B 3 hB.isHermitian.isSelfAdjoint]
    exact D5.S3.Resource.LogDet.PathSpectralClassical.trace_cfc_eq_sum B hB.isHermitian _
  have hM3 : (M ^ 3).trace.re = ∑ j, m j ^ 3 := by
    rw [← cfc_pow_id (R := ℝ) M 3 hM.isSelfAdjoint]
    exact D5.S3.Resource.LogDet.PathSpectralClassical.trace_cfc_eq_sum M hM _
  have hS : (B * M ^ 2).trace.re = ∑ i, ∑ j, b i * m j ^ 2 * w i j := by
    have h := trace_cfc_product B M hB.isHermitian hM
      (id : ℝ → ℝ) (fun z => z ^ 2)
    rwa [cfc_id ℝ B hB.isHermitian.isSelfAdjoint, cfc_pow_id M 2 hM.isSelfAdjoint] at h
  have hL₁ : (B * M ^ 2 * cfc Real.log M).trace.re =
      ∑ i, ∑ j, b i * (m j ^ 2 * Real.log (m j)) * w i j := by
    have h := trace_cfc_product B M hB.isHermitian hM
      (id : ℝ → ℝ) (fun z => z ^ 2 * Real.log z)
    rw [cfc_id ℝ B hB.isHermitian.isSelfAdjoint, ← pow_mul_log_cfc hM 2, ← mul_assoc] at h
    exact h
  have hL₂ : (B * M ^ 2 * cfc Real.log B).trace.re =
      ∑ i, ∑ j, (b i * Real.log (b i)) * m j ^ 2 * w i j := by
    have h := trace_cfc_product B M hB.isHermitian hM
      (fun z : ℝ => z * Real.log z) (fun z => z ^ 2)
    have hBLog : cfc (fun z : ℝ => z * Real.log z) B = B * cfc Real.log B := by
      simpa only [pow_one] using (pow_mul_log_cfc hB.isHermitian 1).symm
    rw [hBLog, cfc_pow_id M 2 hM.isSelfAdjoint] at h
    rw [Matrix.trace_mul_cycle, ← (commute_log hB.isHermitian).eq]
    exact h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hB3, Fintype.sum_prod_type]
    exact overlap_weighted_row hB.isHermitian hM (fun i => b i ^ 3)
  · rw [hS, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    change b i ^ 3 * w i j * (m j / b i) ^ 2 = b i * m j ^ 2 * w i j
    field_simp [(hb i).ne']
    <;> ring
  · rw [hM3, Fintype.sum_prod_type]
    calc
      _ = ∑ i, ∑ j, m j ^ 3 * w i j := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        change b i ^ 3 * w i j * (m j / b i) ^ 3 = m j ^ 3 * w i j
        field_simp [(hb i).ne']
        <;> ring
      _ = _ := overlap_weighted_column hB.isHermitian hM (fun j => m j ^ 3)
  · rw [mul_sub, Matrix.trace_sub, Complex.sub_re, hL₁, hL₂, Fintype.sum_prod_type]
    simp only [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    change b i ^ 3 * w i j * (m j / b i) ^ 2 * Real.log (m j / b i) =
      b i * (m j ^ 2 * Real.log (m j)) * w i j -
        (b i * Real.log (b i)) * m j ^ 2 * w i j
    by_cases hm : m j = 0
    · simp [hm]
    · rw [Real.log_div hm (hb i).ne']
      field_simp [(hb i).ne']
      <;> ring

/-- The right slope in the actual spectral pair. Terms with zero overlap or
zero eigenvalue of M contribute zero to each weighted sum. -/
theorem hasDerivWithinAt_cubicEntropy_spectral_pair (B M : Matrix n n ℂ)
    (hB : B.PosDef) (hM : M.PosSemidef) :
    let pi := spectralWeight hB.isHermitian hM.isHermitian
    let x := spectralRatio hB.isHermitian hM.isHermitian
    HasDerivWithinAt (fun s : ℝ => cubicEntropy B (M + s • B))
      (9 * (∑ p, pi p * x p ^ 2 * Real.log (x p)) -
        3 * (∑ p, pi p * x p ^ 2) * Real.log (∑ p, pi p * x p ^ 3) +
        3 * correction B M) (Set.Ici 0) 0 := by
  dsimp only
  obtain ⟨_, hS, hT, hL⟩ := spectral_moments B M hB hM.isHermitian
  rw [hL, hS, hT]
  exact hasDerivWithinAt_cubicEntropy B M hB hM

set_option maxHeartbeats 2000000 in
/-- The exact entropy slope in the actual Nussbaum–Szkoła coordinates with the
normalized two-thirds tilt. Strict Jensen holds precisely when two supported
likelihood ratios differ, including when some overlap weights are zero. -/
theorem hasDerivAt_cubicEntropy_spectral_pair (B M : Matrix n n ℂ)
    (hB : B.PosDef) (hM : M.PosDef) (hNorm : (B ^ 3).trace.re = 1) :
    let pi := spectralWeight hB.isHermitian hM.isHermitian
    let x := spectralRatio hB.isHermitian hM.isHermitian
    let S := (B * M ^ 2).trace.re
    let T := (M ^ 3).trace.re
    let nu := fun p => pi p * x p ^ 2 / S
    let H := (∑ p, pi p * x p ^ 2 * Real.log (x p ^ 2)) - S * Real.log S
    let D := Real.log (∑ p, nu p * x p) - ∑ p, nu p * Real.log (x p)
    (∀ p, 0 ≤ pi p ∧ 0 < x p ∧ 0 ≤ nu p) ∧
      (∀ p, pi p = 0 ↔ overlap hB.isHermitian hM.isHermitian p.1 p.2 = 0) ∧
      (∑ p, pi p) = 1 ∧ (∑ p, nu p) = 1 ∧ 0 < S ∧ 0 < T ∧
      (∑ p, pi p * x p ^ 3 / T) = 1 ∧
      (∑ p, nu p * x p) = T / S ∧
      (∑ p, nu p * Real.log (x p)) =
        (B * M ^ 2 * (cfc Real.log M - cfc Real.log B)).trace.re / S ∧
      HasDerivAt (fun s : ℝ => cubicEntropy B (M + s • B))
        (3 * (H + correction B M - S * D)) 0 ∧
      0 ≤ D ∧
      (0 < D ↔ ∃ p q : n × n, pi p ≠ 0 ∧ pi q ≠ 0 ∧ x p ≠ x q) := by
  dsimp only
  let pi := spectralWeight hB.isHermitian hM.isHermitian
  let x := spectralRatio hB.isHermitian hM.isHermitian
  let S := (B * M ^ 2).trace.re
  let T := (M ^ 3).trace.re
  let L := (B * M ^ 2 * (cfc Real.log M - cfc Real.log B)).trace.re
  let nu := fun p : n × n => pi p * x p ^ 2 / S
  let H := (∑ p, pi p * x p ^ 2 * Real.log (x p ^ 2)) - S * Real.log S
  let D := Real.log (∑ p, nu p * x p) - ∑ p, nu p * Real.log (x p)
  obtain ⟨hpi, hS, hT, hL⟩ := spectral_moments B M hB hM.isHermitian
  change (∑ p, pi p) = (B ^ 3).trace.re at hpi
  change (∑ p, pi p * x p ^ 2) = S at hS
  change (∑ p, pi p * x p ^ 3) = T at hT
  change (∑ p, pi p * x p ^ 2 * Real.log (x p)) = L at hL
  rw [hNorm] at hpi
  have hp (p : n × n) : 0 ≤ pi p := by
    exact mul_nonneg (pow_nonneg (hB.eigenvalues_pos p.1).le 3) (sq_nonneg _)
  have hx (p : n × n) : 0 < x p :=
    div_pos (hM.eigenvalues_pos p.2) (hB.eigenvalues_pos p.1)
  obtain ⟨p, hpMem, hpPos⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun p _ => hp p)).mp (show 0 < ∑ p, pi p by rw [hpi]; norm_num)
  have hSpos : 0 < S := by
    rw [← hS]
    exact Finset.sum_pos' (fun q _ => mul_nonneg (hp q) (sq_nonneg _))
      ⟨p, hpMem, mul_pos hpPos (pow_pos (hx p) 2)⟩
  have hTpos : 0 < T := by
    rw [← hT]
    exact Finset.sum_pos' (fun q _ => mul_nonneg (hp q) (pow_nonneg (hx q).le 3))
      ⟨p, hpMem, mul_pos hpPos (pow_pos (hx p) 3)⟩
  have hzeroOverlap (p : n × n) :
      pi p = 0 ↔ overlap hB.isHermitian hM.isHermitian p.1 p.2 = 0 := by
    simp [pi, spectralWeight, (hB.eigenvalues_pos p.1).ne']
  have hLikelihood : (∑ p, pi p * x p ^ 3 / T) = 1 := by
    rw [← Finset.sum_div, hT, div_self hTpos.ne']
  have hnu (p : n × n) : 0 ≤ nu p :=
    div_nonneg (mul_nonneg (hp p) (sq_nonneg _)) hSpos.le
  have hnuSum : (∑ p, nu p) = 1 := by
    simp only [nu, ← Finset.sum_div, hS, div_self hSpos.ne']
  have hMean : (∑ p, nu p * x p) = T / S := by
    calc
      _ = ∑ p, (pi p * x p ^ 3) / S := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        dsimp only [nu]
        ring
      _ = _ := by rw [← Finset.sum_div, hT]
  have hMeanLog : (∑ p, nu p * Real.log (x p)) = L / S := by
    calc
      _ = ∑ p, (pi p * x p ^ 2 * Real.log (x p)) / S := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        dsimp only [nu]
        ring
      _ = _ := by rw [← Finset.sum_div, hL]
  have hEntropy : H = 2 * L - S * Real.log S := by
    dsimp only [H]
    congr 1
    rw [← hL, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Real.log_pow]
    push_cast
    ring
  have hD : D = Real.log T - Real.log S - L / S := by
    dsimp only [D]
    rw [hMean, hMeanLog, Real.log_div hTpos.ne' hSpos.ne']
  have hCoeff : 3 * (H + correction B M - S * D) =
      9 * L - 3 * S * Real.log T + 3 * correction B M := by
    rw [hEntropy, hD]
    field_simp [hSpos.ne']
    <;> ring
  have hd : HasDerivAt (fun s : ℝ => cubicEntropy B (M + s • B))
      (3 * (H + correction B M - S * D)) 0 := by
    rw [hCoeff]
    exact hasDerivAt_cubicEntropy B M hB hM
  have hjensen := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (t := Finset.univ) (w := nu) (p := x) (fun p _ => hnu p) hnuSum
    (fun p _ => hx p)
  have hDeficit : 0 ≤ D := by
    dsimp only [D]
    exact sub_nonneg.mpr (by simpa only [smul_eq_mul] using hjensen)
  have hsupport (p : n × n) : nu p ≠ 0 ↔ pi p ≠ 0 := by
    simp [nu, div_ne_zero_iff, mul_ne_zero_iff, (hx p).ne', hSpos.ne']
  have hstrict := strictConcaveOn_log_Ioi.lt_map_sum_iff_of_nonneg
    (t := Finset.univ) (w := nu) (p := x) (fun p _ => hnu p) hnuSum
      (fun p _ => hx p)
  have hStrict : 0 < D ↔ ∃ p q : n × n, pi p ≠ 0 ∧ pi q ≠ 0 ∧ x p ≠ x q := by
    dsimp only [D]
    rw [sub_pos]
    simpa only [smul_eq_mul, Finset.mem_univ, true_and, hsupport] using hstrict
  exact ⟨fun p => ⟨hp p, hx p, hnu p⟩, hzeroOverlap, hpi, hnuSum, hSpos, hTpos,
    hLikelihood, hMean, hMeanLog, hd, hDeficit, hStrict⟩

#print axioms correction_spectral
#print axioms correction_eq_bkm
#print axioms correction_nonneg
#print axioms correction_eq_zero_iff_commute
#print axioms hasDerivAt_cubicEntropy_spectral_pair
#print axioms hasDerivWithinAt_cubicEntropy_spectral_pair

end D5.S3.Quantum.Divergence.TraceEntropy.GibbsCubicTranslationEntropy
