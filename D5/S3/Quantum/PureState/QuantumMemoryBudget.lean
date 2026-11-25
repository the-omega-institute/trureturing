/- GID: D5/S3/Quantum/PureState/QuantumMemoryBudget
   generality: G
   mirror-B: D5/B/S3/Quantum/PureState/QuantumMemoryBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every finite CPTP memory and POVM obey a diagonal budget for flat phase signals. -/

import D5.S3.Quantum.PureState.DistillationProfile
import D5.S3.Quantum.PureState.PhaseRecordSpectralMemory

namespace PhaseRecordDistillation

noncomputable section

open Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.PureState.PureStateHandshake
open D5.S3.Quantum.Subentropy.GuessingProbability
open JointRecordDecoding PhaseRecordMemory

variable {I X M : Type*} [Fintype I] [DecidableEq I] [Fintype X]
  [Fintype M] [DecidableEq M]

omit [DecidableEq I] in
/-- Rank-one expectations also apply to unnormalized vectors. -/
theorem trace_rankOne (F : Matrix I I ℂ) (v : I → ℂ) :
    trace (F * rankOneDensity v) = star v ⬝ᵥ (F *ᵥ v) := by
  rw [rankOneDensity, mul_vecMulVec, trace_vecMulVec, dotProduct_comm]

omit [DecidableEq I] in
theorem trace_rankOne_pair (u v : I → ℂ) :
    trace (rankOneDensity u * rankOneDensity v) =
      (‖star u ⬝ᵥ v‖ ^ 2 : ℝ) := by
  have hconj : star (star u ⬝ᵥ v) = star v ⬝ᵥ u := by
    simp [dotProduct, Pi.star_apply, mul_comm]
  rw [trace_rankOne, rankOneDensity, vecMulVec_mulVec, dotProduct_smul]
  change (star v ⬝ᵥ u) * (star u ⬝ᵥ v) = _
  rw [← hconj, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]

omit [DecidableEq I] in
private theorem ell2_triangle {J : Type*} [Fintype J] (v : J → I → ℂ) :
    Real.sqrt (∑ i, ‖∑ j, v j i‖ ^ 2) ≤
      ∑ j, Real.sqrt (∑ i, ‖v j i‖ ^ 2) := by
  let w (j : J) : PiLp 2 (fun _ : I => ℂ) := WithLp.toLp 2 (v j)
  have h : (∑ j, w j) = WithLp.toLp 2 (fun i => ∑ j, v j i) := by
    rw [← WithLp.toLp_sum]
    congr 1
    funext i
    exact Finset.sum_apply i _ _
  have hnorm := norm_sum_le Finset.univ w
  rw [h, PiLp.norm_eq_of_L2] at hnorm
  simpa only [w, PiLp.norm_eq_of_L2, PiLp.toLp_apply] using hnorm

/-- PSD Cauchy–Schwarz bounds the score by the weighted sum of square roots
of the effect's diagonal entries. -/
private theorem effect_score_le (F : Matrix I I ℂ) (hF : F.PosSemidef)
    (t : I → ℝ) (ht : ∀ i, 0 ≤ t i) (u : I → ℂ) (hu : ∀ i, ‖u i‖ = 1) :
    (trace (F * rankOneDensity (fun i => (t i : ℂ) * u i))).re ≤
      (∑ i, t i * Real.sqrt (F i i).re) ^ 2 := by
  let S := CFC.sqrt F
  have hSH : Sᴴ = S := (CFC.sqrt_nonneg F).posSemidef.isHermitian.eq
  have hSS : Sᴴ * S = F := by
    rw [hSH]
    exact CFC.sqrt_mul_sqrt_self F hF.nonneg
  have hdiag (i : I) : (F i i).re = ∑ k, ‖S k i‖ ^ 2 := by
    rw [← hSS, Matrix.mul_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [conjTranspose_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  let v (i : I) : ℂ := (t i : ℂ) * u i
  have htrace : (trace (F * rankOneDensity v)).re =
      ∑ k, ‖∑ i, S k i * v i‖ ^ 2 := by
    rw [trace_rankOne, ← hSS, ← mulVec_mulVec, dotProduct_mulVec,
      vecMul_conjTranspose, star_star, dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rfl
  have hv (i : I) : ‖v i‖ = t i := by simp [v, hu, abs_of_nonneg (ht i)]
  have hroot (i : I) :
      Real.sqrt (∑ k, ‖S k i * v i‖ ^ 2) = t i * Real.sqrt (F i i).re := by
    simp only [norm_mul, hv, mul_pow, ← Finset.sum_mul, hdiag]
    rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (ht i), mul_comm]
  have h := ell2_triangle (fun i k => S k i * v i)
  simp only [hroot] at h
  have hs : 0 ≤ ∑ k, ‖∑ i, S k i * v i‖ ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  change (trace (F * rankOneDensity v)).re ≤ _
  rw [htrace, ← Real.sq_sqrt hs]
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2

omit [DecidableEq I] in
/-- Minkowski in the label space combines per-effect diagonal bounds. -/
theorem sum_scores_le_of_effect_family (t : I → ℝ) (ht : ∀ i, 0 ≤ t i)
    (F : X → Matrix I I ℂ) (hF : ∀ x, (F x).PosSemidef)
    (u : X → I → ℂ) (hu : ∀ x i, ‖u x i‖ = 1) :
    (∑ x, (trace (F x * rankOneDensity (fun i => (t i : ℂ) * u x i))).re) ≤
      profileValue t (fun i => ∑ x, (F x i i).re) ^ 2 := by
  classical
  let w (i : I) (x : X) : ℂ := (t i * Real.sqrt (F x i i).re : ℝ)
  have hdiag (x : X) (i : I) : 0 ≤ (F x i i).re :=
    (Complex.nonneg_iff.mp ((hF x).diag_nonneg)).1
  have hw (i : I) (x : X) : 0 ≤ t i * Real.sqrt (F x i i).re :=
    mul_nonneg (ht i) (Real.sqrt_nonneg _)
  have hleft (x : X) : ‖∑ i, w i x‖ = ∑ i, t i * Real.sqrt (F x i i).re := by
    rw [show (∑ i, w i x) = ((∑ i, t i * Real.sqrt (F x i i).re : ℝ) : ℂ)
      by simp only [w, Complex.ofReal_sum]]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => hw i x)]
  have hright (i : I) :
      Real.sqrt (∑ x, ‖w i x‖ ^ 2) = t i * Real.sqrt (∑ x, (F x i i).re) := by
    simp only [w, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i _), mul_pow,
      Real.sq_sqrt (hdiag _ i), ← Finset.mul_sum]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (ht i)]
  have h := ell2_triangle w
  simp only [hleft, hright] at h
  calc
    _ ≤ ∑ x, (∑ i, t i * Real.sqrt (F x i i).re) ^ 2 :=
      Finset.sum_le_sum fun x _ => effect_score_le (F x) (hF x) t ht (u x) (hu x)
    _ ≤ _ := by
      rw [← Real.sq_sqrt (Finset.sum_nonneg fun x _ => sq_nonneg _)]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2

/-- Every encoder and measurement supplies a feasible diagonal profile that bounds its success.
Only flatness of the input phases is needed for this bound. -/
theorem exists_success_le_profile (t : I → ℝ) (ht : ∀ i, 0 ≤ t i)
    (u : X → I → ℂ) (hu : ∀ x i, ‖u x i‖ = 1)
    (hv : ∀ x, star (fun i => (t i : ℂ) * u x i) ⬝ᵥ (fun i => (t i : ℂ) * u x i) = 1)
    (Φ : QuantumChannel I M) (D : X → Matrix M M ℂ)
    (hD : ∀ x, (D x).PosSemidef) (hsD : ∑ x, D x = 1) :
    ∃ d : I → ℝ, Feasible d (Fintype.card M) ∧
      successProbability (uniformPrior X)
        (fun x => Φ.mapState (pureState (fun i => (t i : ℂ) * u x i) (hv x))) D ≤
      (Fintype.card X : ℝ)⁻¹ * profileValue t d ^ 2 := by
  obtain ⟨F, hF, hFE, hscore, htrace⟩ :=
    PhaseRecordSpectralMemory.exists_memory_effect_family _ hv Φ D hD
  let d (i : I) := ∑ x, (F x i i).re
  have hf (x : X) : (F x).PosSemidef := (hF x).posSemidef
  have hsum : ∑ x, F x ≤ 1 :=
    (Finset.sum_le_sum fun x _ => hFE x).trans_eq (sum_pullEffect Φ D hsD)
  refine ⟨d, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact fun i => Finset.sum_nonneg fun x _ => (Complex.nonneg_iff.mp (hf x).diag_nonneg).1
  · intro i
    have h := (Complex.nonneg_iff.mp ((Matrix.le_iff.mp hsum).diag_nonneg (i := i))).1
    simpa [d, Matrix.sub_apply, Matrix.sum_apply, Complex.re_sum, sub_nonneg] using h
  · calc
      ∑ i, d i = ∑ x, (trace (F x)).re := by
        simp only [d, trace, diag, Complex.re_sum]
        exact Finset.sum_comm
      _ ≤ ∑ x, (trace (D x)).re := Finset.sum_le_sum fun x _ => htrace x
      _ = _ := by rw [← Complex.re_sum, ← trace_sum, hsD, trace_one]; simp
  · unfold successProbability uniformPrior
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have he (x : X) :
        trace (D x * channelMatrix Φ (rankOneDensity (fun i => (t i : ℂ) * u x i))) =
          trace (F x * rankOneDensity (fun i => (t i : ℂ) * u x i)) := by
      rw [hscore, pullEffect_trace]
    change (∑ x, (trace (D x * channelMatrix Φ
      (rankOneDensity (fun i => (t i : ℂ) * u x i)))).re) ≤ _
    simp only [he]
    exact sum_scores_le_of_effect_family t ht F hf u hu

end

end PhaseRecordDistillation
