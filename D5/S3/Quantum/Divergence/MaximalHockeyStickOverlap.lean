/- GID: D5/S3/Quantum/Divergence/MaximalHockeyStickOverlap
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/MaximalHockeyStickOverlap
   mirror-E: none(waiver:finite-spectral-proof)
   anchors: []
   utility: none
   digest: Exact finite-dimensional Hermitian overlap optimization and uniqueness. -/

import D5.S3.Weil.ZetaLinear.HermitianPosPart
import D5.S3.Quantum.Divergence.MaximalHockeyStickInterior
import Mathlib.Analysis.Matrix.Order
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

/-! The trace optimum under two Hermitian upper bounds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix
open Filter Topology
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator


namespace D5.S3.Quantum.Divergence.MaximalHockeyStickOverlap

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual positive-overlap feasible set, with two Loewner upper bounds. -/
def positiveOverlaps (A B : Matrix n n ℂ) : Set (Matrix n n ℂ) :=
  {X | 0 ≤ X ∧ X ≤ A ∧ X ≤ B}

/-- The supremum of the actual trace objective over positive overlaps. -/
def overlapValue (A B : Matrix n n ℂ) : ℝ :=
  sSup ((fun X : Matrix n n ℂ => X.trace.re) '' positiveOverlaps A B)

/-- The maximal hockey profile in its positive orientation. -/
def maximalHockey (A B : Matrix n n ℂ) (t : ℝ) : ℝ :=
  A.trace.re - overlapValue A (t • B)

private theorem positive_overlaps_compact (A B : Matrix n n ℂ) :
    IsCompact (positiveOverlaps A B) := by
  have hc : IsClosed (positiveOverlaps A B) :=
    (isClosed_le continuous_const continuous_id).inter
      ((isClosed_le continuous_id continuous_const).inter
        (isClosed_le continuous_id continuous_const))
  apply (isCompact_closedBall (0 : Matrix n n ℂ) ‖A‖).of_isClosed_subset hc
  intro X hX
  rw [Metric.mem_closedBall, dist_zero_right]
  exact CStarAlgebra.norm_le_norm_of_le_of_nonneg hX.2.1 hX.1

/-- The positive overlap optimum is attained for every PSD pair, including
zero matrices and singular nonorthogonal supports. -/
theorem overlap_attained (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ∃ X ∈ positiveOverlaps A B, X.trace.re = overlapValue A B := by
  have hn : (positiveOverlaps A B).Nonempty := ⟨0, le_rfl, hA.nonneg, hB.nonneg⟩
  have hcont : Continuous (fun X : Matrix n n ℂ => X.trace.re) := by
    unfold Matrix.trace
    fun_prop
  obtain ⟨X, hX, hmax⟩ := (positive_overlaps_compact A B).exists_isMaxOn hn hcont.continuousOn
  refine ⟨X, hX, ?_⟩
  apply le_antisymm
  · exact le_csSup (by
      refine ⟨X.trace.re, ?_⟩
      rintro _ ⟨Y, hY, rfl⟩
      exact hmax hY) ⟨X, hX, rfl⟩
  · apply csSup_le
    · exact hn.image _
    · rintro _ ⟨Y, hY, rfl⟩
      exact hmax hY

private theorem psd_column_zero {T : Matrix n n ℂ} (hT : T.PosSemidef)
    (i : n) (hi : T i i = 0) : ∀ j, T j i = 0 := by
  have hq : star (Pi.single i (1 : ℂ)) ⬝ᵥ (T *ᵥ Pi.single i 1) = 0 := by
    simpa using hi
  have hz := hT.dotProduct_mulVec_zero_iff.mp hq
  intro j
  simpa using congrFun hz j

private theorem diagonal_residual_bound (d : n → ℝ) (T : Matrix n n ℂ)
    (hT : T.PosSemidef) (hTH : (T - diagonal (fun i => (d i : ℂ))).PosSemidef) :
    (∑ i, max (d i) 0) ≤ T.trace.re ∧
      (T.trace.re = ∑ i, max (d i) 0 → T = diagonal (fun i => ((max (d i) 0 : ℝ) : ℂ))) := by
  classical
  have hdiag (i : n) : max (d i) 0 ≤ (T i i).re := by
    have h0 : 0 ≤ (T i i).re := (Complex.nonneg_iff.mp hT.diag_nonneg).1
    have h1 : 0 ≤ (T i i).re - d i := by
      have h := (Complex.nonneg_iff.mp (hTH.diag_nonneg (i := i))).1
      simpa only [Matrix.sub_apply, Matrix.diagonal_apply_eq, Complex.sub_re,
        Complex.ofReal_re] using h
    exact max_le (by linarith) h0
  have htrace : T.trace.re = ∑ i, (T i i).re := by
    simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum]
  refine ⟨by rw [htrace]; exact Finset.sum_le_sum fun i _ => hdiag i, ?_⟩
  intro heq
  have hsum : (∑ i, ((T i i).re - max (d i) 0)) = 0 := by
    rw [Finset.sum_sub_distrib, ← htrace, heq, sub_self]
  have he (i : n) : (T i i).re = max (d i) 0 :=
    sub_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => sub_nonneg.mpr (hdiag i))).mp hsum i (Finset.mem_univ i))
  have hreal (i : n) : T i i = ((T i i).re : ℂ) :=
    Complex.eq_re_of_ofReal_le (show (0 : ℂ) ≤ T i i from hT.diag_nonneg)
  ext j i
  by_cases hi : 0 < d i
  · have htii : (T - diagonal (fun i => (d i : ℂ))) i i = 0 := by
      rw [Matrix.sub_apply, Matrix.diagonal_apply_eq, hreal i, he i,
        max_eq_left hi.le, sub_self]
    have hz := psd_column_zero hTH i htii j
    have he' : T j i = (diagonal (fun i => (d i : ℂ))) j i := by
      exact sub_eq_zero.mp hz
    rw [he']
    by_cases hji : j = i
    · subst j
      simp only [Matrix.diagonal_apply_eq, max_eq_left hi.le]
    · simp only [Matrix.diagonal_apply_ne _ hji]
  · have hd : d i ≤ 0 := le_of_not_gt hi
    have htii : T i i = 0 := by rw [hreal i, he i, max_eq_right hd, Complex.ofReal_zero]
    rw [psd_column_zero hT i htii j]
    by_cases hji : j = i
    · subst j
      simp only [Matrix.diagonal_apply_eq, max_eq_right hd, Complex.ofReal_zero]
    · simp only [Matrix.diagonal_apply_ne _ hji]

/-- The positive part is the unique trace minimizer among positive matrices
dominating a given Hermitian matrix. This is trace minimization, with no claim
that the positive part is a Loewner least upper bound. -/
theorem positive_residual_unique (H T : Matrix n n ℂ) (hH : H.IsHermitian)
    (hT : T.PosSemidef) (hTH : (T - H).PosSemidef) :
    (RHLinalg.hermPosPart hH).trace.re ≤ T.trace.re ∧
      (T.trace.re = (RHLinalg.hermPosPart hH).trace.re → T = RHLinalg.hermPosPart hH) := by
  classical
  let e := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hH.eigenvectorUnitary
  have hspec : e (diagonal (fun i => (hH.eigenvalues i : ℂ))) = H := by
    simpa only [e, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using hH.spectral_theorem.symm
  have heH : e.symm H = diagonal (fun i => (hH.eigenvalues i : ℂ)) := by
    simpa only [e.symm_apply_apply] using (congrArg e.symm hspec).symm
  have hT' : (e.symm T).PosSemidef := (map_nonneg e.symm hT.nonneg).posSemidef
  have hTH' : (e.symm T - diagonal (fun i => (hH.eigenvalues i : ℂ))).PosSemidef := by
    have hp := (map_nonneg e.symm hTH.nonneg).posSemidef
    simpa only [map_sub, heH] using hp
  have htrace (X : Matrix n n ℂ) : (e X).trace = X.trace := by
    simp only [e, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
      Unitary.coe_star_mul_self, Matrix.one_mul]
  have htrace' : (e.symm T).trace = T.trace := by
    rw [← htrace (e.symm T), e.apply_symm_apply]
  have hpos : RHLinalg.hermPosPart hH =
      e (diagonal (fun i => ((max (hH.eigenvalues i) 0 : ℝ) : ℂ))) := rfl
  have hpTrace : (RHLinalg.hermPosPart hH).trace.re = ∑ i, max (hH.eigenvalues i) 0 := by
    rw [hpos, htrace, Matrix.trace_diagonal]
    simp only [Complex.re_sum, Complex.ofReal_re]
  obtain ⟨hle, heq⟩ := diagonal_residual_bound hH.eigenvalues (e.symm T) hT' hTH'
  rw [htrace'] at hle heq
  refine ⟨by simpa only [hpTrace] using hle, ?_⟩
  intro ht
  have hm := congrArg e (heq (by simpa only [hpTrace] using ht))
  simpa only [e.apply_symm_apply, ← hpos] using hm

/-- The unique optimum of the actual Hermitian two-upper-bound overlap
problem is `U - (U-V)₊`, including zero eigenvalues of `U-V`. -/
theorem hermitian_overlap_unique (U V : Matrix n n ℂ)
    (hU : U.IsHermitian) (hV : V.IsHermitian) :
    let X₀ := U - RHLinalg.hermPosPart (hU.sub hV)
    X₀.IsHermitian ∧ X₀ ≤ U ∧ X₀ ≤ V ∧
      ∀ X : Matrix n n ℂ, X.IsHermitian → X ≤ U → X ≤ V →
        X.trace.re ≤ X₀.trace.re ∧ (X.trace.re = X₀.trace.re → X = X₀) := by
  classical
  dsimp only
  let H := U - V
  let hp := hU.sub hV
  let R := RHLinalg.hermPosPart hp
  let Q := RHLinalg.hermNegPart hp
  have hR : R.PosSemidef := RHLinalg.hermPosPart_posSemidef hp
  have hQ : Q.PosSemidef := RHLinalg.hermNegPart_posSemidef hp
  have hH : R - Q = U - V := RHLinalg.hermPosPart_sub_hermNegPart hp
  have hX : U - R = V - Q := by
    have he := congrArg (fun M : Matrix n n ℂ => -M)
      (sub_eq_sub_iff_sub_eq_sub.mpr hH)
    simpa only [neg_sub] using he
  refine ⟨hU.sub hR.isHermitian, sub_le_self U hR.nonneg, ?_, ?_⟩
  · change U - R ≤ V
    rw [hX]
    exact sub_le_self V hQ.nonneg
  · intro X _ hXU hXV
    have hTX : (U - X).PosSemidef := Matrix.le_iff.mp hXU
    have hTXH : (U - X - (U - V)).PosSemidef := by
      convert Matrix.le_iff.mp hXV using 1 <;> abel
    obtain ⟨hle, heq⟩ := positive_residual_unique (U - V) (U - X) hp hTX hTXH
    simp only [Matrix.trace_sub, Complex.sub_re] at hle heq ⊢
    refine ⟨by linarith, ?_⟩
    intro ht
    have hr := heq (by linarith)
    change U - X = R at hr
    change X = U - R
    rw [← hr]
    abel

end D5.S3.Quantum.Divergence.MaximalHockeyStickOverlap
