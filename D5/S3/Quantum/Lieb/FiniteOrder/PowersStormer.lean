/- GID: D5/S3/Quantum/Lieb/FiniteOrder/PowersStormer
   generality: G
   mirror-B: D5/B/S3/Quantum/Lieb/FiniteOrder/PowersStormer
   mirror-E: none(waiver:registration-audit-pending)
   anchors: []
   utility: none
   digest: The finite doubled-order generalized Powers–Størmer inequality for arbitrary positive semidefinite complex matrices. -/
module

public import OmegaMath.Analysis.TraceRoof
public import D5.S3.Quantum.Lieb.FiniteOrder.SingularRatio
public import D5.S3.Quantum.Matrix.Spectral.TraceOrder
public import D5.S3.Quantum.Matrix.Spectral.TraceNorm

/-! The trace is the unnormalized canonical matrix trace. The quotient is
`t / f(t)` with total division, whose value at zero is zero. The common
roof is `B + posPart (A - B)` throughout the proof. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Quantum.Lieb.FiniteOrder
open Matrix
open D5.S3.Quantum.Lieb.FiniteOrderCompression
open D5.S3.Quantum.Lieb.TraceInverseConvexity
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

private theorem omegaEq_of_eq {α : Sort*} {a b : α} (h : a = b) : Omega.Eq a b := by
  cases h
  exact Omega.Eq.refl _

private theorem trace_pair_mono_left {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hAB : A ≤ B) (C : Matrix (Fin n) (Fin n) ℂ) (hC : C.PosSemidef) :
    (A * C).trace.re ≤ (B * C).trace.re := by
  simpa only [Matrix.trace_mul_comm C A, Matrix.trace_mul_comm C B] using
    weighted_trace_re_mono C hC hAB

private theorem quotient_product {n : ℕ} (f : ℝ → ℝ)
    (hfpos : ∀ t : ℝ, 0 < t → 0 < f t)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef) :
    cfc f A * cfc (fun t => t / f t) A = A := by
  rw [← cfc_mul f (fun t => t / f t) A (A.finite_real_spectrum.continuousOn _)
    (A.finite_real_spectrum.continuousOn _)]
  refine Eq.trans (b := cfc (id : ℝ → ℝ) A) ?_ (cfc_id ℝ A hA.isHermitian)
  apply cfc_congr
  intro t ht
  by_cases ht0 : t = 0
  · simp [ht0]
  · have hft : f t ≠ 0 := (hfpos t
      (lt_of_le_of_ne (spectrum_nonneg_of_nonneg hA.nonneg ht) (Ne.symm ht0))).ne'
    dsimp
    field_simp

/-- The generalized Powers–Størmer inequality with exactly finite order `2n`.
It includes zero dimension, singular noncommuting matrices and `f(0) = 0`.
No continuity of `t / f(t)` at zero is required. -/
theorem generalized_powers_stormer (n : ℕ) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ici 0))
    (hfpos : ∀ t : ℝ, 0 < t → 0 < f t)
    (hmono : ∀ (X Y : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ),
      X.PosSemidef → Y.PosSemidef → X ≤ Y → cfc f X ≤ cfc f Y)
    (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    A.trace.re + B.trace.re - traceNorm (A - B) ≤
      2 * (CFC.sqrt (cfc f A) * cfc (fun t => t / f t) B *
        CFC.sqrt (cfc f A)).trace.re := by
  have hf0 : 0 ≤ f 0 := by
    have ht := ((hf.continuousWithinAt (show (0 : ℝ) ∈ Set.Ici 0 by simp)).mono
      Set.Ioi_subset_Ici_self).tendsto
    exact ge_of_tendsto ht (Filter.mem_of_superset self_mem_nhdsWithin
      (fun t ht => (hfpos t ht).le))
  let P := posPart (A - B)
  let N := negPart (A - B)
  let C := B + P
  have hP : 0 ≤ P := CFC.posPart_nonneg (A - B)
  have hN : 0 ≤ N := CFC.negPart_nonneg (A - B)
  have hdiff : P - N = A - B :=
    CFC.posPart_sub_negPart (A - B) (hA.isHermitian.sub hB.isHermitian)
  have hC : C.PosSemidef := (add_nonneg hB.nonneg hP).posSemidef
  have hBC : B ≤ C := le_add_of_nonneg_right hP
  have hAC : A ≤ C := by
    apply sub_nonneg.mp
    have he : C - A = N := by
      calc
        C - A = P - (A - B) := by dsimp [C]; abel
        _ = N := by rw [← hdiff]; abel
    rw [he]
    exact hN
  have hfnonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ f t := by
    rcases ht.eq_or_lt with rfl | ht
    · exact hf0
    · exact (hfpos t ht).le
  have hfa : (cfc f A).PosSemidef := (cfc_nonneg (fun t ht =>
    hfnonneg t (spectrum_nonneg_of_nonneg hA.nonneg ht))).posSemidef
  have hgb : (cfc (fun t => t / f t) B).PosSemidef := (cfc_nonneg (fun t ht =>
    div_nonneg (spectrum_nonneg_of_nonneg hB.nonneg ht)
      (hfnonneg t (spectrum_nonneg_of_nonneg hB.nonneg ht)))).posSemidef
  have hbound := Omega.TraceRoof.common_roof (· ≤ ·) Matrix.PosSemidef (· - ·)
    (fun X : Matrix (Fin n) (Fin n) ℂ => X.trace.re)
    (fun X Y => (X * Y).trace.re) (· ≤ ·) (· - ·)
    (fun h k => le_trans h k) (fun h c => sub_le_sub_right h c)
    (fun h c => sub_le_sub_left h c) (by intros; linarith)
    Matrix.le_iff.mp trace_pair_mono_left
    (fun h C hC => weighted_trace_re_mono C hC h)
    (by
      intros
      apply omegaEq_of_eq
      simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]) A B C
    (cfc f A) (cfc f B) (cfc f C)
    (cfc (fun t => t / f t) A) (cfc (fun t => t / f t) B)
    (cfc (fun t => t / f t) C) hfa hgb
    (matrix_monotone_restrict n f hmono A C hA hC hAC)
    (matrix_monotone_restrict n f hmono B C hB hC hBC)
    (ratio_monotone_posSemidef n f hf hfpos hmono A C hA hC hAC)
    (ratio_monotone_posSemidef n f hf hfpos hmono B C hB hC hBC)
    (omegaEq_of_eq (congrArg (fun X : Matrix (Fin n) (Fin n) ℂ => X.trace.re)
      (quotient_product f hfpos A hA)))
    (omegaEq_of_eq (congrArg (fun X : Matrix (Fin n) (Fin n) ℂ => X.trace.re)
      (quotient_product f hfpos B hB)))
    (omegaEq_of_eq (congrArg (fun X : Matrix (Fin n) (Fin n) ℂ => X.trace.re)
      (quotient_product f hfpos C hC)))
  change A.trace.re - (C.trace.re - B.trace.re) ≤
    (cfc f A * cfc (fun t => t / f t) B).trace.re at hbound
  have hnorm := trace_norm_jordan_mass (A - B) (hA.isHermitian.sub hB.isHermitian)
  have htrace := congrArg (fun X : Matrix (Fin n) (Fin n) ℂ => X.trace.re) hdiff
  simp only [Matrix.trace_sub, Complex.sub_re] at htrace
  have hroof : C.trace.re = B.trace.re + P.trace.re := by
    simp only [C, Matrix.trace_add, Complex.add_re]
  have hsandwich : (CFC.sqrt (cfc f A) * cfc (fun t => t / f t) B *
      CFC.sqrt (cfc f A)).trace = (cfc f A * cfc (fun t => t / f t) B).trace := by
    rw [Matrix.trace_mul_comm (CFC.sqrt (cfc f A) * cfc (fun t => t / f t) B),
      ← Matrix.mul_assoc, CFC.sqrt_mul_sqrt_self _ hfa.nonneg]
  rw [hsandwich]
  dsimp [P, N] at htrace hroof
  linarith

#print axioms generalized_powers_stormer
#print axioms Omega.TraceRoof.common_roof
end D5.S3.Quantum.Lieb.FiniteOrder
