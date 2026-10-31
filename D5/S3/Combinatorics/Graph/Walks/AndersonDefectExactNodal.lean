/- GID: D5/S3/Combinatorics/Graph/Walks/AndersonDefectExactNodal
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/AndersonDefectExactNodal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Transcendental coupling excludes scalar periodic states at the defect node. -/

import D5.S3.Combinatorics.Graph.Walks.AndersonDefectFamily
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.FieldTheory.RatFunc.AsPolynomial

set_option autoImplicit false
open Matrix
open D5.S3.Combinatorics.SpectralGraph.CyclicTridiagonalTransferTrace
open private sl2_power from D5.S3.Combinatorics.Graph.Walks.AndersonDefectFamily

namespace D5.S3.Combinatorics.Graph.Walks.AndersonDefectExactNodal

private lemma rotated_entries {K : Type*} [Field K] (r : ℕ) (hr : 3 ≤ r) (a b : K) :
    let C := transfer a * transfer b * transfer a ^ (r - 2)
    let s := (Polynomial.Chebyshev.S K ((r : ℤ) - 2)).eval a
    let v := (Polynomial.Chebyshev.S K ((r : ℤ) - 3)).eval a
    C 1 0 = b * s - v ∧ C 0 0 = a * (b * s - v) - s := by
  dsimp only
  have hp := sl2_power (transfer a) (transfer_det a) (r - 2)
  have hi1 : ((r - 2 : ℕ) : ℤ) - 1 = (r : ℤ) - 3 := by omega
  have hi2 : ((r - 2 : ℕ) : ℤ) - 2 = (r : ℤ) - 4 := by omega
  rw [hi1, hi2] at hp
  have hs := congrArg (Polynomial.eval a) (Polynomial.Chebyshev.S_add_one K ((r : ℤ) - 3))
  have hi : (r : ℤ) - 3 + 1 = (r : ℤ) - 2 := by omega
  rw [hi] at hs
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X] at hs
  rw [hp]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Fin.sum_univ_two, transfer, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.trace_fin_two, Matrix.one_apply]
  constructor <;> linear_combination hs

/-- At a transcendental coupling, a periodic state fixed after a whole number of
blocks cannot be a scalar state for the block through the prescribed defect. -/
theorem rotated_block_cyclic {K : Type*} [Field K] [Algebra ℝ K]
    (r m : ℕ) (hr : 3 ≤ r) (hm : 3 ≤ m) (t μ : K)
    (ht : Transcendental ℝ t)
    (hfix : (transfer (2 + t - μ) * transfer (2 - t - μ) *
      transfer (2 + t - μ) ^ (r - 2)) ^ m *ᵥ ![1, 0] = ![1, 0]) :
    (transfer (2 + t - μ) * transfer (2 - t - μ) *
      transfer (2 + t - μ) ^ (r - 2)) 1 0 ≠ 0 := by
  classical
  let a := 2 + t - μ
  let b := 2 - t - μ
  let C := transfer a * transfer b * transfer a ^ (r - 2)
  let s := (Polynomial.Chebyshev.S K ((r : ℤ) - 2)).eval a
  let v := (Polynomial.Chebyshev.S K ((r : ℤ) - 3)).eval a
  change C 1 0 ≠ 0
  intro hzero
  have hc := rotated_entries r hr a b
  change C 1 0 = b * s - v ∧ C 0 0 = a * (b * s - v) - s at hc
  have hbs : b * s - v = 0 := hc.1.symm.trans hzero
  have he : C *ᵥ ![1, 0] = (-s) • ![1, 0] := by
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hc.1, hc.2, hbs]
  have hvec : (C.toLin').HasEigenvector (-s) ![1, 0] := by
    refine ⟨Module.End.mem_eigenspace_iff.mpr he, ?_⟩
    intro h
    have := congrFun h 0
    simp at this
  have hp := hvec.pow_apply m
  rw [← Matrix.toLin'_pow] at hp
  change C ^ m *ᵥ ![1, 0] = (-s) ^ m • ![1, 0] at hp
  have hpower : (-s) ^ m = 1 := by
    have hh := congrFun (hp.symm.trans hfix) 0
    simpa using hh
  have hsalg : IsAlgebraic ℝ s := by
    have hpa : IsAlgebraic ℝ ((-s) ^ m) := by rw [hpower]; exact isAlgebraic_one
    simpa using (IsAlgebraic.of_pow (by omega : 0 < m) hpa).neg
  let P := Polynomial.Chebyshev.S ℝ ((r : ℤ) - 2)
  have hP : P.natDegree = r - 2 := by
    have hi : (r : ℤ) - 2 = ((r - 2 : ℕ) : ℤ) := by omega
    dsimp [P]
    rw [hi]
    exact D5.S3.Combinatorics.Graph.PathCHS.PathCHSNormClosedForm.chebS_degree _
  have haalg : IsAlgebraic ℝ a := by
    apply IsAlgebraic.of_aeval P (by omega : P.natDegree ≠ 0)
      (mem_nonZeroDivisors_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr
        (Polynomial.ne_zero_of_natDegree_gt (by omega : 0 < P.natDegree))))
    simpa only [P, Polynomial.Chebyshev.aeval_S] using hsalg
  have alg_eval (Q : Polynomial ℝ) : IsAlgebraic ℝ (Polynomial.aeval a Q) :=
    (Algebra.isAlgebraic_adjoin_singleton_iff.mpr haalg) _
      (Polynomial.aeval_mem_adjoin_singleton Q ℝ a)
  have hvalg : IsAlgebraic ℝ v := by
    simpa only [Polynomial.Chebyshev.aeval_S] using
      alg_eval (Polynomial.Chebyshev.S ℝ ((r : ℤ) - 3))
  have hsne : s ≠ 0 := by
    intro h
    simpa [h, show m ≠ 0 by omega] using hpower
  have hb : b = v * s⁻¹ := by
    apply (eq_mul_inv_iff_mul_eq₀ hsne).mpr
    exact sub_eq_zero.mp hbs
  have hbalg : IsAlgebraic ℝ b := by
    rw [hb]
    exact hvalg.mul (IsAlgebraic.inv_iff.mpr hsalg)
  apply ht
  have hrel : t = (a - b) * (2 : K)⁻¹ := by dsimp [a, b]; ring
  rw [hrel]
  exact (haalg.sub hbalg).mul (IsAlgebraic.inv_iff.mpr (isAlgebraic_natCast 2))

end D5.S3.Combinatorics.Graph.Walks.AndersonDefectExactNodal
