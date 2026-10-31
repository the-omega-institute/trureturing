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
import Mathlib.LinearAlgebra.Eigenspace.Basic

set_option autoImplicit false
open Matrix
open D5.S3.Combinatorics.SpectralGraph.CyclicTridiagonalTransferTrace
open private sl2_power from D5.S3.Combinatorics.Graph.Walks.AndersonDefectFamily

namespace D5.S3.Combinatorics.Graph.Walks.AndersonDefectExactNodal

private theorem symmetric_nodal_kernel {K n : Type*} [Field K] [Fintype n]
    [DecidableEq n] (S : Matrix n n K) (hS : S.IsSymm) (j : n)
    (hd : S.det = 0)
    (hm : (S.submatrix (Subtype.val : {i : n // i ≠ j} → n) Subtype.val).det = 0) :
    ∃ z : n → K, z ≠ 0 ∧ S *ᵥ z = 0 ∧ z j = 0 := by
  classical
  obtain ⟨z, hz, he⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  by_cases hj : z j = 0
  · exact ⟨z, hz, he, hj⟩
  obtain ⟨w, hw, hminor⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hm
  let y : n → K := fun i => if hi : i ≠ j then w ⟨i, hi⟩ else 0
  have hyj : y j = 0 := by simp [y]
  have hy : y ≠ 0 := by
    intro h
    apply hw
    funext i
    have hh := congrFun h i.val
    simpa [y, i.property] using hh
  have haway (i : n) (hi : i ≠ j) : (S *ᵥ y) i = 0 := by
    have hh := congrFun hminor ⟨i, hi⟩
    have hsum := Fintype.sum_subtype_add_sum_subtype (fun k : n => k ≠ j)
      (fun k => S i k * y k)
    have hzero : (∑ k : {k : n // ¬ k ≠ j}, S i k * y k) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      have hk : k.val = j := by simpa using k.property
      simp [hk, hyj]
    rw [hzero, add_zero] at hsum
    change (∑ k : n, S i k * y k) = 0
    rw [← hsum]
    have hyn (k : {k : n // k ≠ j}) : y k = w k := by simp [y, k.property]
    simpa only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, hyn, Pi.zero_apply] using hh
  have hsupport : S *ᵥ y = Pi.single j ((S *ᵥ y) j) := by
    funext i
    by_cases hi : i = j
    · subst i; simp
    · simp [hi, haway i hi]
  have hdot : z j * (S *ᵥ y) j = 0 := by
    have hcomm := hS.dotProduct_mulVec_comm (x := z) (y := y)
    rw [he, dotProduct_zero, hsupport] at hcomm
    simpa [dotProduct, Pi.single_apply] using hcomm
  have hjzero : (S *ᵥ y) j = 0 := (mul_eq_zero.mp hdot).resolve_left hj
  refine ⟨y, hy, ?_, hyj⟩
  rw [hsupport, hjzero]
  simp

open D5.S3.Combinatorics.Graph.Walks.AndersonDefectSeed
open D5.S3.Combinatorics.Graph.Walks.AndersonDefectFamily

private theorem common_root_nodal {K : Type*} [Field K]
    (r m : ℕ) (hr : 3 ≤ r) (hm : 3 ≤ m) (t μ : K)
    (hp : (hamiltonian r m t).charpoly.IsRoot μ)
    (hq : (deleted r m t ⟨defectSite r m,
      by have := defect_bounds r m hr (by omega); omega⟩).charpoly.IsRoot μ) :
    ∃ z : Fin (r * m) → K, z ≠ 0 ∧ hamiltonian r m t *ᵥ z = μ • z ∧
      z ⟨defectSite r m, by have := defect_bounds r m hr (by omega); omega⟩ = 0 := by
  classical
  let j : Fin (r * m) := ⟨defectSite r m,
    by have := defect_bounds r m hr (by omega); omega⟩
  let H := hamiltonian r m t
  let S := μ • (1 : Matrix (Fin (r * m)) (Fin (r * m)) K) - H
  have hsym : S.IsSymm := (Matrix.isSymm_one.smul μ).sub
    ((SimpleGraph.isSymm_lapMatrix K _).add ((Matrix.isSymm_diagonal _).smul t))
  have hd : S.det = 0 := by
    simpa only [Polynomial.IsRoot, Matrix.eval_charpoly, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal, S, H] using hp
  have hsub : S.submatrix (Subtype.val : {i : Fin (r * m) // i ≠ j} → Fin (r * m))
      Subtype.val = μ • 1 - deleted r m t j := by
    ext i k
    simp [S, H, deleted, Matrix.submatrix_apply, Matrix.one_apply,
      Subtype.ext_iff]
  have hmnr : (S.submatrix (Subtype.val : {i : Fin (r * m) // i ≠ j} → Fin (r * m))
      Subtype.val).det = 0 := by
    rw [hsub]
    simpa only [Polynomial.IsRoot, Matrix.eval_charpoly, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal] using hq
  obtain ⟨z, hz, he, hj⟩ := symmetric_nodal_kernel S hsym j hd hmnr
  refine ⟨z, hz, ?_, hj⟩
  change (μ • (1 : Matrix (Fin (r * m)) (Fin (r * m)) K) - H) *ᵥ z = 0 at he
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at he
  exact he.symm

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
  have hi3 : (r : ℤ) - 3 - 1 = (r : ℤ) - 4 := by omega
  rw [hi3] at hs
  simp [transfer, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two]
  constructor
  · linear_combination -b * hs
  · linear_combination (1 - a * b) * hs

/-- At a transcendental coupling, a periodic state fixed after a whole number of
blocks cannot be a scalar state for the block through the prescribed defect. -/
private theorem rotated_block_cyclic {K : Type*} [Field K] [Algebra ℝ K]
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
  have hvec : Module.End.HasEigenvector C.toLin' (-s) ![1, 0] := by
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
      (Q.aeval_mem_adjoin_singleton ℝ a)
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
  have htwo : (2 : K) ≠ 0 := by
    have hh := (algebraMap ℝ K).injective.ne (by norm_num : (2 : ℝ) ≠ 0)
    simpa only [map_ofNat, map_zero] using hh
  have hrel : t = (a - b) * (2 : K)⁻¹ := by
    dsimp [a, b]
    field_simp [htwo]
    <;> ring
  rw [hrel]
  exact (haalg.sub hbalg).mul (IsAlgebraic.inv_iff.mpr (isAlgebraic_natCast 2))

end D5.S3.Combinatorics.Graph.Walks.AndersonDefectExactNodal
