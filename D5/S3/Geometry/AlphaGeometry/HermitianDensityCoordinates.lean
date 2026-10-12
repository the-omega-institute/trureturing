/- GID: D5/S3/Geometry/AlphaGeometry/HermitianDensityCoordinates
   generality: G
   mirror-B: D5/B/S3/Geometry/AlphaGeometry/HermitianDensityCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Real Hermitian trace-one coordinates and their positive open domain. -/

/-
admission_basis: escape-witness
escape_witness: hermitian_trace_one_chart_equiv
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15716
The grid readout reconstructs all Hermitian entries; the trace equation recovers the final diagonal.
Direct frozen dependencies: none.
Per-declaration classification; non-proposition definitions carry no content claim.
proof_shape: G: bind-only; escape_witness: none; consumers: HermitianDensityCoordinates.rho, HermitianDensityCoordinates.G_isHermitian, HermitianDensityCoordinates.G_trace, HermitianDensityCoordinates.rho_isHermitian, HermitianDensityCoordinates.rho_trace, HermitianDensityCoordinates.rho_continuous, HermitianDensityCoordinates.G_diag_re, HermitianDensityCoordinates.G_upper_re, HermitianDensityCoordinates.G_lower_im, HermitianDensityCoordinates.chart_left_inverse, HermitianCubeDerivative.rho_contDiff, HermitianCubeDerivative.rhoLinearMap, HermitianCubeDerivative.rhoH_affine; frozen_dependencies: none
proof_shape: rho: bind-only; escape_witness: none; consumers: HermitianDensityCoordinates.rho_isHermitian, HermitianDensityCoordinates.rho_trace, HermitianDensityCoordinates.rho_continuous, HermitianDensityCoordinates.chart_left_inverse, HermitianDensityCoordinates.hermitian_trace_one_chart_equiv, HermitianDensityCoordinates.positive_chart_open, HermitianCubeDerivative.rhoH, HermitianCubeDerivative.rhoH_val, HermitianCubeDerivative.rho_contDiff, HermitianCubeDerivative.rhoH_contDiff, HermitianCubeDerivative.rhoH_affine, HermitianCubeDerivative.rhoLinear_injective, HermitianCubeDerivative.immersion_contDiffAt, HermitianCubeDerivative.immersion_derivative_injective, HermitianCubeDerivative.immersion_level_one, QuantumCubeRootScalarCurvatureMonotone.metric, QuantumCubeRootScalarCurvatureMonotone.tangentFrame_independent, QuantumCubeRootScalarCurvatureMonotone.rootMetric_posdef, QuantumCubeRootScalarCurvatureMonotone.metric_eq_nine_rootMetric, QuantumCubeRootScalarCurvatureMonotone.immersion_normal_tangent, QuantumCubeRootScalarCurvatureMonotone.fullFrame_injective, QuantumCubeRootScalarCurvatureMonotone.fullFrameEquiv, QuantumCubeRootScalarCurvatureMonotone.frame_smooth, QuantumCubeRootScalarCurvatureMonotone.de_smooth, QuantumCubeRootScalarCurvatureMonotone.N_smooth, QuantumCubeRootScalarCurvatureMonotone.b_smooth, QuantumCubeRootScalarCurvatureMonotone.metric_entry_smooth, QuantumCubeRootScalarCurvatureMonotone.frame_second, QuantumCubeRootScalarCurvatureMonotone.de_symm, QuantumCubeRootScalarCurvatureMonotone.de_mixed, QuantumCubeRootScalarCurvatureMonotone.N_unit, QuantumCubeRootScalarCurvatureMonotone.N_orthogonal, QuantumCubeRootScalarCurvatureMonotone.DN_orthogonal, QuantumCubeRootScalarCurvatureMonotone.DN_frame, QuantumCubeRootScalarCurvatureMonotone.christoffel_frame, QuantumCubeRootScalarCurvatureMonotone.metric_isUnit, QuantumCubeRootScalarCurvatureMonotone.dual_frame, QuantumCubeRootScalarCurvatureMonotone.dual_N, QuantumCubeRootScalarCurvatureMonotone.dual_derivative, QuantumCubeRootScalarCurvatureMonotone.frame_decomposition, QuantumCubeRootScalarCurvatureMonotone.inverse_metric_smooth, QuantumCubeRootScalarCurvatureMonotone.christoffel_smooth, QuantumCubeRootScalarCurvatureMonotone.frame_structure, QuantumCubeRootScalarCurvatureMonotone.b_symm, QuantumCubeRootScalarCurvatureMonotone.DN_dual, QuantumCubeRootScalarCurvatureMonotone.coordinate_ricci, QuantumCubeRootScalarCurvatureMonotone.ricci_matrix_gauss, QuantumCubeRootScalarCurvatureMonotone.coordinate_gauss_scalar, QuantumCubeRootScalarCurvatureMonotone.DN_shape_derivative, QuantumCubeRootScalarCurvatureMonotone.DN_dual_vector, QuantumCubeRootScalarCurvatureMonotone.DN_fullFrame, QuantumCubeRootScalarCurvatureMonotone.shape_conjugate, QuantumCubeRootScalarCurvatureMonotone.shape_trace, QuantumCubeRootScalarCurvatureMonotone.shape_square_trace, QuantumCubeRootScalarCurvatureMonotone.coordinate_shape_gauss, QuantumCubeRootScalarCurvatureMonotone.chart_scalar_spectral, QuantumCubeRootScalarCurvatureMonotone.scal3_eq_spectral_ratio; frozen_dependencies: none
proof_shape: chartPoint: bind-only; escape_witness: none; consumers: HermitianDensityCoordinates.chart_left_inverse, HermitianDensityCoordinates.chart_at_grid, HermitianDensityCoordinates.extract_real, HermitianDensityCoordinates.extract_imag, HermitianDensityCoordinates.entry_eq_nonfinal, HermitianDensityCoordinates.chart_injective, HermitianDensityCoordinates.hermitian_trace_one_chart_equiv, HermitianCubeDerivative.rhoLinear_injective, QuantumCubeRootScalarCurvatureMonotone.scal3, QuantumCubeRootScalarCurvatureMonotone.scal3_eq_spectral_ratio; frozen_dependencies: none
proof_shape: G_isHermitian: bind-only; escape_witness: none; consumers: HermitianDensityCoordinates.rho_isHermitian; frozen_dependencies: none
proof_shape: G_indices: bind-only; escape_witness: none; consumers: HermitianDensityCoordinates.G_trace, HermitianDensityCoordinates.G_diag_re, HermitianDensityCoordinates.G_upper_re, HermitianDensityCoordinates.G_lower_im, HermitianDensityCoordinates.chart_left_inverse; frozen_dependencies: none
proof_shape: G_diagonal_not_last: bind-only; escape_witness: none; consumers: HermitianDensityCoordinates.G_diag_re; frozen_dependencies: none
proof_shape: G_trace: bind-only; escape_witness: none; consumers: HermitianDensityCoordinates.rho_trace; frozen_dependencies: none
proof_shape: rho_isHermitian: bind-only; escape_witness: none; consumers: HermitianDensityCoordinates.hermitian_trace_one_chart_equiv, HermitianDensityCoordinates.positive_chart_open, HermitianCubeDerivative.rhoH_val; frozen_dependencies: none
proof_shape: rho_trace: bind-only; escape_witness: none; consumers: HermitianDensityCoordinates.hermitian_trace_one_chart_equiv, HermitianCubeDerivative.immersion_level_one; frozen_dependencies: none
proof_shape: rho_continuous: bind-only; escape_witness: none; consumers: HermitianDensityCoordinates.positive_chart_open; frozen_dependencies: none
proof_shape: grid_injective: bind-only; escape_witness: none; consumers: HermitianDensityCoordinates.G_diag_re, HermitianDensityCoordinates.G_upper_re, HermitianDensityCoordinates.G_lower_im; frozen_dependencies: none
proof_shape: G_diag_re: bind-only; escape_witness: none; consumers: HermitianDensityCoordinates.chart_left_inverse; frozen_dependencies: none
proof_shape: G_upper_re: bind-only; escape_witness: none; consumers: HermitianDensityCoordinates.chart_left_inverse; frozen_dependencies: none
proof_shape: G_lower_im: bind-only; escape_witness: none; consumers: HermitianDensityCoordinates.chart_left_inverse; frozen_dependencies: none
proof_shape: chart_left_inverse: content; escape_witness: HermitianDensityCoordinates.chart_left_inverse; consumers: HermitianDensityCoordinates.hermitian_trace_one_chart_equiv, HermitianCubeDerivative.rhoLinear_injective; frozen_dependencies: none
proof_shape: grid_lt: bind-only; escape_witness: none; consumers: HermitianDensityCoordinates.gridIndex; frozen_dependencies: none
proof_shape: gridIndex: bind-only; escape_witness: none; consumers: HermitianDensityCoordinates.gridIndex_row, HermitianDensityCoordinates.gridIndex_col, HermitianDensityCoordinates.chart_at_grid, HermitianDensityCoordinates.extract_real, HermitianDensityCoordinates.extract_imag; frozen_dependencies: none
proof_shape: gridIndex_row: bind-only; escape_witness: none; consumers: HermitianDensityCoordinates.chart_at_grid; frozen_dependencies: none
proof_shape: gridIndex_col: bind-only; escape_witness: none; consumers: HermitianDensityCoordinates.chart_at_grid; frozen_dependencies: none
proof_shape: chart_at_grid: bind-only; escape_witness: none; consumers: HermitianDensityCoordinates.extract_real, HermitianDensityCoordinates.extract_imag; frozen_dependencies: none
proof_shape: extract_real: bind-only; escape_witness: none; consumers: HermitianDensityCoordinates.entry_eq_nonfinal; frozen_dependencies: none
proof_shape: extract_imag: bind-only; escape_witness: none; consumers: HermitianDensityCoordinates.entry_eq_nonfinal; frozen_dependencies: none
proof_shape: diagonal_imag_zero: bind-only; escape_witness: none; consumers: HermitianDensityCoordinates.entry_eq_nonfinal, HermitianDensityCoordinates.chart_injective; frozen_dependencies: none
proof_shape: entry_eq_nonfinal: content; escape_witness: HermitianDensityCoordinates.entry_eq_nonfinal; consumers: HermitianDensityCoordinates.chart_injective; frozen_dependencies: none
proof_shape: chart_injective: content; escape_witness: HermitianDensityCoordinates.chart_injective; consumers: HermitianDensityCoordinates.hermitian_trace_one_chart_equiv; frozen_dependencies: none
proof_shape: hermitian_trace_one_chart_equiv: content; escape_witness: HermitianDensityCoordinates.chart_left_inverse; consumers: QuantumCubeRootScalarCurvatureMonotone.scal3_eq_spectral_ratio; frozen_dependencies: none
proof_shape: hermitian_posdef_open: bind-only; escape_witness: none; consumers: HermitianDensityCoordinates.positive_chart_open, HermitianCubeDerivative.positive_open; frozen_dependencies: none
proof_shape: positive_chart_open: bind-only; escape_witness: none; consumers: QuantumCubeRootScalarCurvatureMonotone.immersion_normal_tangent, QuantumCubeRootScalarCurvatureMonotone.DN_orthogonal, QuantumCubeRootScalarCurvatureMonotone.DN_frame, QuantumCubeRootScalarCurvatureMonotone.christoffel_smooth, QuantumCubeRootScalarCurvatureMonotone.coordinate_ricci, QuantumCubeRootScalarCurvatureMonotone.chart_scalar_spectral; frozen_dependencies: none
-/


import Mathlib.Analysis.Matrix.Order

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Filter Topology
namespace D5.S3.Geometry.AlphaGeometry.HermitianDensityCoordinates

def G (n : ℕ) (k : Fin (n^2-1)) : Matrix (Fin n) (Fin n) ℂ := fun r s =>
  let row := k.val / n
  let col := k.val % n
  if row = col then
    (if r.val = row ∧ s.val = row then 1 else 0) -
      (if r.val = n-1 ∧ s.val = n-1 then 1 else 0)
  else if row < col then
    if (r.val = row ∧ s.val = col) ∨ (r.val = col ∧ s.val = row) then 1 else 0
  else
    (if r.val = row ∧ s.val = col then Complex.I else 0) -
      (if r.val = col ∧ s.val = row then Complex.I else 0)

def rho {n : ℕ} (x : Fin (n^2-1) → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  ((1 : ℝ)/(n : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℂ) + ∑ k, x k • G n k

def chartPoint {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Fin (n^2-1) → ℝ := fun k =>
  let row := k.val / n
  let col := k.val % n
  if h : row < n ∧ col < n then
    let entry := A ⟨row,h.1⟩ ⟨col,h.2⟩
    if row = col then entry.re - 1/(n : ℝ)
    else if row < col then entry.re else entry.im
  else 0

private lemma G_isHermitian (n : ℕ) (k : Fin (n^2-1)) : (G n k).IsHermitian := by
  unfold Matrix.IsHermitian
  ext r s
  simp only [Matrix.conjTranspose_apply]
  unfold G
  dsimp only
  split_ifs <;> simp_all [and_comm,or_comm] <;> aesop

private lemma G_indices {n : ℕ} (hn : 0 < n) (k : Fin (n^2-1)) :
    k.val / n < n ∧ k.val % n < n := by
  refine ⟨(Nat.div_lt_iff_lt_mul hn).mpr ?_,Nat.mod_lt _ hn⟩
  have hk := k.isLt
  nlinarith [Nat.sub_le (n^2) 1]

private lemma G_diagonal_not_last {n : ℕ} (hn : 0 < n) (k : Fin (n^2-1))
    (heq : k.val / n = k.val % n) : k.val / n ≠ n-1 := by
  intro hlast
  have hd := Nat.div_add_mod k.val n
  have hk := k.isLt
  have hcol : k.val % n = n-1 := heq.symm.trans hlast
  rw [hlast,hcol] at hd
  have hnm : n-1+1=n := Nat.sub_add_cancel hn
  have hn2 : 1 ≤ n^2 := by nlinarith
  have hsub : n^2-1+1=n^2 := Nat.sub_add_cancel hn2
  nlinarith

private lemma G_trace {n : ℕ} (hn : 0 < n) (k : Fin (n^2-1)) : (G n k).trace = 0 := by
  classical
  by_cases heq : k.val / n = k.val % n
  · let r0 : Fin n := ⟨k.val/n,(G_indices hn k).1⟩
    let last : Fin n := ⟨n-1,Nat.sub_lt hn (by decide)⟩
    have hrow (r : Fin n) : r.val = k.val/n ↔ r = r0 := by
      change r.val = r0.val ↔ r = r0
      exact Fin.ext_iff.symm
    have hlast (r : Fin n) : r.val = n-1 ↔ r = last := by
      change r.val = last.val ↔ r = last
      exact Fin.ext_iff.symm
    simp only [Matrix.trace,Matrix.diag,G,if_pos heq,and_self]
    simp_rw [hrow,hlast]
    simp
  · unfold Matrix.trace
    apply Finset.sum_eq_zero
    intro r _
    dsimp only [Matrix.diag,G]
    split_ifs <;> simp_all <;> aesop

theorem rho_isHermitian {n : ℕ} (x : Fin (n^2-1) → ℝ) : (rho x).IsHermitian := by
  unfold rho
  apply Matrix.IsHermitian.add
  · exact Matrix.isHermitian_one.smul (IsSelfAdjoint.all _)
  · have H (s : Finset (Fin (n^2-1))) : (∑ k ∈ s, x k • G n k).IsHermitian := by
      induction s using Finset.induction with
      | empty => simpa using (Matrix.isHermitian_zero : (0 : Matrix (Fin n) (Fin n) ℂ).IsHermitian)
      | insert k s hks ih =>
        rw [Finset.sum_insert hks]
        exact ((G_isHermitian n k).smul (IsSelfAdjoint.all _)).add ih
    exact H Finset.univ

theorem rho_trace {n : ℕ} (hn : 0 < n) (x : Fin (n^2-1) → ℝ) : (rho x).trace = 1 := by
  simp only [rho,Matrix.trace_add,Matrix.trace_sum,Matrix.trace_smul,G_trace hn,
    smul_zero,Finset.sum_const_zero,add_zero,Matrix.trace_one,Fintype.card_fin]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  change ((1 : ℝ)/(n : ℝ)) • (n : ℂ) = 1
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  simp [Complex.real_smul,hnC]

private theorem rho_continuous (n : ℕ) : Continuous (@rho n) := by
  unfold rho
  fun_prop


private lemma grid_injective {n : ℕ} {k l : Fin (n^2-1)}
    (hr : k.val / n = l.val / n) (hc : k.val % n = l.val % n) : k = l := by
  apply Fin.ext
  have hk := Nat.div_add_mod k.val n
  have hl := Nat.div_add_mod l.val n
  rw [hr,hc] at hk
  exact hk.symm.trans hl

private lemma G_diag_re {n : ℕ} (hn : 0 < n) (k l : Fin (n^2-1))
    (hk : k.val/n = k.val%n) :
    (G n l ⟨k.val/n,(G_indices hn k).1⟩ ⟨k.val%n,(G_indices hn k).2⟩).re =
      if l = k then 1 else 0 := by
  have hlast := G_diagonal_not_last hn k hk
  by_cases he : l = k
  · subst l
    simp [G,hk,show k.val%n ≠ n-1 by omega]
  · have hd : ¬(l.val/n = l.val%n ∧ k.val/n = l.val/n ∧ k.val%n = l.val/n) := by
      intro h
      apply he
      exact grid_injective h.2.1.symm (by omega)
    unfold G
    dsimp only
    split_ifs <;> norm_num <;> try omega
    all_goals first | contradiction | aesop

private lemma G_upper_re {n : ℕ} (hn : 0 < n) (k l : Fin (n^2-1))
    (hk : k.val/n < k.val%n) :
    (G n l ⟨k.val/n,(G_indices hn k).1⟩ ⟨k.val%n,(G_indices hn k).2⟩).re =
      if l = k then 1 else 0 := by
  by_cases he : l = k
  · subst l
    simp [G,show ¬k.val/n = k.val%n by omega,hk,Complex.I_re]
  · have hf : ¬(k.val/n = l.val/n ∧ k.val%n = l.val%n) := by
      intro h; exact he (grid_injective h.1.symm h.2.symm)
    have hr : ¬(l.val/n < l.val%n ∧ k.val/n = l.val%n ∧ k.val%n = l.val/n) := by omega
    unfold G
    dsimp only
    split_ifs <;> norm_num <;> omega

private lemma G_lower_im {n : ℕ} (hn : 0 < n) (k l : Fin (n^2-1))
    (hk : k.val%n < k.val/n) :
    (G n l ⟨k.val/n,(G_indices hn k).1⟩ ⟨k.val%n,(G_indices hn k).2⟩).im =
      if l = k then 1 else 0 := by
  by_cases he : l = k
  · subst l
    simp [G,show ¬k.val/n = k.val%n by omega,show ¬k.val/n < k.val%n by omega,
      Complex.I_im,show ¬(k.val/n = k.val%n ∧ k.val%n = k.val/n) by omega]
  · have hf : ¬(k.val/n = l.val/n ∧ k.val%n = l.val%n) := by
      intro h; exact he (grid_injective h.1.symm h.2.symm)
    have hr : ¬(l.val%n ≤ l.val/n ∧ k.val/n = l.val%n ∧ k.val%n = l.val/n) := by omega
    unfold G
    dsimp only
    split_ifs <;> norm_num <;> omega

theorem chart_left_inverse {n : ℕ} (hn : 0 < n) : ∀ x : Fin (n^2-1) → ℝ, chartPoint (rho x) = x := by
  intro x
  funext k
  let r : Fin n := ⟨k.val/n,(G_indices hn k).1⟩
  let c : Fin n := ⟨k.val%n,(G_indices hn k).2⟩
  simp only [chartPoint,dif_pos (G_indices hn k)]
  change (if k.val/n = k.val%n then (rho x r c).re - 1/(n : ℝ)
    else if k.val/n < k.val%n then (rho x r c).re else (rho x r c).im) = x k
  rcases lt_trichotomy (k.val/n) (k.val%n) with hk | hk | hk
  · have hrc : r ≠ c := by intro he; have := congrArg Fin.val he; dsimp [r,c] at this; omega
    simp only [if_neg (ne_of_lt hk),if_pos hk]
    simp [rho,Matrix.sum_apply,Matrix.one_apply,hrc,Complex.re_sum,Complex.smul_re,
      r,c,G_upper_re hn k _ hk]
  · simp only [if_pos hk]
    have hrc : r = c := Fin.ext hk
    simp only [rho,Matrix.add_apply,Matrix.smul_apply,Matrix.sum_apply,
      Complex.add_re,Complex.re_sum,Complex.smul_re,smul_eq_mul]
    rw [show (1 : Matrix (Fin n) (Fin n) ℂ) r c = 1 by simp [Matrix.one_apply,hrc]]
    simp only [Complex.one_re,mul_one]
    have hd (l : Fin (n^2-1)) : (G n l r c).re = if l=k then 1 else 0 := G_diag_re hn k l hk
    simp_rw [hd]
    simp
  · simp only [if_neg (ne_of_gt hk),if_neg (not_lt_of_ge hk.le)]
    have hrc : r ≠ c := by intro he; have := congrArg Fin.val he; dsimp [r,c] at this; omega
    simp [rho,Matrix.sum_apply,Matrix.one_apply,hrc,Complex.im_sum,Complex.smul_im,r,c,G_lower_im hn k _ hk]

private lemma grid_lt {n : ℕ} (hn : 0 < n) (r s : Fin n)
    (h : r.val ≠ n-1 ∨ s.val ≠ n-1) : n*r.val+s.val < n^2-1 := by
  have hn2 : 1 ≤ n^2 := by nlinarith
  have hsub : n^2-1+1 = n^2 := Nat.sub_add_cancel hn2
  have hr := r.isLt
  have hs := s.isLt
  have hr' : r.val ≤ n-1 := by omega
  have hs' : s.val ≤ n-1 := by omega
  rcases h with h | h
  · have hr'' : r.val+2 ≤ n := by omega
    have hmul : n*(r.val+2) ≤ n*n := Nat.mul_le_mul_left n hr''
    nlinarith [Nat.sub_add_cancel hn,hsub]
  · have hs'' : s.val+2 ≤ n := by omega
    have hmul : n*(r.val+1) ≤ n*n := Nat.mul_le_mul_left n (by omega)
    nlinarith [Nat.sub_add_cancel hn,hsub]

private def gridIndex {n : ℕ} (hn : 0 < n) (r s : Fin n)
    (h : r.val ≠ n-1 ∨ s.val ≠ n-1) : Fin (n^2-1) := ⟨n*r.val+s.val,grid_lt hn r s h⟩

private lemma gridIndex_row {n : ℕ} (hn : 0 < n) (r s : Fin n)
    (h : r.val ≠ n-1 ∨ s.val ≠ n-1) : (gridIndex hn r s h).val/n = r.val := by
  simp only [gridIndex]
  rw [Nat.mul_add_div hn]
  simp [Nat.div_eq_of_lt s.isLt]

private lemma gridIndex_col {n : ℕ} (hn : 0 < n) (r s : Fin n)
    (h : r.val ≠ n-1 ∨ s.val ≠ n-1) : (gridIndex hn r s h).val%n = s.val := by
  simp [gridIndex,Nat.add_mod,Nat.mod_eq_of_lt s.isLt]

private lemma chart_at_grid {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℂ) (r s : Fin n)
    (h : r.val ≠ n-1 ∨ s.val ≠ n-1) :
    chartPoint A (gridIndex hn r s h) =
      if r.val = s.val then (A r s).re - 1/(n : ℝ)
      else if r.val < s.val then (A r s).re else (A r s).im := by
  simp only [chartPoint,gridIndex_row,gridIndex_col,dif_pos (show r.val < n ∧ s.val < n from ⟨r.isLt,s.isLt⟩)]

private lemma extract_real {n : ℕ} (hn : 0 < n) {A B : Matrix (Fin n) (Fin n) ℂ}
    (hchart : chartPoint A = chartPoint B) (r s : Fin n)
    (h : r.val ≠ n-1 ∨ s.val ≠ n-1) (hrs : r.val ≤ s.val) :
    (A r s).re = (B r s).re := by
  have he := congrFun hchart (gridIndex hn r s h)
  rw [chart_at_grid hn A,chart_at_grid hn B] at he
  by_cases hrc : r.val = s.val
  · simp only [if_pos hrc] at he
    linarith
  · simpa only [if_neg hrc,if_pos (lt_of_le_of_ne hrs hrc)] using he

private lemma extract_imag {n : ℕ} (hn : 0 < n) {A B : Matrix (Fin n) (Fin n) ℂ}
    (hchart : chartPoint A = chartPoint B) (r s : Fin n)
    (h : r.val ≠ n-1 ∨ s.val ≠ n-1) (hrs : s.val < r.val) :
    (A r s).im = (B r s).im := by
  have he := congrFun hchart (gridIndex hn r s h)
  simpa only [chart_at_grid hn A,chart_at_grid hn B,
    if_neg (ne_of_gt hrs),if_neg (not_lt_of_ge hrs.le)] using he

private lemma diagonal_imag_zero {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (r : Fin n) :
    (A r r).im = 0 := by
  have he := congrArg Complex.im (hA.apply r r)
  change -(A r r).im = (A r r).im at he
  linarith

private lemma entry_eq_nonfinal {n : ℕ} (hn : 0 < n) {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hchart : chartPoint A = chartPoint B) (r s : Fin n)
    (h : r.val ≠ n-1 ∨ s.val ≠ n-1) : A r s = B r s := by
  have hs : s.val ≠ n-1 ∨ r.val ≠ n-1 := h.symm
  rcases lt_trichotomy r.val s.val with hrs | hrs | hrs
  · apply Complex.ext
    · exact extract_real hn hchart r s h hrs.le
    · have hi := extract_imag hn hchart s r hs hrs
      have ha := congrArg Complex.im (hA.apply r s)
      have hb := congrArg Complex.im (hB.apply r s)
      change -(A s r).im = (A r s).im at ha
      change -(B s r).im = (B r s).im at hb
      linarith
  · have he : r=s := Fin.ext hrs
    subst s
    apply Complex.ext
    · exact extract_real hn hchart r r h le_rfl
    · rw [diagonal_imag_zero hA,diagonal_imag_zero hB]
  · apply Complex.ext
    · have hi := extract_real hn hchart s r hs hrs.le
      have ha := congrArg Complex.re (hA.apply r s)
      have hb := congrArg Complex.re (hB.apply r s)
      change (A s r).re = (A r s).re at ha
      change (B s r).re = (B r s).re at hb
      exact ha.symm.trans (hi.trans hb)
    · exact extract_imag hn hchart r s h hrs

private lemma chart_injective {n : ℕ} (hn : 0 < n) {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAt : A.trace = 1) (hBt : B.trace = 1)
    (hchart : chartPoint A = chartPoint B) : A = B := by
  classical
  ext r s
  by_cases h : r.val ≠ n-1 ∨ s.val ≠ n-1
  · exact entry_eq_nonfinal hn hA hB hchart r s h
  · have hr : r.val = n-1 := by tauto
    have hs : s.val = n-1 := by tauto
    have hrs : r=s := Fin.ext (hr.trans hs.symm)
    subst s
    apply Complex.ext
    · have hsum : (∑ i, (A i i).re) = ∑ i, (B i i).re := by
        simpa only [Matrix.trace,Matrix.diag,Complex.re_sum] using congrArg Complex.re (hAt.trans hBt.symm)
      have hd : (∑ i, ((A i i).re - (B i i).re)) = 0 := by
        rw [Finset.sum_sub_distrib,hsum,sub_self]
      rw [Finset.sum_eq_single r] at hd
      · linarith
      · intro i _ hir
        have hilast : i.val ≠ n-1 := by intro he; exact hir (Fin.ext (he.trans hr.symm))
        rw [entry_eq_nonfinal hn hA hB hchart i i (Or.inl hilast),sub_self]
      · simp
    · rw [diagonal_imag_zero hA,diagonal_imag_zero hB]

theorem hermitian_trace_one_chart_equiv {n : ℕ} (hn : 0 < n) : ∀ A : Matrix (Fin n) (Fin n) ℂ, A.IsHermitian → A.trace = 1 → rho (chartPoint A) = A := by
  intro A hA ht
  exact chart_injective hn (rho_isHermitian _) hA (rho_trace hn _) ht
    (chart_left_inverse hn _)


open Filter Topology

theorem hermitian_posdef_open (n : ℕ) : IsOpen {A : {A : Matrix (Fin n) (Fin n) ℂ // A.IsHermitian} | A.val.PosDef} := by
  apply isOpen_iff_mem_nhds.mpr
  intro A hA
  have hpos : IsStrictlyPositive A.val := hA.isStrictlyPositive
  have he := (upperHemicontinuous_spectrum ℝ (Matrix (Fin n) (Fin n) ℂ)).forall_isOpen
    A.val (Set.Ioi 0) isOpen_Ioi (by
      intro t ht
      exact hpos.spectrum_pos ht)
  have hes := (continuous_subtype_val.tendsto A).eventually he
  filter_upwards [hes] with B hB
  apply Matrix.IsStrictlyPositive.posDef
  exact (CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos).mpr
    ⟨B.property.isSelfAdjoint,hB⟩

theorem positive_chart_open (n : ℕ) : IsOpen {x : Fin (n^2-1) → ℝ | (rho x).PosDef} := by
  let f : (Fin (n^2-1) → ℝ) → {A : Matrix (Fin n) (Fin n) ℂ // A.IsHermitian} :=
    fun x => ⟨rho x, rho_isHermitian x⟩
  have hf : Continuous f := (rho_continuous n).subtype_mk _
  exact (hermitian_posdef_open n).preimage hf

end D5.S3.Geometry.AlphaGeometry.HermitianDensityCoordinates
