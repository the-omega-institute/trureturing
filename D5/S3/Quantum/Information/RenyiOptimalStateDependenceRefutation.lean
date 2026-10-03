/- GID: D5/S3/Quantum/Information/RenyiOptimalStateDependenceRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/RenyiOptimalStateDependenceRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/RenyiOptimalStateDependenceRefutation.claim; result=D5/S3/Quantum/Information/RenyiOptimalStateDependenceRefutation.result; claim=D5/S3/Quantum/Information/RenyiOptimalStateDependenceRefutation.claim
   digest: A qutrit basis state is Pareto optimal for (1,1), but not for (3/5,3). -/

/-
proof_shape: result: bind-only (frozen Shannon endpoint, upstream PSD zero-form
  characterization, exact finite matrix arithmetic and logarithm comparisons)
escape_witness: none
admission_basis: open-problem-resolution (#11782; Refuted)
Direct frozen dependencies:
  D5/S3/Quantum/Foundation/FiniteStateChannel.DensityState
  D5/S3/Entropy/MaxEntropy.shannonEntropy
  D5/S3/Entropy/EntropyEquality.entropy_eq_zero_iff_point_mass
  D5/S3/Quantum/Information/OrthogonalRecordEntropy.pointerState
Information-escape registration is paused under CLAUDE.md §3.9 「信息逃逸登记暂缓」.
-/

import D5.S3.Quantum.Foundation.FiniteStateChannel
import D5.S3.Entropy.EntropyEquality
import D5.S3.Quantum.Information.OrthogonalRecordEntropy

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Information.OrthogonalRecordEntropy (pointerState)
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Entropy.MaxEntropy D5.S3.Entropy.EntropyEquality

namespace D5.S3.Quantum.Information.RenyiOptimalStateDependenceRefutation

/-!
The independence conjecture in section V.E of Abdelkhalek et al., arXiv:1509.00398v1,
asserts that Pareto optimal states are independent of the finite dual Renyi orders.
A real orthogonal qutrit overlap matrix reverses the entropy ordering of two basis
projectors between orders one and three. The optimality quantifier ranges over all
complex density states, including mixed states. Logarithms are natural throughout.
-/

def pX {d : ℕ} (ρ : DensityState (Fin d)) (i : Fin d) : ℝ := ((CStarMatrix.ofMatrix.symm ρ.val) i i).re

def pY {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (ρ : DensityState (Fin d)) (j : Fin d) : ℝ :=
  (((U : Matrix (Fin d) (Fin d) ℂ)ᴴ * (CStarMatrix.ofMatrix.symm ρ.val) * (U : Matrix (Fin d) (Fin d) ℂ)) j j).re

def H {d : ℕ} (α : ℝ) (p : Fin d → ℝ) : ℝ :=
  if α = 1 then shannonEntropy p
  else Real.log (∑ i, if p i = 0 then 0 else (p i) ^ α) / (1 - α)

def Below {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (α β : ℝ)
    (ρ σ : DensityState (Fin d)) : Prop := H α (pX ρ) ≤ H α (pX σ) ∧ H β (pY U ρ) ≤ H β (pY U σ)

def Optimal {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (α β : ℝ) (ρ : DensityState (Fin d)) : Prop :=
  ∀ σ : DensityState (Fin d), Below U α β σ ρ → Below U α β ρ σ

def claim : Prop :=
  ∀ d (U : Matrix.unitaryGroup (Fin d) ℂ) (α β α' β' : ℝ),
    1/2 < α → 1/2 < β → 1/2 < α' → 1/2 < β' →
    1/α + 1/β = 2 → 1/α' + 1/β' = 2 →
    ∀ ρ : DensityState (Fin d), Optimal U α β ρ → Optimal U α' β' ρ

private def W : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.sqrt 2 / 2, Real.sqrt 2 / 2, 0;
     Real.sqrt 2 / 4, -Real.sqrt 2 / 4, Real.sqrt 3 / 2;
     Real.sqrt 2 * Real.sqrt 3 / 4, -Real.sqrt 2 * Real.sqrt 3 / 4, -(1/2)]

private def UM : Matrix (Fin 3) (Fin 3) ℂ := W.map Complex.ofReal

private def witnessU : Matrix.unitaryGroup (Fin 3) ℂ := by
  have W_orthogonal : W * Wᵀ = 1 := by
    have hs : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    have ht : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [W, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ,
        Matrix.one_apply] <;> ring_nf <;> simp [hs, ht] <;> norm_num <;> ring
  refine ⟨UM, Matrix.mem_unitaryGroup_iff.mpr ?_⟩
  change UM * UMᴴ = 1
  ext i j
  have hh := congrArg Complex.ofReal (congrFun (congrFun W_orthogonal i) j)
  simpa [UM, Matrix.mul_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, Matrix.map_apply, apply_ite Complex.ofReal] using hh

private def rowLaw (k : Fin 3) : Fin 3 → ℝ :=
  ![ ![(1/2 : ℝ), 1/2, 0], ![(1/8 : ℝ), 1/8, 3/4], ![(3/8 : ℝ), 3/8, 1/4]] k

/-- The optimal-state independence conjecture fails for two finite dual pairs. -/
theorem result : ¬ claim := by
  classical
  have psd {d : ℕ} (ρ : DensityState (Fin d)) : ((CStarMatrix.ofMatrix.symm ρ.val)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm ρ.2.1)
  have pX_law {d : ℕ} (ρ : DensityState (Fin d)) :
      (∀ i, 0 ≤ pX ρ i) ∧ ∑ i, pX ρ i = 1 := by
    constructor
    · intro i
      exact (Complex.nonneg_iff.mp (psd ρ).diag_nonneg).1
    · change (∑ i, ((CStarMatrix.ofMatrix.symm ρ.val) i i).re) = 1
      rw [← Complex.re_sum]
      change (Matrix.trace ρ.val).re = 1
      rw [ρ.2.2]
      rfl
  have pX_entropy_nonneg {d : ℕ} (ρ : DensityState (Fin d)) : 0 ≤ H 1 (pX ρ) := by
    rw [H, if_pos rfl, shannonEntropy]
    apply Finset.sum_nonneg
    intro i _
    have hp := pX_law ρ
    apply Real.negMulLog_nonneg (hp.1 i)
    calc pX ρ i ≤ ∑ j, pX ρ j := Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)
         _ = 1 := hp.2

  -- The frozen pointer states are basis projectors in arbitrary dimension.
  have pX_basis {d : ℕ} (k : Fin d) :
      pX (pointerState k) = fun i => if i = k then 1 else 0 := by
    classical
    funext i
    by_cases hi : i = k <;> simp [pX, pointerState, hi]
  have H_basis {d : ℕ} (α : ℝ) (k : Fin d) : H α (pX (pointerState k)) = 0 := by
    classical
    rw [pX_basis]
    by_cases ha : α = 1
    · simp only [H, ha, shannonEntropy]
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : i = k <;> simp [hi]
    · simp [H, ha]
  have point_diagonal_matrix {d : ℕ} (ρ : DensityState (Fin d)) (k : Fin d)
      (hk : pX ρ k = 1) : ρ = pointerState k := by
    classical
    have h : pX ρ = fun i => if i = k then 1 else 0 := by
      funext i
      by_cases hik : i = k
      · simp [hik, hk]
      · have hp := pX_law ρ
        have hsum := Finset.sum_erase_add Finset.univ (pX ρ) (Finset.mem_univ k)
        have hrest : ∑ j ∈ Finset.univ.erase k, pX ρ j = 0 := by
          rw [hp.2, hk] at hsum
          linarith
        have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hp.1 j)).mp hrest
        have hi := hz i (Finset.mem_erase.mpr ⟨hik, Finset.mem_univ i⟩)
        simp [hik, hi]
    have hdiag (i : Fin d) : (CStarMatrix.ofMatrix.symm ρ.val) i i = if i = k then 1 else 0 := by
      have hh := congrFun (psd ρ).isHermitian.coe_re_diag i
      calc
        (CStarMatrix.ofMatrix.symm ρ.val) i i = ((pX ρ i : ℝ) : ℂ) := hh.symm
        _ = _ := by rw [h]; by_cases hi : i = k <;> simp [hi]
    have hcol (j : Fin d) (hj : j ≠ k) (i : Fin d) : (CStarMatrix.ofMatrix.symm ρ.val) i j = 0 := by
      let x : Fin d → ℂ := Pi.single j 1
      have hx : star x ⬝ᵥ ((CStarMatrix.ofMatrix.symm ρ.val) *ᵥ x) = 0 := by
        have hd := hdiag j
        change ρ.val j j = if j = k then 1 else 0 at hd
        simp [x, dotProduct, Matrix.mulVec, Pi.single_apply, hd, hj]
      have hz := ((psd ρ).dotProduct_mulVec_zero_iff x).mp hx
      have hi := congrFun hz i
      simpa [x, Matrix.mulVec, dotProduct, Pi.single_apply] using hi
    apply Subtype.ext
    change (CStarMatrix.ofMatrix.symm ρ.val) = (CStarMatrix.ofMatrix.symm (pointerState k).val)
    ext i j
    change (CStarMatrix.ofMatrix.symm ρ.val) i j = (Matrix.diagonal (fun a : Fin d => if a = k then (1 : ℂ) else 0)) i j
    by_cases hij : i = j
    · subst j
      simp [hdiag]
    · simp only [Matrix.diagonal_apply, hij, if_false]
      by_cases hj : j = k
      · have hi : i ≠ k := by simpa [hj] using hij
        have hh := congrFun (congrFun (psd ρ).isHermitian j) i
        have hc := hcol i hi j
        have hz : star ((CStarMatrix.ofMatrix.symm ρ.val) i j) = 0 := by simpa [Matrix.conjTranspose_apply, hc] using hh
        exact star_eq_zero.mp hz
      · exact hcol j hj i
  have pY_basis {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (k : Fin d) (j : Fin d) :
      pY U (pointerState k) j = Complex.normSq ((U : Matrix (Fin d) (Fin d) ℂ) k j) := by
    classical
    simp [pY, pointerState, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.diagonal_apply, Complex.normSq_apply]
  have witness_rows (k : Fin 3) : pY witnessU (pointerState k) = rowLaw k := by
    have hs : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    have ht : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
    funext j
    rw [pY_basis]
    fin_cases k <;> fin_cases j <;>
      norm_num [witnessU, UM, W, rowLaw, Matrix.map_apply, Complex.normSq_apply] <;>
      ring_nf <;> simp [hs, ht] <;> norm_num
  have log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have shannon_rows :
      H 1 (rowLaw 0) = Real.log 2 ∧
      H 1 (rowLaw 1) = (9/4 : ℝ) * Real.log 2 - (3/4 : ℝ) * Real.log 3 ∧
      H 1 (rowLaw 2) = (11/4 : ℝ) * Real.log 2 - (3/4 : ℝ) * Real.log 3 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      convert Real.log_pow 2 2 using 1 <;> norm_num
    have h8 : Real.log 8 = 3 * Real.log 2 := by
      convert Real.log_pow 2 3 using 1 <;> norm_num
    repeat' apply And.intro
    all_goals
      norm_num [H, shannonEntropy, rowLaw, Matrix.cons_val_two, Fin.sum_univ_succ, Real.negMulLog,
        Real.log_div, h4, h8]
      ring
  have shannon_row1_gt : Real.log 2 < H 1 (rowLaw 1) := by
    have hb : 3 * Real.log 3 < 5 * Real.log 2 := by
      have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 3^3)
        (by norm_num : (3 : ℝ)^3 < 2^5)
      rw [Real.log_pow, Real.log_pow] at h
      norm_num only [Nat.cast_ofNat] at h
      exact h
    rw [shannon_rows.2.1]
    linarith
  have shannon_row2_gt : Real.log 2 < H 1 (rowLaw 2) := by
    rw [shannon_rows.2.2]
    have h := shannon_row1_gt
    rw [shannon_rows.2.1] at h
    linarith [log_two_pos]
  have renyi3_rows :
      H 3 (rowLaw 0) = Real.log 2 ∧
      H 3 (rowLaw 1) = -(1/2 : ℝ) * Real.log (109/256 : ℝ) := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by convert Real.log_pow 2 2 using 1 <;> norm_num
    constructor
    · norm_num [H, rowLaw, Matrix.cons_val_two, Fin.sum_univ_succ, Real.rpow_natCast,
        Real.log_div, h4]
    · norm_num [H, rowLaw, Matrix.cons_val_two, Fin.sum_univ_succ, Real.rpow_natCast]
      ring
  have renyi3_row1_lt : H 3 (rowLaw 1) < Real.log 2 := by
    have hb : Real.log (1/4 : ℝ) < Real.log (109/256 : ℝ) :=
      Real.log_lt_log (by norm_num) (by norm_num)
    have h4 : Real.log 4 = 2 * Real.log 2 := by convert Real.log_pow 2 2 using 1 <;> norm_num
    norm_num [Real.log_div, h4] at hb
    rw [renyi3_rows.2]
    norm_num [Real.log_div] at *
    linarith
  have optimal_shannon : Optimal witnessU 1 1 (pointerState 0) := by
    intro σ hσ
    have hx : H 1 (pX σ) = 0 := by
      have hh := hσ.1
      rw [H_basis] at hh
      exact le_antisymm hh (pX_entropy_nonneg σ)
    have hmass : shannonEntropy (pX σ) = 0 := by simpa [H] using hx
    obtain ⟨k, hk⟩ := (entropy_eq_zero_iff_point_mass (pX σ) (pX_law σ)).mp hmass
    have hs : σ = pointerState k := point_diagonal_matrix σ k (by
      have hi := congrFun hk k
      simpa using hi)
    subst σ
    have hy := hσ.2
    rw [witness_rows, witness_rows, shannon_rows.1] at hy
    have hk0 : k = 0 := by
      fin_cases k
      · rfl
      · exact (not_le_of_gt shannon_row1_gt hy).elim
      · exact (not_le_of_gt shannon_row2_gt hy).elim
    subst k
    exact ⟨le_rfl, le_rfl⟩
  have not_optimal_renyi : ¬ Optimal witnessU (3/5) 3 (pointerState 0) := by
    intro ho
    have hb : Below witnessU (3/5) 3 (pointerState 1) (pointerState 0) := by
      constructor
      · simp only [H_basis]; exact le_rfl
      · rw [witness_rows, witness_rows, renyi3_rows.1]
        exact renyi3_row1_lt.le
    have h := (ho (pointerState 1) hb).2
    rw [witness_rows, witness_rows, renyi3_rows.1] at h
    exact not_le_of_gt renyi3_row1_lt h
  intro hc
  have ho := hc 3 witnessU 1 1 (3/5) 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (pointerState 0) optimal_shannon
  exact not_optimal_renyi ho


end D5.S3.Quantum.Information.RenyiOptimalStateDependenceRefutation
