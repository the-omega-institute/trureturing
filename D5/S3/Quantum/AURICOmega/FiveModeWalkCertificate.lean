/- GID: D5/S3/Quantum/AURICOmega/FiveModeWalkCertificate
   generality: I
   mirror-B: D5/B/S3/Quantum/AURICOmega/FiveModeWalkCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Orthogonality and uniform first-row support of the five-mode exponential at two thirds. -/

import D5.S3.Quantum.AURICOmega.ExponentialTail
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Notation

noncomputable section
open scoped BigOperators Matrix Matrix.Norms.Operator
open NormedSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace D5.S3.Quantum.AURICOmega.FiveModeWalkCertificate
open D5.S3.Quantum.AURICOmega.ExponentialTail
set_option maxRecDepth 8192

private lemma entry_le_row_norm (M : Matrix (Fin 5) (Fin 5) ℝ) (i j : Fin 5) :
    |M i j| ≤ ‖M‖ := by
  rw [Matrix.linfty_opNorm_def]
  have h₁ : ‖M i j‖₊ ≤ ∑ k : Fin 5, ‖M i k‖₊ :=
    Finset.single_le_sum (f := fun k : Fin 5 => ‖M i k‖₊)
      (fun _ _ => by positivity) (Finset.mem_univ j)
  have h₂ : (∑ k : Fin 5, ‖M i k‖₊) ≤
      Finset.univ.sup (fun l : Fin 5 => ∑ k : Fin 5, ‖M l k‖₊) :=
    Finset.le_sup (f := fun l : Fin 5 => ∑ k : Fin 5, ‖M l k‖₊) (Finset.mem_univ i)
  exact_mod_cast h₁.trans h₂

set_option maxHeartbeats 2000000 in
/-- The fixed generator has the mode order N, 2, 3, 5, 25. All five coordinates
belong to the actual analytic exponential at the nonnegative wait two thirds. -/
theorem actual_walk_certificate :
    let A : Matrix (Fin 5) (Fin 5) ℝ :=
      !![0, 1, 1, 1, 0; -1, 0, 0, 0, -1; -1, 0, 0, 0, 0;
         -1, 0, 0, 0, -1; 0, 1, 0, 1, 0]
    let X := (2 / 3 : ℝ) • A
    let O := exp X
    let S := ∑ k ∈ Finset.range 13, ((k.factorial : ℝ)⁻¹) • X ^ k
    let v := Oᵀ *ᵥ Pi.single (0 : Fin 5) (1 : ℝ)
    Oᵀ * O = 1 ∧ O * Oᵀ = 1 ∧
      ‖O - S‖ ≤ (7 / 6 : ℝ) * 2 ^ 13 / ((13 : ℕ).factorial : ℝ) ∧
      (∀ j : Fin 5, 9 / 25 < |v j|) ∧
      (∀ j : Fin 5, (1 / 8 : ℝ) < (v j) ^ 2) ∧
      (1 / 8 : ℝ) < Finset.univ.inf' Finset.univ_nonempty (fun j : Fin 5 => (v j) ^ 2) ∧
      (∑ j : Fin 5, (v j) ^ 2) = 1 := by
  dsimp only
  let A : Matrix (Fin 5) (Fin 5) ℝ :=
    !![0, 1, 1, 1, 0; -1, 0, 0, 0, -1; -1, 0, 0, 0, 0;
       -1, 0, 0, 0, -1; 0, 1, 0, 1, 0]
  let X := (2 / 3 : ℝ) • A
  let O := exp X
  let S := ∑ k ∈ Finset.range 13, ((k.factorial : ℝ)⁻¹) • X ^ k
  let v := Oᵀ *ᵥ Pi.single (0 : Fin 5) (1 : ℝ)
  change Oᵀ * O = 1 ∧ O * Oᵀ = 1 ∧
    ‖O - S‖ ≤ (7 / 6 : ℝ) * 2 ^ 13 / ((13 : ℕ).factorial : ℝ) ∧
    (∀ j : Fin 5, 9 / 25 < |v j|) ∧
    (∀ j : Fin 5, (1 / 8 : ℝ) < (v j) ^ 2) ∧
    (1 / 8 : ℝ) < Finset.univ.inf' Finset.univ_nonempty (fun j : Fin 5 => (v j) ^ 2) ∧
    (∑ j : Fin 5, (v j) ^ 2) = 1
  have hv (j : Fin 5) : v j = O 0 j := by
    simp [v, Matrix.mulVec_single]
  have hskew : Xᵀ = -X := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [X, A]
  have htrans : Oᵀ = exp (-X) := (Matrix.exp_transpose X).symm.trans (congrArg exp hskew)
  have hleft : Oᵀ * O = 1 := by
    rw [htrans, ← Matrix.exp_add_of_commute (-X) X (Commute.refl X).neg_left]
    simp
  have hright : O * Oᵀ = 1 := by
    rw [htrans, ← Matrix.exp_add_of_commute X (-X) (Commute.refl X).neg_right]
    simp
  have hnorm : ‖X‖ ≤ 2 := by
    rw [Matrix.linfty_opNorm_def]
    change ((Finset.univ.sup (fun i : Fin 5 => ∑ j : Fin 5, ‖X i j‖₊) : NNReal) : ℝ) ≤
      ((2 : NNReal) : ℝ)
    norm_cast
    apply Finset.sup_le
    intro i hi
    have hrow : (∑ j : Fin 5, ‖X i j‖) ≤ 2 := by
      fin_cases i <;> norm_num [X, A, Fin.sum_univ_succ, Real.norm_eq_abs]
    exact_mod_cast hrow
  have htail : ‖O - S‖ ≤ (7 / 6 : ℝ) * 2 ^ 13 / ((13 : ℕ).factorial : ℝ) := by
    have ht := exp_remainder_le X 2 13 (by norm_num) hnorm (by norm_num)
    change ‖exp X - ∑ k ∈ Finset.range 13, ((k.factorial : ℝ)⁻¹) • X ^ k‖ ≤ _
    convert ht using 1; norm_num

  let rows : Fin 13 → Fin 5 → ℝ := fun k =>
    match k.val with
    | 0 => ![1,0,0,0,0]
    | 1 => ![0,1,1,1,0]
    | 2 => ![-3,0,0,0,-2]
    | 3 => ![0,-5,-3,-5,0]
    | 4 => ![13,0,0,0,10]
    | 5 => ![0,23,13,23,0]
    | 6 => ![-59,0,0,0,-46]
    | 7 => ![0,-105,-59,-105,0]
    | 8 => ![269,0,0,0,210]
    | 9 => ![0,479,269,479,0]
    | 10 => ![-1227,0,0,0,-958]
    | 11 => ![0,-2185,-1227,-2185,0]
    | 12 => ![5597,0,0,0,4370]
    | _ => 0
  have hstep (k : Fin 12) (j : Fin 5) :
      ∑ i : Fin 5, rows k.castSucc i * A i j = rows k.succ j := by
    fin_cases k <;> fin_cases j <;> norm_num [rows, A, Fin.sum_univ_succ, Fin.castSucc, Fin.succ]
  have hpower (n : ℕ) (hn : n < 13) (j : Fin 5) :
      (A ^ n) 0 j = rows ⟨n, hn⟩ j := by
    induction n generalizing j with
    | zero =>
      fin_cases j <;> norm_num [rows, Matrix.one_apply]
    | succ n ih =>
      rw [pow_succ, Matrix.mul_apply]
      have hcast : (⟨n, by omega⟩ : Fin 13) = (⟨n, by omega⟩ : Fin 12).castSucc := rfl
      simp_rw [ih (by omega), hcast]
      exact hstep ⟨n, by omega⟩ j
  have hXpower (k : ℕ) (hk : k < 13) (j : Fin 5) :
      (X ^ k) 0 j = (2 / 3 : ℝ) ^ k * rows ⟨k, hk⟩ j := by
    change (((2 / 3 : ℝ) • A) ^ k) 0 j = _
    rw [smul_pow, Matrix.smul_apply, smul_eq_mul, hpower k hk]
  let certifiedRow : Fin 5 → ℝ :=
    ![107738440637/248594813775, 490347766/1104865839, 4899328858/9207215325,
      490347766/1104865839, -91371050044/248594813775]
  have hS (j : Fin 5) : S 0 j = certifiedRow j := by
    have hsum : S 0 j = ∑ k : Fin 13,
        ((k.val.factorial : ℝ)⁻¹) * (2 / 3 : ℝ) ^ k.val * rows k j := by
      simp only [S, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      rw [← Fin.sum_univ_eq_sum_range]
      congr 1
      ext k
      rw [hXpower k.val k.isLt j]
      ring
    rw [hsum]
    fin_cases j <;> norm_num [certifiedRow, rows, Fin.sum_univ_succ, Nat.factorial]
  have hcertificate (j : Fin 5) : (367 / 1000 : ℝ) < |S 0 j| := by
    rw [hS]
    fin_cases j <;> norm_num [certifiedRow]
  have hcoordinate (j : Fin 5) : (9 / 25 : ℝ) < |O 0 j| := by
    have herr : |O 0 j - S 0 j| ≤ (7 / 6 : ℝ) * 2 ^ 13 / ((13 : ℕ).factorial : ℝ) :=
      (entry_le_row_norm (O - S) 0 j).trans htail
    have htri : |S 0 j| ≤ |O 0 j| + |O 0 j - S 0 j| := by
      calc
        |S 0 j| = |O 0 j - (O 0 j - S 0 j)| := by congr 1; ring
        _ ≤ _ := abs_sub _ _
    have hc := hcertificate j
    norm_num [Nat.factorial] at herr
    linarith
  have hsquare (j : Fin 5) : (1 / 8 : ℝ) < (O 0 j) ^ 2 := by
    have hc := hcoordinate j
    have ha := abs_nonneg (O 0 j)
    nlinarith [sq_abs (O 0 j)]
  have hunit : (∑ j : Fin 5, (O 0 j) ^ 2) = 1 := by
    have hh := congrArg (fun M : Matrix (Fin 5) (Fin 5) ℝ => M 0 0) hright
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, if_true, pow_two] using hh
  refine ⟨hleft, hright, htail, ?_, ?_, ?_, ?_⟩
  · simpa only [hv] using hcoordinate
  · simpa only [hv] using hsquare
  · apply (Finset.lt_inf'_iff Finset.univ_nonempty).mpr
    intro j hj
    simpa only [hv] using hsquare j
  · simpa only [hv] using hunit

end D5.S3.Quantum.AURICOmega.FiveModeWalkCertificate
