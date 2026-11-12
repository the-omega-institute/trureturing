/- GID: D5/S3/Quantum/Divergence/MaximalHockeyStickCornerOptimization
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/MaximalHockeyStickCornerOptimization
   mirror-E: none(waiver:finite-spectral-proof)
   anchors: []
   utility: none
   digest: Common-corner reduction of actual weighted positive overlap optimization. -/


import D5.S3.Quantum.Divergence.MaximalHockeyStickCorner
import D5.S3.Quantum.Divergence.MaximalHockeyStickCornerWeight
import D5.S3.Quantum.Divergence.MaximalHockeyStickThreshold

/-! Restriction to the common support preserves the entire overlap optimization. -/


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Divergence.MaximalHockeyStickOverlap
open D5.S3.Quantum.Divergence.MaximalHockeyStickCorner
open D5.S3.Quantum.Divergence.MaximalHockeyStickCornerWeight
open D5.S3.Quantum.Divergence.MaximalHockeyStickThreshold
open D5.S3.Quantum.Divergence.MaximalHockeyStickSpectral

namespace D5.S3.Quantum.Divergence.MaximalHockeyStickCornerOptimization

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem extend_compress (p : n → Prop) [DecidablePred p]
    (X : Matrix n n ℂ)
    (hl : diagonal (fun i => if p i then (1 : ℂ) else 0) * X = X)
    (hr : X * diagonal (fun i => if p i then (1 : ℂ) else 0) = X) :
    inclusion p * (X.submatrix (fun i : {i // p i} => i.val) (fun i : {i // p i} => i.val)) * (inclusion p)ᴴ = X := by
  rw [← inclusion_compress]
  calc
    _ = (inclusion p * (inclusion p)ᴴ) * X * (inclusion p * (inclusion p)ᴴ) := by
      simp only [Matrix.mul_assoc]
    _ = X := by rw [inclusion_projection, hl, hr]

private theorem extend_compress_le_diagonal (p : n → Prop) [DecidablePred p]
    (d : n → ℝ) (hd : ∀ i, 0 ≤ d i) :
    inclusion p * ((diagonal (fun i => (d i : ℂ))).submatrix (fun i : {i // p i} => i.val) (fun i : {i // p i} => i.val)) *
      (inclusion p)ᴴ ≤ diagonal (fun i => (d i : ℂ)) := by
  apply Matrix.le_iff.mpr
  have he : diagonal (fun i => (d i : ℂ)) -
      inclusion p * ((diagonal (fun i => (d i : ℂ))).submatrix (fun i : {i // p i} => i.val) (fun i : {i // p i} => i.val)) *
        (inclusion p)ᴴ = diagonal (fun i => if p i then 0 else (d i : ℂ)) := by
    rw [← inclusion_compress]
    calc
      _ = diagonal (fun i => (d i : ℂ)) -
          (inclusion p * (inclusion p)ᴴ) * diagonal (fun i => (d i : ℂ)) *
            (inclusion p * (inclusion p)ᴴ) := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [inclusion_projection, Matrix.diagonal_mul_diagonal,
          Matrix.diagonal_mul_diagonal, Matrix.diagonal_sub]
        congr 1
        funext i
        split_ifs <;> simp
  rw [he]
  exact Matrix.PosSemidef.diagonal (fun i => by split_ifs <;> simp [hd i])

private theorem trace_extension (p : n → Prop) [DecidablePred p]
    (W : Matrix n n ℂ) (X : Matrix {i // p i} {i // p i} ℂ) :
    (W * (inclusion p * X * (inclusion p)ᴴ)).trace =
      ((W.submatrix (fun i : {i // p i} => i.val) (fun i : {i // p i} => i.val)) * X).trace := by
  rw [← inclusion_compress]
  calc
    _ = ((inclusion p)ᴴ * W * inclusion p * X).trace := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
      simp only [Matrix.mul_assoc]
    _ = _ := rfl

theorem diagonal_feasible (d : n → ℝ) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1)
    (t : ℝ) (ht : 0 ≤ t) :
    diagonal (fun i => ((min (d i) (t * (1 - d i)) : ℝ) : ℂ)) ∈
      positiveOverlaps (diagonal (fun i => (d i : ℂ)))
        (t • (1 - diagonal (fun i => (d i : ℂ)))) := by
  refine ⟨(Matrix.PosSemidef.diagonal (fun i => by
    change (0 : ℂ) ≤ _
    exact_mod_cast le_min (hd i).1 (mul_nonneg ht (sub_nonneg.mpr (hd i).2)))).nonneg,
    Matrix.le_iff.mpr ?_, Matrix.le_iff.mpr ?_⟩
  · rw [Matrix.diagonal_sub]
    exact Matrix.PosSemidef.diagonal (fun i => by
      change (0 : ℂ) ≤ _
      exact_mod_cast sub_nonneg.mpr (min_le_left (d i) (t * (1 - d i))))
  · have he : t • (1 - diagonal (fun i => (d i : ℂ))) =
        diagonal (fun i => ((t * (1 - d i) : ℝ) : ℂ)) := by
      rw [← Matrix.diagonal_one, Matrix.diagonal_sub, ← Matrix.diagonal_smul]
      apply congrArg (fun f : n → ℂ => diagonal f)
      funext i
      simp [Complex.real_smul]
    rw [he, Matrix.diagonal_sub]
    exact Matrix.PosSemidef.diagonal (fun i => by
      change (0 : ℂ) ≤ _
      exact_mod_cast sub_nonneg.mpr (min_le_right (d i) (t * (1 - d i))))

theorem diagonal_optimization_reduction (d : n → ℝ)
    (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1) (W : Matrix n n ℂ) (t : ℝ) (ht : 0 ≤ t) :
    let p := fun i => 0 < d i ∧ d i < 1
    let D := diagonal (fun i => (d i : ℂ))
    let Y := diagonal (fun i => ((min (d i) (t * (1 - d i)) : ℝ) : ℂ))
    (∀ X ∈ positiveOverlaps D (t • (1 - D)), (W * X).trace.re ≤ (W * Y).trace.re) ↔
      (∀ X ∈ positiveOverlaps (D.submatrix (fun i : {i // p i} => i.val) (fun i : {i // p i} => i.val))
          (t • (1 - D.submatrix (fun i : {i // p i} => i.val) (fun i : {i // p i} => i.val))),
        ((W.submatrix (fun i : {i // p i} => i.val) (fun i : {i // p i} => i.val)) * X).trace.re ≤
          ((W.submatrix (fun i : {i // p i} => i.val) (fun i : {i // p i} => i.val)) *
            (Y.submatrix (fun i : {i // p i} => i.val) (fun i : {i // p i} => i.val))).trace.re) := by
  classical
  dsimp only
  let p := fun i => 0 < d i ∧ d i < 1
  let D := diagonal (fun i => (d i : ℂ))
  let Y := diagonal (fun i => ((min (d i) (t * (1 - d i)) : ℝ) : ℂ))
  let J := inclusion p
  have hY := diagonal_feasible d hd t ht
  obtain ⟨hPY, hYP⟩ := diagonal_corner_support d hd t Y hY.1 hY.2.1 hY.2.2
  have hrecY := extend_compress p Y hPY hYP
  have htrY : (W * Y).trace =
      ((W.submatrix (fun i : {i // p i} => i.val) (fun i : {i // p i} => i.val)) *
        (Y.submatrix (fun i : {i // p i} => i.val) (fun i : {i // p i} => i.val))).trace := by
    calc
      _ = (W * (inclusion p * (Y.submatrix (fun i : {i // p i} => i.val)
          (fun i : {i // p i} => i.val)) * (inclusion p)ᴴ)).trace :=
        congrArg (fun M : Matrix n n ℂ => (W * M).trace) hrecY.symm
      _ = _ := trace_extension p W _
  have hB : (t • (1 - D)).submatrix (fun i : {i // p i} => i.val) (fun i : {i // p i} => i.val) =
      t • (1 - D.submatrix (fun i : {i // p i} => i.val) (fun i : {i // p i} => i.val)) := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.smul_apply, Matrix.sub_apply,
      Matrix.one_apply, Subtype.ext_iff]
  constructor
  · intro h X hX
    have hDX : J * X * Jᴴ ≤ D := by
      exact (extend_le p hX.2.1).trans (extend_compress_le_diagonal p d (fun i => (hd i).1))
    have hBX : J * X * Jᴴ ≤ t • (1 - D) := by
      have hb' : X ≤ (t • (1 - D)).submatrix (fun i : {i // p i} => i.val) (fun i : {i // p i} => i.val) := by
        rw [hB]
        exact hX.2.2
      have hh := extend_le p hb'
      have hdB (i : n) : 0 ≤ t * (1 - d i) := mul_nonneg ht (sub_nonneg.mpr (hd i).2)
      have he : t • (1 - D) = diagonal (fun i => ((t * (1 - d i) : ℝ) : ℂ)) := by
        ext i j
        by_cases hij : i = j
        · subst j; simp [D, Complex.real_smul]
        · simp [D, Matrix.diagonal, Matrix.one_apply, hij]
      apply hh.trans
      rw [he]
      exact extend_compress_le_diagonal p (fun i => t * (1 - d i)) hdB
    have hh := h (J * X * Jᴴ) ⟨(hX.1.posSemidef.mul_mul_conjTranspose_same J).nonneg, hDX, hBX⟩
    rw [htrY, trace_extension p W X] at hh
    exact hh
  · intro h X hX
    obtain ⟨hl, hr⟩ := diagonal_corner_support d hd t X hX.1 hX.2.1 hX.2.2
    have hrecX := extend_compress p X hl hr
    have hxB := compress_le p hX.2.2
    rw [hB] at hxB
    have hh := h (X.submatrix (fun i : {i // p i} => i.val) (fun i : {i // p i} => i.val))
      ⟨(hX.1.posSemidef.submatrix _).nonneg, compress_le p hX.2.1, hxB⟩
    have htrX : (W * X).trace =
        ((W.submatrix (fun i : {i // p i} => i.val) (fun i : {i // p i} => i.val)) *
          (X.submatrix (fun i : {i // p i} => i.val) (fun i : {i // p i} => i.val))).trace := by
      calc
        _ = (W * (inclusion p * (X.submatrix (fun i : {i // p i} => i.val)
            (fun i : {i // p i} => i.val)) * (inclusion p)ᴴ)).trace :=
          congrArg (fun M : Matrix n n ℂ => (W * M).trace) hrecX.symm
        _ = _ := trace_extension p W _
    change (W * X).trace.re ≤ (W * Y).trace.re
    rw [htrX, htrY]
    exact hh

end D5.S3.Quantum.Divergence.MaximalHockeyStickCornerOptimization
