/- GID: D5/S3/Quantum/NormCompression/ThreePointPositivityGate
   generality: G
   mirror-B: none(waiver:finite-gate-only)
   mirror-E: none(waiver:finite-gate-only)
   anchors: []
   utility: none
   digest: Abstract Fin 3 sign-pattern gate for three-point positivity. -/

/-
  A finite-dimensional proof gate extracted from the three-point trace
  positivity argument of arXiv:2610.11021.

  This file deliberately proves only the algebraic 3-by-3 shell.  It does
  not define the trace kernel K_r and does not claim the analytic theorem.
  The missing analytic input is the one-versus-many inequality supplied by
  Carlen--Lieb convexity in the source paper.
-/

import Mathlib.LinearAlgebra.Matrix.PosDef

noncomputable section

namespace D5.S3.Quantum.NormCompression.ThreePointPositivityGate

open scoped BigOperators Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! The one-versus-many estimate used by the source proof, specialized to
    two positive coefficients.  The indices are intentionally unrestricted:
    this makes the gate reusable for any three distinguished entries. -/
def OneVsMany (K : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ (i j k : Fin 3) (u v : ℝ),
    0 ≤ u → 0 ≤ v →
      (u * K i k + v * K j k) ^ 2 ≤
        K k k * (u ^ 2 * K i i + 2 * u * v * K i j + v ^ 2 * K j j)

private lemma mixed_quadratic_nonneg
    (K : Matrix (Fin 3) (Fin 3) ℝ)
    (hnonneg : ∀ i j, 0 ≤ K i j)
    (hone : OneVsMany K)
    {i j k : Fin 3}
    {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    0 ≤ u ^ 2 * K i i + v ^ 2 * K j j + w ^ 2 * K k k
      + 2 * u * v * K i j - 2 * u * w * K i k - 2 * v * w * K j k := by
  let S := u ^ 2 * K i i + v ^ 2 * K j j + 2 * u * v * K i j
  let L := u * K i k + v * K j k
  let c := K k k
  have hS : 0 ≤ S := by
    dsimp [S]
    have hii : 0 ≤ K i i := hnonneg i i
    have hjj : 0 ≤ K j j := hnonneg j j
    have hij' : 0 ≤ K i j := hnonneg i j
    positivity
  have hL : 0 ≤ L := by
    dsimp [L]
    have hik' : 0 ≤ K i k := hnonneg i k
    have hjk' : 0 ≤ K j k := hnonneg j k
    positivity
  have hc : 0 ≤ c := hnonneg k k
  have hCL : L ^ 2 ≤ c * S := by
    convert hone i j k u v hu hv using 1 <;> ring
  have hsq : 0 ≤ (c * w - L) ^ 2 := sq_nonneg _
  have hprod : 0 ≤ c * (S + c * w ^ 2 - 2 * w * L) := by
    nlinarith
  by_cases hcz : c = 0
  · have hLz : L = 0 := by nlinarith
    dsimp [S, L, c] at hprod ⊢
    nlinarith
  · have hcp : 0 < c := lt_of_le_of_ne hc (Ne.symm hcz)
    have hmain : 0 ≤ S + c * w ^ 2 - 2 * w * L := by
      apply nonneg_of_mul_nonneg_left (b := c)
      · simpa [mul_comm] using hprod
      · exact hcp
    dsimp [S, L, c] at hmain ⊢
    nlinarith

/-!
The finite `Fin 3` shell.  Entrywise nonnegativity handles equal-sign
quadrants.  In a mixed quadrant, after a global sign and a permutation, the
quadratic form is exactly `mixed_quadratic_nonneg`.
-/
theorem posSemidef_of_oneVsMany
    (K : Matrix (Fin 3) (Fin 3) ℝ)
    (hHerm : K.IsHermitian)
    (hnonneg : ∀ i j, 0 ≤ K i j)
    (hone : OneVsMany K) :
    K.PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨hHerm, ?_⟩
  intro x
  have hsymm (i j : Fin 3) : K i j = K j i := by
    simpa using (congrFun (congrFun hHerm.eq i) j).symm
  have hexpand : x ⬝ᵥ K *ᵥ x =
      (x 0) ^ 2 * K 0 0 + (x 1) ^ 2 * K 1 1 + (x 2) ^ 2 * K 2 2
        + 2 * (x 0) * (x 1) * K 0 1 + 2 * (x 0) * (x 2) * K 0 2
        + 2 * (x 1) * (x 2) * K 1 2 := by
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
    rw [hsymm 1 0, hsymm 2 0, hsymm 2 1]
    ring
  simp only [star_trivial]
  rw [hexpand]
  have hq (i j k : Fin 3)
      (u v w : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) :
      0 ≤ u ^ 2 * K i i + v ^ 2 * K j j + w ^ 2 * K k k
        + 2 * u * v * K i j - 2 * u * w * K i k - 2 * v * w * K j k :=
    mixed_quadratic_nonneg K hnonneg hone hu hv hw
  have hsame (i j k : Fin 3) (u v w : ℝ)
      (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) :
      0 ≤ u ^ 2 * K i i + v ^ 2 * K j j + w ^ 2 * K k k
        + 2 * u * v * K i j + 2 * u * w * K i k + 2 * v * w * K j k := by
    have hii : 0 ≤ K i i := hnonneg i i
    have hjj : 0 ≤ K j j := hnonneg j j
    have hkk : 0 ≤ K k k := hnonneg k k
    have hij' : 0 ≤ K i j := hnonneg i j
    have hik' : 0 ≤ K i k := hnonneg i k
    have hjk' : 0 ≤ K j k := hnonneg j k
    positivity
  by_cases h0 : 0 ≤ x 0 <;>
    by_cases h1 : 0 ≤ x 1 <;>
    by_cases h2 : 0 ≤ x 2
  all_goals
    try {
      have h := hsame 0 1 2 (x 0) (x 1) (x 2) h0 h1 h2
      nlinarith
    }
  all_goals
    try {
      have h := hsame 0 1 2 (-x 0) (-x 1) (-x 2)
        (by linarith) (by linarith) (by linarith)
      nlinarith
    }
  all_goals
    try {
      have h := hq 0 1 2
        (x 0) (x 1) (-x 2) h0 h1 (by linarith)
      nlinarith
    }
  all_goals
    try {
      have h := hq 0 2 1
        (x 0) (x 2) (-x 1) h0 h2 (by linarith)
      rw [hsymm 2 1] at h
      nlinarith
    }
  all_goals
    try {
      have h := hq 1 2 0
        (x 1) (x 2) (-x 0) h1 h2 (by linarith)
      rw [hsymm 2 0, hsymm 1 0] at h
      nlinarith
    }
  all_goals
    try {
      have h := hq 0 1 2
        (-x 0) (-x 1) (x 2) (by linarith) (by linarith) h2
      nlinarith
    }
  all_goals
    try {
      have h := hq 0 2 1
        (-x 0) (-x 2) (x 1) (by linarith) (by linarith) h1
      rw [hsymm 2 1] at h
      nlinarith
    }
  all_goals
    try {
      have h := hq 1 2 0
        (-x 1) (-x 2) (x 0) (by linarith) (by linarith) h0
      rw [hsymm 2 0, hsymm 1 0] at h
      nlinarith
    }

end D5.S3.Quantum.NormCompression.ThreePointPositivityGate
