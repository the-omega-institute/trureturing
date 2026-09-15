/- GID: D5/S3/Observer/Monodromy/TransvectionTraceReconstruction
   generality: G
   mirror-B: D5/B/S3/Observer/Monodromy/TransvectionTraceReconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A bidirected star recovers a zero-diagonal rank-one tuple from anchored traces. -/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.Tactic

/-!
# Rational reconstruction of a transvection frame

For a zero-diagonal matrix H, the i-th increment N_i has i-th row H_i
and all other rows zero. These are actual matrices: N_i^2 = 0, so I+N_i
is invertible. When H is a Gram matrix in a spanning frame this is the
coefficient-space realization of the corresponding rank-one operators.

With an anchor a satisfying H[a,j] H[j,a] != 0 for j != a, put
p_j = tr(N_a N_j), t_ij = tr(N_a N_i N_j). A single explicit diagonal
change of basis simultaneously changes the increments to row matrices
with entries 1 in row a, p_i in column a, and t_ij/p_j elsewhere.
No square roots or pre-supplied conjugating matrix are assumed.

Literature: Eberhard, arXiv:2308.07086v3, Section 3 supplies the classical
cycle-weight language. This module develops an explicit star normal form,
not a proof of the geometric Sp8 expectation in arXiv:2604.20970, Section 1.1.
- The latter requires an actual geometric rank-eight lift and density.
- Matrix coordinates here may have a radical; irreducibility is not assumed.
- No new result about all transvection-generated groups is claimed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Monodromy.TransvectionTraceReconstruction

variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

/-- The actual rank-at-most-one increment supported on row i. -/
def increment (H : Matrix I I K) (i : I) : Matrix I I K :=
  fun r c => if r = i then H i c else 0

private theorem increment_mul_entry (H : Matrix I I K) (i j r c : I) :
    (increment H i * increment H j) r c =
      if r = i then H i j * H j c else 0 := by
  classical
  by_cases hr : r = i
  · subst r
    simp [Matrix.mul_apply, increment]
  · simp [Matrix.mul_apply, increment, hr]

private theorem increment_mul_mul_entry (H : Matrix I I K) (i j k r c : I) :
    (increment H i * increment H j * increment H k) r c =
      if r = i then H i j * H j k * H k c else 0 := by
  classical
  by_cases hr : r = i
  · subst r
    simp [Matrix.mul_apply, increment_mul_entry, increment, mul_assoc]
  · simp [Matrix.mul_apply, increment_mul_entry, increment, hr]

/-- Cycle traces are calculated from the actual matrix products. -/
theorem trace_pair (H : Matrix I I K) (i j : I) :
    Matrix.trace (increment H i * increment H j) = H i j * H j i := by
  classical
  simp [Matrix.trace, increment_mul_entry]

/-- The anchored triangle is an oriented observable, not a squared pairing. -/
theorem trace_triple (H : Matrix I I K) (i j k : I) :
    Matrix.trace (increment H i * increment H j * increment H k) =
      H i j * H j k * H k i := by
  classical
  simp [Matrix.trace, increment_mul_mul_entry]

theorem increment_sq_zero (H : Matrix I I K)
    (hdiag : ∀ i, H i i = 0) (i : I) :
    increment H i * increment H i = 0 := by
  ext r c
  simp [increment_mul_entry, hdiag]

/-- Both inverse identities are derived, rather than stored as fields. -/
theorem transvection_inverse (H : Matrix I I K)
    (hdiag : ∀ i, H i i = 0) (i : I) :
    (1 + increment H i) * (1 - increment H i) = 1 ∧
      (1 - increment H i) * (1 + increment H i) = 1 := by
  have hs := increment_sq_zero H hdiag i
  constructor <;>
    simp [mul_add, add_mul, mul_sub, sub_mul, hs]

/-- Products of anchored increments, read using the standard matrix trace. -/
def pairRead (H : Matrix I I K) (a j : I) : K :=
  Matrix.trace (increment H a * increment H j)

def tripleRead (H : Matrix I I K) (a i j : I) : K :=
  Matrix.trace (increment H a * increment H i * increment H j)

/-- The nonzero diagonal normalizer is constructed directly from the frame. -/
def anchorScale (H : Matrix I I K) (a j : I) : K :=
  if j = a then 1 else H a j

/-- Entrywise description of conjugation by an invertible diagonal matrix. -/
def gauge (d : I → K) (M : Matrix I I K) : Matrix I I K :=
  fun i j => d i * M i j / d j

/-- A reconstruction depending only on anchored pair and triangle observations. -/
def recoveredGram (a : I) (p : I → K) (t : I → I → K) : Matrix I I K :=
  fun i j => if i = a then (if j = a then 0 else 1)
    else if j = a then p i else t i j / p j

private theorem anchorScale_ne_zero (H : Matrix I I K) (a : I)
    (hstar : ∀ j, j ≠ a → H a j ≠ 0 ∧ H j a ≠ 0) (j : I) :
    anchorScale H a j ≠ 0 := by
  by_cases hj : j = a
  · simp [anchorScale, hj]
  · simpa [anchorScale, hj] using (hstar j hj).1

/-- Central reconstruction identity. The conclusion contains no unobserved entry
of H except in the explicitly exhibited diagonal coordinate change. -/
theorem recoveredGram_eq_gauge (H : Matrix I I K) (a : I)
    (hdiag : ∀ i, H i i = 0)
    (hstar : ∀ j, j ≠ a → H a j ≠ 0 ∧ H j a ≠ 0) :
    recoveredGram a (pairRead H a) (tripleRead H a) =
      gauge (anchorScale H a) H := by
  ext i j
  by_cases hi : i = a
  · subst i
    by_cases hj : j = a
    · subst j
      simp [recoveredGram, gauge, anchorScale, hdiag]
    · simp [recoveredGram, gauge, anchorScale, hj, (hstar j hj).1]
  · by_cases hj : j = a
    · subst j
      simp [recoveredGram, gauge, anchorScale, hi, pairRead, trace_pair]
    · simp only [recoveredGram, hi, hj, if_false, gauge, anchorScale,
        pairRead, tripleRead, trace_pair, trace_triple]
      field_simp [(hstar j hj).1, (hstar j hj).2]
      <;> ring

private theorem gauge_increment (d : I → K) (H : Matrix I I K) (i : I) :
    gauge d (increment H i) = increment (gauge d H) i := by
  ext r c
  by_cases hr : r = i
  · subst r
    simp [gauge, increment]
  · simp [gauge, increment, hr]

/-- The entrywise gauge really is simultaneous matrix conjugation. -/
theorem gauge_eq_diagonal_conjugation (d : I → K) (M : Matrix I I K) :
    gauge d M = Matrix.diagonal d * M * Matrix.diagonal (fun i => (d i)⁻¹) := by
  ext i j
  simp [gauge, Matrix.mul_apply, Matrix.diagonal, div_eq_mul_inv]

/-- Invertibility of the exhibited normalizer. -/
theorem anchor_diagonal_inverse (H : Matrix I I K) (a : I)
    (hstar : ∀ j, j ≠ a → H a j ≠ 0 ∧ H j a ≠ 0) :
    Matrix.diagonal (anchorScale H a) *
        Matrix.diagonal (fun i => (anchorScale H a i)⁻¹) = 1 ∧
      Matrix.diagonal (fun i => (anchorScale H a i)⁻¹) *
        Matrix.diagonal (anchorScale H a) = 1 := by
  constructor <;> ext i j <;> by_cases h : i = j
  · subst j
    simp [Matrix.mul_apply, Matrix.diagonal, anchorScale_ne_zero H a hstar]
  · simp [Matrix.mul_apply, Matrix.diagonal, h]
  · subst j
    simp [Matrix.mul_apply, Matrix.diagonal, anchorScale_ne_zero H a hstar]
  · simp [Matrix.mul_apply, Matrix.diagonal, h]

/-- Actual tuple recovery from scalar observations, with a constructed invertible
normalizer and genuine matrix products. -/
theorem simultaneous_reconstruction (H : Matrix I I K) (a : I)
    (hdiag : ∀ i, H i i = 0)
    (hstar : ∀ j, j ≠ a → H a j ≠ 0 ∧ H j a ≠ 0) (i : I) :
    Matrix.diagonal (anchorScale H a) * increment H i *
        Matrix.diagonal (fun j => (anchorScale H a j)⁻¹) =
      increment (recoveredGram a (pairRead H a) (tripleRead H a)) i := by
  rw [← gauge_eq_diagonal_conjugation, gauge_increment,
    recoveredGram_eq_gauge H a hdiag hstar]

/-- Products are preserved by the constructed gauge on every finite word. -/
theorem gauge_mul (d : I → K) (hd : ∀ i, d i ≠ 0)
    (M N : Matrix I I K) : gauge d (M * N) = gauge d M * gauge d N := by
  ext i j
  simp only [gauge, Matrix.mul_apply, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  field_simp [hd i, hd j, hd k]
  <;> ring

private theorem gauge_one (d : I → K) (hd : ∀ i, d i ≠ 0) :
    gauge d (1 : Matrix I I K) = 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [gauge, hd]
  · simp [gauge, h]

/-- Observable recovery propagates to arbitrarily long noncommuting words. -/
theorem reconstruct_word (H : Matrix I I K) (a : I)
    (hdiag : ∀ i, H i i = 0)
    (hstar : ∀ j, j ≠ a → H a j ≠ 0 ∧ H j a ≠ 0) (w : List I) :
    gauge (anchorScale H a) ((w.map (increment H)).prod) =
      (w.map (increment (recoveredGram a (pairRead H a) (tripleRead H a)))).prod := by
  induction w with
  | nil => simp [gauge_one, anchorScale_ne_zero H a hstar]
  | cons i w ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [gauge_mul _ (anchorScale_ne_zero H a hstar), ih, gauge_increment,
        recoveredGram_eq_gauge H a hdiag hstar]

private theorem gauge_add (d : I → K) (M N : Matrix I I K) :
    gauge d (M + N) = gauge d M + gauge d N := by
  ext i j
  simp [gauge, mul_add, add_div]

/-- Recovery of the invertible generators, including arbitrarily long ordered words. -/
theorem reconstruct_transvection_word (H : Matrix I I K) (a : I)
    (hdiag : ∀ i, H i i = 0)
    (hstar : ∀ j, j ≠ a → H a j ≠ 0 ∧ H j a ≠ 0) (w : List I) :
    gauge (anchorScale H a) ((w.map (fun i => 1 + increment H i)).prod) =
      (w.map (fun i => 1 +
        increment (recoveredGram a (pairRead H a) (tripleRead H a)) i)).prod := by
  induction w with
  | nil => simp [gauge_one, anchorScale_ne_zero H a hstar]
  | cons i w ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [gauge_mul _ (anchorScale_ne_zero H a hstar), ih, gauge_add,
        gauge_one _ (anchorScale_ne_zero H a hstar), gauge_increment,
        recoveredGram_eq_gauge H a hdiag hstar]

#print axioms simultaneous_reconstruction
#print axioms reconstruct_transvection_word

end D5.S3.Observer.Monodromy.TransvectionTraceReconstruction
