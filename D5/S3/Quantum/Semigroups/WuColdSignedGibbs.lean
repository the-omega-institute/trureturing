/- GID: D5/S3/Quantum/Semigroups/WuColdSignedGibbs
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuColdSignedGibbs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The signed Gibbs map transports the odd kernel and determines its trace quartic. -/

import D5.S3.Quantum.Semigroups.WuRankOneEndpointFloor
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
The signed two-mode map at Wu's 3-to-4 critical time, in ordinary traces.
The physical parameter is `s = exp (-β/12)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped Matrix ComplexConjugate
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf

namespace D5.S3.Quantum.Semigroups.WuColdSignedGibbs

open WuRankOneEndpointFloor (Bit Mode Qubit TwoMode W)

abbrev Row := Bit → ℂ

def u (s : ℝ) : ℝ := s ^ 4
def w (s : ℝ) : ℝ := s ^ 3
def M (s : ℝ) : ℝ := 1 + s ^ 12
def L (s : ℝ) : ℝ := 1 + w s + w s ^ 2
def h (s : ℝ) : ℝ := (1 + u s) / L s
def r (s : ℝ) : ℝ := s * h s
def κ (s : ℝ) : ℂ := (Real.sqrt (h s) : ℂ)

def α (s : ℝ) : ℝ := (s ^ 11 + h s) / M s
def η (s : ℝ) : ℝ := w s * (1 - r s) / M s
def ζ (s : ℝ) : ℝ := u s ^ 2 * (1 - r s) / M s
def δ (s : ℝ) : ℝ := (1 + s ^ 12 * r s) / M s

private theorem M_pos (s : ℝ) : 0 < M s := by
  unfold M
  positivity

private theorem L_pos {s : ℝ} (hs : 0 ≤ s) : 0 < L s := by
  unfold L w
  positivity

private theorem κ_mul_self {s : ℝ} (hs : 0 ≤ s) : κ s * κ s = (h s : ℂ) := by
  have hh : 0 ≤ h s := by
    unfold h u
    exact div_nonneg (by positivity) (L_pos hs).le
  unfold κ
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt hh]

private theorem population_gibbs_top (s : ℝ) : α s * u s + η s = w s := by
  unfold α η
  field_simp [ne_of_gt (M_pos s)]
  simp only [M, w, u, r]
  ring

private theorem population_gibbs_bottom (s : ℝ) : ζ s * u s + δ s = 1 := by
  unfold ζ δ
  field_simp [ne_of_gt (M_pos s)]
  simp only [M, u]
  ring

/-- Coordinates of the ordinary-transpose row `zᵀ J` for `J = !![0,-1;1,0]`. -/
def jRow (z : Row) : Row := ![z 1, -z 0]

/-- The `00`-to-odd row `x'`. -/
def signedX (s : ℝ) (x z : Row) : Row :=
  fun i => κ s * ((α s : ℂ) * x i + (η s : ℂ) * jRow z i)

/-- The odd-to-`11` column `z'` in the same coordinate type. `J xᵀ` has coordinates `-jRow x`. -/
def signedZ (s : ℝ) (x z : Row) : Row :=
  fun i => κ s * ((δ s : ℂ) * z i - (ζ s : ℂ) * jRow x i)

/-- The population weights for the matching and flipped diagonal entries of the local map. -/
private def diagonalWeight (s : ℝ) (i : Bit) : ℂ :=
  if i = 0 then (α s : ℂ) else (δ s : ℂ)

private def flipWeight (s : ℝ) (i : Bit) : ℂ :=
  if i = 0 then (η s : ℂ) else (ζ s : ℂ)

private def localApply (s : ℝ) (X : Qubit) : Qubit := fun i j =>
  if i = j then diagonalWeight s i * X i j + flipWeight s i * X i.rev j.rev
  else κ s * X i j

def localMap (s : ℝ) : MatrixMap Bit Bit ℂ where
  toFun := localApply s
  map_add' X Y := by
    ext i j
    by_cases hij : i = j <;> simp [localApply, hij] <;> ring
  map_smul' c X := by
    ext i j
    by_cases hij : i = j <;> simp [localApply, hij] <;> ring

/-- The literal two-twist composition, using the same `W` as the endpoint map. -/
def signedMap (s : ℝ) : MatrixMap Mode Mode ℂ :=
  (MatrixMap.kron (localMap s) LinearMap.id).comp
    ((MatrixMap.conj W).comp
      ((MatrixMap.kron LinearMap.id (localMap s)).comp (MatrixMap.conj W)))

private theorem left_apply (s : ℝ) (X : TwoMode) (i j k l : Bit) :
    MatrixMap.kron (localMap s) LinearMap.id X (i,k) (j,l) =
      if i = j then diagonalWeight s i * X (i,k) (j,l) +
        flipWeight s i * X (i.rev,k) (j.rev,l)
      else κ s * X (i,k) (j,l) := by
  rw [MatrixMap.kron_def]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [Fin.sum_univ_two, localMap, localApply, Matrix.single_apply, Fin.rev, Fin.isValue] <;>
    ring

private theorem right_apply (s : ℝ) (X : TwoMode) (i j k l : Bit) :
    MatrixMap.kron LinearMap.id (localMap s) X (i,k) (j,l) =
      if k = l then diagonalWeight s k * X (i,k) (j,l) +
        flipWeight s k * X (i,k.rev) (j,l.rev)
      else κ s * X (i,k) (j,l) := by
  rw [MatrixMap.kron_def]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [Fin.sum_univ_two, localMap, localApply, Matrix.single_apply, Fin.rev, Fin.isValue] <;>
    ring

private def twistSign (i : Mode) : ℂ := if i = (1, 0) then -1 else 1

private theorem twist_apply (X : TwoMode) (i j : Mode) :
    MatrixMap.conj W X i j = twistSign i * X i j * twistSign j := by
  have hW : W = diagonal twistSign := rfl
  have hHerm : W.conjTranspose = W := by
    rw [hW]
    ext a b
    by_cases hab : a = b
    · subst b
      by_cases ha : a = (1, 0) <;>
        simp [twistSign, ha, Matrix.conjTranspose_apply]
    · simp [hab, Ne.symm hab, Matrix.conjTranspose_apply]
  rw [MatrixMap.conj_apply, hHerm, hW, mul_diagonal, diagonal_mul]

private def modeIndex (i : Mode) : Fin 4 :=
  if i.1 = 0 then (if i.2 = 0 then 0 else 1) else (if i.2 = 0 then 2 else 3)

/-- The Hermitian matrix supported on the `x`, `z`, and `d` coherences.
    Its three-edge walks select the `conj d * (x z)` part of the full cubic. -/
def triangleMatrix (x z : Row) (d : ℂ) : TwoMode := Matrix.of fun i j =>
  (!![0, x 0, x 1, d;
      conj (x 0), 0, 0, z 0;
      conj (x 1), 0, 0, z 1;
      conj d, conj (z 0), conj (z 1), 0] : Matrix (Fin 4) (Fin 4) ℂ)
    (modeIndex i) (modeIndex j)

set_option maxHeartbeats 2000000 in
-- Unfold the map and both twists at all sixteen entries.
/-- The literal map has the adjugate row action and multiplies `d` by `h`. -/
theorem signedMap_triangle {s : ℝ} (hs : 0 ≤ s) (x z : Row) (d : ℂ) :
    signedMap s (triangleMatrix x z d) =
      triangleMatrix (signedX s x z) (signedZ s x z) ((h s : ℂ) * d) := by
  have hsquare := κ_mul_self hs
  have hconj : conj (κ s) = κ s := by simp [κ]
  ext ⟨i,k⟩ ⟨j,l⟩
  simp only [signedMap, LinearMap.comp_apply, left_apply, right_apply, twist_apply]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [diagonalWeight, flipWeight, twistSign, triangleMatrix, modeIndex,
      signedX, signedZ, jRow, Fin.rev, Fin.isValue, hconj, ← mul_assoc, hsquare,
      -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring

def gibbsWeight (a : ℝ) : TwoMode :=
  diagonal fun i => ![(a : ℂ) ^ 2, (a : ℂ), (a : ℂ), (1 : ℂ)] (modeIndex i)

/-- The odd Hessian direction `N_a(z)` used in the fixed-cube path. -/
def kernelMatrix (a : ℝ) (z : Row) : TwoMode :=
  triangleMatrix ((a : ℂ) • jRow z) z 0

private theorem triangleMatrix_scale (c : ℂ) (hc : conj c = c) (x z : Row) :
    triangleMatrix (c • x) (c • z) 0 = c • triangleMatrix x z 0 := by
  ext ⟨i,k⟩ ⟨j,l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [triangleMatrix, modeIndex, Pi.smul_apply, smul_eq_mul, hc, Fin.isValue]

/-- The physical map transports `N_u(z)` to `sqrt h * N_w(z)`. -/
theorem signedMap_kernel {s : ℝ} (hs : 0 ≤ s) (z : Row) :
    signedMap s (kernelMatrix (u s) z) = κ s • kernelMatrix (w s) z := by
  have htop : (α s : ℂ) * (u s : ℂ) + (η s : ℂ) = (w s : ℂ) := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_add] using
      congrArg (fun a : ℝ => (a : ℂ)) (population_gibbs_top s)
  have hbottom : (ζ s : ℂ) * (u s : ℂ) + (δ s : ℂ) = 1 := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_one] using
      congrArg (fun a : ℝ => (a : ℂ)) (population_gibbs_bottom s)
  have hx : signedX s ((u s : ℂ) • jRow z) z = κ s • ((w s : ℂ) • jRow z) := by
    funext i
    calc
      _ = κ s * (((α s : ℂ) * (u s : ℂ) + (η s : ℂ)) * jRow z i) := by
        simp only [signedX, Pi.smul_apply, smul_eq_mul]
        ring
      _ = _ := by simp only [htop, Pi.smul_apply, smul_eq_mul]
  have hz : signedZ s ((u s : ℂ) • jRow z) z = κ s • z := by
    funext i
    calc
      _ = κ s * (((ζ s : ℂ) * (u s : ℂ) + (δ s : ℂ)) * z i) := by
        fin_cases i <;>
          simp [signedZ, jRow, Pi.smul_apply, smul_eq_mul, -mul_eq_mul_left_iff] <;> ring
      _ = _ := by simp only [hbottom, one_mul, Pi.smul_apply, smul_eq_mul]
  unfold kernelMatrix
  rw [signedMap_triangle hs, hx, hz, mul_zero]
  exact triangleMatrix_scale (κ s) (by simp [κ]) _ _

def ν (z : Row) : ℝ := Complex.normSq (z 0) + Complex.normSq (z 1)

set_option maxHeartbeats 2000000 in
-- The entrywise expansion sums over both mode bits.
private theorem weighted_kernel_sq (a : ℝ) (z : Row) :
    (gibbsWeight a * kernelMatrix a z ^ 2).trace.re = (1 + a) * (1 + a ^ 3) * ν z := by
  simp only [gibbsWeight, Matrix.trace, Matrix.diag_apply, diagonal_mul, pow_two]
  norm_num [kernelMatrix, triangleMatrix, modeIndex, jRow, ν, Matrix.mul_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

set_option maxHeartbeats 2000000 in
-- The entrywise expansion multiplies two matrix squares before taking the trace.
private theorem kernel_trace_fourth (a : ℝ) (z : Row) :
    (kernelMatrix a z ^ 4).trace.re = 2 * (1 + a ^ 4) * ν z ^ 2 := by
  let N := kernelMatrix a z
  have hpow : N ^ 4 = (N * N) * (N * N) := by
    simpa only [pow_two] using pow_mul N 2 2
  change (N ^ 4).trace.re = _
  rw [hpow]
  norm_num [N, kernelMatrix, triangleMatrix, modeIndex, jRow, ν, Matrix.trace,
    Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Pi.smul_apply, smul_eq_mul, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

/-- The pure quartic on `N_u(z)` with the ordinary trace-cube normalization. -/
theorem kernel_pure_quartic {s : ℝ} (hs : 0 ≤ s) (z : Row) :
    2 / M s ^ 2 * (gibbsWeight (u s) * kernelMatrix (u s) z ^ 2).trace.re ^ 2 -
        (signedMap s (kernelMatrix (u s) z) ^ 4).trace.re =
      2 * h s ^ 2 * w s * (2 + 3 * w s + 2 * w s ^ 2) * ν z ^ 2 := by
  have hu : 1 + u s ^ 3 = M s := by unfold u M; ring
  have hw : 1 + w s ^ 4 = M s := by unfold w M; ring
  have hh : h s * L s = 1 + u s := by
    unfold h
    exact div_mul_cancel₀ _ (ne_of_gt (L_pos hs))
  have hk : κ s ^ 4 = ((h s ^ 2 : ℝ) : ℂ) := by
    calc
      _ = (κ s * κ s) ^ 2 := by ring
      _ = _ := by rw [κ_mul_self hs, Complex.ofReal_pow]
  rw [weighted_kernel_sq, signedMap_kernel hs, smul_pow, Matrix.trace_smul, hk,
    smul_eq_mul, Complex.re_ofReal_mul, kernel_trace_fourth, hu, hw]
  calc
    _ = (2 * (1 + u s) ^ 2 - 2 * h s ^ 2 * M s) * ν z ^ 2 := by
      field_simp [ne_of_gt (M_pos s)]
    _ = _ := by
      rw [← hh, ← hw]
      unfold L
      ring

#print axioms signedMap_triangle
#print axioms signedMap_kernel
#print axioms kernel_pure_quartic

end D5.S3.Quantum.Semigroups.WuColdSignedGibbs
