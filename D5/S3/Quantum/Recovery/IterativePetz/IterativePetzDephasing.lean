/- GID: D5/S3/Quantum/Recovery/IterativePetz/IterativePetzDephasing
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/IterativePetz/IterativePetzDephasing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Derive single-axis iterative Petz dynamics and the pure-state recovery bias. -/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import OmegaBuild.Commands

/-! Omega original.

The single-axis qubit update of Lautenbacher et al., arXiv:2611.32995v1,
in real coherence and axial Bloch coordinates. Iteration starts at the first
recovered state, where the determinant is positive for nonpolar pure inputs.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter
open scoped Matrix Topology

namespace D5.S3.Quantum.Recovery.IterativePetz.IterativePetzDephasing

/-- Determinant at coherence `c` and axial coordinate `z`. -/
def blochDet (c z : ℝ) : ℝ := (1 - z ^ 2) / 4 - c ^ 2

def petzL (a c s d : ℝ) : ℝ :=
  a * (1 - a) * c * s / (d ^ 2 * (1 + 2 * d))

def petzDelta (a c z s d : ℝ) : ℝ :=
  petzL a c s d *
    (s * (1 + 2 * d) + z ^ 2 * (d - s) / (1 + 2 * s))

def petzShrink (a c s d : ℝ) : ℝ :=
  1 - 4 * c * petzL a c s d * (d - s) / (1 + 2 * s)

/-- The coordinate update with the two square roots of determinants supplied. -/
def petzStep (a c z s d : ℝ) : ℝ × ℝ :=
  (c + petzDelta a c z s d, z * petzShrink a c s d)

def step (a c z : ℝ) : ℝ × ℝ :=
  petzStep a c z (Real.sqrt (blochDet c z)) (Real.sqrt (blochDet (a * c) z))

private theorem l_pos {a c s d : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hc : 0 < c) (hs : 0 < s) (hd : 0 < d) : 0 < petzL a c s d := by
  have ha : 0 < 1 - a := sub_pos.mpr ha1
  unfold petzL
  positivity

private theorem det_lt_dephased {a c z : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hc : 0 < c) : blochDet c z < blochDet (a * c) z := by
  have hac : a * c < c := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right ha1 hc
  have hsq : (a * c) ^ 2 < c ^ 2 := (sq_lt_sq₀ (by positivity) hc.le).mpr hac
  unfold blochDet
  linarith

private theorem delta_lower {a c z s d : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hc : 0 < c) (hs : 0 < s) (hsd : s < d) (hd2 : d ^ 2 ≤ 1) :
    a * (1 - a) * c * s ^ 2 ≤ petzDelta a c z s d := by
  have hd : 0 < d := hs.trans hsd
  have hds : 0 ≤ d - s := sub_nonneg.mpr hsd.le
  have hL : 0 < petzL a c s d := l_pos ha0 ha1 hc hs hd
  have hterm : 0 ≤ z ^ 2 * (d - s) / (1 + 2 * s) := by positivity
  have hbase : 0 < a * (1 - a) * c * s ^ 2 := by
    have ha : 0 < 1 - a := sub_pos.mpr ha1
    positivity
  have hd0 : d ≠ 0 := hd.ne'
  have hd1 : 1 + 2 * d ≠ 0 := ne_of_gt (by positivity)
  calc
    a * (1 - a) * c * s ^ 2 ≤ (a * (1 - a) * c * s ^ 2) / d ^ 2 := by
      apply (le_div_iff₀ (by positivity : 0 < d ^ 2)).mpr
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hd2 hbase.le
    _ = petzL a c s d * (s * (1 + 2 * d)) := by
      unfold petzL
      field_simp [hd0, hd1]
    _ ≤ petzDelta a c z s d := by
      unfold petzDelta
      apply mul_le_mul_of_nonneg_left _ hL.le
      linarith

private theorem shrink_bounds {a c s d : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hc : 0 < c) (hc2 : c ^ 2 ≤ 1 / 4) (hs : 0 < s) (hsd : s < d) :
    0 < petzShrink a c s d ∧ petzShrink a c s d < 1 := by
  have hd : 0 < d := hs.trans hsd
  have hds : 0 < d - s := sub_pos.mpr hsd
  have ha : 0 < 1 - a := sub_pos.mpr ha1
  have hB : 0 < 4 * a * (1 - a) * c ^ 2 := by positivity
  have hB' : 4 * a * (1 - a) * c ^ 2 ≤ 1 / 4 := by
    have ha' : a * (1 - a) ≤ 1 / 4 := by nlinarith [sq_nonneg (a - 1 / 2)]
    have hmul := mul_le_mul_of_nonneg_left hc2 (by positivity : 0 ≤ 4 * (a * (1 - a)))
    nlinarith only [ha', hmul]
  have hnum : s * (d - s) ≤ d ^ 2 := by
    calc
      s * (d - s) ≤ d * (d - s) := mul_le_mul_of_nonneg_right hsd.le hds.le
      _ ≤ d * d := mul_le_mul_of_nonneg_left (by linarith) hd.le
      _ = d ^ 2 := by ring
  have hden : d ^ 2 ≤ (d ^ 2 * (1 + 2 * d)) * (1 + 2 * s) := by
    have h₁ : d ^ 2 ≤ d ^ 2 * (1 + 2 * d) := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (show 1 ≤ 1 + 2 * d by linarith) (sq_nonneg d)
    have h₂ : d ^ 2 * (1 + 2 * d) ≤ (d ^ 2 * (1 + 2 * d)) * (1 + 2 * s) := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (show 1 ≤ 1 + 2 * s by linarith)
          (by positivity : 0 ≤ d ^ 2 * (1 + 2 * d))
    exact h₁.trans h₂
  have hratio : 0 < s * (d - s) / ((d ^ 2 * (1 + 2 * d)) * (1 + 2 * s)) := by
    positivity
  have hratio' : s * (d - s) / ((d ^ 2 * (1 + 2 * d)) * (1 + 2 * s)) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    simpa only [one_mul] using hnum.trans hden
  have hform : petzShrink a c s d = 1 -
      (4 * a * (1 - a) * c ^ 2) *
        (s * (d - s) / ((d ^ 2 * (1 + 2 * d)) * (1 + 2 * s))) := by
    unfold petzShrink petzL
    have hd' : d ≠ 0 := hd.ne'
    have hd'' : 1 + 2 * d ≠ 0 := ne_of_gt (by positivity)
    have hs' : 1 + 2 * s ≠ 0 := ne_of_gt (by positivity)
    field_simp [hd', hd'', hs']
  have hmul := mul_le_mul_of_nonneg_left hratio' hB.le
  rw [mul_one] at hmul
  rw [hform]
  constructor
  · linarith only [hmul, hB']
  · linarith only [mul_pos hB hratio]

private theorem step_bounds {a c z : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hc : 0 < c) (hdet : 0 < blochDet c z) :
    (a * (1 - a) * c) * blochDet c z ≤
        petzDelta a c z (Real.sqrt (blochDet c z)) (Real.sqrt (blochDet (a * c) z)) ∧
      0 < petzShrink a c (Real.sqrt (blochDet c z)) (Real.sqrt (blochDet (a * c) z)) ∧
      petzShrink a c (Real.sqrt (blochDet c z)) (Real.sqrt (blochDet (a * c) z)) < 1 := by
  have hlt := det_lt_dephased (z := z) ha0 ha1 hc
  have hdet' := hdet.trans hlt
  have hs := Real.sqrt_pos.mpr hdet
  have hsd := Real.sqrt_lt_sqrt hdet.le hlt
  have hc2 : c ^ 2 ≤ 1 / 4 := by
    unfold blochDet at hdet
    linarith [sq_nonneg z]
  have hd2 : Real.sqrt (blochDet (a * c) z) ^ 2 ≤ 1 := by
    rw [Real.sq_sqrt hdet'.le]
    unfold blochDet
    linarith [sq_nonneg z, sq_nonneg (a * c)]
  refine ⟨?_, shrink_bounds ha0 ha1 hc hc2 hs hsd⟩
  simpa only [Real.sq_sqrt hdet.le] using delta_lower ha0 ha1 hc hs hsd hd2

/-! ## Matrix calculation -/

abbrev QubitMatrix := Matrix (Fin 2) (Fin 2) ℝ

def qubitState (p c : ℝ) : QubitMatrix := !![p, c; c, 1 - p]

def dephase (a : ℝ) (A : QubitMatrix) : QubitMatrix :=
  !![A 0 0, a * A 0 1; a * A 1 0, A 1 1]

private def flip : QubitMatrix := !![0, 1; 1, 0]

def rootNumerator (p c s : ℝ) : QubitMatrix :=
  !![p + s, c; c, 1 - p + s]

def inverseRootNumerator (a p c d : ℝ) : QubitMatrix :=
  !![1 - p + d, -(a * c); -(a * c), p + d]

private def responseNumerator (p c d : ℝ) : QubitMatrix :=
  !![-2 * c * (1 - p + d), d + 2 * p * (1 - p);
    d + 2 * p * (1 - p), -2 * c * (p + d)]

@[simp] theorem dephase_state (a p c : ℝ) :
    dephase a (qubitState p c) = qubitState p (a * c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem dephase_add (a : ℝ) (A B : QubitMatrix) :
    dephase a (A + B) = dephase a A + dephase a B := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dephase, mul_add]

private theorem dephase_smul (a b : ℝ) (A : QubitMatrix) :
    dephase a (b • A) = b • dephase a A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dephase, smul_eq_mul] <;> ring

private theorem dephase_one (a : ℝ) : dephase a (1 : QubitMatrix) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dephase]

private theorem state_eq_dephase_add (a p c : ℝ) :
    qubitState p c = dephase a (qubitState p c) + ((1 - a) * c) • flip := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qubitState, dephase, flip, smul_eq_mul] <;> ring

/-- The square-root numerator squared, by the trace-one determinant relation. -/
theorem rootNumerator_sq (p c s : ℝ) (hs : s ^ 2 = p * (1 - p) - c ^ 2) :
    rootNumerator p c s * rootNumerator p c s = (1 + 2 * s) • qubitState p c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootNumerator, qubitState, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]
  · linear_combination hs
  · ring
  · ring
  · linear_combination hs

/-- Product of the inverse-root numerator and the dephased root numerator. -/
theorem inverseRootNumerator_mul_rootNumerator (a p c d : ℝ)
    (hd : d ^ 2 = p * (1 - p) - (a * c) ^ 2) :
    inverseRootNumerator a p c d * rootNumerator p (a * c) d =
      (d * (1 + 2 * d)) • (1 : QubitMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootNumerator, inverseRootNumerator, Matrix.mul_apply, Fin.sum_univ_two,
      smul_eq_mul]
  · linear_combination -hd
  · ring
  · ring
  · linear_combination -hd

/-- The normalized explicit square root in the real slice. -/
def qubitRoot (p c s : ℝ) : QubitMatrix :=
  (Real.sqrt (1 + 2 * s))⁻¹ • rootNumerator p c s

/-- The normalized explicit inverse root of the dephased state. -/
def qubitInverseRoot (a p c d : ℝ) : QubitMatrix :=
  (d * Real.sqrt (1 + 2 * d))⁻¹ • inverseRootNumerator a p c d

theorem qubitRoot_mul_self (p c s : ℝ)
    (hs : s ^ 2 = p * (1 - p) - c ^ 2) (hs₀ : 0 ≤ s) :
    qubitRoot p c s * qubitRoot p c s = qubitState p c := by
  have hpos : 0 < 1 + 2 * s := by positivity
  have hnorm : (Real.sqrt (1 + 2 * s))⁻¹ * (Real.sqrt (1 + 2 * s))⁻¹ =
      (1 + 2 * s)⁻¹ := by
    rw [← pow_two, inv_pow, Real.sq_sqrt hpos.le]
  simp only [qubitRoot, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [rootNumerator_sq p c s hs, hnorm, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]

theorem qubitInverseRoot_mul_root (a p c d : ℝ)
    (hd : d ^ 2 = p * (1 - p) - (a * c) ^ 2) (hd₀ : 0 < d) :
    qubitInverseRoot a p c d * qubitRoot p (a * c) d = 1 := by
  have hpos : 0 < 1 + 2 * d := by positivity
  have hroot : Real.sqrt (1 + 2 * d) * (d * Real.sqrt (1 + 2 * d)) =
      d * (1 + 2 * d) := by
    calc
      _ = d * Real.sqrt (1 + 2 * d) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hpos.le]
  have hnorm : (Real.sqrt (1 + 2 * d))⁻¹ * (d * Real.sqrt (1 + 2 * d))⁻¹ *
      (d * (1 + 2 * d)) = 1 := by
    rw [← mul_inv, hroot, inv_mul_cancel₀ (mul_ne_zero hd₀.ne' hpos.ne')]
  simp only [qubitInverseRoot, qubitRoot, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [inverseRootNumerator_mul_rootNumerator a p c d hd, smul_smul, hnorm, one_smul]

private theorem inverseRootNumerator_congr_dephased (a p c d : ℝ)
    (hd : d ^ 2 = p * (1 - p) - (a * c) ^ 2) :
    inverseRootNumerator a p c d * dephase a (qubitState p c) *
        inverseRootNumerator a p c d =
      (d ^ 2 * (1 + 2 * d)) • (1 : QubitMatrix) := by
  rw [dephase_state]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qubitState, inverseRootNumerator, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]
  · linear_combination (-2 * d + p - 1) * hd
  · linear_combination (a * c) * hd
  · linear_combination (a * c) * hd
  · linear_combination (-2 * d - p) * hd

private theorem dephase_inverseRootNumerator_flip (a p c d : ℝ)
    (hd : d ^ 2 = p * (1 - p) - (a * c) ^ 2) :
    dephase a (inverseRootNumerator a p c d * flip * inverseRootNumerator a p c d) =
      a • responseNumerator p c d := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dephase, inverseRootNumerator, responseNumerator, flip,
      Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]
  · ring
  · exact Or.inl (by linear_combination hd)
  · exact Or.inl (by linear_combination hd)
  · ring

private theorem rootNumerator_congr_response (p c s d : ℝ)
    (hs : s ^ 2 = p * (1 - p) - c ^ 2) :
    rootNumerator p c s * responseNumerator p c d * rootNumerator p c s =
      let z := 2 * p - 1
      let x := s * (s * (1 + 2 * d) * (1 + 2 * s) + z ^ 2 * (d - s))
      let y := -2 * c * s * z * (d - s)
      !![y, x; x, -y] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootNumerator, responseNumerator, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (-2 * c * (d + p)) * hs
  · linear_combination (-4 * d * s - d + 2 * p ^ 2 - 2 * p - 2 * s) * hs
  · linear_combination (-4 * d * s - d + 2 * p ^ 2 - 2 * p - 2 * s) * hs
  · linear_combination (2 * c * (-d + p - 1)) * hs

/-- The recovery map applied to its own reference in the phase-aligned slice.
The two root normalizations combine into the displayed scalar. -/
def matrixStep (a p c s d : ℝ) : QubitMatrix :=
  ((1 + 2 * s) * (d ^ 2 * (1 + 2 * d)))⁻¹ •
    (rootNumerator p c s *
      dephase a (inverseRootNumerator a p c d * qubitState p c *
        inverseRootNumerator a p c d) * rootNumerator p c s)

/-- The scaled matrix update equals the product using the normalized roots. -/
theorem matrixStep_eq_root_product (a p c s d : ℝ) (hs : 0 ≤ s) (hd : 0 ≤ d) :
    matrixStep a p c s d =
      qubitRoot p c s *
        dephase a (qubitInverseRoot a p c d * qubitState p c *
          qubitInverseRoot a p c d) * qubitRoot p c s := by
  have hs' : 0 ≤ 1 + 2 * s := by positivity
  have hd' : 0 ≤ 1 + 2 * d := by positivity
  have hden : (1 + 2 * s) * (d ^ 2 * (1 + 2 * d)) =
      Real.sqrt (1 + 2 * s) ^ 2 * (d * Real.sqrt (1 + 2 * d)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hs', Real.sq_sqrt hd']
  simp only [matrixStep, qubitRoot, qubitInverseRoot, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, dephase_smul]
  congr 1
  rw [hden, mul_inv, ← inv_pow, ← inv_pow]
  ring

/-- The explicit matrix update gives both scalar recurrence equations. -/
theorem matrixStep_eq_step (a p c s d : ℝ) (hs : s ^ 2 = p * (1 - p) - c ^ 2)
    (hd : d ^ 2 = p * (1 - p) - (a * c) ^ 2) (hs₀ : 0 ≤ s) (hd₀ : 0 < d) :
    matrixStep a p c s d =
      let next := petzStep a c (2 * p - 1) s d
      qubitState ((1 + next.2) / 2) next.1 := by
  let R := rootNumerator p c s
  let T := inverseRootNumerator a p c d
  let A := qubitState p c
  have hstate : A = dephase a A + ((1 - a) * c) • flip :=
    state_eq_dephase_add a p c
  have hinner : T * A * T =
      T * dephase a A * T + ((1 - a) * c) • (T * flip * T) := by
    calc
      _ = T * (dephase a A + ((1 - a) * c) • flip) * T :=
        congrArg (fun M => T * M * T) hstate
      _ = _ := by simp only [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hd' : d ≠ 0 := hd₀.ne'
  have hd'' : 1 + 2 * d ≠ 0 := ne_of_gt (by positivity)
  have hs' : 1 + 2 * s ≠ 0 := ne_of_gt (by positivity)
  change _ • (R * dephase a (T * A * T) * R) = _
  rw [hinner, dephase_add, dephase_smul,
    show T * dephase a A * T = _ from inverseRootNumerator_congr_dephased a p c d hd,
    dephase_smul, dephase_one,
    show dephase a (T * flip * T) = _ from dephase_inverseRootNumerator_flip a p c d hd]
  simp only [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one]
  rw [show R * R = _ from rootNumerator_sq p c s hs,
    show R * responseNumerator p c d * R = _ from rootNumerator_congr_response p c s d hs]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [qubitState, petzStep, petzDelta, petzShrink, petzL, smul_eq_mul] <;>
    field_simp [hd', hd'', hs'] <;> ring

private theorem det_dephase_pos {a : ℝ} (ha : a ^ 2 ≤ 1) (B : QubitMatrix)
    (hsym : B 0 1 = B 1 0) (hdet : 0 < B.det) :
    0 < (dephase a B).det := by
  rw [Matrix.det_fin_two, ← hsym] at hdet
  have h := mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg (B 0 1))
  simp [dephase, Matrix.det_fin_two, ← hsym]
  nlinarith only [hdet, h]

private theorem det_matrixStep_pos {a p c s d : ℝ} (ha : a ^ 2 ≤ 1)
    (hs : s ^ 2 = p * (1 - p) - c ^ 2) (hs₀ : 0 < s)
    (hd : d ^ 2 = p * (1 - p) - (a * c) ^ 2) (hd₀ : 0 < d) :
    0 < (matrixStep a p c s d).det := by
  let T := inverseRootNumerator a p c d
  let R := rootNumerator p c s
  let A := qubitState p c
  let B := T * A * T
  have hA : 0 < A.det := by
    change 0 < (qubitState p c).det
    rw [qubitState, Matrix.det_fin_two_of]
    nlinarith only [hs, sq_pos_of_pos hs₀]
  have hR : 0 < R.det := by
    change 0 < (rootNumerator p c s).det
    rw [rootNumerator, Matrix.det_fin_two_of]
    have h : 0 < s * (1 + 2 * s) := by positivity
    nlinarith only [hs, h]
  have hT : 0 < T.det := by
    change 0 < (inverseRootNumerator a p c d).det
    rw [inverseRootNumerator, Matrix.det_fin_two_of]
    have h : 0 < d * (1 + 2 * d) := by positivity
    nlinarith only [hd, h]
  have hB : 0 < B.det := by
    change 0 < (T * A * T).det
    rw [Matrix.det_mul, Matrix.det_mul]
    positivity
  have hsym : B 0 1 = B 1 0 := by
    simp [B, T, A, inverseRootNumerator, qubitState]
    ring
  have hN := det_dephase_pos ha B hsym hB
  change 0 < ((_ : ℝ) • (R * dephase a B * R)).det
  rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul]
  positivity

/-- Strict positivity of the determinant is preserved by the recovery step. -/
theorem step_det_pos {a c z : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hc : 0 < c) (hdet : 0 < blochDet c z) :
    0 < blochDet (step a c z).1 (step a c z).2 := by
  let p := (1 + z) / 2
  let s := Real.sqrt (blochDet c z)
  let d := Real.sqrt (blochDet (a * c) z)
  have hs₀ : 0 < s := Real.sqrt_pos.mpr hdet
  have hdet' := hdet.trans (det_lt_dephased (z := z) ha0 ha1 hc)
  have hd₀ : 0 < d := Real.sqrt_pos.mpr hdet'
  have hs : s ^ 2 = p * (1 - p) - c ^ 2 := by
    change Real.sqrt (blochDet c z) ^ 2 = _
    rw [Real.sq_sqrt hdet.le]
    unfold p blochDet
    ring
  have hd : d ^ 2 = p * (1 - p) - (a * c) ^ 2 := by
    change Real.sqrt (blochDet (a * c) z) ^ 2 = _
    rw [Real.sq_sqrt hdet'.le]
    unfold p blochDet
    ring
  have ha : a ^ 2 ≤ 1 := by
    simpa only [one_pow] using (sq_le_sq₀ ha0.le zero_le_one).mpr ha1.le
  have h := det_matrixStep_pos ha hs hs₀ hd hd₀
  rw [matrixStep_eq_step a p c s d hs hd hs₀.le hd₀,
    show 2 * p - 1 = z by dsimp [p]; ring] at h
  let next := step a c z
  change 0 < (qubitState ((1 + next.2) / 2) next.1).det at h
  rw [qubitState, Matrix.det_fin_two_of] at h
  change 0 < blochDet next.1 next.2
  unfold blochDet
  nlinarith only [h]

/-- Positive coherence and a positive determinant persist through each step. -/
theorem step_preserves_open_disk {a c z : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hc : 0 < c) (hdet : 0 < blochDet c z) :
    0 < (step a c z).1 ∧ 0 < blochDet (step a c z).1 (step a c z).2 := by
  refine ⟨?_, step_det_pos ha0 ha1 hc hdet⟩
  have hlower := (step_bounds ha0 ha1 hc hdet).1
  have hmul : 0 < a * (1 - a) * c * blochDet c z := by positivity
  exact add_pos hc (hmul.trans_le hlower)

/-- The first recovered state for an unbiased reference uses two dephasings. -/
theorem dephase_twice (a p c : ℝ) :
    dephase a (dephase a (qubitState p c)) = qubitState p (a ^ 2 * c) := by
  rw [dephase_state, dephase_state, show a * (a * c) = a ^ 2 * c by ring]

/-- A pure input with nonzero coherence enters the open Bloch disk after that step. -/
theorem first_det_pos {a ct z : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hc : 0 < ct) (hpure : 4 * ct ^ 2 + z ^ 2 = 1) :
    0 < blochDet (a ^ 2 * ct) z := by
  have ha20 : 0 < a ^ 2 := by positivity
  have ha21 : a ^ 2 < 1 := by
    simpa only [one_pow] using (sq_lt_sq₀ ha0.le zero_le_one).mpr ha1
  have h := det_lt_dephased (z := z) ha20 ha21 hc
  have hzero : blochDet ct z = 0 := by unfold blochDet; linarith
  simpa only [hzero] using h

/-! ## Coordinate limits -/

private theorem abs_antitone_of_mul {z r : ℕ → ℝ}
    (hz : ∀ n, z (n + 1) = z n * r n) (hr : ∀ n, 0 < r n ∧ r n < 1) :
    Antitone (fun n => |z n|) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [hz, abs_mul, abs_of_pos (hr n).1]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (hr n).2.le (abs_nonneg (z n))

private theorem z_tendsto_of_mul {z r : ℕ → ℝ}
    (hz : ∀ n, z (n + 1) = z n * r n) (hr : ∀ n, 0 < r n ∧ r n < 1) :
    ∃ Z : ℝ, Tendsto z atTop (𝓝 Z) := by
  have habs := abs_antitone_of_mul hz hr
  have hbdd : BddBelow (Set.range (fun n => |z n|)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact abs_nonneg _
  have hlim := tendsto_atTop_ciInf habs hbdd
  by_cases h₀ : 0 ≤ z 0
  · have hsign : ∀ n, 0 ≤ z n := by
      intro n
      induction n with
      | zero => exact h₀
      | succ n ih => rw [hz n]; exact mul_nonneg ih (hr n).1.le
    exact ⟨_, Filter.Tendsto.congr (fun n => abs_of_nonneg (hsign n)) hlim⟩
  · have hsign : ∀ n, z n ≤ 0 := by
      intro n
      induction n with
      | zero => exact le_of_lt (lt_of_not_ge h₀)
      | succ n ih => rw [hz n]; exact mul_nonpos_of_nonpos_of_nonneg ih (hr n).1.le
    exact ⟨_, Filter.Tendsto.congr
      (fun n => by simp only [abs_of_nonpos (hsign n), neg_neg]) hlim.neg⟩

theorem z_strict_drop {z r : ℕ → ℝ}
    (hz : ∀ n, z (n + 1) = z n * r n) (hr : ∀ n, 0 < r n ∧ r n < 1)
    {n₀ : ℕ} (hz₀ : z n₀ ≠ 0) :
    |z (n₀ + 1)| < |z n₀| ∧ ∀ n, n₀ + 1 ≤ n → |z n| ≤ |z (n₀ + 1)| := by
  refine ⟨?_, fun n hn => abs_antitone_of_mul hz hr hn⟩
  rw [hz, abs_mul, abs_of_pos (hr n₀).1]
  simpa only [mul_one] using mul_lt_mul_of_pos_left (hr n₀).2 (abs_pos.mpr hz₀)

/-- An orbit in the open disk converges to the positive-coherence half of the
unit Bloch circle. The first axial decrease persists to the limit. -/
theorem pure_limit {a : ℝ} {c z : ℕ → ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hc0 : 0 < c 0)
    (hstep : ∀ n, (c (n + 1), z (n + 1)) = step a (c n) (z n))
    (hdet0 : 0 < blochDet (c 0) (z 0)) :
    ∃ C Z : ℝ, Tendsto c atTop (𝓝 C) ∧ Tendsto z atTop (𝓝 Z) ∧
      0 < C ∧ 4 * C ^ 2 + Z ^ 2 = 1 ∧
      |Z| ≤ |z 1| ∧ (z 0 ≠ 0 → |z 1| < |z 0|) := by
  let s := fun n => Real.sqrt (blochDet (c n) (z n))
  let d := fun n => Real.sqrt (blochDet (a * c n) (z n))
  let delta := fun n => petzDelta a (c n) (z n) (s n) (d n)
  let r := fun n => petzShrink a (c n) (s n) (d n)
  have hcstep (n : ℕ) : c (n + 1) = c n + delta n := congrArg Prod.fst (hstep n)
  have hzstep (n : ℕ) : z (n + 1) = z n * r n := congrArg Prod.snd (hstep n)
  have ha : 0 < 1 - a := sub_pos.mpr ha1
  have hinc (n : ℕ) (hc : 0 < c n) (hdet : 0 < blochDet (c n) (z n)) :
      0 < delta n :=
    (mul_pos (mul_pos (mul_pos ha0 ha) hc) hdet).trans_le (step_bounds ha0 ha1 hc hdet).1
  have hinterior : ∀ n, 0 < c n ∧ 0 < blochDet (c n) (z n) := by
    intro n
    induction n with
    | zero => exact ⟨hc0, hdet0⟩
    | succ n ih =>
        refine ⟨?_, ?_⟩
        · rw [hcstep n]
          exact add_pos ih.1 (hinc n ih.1 ih.2)
        · have h := step_det_pos ha0 ha1 ih.1 ih.2
          rw [← hstep n] at h
          exact h
  have hcpos (n : ℕ) : 0 < c n := (hinterior n).1
  have hdet (n : ℕ) : 0 < blochDet (c n) (z n) := (hinterior n).2
  have hmono : Monotone c := monotone_nat_of_le_succ fun n => by
    rw [hcstep n]
    linarith only [hinc n (hcpos n) (hdet n)]
  have hbdd : BddAbove (Set.range c) := by
    refine ⟨1 / 2, ?_⟩
    rintro _ ⟨n, rfl⟩
    have h := hdet n
    unfold blochDet at h
    by_contra hn
    have hn' : 1 / 2 < c n := lt_of_not_ge hn
    have hsquare := mul_pos (sub_pos.mpr hn') (show 0 < c n + 1 / 2 by linarith)
    nlinarith only [hsquare, h, sq_nonneg (z n)]
  let C := ⨆ n, c n
  have hc : Tendsto c atTop (𝓝 C) := tendsto_atTop_ciSup hmono hbdd
  have hC : 0 < C := hc0.trans_le (ge_of_tendsto' hc fun n => hmono (Nat.zero_le n))
  have hr (n : ℕ) : 0 < r n ∧ r n < 1 := (step_bounds ha0 ha1 (hcpos n) (hdet n)).2
  obtain ⟨Z, hz⟩ := z_tendsto_of_mul hzstep hr
  have hshift : Tendsto (fun n => c (n + 1)) atTop (𝓝 C) :=
    hc.comp (tendsto_add_atTop_nat 1)
  have hdelta : Tendsto delta atTop (𝓝 0) := by
    have hEq (n : ℕ) : c (n + 1) - c n = delta n := by
      rw [hcstep n, add_sub_cancel_left]
    simpa only [sub_self] using Filter.Tendsto.congr hEq (hshift.sub hc)
  have hdetlim : Tendsto (fun n => blochDet (c n) (z n)) atTop (𝓝 (blochDet C Z)) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    exact ((hone.sub (hz.pow 2)).div_const 4).sub (hc.pow 2)
  let K := a * (1 - a) * c 0
  have hK : 0 < K := by dsimp [K]; positivity
  have hupper : K * blochDet C Z ≤ 0 :=
    le_of_tendsto_of_tendsto' (hdetlim.const_mul K) hdelta fun n => by
      refine le_trans ?_ ((step_bounds ha0 ha1 (hcpos n) (hdet n)).1)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hmono (Nat.zero_le n)) (by positivity)) (hdet n).le
  have hzero : blochDet C Z = 0 := by
    refine le_antisymm ?_ (ge_of_tendsto' hdetlim fun n => (hdet n).le)
    by_contra h
    exact (not_lt_of_ge hupper) (mul_pos hK (lt_of_not_ge h))
  have hZ : |Z| ≤ |z 1| := by
    apply le_of_tendsto hz.abs
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact abs_antitone_of_mul hzstep hr hn
  refine ⟨C, Z, hc, hz, hC, ?_, hZ, ?_⟩
  · unfold blochDet at hzero
    linarith
  · intro h
    exact (z_strict_drop hzstep hr h).1

/-- A persistent axial gap yields a fidelity deficit against a pure target. -/
def blochFidelity (ct zt c z : ℝ) : ℝ := (1 + 4 * ct * c + zt * z) / 2

theorem blochFidelity_le_of_gap {ct zt c z g : ℝ}
    (htarget : 4 * ct ^ 2 + zt ^ 2 = 1) (hstate : 4 * c ^ 2 + z ^ 2 ≤ 1)
    (hg : 0 ≤ g) (hgap : g ≤ |zt| - |z|) :
    blochFidelity ct zt c z ≤ 1 - g ^ 2 / 4 := by
  have habs : g ≤ |zt - z| := hgap.trans (abs_sub_abs_le_abs_sub _ _)
  have hsq : g ^ 2 ≤ (zt - z) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ hg (abs_nonneg _)).mpr habs
  unfold blochFidelity
  nlinarith only [htarget, hstate, hsq, sq_nonneg (2 * ct - 2 * c)]

/-- Index zero is the first recovered state. The gap at index one persists
at the pure limit and vanishes at the equator. -/
theorem pure_target_limit {a ct zt : ℝ} {c z : ℕ → ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hct : 0 < ct)
    (htarget : 4 * ct ^ 2 + zt ^ 2 = 1)
    (hc0 : c 0 = a ^ 2 * ct) (hz0 : z 0 = zt)
    (hstep : ∀ n, (c (n + 1), z (n + 1)) = step a (c n) (z n)) :
    ∃ C Z : ℝ, Tendsto c atTop (𝓝 C) ∧ Tendsto z atTop (𝓝 Z) ∧
      4 * C ^ 2 + Z ^ 2 = 1 ∧
      (zt ≠ 0 → 0 < |zt| - |z 1| ∧ |Z| < |zt| ∧
        blochFidelity ct zt C Z ≤ 1 - (|zt| - |z 1|) ^ 2 / 4) ∧
      (zt = 0 → C = ct ∧ Z = zt) := by
  have hcpos : 0 < c 0 := by rw [hc0]; positivity
  have hdet : 0 < blochDet (c 0) (z 0) := by
    rw [hc0, hz0]
    exact first_det_pos ha0 ha1 hct htarget
  obtain ⟨C, Z, hc, hz, hC, hcircle, hbound, hdrop⟩ :=
    pure_limit ha0 ha1 hcpos hstep hdet
  refine ⟨C, Z, hc, hz, hcircle, ?_, ?_⟩
  · intro hzt
    have hdrop' : |z 1| < |zt| := by
      rw [← hz0]
      exact hdrop (by simpa only [hz0] using hzt)
    refine ⟨sub_pos.mpr hdrop', hbound.trans_lt hdrop', ?_⟩
    exact blochFidelity_le_of_gap htarget hcircle.le
      (sub_nonneg.mpr hdrop'.le) (sub_le_sub_left hbound _)
  · intro heq
    have hzall (n : ℕ) : z n = 0 := by
      induction n with
      | zero => exact hz0.trans heq
      | succ n ih =>
          have h := congrArg Prod.snd (hstep n)
          change z (n + 1) = z n * _ at h
          simpa only [ih, zero_mul] using h
    have hZ : Z = 0 := tendsto_nhds_unique hz
      (Filter.Tendsto.congr (fun n => (hzall n).symm) tendsto_const_nhds)
    refine ⟨?_, hZ.trans heq.symm⟩
    have hsquare : C ^ 2 = ct ^ 2 := by nlinarith only [hcircle, htarget, hZ, heq]
    have hprod : (C - ct) * (C + ct) = 0 := by nlinarith only [hsquare]
    rcases mul_eq_zero.mp hprod with h | h
    · exact sub_eq_zero.mp h
    · linarith only [h, hC, hct]

/-- The polar inputs are fixed under the paper's stopping convention.
The coordinate formula also evaluates to the same pair there. -/
theorem step_pole (a z : ℝ) (hz : z ^ 2 = 1) : step a 0 z = (0, z) := by
  simp [step, blochDet, hz, petzStep, petzDelta, petzShrink, petzL]

section PrincipalRoots

open scoped MatrixOrder Matrix.Norms.L2Operator

private theorem symmetric_nonneg {p c q : ℝ} (hp : 0 < p) (hdet : 0 ≤ p * q - c ^ 2) :
    0 ≤ (!![p, c; c, q] : QubitMatrix) := by
  let R : QubitMatrix := !![Real.sqrt p, 0; c / Real.sqrt p, Real.sqrt (q - c ^ 2 / p)]
  have hp' := (Real.sqrt_pos.mpr hp).ne'
  have hq : 0 ≤ q - c ^ 2 / p := sub_nonneg.mpr
    ((div_le_iff₀ hp).2 (by linarith))
  have hroot : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp.le
  have hres : Real.sqrt (q - c ^ 2 / p) * Real.sqrt (q - c ^ 2 / p) =
      q - c ^ 2 / p := Real.mul_self_sqrt hq
  have hfactor : (!![p, c; c, q] : QubitMatrix) = R * Rᴴ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [R, Matrix.mul_apply, Fin.sum_univ_two, hroot, hres]
    · field_simp
    · field_simp
    · rw [← sq, div_pow, Real.sq_sqrt hp.le]
      ring
  rw [hfactor]
  exact (Matrix.posSemidef_self_mul_conjTranspose R).nonneg

theorem principal_root_eq (p c s : ℝ) (hs : s ^ 2 = p * (1 - p) - c ^ 2)
    (hs₀ : 0 < s) : CFC.sqrt (qubitState p c) = qubitRoot p c s := by
  have hd : 0 < p * (1 - p) := by nlinarith [sq_pos_of_pos hs₀, sq_nonneg c]
  have hp : 0 < p := by
    by_contra! h
    exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg h (by linarith))) hd
  refine CFC.sqrt_unique (qubitRoot_mul_self p c s hs hs₀.le) ?_
  have hr : 0 ≤ rootNumerator p c s := by
    apply symmetric_nonneg (by positivity)
    have hproduct : 0 ≤ s * (1 + 2 * s) := by positivity
    nlinarith only [hs, hproduct]
  exact ((Matrix.nonneg_iff_posSemidef.mp hr).smul
    (show 0 ≤ (Real.sqrt (1 + 2 * s))⁻¹ by positivity)).nonneg

/-- The phase-aligned Petz update uses the principal root and the inverse
of the principal dephased root. The dephasing map is its own adjoint. -/
theorem matrixStep_eq_principal_petz (a p c s d : ℝ)
    (hs : s ^ 2 = p * (1 - p) - c ^ 2)
    (hd : d ^ 2 = p * (1 - p) - (a * c) ^ 2) (hs₀ : 0 < s) (hd₀ : 0 < d) :
    matrixStep a p c s d =
      let S := CFC.sqrt (qubitState p c)
      let M := (CFC.sqrt (dephase a (qubitState p c)))⁻¹
      S * dephase a (M * qubitState p c * M) * S := by
  rw [matrixStep_eq_root_product a p c s d hs₀.le hd₀.le]
  simp only [dephase_state, principal_root_eq p c s hs hs₀,
    principal_root_eq p (a * c) d hd hd₀]
  rw [Matrix.inv_eq_left_inv (qubitInverseRoot_mul_root a p c d hd hd₀)]

end PrincipalRoots

#print axioms matrixStep_eq_principal_petz
#print axioms pure_target_limit

end D5.S3.Quantum.Recovery.IterativePetz.IterativePetzDephasing
