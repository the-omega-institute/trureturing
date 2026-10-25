import Batteries.Tactic.OpenPrivate
import D5.S3.Quantum.Information.PauliRotationCriticalValues
import D5.S3.Geometry.Hyperideal.LengthGramBody
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
open D5.S3.Quantum.Information.PauliRotationCriticalValues

open private detForm detDiff detForm_deriv from
  D5.S3.Quantum.Information.PauliRotationCriticalValues

namespace CFMPFrameMotion435Transient

theorem detDiff_left_rate {n : Type*} [Fintype n] [DecidableEq n]
    (M K : Matrix n n ℝ) : detDiff M (K * M) = M.det * K.trace := by
  simp -implicitDefEqProofs only [detForm_deriv]
  have row (i : n) : (K * M) i = ∑ k, K i k • M k := by
    ext j
    simp [Matrix.mul_apply, Finset.sum_apply, smul_eq_mul]
  have term (i : n) :
      Matrix.det (Matrix.of (Function.update M i ((K * M) i))) = K i i * M.det := by
    change (M.updateRow i ((K * M) i)).det = _
    rw [row, Matrix.det_updateRow_sum]
    rfl
  simp_rw [term]
  rw [← Finset.sum_mul]
  simp [Matrix.trace, Matrix.diag_apply, mul_comm]

theorem frame_absolute_det_derivative {n : Type*} [Fintype n] [DecidableEq n]
    (M : ℝ → Matrix n n ℝ) (D : Matrix n n ℝ) (t : ℝ)
    (hM : HasDerivAt M D t) (hd : (M t).det ≠ 0) :
    HasDerivAt (fun s => |(M s).det|)
      (|(M t).det| * (D * (M t)⁻¹).trace) t := by
  let K := D * (M t)⁻¹
  have hKM : K * M t = D := by
    dsimp [K]
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd),
      Matrix.mul_one]
  have hdet : HasDerivAt (fun s => (M s).det)
      ((M t).det * K.trace) t := by
    have h := ((detForm (n := n)).1.hasFDerivAt (M t)).comp_hasDerivAt t hM
    change HasDerivAt (fun s => (M s).det) (detDiff (M t) D) t at h
    rw [← hKM, detDiff_left_rate] at h
    exact h
  rcases lt_or_gt_of_ne hd with hn | hp
  · have h := (hasDerivAt_abs_neg hn).comp t hdet
    simpa -implicitDefEqProofs [abs_of_neg hn, K, Function.comp_def] using h
  · have h := (hasDerivAt_abs_pos hp).comp t hdet
    simpa -implicitDefEqProofs [abs_of_pos hp, K, Function.comp_def] using h

abbrev V := Fin 3 → ℝ
abbrev W := Fin 4 → ℝ
abbrev M4 := Matrix (Fin 4) (Fin 4) ℝ

def lift (x : V) : W := ![x 0, x 1, x 2, 1 - x 0 - x 1 - x 2]
def rowSum (K : M4) (i : Fin 4) : ℝ := ∑ j, K i j
def alpha (K : M4) (x : V) : ℝ := ∑ i, lift x i * rowSum K i
def field (K : M4) (x : V) (i : Fin 3) : ℝ :=
  (∑ j, lift x j * K j i.castSucc) - alpha K x * x i
def basis (i : Fin 3) : V := Pi.single i 1
def divergence (F : V → V) (x : V) : ℝ :=
  ∑ i, deriv (fun s : ℝ => F (x + s • basis i) i) 0

theorem alpha_line (K : M4) (x : V) (i : Fin 3) (s : ℝ) :
    alpha K (x + s • basis i) =
      alpha K x + s * (rowSum K i.castSucc - rowSum K 3) := by
  fin_cases i <;>
    simp [alpha, lift, basis, Fin.sum_univ_four] <;> ring

theorem linear_row_line (K : M4) (x : V) (i : Fin 3) (s : ℝ) :
    (∑ j, lift (x + s • basis i) j * K j i.castSucc) =
      (∑ j, lift x j * K j i.castSucc) +
        s * (K i.castSucc i.castSucc - K 3 i.castSucc) := by
  fin_cases i <;>
    simp [lift, basis, Fin.sum_univ_four] <;> ring

theorem field_coordinate_derivative (K : M4) (x : V) (i : Fin 3) :
    HasDerivAt (fun s : ℝ => field K (x + s • basis i) i)
      (K i.castSucc i.castSucc - K 3 i.castSucc -
        (rowSum K i.castSucc - rowSum K 3) * x i - alpha K x) 0 := by
  have ha : HasDerivAt
      (fun s : ℝ => alpha K x + s * (rowSum K i.castSucc - rowSum K 3))
      (rowSum K i.castSucc - rowSum K 3) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const
      (rowSum K i.castSucc - rowSum K 3)).const_add (alpha K x)
  have hr : HasDerivAt
      (fun s : ℝ => (∑ j, lift x j * K j i.castSucc) +
        s * (K i.castSucc i.castSucc - K 3 i.castSucc))
      (K i.castSucc i.castSucc - K 3 i.castSucc) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const
      (K i.castSucc i.castSucc - K 3 i.castSucc)).const_add
        (∑ j, lift x j * K j i.castSucc)
  have hx : HasDerivAt (fun s : ℝ => x i + s) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add (x i)
  convert hr.sub (ha.mul hx) using 1
  · funext s
    simp only [field]
    rw [alpha_line, linear_row_line]
    simp [basis]
  · simp
    ring

theorem projective_divergence (K : M4) (x : V) :
    divergence (field K) x = K.trace - 4 * alpha K x := by
  unfold divergence
  simp_rw [(field_coordinate_derivative K x _).deriv]
  simp [Fin.sum_univ_three, Fin.sum_univ_four, Matrix.trace, Matrix.diag_apply,
    alpha, lift, rowSum]
  ring

#print axioms frame_absolute_det_derivative
#print axioms projective_divergence
end CFMPFrameMotion435Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPFrameMotion435Transient.detDiff_left_rate,
      ``CFMPFrameMotion435Transient.frame_absolute_det_derivative,
      ``CFMPFrameMotion435Transient.projective_divergence] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP574 declaration absent from checked environment: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP574 disallowed axiom {ax} for {name}"
    Lean.logInfo m!"CFMP574 CHECKED {name} axioms={axioms}"
