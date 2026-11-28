/- GID: D5/S3/Quantum/Gauge/CKMFlavorJarlskog4D
   generality: G
   mirror-B: D5/B/S3/Quantum/Gauge/CKMFlavorJarlskog4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cabibbo rephasing, flavor counts, and the Jarlskog invariant. -/

import OmegaBuild.Commands
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Flavor mixing with independent row and column phases. The quartet convention uses
the entries at the north-west and south-east corners without complex conjugation. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Complex
open scoped BigOperators ComplexConjugate

namespace D5.S3.Quantum.Gauge.CKMFlavorJarlskog4D

def unitaryParamCount (N : ℕ) : ℕ := N ^ 2
def orthogonalAngleCount (N : ℕ) : ℕ := N * (N - 1) / 2
def relativePhaseCount (N : ℕ) : ℕ := 2 * N - 1
def physicalPhaseCount (N : ℕ) : ℕ := (N - 1) * (N - 2) / 2

theorem ckm_physical_parameter_square (N : ℕ) (hN : 1 ≤ N) :
    unitaryParamCount N - relativePhaseCount N = (N - 1) ^ 2 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  change (n + 1) ^ 2 - (2 * (n + 1) - 1) = (n + 1 - 1) ^ 2
  rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega,
    show (n + 1) ^ 2 = n ^ 2 + (2 * n + 1) by ring]
  simp

theorem ckm_parameter_decomp (N : ℕ) (hN : 1 ≤ N) :
    orthogonalAngleCount N + physicalPhaseCount N =
      unitaryParamCount N - relativePhaseCount N := by
  rw [ckm_physical_parameter_square N hN]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  unfold orthogonalAngleCount physicalPhaseCount
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  rw [show n + 1 - 2 = n - 1 by omega]
  have ha := Nat.div_mul_cancel (n + 1).two_dvd_mul_sub_one
  have hp := Nat.div_mul_cancel n.two_dvd_mul_sub_one
  simp only [Nat.add_sub_cancel] at ha
  have hsum : (n + 1) * n + n * (n - 1) = n ^ 2 * 2 := by
    cases n
    · simp
    · simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
      ring
  omega

theorem cp_phase_pos_iff_three_generations (N : ℕ) :
    0 < physicalPhaseCount N ↔ 3 ≤ N := by
  unfold physicalPhaseCount
  constructor
  · intro h
    by_contra hn
    interval_cases N <;> norm_num at h
  · intro h
    have hprod : 2 * 1 ≤ (N - 1) * (N - 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega

theorem ckm_small_generation_counts :
    (orthogonalAngleCount 1, physicalPhaseCount 1) = (0, 0) ∧
    (orthogonalAngleCount 2, physicalPhaseCount 2) = (1, 0) ∧
    (orthogonalAngleCount 3, physicalPhaseCount 3) = (3, 1) := by
  decide

private def phase (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * I)

private theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  simp only [phase, ofReal_add, add_mul, exp_add]

private theorem phase_zero : phase 0 = 1 := by simp [phase]

private theorem phase_mul_neg (x : ℝ) : phase x * phase (-x) = 1 := by
  rw [← phase_add, add_neg_cancel, phase_zero]

private theorem conj_phase (x : ℝ) : conj (phase x) = phase (-x) := by
  simp [phase, ← Complex.exp_conj, map_mul, neg_mul, mul_neg]

private theorem remove_arg (z : ℂ) : z * phase (-arg z) = (‖z‖ : ℂ) := by
  calc
    z * phase (-arg z) = (‖z‖ : ℂ) * phase (arg z) * phase (-arg z) := by
      exact congrArg (fun w : ℂ => w * phase (-arg z))
        (Complex.norm_mul_exp_arg_mul_I z).symm
    _ = _ := by rw [mul_assoc, phase_mul_neg, mul_one]

/-- Independent phases multiply the rows on the left and the columns on the right. -/
def rephase {N : ℕ} (α β : Fin N → ℝ) (V : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => phase (α i) * V i j * phase (-β j)

private theorem rephase_eq_diagonal {N : ℕ} (α β : Fin N → ℝ)
    (V : Matrix (Fin N) (Fin N) ℂ) :
    rephase α β V = Matrix.diagonal (fun i => phase (α i)) * V *
      (Matrix.diagonal (fun j => phase (β j)))ᴴ := by
  ext i j
  rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp [rephase, conj_phase]

private theorem phaseDiagonal_unitary {N : ℕ} (α : Fin N → ℝ) :
    (Matrix.diagonal (fun i => phase (α i)))ᴴ * Matrix.diagonal (fun i => phase (α i)) = 1 := by
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  simp [conj_phase, ← phase_add, phase_zero]

private theorem unitary_mul {N : ℕ} {A B : Matrix (Fin N) (Fin N) ℂ}
    (hA : Aᴴ * A = 1) (hB : Bᴴ * B = 1) : (A * B)ᴴ * (A * B) = 1 := by
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, hA, one_mul, hB]

private theorem rephase_unitary {N : ℕ} (α β : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : Vᴴ * V = 1) :
    (rephase α β V)ᴴ * rephase α β V = 1 := by
  rw [rephase_eq_diagonal]
  apply unitary_mul (unitary_mul (phaseDiagonal_unitary α) hV)
  rw [Matrix.conjTranspose_conjTranspose]
  exact mul_eq_one_comm.mp (phaseDiagonal_unitary β)

def jarlskogQuartet {N : ℕ} (V : Matrix (Fin N) (Fin N) ℂ) (i j k l : Fin N) : ℝ :=
  (V i j * V k l * conj (V i l) * conj (V k j)).im

theorem jarlskogQuartet_rephase_invariant {N : ℕ} (α β : Fin N → ℝ)
    (V : Matrix (Fin N) (Fin N) ℂ) (i j k l : Fin N) :
    jarlskogQuartet (rephase α β V) i j k l = jarlskogQuartet V i j k l := by
  unfold jarlskogQuartet rephase
  simp only [Matrix.of_apply, map_mul, conj_phase, neg_neg]
  congr 1
  calc
    _ = (V i j * V k l * conj (V i l) * conj (V k j)) *
        ((phase (α i) * phase (-α i)) * (phase (α k) * phase (-α k)) *
        (phase (β j) * phase (-β j)) * (phase (β l) * phase (-β l))) := by ring
    _ = _ := by simp only [phase_mul_neg, mul_one]

private theorem first_row_su_two {V : Matrix (Fin 2) (Fin 2) ℂ}
    (hV : Vᴴ * V = 1) (hdet : V.det = 1) :
    V 1 0 = -conj (V 0 1) ∧ V 1 1 = conj (V 0 0) := by
  let adj : Matrix (Fin 2) (Fin 2) ℂ := !![V 1 1, -V 0 1; -V 1 0, V 0 0]
  have hAdj : adj * V = 1 := by
    rw [Matrix.det_fin_two] at hdet
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [adj, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | (ring; done) | linear_combination hdet
  have heq : adj = Vᴴ := by
    calc
      adj = adj * (V * Vᴴ) := by rw [mul_eq_one_comm.mp hV, mul_one]
      _ = Vᴴ := by rw [← Matrix.mul_assoc, hAdj, one_mul]
  constructor
  · have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) heq
    simpa [adj, Matrix.conjTranspose_apply, Complex.star_def] using congrArg Neg.neg h
  · simpa [adj, Matrix.conjTranspose_apply, Complex.star_def] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) heq

private def cabibboRotation (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![↑(Real.cos θ), ↑(Real.sin θ); -↑(Real.sin θ), ↑(Real.cos θ)]

/-- The arguments of the first row remove its phases. The determinant fixes the
remaining row phase, including when either entry in the first row vanishes. -/
theorem u2_rephasing_to_real_rotation (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : Uᴴ * U = 1) :
    ∃ (α β : Fin 2 → ℝ) (θ : ℝ),
      Matrix.diagonal (fun i => Complex.exp (α i * I)) * U *
        (Matrix.diagonal (fun j => Complex.exp (β j * I)))ᴴ =
          !![↑(Real.cos θ), ↑(Real.sin θ); -↑(Real.sin θ), ↑(Real.cos θ)] := by
  let β : Fin 2 → ℝ := fun j => arg (U 0 j)
  let α : Fin 2 → ℝ := ![0, β 0 + β 1 - arg U.det]
  let V := rephase α β U
  have hV : Vᴴ * V = 1 := rephase_unitary α β hU
  have hnorm : ‖U.det‖ = 1 := by
    have h := congrArg Matrix.det hU
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one, Complex.star_def,
      Complex.conj_mul'] at h
    have hsq : ‖U.det‖ ^ 2 = 1 := by exact_mod_cast h
    nlinarith [norm_nonneg U.det]
  have hdet : V.det = 1 := by
    dsimp [V]
    rw [rephase_eq_diagonal, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose,
      Matrix.det_diagonal, Matrix.det_diagonal, Fin.prod_univ_two, Fin.prod_univ_two]
    change (phase 0 * phase (β 0 + β 1 - arg U.det)) * U.det *
      conj (phase (β 0) * phase (β 1)) = 1
    rw [phase_zero, one_mul, ← phase_add, conj_phase, sub_eq_add_neg, phase_add]
    calc
      _ = (U.det * phase (-arg U.det)) *
        (phase (β 0 + β 1) * phase (-(β 0 + β 1))) := by ring
      _ = _ := by rw [remove_arg, hnorm, ofReal_one, phase_mul_neg, mul_one]
  have htop (j : Fin 2) : V 0 j = (‖U 0 j‖ : ℂ) := by
    change phase 0 * U 0 j * phase (-arg (U 0 j)) = _
    rw [phase_zero, one_mul, remove_arg]
  have hrow : ‖U 0 0‖ ^ 2 + ‖U 0 1‖ ^ 2 = 1 := by
    have heq := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0)
      (mul_eq_one_comm.mp hU)
    have hcomplex : ((‖U 0 0‖ : ℂ) ^ 2 + (‖U 0 1‖ : ℂ) ^ 2) = 1 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
        Complex.star_def, Complex.mul_conj'] using heq
    exact_mod_cast hcomplex
  let θ := Real.arcsin ‖U 0 1‖
  have hb : ‖U 0 1‖ ≤ 1 := by nlinarith [sq_nonneg ‖U 0 0‖]
  have hs : Real.sin θ = ‖U 0 1‖ :=
    Real.sin_arcsin ((by norm_num : (-1 : ℝ) ≤ 0).trans (norm_nonneg _)) hb
  have hc : Real.cos θ = ‖U 0 0‖ := by
    rw [show θ = Real.arcsin ‖U 0 1‖ from rfl, Real.cos_arcsin,
      show 1 - ‖U 0 1‖ ^ 2 = ‖U 0 0‖ ^ 2 by linarith,
      Real.sqrt_sq (norm_nonneg _)]
  obtain ⟨h10, h11⟩ := first_row_su_two hV hdet
  change V 1 0 = -conj (V 0 1) at h10
  change V 1 1 = conj (V 0 0) at h11
  rw [htop] at h10 h11
  refine ⟨α, β, θ, ?_⟩
  change Matrix.diagonal (fun i => phase (α i)) * U *
    (Matrix.diagonal (fun j => phase (β j)))ᴴ = cabibboRotation θ
  rw [← rephase_eq_diagonal]
  change V = cabibboRotation θ
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cabibboRotation, htop, hc, hs, h10, h11]

theorem u2_jarlskog_zero (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : Uᴴ * U = 1)
    (i j k l : Fin 2) : jarlskogQuartet U i j k l = 0 := by
  obtain ⟨α, β, θ, h⟩ := u2_rephasing_to_real_rotation U hU
  change Matrix.diagonal (fun i => phase (α i)) * U *
    (Matrix.diagonal (fun j => phase (β j)))ᴴ = cabibboRotation θ at h
  rw [← rephase_eq_diagonal] at h
  rw [← jarlskogQuartet_rephase_invariant α β U, h]
  have hreal (a b : Fin 2) : (cabibboRotation θ a b).im = 0 := by
    fin_cases a <;> fin_cases b <;> simp [cabibboRotation]
  simp [jarlskogQuartet, Complex.mul_im, Complex.conj_im, hreal]

def rot23 (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 0; 0, ↑(Real.cos θ), ↑(Real.sin θ); 0, -↑(Real.sin θ), ↑(Real.cos θ)]

def rot13 (θ δ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![↑(Real.cos θ), 0, ↑(Real.sin θ) * phase (-δ); 0, 1, 0;
    -↑(Real.sin θ) * phase δ, 0, ↑(Real.cos θ)]

def rot12 (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![↑(Real.cos θ), ↑(Real.sin θ), 0; -↑(Real.sin θ), ↑(Real.cos θ), 0; 0, 0, 1]

def ckmStandard (θ₁₂ θ₂₃ θ₁₃ δ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  rot23 θ₂₃ * rot13 θ₁₃ δ * rot12 θ₁₂

private theorem trig_unit (θ : ℝ) :
    (Real.cos θ : ℂ) * Real.cos θ + (Real.sin θ : ℂ) * Real.sin θ = 1 := by
  exact_mod_cast (by simpa [pow_two, add_comm] using Real.sin_sq_add_cos_sq θ :
    Real.cos θ * Real.cos θ + Real.sin θ * Real.sin θ = 1)

private theorem rot23_su (θ : ℝ) : (rot23 θ)ᴴ * rot23 θ = 1 ∧ (rot23 θ).det = 1 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [rot23, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.conjTranspose_apply, trig_unit, -Complex.ofReal_cos, -Complex.ofReal_sin,
      add_comm, mul_comm]
  · simp [Matrix.det_fin_three, rot23, sub_neg_eq_add, trig_unit, -ofReal_cos, -ofReal_sin]

private theorem rot12_su (θ : ℝ) : (rot12 θ)ᴴ * rot12 θ = 1 ∧ (rot12 θ).det = 1 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [rot12, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.conjTranspose_apply, trig_unit, -Complex.ofReal_cos, -Complex.ofReal_sin,
      add_comm, mul_comm]
  · simp [Matrix.det_fin_three, rot12, sub_neg_eq_add, trig_unit, -ofReal_cos, -ofReal_sin]

private theorem rot13_su (θ δ : ℝ) : (rot13 θ δ)ᴴ * rot13 θ δ = 1 ∧ (rot13 θ δ).det = 1 := by
  have hphase : phase (-δ) * phase δ = 1 := by simpa using phase_mul_neg (-δ)
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [rot13, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.conjTranspose_apply, conj_phase, -Complex.ofReal_cos, -Complex.ofReal_sin,
      mul_mul_mul_comm, hphase, phase_mul_neg, trig_unit, add_comm] <;> ring
  · simp [Matrix.det_fin_three, rot13, mul_mul_mul_comm, hphase, trig_unit,
      -ofReal_cos, -ofReal_sin, sub_neg_eq_add]

theorem ckmStandard_unitary (θ₁₂ θ₂₃ θ₁₃ δ : ℝ) :
    (ckmStandard θ₁₂ θ₂₃ θ₁₃ δ)ᴴ * ckmStandard θ₁₂ θ₂₃ θ₁₃ δ = 1 ∧
    (ckmStandard θ₁₂ θ₂₃ θ₁₃ δ).det = 1 := by
  constructor
  · exact unitary_mul (unitary_mul (rot23_su θ₂₃).1 (rot13_su θ₁₃ δ).1) (rot12_su θ₁₂).1
  · simp [ckmStandard, Matrix.det_mul, (rot23_su θ₂₃).2, (rot13_su θ₁₃ δ).2, (rot12_su θ₁₂).2]

/-- The orientation of an ordered pair in the cyclic ordering of three indices. -/
def leviSign (i k : Fin 3) : ℝ :=
  if i = k then 0 else if k = i + 1 then 1 else -1

private def cross (z w : ℂ) : ℝ := (z * conj w).im

private theorem cross_swap (z w : ℂ) : cross w z = -cross z w := by
  simp [cross, Complex.mul_im]
  ring

private theorem cross_self (z : ℂ) : cross z z = 0 := by
  simp [cross, Complex.mul_im, mul_comm]

private theorem cross_add (z v w : ℂ) : cross (z + v) w = cross z w + cross v w := by
  simp [cross, add_mul]

private theorem cross_of_triangle (z : Fin 3 → ℂ) (hz : z 0 + z 1 + z 2 = 0)
    (i k : Fin 3) : cross (z i) (z k) = leviSign i k * cross (z 0) (z 1) := by
  have hzero (a : Fin 3) : cross (z 0) (z a) + cross (z 1) (z a) + cross (z 2) (z a) = 0 := by
    rw [← cross_add, ← cross_add, hz]
    simp [cross]
  have h02 : cross (z 0) (z 2) = -cross (z 0) (z 1) := by
    have h := hzero 0
    rw [cross_self, cross_swap (z 0) (z 1), cross_swap (z 0) (z 2)] at h
    linarith
  have h12 : cross (z 1) (z 2) = cross (z 0) (z 1) := by
    have h := hzero 2
    rw [cross_self, h02] at h
    linarith
  have h10 := cross_swap (z 0) (z 1)
  have h20 := cross_swap (z 0) (z 2)
  have h21 := cross_swap (z 1) (z 2)
  fin_cases i <;> fin_cases k <;>
    norm_num [leviSign, cross_self, h02, h12, h10, h20, h21]

private theorem quartet_rows {N : ℕ} (V : Matrix (Fin N) (Fin N) ℂ)
    (i j k l : Fin N) :
    jarlskogQuartet V i j k l = cross (V i j * conj (V k j)) (V i l * conj (V k l)) := by
  unfold jarlskogQuartet cross
  simp only [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
  congr 1
  ring

private theorem quartet_columns {N : ℕ} (V : Matrix (Fin N) (Fin N) ℂ)
    (i j k l : Fin N) :
    jarlskogQuartet V i j k l = cross (V i j * conj (V i l)) (V k j * conj (V k l)) := by
  unfold jarlskogQuartet cross
  simp only [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
  congr 1
  ring

private theorem row_triangle (V : Matrix (Fin 3) (Fin 3) ℂ) (hV : V * Vᴴ = 1)
    {i k : Fin 3} (hik : i ≠ k) :
    V i 0 * conj (V k 0) + V i 1 * conj (V k 1) + V i 2 * conj (V k 2) = 0 := by
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def, Fin.sum_univ_three,
    Matrix.one_apply, hik, add_assoc] using
    congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M i k) hV

private theorem column_triangle (V : Matrix (Fin 3) (Fin 3) ℂ) (hV : Vᴴ * V = 1)
    {j l : Fin 3} (hjl : j ≠ l) :
    V 0 j * conj (V 0 l) + V 1 j * conj (V 1 l) + V 2 j * conj (V 2 l) = 0 := by
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def, Fin.sum_univ_three,
    Matrix.one_apply, Ne.symm hjl, add_assoc, mul_comm] using
    congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M l j) hV

theorem jarlskogQuartet_unitary_universal (V : Matrix (Fin 3) (Fin 3) ℂ)
    (hV : Vᴴ * V = 1) (i j k l : Fin 3) :
    jarlskogQuartet V i j k l =
      (leviSign i k * leviSign j l) * jarlskogQuartet V 0 0 1 1 := by
  by_cases hik : i = k
  · subst k
    simp [quartet_columns, cross_self, leviSign]
  have hr := cross_of_triangle (fun m => V i m * conj (V k m))
    (row_triangle V (mul_eq_one_comm.mp hV) hik) j l
  have hc := cross_of_triangle (fun m => V m 0 * conj (V m 1))
    (column_triangle V hV (by decide : (0 : Fin 3) ≠ 1)) i k
  change cross _ _ = _ * cross _ _ at hr hc
  rw [← quartet_rows, ← quartet_rows] at hr
  rw [← quartet_columns, ← quartet_columns] at hc
  rw [hr, hc]
  ring

theorem jarlskog_ckmStandard_formula (θ₁₂ θ₂₃ θ₁₃ δ : ℝ) :
    jarlskogQuartet (ckmStandard θ₁₂ θ₂₃ θ₁₃ δ) 0 0 1 1 =
      Real.cos θ₁₂ * Real.cos θ₁₃ ^ 2 * Real.cos θ₂₃ *
        Real.sin θ₁₂ * Real.sin θ₁₃ * Real.sin θ₂₃ * Real.sin δ := by
  simp [jarlskogQuartet, ckmStandard, Matrix.mul_apply, Fin.sum_univ_three,
    rot12, rot13, rot23, phase, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im]
  linear_combination
    (Real.cos θ₁₂ * Real.cos θ₁₃ ^ 2 * Real.cos θ₂₃ *
      Real.sin θ₁₂ * Real.sin θ₁₃ * Real.sin θ₂₃ * Real.sin δ) *
      Real.sin_sq_add_cos_sq θ₁₂

theorem jarlskog_zero_iff_no_cp (θ₁₂ θ₂₃ θ₁₃ δ : ℝ) :
    jarlskogQuartet (ckmStandard θ₁₂ θ₂₃ θ₁₃ δ) 0 0 1 1 = 0 ↔
      Real.sin (2 * θ₁₂) = 0 ∨ Real.sin (2 * θ₂₃) = 0 ∨
      Real.sin θ₁₃ = 0 ∨ Real.cos θ₁₃ = 0 ∨ Real.sin δ = 0 := by
  rw [jarlskog_ckmStandard_formula, Real.sin_two_mul, Real.sin_two_mul]
  simp only [mul_eq_zero, pow_eq_zero_iff (by decide : 2 ≠ 0), two_ne_zero, false_or]
  tauto

private theorem abs_cos_mul_sin_le (θ : ℝ) :
    |Real.cos θ * Real.sin θ| ≤ 1 / 2 := by
  have h : |2 * (Real.cos θ * Real.sin θ)| ≤ 1 := by
    have heq : 2 * (Real.cos θ * Real.sin θ) = Real.sin (2 * θ) := by
      rw [Real.sin_two_mul]
      ring
    rw [heq]
    exact Real.abs_sin_le_one _
  rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))] at h
  linarith

private theorem abs_sin_mul_cos_sq_le (θ : ℝ) :
    |Real.sin θ| * Real.cos θ ^ 2 ≤ 2 / (3 * Real.sqrt 3) := by
  have hsqrt : 0 < Real.sqrt 3 := by positivity
  have hsqrt_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have htrig := Real.sin_sq_add_cos_sq θ
  let x := Real.sin θ ^ 2
  have hx : x ≤ 1 := by
    dsimp [x]
    linarith [sq_nonneg (Real.cos θ)]
  have hgap : 0 ≤ (x - 1/3) ^ 2 * (4/3 - x) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have hpoly : x * (1 - x) ^ 2 ≤ 4/27 := by nlinarith only [hgap]
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, sq_abs, show Real.cos θ ^ 2 = 1 - x by linarith]
  calc
    _ ≤ 4/27 := hpoly
    _ = (2 / (3 * Real.sqrt 3)) ^ 2 := by
      rw [div_pow, mul_pow, hsqrt_sq]
      norm_num

theorem jarlskog_sharp_upper_bound (θ₁₂ θ₂₃ θ₁₃ δ : ℝ) :
    |jarlskogQuartet (ckmStandard θ₁₂ θ₂₃ θ₁₃ δ) 0 0 1 1| ≤ 1 / (6 * Real.sqrt 3) := by
  rw [jarlskog_ckmStandard_formula]
  calc
    _ = |Real.cos θ₁₂ * Real.sin θ₁₂| * |Real.cos θ₂₃ * Real.sin θ₂₃| *
        (|Real.sin θ₁₃| * Real.cos θ₁₃ ^ 2) * |Real.sin δ| := by
      simp only [abs_mul, abs_of_nonneg (sq_nonneg (Real.cos θ₁₃))]
      ring
    _ ≤ (1 / 2) * (1 / 2) * (2 / (3 * Real.sqrt 3)) * 1 := by
      gcongr
      · exact abs_cos_mul_sin_le θ₁₂
      · exact abs_cos_mul_sin_le θ₂₃
      · exact abs_sin_mul_cos_sq_le θ₁₃
      · exact Real.abs_sin_le_one δ
    _ = _ := by ring

theorem jarlskog_bound_attained :
    let θ := Real.arcsin (1 / Real.sqrt 3)
    Real.sin θ = 1 / Real.sqrt 3 ∧
      jarlskogQuartet (ckmStandard (Real.pi / 4) (Real.pi / 4) θ (Real.pi / 2)) 0 0 1 1 =
        1 / (6 * Real.sqrt 3) := by
  dsimp
  have hsqrt : 0 < Real.sqrt 3 := by positivity
  have hsqrt_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : Real.sin (Real.arcsin (1 / Real.sqrt 3)) = 1 / Real.sqrt 3 :=
    Real.sin_arcsin ((by norm_num : (-1 : ℝ) ≤ 0).trans (by positivity))
      ((div_le_iff₀ hsqrt).2 (by nlinarith))
  have hc : Real.cos (Real.arcsin (1 / Real.sqrt 3)) ^ 2 = 2 / 3 := by
    have h := Real.sin_sq_add_cos_sq (Real.arcsin (1 / Real.sqrt 3))
    rw [hs, div_pow, hsqrt_sq] at h
    linarith
  have htwo : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  refine ⟨hs, ?_⟩
  rw [jarlskog_ckmStandard_formula, hs, hc, Real.cos_pi_div_four, Real.sin_pi_div_four,
    Real.sin_pi_div_two]
  calc
    _ = (Real.sqrt 2 ^ 2) ^ 2 / (24 * Real.sqrt 3) := by ring
    _ = _ := by rw [htwo]; ring

private theorem abs_leviSign_of_ne {j l : Fin 3} (h : j ≠ l) : |leviSign j l| = 1 := by
  simp only [leviSign, ite_eq_right h]
  split <;> norm_num

theorem unitarity_triangle_area_eq_half_jarlskog (V : Matrix (Fin 3) (Fin 3) ℂ)
    (hV : Vᴴ * V = 1) {j l : Fin 3} (hjl : j ≠ l) :
    let z := fun i => V i j * conj (V i l)
    z 0 + z 1 + z 2 = 0 ∧
      (conj (z 0) * z 1).im / 2 = -jarlskogQuartet V 0 j 1 l / 2 ∧
      |(conj (z 0) * z 1).im / 2| = |jarlskogQuartet V 0 0 1 1| / 2 := by
  dsimp
  refine ⟨column_triangle V hV hjl, ?_, ?_⟩
  · rw [quartet_columns, mul_comm (conj (_ * _)) (_ * _), ← cross, cross_swap]
  · rw [mul_comm (conj (_ * _)) (_ * _), ← cross, cross_swap, ← quartet_columns,
      jarlskogQuartet_unitary_universal V hV 0 j 1 l]
    have h01 : leviSign 0 1 = 1 := by norm_num [leviSign]
    norm_num [h01, abs_div, abs_mul, abs_leviSign_of_ne hjl]

theorem row_unitarity_triangle_area_eq_half_jarlskog (V : Matrix (Fin 3) (Fin 3) ℂ)
    (hV : Vᴴ * V = 1) {i k : Fin 3} (hik : i ≠ k) :
    let z := fun j => V i j * conj (V k j)
    z 0 + z 1 + z 2 = 0 ∧
      (conj (z 0) * z 1).im / 2 = -jarlskogQuartet V i 0 k 1 / 2 ∧
      |(conj (z 0) * z 1).im / 2| = |jarlskogQuartet V 0 0 1 1| / 2 := by
  dsimp
  refine ⟨row_triangle V (mul_eq_one_comm.mp hV) hik, ?_, ?_⟩
  · rw [quartet_rows, mul_comm (conj (_ * _)) (_ * _), ← cross, cross_swap]
  · rw [mul_comm (conj (_ * _)) (_ * _), ← cross, cross_swap, ← quartet_rows,
      jarlskogQuartet_unitary_universal V hV i 0 k 1]
    have h01 : leviSign 0 1 = 1 := by norm_num [leviSign]
    norm_num [h01, abs_div, abs_mul, abs_leviSign_of_ne hik]

end D5.S3.Quantum.Gauge.CKMFlavorJarlskog4D
