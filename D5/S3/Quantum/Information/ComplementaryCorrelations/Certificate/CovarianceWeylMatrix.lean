/- GID: D5/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceWeylMatrix
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/ComplementaryCorrelations/Certificate/CovarianceWeylMatrix
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Hermitian qutrit matrices induce the Weyl coefficient system used by the covariance proof. -/

import D5.S3.Quantum.Information.ComplementaryCorrelations.Certificate.CovarianceCertificateCore
import D5.S3.Quantum.Entanglement.QutritWeylBlochNormSeparableBound
import Mathlib.LinearAlgebra.Matrix.Circulant

/-! The exact Weyl trace convention realized on complex qutrit matrices. -/

set_option autoImplicit false

noncomputable section
open Matrix
open scoped BigOperators

namespace QianACC.CovarianceWeylMatrix

open CovarianceCertificate
open D5.S3.QuantumContext.HesseSicCertificate (omega omega_pow_four)
open D5.S3.Quantum.Entanglement.QutritWeylBlochNormSeparableBound (W)

abbrev Mat := Matrix (Fin 3) (Fin 3) ℂ

private def axisX (w : Weight) : Fin 3 := Fin.ofNat 3 (w.val / 3)
private def axisZ (w : Weight) : Fin 3 := Fin.ofNat 3 w.val

private def phase (k : Fin 3) : Coeff :=
  ![1, ⟨-1 / 2, 1 / 2⟩, ⟨-1 / 2, -1 / 2⟩] k

private def phaseIndex (w v : Weight) : Fin 3 :=
  2 * (axisZ w * axisX v - axisX w * axisZ v)

/-- In the certificate's ordering, the shift index in the repository's W is
negative and the symmetrizing phase is ω^(ab). -/
def weyl (w : Weight) : Mat :=
  omega ^ ((axisX w).val * (axisZ w).val) • W (axisZ w) (0 - axisX w)

private def exactWeyl (w : Weight) : Matrix (Fin 3) (Fin 3) Coeff :=
  fun i j => if j = i + (0 - axisX w) then phase ((i + axisX w) * axisZ w) else 0

private theorem omega_parts : omega.re = -1 / 2 ∧ omega.im = Real.sqrt 3 / 2 := by
  have harg : (2 * Real.pi * Complex.I / 3 : ℂ) =
      (2 * Real.pi / 3 : ℝ) * Complex.I := by push_cast; ring
  have hangle : (2 * Real.pi / 3 : ℝ) = 2 * (Real.pi / 3) := by ring
  unfold omega
  rw [harg]
  constructor
  · rw [Complex.exp_ofReal_mul_I_re, hangle, Real.cos_two_mul, Real.cos_pi_div_three]
    norm_num
  · rw [Complex.exp_ofReal_mul_I_im, hangle, Real.sin_two_mul,
      Real.sin_pi_div_three, Real.cos_pi_div_three]
    ring

private theorem phase_eval (k : Fin 3) : toComplex (phase k) = omega ^ k.val := by
  have hs := Real.mul_self_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  fin_cases k
  · change toComplex 1 = omega ^ 0
    simp
  · change (⟨((-1 / 2 : ℚ) : ℝ), ((1 / 2 : ℚ) : ℝ) * Real.sqrt 3⟩ : ℂ) = omega ^ 1
    rw [pow_one]
    apply Complex.ext
    · change ((-1 / 2 : ℚ) : ℝ) = omega.re
      push_cast
      exact omega_parts.1.symm
    · change ((1 / 2 : ℚ) : ℝ) * Real.sqrt 3 = omega.im
      rw [omega_parts.2]
      push_cast
      ring
  · change (⟨((-1 / 2 : ℚ) : ℝ), ((-1 / 2 : ℚ) : ℝ) * Real.sqrt 3⟩ : ℂ) = omega ^ 2
    rw [pow_two]
    apply Complex.ext
    · change ((-1 / 2 : ℚ) : ℝ) = _
      rw [Complex.mul_re, omega_parts.1, omega_parts.2]
      push_cast
      linear_combination hs / 4
    · change ((-1 / 2 : ℚ) : ℝ) * Real.sqrt 3 = (omega * omega).im
      rw [Complex.mul_im, omega_parts.1, omega_parts.2]
      push_cast
      ring

private theorem exactWeyl_eval (w : Weight) : complexMatrix (exactWeyl w) = weyl w := by
  ext i j : 1
  change toComplex (if j = i + (0 - axisX w) then phase ((i + axisX w) * axisZ w) else 0) =
    omega ^ ((axisX w).val * (axisZ w).val) *
      (if j = i + (0 - axisX w) then omega ^ (i.val * (axisZ w).val) else 0)
  by_cases h : j = i + (0 - axisX w)
  · simp only [ite_eq_left h, phase_eval]
    have hcube : omega ^ 3 = 1 := by
      have hn : omega ≠ 0 := Complex.exp_ne_zero _
      apply mul_left_cancel₀ hn
      simpa only [← pow_succ', mul_one] using omega_pow_four
    rw [← pow_add]
    have hmod : ((i + axisX w) * axisZ w).val =
        ((axisX w).val * (axisZ w).val + i.val * (axisZ w).val) % 3 := by
      clear h
      revert w i
      decide +kernel
    rw [hmod]
    generalize (axisX w).val * (axisZ w).val + i.val * (axisZ w).val = n
    conv_rhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hcube, one_pow, mul_one]
  · simp only [ite_eq_right h, map_zero, mul_zero]

private def allFin {n : ℕ} (p : Fin n → Bool) : Bool := (List.finRange n).all p

private theorem allFin_true {n : ℕ} {p : Fin n → Bool} :
    allFin p = true ↔ ∀ i, p i = true := by simp [allFin]

private theorem exactWeyl_one : exactWeyl 0 = 1 := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem exactWeyl_adjoint (w : Weight) : (exactWeyl w)ᴴ = exactWeyl (negWeight w) := by
  have h : allFin (fun w => allFin fun i => allFin fun j =>
      decide ((exactWeyl w)ᴴ i j = exactWeyl (negWeight w) i j)) = true := by
    decide +kernel
  have h' : ∀ w i j, (exactWeyl w)ᴴ i j = exactWeyl (negWeight w) i j := by
    simpa only [allFin_true, decide_eq_true_eq] using h
  exact Matrix.ext fun i j => h' w i j

private theorem exactWeyl_mul (w v : Weight) :
    exactWeyl w * exactWeyl v = phase (phaseIndex w v) • exactWeyl (addWeight w v) := by
  have h : allFin (fun w => allFin fun v => allFin fun i => allFin fun j =>
      decide ((sumFin fun k => exactWeyl w i k * exactWeyl v k j) =
        phase (phaseIndex w v) * exactWeyl (addWeight w v) i j)) = true := by
    decide +kernel
  have h' : ∀ w v i j, (sumFin fun k => exactWeyl w i k * exactWeyl v k j) =
      phase (phaseIndex w v) * exactWeyl (addWeight w v) i j := by
    simpa only [allFin_true, decide_eq_true_eq] using h
  ext i j : 1
  rw [Matrix.mul_apply, ← sumFin_eq]
  exact h' w v i j

private theorem phase_mul (p q : Fin 3) : phase p * phase q = phase (p + q) := by
  revert p q
  decide +kernel

private theorem exactWeyl_trace (w : Weight) :
    (exactWeyl w).trace = if w = 0 then rat 3 else 0 := by
  simp only [Matrix.trace, Matrix.diag_apply, ← sumFin_eq]
  revert w
  decide +kernel

@[simp] theorem weyl_zero : weyl 0 = 1 := by
  rw [← exactWeyl_eval, exactWeyl_one]
  exact Matrix.map_one (n := Fin 3) toComplex (map_zero _) (map_one _)

@[simp] theorem weyl_adjoint (w : Weight) : (weyl w)ᴴ = weyl (negWeight w) := by
  rw [← exactWeyl_eval, ← complexMatrix_adjoint, exactWeyl_adjoint, exactWeyl_eval]

private theorem trace_eval (A : Matrix (Fin 3) (Fin 3) Coeff) :
    (complexMatrix A).trace = toComplex A.trace := by
  simp [Matrix.trace, Matrix.diag_apply, complexMatrix, map_sum]

private def step (s : Weight × Fin 3) (v : Weight) : Weight × Fin 3 :=
  (addWeight s.1 v, s.2 + phaseIndex s.1 v)

private theorem exactWord (s : Weight × Fin 3) (word : List Weight) :
    (phase s.2 • exactWeyl s.1) * (word.map exactWeyl).prod =
      phase (word.foldl step s).2 • exactWeyl (word.foldl step s).1 := by
  induction word generalizing s with
  | nil => simp
  | cons v tail ih =>
    simp only [List.map_cons, List.prod_cons, List.foldl_cons]
    rw [← Matrix.mul_assoc, smul_mul_assoc, exactWeyl_mul, smul_smul, phase_mul]
    exact ih (step s v)

theorem trace_word (word : List Weight) :
    ((word.map weyl).prod).trace = toComplex (weylTrace word) := by
  have h : complexMatrix (word.map exactWeyl).prod = (word.map weyl).prod := by
    induction word with
    | nil => exact Matrix.map_one (n := Fin 3) toComplex (map_zero _) (map_one _)
    | cons v tail ih =>
      simp only [List.map_cons, List.prod_cons, complexMatrix_mul, exactWeyl_eval, ih]
  rw [← h, trace_eval]
  congr 1
  have hw := exactWord (0, 0) word
  change (1 : Coeff) • exactWeyl 0 * (word.map exactWeyl).prod = _ at hw
  rw [one_smul, exactWeyl_one, Matrix.one_mul] at hw
  rw [hw, Matrix.trace_smul, exactWeyl_trace]
  change _ = if (word.foldl step (0, 0)).1 = 0 then
    rat 3 * phase (word.foldl step (0, 0)).2 else 0
  split <;> simp [*, mul_comm]

/-- The coefficient is the normalized trace against the adjoint basis word. -/
def coordinate (T : Mat) (w : Weight) : ℂ :=
  (T * weyl (negWeight w)).trace / 3

theorem coordinate_star {T : Mat} (hT : T.IsHermitian) (w : Weight) :
    star (coordinate T w) = coordinate T (negWeight w) := by
  unfold coordinate
  rw [star_div₀, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hT.eq,
    weyl_adjoint, Matrix.trace_mul_comm]
  have hn : negWeight (negWeight w) = w := by
    revert w
    decide +kernel
  rw [hn]
  norm_num

private theorem exact_completeness (i j k l : Fin 3) :
    (∑ w : Weight, exactWeyl (negWeight w) j i * exactWeyl w k l) =
      if i = k ∧ j = l then rat 3 else 0 := by
  rw [← sumFin_eq]
  revert i j k l
  decide +kernel

private theorem completeness (i j k l : Fin 3) :
    (∑ w : Weight, weyl (negWeight w) j i * weyl w k l) =
      if i = k ∧ j = l then (3 : ℂ) else 0 := by
  have h := congrArg toComplex (exact_completeness i j k l)
  simp only [map_sum, map_mul] at h
  simp_rw [show ∀ w a b, toComplex (exactWeyl w a b) = weyl w a b from
    fun w a b => congrFun (congrFun (exactWeyl_eval w) a) b] at h
  by_cases hkl : i = k ∧ j = l <;> simpa [hkl] using h

theorem reconstruct (T : Mat) : (∑ w : Weight, coordinate T w • weyl w) = T := by
  ext k l : 1
  calc
    (∑ w : Weight, coordinate T w • weyl w) k l =
        (3 : ℂ)⁻¹ * ∑ w : Weight, ∑ i : Fin 3, ∑ j : Fin 3,
          T i j * (weyl (negWeight w) j i * weyl w k l) := by
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, coordinate, Matrix.trace,
        Matrix.diag_apply, Matrix.mul_apply, div_eq_mul_inv]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (3 : ℂ)⁻¹ * ∑ i : Fin 3, ∑ j : Fin 3,
        T i j * (if i = k ∧ j = l then 3 else 0) := by
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.mul_sum, completeness]
    _ = T k l := by
      simp only [ite_and, mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
      rw [Finset.sum_eq_single k]
      · simp
        ring
      · intro i _ hik
        simp [hik]
      · simp

theorem trace_two (x : Weight → ℂ) (A B : List Weight)
    (T : Mat) (hT : (∑ w : Weight, x w • weyl w) = T) :
    (T * (A.map weyl).prod * T * (B.map weyl).prod).trace =
      traceForm x (fun i j => i :: A ++ j :: B) := by
  rw [← hT]
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum, smul_mul_assoc,
    mul_smul_comm, Matrix.trace_smul, smul_eq_mul, traceForm, List.map_cons,
    List.map_append, List.prod_cons, List.prod_append, ← trace_word]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.mul_assoc]
  ring

private theorem diagonal_coordinate_zero (d : Fin 3 → ℂ) (w : Weight) (h : 3 ≤ w.val) :
    coordinate (Matrix.diagonal d) w = 0 := by
  unfold coordinate
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]
  have hzero : ∀ (v : Weight) (i : Fin 3), 3 ≤ v.val → exactWeyl (negWeight v) i i = 0 := by
    decide +kernel
  rw [← exactWeyl_eval]
  simp [complexMatrix, hzero w _ h]

theorem diagonal_expansion (d : Fin 3 → ℂ) :
    Matrix.diagonal d =
      coordinate (Matrix.diagonal d) 0 • (1 : Mat) +
        (coordinate (Matrix.diagonal d) 1 • weyl 1 +
          coordinate (Matrix.diagonal d) 2 • weyl 2) := by
  have h := reconstruct (Matrix.diagonal d)
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at h
  change (coordinate (Matrix.diagonal d) 0 • weyl 0 +
    (coordinate (Matrix.diagonal d) 1 • weyl 1 + (coordinate (Matrix.diagonal d) 2 • weyl 2 +
    (coordinate (Matrix.diagonal d) 3 • weyl 3 + (coordinate (Matrix.diagonal d) 4 • weyl 4 +
    (coordinate (Matrix.diagonal d) 5 • weyl 5 + (coordinate (Matrix.diagonal d) 6 • weyl 6 +
    (coordinate (Matrix.diagonal d) 7 • weyl 7 + (coordinate (Matrix.diagonal d) 8 • weyl 8 +
    0))))))))) = _ at h
  rw [weyl_zero] at h
  have hz := diagonal_coordinate_zero d
  simp only [hz 3 (by decide), hz 4 (by decide), hz 5 (by decide), hz 6 (by decide),
    hz 7 (by decide), hz 8 (by decide), zero_smul, add_zero] at h
  exact h.symm

theorem circulant_expansion (f : Fin 3 → ℂ) :
    Matrix.circulant f = f 0 • (1 : Mat) + (f 1 • weyl 3 + f 2 • weyl 6) := by
  have h0 (i j : Fin 3) : exactWeyl 0 i j = if i - j = 0 then 1 else 0 := by
    fin_cases i <;> fin_cases j <;> decide +kernel
  have h1 (i j : Fin 3) : exactWeyl 3 i j = if i - j = 1 then 1 else 0 := by
    fin_cases i <;> fin_cases j <;> decide +kernel
  have h2 (i j : Fin 3) : exactWeyl 6 i j = if i - j = 2 then 1 else 0 := by
    fin_cases i <;> fin_cases j <;> decide +kernel
  ext i j : 1
  rw [← weyl_zero, ← exactWeyl_eval 0, ← exactWeyl_eval 3, ← exactWeyl_eval 6]
  simp only [Matrix.circulant_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    complexMatrix, Matrix.map_apply, h0, h1, h2]
  generalize i - j = k
  fin_cases k <;> simp

end QianACC.CovarianceWeylMatrix
