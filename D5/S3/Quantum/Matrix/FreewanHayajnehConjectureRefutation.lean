/- GID: D5/S3/Quantum/Matrix/FreewanHayajnehConjectureRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/FreewanHayajnehConjectureRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/FreewanHayajnehConjectureRefutation.conjecture; result=D5/S3/Quantum/Matrix/FreewanHayajnehConjectureRefutation.result; claim=D5/S3/Quantum/Matrix/FreewanHayajnehConjectureRefutation.conjecture
   digest: A rational positive definite pair refutes the weighted geometric mean norm conjecture. -/

import D5.S3.Quantum.Matrix.SpectralGeometricLogEuclideanRefutation
import D5.S3.Quantum.Matrix.AlternativeMeanLinearization
import D5.S0.Observation.MatrixTracePowerSum
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Isometry
import D5.S3.Quantum.Schatten.UnitarilyInvariantNorm
import Mathlib.Tactic

/- admission_basis: open-problem-resolution (#31551; Refuted). -/

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace D5.S3.Quantum.Matrix.FreewanHayajnehConjectureRefutation
open SpectralPower (mpow)
open SpectralGeometricLogEuclideanRefutation (wgm cfc_diag)
open D5.S3.Quantum.Schatten (UINorm)

/-- Conjecture 2; the additional zero-dimensional case is trivial. -/
def conjecture : Prop :=
  ∀ (n m : ℕ), 1 ≤ m → ∀ A B : Fin m → Matrix (Fin n) (Fin n) ℂ,
    (∀ i, (A i).PosDef) → (∀ i, (B i).PosDef) →
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ r : ℝ, 1 ≤ 2 * r → ∀ p : ℝ, 0 < p →
    ∀ N : UINorm n,
      N.N (∑ i, mpow (wgm (A i ^ 2) (B i ^ 2) t) r) ≤
        N.N (mpow (mpow (∑ i, A i) ((1 - t) * p * r) *
          mpow (∑ i, B i) (2 * t * p * r) *
          mpow (∑ i, A i) ((1 - t) * p * r)) (1 / p))

private abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ

private def opNorm : UINorm 2 where
  N X := ‖X‖
  nonneg := norm_nonneg
  eq_zero_iff _ := norm_eq_zero
  add_le := norm_add_le
  smul_eq := norm_smul
  unitary_invariant U V X hU hV := by
    change ‖(⟨U, hU⟩ : Matrix.unitaryGroup (Fin 2) ℂ).val * X *
      (⟨V, hV⟩ : Matrix.unitaryGroup (Fin 2) ℂ).val‖ = ‖X‖
    rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]

private def P : Mat := !![1, 3 / 20; 3 / 20, 9 / 4]
private def Q : Mat := !![1, 1 / 5; 1 / 5, 4 / 9]
private def Pi : Mat := !![100 / 99, -20 / 297; -20 / 297, 400 / 891]
private def u : ℝ := Real.sqrt (5711641 / 625)
private def v : ℝ := Real.sqrt (9009 / 10000)
private def a : ℝ := 245713 / 2500 / u
private def b : ℝ := 3783 / 125 / u
private def c : ℝ := 232713 / 2500 / u
private def C : Mat := !![(a : ℂ), (b : ℂ); (b : ℂ), (c : ℂ)]
private def w : ℝ := Real.sqrt (a + c + 2 * v)
private def M : Mat := w⁻¹ • (C + v • (1 : Mat))

private lemma P_pos : P.PosDef := by
  convert SpectralPower.posDef_two 1 (3 / 20) (9 / 4)
    (by norm_num) (by norm_num) using 1 <;> norm_num [P]

private lemma Q_pos : Q.PosDef := by
  convert SpectralPower.posDef_two 1 (1 / 5) (4 / 9)
    (by norm_num) (by norm_num) using 1 <;> norm_num [Q]

private lemma Pi_inverse : P * Pi = 1 ∧ Pi * P = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [P, Pi, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

private lemma roots :
    0 < u ∧ u ^ 2 = 5711641 / 625 ∧ 0 < v ∧ v ^ 2 = 9009 / 10000 := by
  exact ⟨Real.sqrt_pos.mpr (by norm_num), Real.sq_sqrt (by norm_num),
    Real.sqrt_pos.mpr (by norm_num), Real.sq_sqrt (by norm_num)⟩

private lemma C_pos : C.PosDef := by
  apply SpectralPower.posDef_two
  · exact div_pos (by norm_num [a]) roots.1
  · have hu := roots.1.ne'
    dsimp [a, b, c]
    field_simp
    norm_num
    exact sq_pos_of_ne_zero hu

private lemma half_of_square (X : Mat) (hX : X.PosDef) :
    mpow (X * X) (1 / 2) = X := by
  have hXX : (X * X).PosDef := by
    exact (show (X * X).PosSemidef by
      simpa only [pow_two] using hX.posSemidef.pow 2).posDef_iff_isUnit.mpr
        (hX.isUnit.mul hX.isUnit)
  change cfc (fun x : ℝ => x ^ (1 / 2 : ℝ)) (X * X) = X
  rw [AlternativeMeanLinearization.half_eq_sqrt hXX]
  exact CFC.sqrt_unique rfl hX.posSemidef.nonneg

private lemma geometric_of_riccati (X Y Z T : Mat) (hX : X.PosDef)
    (hZ : Z.PosDef) (hXT : X * T = 1) (hTX : T * X = 1)
    (hT : T.PosDef) (hZT : Z * T * T * Z = Y * Y) :
    wgm (X * X) (Y * Y) (1 / 2) = Z := by
  have square_pos (W : Mat) (hW : W.PosDef) : (W * W).PosDef := by
    exact (show (W * W).PosSemidef by
      simpa only [pow_two] using hW.posSemidef.pow 2).posDef_iff_isUnit.mpr
        (hW.isUnit.mul hW.isUnit)
  have neg_half (W V : Mat) (hW : W.PosDef) (hVW : V * W = 1) :
      mpow (W * W) (-1 / 2) = V := by
    have h := (AlternativeMeanLinearization.half_inverse (square_pos W hW)).1
    change mpow (W * W) (1 / 2) * mpow (W * W) (-(1 / 2)) = 1 at h
    rw [half_of_square W hW] at h
    calc
      mpow (W * W) (-1 / 2) = V * (W * mpow (W * W) (-1 / 2)) := by
        rw [← mul_assoc, hVW, one_mul]
      _ = V := by simpa only [neg_div, one_div, mul_one] using congrArg (V * ·) h
  have hg := AlternativeMeanLinearization.riccati_unique (square_pos T hT) hZ
    (by simpa only [mul_assoc] using hZT)
  simp only [AlternativeMeanLinearization.gmInv, ← neg_div] at hg
  change mpow (T * T) (-1 / 2) *
    mpow (mpow (T * T) (1 / 2) * (Y * Y) * mpow (T * T) (1 / 2)) (1 / 2) *
    mpow (T * T) (-1 / 2) = Z at hg
  rw [half_of_square T hT, neg_half T X hT hXT] at hg
  simpa only [wgm, half_of_square X hX, neg_half X T hX hTX] using hg

private lemma riccati_certificate : C * Pi * Pi * C = Q * Q := by
  have hu : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr roots.1.ne'
  have hs : (u : ℂ) ^ 2 = (5711641 / 625 : ℂ) := by
    have h := congrArg Complex.ofReal roots.2.1
    push_cast at h
    exact h
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [C, Pi, Q, a, b, c, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals
    field_simp [hu]
    rw [hs]
    norm_num

private lemma geometric_value : wgm (P * P) (Q * Q) (1 / 2) = C := by
  apply geometric_of_riccati P Q C Pi P_pos C_pos Pi_inverse.1 Pi_inverse.2
  · convert SpectralPower.posDef_two (100 / 99) (-20 / 297) (400 / 891)
      (by norm_num) (by norm_num) using 1 <;> norm_num [Pi]
  · exact riccati_certificate

private lemma scalar_bounds :
    1028 / 1000 < a ∧ a < 1029 / 1000 ∧
    973 / 1000 < c ∧ c < 974 / 1000 ∧
    949 / 1000 < v ∧ v < 950 / 1000 := by
  have hu : 9559 / 100 < u ∧ u < 956 / 10 := by
    constructor <;> nlinarith [roots.1, roots.2.1]
  have hv : 949 / 1000 < v ∧ v < 950 / 1000 := by
    constructor <;> nlinarith [roots.2.2.1, roots.2.2.2]
  dsimp only [a, c]
  refine ⟨?_, ?_, ?_, ?_, hv.1, hv.2⟩
  · apply (lt_div_iff₀ roots.1).mpr
    nlinarith [hu.2]
  · apply (div_lt_iff₀ roots.1).mpr
    nlinarith [hu.1]
  · apply (lt_div_iff₀ roots.1).mpr
    nlinarith [hu.2]
  · apply (div_lt_iff₀ roots.1).mpr
    nlinarith [hu.1]

private lemma determinant_certificate : a * c - b ^ 2 = v ^ 2 := by
  have hu : u ≠ 0 := roots.1.ne'
  have hs := roots.2.1
  rw [roots.2.2.2]
  dsimp [a, b, c]
  field_simp
  nlinarith [hs]

private lemma w_data : 0 < w ∧ w ^ 2 = a + c + 2 * v := by
  have h := scalar_bounds
  have hp : 0 < a + c + 2 * v := by linarith [h.1, h.2.2.1, h.2.2.2.2.1]
  exact ⟨Real.sqrt_pos.mpr hp, Real.sq_sqrt hp.le⟩

private lemma M_nonneg : 0 ≤ M := by
  exact smul_nonneg (inv_nonneg.mpr w_data.1.le)
    (add_nonneg C_pos.posSemidef.nonneg (smul_nonneg roots.2.2.1.le zero_le_one))

private lemma M_square : M * M = C := by
  have hK : (C + v • (1 : Mat)) * (C + v • (1 : Mat)) =
      (a + c + 2 * v) • C := by
    have hCH := D5.S0.Observation.MatrixTracePowerSum.pow_add_two C 0
    have htrace : Matrix.trace C = ((a + c : ℝ) : ℂ) := by
      simp [C, Matrix.trace_fin_two]
    have hdet : Matrix.det C = ((v ^ 2 : ℝ) : ℂ) := by
      simpa [C, Matrix.det_fin_two, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
        ← Complex.ofReal_pow, ← pow_two] using
        congrArg Complex.ofReal determinant_certificate
    simp only [Nat.zero_add, pow_one, pow_zero, htrace, hdet, pow_two] at hCH
    simp only [add_mul, mul_add, mul_smul_comm, smul_mul_assoc,
      mul_one, one_mul, smul_smul]
    rw [hCH]
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), Complex.ofReal_add,
      Complex.ofReal_mul, Complex.ofReal_ofNat]
    module
  simp only [M, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [hK, smul_smul, ← w_data.2]
  rw [show w⁻¹ * w⁻¹ * w ^ 2 = 1 by field_simp [w_data.1.ne']]
  exact one_smul _ _

private lemma half_value : mpow C (1 / 2) = M := by
  change cfc (fun x : ℝ => x ^ (1 / 2 : ℝ)) C = M
  rw [AlternativeMeanLinearization.half_eq_sqrt C_pos]
  exact CFC.sqrt_unique M_square M_nonneg

private lemma M_entry_gt : 1 < (M 0 0).re := by
  have h := scalar_bounds
  have hw : w < 1976 / 1000 := by
    nlinarith [w_data.1, w_data.2, h.2.1, h.2.2.2.1, h.2.2.2.2.2]
  have hnum : 1977 / 1000 < a + v := by linarith [h.1, h.2.2.2.2.1]
  have he : (M 0 0).re = (a + v) / w := by
    change (w⁻¹ • ((a : ℂ) + v • (1 : ℂ))).re = (a + v) / w
    simp only [Complex.smul_re, Complex.add_re, Complex.ofReal_re, Complex.one_re,
      mul_one, div_eq_mul_inv]
    ring
  rw [he]
  apply (lt_div_iff₀ w_data.1).mpr
  linarith

private def J : Mat := diagonal ![1, -1]

private lemma J_data : Jᴴ = J ∧ J * J = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [J, Matrix.diagonal, Matrix.conjTranspose_apply, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.one_apply]

private def flip : Mat ≃⋆ₐ[ℂ] Mat :=
  Unitary.conjStarAlgAut ℂ Mat ⟨J, by
    change Jᴴ * J = 1 ∧ J * Jᴴ = 1
    rw [J_data.1]
    exact ⟨J_data.2, J_data.2⟩⟩

private lemma flip_pos (X : Mat) (hX : X.PosDef) : (flip X).PosDef := by
  have hJU : IsUnit J := ⟨⟨J, J, J_data.2, J_data.2⟩, rfl⟩
  exact hJU.posDef_star_right_conjugate_iff.mpr hX

private lemma flipped_geometric :
    wgm (flip P * flip P) (flip Q * flip Q) (1 / 2) = flip C := by
  apply geometric_of_riccati (flip P) (flip Q) (flip C) (flip Pi)
    (flip_pos P P_pos) (flip_pos C C_pos)
  · simpa using congrArg flip Pi_inverse.1
  · simpa using congrArg flip Pi_inverse.2
  · apply flip_pos
    convert SpectralPower.posDef_two (100 / 99) (-20 / 297) (400 / 891)
      (by norm_num) (by norm_num) using 1 <;> norm_num [Pi]
  · simpa using congrArg flip riccati_certificate

private lemma flipped_half : mpow (flip C) (1 / 2) = flip M := by
  change cfc (fun x : ℝ => x ^ (1 / 2 : ℝ)) (flip C) = flip M
  have hc := Matrix.cfc_conj_unitary (A := C) (fun x : ℝ => x ^ (1 / 2 : ℝ))
    (⟨J, by
      change Jᴴ * J = 1 ∧ J * Jᴴ = 1
      rw [J_data.1]
      exact ⟨J_data.2, J_data.2⟩⟩ : Matrix.unitaryGroup (Fin 2) ℂ)
  change cfc (fun x : ℝ => x ^ (1 / 2 : ℝ)) (flip C) = flip (mpow C (1 / 2)) at hc
  simpa only [half_value] using hc

private def AA : Fin 2 → Mat := ![P, flip P]
private def BB : Fin 2 → Mat := ![Q, flip Q]

private lemma inputs_positive : (∀ i, (AA i).PosDef) ∧ (∀ i, (BB i).PosDef) := by
  constructor <;> intro i <;> fin_cases i
  · exact P_pos
  · exact flip_pos P P_pos
  · exact Q_pos
  · exact flip_pos Q Q_pos

private lemma input_sums :
    (∑ i, AA i) = diagonal (fun i => ((![2, 9 / 2] : Fin 2 → ℝ) i : ℂ)) ∧
    (∑ i, BB i) = diagonal (fun i => ((![2, 8 / 9] : Fin 2 → ℝ) i : ℂ)) := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [AA, BB, flip, Unitary.conjStarAlgAut_apply, J, P, Q,
      Matrix.diagonal, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]

private lemma left_value :
    (∑ i, mpow (wgm (AA i ^ 2) (BB i ^ 2) (1 / 2)) (1 / 2)) =
      diagonal ![((2 * (M 0 0).re : ℝ) : ℂ), ((2 * (M 1 1).re : ℝ) : ℂ)] := by
  simp only [Fin.sum_univ_two, AA, BB, Matrix.cons_val_zero, Matrix.cons_val_one,
    pow_two, geometric_value, flipped_geometric, half_value, flipped_half]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flip, Unitary.conjStarAlgAut_apply, J, M, C, Matrix.diagonal,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Complex.real_smul] <;> ring

private lemma right_value :
    mpow (mpow (∑ i, AA i) (1 / 2) * (∑ i, BB i) *
      mpow (∑ i, AA i) (1 / 2)) (1 / 2) = 2 := by
  have hinner : mpow (∑ i, AA i) (1 / 2) * (∑ i, BB i) *
      mpow (∑ i, AA i) (1 / 2) = (2 : Mat) * 2 := by
    have hs : (Real.sqrt (2 : ℝ) : ℂ) ^ 2 = 2 := by
      exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have ht : (Real.sqrt (9 / 2 : ℝ) : ℂ) ^ 2 = 9 / 2 := by
      have h := congrArg Complex.ofReal
        (Real.sq_sqrt (show (0 : ℝ) ≤ 9 / 2 by norm_num))
      push_cast at h
      exact h
    have hn : (Real.sqrt (2 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
    have hm : (Real.sqrt (9 / 2 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
    rw [input_sums.1, input_sums.2]
    simp only [mpow, cfc_diag]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, Matrix.ofNat_apply,
        ← Real.sqrt_eq_rpow, ← Complex.ofReal_mul, ← Complex.ofReal_add]
    all_goals field_simp [hn, hm]
    all_goals ring_nf
    all_goals norm_num [hs, ht]
  rw [hinner, half_of_square _ (Matrix.PosDef.ofNat 2)]

/-- Positive definite rational inputs in dimension two refute Conjecture 2. -/
theorem result : ¬ conjecture := by
  intro h
  have bad := h 2 2 (by norm_num) AA BB inputs_positive.1 inputs_positive.2
    (1 / 2) (by norm_num) (by norm_num) (1 / 2) (by norm_num) 2 (by norm_num) opNorm
  norm_num only [show (1 - (1 / 2 : ℝ)) * 2 * (1 / 2) = 1 / 2 by norm_num,
    show 2 * (1 / 2 : ℝ) * 2 * (1 / 2) = 1 by norm_num,
    show (1 : ℝ) / 2 = 1 / 2 by rfl] at bad
  have hB : (∑ i, BB i).IsHermitian := by
    rw [input_sums.2]
    exact isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)
  rw [SpectralPower.mpow_one hB, right_value, left_value] at bad
  change ‖diagonal ![((2 * (M 0 0).re : ℝ) : ℂ),
    ((2 * (M 1 1).re : ℝ) : ℂ)]‖ ≤ ‖(2 : Mat)‖ at bad
  have htwo : ‖(2 : Mat)‖ = 2 := by
    have he : (2 : Mat) = diagonal (fun _ : Fin 2 => (2 : ℂ)) := rfl
    rw [he, Matrix.l2_opNorm_diagonal]
    norm_num
  rw [htwo, Matrix.l2_opNorm_diagonal] at bad
  have he := norm_le_pi_norm
    (![((2 * (M 0 0).re : ℝ) : ℂ), ((2 * (M 1 1).re : ℝ) : ℂ)]) (0 : Fin 2)
  have hp : 0 < 2 * (M 0 0).re := by linarith [M_entry_gt]
  simp only [Matrix.cons_val_zero, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hp] at he
  linarith [M_entry_gt]

#print axioms result

end D5.S3.Quantum.Matrix.FreewanHayajnehConjectureRefutation
