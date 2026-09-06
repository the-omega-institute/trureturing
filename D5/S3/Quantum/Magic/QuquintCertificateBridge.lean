/- GID: D5/S3/Quantum/Magic/QuquintCertificateBridge
   generality: I
   mirror-B: D5/B/S3/Quantum/Magic/QuquintCertificateBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=consumer=D5/S3/Quantum/Magic/QuquintFiniteMaximum.finite_sign_maximum
   digest: Identify the numerical certificate matrices with the ququint tangent forms. -/

import D5.S3.Quantum.Magic.QuquintWignerCriticalGeometry
import D5.S3.Quantum.Magic.QuquintCertificateData

noncomputable section
open Complex Matrix
open scoped BigOperators
open D5.S3.Quantum.Magic.QuquintWignerCriticalGeometry
open D5.S3.Quantum.Magic.QuquintCertificateData (base zeroQ radical radical_sq radical_quartic)
set_option maxRecDepth 2000
set_option maxHeartbeats 8000000

namespace D5.S3.Quantum.Magic.QuquintCertificateBridge

-- Reuse the checked phase-point computations from the geometry module.
open private zeta_value zeta_powers powerTable sign_table from
  D5.S3.Quantum.Magic.QuquintWignerCriticalGeometry

private theorem zeta_two : zeta ^ 2 =
    ⟨(8 - radical ^ 2)/8, (radical ^ 3 - 12*radical)/16⟩ := by
  simpa [powerTable] using zeta_powers 2
private theorem zeta_three : zeta ^ 3 =
    ⟨(8 - radical ^ 2)/8, (12*radical - radical ^ 3)/16⟩ := by
  simpa [powerTable] using zeta_powers 3
private theorem zeta_four : zeta ^ 4 =
    ⟨(radical ^ 2 - 12)/8, -radical/4⟩ := by
  simpa [powerTable] using zeta_powers 4

def complexBasis : Matrix (Fin 5) (Fin 4) ℂ := fun i j =>
  phases i * ⟨basisMatrix (Fin.castAdd 5 i) j, basisMatrix (Fin.natAdd 5 i) j⟩

def pullback (m : Matrix (Fin 5) (Fin 5) ℂ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => (star (fun k => complexBasis k i) ⬝ᵥ
    (m *ᵥ fun k => complexBasis k j)).re / 5

def phaseForm (q p : Fin 5) : Matrix (Fin 4) (Fin 4) ℝ := pullback (phasePoint q p)

def gram : Matrix (Fin 4) (Fin 4) ℝ :=
  !![10 - radical ^ 2/2, 10 - 3*radical ^ 2/4,
      radical ^ 3/4 - 3*radical, -radical ^ 3/8 + 5*radical/2;
    10 - 3*radical ^ 2/4, 10 - radical ^ 2/2,
      radical ^ 3/8 - 5*radical/2, -radical ^ 3/4 + 3*radical;
    radical ^ 3/4 - 3*radical, radical ^ 3/8 - 5*radical/2,
      7*radical ^ 2/10 + 2, 31*radical ^ 2/20 - 12;
    -radical ^ 3/8 + 5*radical/2, -radical ^ 3/4 + 3*radical,
      31*radical ^ 2/20 - 12, 7*radical ^ 2/10 + 2]

def signs : Matrix (Fin 5) (Fin 5) SignType :=
  !![-1,1,1,0,1; -1,1,1,0,1; 1,-1,1,1,0;
    1,0,1,-1,1; 1,-1,1,1,0]

def zeroIndex : Fin 5 → Fin 5 × Fin 5 := ![(0,3),(1,3),(2,4),(3,1),(4,4)]

def realification (m : Matrix (Fin 5) (Fin 5) ℂ) : Matrix (Fin 10) (Fin 10) ℝ :=
  fun i j => Fin.addCases
    (fun x => Fin.addCases (fun y => (m x y).re) (fun y => -(m x y).im) j)
    (fun x => Fin.addCases (fun y => (m x y).im) (fun y => (m x y).re) j) i

theorem signs_eq (q p : Fin 5) : signs q p = SignType.sign (wigner psi q p) :=
  (sign_table q p).symm

theorem zeroIndex_image : Finset.univ.image zeroIndex = zeroPoints := by
  rw [zero_points_eq]
  decide

theorem gram_eq : gram = basisMatrixᵀ * basisMatrix := by
  have h := radical_quartic
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gram, basisMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;> grind only

theorem zeroQ_0_eq : zeroQ 0 = phaseForm 0 3 := by
  have h := radical_quartic
  unfold zeroQ
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [phaseForm, pullback, complexBasis, basisMatrix, phases, phasePoint,
    zeta_value, dotProduct, mulVec, Fin.sum_univ_succ, pow_succ,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.conj_re, Complex.conj_im, ZMod.val, Fin.val, Fin.neg_def]
  all_goals norm_num [Complex.conj_ofNat, Complex.div_re, Complex.div_im,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.normSq_apply]
  all_goals grind only

theorem zeroQ_1_eq : zeroQ 1 = phaseForm 1 3 := by
  have h := radical_quartic
  unfold zeroQ
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [phaseForm, pullback, complexBasis, basisMatrix, phases, phasePoint,
    zeta_value, dotProduct, mulVec, Fin.sum_univ_succ, pow_succ,
    Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.conj_re, Complex.conj_im]
  all_goals norm_num [Complex.conj_ofNat, Complex.div_re, Complex.div_im,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.normSq_apply]
  all_goals grind only

theorem zeroQ_2_eq : zeroQ 2 = phaseForm 2 4 := by
  have h := radical_quartic
  unfold zeroQ
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [phaseForm, pullback, complexBasis, basisMatrix, phases, phasePoint,
    zeta_value, dotProduct, mulVec, Fin.sum_univ_succ, pow_succ,
    Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.conj_re, Complex.conj_im]
  all_goals norm_num [Complex.conj_ofNat, Complex.div_re, Complex.div_im,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.normSq_apply]
  all_goals grind only

theorem zeroQ_3_eq : zeroQ 3 = phaseForm 3 1 := by
  have h := radical_quartic
  unfold zeroQ
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [phaseForm, pullback, complexBasis, basisMatrix, phases, phasePoint,
    zeta_value, dotProduct, mulVec, Fin.sum_univ_succ, pow_succ,
    Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.conj_re, Complex.conj_im]
  all_goals norm_num [Complex.conj_ofNat, Complex.div_re, Complex.div_im,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.normSq_apply]
  all_goals grind only

theorem zeroQ_4_eq : zeroQ 4 = phaseForm 4 4 := by
  have h := radical_quartic
  unfold zeroQ
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [phaseForm, pullback, complexBasis, basisMatrix, phases, phasePoint,
    dotProduct, mulVec, Fin.sum_univ_succ, ZMod.val, Fin.val, Fin.neg_def,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ']
  all_goals simp only [zeta_two, zeta_three, zeta_four]
  all_goals norm_num [powerTable, zeta_value, pow_succ, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
  all_goals grind only

theorem base_eq_gradient : base = pullback gradient - lOne psi • gram := by
  have h := radical_quartic
  have hs : Real.sqrt 5 = (radical ^ 2 - 10) / 2 := by linarith [radical_sq]
  unfold base
  rw [lOne_psi, hs]
  unfold gradient
  simp only [sign_table]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [pullback, complexBasis, basisMatrix, phases, phasePoint, gram,
    dotProduct, mulVec, Fin.sum_univ_succ, ZMod.val, Fin.val, Fin.neg_def,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ']
  all_goals simp only [zeta_two, zeta_three, zeta_four]
  all_goals norm_num [powerTable, zeta_value, pow_succ, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im]
  all_goals ring_nf
  all_goals grind only

theorem complexBasis_tangentEquiv (a : Fin 4 → ℝ) :
    complexBasis *ᵥ (fun i => (a i : ℂ)) = WithLp.ofLp (tangentEquiv a : State) := by
  ext i
  change _ = phases i * ⟨(basisMatrix *ᵥ a) (Fin.castAdd 5 i),
    (basisMatrix *ᵥ a) (Fin.natAdd 5 i)⟩
  apply Complex.ext <;>
    simp [complexBasis, mulVec, dotProduct, Fin.sum_univ_succ,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

theorem phaseForm_realification (q p : Fin 5) : phaseForm q p =
    (1 / 5 : ℝ) • (basisMatrixᵀ *
      realification ((diagonal phases)ᴴ * phasePoint q p * diagonal phases) * basisMatrix) := by
  have hm : (diagonal phases)ᴴ * phasePoint q p * diagonal phases =
      fun x y => star (phases x) * phasePoint q p x y * phases y := by
    ext x y
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [hm]
  unfold phaseForm pullback complexBasis
  generalize basisMatrix = b
  generalize phases = d
  generalize phasePoint q p = m
  ext i j
  simp [realification, Fin.addCases, Matrix.mul_apply, dotProduct, mulVec,
    Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.conj_re, Complex.conj_im]
  ring

private theorem pullback_matrix (m : Matrix (Fin 5) (Fin 5) ℂ) :
    pullback m = fun i j => ((complexBasisᴴ * m * complexBasis) i j).re / 5 := by
  ext i j
  unfold pullback
  rw [dotProduct_mulVec]
  rfl

private theorem pullback_eval (m : Matrix (Fin 5) (Fin 5) ℂ) (a : Fin 4 → ℝ) :
    a ⬝ᵥ (pullback m *ᵥ a) =
      (star (complexBasis *ᵥ (fun i => (a i : ℂ))) ⬝ᵥ
        (m *ᵥ (complexBasis *ᵥ (fun i => (a i : ℂ))))).re / 5 := by
  rw [pullback_matrix, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  simp [dotProduct, mulVec, Complex.mul_re, Complex.mul_im, Complex.re_sum,
    Finset.sum_div, Finset.mul_sum, div_mul_eq_mul_div, mul_div_assoc]

theorem phaseForm_eval (q p : Fin 5) (a : Fin 4 → ℝ) :
    a ⬝ᵥ (phaseForm q p *ᵥ a) = wigner (tangentEquiv a : State) q p := by
  simp only [phaseForm, pullback_eval, complexBasis_tangentEquiv, wigner]

private theorem phase_norm (i : Fin 5) : ‖phases i‖ = 1 := by
  have hz : ‖zeta‖ = 1 := by simp [zeta, Complex.norm_exp]
  fin_cases i <;> simp [phases, norm_pow, hz]

private theorem gauge_norm_sq (u : Fin 10 → ℝ) : ‖gauge u‖ ^ 2 = u ⬝ᵥ u := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [gauge, WithLp.ofLp_toLp, PiLp.toLp_apply, norm_mul, mul_pow,
    phase_norm, one_pow, one_mul, Complex.sq_norm, Complex.normSq_apply]
  simp [dotProduct, Fin.sum_univ_succ, pow_two]
  ring

theorem gram_eval (a : Fin 4 → ℝ) :
    a ⬝ᵥ (gram *ᵥ a) = ‖(tangentEquiv a : State)‖ ^ 2 := by
  rw [gram_eq, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  exact (gauge_norm_sq (basisMatrix *ᵥ a)).symm

theorem zeroQ_eq (i : Fin 5) : zeroQ i = phaseForm (zeroIndex i).1 (zeroIndex i).2 := by
  fin_cases i
  · exact zeroQ_0_eq
  · exact zeroQ_1_eq
  · exact zeroQ_2_eq
  · exact zeroQ_3_eq
  · exact zeroQ_4_eq

private theorem pullback_gradient : pullback gradient =
    ∑ qp ∈ (Finset.univ \ zeroPoints),
      (SignType.sign (wigner psi qp.1 qp.2) : ℝ) • phaseForm qp.1 qp.2 := by
  classical
  have hs (s : SignType) : (s : ℂ).re = (s : ℝ) ∧ (s : ℂ).im = 0 := by
    cases s <;> norm_num
  rw [gradient_restricted]
  ext i j
  simp only [phaseForm, pullback, sum_mulVec, dotProduct_sum, smul_mulVec, dotProduct_smul,
    Complex.re_sum, Finset.sum_div, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Complex.mul_re, hs, mul_zero, zero_mul, sub_zero, mul_div_assoc]

theorem base_eq : base =
    (∑ qp ∈ (Finset.univ \ zeroPoints),
      (SignType.sign (wigner psi qp.1 qp.2) : ℝ) • phaseForm qp.1 qp.2) -
      lOne psi • gram := by
  rw [base_eq_gradient, pullback_gradient]

#print axioms signs_eq
#print axioms zeroIndex_image
#print axioms gram_eq
#print axioms zeroQ_0_eq
#print axioms zeroQ_1_eq
#print axioms zeroQ_2_eq
#print axioms zeroQ_3_eq
#print axioms zeroQ_4_eq
#print axioms base_eq_gradient
#print axioms complexBasis_tangentEquiv
#print axioms phaseForm_realification
#print axioms phaseForm_eval
#print axioms gram_eval
#print axioms zeroQ_eq
#print axioms base_eq
end D5.S3.Quantum.Magic.QuquintCertificateBridge
