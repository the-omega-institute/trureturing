/- GID: D5/S3/Quantum/Entanglement/ChoiKiemKye/MaximalBirankEdgeStates
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/ChoiKiemKye/MaximalBirankEdgeStates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/Quantum/Entanglement/ChoiKiemKye/MaximalBirankEdgeStates.result; instance=D5/S3/Quantum/Entanglement/ChoiKiemKye/MaximalBirankEdgeStates.valid3
   digest: The CKK conjecture for all dimensions n ≥ 3. -/

/- Judgement form (implementation assessment; each helper retains its own classification).
   proof_shape: Small.certificate_sound: content; consumer=MaximalBirankEdgeStates.Small.case10; same-delivery-content=D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.proposition61.
   proof_shape: Small.valid3: bind-only; consumer=MaximalBirankEdgeStates.Small.case3.
   proof_shape: Small.valid4: bind-only; consumer=MaximalBirankEdgeStates.Small.case4.
   proof_shape: Small.valid5: bind-only; consumer=MaximalBirankEdgeStates.Small.case5.
   proof_shape: Small.valid6: bind-only; consumer=MaximalBirankEdgeStates.Small.case6.
   proof_shape: Small.valid7: bind-only; consumer=MaximalBirankEdgeStates.Small.case7.
   proof_shape: Small.valid8: bind-only; consumer=MaximalBirankEdgeStates.Small.case8.
   proof_shape: Small.valid9: bind-only; consumer=MaximalBirankEdgeStates.Small.case9.
   proof_shape: Small.valid10: bind-only; consumer=MaximalBirankEdgeStates.Small.case10.
   proof_shape: Small.valid11: bind-only; consumer=MaximalBirankEdgeStates.Small.case11.
   proof_shape: Small.valid12: bind-only; consumer=MaximalBirankEdgeStates.Small.case12.
   proof_shape: Small.valid13: bind-only; consumer=MaximalBirankEdgeStates.Small.case13.
   proof_shape: Small.valid14: bind-only; consumer=MaximalBirankEdgeStates.Small.case14.
   proof_shape: Small.valid15: bind-only; consumer=MaximalBirankEdgeStates.Small.case15.
   proof_shape: Small.valid16: bind-only; consumer=MaximalBirankEdgeStates.Small.case16.
   proof_shape: Full.construction: content; consumer=MaximalBirankEdgeStates.Full.result; same-delivery-content=D5.S3.Quantum.Entanglement.ChoiKiemKye.MaximalBirankEdgeStates.Small.case10.
   proof_shape: Full.result: content; same-delivery-content=D5.S3.Quantum.Entanglement.ChoiKiemKye.MaximalBirankEdgeStates.Full.construction.
   proof_shape: Finite.last_nonzero: bind-only; consumer=MaximalBirankEdgeStates.Finite.root_and_kernel_enclosure.
   escape_witness: Small.certificate_sound, via Finite.kernel_close on its residual-enclosure path.
   Classification totals: 21 content; 50 bind-only.
   admission_basis: open-problem-resolution (#13859; Proved)
   Direct frozen dependencies:
   D5/S3/Weil/ZetaLinear/Sylvester.hermForm; statement_id=sha256:80fb2c125caa6f180274d058b22d584cf1572b3089380febbc5dfae997f03ebf
   D5/S3/Weil/ZetaLinear/Sylvester.hermForm_sub; statement_id=sha256:6948d79f8bb85d326207469b5bfeb44953cc7d9bdb58c87fb967a4276fac4221
   Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformPerturbedParameters
import D5.S3.Weil.ZetaLinear.Sylvester

set_option Elab.async false

noncomputable section
namespace D5.S3.Quantum.Entanglement.ChoiKiemKye.MaximalBirankEdgeStates
open Matrix
open scoped ComplexConjugate ComplexOrder
namespace Certificates
set_option backward.isDefEq.respectTransparency false
def size (z : GaussianInt) : ℤ := |z.re| + |z.im|
def Dominant {n : ℕ} (A : Matrix (Fin n) (Fin n) GaussianInt) : Prop :=
  A.IsHermitian ∧ ∀ i, (∑ j ∈ Finset.univ.erase i, size (A i j)) < (A i i).re
instance instDecidableDominant {n : ℕ} (A : Matrix (Fin n) (Fin n) GaussianInt) : Decidable (Dominant A) := inferInstanceAs (Decidable (_ ∧ _))
private theorem norm_cast_le_size (z : GaussianInt) : ‖(z : ℂ)‖ ≤ (size z : ℝ) := by
  rw [GaussianInt.toComplex_def]
  calc ‖(z.re : ℂ) + (z.im : ℂ) * Complex.I‖ ≤ ‖(z.re : ℂ)‖ + ‖(z.im : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = (size z : ℝ) := by simp [size, norm_mul, Complex.norm_real, Real.norm_eq_abs, Int.cast_abs]
private theorem castMat_hermitian {n : ℕ} {A : Matrix (Fin n) (Fin n) GaussianInt} (h : A.IsHermitian) : ((fun A => Matrix.map A GaussianInt.toComplex) A).IsHermitian := by
  ext i j
  have hh := congrArg GaussianInt.toComplex (congrFun (congrFun h i) j)
  simpa [Matrix.map, Matrix.conjTranspose_apply, GaussianInt.toComplex_star] using hh
private theorem dominant_posDef {n : ℕ} {A : Matrix (Fin n) (Fin n) GaussianInt} (h : Dominant A) : ((fun A => Matrix.map A GaussianInt.toComplex) A).PosDef := by
  apply D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Path.scaled_dominance_posDef (castMat_hermitian h.1) (fun _ => 1) (by simp)
  intro i
  simp only [inv_one, one_mul, mul_one]
  calc (∑ j ∈ Finset.univ.erase i, ‖(fun A => Matrix.map A GaussianInt.toComplex) A i j‖) ≤ ∑ j ∈ Finset.univ.erase i, (size (A i j) : ℝ) :=
        Finset.sum_le_sum fun j _ => norm_cast_le_size _
    _ < ((fun A => Matrix.map A GaussianInt.toComplex) A i i).re := by
      change (∑ j ∈ Finset.univ.erase i, (size (A i j) : ℝ)) < ((A i i : GaussianInt) : ℂ).re
      rw [← GaussianInt.intCast_re]
      exact_mod_cast h.2 i

private theorem castMat_star {m n : ℕ} (A : Matrix (Fin m) (Fin n) GaussianInt) : (fun A => Matrix.map A GaussianInt.toComplex) Aᴴ = ((fun A => Matrix.map A GaussianInt.toComplex) A)ᴴ := by
  ext i j
  simp [Matrix.map, Matrix.conjTranspose_apply, GaussianInt.toComplex_star]
private theorem upper_isUnit {n : ℕ} {C : Matrix (Fin n) (Fin n) GaussianInt}
    (ht : C.IsUpperTriangular) (hd : ∀ i, C i i ≠ 0) : IsUnit ((fun A => Matrix.map A GaussianInt.toComplex) C) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, Matrix.det_of_isUpperTriangular]
  · exact Finset.prod_ne_zero_iff.mpr fun i _ => GaussianInt.toComplex_eq_zero.not.mpr (hd i)
  · intro i j hij
    change (C i j : ℂ) = 0
    rw [ht hij, GaussianInt.toComplex_zero]
private theorem congruence_posDef {n : ℕ} {A C : Matrix (Fin n) (Fin n) GaussianInt}
    (ht : C.IsUpperTriangular) (hd : ∀ i, C i i ≠ 0) (hc : Dominant (Cᴴ * A * C)) :
    ((fun A => Matrix.map A GaussianInt.toComplex) A).PosDef := by
  have hC := upper_isUnit ht hd
  letI := hC.invertible
  have h := (dominant_posDef hc).conjTranspose_mul_mul_same
    (B := ((fun A => Matrix.map A GaussianInt.toComplex) C)⁻¹) (Matrix.mulVec_injective_of_invertible _)
  simp only [Matrix.map_mul, castMat_star] at h
  have he : (((fun A => Matrix.map A GaussianInt.toComplex) C)⁻¹)ᴴ * (((fun A => Matrix.map A GaussianInt.toComplex) C)ᴴ * (fun A => Matrix.map A GaussianInt.toComplex) A * (fun A => Matrix.map A GaussianInt.toComplex) C) * ((fun A => Matrix.map A GaussianInt.toComplex) C)⁻¹ = (fun A => Matrix.map A GaussianInt.toComplex) A := by
    rw [Matrix.conjTranspose_nonsing_inv]
    letI := (show IsUnit ((fun A => Matrix.map A GaussianInt.toComplex) C)ᴴ by simpa using hC).invertible
    simp [Matrix.mul_assoc, Matrix.inv_mul_of_invertible, Matrix.mul_inv_of_invertible]
  rwa [he] at h
end Certificates
#print axioms Certificates.congruence_posDef


open Matrix
open scoped ComplexConjugate ComplexOrder InnerProductSpace
namespace Finite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private theorem energy_eq_inner {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ) :
    RHLinalg.hermForm A v = (⟪(WithLp.toLp 2) v, Matrix.toEuclideanCLM (𝕜 := ℂ) A ((WithLp.toLp 2) v)⟫_ℂ).re := by
  rw [Matrix.toEuclideanCLM_toLp]
  simp [RHLinalg.hermForm, WithLp.toLp, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
private theorem energy_shift {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ) (t : ℝ) :
    RHLinalg.hermForm (A + (t : ℂ) • 1) v = RHLinalg.hermForm A v + t * ‖(WithLp.toLp 2) v‖^2 := by
  change (star v ⬝ᵥ (A + (t : ℂ) • 1) *ᵥ v).re = (star v ⬝ᵥ A *ᵥ v).re + t * ‖WithLp.toLp 2 v‖^2
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_add, dotProduct_smul, smul_eq_mul, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have he : (star v ⬝ᵥ v).re = ‖(WithLp.toLp 2) v‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    change (star v ⬝ᵥ v).re=∑ i,‖v i‖^2
    simp only [dotProduct, Pi.star_apply]
    change Complex.reAddGroupHom (∑ i,star (v i)*v i)=_
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply,Complex.mul_re,Complex.conj_re,Complex.conj_im,pow_two]
  rw [he]
private theorem leading_shift {m : ℕ} (A : Matrix (Fin (m+1)) (Fin (m+1)) ℂ) (t : ℝ) :
    (fun A => Matrix.submatrix A Fin.castSucc Fin.castSucc) (A + (t : ℂ) • 1) = (fun A => Matrix.submatrix A Fin.castSucc Fin.castSucc) A + (t : ℂ) • 1 := by
  ext i j
  simp [Matrix.submatrix_apply, Matrix.one_apply]
private theorem energy_bound {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ) :
    |RHLinalg.hermForm A v| ≤ ‖(WithLp.toLp 2) v‖ * ‖(WithLp.toLp 2) (A *ᵥ v)‖ := by
  rw [energy_eq_inner, Matrix.toEuclideanCLM_toLp]
  exact (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)

private theorem leading_mul_zero {m : ℕ} (A : Matrix (Fin (m+1)) (Fin (m+1)) ℂ)
    (v : Fin (m+1) → ℂ) (hv : v (Fin.last m) = 0) :
    (fun A => Matrix.submatrix A Fin.castSucc Fin.castSucc) A *ᵥ (v ∘ Fin.castSucc) = (A *ᵥ v) ∘ Fin.castSucc := by
  ext i
  simp [Matrix.submatrix_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hv]
private theorem last_nonzero {m : ℕ} {A : Matrix (Fin (m+1)) (Fin (m+1)) ℂ}
    (hA : ((fun A => Matrix.submatrix A Fin.castSucc Fin.castSucc) A).PosDef) {v : Fin (m+1) → ℂ} (hv : A *ᵥ v = 0) (hne : v ≠ 0) : v (Fin.last m) ≠ 0 := by
  intro hz
  have hk : (fun A => Matrix.submatrix A Fin.castSucc Fin.castSucc) A *ᵥ (v ∘ Fin.castSucc) = 0 := by rw [leading_mul_zero A v hz, hv]; rfl
  have hzero : v ∘ Fin.castSucc = 0 := Matrix.mulVec_injective_of_isUnit hA.isUnit (hk.trans (Matrix.mulVec_zero _).symm)
  apply hne
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact hz
  · exact congrFun hzero j
private theorem norm_leading {m : ℕ} (v : Fin (m+1) → ℂ) : ‖(WithLp.toLp 2) (v ∘ Fin.castSucc)‖ ≤ ‖(WithLp.toLp 2) v‖ := by
  have h : ‖(WithLp.toLp 2) (v ∘ Fin.castSucc)‖^2 ≤ ‖(WithLp.toLp 2) v‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq, WithLp.toLp]
    change (∑ i : Fin m, ‖v i.castSucc‖^2) ≤ ∑ i : Fin (m+1), ‖v i‖^2
    rw [Fin.sum_univ_castSucc]
    exact le_add_of_nonneg_right (sq_nonneg _)
  nlinarith [norm_nonneg ((WithLp.toLp 2) (v ∘ Fin.castSucc)), norm_nonneg ((WithLp.toLp 2) v)]
private theorem norm_eq_leading {m : ℕ} (v : Fin (m+1) → ℂ) (hv : v (Fin.last m) = 0) : ‖(WithLp.toLp 2) v‖ = ‖(WithLp.toLp 2) (v ∘ Fin.castSucc)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.norm_sq_eq, WithLp.toLp, Fin.sum_univ_castSucc, hv]
private theorem shift_posDef {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (hA : A.PosDef) (t : ℝ) (ht : 0 ≤ t) :
    (A + (t : ℂ) • 1).PosDef := hA.add_posSemidef (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr ht))
private theorem kernel_close {m : ℕ} {A : Matrix (Fin (m+1)) (Fin (m+1)) ℂ}
    (hA : ((fun A => Matrix.submatrix A Fin.castSucc Fin.castSucc) A - (1/2 : ℂ) • 1).PosSemidef)
    (w v : Fin (m+1) → ℂ) (hw : A *ᵥ w = 0)
    (hlast : w (Fin.last m) = v (Fin.last m)) :
    ‖(WithLp.toLp 2) (w-v)‖ ≤ 2 * ‖(WithLp.toLp 2) (A *ᵥ v)‖ := by
  let z := w-v
  have hzlast : z (Fin.last m) = 0 := by simp [z, hlast]
  have hmul : (fun A => Matrix.submatrix A Fin.castSucc Fin.castSucc) A *ᵥ (z ∘ Fin.castSucc) = -((A *ᵥ v) ∘ Fin.castSucc) := by
    rw [leading_mul_zero A z hzlast]
    ext i
    simp [z, Matrix.mulVec_sub, hw]
  have hlo : (1/2 : ℝ) * ‖(WithLp.toLp 2) (z ∘ Fin.castSucc)‖^2 ≤ RHLinalg.hermForm ((fun A => Matrix.submatrix A Fin.castSucc Fin.castSucc) A) (z ∘ Fin.castSucc) := by
    have h := hA.re_dotProduct_nonneg (z ∘ Fin.castSucc)
    have he : (fun A => Matrix.submatrix A Fin.castSucc Fin.castSucc) A - (1/2 : ℂ) • 1 = (fun A => Matrix.submatrix A Fin.castSucc Fin.castSucc) A + ((-1/2 : ℝ) : ℂ) • 1 := by push_cast; module
    change 0 ≤ RHLinalg.hermForm ((fun A => Matrix.submatrix A Fin.castSucc Fin.castSucc) A - (1/2 : ℂ) • 1) (z ∘ Fin.castSucc) at h
    rw [he, energy_shift] at h
    linarith
  have hupper := (le_abs_self (RHLinalg.hermForm ((fun A => Matrix.submatrix A Fin.castSucc Fin.castSucc) A) (z ∘ Fin.castSucc))).trans (energy_bound _ _)
  rw [hmul] at hupper
  have hnormneg : ‖(WithLp.toLp 2) (-((A *ᵥ v) ∘ Fin.castSucc))‖ = ‖(WithLp.toLp 2) ((A *ᵥ v) ∘ Fin.castSucc)‖ := by
    change ‖-(WithLp.toLp 2) ((A *ᵥ v) ∘ Fin.castSucc)‖ = _
    exact norm_neg _
  rw [hnormneg] at hupper
  have h := hupper.trans (mul_le_mul_of_nonneg_left (norm_leading (A *ᵥ v)) (norm_nonneg _))
  have hnorm := norm_eq_leading z hzlast
  change ‖(WithLp.toLp 2) z‖ ≤ _
  rw [hnorm]
  nlinarith [norm_nonneg ((WithLp.toLp 2) (z ∘ Fin.castSucc)), norm_nonneg ((WithLp.toLp 2) (A *ᵥ v))]
private theorem entry_norm_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ)
    (hε : 0 ≤ ε) (hA : ∀ i j, ‖A i j‖ ≤ ε) : (norm ∘ (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))) A ≤ n * ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact D5.S3.SpectralTopology.HermitianEigenvaluePerturbation.norm_toEuclideanLin_le_of_entry_le hA
private theorem energy_opNorm_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    |RHLinalg.hermForm A v| ≤ (norm ∘ (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))) A * ‖(WithLp.toLp 2) v‖^2 := by
  have h := energy_bound A v
  have hb : ‖(WithLp.toLp 2) (A *ᵥ v)‖ ≤ (norm ∘ (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))) A * ‖(WithLp.toLp 2) v‖ := by
    simpa [WithLp.toLp, Function.comp_apply, Matrix.toEuclideanCLM_toLp] using
      (Matrix.toEuclideanCLM (𝕜 := ℂ) A).le_opNorm ((WithLp.toLp 2) v)
  exact h.trans ((mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans_eq (by ring))
private theorem lower_energy {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ)
    (hB : (B-(δ:ℂ) • 1).PosSemidef) (v : Fin n → ℂ) : δ*‖(WithLp.toLp 2) v‖^2 ≤ RHLinalg.hermForm B v := by
  have h := hB.re_dotProduct_nonneg v
  have he : B-(δ:ℂ) • 1 = B+((-δ:ℝ):ℂ) • 1 := by push_cast; module
  change 0≤RHLinalg.hermForm (B-(δ:ℂ) • 1) v at h
  rw [he, energy_shift] at h
  linarith
private theorem posDef_of_approx {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (δ ε : ℝ)
    (hA : A.IsHermitian) (hB : (B-(δ:ℂ) • 1).PosSemidef)
    (herror : (norm ∘ (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ))) (A-B) ≤ ε) (hsmall : ε<δ) : A.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hA
  intro v hv
  have hlow := lower_energy B δ hB v
  have hdiff := energy_opNorm_bound (A-B) v
  rw [RHLinalg.hermForm_sub] at hdiff
  have he := (abs_le.mp (hdiff.trans (mul_le_mul_of_nonneg_right herror (sq_nonneg _)))).1
  have hnv : (WithLp.toLp 2) v ≠ 0 := by intro h; apply hv; simpa [WithLp.toLp] using congrArg WithLp.ofLp h
  have hpos : 0 < ‖(WithLp.toLp 2) v‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hnv)
  have hprod := mul_pos (sub_pos.mpr hsmall) hpos
  have hreal : 0 < RHLinalg.hermForm A v := by nlinarith
  exact Complex.pos_iff.mpr ⟨hreal, (hA.im_star_dotProduct_mulVec_self v).symm⟩
private theorem root_and_kernel_enclosure {m : ℕ} (hn : 3≤ m+1) (a b : Fin (m+1) → ℂ)
    (R : ℝ) (v : Fin (m+1) → ℂ) (hR : 1<R-1/1000000)
    (hupper : (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b (R+1/1000000)).PosDef)
    (hlower : ((fun A => Matrix.submatrix A Fin.castSucc Fin.castSucc) (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b (R-1/1000000))-(1/2:ℂ) • 1).PosSemidef)
    (hvlast : v (Fin.last m)=1) (hvnorm : ‖(WithLp.toLp 2) v‖≤4)
    (hvres : ‖(WithLp.toLp 2) (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b R *ᵥ v)‖≤1/10000000) :
    ∃ (r : ℝ) (w : Fin (m+1) → ℂ), 1<r ∧ R-1/1000000<r ∧ r<R+1/1000000 ∧
      D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.LargestRoot a b r ∧ D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.SimpleRoot a b r ∧ w≠0 ∧ D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b r *ᵥ w=0 ∧
      w (Fin.last m)=1 ∧ ‖(WithLp.toLp 2) (w-v)‖≤1/100000 := by
  let H := -D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b 0
  let hH : H.IsHermitian := (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D_hermitian hn a b 0).neg
  let k : Fin (Fintype.card (Fin (m+1))) := ⟨0,by simp⟩
  let r := hH.eigenvalues₀ k
  have hr : D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.LargestRoot a b r := by
    simpa only [D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.LargestRoot,←D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D_pencil,H,r,k] using D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.pencil_top_largest (by omega : 0< m+1) hH
  have hpsd := D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformPerturbedParameters.Anchor.largest_root_psd hn a b hr
  have hvone : 1≤‖(WithLp.toLp 2) v‖ := by
    have h := PiLp.norm_apply_le ((WithLp.toLp 2) v) (Fin.last m)
    simpa [WithLp.toLp,hvlast] using h
  have hnegative : RHLinalg.hermForm (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b (R-1/1000000)) v<0 := by
    rw [D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformPerturbedParameters.Anchor.D_shift a b R (R-1/1000000),energy_shift]
    have he := (le_abs_self (RHLinalg.hermForm (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b R) v)).trans (energy_bound _ _)
    have hb := mul_le_mul hvnorm hvres (norm_nonneg _) (by norm_num : (0:ℝ)≤4)
    nlinarith
  have hlow : R-1/1000000<r := by
    by_contra h
    have hle : r≤R-1/1000000 := le_of_not_gt h
    have h := hpsd.add (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr (by linarith : 0 ≤ R-1/1000000-r)))
    rw [←D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformPerturbedParameters.Anchor.D_shift] at h
    exact (not_lt_of_ge (h.re_dotProduct_nonneg v)) hnegative
  have hup : r<R+1/1000000 := by
    by_contra h
    have hle : R+1/1000000≤r := le_of_not_gt h
    have hpd := shift_posDef _ hupper (r-(R+1/1000000)) (by linarith)
    rw [←D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformPerturbedParameters.Anchor.D_shift] at hpd
    have hnz := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit)
    exact hnz hr.1
  have hleading : ((fun A => Matrix.submatrix A Fin.castSucc Fin.castSucc) (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b r)-(1/2:ℂ) • 1).PosSemidef := by
    have h := hlower.add (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr (by linarith : 0 ≤ r-(R-1/1000000))))
    have he : (fun A => Matrix.submatrix A Fin.castSucc Fin.castSucc) (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b r)-(1/2:ℂ) • 1 =
        ((fun A => Matrix.submatrix A Fin.castSucc Fin.castSucc) (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b (R-1/1000000))-(1/2:ℂ) • 1)+((r-(R-1/1000000):ℝ):ℂ) • 1 := by
      rw [D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformPerturbedParameters.Anchor.D_shift a b (R-1/1000000) r,leading_shift]
      module
    rwa [←he] at h
  have hleadpd : ((fun A => Matrix.submatrix A Fin.castSucc Fin.castSucc) (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b r)).PosDef := by
    have h := Matrix.PosDef.posSemidef_add hleading (Matrix.PosDef.one.smul (show (0:ℂ)<(1/2:ℂ) by norm_num [Complex.pos_iff]))
    have he : ((fun A => Matrix.submatrix A Fin.castSucc Fin.castSucc) (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b r)-(1/2:ℂ) • 1)+(1/2:ℂ) • 1 = (fun A => Matrix.submatrix A Fin.castSucc Fin.castSucc) (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b r) := by module
    rwa [he] at h
  let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
  let Q := hT.eigenvectorBasis finrank_euclideanSpace k
  let u := WithLp.ofLp Q
  have hQ : ‖Q‖=1 := (hT.eigenvectorBasis finrank_euclideanSpace).orthonormal.norm_eq_one k
  have hu : u≠0 := by
    intro h
    have hh : Q=0 := WithLp.ofLp_injective 2 h
    rw [hh,norm_zero] at hQ
    norm_num at hQ
  have hku : D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b r *ᵥ u=0 := by
    have heig : Matrix.toEuclideanCLM (𝕜:=ℂ) H Q=(r:ℂ) • Q := hT.apply_eigenvectorBasis finrank_euclideanSpace k
    have hh : Matrix.toEuclideanCLM (𝕜:=ℂ) (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b r) Q=0 := by
      rw [D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D_pencil]
      change Matrix.toEuclideanCLM (𝕜:=ℂ) (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Spectral.pencil H r) Q=0
      simp only [D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Spectral.pencil,map_sub,map_smul,map_one,ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply,ContinuousLinearMap.one_apply,heig,r,sub_self]
    simpa only [Matrix.ofLp_toEuclideanCLM,WithLp.ofLp_zero] using congrArg WithLp.ofLp hh
  have hlast := last_nonzero hleadpd hku hu
  let w := (u (Fin.last m))⁻¹ • u
  have hw : D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b r *ᵥ w=0 := by simp [w,Matrix.mulVec_smul,hku]
  have hwlast : w (Fin.last m)=1 := by simp [w,hlast]
  have hwne : w≠0 := by intro h; have hh := congrFun h (Fin.last m); rw [hwlast] at hh; norm_num at hh
  have hrank : (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b r).rank=m := by
    have hlo := Matrix.rank_submatrix_le (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b r) Fin.castSucc Fin.castSucc
    change ((fun A => Matrix.submatrix A Fin.castSucc Fin.castSucc) (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b r)).rank≤(D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b r).rank at hlo
    rw [Matrix.rank_of_isUnit _ hleadpd.isUnit,Fintype.card_fin] at hlo
    have hker : 0<Module.finrank ℂ (LinearMap.ker (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b r).mulVecLin) :=
      Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨u, by simpa [LinearMap.mem_ker] using hku⟩, by
        intro hh; exact hu (congrArg Subtype.val hh)⟩
    have ht := (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b r).mulVecLin.finrank_range_add_finrank_ker
    change (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b r).rank+Module.finrank ℂ (LinearMap.ker (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b r).mulVecLin)=Module.finrank ℂ (Fin (m+1)→ℂ) at ht
    simp only [Module.finrank_pi,Fintype.card_fin] at ht
    omega
  have hsimple : D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.SimpleRoot a b r := by
    have hh := D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.simple_root_of_rank (by omega : 0< m+1) hH
      (by simpa only [←D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D_pencil,H] using hr.1)
      (by simpa only [←D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D_pencil,H,Nat.add_sub_cancel] using hrank)
    simpa only [D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.SimpleRoot,←D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D_pencil,H] using hh
  have hdist : |r-R|≤1/1000000 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hres : ‖(WithLp.toLp 2) (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b r *ᵥ v)‖≤1/10000000+4/1000000 := by
    rw [D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformPerturbedParameters.Anchor.D_shift a b R r,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec]
    change ‖(WithLp.toLp 2) (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b R *ᵥ v)+((r-R:ℝ):ℂ) • (WithLp.toLp 2) v‖≤_
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
    have hm := mul_le_mul hdist hvnorm (norm_nonneg _) (by norm_num : (0:ℝ)≤1/1000000)
    linarith
  have hclose := kernel_close hleading w v hw (hwlast.trans hvlast.symm)
  exact ⟨r,w,by linarith,hlow,hup,hr,hsimple,hwne,hw,hwlast,by linarith⟩
end Finite
#print axioms Finite.kernel_close

#print axioms Finite.root_and_kernel_enclosure


open Matrix
open scoped ComplexConjugate ComplexOrder
namespace Small
set_option backward.isDefEq.respectTransparency false
abbrev den : ℤ := 1000000000000
abbrev phaseInt : GaussianInt := ⟨707106781187,707106781187⟩
def alphaInt (n : ℕ) (i : Fin n) : GaussianInt := if i.val=0 then den else if i.val+1=n then -den else phaseInt
private def alpha0 (n : ℕ) (i : Fin n) : ℂ := (alphaInt n i : ℂ)/(den:ℂ)
def matrixInt (n : ℕ) (Rnum : ℤ) : Matrix (Fin n) (Fin n) GaussianInt := fun i j =>
  if i=j then Rnum*den else
  if i.val=0 then (if j.val=2 then 2 else 1)*star (alphaInt n j)*den else
  if j.val=0 then (if i.val=2 then 2 else 1)*alphaInt n i*den else
  if j.val+1=n then (if i.val+3=n then 2 else 1)*(den*den) else
  if i.val+1=n then (if j.val+3=n then 2 else 1)*(den*den) else
  if i.val+1=j.val ∨ j.val+1=i.val ∨ i.val+2=j.val ∨ j.val+2=i.val then
    if i.val+j.val+1≤n then alphaInt n i*star (alphaInt n j) else den*den else 0
set_option maxHeartbeats 1000000 in
private theorem matrixInt_scale (n : ℕ) (Rnum : ℤ) : (fun A => Matrix.map A GaussianInt.toComplex) (matrixInt n Rnum) =
    ((den:ℂ)^2) • (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (alpha0 n) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta n) ((Rnum:ℝ)/den)) := by
  ext i j
  simp only [Matrix.map_apply, matrixInt,  D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D, alpha0, D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta,
    Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp [GaussianInt.toComplex_mul,GaussianInt.toComplex_star,GaussianInt.toComplex_def,
    map_mul,map_neg,map_ofNat,map_intCast,map_div₀,Complex.conj_ofReal,Complex.ofReal_div] <;> field_simp <;> ring
private theorem anchor_phase_error : ‖D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor.a - ((phaseInt:ℂ)/(den:ℂ))‖ ≤ 1/100000000000 := by
  have hs := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hp := Real.sqrt_nonneg 2
  have hl : 1414213562372/1000000000000 ≤ Real.sqrt 2 := by nlinarith
  have hu : Real.sqrt 2 ≤ 1414213562374/1000000000000 := by nlinarith
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor.a_cartesian]
  norm_num [D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.s2,
    phaseInt,den,GaussianInt.toComplex_def,Complex.div_re,Complex.div_im,
    Complex.mul_re,Complex.mul_im,Complex.normSq,Complex.sub_re,Complex.sub_im]
  rw [abs_of_nonpos (by linarith : Real.sqrt 2/2-707106781187/1000000000000≤0)]
  linarith
private theorem anchor_alpha_error {n : ℕ} (hn : 3≤n) (i : Fin n) :
    ‖D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha n i-alpha0 n i‖ ≤ 1/100000000000 := by
  unfold D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha alpha0 alphaInt
  split_ifs
  · norm_num [den,GaussianInt.toComplex_def]
  · norm_num [den,GaussianInt.toComplex_def]
  · rw [D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Anchor.phase_def]
    exact anchor_phase_error
private theorem alpha_error {n : ℕ} (hn : 3≤n) (i : Fin n) :
    ‖D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha n i-alpha0 n i‖ ≤ 1/10000000000 := by
  have ha := D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha_anchor_distance hn i
  have hbase := anchor_alpha_error hn i
  have hnr : (3:ℝ)≤n := by exact_mod_cast hn
  have hn5 : (243:ℝ) ≤ (n:ℝ)^5 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3) hnr 5]
  have hnum : Real.pi*n*D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.epsilon n ≤ 4/(1000000000*(n:ℝ)^5) := by
    unfold D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.epsilon
    have hnz : (n:ℝ)≠0 := by positivity
    have he : Real.pi*n*(1/(1000000000*(n:ℝ)^6)) = Real.pi/(1000000000*(n:ℝ)^5) := by field_simp <;> ring
    rw [he]
    exact div_le_div_of_nonneg_right Real.pi_le_four (by positivity)
  have hsmall : Real.pi*n*D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.epsilon n ≤ 4/(1000000000*243) := hnum.trans (by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith))
  calc _ ≤ ‖D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha n i-D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha n i‖+‖D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.anchorAlpha n i-alpha0 n i‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by linarith
private theorem alpha0_norm_le {n : ℕ} (hn : 3≤n) (i : Fin n) : ‖alpha0 n i‖ ≤ 2 := by
  calc ‖alpha0 n i‖ ≤ ‖D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha n i‖+‖D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha n i-alpha0 n i‖ := by
        simpa [norm_sub_rev] using norm_le_insert (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha n i) (alpha0 n i)
    _ ≤ 2 := by rw [D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha_norm]; linarith [alpha_error hn i]
set_option maxHeartbeats 1000000 in
private theorem matrix_entry_error {n : ℕ} (hn : 3≤n) (i j : Fin n) (r : ℝ) :
    ‖D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha n) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta n) r i j-(D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (alpha0 n) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta n) r) i j‖ ≤ 1/1000000000 := by
  have hi := alpha_error hn i
  have hj := alpha_error hn j
  have hp : (0:ℝ) ≤ 1/1000000000 := by norm_num
  unfold D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D
  split_ifs
  all_goals try simpa using hp
  all_goals try (simpa only [one_mul, ←map_sub,Complex.norm_conj] using hj.trans (by norm_num))
  all_goals try (simpa only [one_mul] using hi.trans (by norm_num))
  all_goals try (simpa only [←mul_sub,norm_mul,Complex.norm_ofNat,←map_sub,Complex.norm_conj] using mul_le_mul_of_nonneg_left hj (by norm_num : (0:ℝ)≤2) |>.trans (by norm_num))
  all_goals try (simpa only [←mul_sub,norm_mul,Complex.norm_ofNat] using mul_le_mul_of_nonneg_left hi (by norm_num : (0:ℝ)≤2) |>.trans (by norm_num))
  all_goals try (simp [D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta]; norm_num)
  all_goals
    have hfactor : D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha n i*conj (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha n j)-alpha0 n i*conj (alpha0 n j) =
      D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha n i*conj (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha n j-alpha0 n j)+(D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha n i-alpha0 n i)*conj (alpha0 n j) := by simp [map_sub]; ring
    rw [hfactor]
    calc _ ≤ ‖D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha n i*conj (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha n j-alpha0 n j)‖+‖(D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha n i-alpha0 n i)*conj (alpha0 n j)‖ := norm_add_le _ _
      _ ≤ 1/10000000000+2*(1/10000000000) := by
        simp only [norm_mul,Complex.norm_conj,D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha_norm,one_mul]
        exact add_le_add hj (by nlinarith [mul_le_mul hi (alpha0_norm_le hn j) (norm_nonneg _) (by norm_num : (0:ℝ)≤1/10000000000)])
      _ ≤ _ := by norm_num
end Small


open Matrix
open scoped ComplexConjugate ComplexOrder
namespace Small
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev directionDen : ℤ := 1000000
private def rationalVector {n : ℕ} (d : ℤ) (v : Fin n → GaussianInt) : Fin n → ℂ := (d:ℂ)⁻¹ • (fun v => GaussianInt.toComplex ∘ v) v
private def rationalDirection (z : GaussianInt) : ℂ := (z:ℂ)/(directionDen:ℂ)
def lowerInt (m : ℕ) (Rnum : ℤ) : Matrix (Fin m) (Fin m) GaussianInt :=
  (matrixInt (m+1) (Rnum-1000000)).submatrix Fin.castSucc Fin.castSucc-(den*den:GaussianInt) • 1
def upperInt (m : ℕ) (Rnum : ℤ) : Matrix (Fin (m+1)) (Fin (m+1)) GaussianInt :=
  matrixInt (m+1) (Rnum+1000000)-(100000000000000000:GaussianInt) • 1
structure Data (m : ℕ) where
  Rnum : ℤ
  vector : Fin (m+1) → GaussianInt
  zAlpha : GaussianInt
  zBeta : GaussianInt
  zEnds : GaussianInt
  lowerC : Matrix (Fin m) (Fin m) GaussianInt
  upperC : Matrix (Fin (m+1)) (Fin (m+1)) GaussianInt
def Valid {m : ℕ} (d : Data m) : Prop :=
  den+1000000<d.Rnum ∧
  d.lowerC.IsUpperTriangular ∧ (∀ i,d.lowerC i i≠0) ∧
  Certificates.Dominant (d.lowerCᴴ * lowerInt m d.Rnum * d.lowerC) ∧
  d.upperC.IsUpperTriangular ∧ (∀ i,d.upperC i i≠0) ∧
  Certificates.Dominant (d.upperCᴴ * upperInt m d.Rnum * d.upperC) ∧
  d.vector (Fin.last m)=den ∧
  (∑ i,Zsqrtd.norm (d.vector i))≤16*den^2 ∧
  (∑ i,Certificates.size ((matrixInt (m+1) d.Rnum *ᵥ d.vector) i))≤den^3/100000000 ∧
  Zsqrtd.norm d.zAlpha≤4*directionDen^2 ∧ Zsqrtd.norm d.zBeta≤4*directionDen^2 ∧ Zsqrtd.norm d.zEnds≤4*directionDen^2 ∧
  (∀ i : Fin (m+1),i.val+1≠m+1→(d.zAlpha*(alphaInt (m+1) i*star (d.vector i))).re≥directionDen*den^2/10000) ∧
  (∀ i : Fin (m+1),i.val≠0→(d.zBeta*(den*star (d.vector i))).re≥directionDen*den^2/10000) ∧
  (∀ i : Fin (m+1),i.val=0 ∨ i.val+1=m+1→(d.zEnds*(alphaInt (m+1) i*star (d.vector i))).re≥directionDen*den^2/10000)
instance instDecidableValid {m : ℕ} (d : Data m) : Decidable (Valid d) := inferInstanceAs (Decidable (_ ∧ _))
private theorem cast_mass (z : GaussianInt) : ‖(z:ℂ)‖^2=(Zsqrtd.norm z:ℝ) := by
  rw [GaussianInt.intCast_real_norm, Complex.normSq_eq_norm_sq]
private theorem rationalVector_norm {n : ℕ} (d : ℤ) (hd : 0<d) (v : Fin n → GaussianInt)
    (hv : (∑ i,Zsqrtd.norm (v i))≤16*d^2) : ‖(WithLp.toLp 2) (rationalVector d v)‖≤4 := by
  have hs : ‖(WithLp.toLp 2) ((fun v => GaussianInt.toComplex ∘ v) v)‖^2≤16*(d:ℝ)^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ i,‖(v i:ℂ)‖^2)≤16*(d:ℝ)^2
    simp_rw [cast_mass]
    exact_mod_cast hv
  have hdR : 0<(d:ℝ) := by exact_mod_cast hd
  have hb : ‖(WithLp.toLp 2) ((fun v => GaussianInt.toComplex ∘ v) v)‖≤4*(d:ℝ) := by nlinarith [norm_nonneg ((WithLp.toLp 2) ((fun v => GaussianInt.toComplex ∘ v) v))]
  change ‖(d:ℂ)⁻¹ • (WithLp.toLp 2) ((fun v => GaussianInt.toComplex ∘ v) v)‖≤4
  rw [norm_smul,norm_inv,Complex.norm_intCast,abs_of_pos hdR,inv_mul_eq_div]
  exact (div_le_iff₀ hdR).mpr hb
private theorem euclidean_norm_le_sum {n : ℕ} (v : Fin n → ℂ) : ‖(WithLp.toLp 2) v‖≤∑ i,‖v i‖ := by
  have hs : (∑ i,‖v i‖^2)≤(∑ i,‖v i‖)^2 := by
    simpa using Finset.sum_sq_le_sq_sum_of_nonneg (s:=Finset.univ) (fun i (_ : i∈Finset.univ) => norm_nonneg (v i))
  have he : ‖(WithLp.toLp 2) v‖^2=∑ i,‖v i‖^2 := EuclideanSpace.norm_sq_eq _
  have hp : 0≤∑ i,‖v i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  nlinarith [norm_nonneg ((WithLp.toLp 2) v)]
private theorem rationalVector_l1 {n : ℕ} (d : ℤ) (hd : 0<d) (v : Fin n → GaussianInt) :
    ‖(WithLp.toLp 2) (rationalVector d v)‖≤(∑ i,Certificates.size (v i):ℤ)/(d:ℝ) := by
  have h := (euclidean_norm_le_sum ((fun v => GaussianInt.toComplex ∘ v) v)).trans (Finset.sum_le_sum fun i _ => Certificates.norm_cast_le_size (v i))
  have hdR : 0<(d:ℝ) := by exact_mod_cast hd
  change ‖(d:ℂ)⁻¹ • (WithLp.toLp 2) ((fun v => GaussianInt.toComplex ∘ v) v)‖≤_
  rw [norm_smul,norm_inv,Complex.norm_intCast,abs_of_pos hdR,inv_mul_eq_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) hdR.le
private theorem rationalDirection_norm (z : GaussianInt) (hz : Zsqrtd.norm z≤4*directionDen^2) : ‖rationalDirection z‖≤2 := by
  have hs : ‖(z:ℂ)‖^2≤4*(directionDen:ℝ)^2 := by rw [cast_mass]; exact_mod_cast hz
  have hn : ‖(z:ℂ)‖≤2*(directionDen:ℝ) := by
    norm_num [directionDen] at hs ⊢
    nlinarith [norm_nonneg (z:ℂ)]
  rw [rationalDirection,norm_div]
  norm_num [directionDen] at hn ⊢
  linarith
private theorem castMat_sub_scalar {n : ℕ} (A : Matrix (Fin n) (Fin n) GaussianInt) (t : GaussianInt) :
    (fun A => Matrix.map A GaussianInt.toComplex) (A-t • 1)=(fun A => Matrix.map A GaussianInt.toComplex) A-(t:ℂ) • 1 := by
  ext i j
  by_cases hij : i=j <;> simp [Matrix.map,Matrix.one_apply,hij,GaussianInt.toComplex_sub,GaussianInt.toComplex_mul]
private theorem lower_scale (m : ℕ) (Rnum : ℤ) : (fun A => Matrix.map A GaussianInt.toComplex) (lowerInt m Rnum)=((den:ℂ)^2) •
    ((fun A => Matrix.submatrix A Fin.castSucc Fin.castSucc) ((D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (alpha0 (m+1)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+1)) ((Rnum:ℝ)/den-1/1000000)))-1) := by
  rw [lowerInt,castMat_sub_scalar]
  have he : (fun A => Matrix.map A GaussianInt.toComplex) ((matrixInt (m+1) (Rnum-1000000)).submatrix Fin.castSucc Fin.castSucc)=
    ((fun A => Matrix.map A GaussianInt.toComplex) (matrixInt (m+1) (Rnum-1000000))).submatrix Fin.castSucc Fin.castSucc := rfl
  rw [he,matrixInt_scale]
  ext i j
  have hr : ((Rnum-1000000:ℤ):ℝ)/den=(Rnum:ℝ)/den-1/1000000 := by push_cast; norm_num [den]; ring
  rw [hr]
  simp [Matrix.submatrix_apply,Matrix.one_apply,den,smul_eq_mul,mul_sub,GaussianInt.toComplex_def]
  split_ifs <;> norm_num
private theorem upper_scale (m : ℕ) (Rnum : ℤ) : (fun A => Matrix.map A GaussianInt.toComplex) (upperInt m Rnum)=((den:ℂ)^2) •
    ((D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (alpha0 (m+1)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+1)) ((Rnum:ℝ)/den+1/1000000))-(1/10000000:ℂ) • 1) := by
  rw [upperInt,castMat_sub_scalar,matrixInt_scale]
  have hr : ((Rnum+1000000:ℤ):ℝ)/den=(Rnum:ℝ)/den+1/1000000 := by push_cast; norm_num [den]; ring
  rw [hr]
  ext i j
  simp [Matrix.one_apply,den,smul_eq_mul,mul_sub,GaussianInt.toComplex_def]
  split_ifs <;> norm_num
private theorem unscale_posDef {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : (((den:ℂ)^2) • A).PosDef) : A.PosDef := by
  have h := hA.smul (show (0:ℂ)<(((den:ℂ)^2)⁻¹) by norm_num [den,Complex.pos_iff])
  simpa [smul_smul,den] using h
private theorem cast_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) GaussianInt) (v : Fin n → GaussianInt) :
    (fun v => GaussianInt.toComplex ∘ v) (A *ᵥ v)=(fun A => Matrix.map A GaussianInt.toComplex) A *ᵥ (fun v => GaussianInt.toComplex ∘ v) v := by
  ext i
  simp [Function.comp_apply,Matrix.map,Matrix.mulVec,dotProduct,map_sum,GaussianInt.toComplex_mul]
private theorem residual_scale {m : ℕ} (d : Data m) : (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (alpha0 (m+1)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+1)) ((d.Rnum:ℝ)/den)) *ᵥ rationalVector den d.vector=
    rationalVector (den^3) (matrixInt (m+1) d.Rnum *ᵥ d.vector) := by
  rw [rationalVector,Matrix.mulVec_smul,rationalVector,cast_mulVec,matrixInt_scale,Matrix.smul_mulVec]
  simp only [smul_smul]
  congr 1
  norm_num [den]
private theorem projection_integer {n : ℕ} (z : GaussianInt) (c v : Fin n → GaussianInt) (i : Fin n)
    (h : (z*(c i*star (v i))).re≥directionDen*den^2/10000) :
    1/10000≤(rationalDirection z*((c i:ℂ)/(den:ℂ)*conj (rationalVector den v i))).re := by
  have he : (rationalDirection z*((c i:ℂ)/(den:ℂ)*conj (rationalVector den v i))).re=
      ((z*(c i*star (v i))).re:ℝ)/((directionDen:ℝ)*(den:ℝ)^2) := by
    have hc := GaussianInt.intCast_re (z*(c i*star (v i)))
    rw [GaussianInt.toComplex_mul,GaussianInt.toComplex_mul,GaussianInt.toComplex_star] at hc
    simp only [rationalDirection,rationalVector,Pi.smul_apply,smul_eq_mul,Function.comp_apply,
      map_mul,map_inv₀,map_intCast]
    have hf : (z:ℂ)/(directionDen:ℂ)*((c i:ℂ)/(den:ℂ)*((den:ℂ)⁻¹*conj (v i:ℂ))) =
        ((z:ℂ)*((c i:ℂ)*conj (v i:ℂ)))/((directionDen:ℂ)*(den:ℂ)^2) := by field_simp <;> ring
    rw [hf]
    norm_num [directionDen,den,Complex.div_re,Complex.div_im,Complex.normSq] at ⊢
    nlinarith [hc]
  rw [he]
  have hint : directionDen*den^2/10000≤(z*(c i*star (v i))).re := h
  have hr : (((directionDen*den^2/10000:ℤ):ℝ))≤((z*(c i*star (v i))).re:ℝ) := by exact_mod_cast hint
  norm_num [directionDen,den] at hr ⊢
  linarith
private theorem positive_projection {n : ℕ} (c c₀ w v : Fin n → ℂ) (z : ℂ) (i : Fin n)
    (hz : ‖z‖≤2) (hc : ‖c i‖=1) (hv : ‖(WithLp.toLp 2) v‖≤4)
    (hclose : ‖(WithLp.toLp 2) (w-v)‖≤1/100000)
    (hphase : ‖c i-c₀ i‖≤1/10000000000)
    (hmargin : 1/10000≤(z*(c₀ i*conj (v i))).re) : 0<(z*(c i*conj (w i))).re := by
  have hvi : ‖v i‖≤4 := (PiLp.norm_apply_le ((WithLp.toLp 2) v) i).trans hv
  have hwi : ‖w i-v i‖≤1/100000 := (PiLp.norm_apply_le ((WithLp.toLp 2) (w-v)) i).trans hclose
  have hfactor : c i*conj (w i)-c₀ i*conj (v i)=c i*conj (w i-v i)+(c i-c₀ i)*conj (v i) := by simp [map_sub]; ring
  have hd : |(z*(c i*conj (w i))).re-(z*(c₀ i*conj (v i))).re|≤2*(1/100000+4/10000000000) := by
    calc _ = |(z*(c i*conj (w i)-c₀ i*conj (v i))).re| := by rw [mul_sub,Complex.sub_re]
      _ ≤ ‖z*(c i*conj (w i)-c₀ i*conj (v i))‖ := Complex.abs_re_le_norm _
      _ ≤ 2*(1/100000+4/10000000000) := by
        rw [norm_mul,hfactor]
        have hs := norm_add_le (c i*conj (w i-v i)) ((c i-c₀ i)*conj (v i))
        simp only [norm_mul,Complex.norm_conj,hc,one_mul] at hs
        have ht := mul_le_mul hphase hvi (norm_nonneg _) (by norm_num : (0:ℝ)≤1/10000000000)
        have hsum : ‖c i*conj (w i-v i)+(c i-c₀ i)*conj (v i)‖≤1/100000+4/10000000000 := by linarith
        exact mul_le_mul hz hsum (norm_nonneg _) (by norm_num)
  have hh := (abs_le.mp hd).1
  linarith
def Construction (n : ℕ) : Prop := ∃ (r : ℝ) (w : Fin n → ℂ),
  D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Admissible (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha n) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta n) ∧ 1<r ∧
  D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.LargestRoot (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha n) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta n) r ∧
  D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.SimpleRoot (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha n) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta n) r ∧ w≠0 ∧
  D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha n) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta n) r *ᵥ w=0 ∧
  D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.StarCondition (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha n) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta n) w ∧
  D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.PPT (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.rho (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha n) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta n) r) ∧
  D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Edge (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.rho (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha n) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta n) r) ∧
  Matrix.rank (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.rho (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha n) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta n) r)=n*n-1 ∧
  Matrix.rank (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.rhoGamma (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha n) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta n) r)=n*n-2*n+3
theorem certificate_sound {m : ℕ} (hn : 3≤ m+1) (hn16 : m+1≤16) (d : Data m) (hd : Valid d) : Construction (m+1) := by
  rcases hd with ⟨hR,hlt,hld,hlo,hut,hud,hup,hvl,hvm,hres,hza,hzb,hze,ha,hb,he⟩
  let R : ℝ := (d.Rnum:ℝ)/den
  let a := D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha (m+1)
  let b := D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+1)
  let v := rationalVector den d.vector
  have herror (s : ℝ) : (norm ∘ (Matrix.toEuclideanCLM (n := Fin (m+1)) (𝕜 := ℂ))) (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b s-(D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (alpha0 (m+1)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+1)) s))≤1/50000000 := by
    have h := Finite.entry_norm_bound (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b s-(D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (alpha0 (m+1)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+1)) s)) (1/1000000000)
      (by norm_num) (fun i j => matrix_entry_error hn i j s)
    have hnR : ((m+1:ℕ):ℝ)≤16 := by exact_mod_cast hn16
    linarith
  have herrlead (s : ℝ) : (norm ∘ (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℂ))) ((fun A => Matrix.submatrix A Fin.castSucc Fin.castSucc) (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b s)-(fun A => Matrix.submatrix A Fin.castSucc Fin.castSucc) ((D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (alpha0 (m+1)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+1)) s)))≤1/50000000 := by
    have h := Finite.entry_norm_bound ((fun A => Matrix.submatrix A Fin.castSucc Fin.castSucc) (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b s)-(fun A => Matrix.submatrix A Fin.castSucc Fin.castSucc) ((D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (alpha0 (m+1)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+1)) s))) (1/1000000000)
      (by norm_num) (fun i j => matrix_entry_error hn i.castSucc j.castSucc s)
    have hmR : (m:ℝ)≤16 := by exact_mod_cast (show m≤16 by omega)
    linarith
  have hLow0 : ((fun A => Matrix.submatrix A Fin.castSucc Fin.castSucc) ((D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (alpha0 (m+1)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+1)) (R-1/1000000)))-1).PosDef := by
    have h := Certificates.congruence_posDef hlt hld hlo
    rw [lower_scale] at h
    exact unscale_posDef _ h
  have hUp0 : ((D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (alpha0 (m+1)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+1)) (R+1/1000000))-(1/10000000:ℂ) • 1).PosDef := by
    have h := Certificates.congruence_posDef hut hud hup
    rw [upper_scale] at h
    exact unscale_posDef _ h
  have hupper : (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b (R+1/1000000)).PosDef := Finite.posDef_of_approx _ _
    (1/10000000) (1/50000000) (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D_hermitian hn a b _) (by simpa only [Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_one] using hUp0.posSemidef) (herror _) (by norm_num)
  have hlower : ((fun A => Matrix.submatrix A Fin.castSucc Fin.castSucc) (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b (R-1/1000000))-(1/2:ℂ) • 1).PosSemidef := by
    have hH : ((fun A => Matrix.submatrix A Fin.castSucc Fin.castSucc) (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b (R-1/1000000))).IsHermitian := (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D_hermitian hn a b _).submatrix _
    have hH' : ((fun A => Matrix.submatrix A Fin.castSucc Fin.castSucc) (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b (R-1/1000000))-(1/2:ℂ) • 1).IsHermitian :=
      hH.sub (by simpa only [Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_one] using (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr (by norm_num : (0:ℝ) ≤ 1/2))).isHermitian)
    apply (Finite.posDef_of_approx _ ((fun A => Matrix.submatrix A Fin.castSucc Fin.castSucc) ((D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (alpha0 (m+1)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+1)) (R-1/1000000)))-(1/2:ℂ) • 1)
      (1/2) (1/50000000) hH' ?_ ?_ (by norm_num)).posSemidef
    · convert hLow0.posSemidef using 1 <;> module
    · have heq : ((fun A => Matrix.submatrix A Fin.castSucc Fin.castSucc) (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b (R-1/1000000))-(1/2:ℂ) • 1)-
          ((fun A => Matrix.submatrix A Fin.castSucc Fin.castSucc) ((D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (alpha0 (m+1)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+1)) (R-1/1000000)))-(1/2:ℂ) • 1)=
          (fun A => Matrix.submatrix A Fin.castSucc Fin.castSucc) (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b (R-1/1000000))-(fun A => Matrix.submatrix A Fin.castSucc Fin.castSucc) ((D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (alpha0 (m+1)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+1)) (R-1/1000000))) := by abel
      rw [heq]
      exact herrlead _
  have hvnorm : ‖(WithLp.toLp 2) v‖≤4 := rationalVector_norm den (by norm_num) d.vector hvm
  have hvlast : v (Fin.last m)=1 := by norm_num [v,rationalVector,Function.comp_apply,hvl,den,GaussianInt.toComplex_def]
  have hres0 : ‖(WithLp.toLp 2) ((D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (alpha0 (m+1)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+1)) R) *ᵥ v)‖≤1/100000000 := by
    rw [show (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (alpha0 (m+1)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+1)) R) *ᵥ v=rationalVector (den^3) (matrixInt (m+1) d.Rnum *ᵥ d.vector) from residual_scale d]
    have hh := rationalVector_l1 (den^3) (by norm_num) (matrixInt (m+1) d.Rnum *ᵥ d.vector)
    have hi : ((∑ i,Certificates.size ((matrixInt (m+1) d.Rnum *ᵥ d.vector) i):ℤ):ℝ)≤(den^3/100000000:ℤ) := by exact_mod_cast hres
    norm_num [den] at hi hh ⊢
    linarith
  have hvres : ‖(WithLp.toLp 2) (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b R *ᵥ v)‖≤1/10000000 := by
    have heq : D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b R=(D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (alpha0 (m+1)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+1)) R)+(D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b R-(D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (alpha0 (m+1)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+1)) R)) := by abel
    rw [heq,Matrix.add_mulVec]
    change ‖(WithLp.toLp 2) ((D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (alpha0 (m+1)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+1)) R) *ᵥ v)+(WithLp.toLp 2) ((D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b R-(D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (alpha0 (m+1)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+1)) R)) *ᵥ v)‖≤_
    have hp : ‖(WithLp.toLp 2) ((D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b R-(D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (alpha0 (m+1)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+1)) R)) *ᵥ v)‖≤(1/50000000)*4 := by
      have hh := (Matrix.toEuclideanCLM (𝕜:=ℂ) (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D a b R-(D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.D (alpha0 (m+1)) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta (m+1)) R))).le_opNorm ((WithLp.toLp 2) v)
      exact hh.trans (mul_le_mul (herror R) hvnorm (norm_nonneg _) (by norm_num))
    exact (norm_add_le _ _).trans (by linarith)
  have hRreal : 1<R-1/1000000 := by
    have hi : (den+1000000:ℝ)<(d.Rnum:ℝ) := by exact_mod_cast hR
    dsimp [R]; norm_num [den] at hi ⊢; linarith
  obtain ⟨r,w,h1,hloR,hupR,hr,hs,hwne,hw,hwlast,hclose⟩ := Finite.root_and_kernel_enclosure hn a b R v hRreal hupper hlower hvlast hvnorm hvres
  have halpha (i : Fin (m+1)) (hi : i.val+1≠m+1) : 0<(rationalDirection d.zAlpha*(a i*conj (w i))).re :=
    positive_projection a (alpha0 (m+1)) w v _ i (rationalDirection_norm _ hza) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha_norm _ _) hvnorm hclose (alpha_error hn i)
      (projection_integer _ (alphaInt (m+1)) d.vector i (ha i hi))
  have hbeta (i : Fin (m+1)) (hi : i.val≠0) : 0<(rationalDirection d.zBeta*(b i*conj (w i))).re := by
    have hp := projection_integer d.zBeta (fun _=> (den:GaussianInt)) d.vector i (hb i hi)
    have he : ((den:GaussianInt):ℂ)/(den:ℂ)=1 := by norm_num [den,GaussianInt.toComplex_def]
    rw [he] at hp
    exact positive_projection b b w v _ i (rationalDirection_norm _ hzb) (by simp [b,D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta]) hvnorm hclose (by simp) hp
  have hends (i : Fin (m+1)) (hi : i.val=0 ∨ i.val+1=m+1) : 0<(rationalDirection d.zEnds*(a i*conj (w i))).re :=
    positive_projection a (alpha0 (m+1)) w v _ i (rationalDirection_norm _ hze) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha_norm _ _) hvnorm hclose (alpha_error hn i)
      (projection_integer _ (alphaInt (m+1)) d.vector i (he i hi))
  have hstar := D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.three_halfplanes_star hn a b w _ _ _ halpha hbeta hends
  have hab := D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.admissible hn
  have hp := D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.proposition61 (m+1) hn a b r w hab h1 hr hs hwne hw hstar
  exact ⟨r,w,hab,h1,hr,hs,hwne,hw,hstar,hp⟩
end Small
#print axioms Small.certificate_sound


open Matrix
namespace Small
set_option maxRecDepth 20000
set_option maxHeartbeats 0
def data3 : Data 2 where
  Rnum := 2657852097554
  vector := ![⟨993178498762,-116603900433⟩,⟨-671495100029,-233207800866⟩,⟨1000000000000,0⟩]
  zAlpha := ⟨280199,959942⟩
  zBeta := ⟨166355,-986066⟩
  zEnds := ⟨-58402,-998293⟩
  lowerC := ![![⟨776653,0⟩,⟨-415320,415320⟩],![⟨0,0⟩,⟨973741,0⟩]]
  upperC := ![![⟨613387,0⟩,⟨-176130,176130⟩,⟨661419546,-77653791⟩],![⟨0,0⟩,⟨662033,0⟩,⟨-447190460,-155307583⟩],![⟨0,0⟩,⟨0,0⟩,⟨665962736,0⟩]]
theorem valid3 : Valid data3 := by decide +kernel
private theorem case3 : Construction 3 := certificate_sound (by norm_num) (by norm_num) data3 valid3

def data4 : Data 3 where
  Rnum := 3070124637784
  vector := ![⟨935010679520,-354619555558⟩,⟨-725889582162,-52123782565⟩,⟨-683334793940,-250371990428⟩,⟨1000000000000,0⟩]
  zAlpha := ⟨387897,921703⟩
  zBeta := ⟨35834,-999358⟩
  zEnds := ⟨-180263,-983618⟩
  lowerC := ![![⟨695027,0⟩,⟨-271139,271139⟩,⟨-1825000,1825000⟩],![⟨0,0⟩,⟨793786,0⟩,⟨-57634,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨2700249,0⟩]]
  upperC := ![![⟨570718,0⟩,⟨-139029,139029⟩,⟨-328644,328644⟩,⟨563490545,-213713866⟩],![⟨0,0⟩,⟨603637,0⟩,⟨-96759,0⟩,⟨-437462481,-31412760⟩],![⟨0,0⟩,⟨0,0⟩,⟨761834,0⟩,⟨-411816324,-150888346⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨602657275,0⟩]]
theorem valid4 : Valid data4 := by decide +kernel
private theorem case4 : Construction 4 := certificate_sound (by norm_num) (by norm_num) data4 valid4

def data5 : Data 4 where
  Rnum := 3375300931410
  vector := ![⟨903733284910,-428095958571⟩,⟨-209155177729,-36227406693⟩,⟨-1026628645521,-177820572592⟩,⟨-209155177729,-36227406693⟩,⟨1000000000000,0⟩]
  zAlpha := ⟨503926,863747⟩
  zBeta := ⟨85648,-996325⟩
  zEnds := ⟨-219393,-975637⟩
  lowerC := ![![⟨648845,0⟩,⟨-212947,212947⟩,⟨-693573,693573⟩,⟨-87230,87230⟩],![⟨0,0⟩,⟨715327,0⟩,⟨-98149,0⟩,⟨-213061,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨1213993,0⟩,⟨-123362,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨752808,0⟩]]
  upperC := ![![⟨544307,0⟩,⟨-119389,119389⟩,⟨-267695,267695⟩,⟨-61394,61394⟩,⟨534563276,-253221118⟩],![⟨0,0⟩,⟨569892,0⟩,⟨-90540,0⟩,⟨-123377,0⟩,⟨-123716507,-21428718⟩],![⟨0,0⟩,⟨0,0⟩,⟨684177,0⟩,⟨-86824,0⟩,⟨-607256593,-105181841⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨590082,0⟩,⟨-123716507,-21428718⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨591505965,0⟩]]
theorem valid5 : Valid data5 := by decide +kernel
private theorem case5 : Construction 5 := certificate_sound (by norm_num) (by norm_num) data5 valid5

def data6 : Data 5 where
  Rnum := 3159268299663
  vector := ![⟨930258232087,-366905466890⟩,⟨-243165019272,-50523284959⟩,⟨-555339392734,-211608998840⟩,⟨-593670318149,-27124949066⟩,⟨-243165019272,-50523284959⟩,⟨1000000000000,0⟩]
  zAlpha := ⟨388045,921640⟩
  zBeta := ⟨22827,-999739⟩
  zEnds := ⟨-186737,-982410⟩
  lowerC := ![![⟨680529,0⟩,⟨-251447,251447⟩,⟨-1162854,1162854⟩,⟨-95310,95310⟩,⟨-149603,149603⟩],![⟨0,0⟩,⟨767836,0⟩,⟨-78926,0⟩,⟨-251060,0⟩,⟨378469,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨1814946,0⟩,⟨-134789,0⟩,⟨-211571,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨811685,0⟩,⟨-394074,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨895584,0⟩]]
  upperC := ![![⟨562609,0⟩,⟨-132749,132749⟩,⟨-308221,308221⟩,⟨-65761,65761⟩,⟨-80403,80403⟩,⟨582921488,-229911502⟩],![⟨0,0⟩,⟨593105,0⟩,⟨-95010,0⟩,⟨-136071,0⟩,⟨124644,0⟩,⟨-152372932,-31659071⟩],![⟨0,0⟩,⟨0,0⟩,⟨736053,0⟩,⟨-93001,0⟩,⟨-113708,0⟩,⟨-347988554,-132599094⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨615886,0⟩,⟨-166368,0⟩,⟨-372007805,-16997133⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨628372,0⟩,⟨-152372932,-31659071⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨626623749,0⟩]]
theorem valid6 : Valid data6 := by decide +kernel
private theorem case6 : Construction 6 := certificate_sound (by norm_num) (by norm_num) data6 valid6

def data7 : Data 6 where
  Rnum := 3424259411894
  vector := ![⟨919517585457,-393048864692⟩,⟨-403034421139,-51371502429⟩,⟨-546534394622,-196071446233⟩,⟨-1495833134,-288805607⟩,⟨-580243476334,-21479401868⟩,⟨-393190224874,-102358306688⟩,⟨1000000000000,0⟩]
  zAlpha := ⟨409992,912089⟩
  zBeta := ⟨18499,-999829⟩
  zEnds := ⟨-200602,-979673⟩
  lowerC := ![![⟨642260,0⟩,⟨-205645,205645⟩,⟨-640456,640456⟩,⟨-85556,85556⟩,⟨-120818,120818⟩,⟨-1068542,1068542⟩],![⟨0,0⟩,⟨705037,0⟩,⟨-99848,0⟩,⟨-205947,0⟩,⟨260926,0⟩,⟨200849,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨1147800,0⟩,⟨-120994,0⟩,⟨-170862,0⟩,⟨1489544,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨741256,0⟩,⟨-290827,0⟩,⟨-465308,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨785839,0⟩,⟨-324288,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨1273068,0⟩]]
  upperC := ![![⟨540402,0⟩,⟨-116679,116679⟩,⟨-259903,259903⟩,⟨-60473,60473⟩,⟨-71846,71846⟩,⟨-165030,165030⟩,⟨559186833,-239025048⟩],![⟨0,0⟩,⟨565032,0⟩,⟨-89510,0⟩,⟨-120800,0⟩,⟨101257,0⟩,⟨52950,0⟩,⟨-245097635,-31240586⟩],![⟨0,0⟩,⟨0,0⟩,⟨674063,0⟩,⟨-85522,0⟩,⟨-101606,0⟩,⟨202096,0⟩,⟨-332364271,-119237025⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨584693,0⟩,⟨-143518,0⟩,⟨-150023,0⟩,⟨-909743,-175647⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨593396,0⟩,⟨-128182,0⟩,⟨-352863993,-13062294⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨620241,0⟩,⟨-239111022,-62247203⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨608131083,0⟩]]
theorem valid7 : Valid data7 := by decide +kernel
private theorem case7 : Construction 7 := certificate_sound (by norm_num) (by norm_num) data7 valid7

def data8 : Data 7 where
  Rnum := 3691942425612
  vector := ![⟨902969617927,-429704397349⟩,⟨-331729406178,-41851530341⟩,⟨-659490517536,-164436320147⟩,⟨-58126447287,-15699286182⟩,⟨-60028792182,-4657850355⟩,⟨-676494620629,-65742485220⟩,⟨-326608403245,-71574439884⟩,⟨1000000000000,0⟩]
  zAlpha := ⟨464336,885659⟩
  zBeta := ⟨38710,-999251⟩
  zEnds := ⟨-220262,-975441⟩
  lowerC := ![![⟨609491,0⟩,⟨-172438,172438⟩,⟨-457313,457313⟩,⟨-77288,77288⟩,⟨-101892,101892⟩,⟨-441500,441500⟩,⟨-442596,442596⟩],![⟨0,0⟩,⟨656467,0⟩,⟨-102080,0⟩,⟨-173903,0⟩,⟨192225,0⟩,⟨109413,0⟩,⟨-29513,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨921531,0⟩,⟨-109302,0⟩,⟨-144097,0⟩,⟨599745,0⟩,⟨534109,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨686739,0⟩,⟨-229264,0⟩,⟨-269904,0⟩,⟨171264,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨713135,0⟩,⟨-205237,0⟩,⟨-327690,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨847019,0⟩,⟨-12012,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨814688,0⟩]]
  upperC := ![![⟨520442,0⟩,⟨-103550,103550⟩,⟨-223938,223938⟩,⟨-55835,55835⟩,⟨-64844,64844⟩,⟨-132984,132984⟩,⟨-123794,123794⟩,⟨535880115,-255014140⟩],![⟨0,0⟩,⟨540652,0⟩,⟨-83935,0⟩,⟨-108295,0⟩,⟨83743,0⟩,⟨43912,0⟩,⟨-4523,0⟩,⟨-196869567,-24837386⟩],![⟨0,0⟩,⟨0,0⟩,⟨626579,0⟩,⟨-78962,0⟩,⟨-91703,0⟩,⟨156045,0⟩,⟨110872,0⟩,⟨-391383947,-97587044⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨557744,0⟩,⟨-125769,0⟩,⟨-130100,0⟩,⟨80896,0⟩,⟨-34496018,-9316970⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨563995,0⟩,⟨-113787,0⟩,⟨-135564,0⟩,⟨-35625003,-2764279⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨582219,0⟩,⟨-94378,0⟩,⟨-401475390,-39015801⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨578175,0⟩,⟨-193830401,-42476859⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨593464559,0⟩]]
theorem valid8 : Valid data8 := by decide +kernel
private theorem case8 : Construction 8 := certificate_sound (by norm_num) (by norm_num) data8 valid8

def data9 : Data 8 where
  Rnum := 3818668191243
  vector := ![⟨898753456126,-438454359201⟩,⟨-299020581505,-40704985850⟩,⟨-604137905407,-151102100998⟩,⟨-199550425546,-18939677122⟩,⟨-85524218594,-14307775938⟩,⟨-194849145984,-47041407446⟩,⟨-620422624009,-53760778381⟩,⟨-295987210062,-58836855084⟩,⟨1000000000000,0⟩]
  zAlpha := ⟨476875,878971⟩
  zBeta := ⟨43205,-999066⟩
  zEnds := ⟨-224996,-974360⟩
  lowerC := ![![⟨595632,0⟩,⟨-159820,159820⟩,⟨-404084,404084⟩,⟨-73837,73837⟩,⟨-94968,94968⟩,⟨-345153,345153⟩,⟨-329140,329140⟩,⟨-262534,262534⟩],![⟨0,0⟩,⟨637073,0⟩,⟨-100885,0⟩,⟨-161837,0⟩,⟨169145,0⟩,⟨92474,0⟩,⟨-25418,0⟩,⟨51309,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨855821,0⟩,⟨-104421,0⟩,⟨-134305,0⟩,⟨461711,0⟩,⟨379434,0⟩,⟨173559,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨665005,0⟩,⟨-208153,0⟩,⟨-234246,0⟩,⟨157684,0⟩,⟨53099,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨686179,0⟩,⟨-183399,0⟩,⟨-270817,0⟩,⟨148947,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨777595,0⟩,⟨-62184,0⟩,⟨-152204,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨753882,0⟩,⟨-123007,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨721252,0⟩]]
  upperC := ![![⟨511734,0⟩,⟨-98185,98185⟩,⟨-210005,210005⟩,⟨-53848,53848⟩,⟨-61970,61970⟩,⟨-121628,121628⟩,⟨-113666,113666⟩,⟨-104968,104968⟩,⟨542849695,-264827685⟩],![⟨0,0⟩,⟨530237,0⟩,⟨-81378,0⟩,⟨-103170,0⟩,⟨76992,0⟩,⟨40478,0⟩,⟨-3241,0⟩,⟨18700,0⟩,⟨-180609348,-24585931⟩],![⟨0,0⟩,⟨0,0⟩,⟨607747,0⟩,⟨-76153,0⟩,⟨-87638,0⟩,⟨139832,0⟩,⟨98792,0⟩,⟨45411,0⟩,⟨-364901013,-91266090⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨546277,0⟩,⟨-118730,0⟩,⟨-122398,0⟩,⟨74330,0⟩,⟨31625,0⟩,⟨-120529080,-11439624⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨551675,0⟩,⟨-108038,0⟩,⟨-126848,0⟩,⟨73160,0⟩,⟨-51656932,-8641945⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨567134,0⟩,⟨-91799,0⟩,⟨-109591,0⟩,⟨-117689462,-28413142⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨563815,0⟩,⟨-98371,0⟩,⟨-374737143,-32471662⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨560524,0⟩,⟨-178777162,-35537629⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨604003273,0⟩]]
theorem valid9 : Valid data9 := by decide +kernel
private theorem case9 : Construction 9 := certificate_sound (by norm_num) (by norm_num) data9 valid9

def data10 : Data 9 where
  Rnum := 3965080022409
  vector := ![⟨894274054673,-447519737150⟩,⟨-309272295570,-40010143219⟩,⟨-556648428118,-140497892954⟩,⟨-165853660385,-16761694921⟩,⟨-215301460515,-17948788209⟩,⟨-209946269514,-50984721391⟩,⟨-162655611253,-36490316627⟩,⟨-572526997972,-42543707453⟩,⟨-306074246438,-59738764924⟩,⟨1000000000000,0⟩]
  zAlpha := ⟨480370,877066⟩
  zBeta := ⟨37078,-999312⟩
  zEnds := ⟨-229919,-973210⟩
  lowerC := ![![⟨580740,0⟩,⟨-147113,147113⟩,⟨-356429,356429⟩,⟨-70167,70167⟩,⟨-88094,88094⟩,⟨-274654,274654⟩,⟨-255697,255697⟩,⟨-211820,211820⟩,⟨-306554,306554⟩],![⟨0,0⟩,⟨616882,0⟩,⟨-98671,0⟩,⟨-149728,0⟩,⟨147433,0⟩,⟨78646,0⟩,⟨-20022,0⟩,⟨41830,0⟩,⟨77449,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨796635,0⟩,⟨-99231,0⟩,⟨-124583,0⟩,⟨360298,0⟩,⟨280547,0⟩,⟨125744,0⟩,⟨275678,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨642416,0⟩,⟨-187982,0⟩,⟨-205070,0⟩,⟨140429,0⟩,⟨49785,0⟩,⟨-71787,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨659116,0⟩,⟨-165048,0⟩,⟨-229032,0⟩,⟨134662,0⟩,⟨43997,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨722572,0⟩,⟨-86266,0⟩,⟨-150294,0⟩,⟨249263,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨705999,0⟩,⟨-124959,0⟩,⟨-150075,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨685704,0⟩,⟨-127685,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨712943,0⟩]]
  upperC := ![![⟨502197,0⟩,⟨-92550,92550⟩,⟨-195798,195798⟩,⟨-51700,51700⟩,⟨-58937,58937⟩,⟨-110609,110609⟩,⟨-103834,103834⟩,⟨-96742,96742⟩,⟨-108870,108870⟩,⟨543999876,-272232729⟩],![⟨0,0⟩,⟨518973,0⟩,⟨-78516,0⟩,⟨-97773,0⟩,⟨70152,0⟩,⟨37016,0⟩,⟨-2051,0⟩,⟨16878,0⟩,⟨25336,0⟩,⟨-188134862,-24338751⟩],![⟨0,0⟩,⟨0,0⟩,⟨588223,0⟩,⟨-73115,0⟩,⟨-83350,0⟩,⟨124191,0⟩,⟨87301,0⟩,⟨40513,0⟩,⟨67023,0⟩,⟨-338617286,-85466890⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨533907,0⟩,⟨-111460,0⟩,⟨-114540,0⟩,⟨67674,0⟩,⟨29377,0⟩,⟨-13519,0⟩,⟨-100891235,-10196387⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨538497,0⟩,⟨-102056,0⟩,⟨-118092,0⟩,⟨66734,0⟩,⟨30361,0⟩,⟨-130971044,-10918513⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨551433,0⟩,⟨-88649,0⟩,⟨-103795,0⟩,⟨84847,0⟩,⟨-127713367,-31014739⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨548759,0⟩,⟨-93887,0⟩,⟨-104772,0⟩,⟨-98945793,-22197588⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨546145,0⟩,⟨-94532,0⟩,⟨-348276562,-25879954⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨548716,0⟩,⟨-186189420,-36339952⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨608314861,0⟩]]
theorem valid10 : Valid data10 := by decide +kernel
private theorem case10 : Construction 10 := certificate_sound (by norm_num) (by norm_num) data10 valid10

def data11 : Data 10 where
  Rnum := 4136486634613
  vector := ![⟨888058641344,-459730192107⟩,⟨-304244507870,-37845075196⟩,⟨-549235192885,-129207451724⟩,⟨-145292090398,-17120851574⟩,⟨-184620614585,-16317078142⟩,⟨-313931518356,-48684172261⟩,⟨-180891117399,-40366099822⟩,⟨-143653271497,-27688493618⟩,⟨-562571529862,-43210374606⟩,⟨-301416620556,-56080220559⟩,⟨1000000000000,0⟩]
  zAlpha := ⟨493423,869790⟩
  zBeta := ⟨38320,-999266⟩
  zEnds := ⟨-236581,-971612⟩
  lowerC := ![![⟨564649,0⟩,⟨-134307,134307⟩,⟨-313200,313200⟩,⟨-66253,66253⟩,⟨-81235,81235⟩,⟨-220780,220780⟩,⟨-203683,203683⟩,⟨-174643,174643⟩,⟨-232266,232266⟩,⟨-279529,279529⟩],![⟨0,0⟩,⟨595739,0⟩,⟨-95465,0⟩,⟨-137551,0⟩,⟨127028,0⟩,⟨66835,0⟩,⟨-14654,0⟩,⟨34141,0⟩,⟨59604,0⟩,⟨42430,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨742356,0⟩,⟨-93696,0⟩,⟨-114883,0⟩,⟨282572,0⟩,⟨211804,0⟩,⟨94363,0⟩,⟨192621,0⟩,⟨255314,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨618820,0⟩,⟨-168655,0⟩,⟨-179970,0⟩,⟨122211,0⟩,⟨45538,0⟩,⟨-51096,0⟩,⟨6917,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨631724,0⟩,⟨-148687,0⟩,⟨-195774,0⟩,⟨118318,0⟩,⟨44285,0⟩,⟨-59509,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨675984,0⟩,⟨-96637,0⟩,⟨-142668,0⟩,⟨192223,0⟩,⟨135382,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨664714,0⟩,⟨-121354,0⟩,⟨-144175,0⟩,⟨184349,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨651956,0⟩,⟨-123447,0⟩,⟨-161066,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨667615,0⟩,⟨-97700,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨678465,0⟩]]
  upperC := ![![⟨491682,0⟩,⟨-86619,86619⟩,⟨-181275,181275⟩,⟨-49366,49366⟩,⟨-55726,55726⟩,⟨-99901,99901⟩,⟨-94256,94256⟩,⟨-88583,88583⟩,⟨-98177,98177⟩,⟨-105037,105037⟩,⟨537141350,-278067313⟩],![⟨0,0⟩,⟨506712,0⟩,⟨-75308,0⟩,⟨-92073,0⟩,⟨63230,0⟩,⟨33522,0⟩,⟨-969,0⟩,⟨15090,0⟩,⟨22198,0⟩,⟨17646,0⟩,⟨-184022011,-22890555⟩],![⟨0,0⟩,⟨0,0⟩,⟨567871,0⟩,⟨-69814,0⟩,⟨-78809,0⟩,⟨109112,0⟩,⟨76366,0⟩,⟨35837,0⟩,⟨57568,0⟩,⟨68358,0⟩,⟨-332204312,-78150980⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨520486,0⟩,⟨-103935,0⟩,⟨-106494,0⟩,⟨60939,0⟩,⟨27017,0⟩,⟨-10549,0⟩,⟨7196,0⟩,⟨-87879818,-10355533⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨524312,0⟩,⟨-95806,0⟩,⟨-109259,0⟩,⟨60204,0⟩,⟨27908,0⟩,⟨-10513,0⟩,⟨-111667633,-9869373⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨534963,0⟩,⟨-84912,0⟩,⟨-97612,0⟩,⟨74804,0⟩,⟨43288,0⟩,⟨-189881158,-29446565⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨532856,0⟩,⟨-88998,0⟩,⟨-98420,0⟩,⟨73189,0⟩,⟨-109411824,-24415391⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨530824,0⟩,⟨-89522,0⟩,⟨-100388,0⟩,⟨-86888568,-16747360⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨532766,0⟩,⟨-86586,0⟩,⟨-340270881,-26135749⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨533908,0⟩,⟨-182311546,-33920059⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨604849311,0⟩]]
theorem valid11 : Valid data11 := by decide +kernel
private theorem case11 : Construction 11 := certificate_sound (by norm_num) (by norm_num) data11 valid11

def data12 : Data 11 where
  Rnum := 4294625377320
  vector := ![⟨882844437423,-469665518547⟩,⟨-293937136704,-36024362319⟩,⟨-534262834094,-119631565013⟩,⟨-159756240769,-17818909749⟩,⟨-164585820045,-16707203659⟩,⟨-277489964854,-43272942385⟩,⟨-278025482260,-39687017414⟩,⟨-162285973402,-32107408040⟩,⟨-157991911532,-29633189159⟩,⟨-545904143089,-41679177054⟩,⟨-291637290061,-51424566700⟩,⟨1000000000000,0⟩]
  zAlpha := ⟨502953,864314⟩
  zBeta := ⟨38091,-999274⟩
  zEnds := ⟨-242028,-970269⟩
  lowerC := ![![⟨550931,0⟩,⟨-124098,124098⟩,⟨-281560,281560⟩,⟨-62965,62965⟩,⟨-75795,75795⟩,⟨-186404,186404⟩,⟨-171881,171881⟩,⟨-151000,151000⟩,⟨-190414,190414⟩,⟨-220737,220737⟩,⟨-234628,234628⟩],![⟨0,0⟩,⟨578209,0⟩,⟨-92231,0⟩,⟨-127852,0⟩,⟨111783,0⟩,⟨58516,0⟩,⟨-10788,0⟩,⟨28987,0⟩,⟨48604,0⟩,⟨34765,0⟩,⟨37636,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨702052,0⟩,⟨-89046,0⟩,⟨-107190,0⟩,⟨232931,0⟩,⟨170706,0⟩,⟨76259,0⟩,⟨147630,0⟩,⟨189460,0⟩,⟨181123,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨599314,0⟩,⟨-153903,0⟩,⟨-162103,0⟩,⟨107913,0⟩,⟨41787,0⟩,⟨-38478,0⟩,⟨8171,0⟩,⟨26692,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨609650,0⟩,⟨-136602,0⟩,⟨-173384,0⟩,⟨105075,0⟩,⟨42059,0⟩,⟨-42797,0⟩,⟨2566,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨642840,0⟩,⟨-98990,0⟩,⟨-134446,0⟩,⟨157763,0⟩,⟨103822,0⟩,⟨22547,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨634683,0⟩,⟨-116235,0⟩,⟨-136198,0⟩,⟨151716,0⟩,⟨92999,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨625869,0⟩,⟨-117868,0⟩,⟨-146975,0⟩,⟨135273,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨636052,0⟩,⟨-101729,0⟩,⟨-134967,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨642587,0⟩,⟨-94439,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨642648,0⟩]]
  upperC := ![![⟨482544,0⟩,⟨-81696,81696⟩,⟨-169531,169531⟩,⟨-47369,47369⟩,⟨-53042,53042⟩,⟨-91633,91633⟩,⟨-86832,86832⟩,⟨-82154,82154⟩,⟨-90006,90006⟩,⟨-95637,95637⟩,⟨-98789,98789⟩,⟨533819029,-283987037⟩],![⟨0,0⟩,⟨496183,0⟩,⟨-72490,0⟩,⟨-87323,0⟩,⟨57702,0⟩,⟨30732,0⟩,⟨-199,0⟩,⟨13700,0⟩,⟨19814,0⟩,⟨16026,0⟩,⟨16326,0⟩,⟨-177731501,-21782422⟩],![⟨0,0⟩,⟨0,0⟩,⟨551071,0⟩,⟨-66990,0⟩,⟨-75013,0⟩,⟨97578,0⟩,⟨68091,0⟩,⟨32279,0⟩,⟨50597,0⟩,⟨59588,0⟩,⟨56697,0⟩,⟨-323046320,-72336182⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨508997,0⟩,⟨-97781,0⟩,⟨-99971,0⟩,⟨55564,0⟩,⟨25069,0⟩,⟨-8406,0⟩,⟨6837,0⟩,⟨12896,0⟩,⟨-96597942,-10774351⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨512257,0⟩,⟨-90643,0⟩,⟨-102193,0⟩,⟨54973,0⟩,⟨25870,0⟩,⟨-8270,0⟩,⟨6700,0⟩,⟨-99518191,-10102150⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨521262,0⟩,⟨-81525,0⟩,⟨-92430,0⟩,⟨67105,0⟩,⟨38545,0⟩,⟨4601,0⟩,⟨-167786562,-26165331⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨519548,0⟩,⟨-84821,0⟩,⟨-93109,0⟩,⟨65797,0⟩,⟨36740,0⟩,⟨-168110371,-23997073⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨517915,0⟩,⟨-85257,0⟩,⟨-94649,0⟩,⟨63614,0⟩,⟨-98127553,-19414004⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨519440,0⟩,⟨-82950,0⟩,⟨-92990,0⟩,⟨-95531113,-17917948⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨520341,0⟩,⟨-81839,0⟩,⟨-330085422,-25201649⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨520552,0⟩,⟨-176340862,-31094277⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨604658421,0⟩]]
theorem valid12 : Valid data12 := by decide +kernel
private theorem case12 : Construction 12 := certificate_sound (by norm_num) (by norm_num) data12 valid12

def data13 : Data 12 where
  Rnum := 4446511971612
  vector := ![⟨878279563598,-478147475331⟩,⟨-287837568720,-34535244199⟩,⟨-515265918962,-111585712092⟩,⟨-163999643258,-17789024120⟩,⟨-175304225617,-17380752971⟩,⟨-251504667027,-40335295010⟩,⟨-248876190285,-35942355603⟩,⟨-252640185401,-32472608150⟩,⟨-173058719813,-32929342379⟩,⟨-162331571389,-29339279104⟩,⟨-525783140894,-38761155023⟩,⟨-285847435753,-48315551657⟩,⟨1000000000000,0⟩]
  zAlpha := ⟨510132,860096⟩
  zBeta := ⟨36786,-999323⟩
  zEnds := ⟨-246699,-969092⟩
  lowerC := ![![⟨538654,0⟩,⟨-115481,115481⟩,⟨-256504,256504⟩,⟨-60063,60063⟩,⟨-71209,71209⟩,⟨-161822,161822⟩,⟨-149612,149612⟩,⟨-133874,133874⟩,⟨-162584,162584⟩,⟨-183902,183902⟩,⟨-193726,193726⟩,⟨-215384,215384⟩],![⟨0,0⟩,⟨562868,0⟩,⟨-89041,0⟩,⟨-119661,0⟩,⟨99601,0⟩,⟨52085,0⟩,⟨-7902,0⟩,⟨25172,0⟩,⟨40898,0⟩,⟨29727,0⟩,⟨31619,0⟩,⟨40607,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨669633,0⟩,⟨-84941,0⟩,⟨-100704,0⟩,⟨197474,0⟩,⟨142567,0⟩,⟨64097,0⟩,⟨118811,0⟩,⟨149183,0⟩,⟨141502,0⟩,⟨156412,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨582295,0⟩,⟨-141866,0⟩,⟨-148134,0⟩,⟨96249,0⟩,⟨38473,0⟩,⟨-29838,0⟩,⟨8438,0⟩,⟨23492,0⟩,⟨8234,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨590752,0⟩,⟨-126845,0⟩,⟨-156539,0⟩,⟨94098,0⟩,⟨39313,0⟩,⟨-32174,0⟩,⟨5140,0⟩,⟨21283,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨616684,0⟩,⟨-98266,0⟩,⟨-126639,0⟩,⟨133743,0⟩,⟨84259,0⟩,⟨14744,0⟩,⟨57920,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨610548,0⟩,⟨-110913,0⟩,⟨-128281,0⟩,⟨129086,0⟩,⟨76518,0⟩,⟨8683,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨604132,0⟩,⟨-112212,0⟩,⟨-135672,0⟩,⟨118007,0⟩,⟨66778,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨611207,0⟩,⟨-101231,0⟩,⟨-127640,0⟩,⟨128692,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨615557,0⟩,⟨-96363,0⟩,⟨-120848,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨615720,0⟩,⟨-93552,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨619185,0⟩]]
  upperC := ![![⟨474231,0⟩,⟨-77397,77397⟩,⟨-159492,159492⟩,⟨-45578,45578⟩,⟨-50682,50682⟩,⟨-84828,84828⟩,⟨-80697,80697⟩,⟨-76769,76769⟩,⟨-83326,83326⟩,⟨-88050,88050⟩,⟨-90779,90779⟩,⟨-94901,94901⟩,⟨531546665,-289381300⟩],![⟨0,0⟩,⟨486699,0⟩,⟨-69913,0⟩,⟨-83158,0⟩,⟨53035,0⟩,⟨28374,0⟩,⟨379,0⟩,⟨12550,0⟩,⟨17882,0⟩,⟨14685,0⟩,⟨14909,0⟩,⟨16662,0⟩,⟨-174203219,-20901197⟩],![⟨0,0⟩,⟨0,0⟩,⟨536425,0⟩,⟨-64456,0⟩,⟨-71675,0⟩,⟨88178,0⟩,⟨61403,0⟩,⟨29384,0⟩,⟨45082,0⟩,⟨52719,0⟩,⟨50281,0⟩,⟨52128,0⟩,⟨-311845881,-67533172⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨498677,0⟩,⟨-92471,0⟩,⟨-94380,0⟩,⟨51032,0⟩,⟨23380,0⟩,⟨-6755,0⟩,⟨6506,0⟩,⟨11804,0⟩,⟨7994,0⟩,⟨-99254837,-10766161⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨501490,0⟩,⟨-86147,0⟩,⟨-96196,0⟩,⟨50550,0⟩,⟨24098,0⟩,⟨-6566,0⟩,⟨6471,0⟩,⟨11979,0⟩,⟨-106096525,-10519070⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨509223,0⟩,⟨-78380,0⟩,⟨-87875,0⟩,⟨60814,0⟩,⟨34753,0⟩,⟨4232,0⟩,⟨17897,0⟩,⟨-152214038,-24411463⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨507805,0⟩,⟨-81091,0⟩,⟨-88452,0⟩,⟨59737,0⟩,⟨33290,0⟩,⟨2929,0⟩,⟨-150623254,-21752798⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨506465,0⟩,⟨-81460,0⟩,⟨-89685,0⟩,⟨57999,0⟩,⟨31731,0⟩,⟨-152901278,-19652861⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨507691,0⟩,⟨-79602,0⟩,⟨-88346,0⟩,⟨59580,0⟩,⟨-104737497,-19929282⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨508419,0⟩,⟨-78687,0⟩,⟨-87289,0⟩,⟨-98245284,-17756529⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨508612,0⟩,⟨-78082,0⟩,⟨-318211130,-23458774⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨509114,0⟩,⟨-172998748,-29241222⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨605213842,0⟩]]
theorem valid13 : Valid data13 := by decide +kernel
private theorem case13 : Construction 13 := certificate_sound (by norm_num) (by norm_num) data13 valid13

def data14 : Data 13 where
  Rnum := 4598109225831
  vector := ![⟨873906605870,-486093863587⟩,⟨-282448315425,-33083487603⟩,⟨-500307045767,-104458508893⟩,⟨-162630303624,-17645021437⟩,⟨-177786046800,-17409897299⟩,⟨-253332246883,-38139390244⟩,⟨-227916296081,-33929489934⟩,⟨-228483566273,-29871529081⟩,⟨-254079670687,-32792702580⟩,⟨-175744946688,-32010883684⟩,⟨-161234667447,-27628688925⟩,⟨-509773189203,-36742559717⟩,⟨-280693135881,-45639144472⟩,⟨1000000000000,0⟩]
  zAlpha := ⟨517212,855857⟩
  zBeta := ⟨35968,-999353⟩
  zEnds := ⟨-251091,-967963⟩
  lowerC := ![![⟨527185,0⟩,⟨-107852,107852⟩,⟨-235418,235418⟩,⟨-57389,57389⟩,⟨-67143,67143⟩,⟨-142772,142772⟩,⟨-132533,132533⟩,⟨-120354,120354⟩,⟨-142017,142017⟩,⟨-157774,157774⟩,⟨-165235,165235⟩,⟨-180494,180494⟩,⟨-201486,201486⟩],![⟨0,0⟩,⟨548806,0⟩,⟨-85869,0⟩,⟨-112398,0⟩,⟨89327,0⟩,⟨46770,0⟩,⟨-5657,0⟩,⟨22141,0⟩,⟨35022,0⟩,⟨25969,0⟩,⟨27269,0⟩,⟨33863,0⟩,⟨36724,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨641897,0⟩,⟨-81160,0⟩,⟨-94954,0⟩,⟨170074,0⟩,⟨121468,0⟩,⟨55069,0⟩,⟨98274,0⟩,⟨121354,0⟩,⟨114770,0⟩,⟨124547,0⟩,⟨143426,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨566741,0⟩,⟨-131501,0⟩,⟨-136449,0⟩,⟨86317,0⟩,⟨35473,0⟩,⟨-23444,0⟩,⟨8333,0⟩,⟨20791,0⟩,⟨8869,0⟩,⟨9383,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨573737,0⟩,⟨-118447,0⟩,⟨-142855,0⟩,⟨84655,0⟩,⟨36506,0⟩,⟨-24694,0⟩,⟨6338,0⟩,⟨19650,0⟩,⟨7721,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨594472,0⟩,⟨-96102,0⟩,⟨-119293,0⟩,⟨115394,0⟩,⟨70515,0⟩,⟨10492,0⟩,⟨45285,0⟩,⟨63314,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨589756,0⟩,⟨-105639,0⟩,⟨-120735,0⟩,⟨111777,0⟩,⟨64818,0⟩,⟨5853,0⟩,⟨41041,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨584946,0⟩,⟨-106684,0⟩,⟨-126011,0⟩,⟨103978,0⟩,⟨57944,0⟩,⟨-1012,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨590045,0⟩,⟨-98870,0⟩,⟨-120352,0⟩,⟨111319,0⟩,⟨67252,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨593104,0⟩,⟨-95404,0⟩,⟨-115689,0⟩,⟨116980,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨593325,0⟩,⟨-93387,0⟩,⟨-114042,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨595644,0⟩,⟨-88158,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨599208,0⟩]]
  upperC := ![![⟨466348,0⟩,⟨-73475,73475⟩,⟨-150495,150495⟩,⟨-43903,43903⟩,⟨-48513,48513⟩,⟨-78927,78927⟩,⟨-75352,75352⟩,⟨-72025,72025⟩,⟨-77561,77561⟩,⟨-81570,81570⟩,⟨-83955,83955⟩,⟨-87433,87433⟩,⟨-91544,91544⟩,⟨528420885,-293924013⟩],![⟨0,0⟩,⟨477784,0⟩,⟨-67465,0⟩,⟨-79343,0⟩,⟨48909,0⟩,⟨26286,0⟩,⟨834,0⟩,⟨11550,0⟩,⟨16232,0⟩,⟨13515,0⟩,⟨13685,0⟩,⟨15131,0⟩,⟨15726,0⟩,⟨-170786687,-20004432⟩],![⟨0,0⟩,⟨0,0⟩,⟨523044,0⟩,⟨-62088,0⟩,⟨-68607,0⟩,⟨80111,0⟩,⟨55700,0⟩,⟨26898,0⟩,⟨40466,0⟩,⟨47021,0⟩,⟨44953,0⟩,⟨46425,0⟩,⟨49513,0⟩,⟨-302518227,-63162413⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨489004,0⟩,⟨-87675,0⟩,⟨-89355,0⟩,⟨47031,0⟩,⟨21851,0⟩,⟨-5416,0⟩,⟨6193,0⟩,⟨10855,0⟩,⟨7649,0⟩,⟨7642,0⟩,⟨-98336914,-10669332⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨491443,0⟩,⟨-82050,0⟩,⟨-90852,0⟩,⟨46634,0⟩,⟨22493,0⟩,⟨-5199,0⟩,⟨6224,0⟩,⟨11053,0⟩,⟨7891,0⟩,⟨-107501064,-10527161⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨498139,0⟩,⟨-75372,0⟩,⟨-83697,0⟩,⟨55400,0⟩,⟨31545,0⟩,⟨3958,0⟩,⟨15871,0⟩,⟨21194,0⟩,⟨-153181197,-23061558⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨496954,0⟩,⟨-77624,0⟩,⟨-84189,0⟩,⟨54506,0⟩,⟨30347,0⟩,⟨2883,0⟩,⟨14829,0⟩,⟨-137813065,-20515979⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨495844,0⟩,⟨-77937,0⟩,⟨-85189,0⟩,⟨53104,0⟩,⟨29086,0⟩,⟨1648,0⟩,⟨-138156079,-18062273⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨496841,0⟩,⟨-76422,0⟩,⟨-84094,0⟩,⟨54382,0⟩,⟨30546,0⟩,⟨-153633144,-19828604⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨497437,0⟩,⟨-75660,0⟩,⟨-83229,0⟩,⟨55316,0⟩,⟨-106266865,-19355865⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨497613,0⟩,⟨-75145,0⟩,⟨-82784,0⟩,⟨-97493010,-16706106⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨498023,0⟩,⟨-74295,0⟩,⟨-308242153,-22216945⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨498547,0⟩,⟨-169725377,-27596398⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨604665482,0⟩]]
theorem valid14 : Valid data14 := by decide +kernel
private theorem case14 : Construction 14 := certificate_sound (by norm_num) (by norm_num) data14 valid14

def data15 : Data 14 where
  Rnum := 4747228856332
  vector := ![⟨869807355131,-493391492589⟩,⟨-276687029092,-31708724213⟩,⟨-487079257754,-98118544515⟩,⟨-163351242898,-17519093852⟩,⟨-175539318938,-17313413972⟩,⟨-249155809541,-35858378379⟩,⟨-231015518854,-32479453796⟩,⟨-211221419863,-28626318748⟩,⟨-231327063625,-30180697552⟩,⟨-249712337862,-31751992813⟩,⟨-173815361060,-30033765268⟩,⟨-162121688701,-26591450854⟩,⟨-495624761445,-35064910584⟩,⟨-275145930123,-43079837459⟩,⟨1000000000000,0⟩]
  zAlpha := ⟨523795,851844⟩
  zBeta := ⟨35308,-999376⟩
  zEnds := ⟨-255140,-966904⟩
  lowerC := ![![⟨516589,0⟩,⟨-101149,101149⟩,⟨-217654,217654⟩,⟨-54953,54953⟩,⟨-63559,63559⟩,⟨-127792,127792⟩,⟨-119163,119163⟩,⟨-109503,109503⟩,⟨-126362,126362⟩,⟨-138488,138488⟩,⟨-144435,144435⟩,⟨-155795,155795⟩,⟨-170863,170863⟩,⟨-186733,186733⟩],![⟨0,0⟩,⟨536028,0⟩,⟨-82811,0⟩,⟨-106003,0⟩,⟨80694,0⟩,⟨42359,0⟩,⟨-3931,0⟩,⟨19711,0⟩,⟨30469,0⟩,⟨23058,0⟩,⟨23981,0⟩,⟨28989,0⟩,⟨31049,0⟩,⟨33141,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨618120,0⟩,⟨-77715,0⟩,⟨-89886,0⟩,⟨148624,0⟩,⟨105320,0⟩,⟨48190,0⟩,⟨83189,0⟩,⟨101373,0⟩,⟨95840,0⟩,⟨102638,0⟩,⟨115894,0⟩,⟨126110,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨552649,0⟩,⟨-122605,0⟩,⟨-126626,0⟩,⟨77932,0⟩,⟨32808,0⟩,⟨-18661,0⟩,⟨8074,0⟩,⟨18558,0⟩,⟨9060,0⟩,⟨9396,0⟩,⟨13783,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨558509,0⟩,⟨-111207,0⟩,⟨-131616,0⟩,⟨76624,0⟩,⟨33869,0⟩,⟨-19296,0⟩,⟨6850,0⟩,⟨17996,0⟩,⟨8547,0⟩,⟨8673,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨575448,0⟩,⟨-93279,0⟩,⟨-112603,0⟩,⟨101101,0⟩,⟨60463,0⟩,⟨8049,0⟩,⟨36753,0⟩,⟨50939,0⟩,⟨44509,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨571743,0⟩,⟨-100661,0⟩,⟨-113842,0⟩,⟨98250,0⟩,⟨56148,0⟩,⟨4440,0⟩,⟨33380,0⟩,⟨47179,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨568038,0⟩,⟨-101514,0⟩,⟨-117743,0⟩,⟨92546,0⟩,⟨51108,0⟩,⟨-565,0⟩,⟨27660,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨571838,0⟩,⟨-95735,0⟩,⟨-113582,0⟩,⟨97831,0⟩,⟨57633,0⟩,⟨6449,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨574086,0⟩,⟨-93144,0⟩,⟨-110210,0⟩,⟨101803,0⟩,⟨62295,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨574330,0⟩,⟨-91607,0⟩,⟨-108945,0⟩,⟨102782,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨575978,0⟩,⟨-87967,0⟩,⟨-106244,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨578409,0⟩,⟨-83568,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨580691,0⟩]]
  upperC := ![![⟨458965,0⟩,⟨-69933,69933⟩,⟨-142497,142497⟩,⟨-42355,42355⟩,⟨-46540,46540⟩,⟨-73834,73834⟩,⟨-70718,70718⟩,⟨-67869,67869⟩,⟨-72599,72599⟩,⟨-76044,76044⟩,⟨-78149,78149⟩,⟨-81125,81125⟩,⟨-84601,84601⟩,⟨-88144,88144⟩,⟨525328144,-297988310⟩],![⟨0,0⟩,⟨469500,0⟩,⟨-65175,0⟩,⟨-75884,0⟩,⟨45293,0⟩,⟨24450,0⟩,⟨1185,0⟩,⟨10686,0⟩,⟨14829,0⟩,⟨12501,0⟩,⟨12630,0⟩,⟨13839,0⟩,⟨14344,0⟩,⟨14794,0⟩,⟨-167107700,-19150775⟩],![⟨0,0⟩,⟨0,0⟩,⟨510922,0⟩,⟨-59899,0⟩,⟨-65817,0⟩,⟨73224,0⟩,⟨50857,0⟩,⟨24771,0⟩,⟨36609,0⟩,⟨42297,0⟩,⟨40529,0⟩,⟨41722,0⟩,⟨44256,0⟩,⟨46051,0⟩,⟨-294175978,-59259589⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨480038,0⟩,⟨-83381,0⟩,⟨-84876,0⟩,⟨43529,0⟩,⟨20482,0⟩,⟨-4337,0⟩,⟨5902,0⟩,⟨10035,0⟩,⟨7310,0⟩,⟨7291,0⟩,⟨8371,0⟩,⟨-98657516,-10580820⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨482170,0⟩,⟨-78351,0⟩,⟨-86123,0⟩,⟨43200,0⟩,⟨21058,0⟩,⟨-4109,0⟩,⟨5975,0⟩,⟨10242,0⟩,⟨7556,0⟩,⟨7527,0⟩,⟨-106018617,-10456598⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨488020,0⟩,⟨-72551,0⟩,⟨-79909,0⟩,⟨50765,0⟩,⟨28836,0⟩,⟨3750,0⟩,⟨14222,0⟩,⟨18876,0⟩,⟨16542,0⟩,⟨-150479952,-21656995⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨487019,0⟩,⟨-74443,0⟩,⟨-80331,0⟩,⟨50014,0⟩,⟨27842,0⟩,⟨2852,0⟩,⟨13350,0⟩,⟨17957,0⟩,⟨-139523962,-19616263⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨486088,0⟩,⟨-74712,0⟩,⟨-81154,0⟩,⟨48868,0⟩,⟨26808,0⟩,⟨1840,0⟩,⟨12271,0⟩,⟨-127569141,-17289128⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨486911,0⟩,⟨-73458,0⟩,⟨-80245,0⟩,⟨49917,0⟩,⟨27997,0⟩,⟨3069,0⟩,⟨-139712125,-18227909⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨487406,0⟩,⟨-72815,0⟩,⟨-79526,0⟩,⟨50686,0⟩,⟨28832,0⟩,⟨-150816077,-19176907⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨487566,0⟩,⟨-72372,0⟩,⟨-79142,0⟩,⟨51025,0⟩,⟨-104977402,-18139168⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨487906,0⟩,⟨-71670,0⟩,⟨-78584,0⟩,⟨-97914905,-16060151⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨488334,0⟩,⟨-70890,0⟩,⟨-299337186,-21177774⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨488745,0⟩,⟨-166176926,-26018461⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨603959492,0⟩]]
theorem valid15 : Valid data15 := by decide +kernel
private theorem case15 : Construction 15 := certificate_sound (by norm_num) (by norm_num) data15 valid15

def data16 : Data 15 where
  Rnum := 4893297946607
  vector := ![⟨865997666805,-500048038781⟩,⟨-271261263933,-30440275964⟩,⟨-474387825897,-92483422851⟩,⟨-164190170134,-17328700830⟩,⟨-175107955234,-17213007170⟩,⟨-241751714394,-33834261375⟩,⟨-228755073624,-30890705852⟩,⟨-214923815206,-27771927985⟩,⟨-214789964958,-28788839502⟩,⟨-228957165230,-29355338637⟩,⟨-242272833288,-29875121854⟩,⟨-173597941898,-28685155932⟩,⟨-163081952097,-25748257054⟩,⟨-482161778590,-33421731385⟩,⟨-269899046728,-40789561005⟩,⟨1000000000000,0⟩]
  zAlpha := ⟨529709,848180⟩
  zBeta := ⟨34596,-999401⟩
  zEnds := ⟨-258846,-965919⟩
  lowerC := ![![⟨506805,0⟩,⟨-95242,95242⟩,⟨-202533,202533⟩,⟨-52734,52734⟩,⟨-60388,60388⟩,⟨-115764,115764⟩,⟨-108435,108435⟩,⟨-100611,100611⟩,⟨-114071,114071⟩,⟨-123704,123704⟩,⟨-128604,128604⟩,⟨-137414,137414⟩,⟨-148772,148772⟩,⟨-160581,160581⟩,⟨-174383,174383⟩],![⟨0,0⟩,⟨524399,0⟩,⟨-79906,0⟩,⟨-100353,0⟩,⟨73388,0⟩,⟨38653,0⟩,⟨-2599,0⟩,⟨17733,0⟩,⟨26865,0⟩,⟨20729,0⟩,⟨21402,0⟩,⟨25310,0⟩,⟨26875,0⟩,⟨28410,0⟩,⟨31140,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨597523,0⟩,⟨-74577,0⟩,⟨-85401,0⟩,⟨131496,0⟩,⟨92648,0⟩,⟨42794,0⟩,⟨71745,0⟩,⟨86480,0⟩,⟨81840,0⟩,⟨86783,0⟩,⟨96538,0⟩,⟨103815,0⟩,⟨112072,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨539861,0⟩,⟨-114918,0⟩,⟨-118267,0⟩,⟨70823,0⟩,⟨30451,0⟩,⟨-15017,0⟩,⟨7758,0⟩,⟨16710,0⟩,⟨9009,0⟩,⟨9224,0⟩,⟨12674,0⟩,⟨13306,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨544826,0⟩,⟨-104907,0⟩,⟨-122228,0⟩,⟨69778,0⟩,⟨31469,0⟩,⟨-15293,0⟩,⟨7008,0⟩,⟨16475,0⟩,⟨8841,0⟩,⟨8927,0⟩,⟨12455,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨558922,0⟩,⟨-90206,0⟩,⟨-106575,0⟩,⟨89707,0⟩,⟨52824,0⟩,⟨6565,0⟩,⟨30689,0⟩,⟨42229,0⟩,⟨36602,0⟩,⟨39142,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨555954,0⟩,⟨-96050,0⟩,⟨-107632,0⟩,⟨87423,0⟩,⟨49474,0⟩,⟨3709,0⟩,⟨27984,0⟩,⟨39250,0⟩,⟨33603,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨553033,0⟩,⟨-96755,0⟩,⟨-110603,0⟩,⟨83119,0⟩,⟨45660,0⟩,⟨-63,0⟩,⟨23742,0⟩,⟨34857,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨555943,0⟩,⟨-92346,0⟩,⟨-107437,0⟩,⟨87068,0⟩,⟨50438,0⟩,⟨5013,0⟩,⟨29333,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨557655,0⟩,⟨-90338,0⟩,⟨-104899,0⟩,⟨89990,0⟩,⟨53796,0⟩,⟨8828,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨557902,0⟩,⟨-89118,0⟩,⟨-103885,0⟩,⟨90793,0⟩,⟨55126,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨559128,0⟩,⟨-86453,0⟩,⟨-101894,0⟩,⟨92930,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨560876,0⟩,⟨-83301,0⟩,⟨-99099,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨562513,0⟩,⟨-80046,0⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨564425,0⟩]]
  upperC := ![![⟨452063,0⟩,⟨-66734,66734⟩,⟨-135372,135372⟩,⟨-40928,40928⟩,⟨-44745,44745⟩,⟨-69411,69411⟩,⟨-66677,66677⟩,⟨-64214,64214⟩,⟨-68299,68299⟩,⟨-71293,71293⟩,⟨-73167,73167⟩,⟨-75746,75746⟩,⟨-78726,78726⟩,⟨-81762,81762⟩,⟨-85027,85027⟩,⟨522493162,-301700199⟩],![⟨0,0⟩,⟨461809,0⟩,⟨-63040,0⟩,⟨-72747,0⟩,⟨42116,0⟩,⟨22832,0⟩,⟨1455,0⟩,⟨9935,0⟩,⟨13630,0⟩,⟨11617,0⟩,⟨11716,0⟩,⟨12738,0⟩,⟨13174,0⟩,⟨13559,0⟩,⟨14137,0⟩,⟨-163663463,-18365911⟩],![⟨0,0⟩,⟨0,0⟩,⟨499919,0⟩,⟨-57881,0⟩,⟨-63278,0⟩,⟨67312,0⟩,⟨46717,0⟩,⟨22940,0⟩,⟨33360,0⟩,⟨38344,0⟩,⟨36821,0⟩,⟨37804,0⟩,⟨39914,0⟩,⟨41410,0⟩,⟨42934,0⟩,⟨-286218304,-55799169⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨471735,0⟩,⟨-79531,0⟩,⟨-80874,0⟩,⟨40457,0⟩,⟨19257,0⟩,⟨-3464,0⟩,⟨5634,0⟩,⟨9323,0⟩,⟨6986,0⟩,⟨6959,0⟩,⟨7872,0⟩,⟨8137,0⟩,⟨-99062930,-10455143⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨473612,0⟩,⟨-75009,0⟩,⟨-81922,0⟩,⟨40182,0⟩,⟨19774,0⟩,⟨-3233,0⟩,⟨5733,0⟩,⟨9532,0⟩,⟨7228,0⟩,⟨7195,0⟩,⟨8130,0⟩,⟨-105650094,-10385340⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨478766,0⟩,⟨-69923,0⟩,⟨-76476,0⟩,⟨46775,0⟩,⟨26528,0⟩,⟨3583,0⟩,⟨12863,0⟩,⟨16970,0⟩,⟨14945,0⟩,⟨15231,0⟩,⟨-145859086,-20413644⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨477913,0⟩,⟨-71530,0⟩,⟨-76841,0⟩,⟨46138,0⟩,⟨25695,0⟩,⟨2826,0⟩,⟨12125,0⟩,⟨16197,0⟩,⟨14162,0⟩,⟨-138017665,-18637673⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨477124,0⟩,⟨-71762,0⟩,⟨-77526,0⟩,⟨45188,0⟩,⟨24835,0⟩,⟨1986,0⟩,⟨11234,0⟩,⟨15289,0⟩,⟨-129672684,-16755983⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨477811,0⟩,⟨-70712,0⟩,⟨-76762,0⟩,⟨46062,0⟩,⟨25819,0⟩,⟨3000,0⟩,⟨12298,0⟩,⟨-129591926,-17369529⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨478228,0⟩,⟨-70162,0⟩,⟨-76157,0⟩,⟨46705,0⟩,⟨26514,0⟩,⟨3742,0⟩,⟨-138139597,-17711321⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨478372,0⟩,⟨-69778,0⟩,⟨-75821,0⟩,⟨47004,0⟩,⟨26878,0⟩,⟨-146173503,-18024929⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨478659,0⟩,⟨-69189,0⟩,⟨-75349,0⟩,⟨47472,0⟩,⟨-104739026,-17306972⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨479015,0⟩,⟨-68539,0⟩,⟨-74785,0⟩,⟨-98394286,-15535017⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨479358,0⟩,⟨-67882,0⟩,⟨-290908729,-20164749⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨479725,0⟩,⟨-162841568,-24610072⟩],![⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨0,0⟩,⟨603342756,0⟩]]
theorem valid16 : Valid data16 := by decide +kernel
private theorem case16 : Construction 16 := certificate_sound (by norm_num) (by norm_num) data16 valid16
end Small

open Matrix
namespace Full
/-- Entanglement is stated through the nonzero edge condition, as in the binding convention.
The Section 6 matrices are unnormalized positive operators. -/
def claim : Prop := ∀ n : ℕ, 3≤n → ∃ (a b : Fin n → ℂ) (r : ℝ),
  D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Admissible a b ∧ D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.LargestRoot a b r ∧ D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.SimpleRoot a b r ∧ 1<r ∧
  D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.PPT (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.rho a b r) ∧ D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.Edge (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.rho a b r) ∧ D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.rho a b r≠0 ∧
  Matrix.rank (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.rho a b r)=n*n-1 ∧ Matrix.rank (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.partialTranspose (D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.rho a b r))=n*n-2*n+3
theorem construction {n : ℕ} (hn : 3≤n) : Small.Construction n := by
  by_cases h17 : 17≤n
  · obtain ⟨r,w,ha,h5,hr,hs,hw,hk,hstar,hppt,hedge,hrank,hgamma⟩ := D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformPerturbedParameters.Anchor.n_ge_17 h17
    exact ⟨r,w,ha,by linarith,hr,hs,hw,hk,hstar,hppt,hedge,hrank,hgamma⟩
  · have hn16 : n≤16 := by omega
    interval_cases n
    · exact Small.case3
    · exact Small.case4
    · exact Small.case5
    · exact Small.case6
    · exact Small.case7
    · exact Small.case8
    · exact Small.case9
    · exact Small.case10
    · exact Small.case11
    · exact Small.case12
    · exact Small.case13
    · exact Small.case14
    · exact Small.case15
    · exact Small.case16
theorem result : claim := by
  intro n hn
  obtain ⟨r,w,ha,h1,hr,hs,hw,hk,hstar,hppt,hedge,hrank,hgamma⟩ := construction hn
  have hnonzero : D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.rho (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha n) (D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta n) r≠0 := by
    intro hz
    rw [hz,Matrix.rank_zero] at hrank
    have hm := Nat.mul_le_mul hn hn
    omega
  refine ⟨D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.alpha n,D5.S3.Quantum.Entanglement.ChoiKiemKye.UniformParameterAnchor.Uniform.beta n,r,ha,hr,hs,h1,hppt,hedge,hnonzero,hrank,?_⟩
  simpa only [D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.rho,D5.S3.Quantum.Entanglement.ChoiKiemKye.ConstructionReduction.partialTranspose_involutive] using hgamma
end Full
#print Full.claim
#print axioms Full.result


end D5.S3.Quantum.Entanglement.ChoiKiemKye.MaximalBirankEdgeStates
