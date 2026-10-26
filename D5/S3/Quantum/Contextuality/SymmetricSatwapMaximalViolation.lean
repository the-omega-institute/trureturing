/- GID: D5/S3/Quantum/Contextuality/SymmetricSatwapMaximalViolation
   generality: G
   mirror-B: D5/B/S3/Quantum/Contextuality/SymmetricSatwapMaximalViolation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Identical TW measurements attain the symmetric SATWAP value in every dimension. -/
import D5.S3.Quantum.Measurements.CliffordJointMeasurability.ShiftedFourierOperatorCertificate
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Kronecker
open Complex Matrix
open D5.S3.Quantum.Measurements.CliffordJointMeasurability.ShiftedFourierOperatorCertificate
namespace D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation
def omegaPow (d : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * I * (t : ℂ) / d)
def twMatrix (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal (fun i : Fin d => if i.val = 0 then -1 else 1) *
    (Matrix.of fun (i j : Fin d) => (1 : ℂ) / ((d : ℂ) *
      (Real.sin (((i.val : ℝ) - j.val - 1 / 2) * Real.pi / d) : ℂ)))
private def basisProjector (d : ℕ) (a : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => if i = a ∧ j = a then 1 else 0
def measurement (d : ℕ) (x : Fin 2) (a : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  if x = 0 then basisProjector d a
  else twMatrix d * basisProjector d a * (twMatrix d)ᴴ
def prob (d : ℕ) (ψ : EuclideanSpace ℂ (Fin d × Fin d))
    (x y : Fin 2) (a b : Fin d) : ℂ :=
  inner ℂ ψ (WithLp.toLp 2
    ((measurement d x a ⊗ₖ measurement d y b).mulVec ψ))
def correlator (d : ℕ) (ψ : EuclideanSpace ℂ (Fin d × Fin d))
    (x y : Fin 2) (k : ℕ) : ℂ :=
  ∑ a : Fin d, ∑ b : Fin d,
    omegaPow d (-((k : ℝ) * ((a.val : ℝ) + b.val))) * prob d ψ x y a b
def satwapValue (d : ℕ) (ψ : EuclideanSpace ℂ (Fin d × Fin d)) : ℂ :=
  ∑ k ∈ Finset.Icc 1 (d - 1),
    let a := (1 - I) / 2 * omegaPow d ((k : ℝ) / 4)
    omegaPow d (-2 * (k : ℝ)) *
      (a * correlator d ψ 0 0 k + conj a * correlator d ψ 0 1 k +
        conj a * correlator d ψ 1 0 k) +
      omegaPow d (-3 * (k : ℝ)) * a * correlator d ψ 1 1 k
def swap {d : ℕ} (ψ : EuclideanSpace ℂ (Fin d × Fin d)) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  WithLp.toLp 2 (fun ij => ψ (ij.2, ij.1))
def reducedState {d : ℕ} (ψ : EuclideanSpace ℂ (Fin d × Fin d)) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun i i' => ∑ j, ψ (i, j) * conj (ψ (i', j))
def claim : Prop := ∀ d : ℕ, 2 ≤ d →
  ∃ ψ : EuclideanSpace ℂ (Fin d × Fin d),
    ‖ψ‖ = 1 ∧ swap ψ = ψ ∧
    reducedState ψ = (1 / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) ∧
    satwapValue d ψ = 2 * ((d : ℂ) - 1)
private def offset (x : Fin 2) : ℝ := if x = 0 then 7 / 8 else 11 / 8
private def fourierBasis (d : ℕ) (x : Fin 2) : Matrix (Fin d) (Fin d) ℂ :=
  fun j a => omegaPow d ((j.val : ℝ) * ((a.val : ℝ) + offset x)) / Real.sqrt d
private def gaugeD (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal (fun a => omegaPow d ((a.val : ℝ) / 2))
private def gaugeF (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal (fun b => -I * omegaPow d (-((b.val : ℝ) + 1 / 2) / 2))
private def transport (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal (fun i : Fin d => if i.val = 0 then -1 else 1) *
    (gaugeD d)ᴴ * (fourierBasis d 0)ᴴ
private def state (d : ℕ) : EuclideanSpace ℂ (Fin d × Fin d) :=
  WithLp.toLp 2 (fun ij =>
    (∑ m, transport d ij.1 m * transport d ij.2 m) / Real.sqrt d)
private lemma omega_zero (d : ℕ) : omegaPow d 0 = 1 := by
  simp only [omegaPow, Complex.ofReal_zero, mul_zero, zero_div, Complex.exp_zero]
private lemma omega_mul (d : ℕ) (s t : ℝ) :
    omegaPow d s * omegaPow d t = omegaPow d (s + t) := by
  unfold omegaPow; rw [← Complex.exp_add]; congr 1; push_cast; ring
private lemma omega_conj (d : ℕ) (t : ℝ) : conj (omegaPow d t) = omegaPow d (-t) := by
  unfold omegaPow; rw [← Complex.exp_conj]; congr 1
  simp only [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
    map_natCast, Complex.ofReal_neg]
  ring
private lemma fourier_unitary (d : ℕ) (hd : 2 ≤ d) (x : Fin 2) :
    (fourierBasis d x)ᴴ * fourierBasis d x = 1 := by
  classical
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hs : (Real.sqrt d : ℂ) * Real.sqrt d = d := by
    exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg d)
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply]
  have ht (j : Fin d) :
      (fourierBasis d x)ᴴ a j * fourierBasis d x j b =
        omegaPow d ((j.val : ℝ) * ((b.val : ℝ) - a.val)) / d := by
    change conj (omegaPow d _ / (Real.sqrt d : ℂ)) *
      (omegaPow d _ / (Real.sqrt d : ℂ)) = _
    rw [map_div₀, Complex.conj_ofReal, omega_conj, div_mul_div_comm, hs, omega_mul]; congr 2; ring
  simp_rw [ht]
  rw [← Finset.sum_div]
  have he : (∑ j : Fin d, omegaPow d ((j.val : ℝ) * ((b.val : ℝ) - a.val))) =
      if b = a then (d : ℂ) else 0 := by
    change (∑ j : Fin d, (fun j : ℕ => omegaPow d
      ((j : ℝ) * ((b.val : ℝ) - a.val))) j) = _
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => omegaPow d
      ((j : ℝ) * ((b.val : ℝ) - a.val))) d]
    convert exponential_sum_orthogonality d (by omega) b a using 1
    apply Finset.sum_congr rfl; intro j hj; unfold omegaPow; congr 1; push_cast; ring
  rw [he]
  by_cases hab : a = b
  · simp [hab, hd0]
  · simp [hab, Ne.symm hab]
private lemma gauge_identity (d : ℕ) (hd : 2 ≤ d) :
    (fourierBasis d 0)ᴴ * fourierBasis d 1 =
      gaugeD d * (Matrix.of fun (a b : Fin d) => (1 : ℂ) / ((d : ℂ) *
        (Real.sin (((a.val : ℝ) - b.val - 1 / 2) * Real.pi / d) : ℂ))) * gaugeF d := by
  classical
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hs : (Real.sqrt d : ℂ) * Real.sqrt d = d := by
    exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg d)
  ext a b
  let δ : ℝ := (b.val : ℝ) - a.val + 1 / 2
  let θ : ℝ := ((a.val : ℝ) - b.val - 1 / 2) * Real.pi / d
  have hp : omegaPow d δ ^ d = -1 := by
    unfold omegaPow
    rw [← Complex.exp_nat_mul]
    conv_rhs => rw [← Complex.exp_pi_mul_I]
    apply Complex.exp_eq_exp_iff_exists_int.mpr
    refine ⟨(b.val : ℤ) - a.val, ?_⟩
    dsimp only [δ]; push_cast; field_simp; ring
  have hq : omegaPow d δ ≠ 1 := by
    intro h
    rw [h, one_pow] at hp
    norm_num at hp
  have hgeom : (∑ j : Fin d, omegaPow d ((j.val : ℝ) * δ)) =
      -2 / (omegaPow d δ - 1) := by
    change (∑ j : Fin d, (fun j : ℕ => omegaPow d ((j : ℝ) * δ)) j) = _
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => omegaPow d ((j : ℝ) * δ)) d]
    have hj (j : ℕ) : omegaPow d ((j : ℝ) * δ) = omegaPow d δ ^ j := by
      unfold omegaPow
      rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
    simp_rw [hj]
    rw [geom_sum_eq hq, hp]
    norm_num
  have hsin : 2 * (Real.sin θ : ℂ) =
      (omegaPow d (δ / 2) - omegaPow d (-δ / 2)) * I := by
    rw [Complex.ofReal_sin, Complex.two_sin]
    congr 2 <;> unfold omegaPow <;> congr 1 <;> dsimp only [δ, θ] <;> push_cast <;> ring
  have hm : omegaPow d δ * omegaPow d (-δ / 2) = omegaPow d (δ / 2) := by
    rw [omega_mul]
    congr 1; ring
  have hden : (omegaPow d δ - 1) * (-I * omegaPow d (-δ / 2)) =
      -2 * (Real.sin θ : ℂ) := by
    calc
      _ = -(omegaPow d δ * omegaPow d (-δ / 2) - omegaPow d (-δ / 2)) * I := by ring
      _ = _ := by rw [hm]; linear_combination hsin
  have hs0 : (Real.sin θ : ℂ) ≠ 0 := by
    intro h
    have hn : (omegaPow d δ - 1) * (-I * omegaPow d (-δ / 2)) ≠ 0 :=
      mul_ne_zero (sub_ne_zero.mpr hq)
        (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (Complex.exp_ne_zero _))
    apply hn
    rw [hden, h, mul_zero]
  have hv : -2 / (omegaPow d δ - 1) = -I * omegaPow d (-δ / 2) / (Real.sin θ : ℂ) := by
    apply (div_eq_div_iff (sub_ne_zero.mpr hq) hs0).mpr
    linear_combination -hden
  rw [Matrix.mul_apply]
  simp only [gaugeD, gaugeF, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have ht (j : Fin d) : (fourierBasis d 0)ᴴ a j * fourierBasis d 1 j b =
      omegaPow d ((j.val : ℝ) * δ) / d := by
    change conj (omegaPow d _ / (Real.sqrt d : ℂ)) *
      (omegaPow d _ / (Real.sqrt d : ℂ)) = _
    rw [map_div₀, Complex.conj_ofReal, omega_conj, div_mul_div_comm, hs, omega_mul]; congr 2
    norm_num [offset, δ]
    ring
  simp_rw [ht]
  rw [← Finset.sum_div, hgeom, hv]
  change (-I * omegaPow d (-δ / 2) / (Real.sin θ : ℂ)) / d =
    omegaPow d ((a.val : ℝ) / 2) * (1 / ((d : ℂ) * (Real.sin θ : ℂ))) *
      (-I * omegaPow d (-((b.val : ℝ) + 1 / 2) / 2))
  have hphase : omegaPow d ((a.val : ℝ) / 2) *
      omegaPow d (-((b.val : ℝ) + 1 / 2) / 2) = omegaPow d (-δ / 2) := by
    rw [omega_mul]; congr 1; dsimp only [δ]; ring
  rw [← hphase]; field_simp
private lemma transport_unitary (d : ℕ)
    (hf : (fourierBasis d 0)ᴴ * fourierBasis d 0 = 1) :
    transport d * (transport d)ᴴ = 1 := by
  classical
  have hg : (gaugeD d)ᴴ * gaugeD d = 1 := by
    ext a b
    simp only [gaugeD, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply, Matrix.one_apply, Pi.star_apply, Complex.star_def, omega_conj]
    split_ifs with hab
    · rw [omega_mul, neg_add_cancel, omega_zero]
    · rfl
  let t : Matrix (Fin d) (Fin d) ℂ :=
    Matrix.diagonal (fun i : Fin d => if i.val = 0 then -1 else 1)
  have ht : t * tᴴ = 1 := by
    ext a b
    by_cases hab : a = b
    · subst b
      by_cases ha : a.val = 0 <;> simp [t, ha]
    · simp [t, hab]
  change (t * (gaugeD d)ᴴ * (fourierBasis d 0)ᴴ) *
    (t * (gaugeD d)ᴴ * (fourierBasis d 0)ᴴ)ᴴ = 1
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc
    _ = t * (gaugeD d)ᴴ * ((fourierBasis d 0)ᴴ * fourierBasis d 0) *
        gaugeD d * tᴴ := by noncomm_ring
    _ = t * ((gaugeD d)ᴴ * gaugeD d) * tᴴ := by rw [hf]; simp [Matrix.mul_assoc]
    _ = 1 := by rw [hg]; simpa using ht
private lemma state_swap (d : ℕ) : swap (state d) = state d := by
  ext ij
  change (∑ m, transport d ij.2 m * transport d ij.1 m) / (Real.sqrt d : ℂ) =
    (∑ m, transport d ij.1 m * transport d ij.2 m) / (Real.sqrt d : ℂ)
  simp only [mul_comm]
private lemma state_reduced (d : ℕ)
    (hl : transport d * (transport d)ᴴ = 1) :
    reducedState (state d) = (1 / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  classical
  have hs : (Real.sqrt d : ℂ) * Real.sqrt d = d := by
    exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg d)
  have hl' : (transport d)ᴴ * transport d = 1 := mul_eq_one_comm.mp hl
  have ht : (transport d)ᵀ * ((transport d)ᵀ)ᴴ = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one,
      Matrix.conjTranspose_transpose, Matrix.transpose_conjTranspose] using
        congrArg Matrix.transpose hl'
  have hq : (transport d * (transport d)ᵀ) * (transport d * (transport d)ᵀ)ᴴ = 1 := by
    rw [Matrix.conjTranspose_mul]
    calc
      _ = transport d * ((transport d)ᵀ * ((transport d)ᵀ)ᴴ) * (transport d)ᴴ := by noncomm_ring
      _ = 1 := by rw [ht, Matrix.mul_one, hl]
  ext a b
  change (∑ j, ((∑ m, transport d a m * transport d j m) / (Real.sqrt d : ℂ)) *
    conj ((∑ m, transport d b m * transport d j m) / (Real.sqrt d : ℂ))) = _
  simp only [map_div₀, Complex.conj_ofReal, div_mul_div_comm, hs, ← Finset.sum_div]
  change ((transport d * (transport d)ᵀ) * (transport d * (transport d)ᵀ)ᴴ) a b /
    (d : ℂ) = _
  rw [hq]
  simp only [Matrix.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm, mul_one]
private lemma state_norm (d : ℕ) (hd : 2 ≤ d)
    (hr : reducedState (state d) = (1 / (d : ℂ)) •
      (1 : Matrix (Fin d) (Fin d) ℂ)) : ‖state d‖ = 1 := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hn : (↑(‖state d‖ ^ 2) : ℂ) = 1 := by
    rw [EuclideanSpace.norm_sq_eq, Complex.ofReal_sum, Fintype.sum_prod_type]
    calc
      _ = ∑ i : Fin d, reducedState (state d) i i := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [reducedState, Complex.mul_conj', Complex.ofReal_pow]
      _ = 1 := by simp [hr, Matrix.smul_apply, hd0]
  have hn' : ‖state d‖ ^ 2 = 1 := by exact_mod_cast hn
  nlinarith [norm_nonneg (state d)]
private def measuredBasis (d : ℕ) (x : Fin 2) : Matrix (Fin d) (Fin d) ℂ :=
  if x = 0 then 1 else twMatrix d
private def settingPhase (d : ℕ) (x : Fin 2) (a : Fin d) : ℂ :=
  if x = 0 then (if a.val = 0 then -1 else 1) * omegaPow d (-(a.val : ℝ) / 2)
  else -I * omegaPow d (-((a.val : ℝ) + 1 / 2) / 2)
private lemma omega_norm (d : ℕ) (t : ℝ) : ‖omegaPow d t‖ = 1 := by
  unfold omegaPow
  rw [show 2 * (Real.pi : ℂ) * I * (t : ℂ) / d =
    ((2 * Real.pi * t / d : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _
private lemma setting_phase_norm (d : ℕ) (x : Fin 2) (a : Fin d) :
    ‖settingPhase d x a‖ = 1 := by
  unfold settingPhase
  split_ifs <;> simp only [norm_mul, norm_neg, norm_one, Complex.norm_I, omega_norm, one_mul]
private lemma measurement_rankone (d : ℕ) (x : Fin 2) (a : Fin d) :
    measurement d x a = Matrix.vecMulVec ((measuredBasis d x)ᵀ a)
      (star ((measuredBasis d x)ᵀ a)) := by
  classical
  ext i j
  fin_cases x
  · by_cases hi : i = a <;> by_cases hj : j = a <;>
      simp [measurement, measuredBasis, basisProjector, Matrix.vecMulVec_apply,
        Matrix.one_apply, Pi.star_apply, hi, hj] <;> grind
  · simp [measurement, measuredBasis, basisProjector, Matrix.mul_apply,
      Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, Pi.star_apply, ite_and]
private lemma transport_readout (d : ℕ) (hd : 2 ≤ d)
    (hf : ∀ x, (fourierBasis d x)ᴴ * fourierBasis d x = 1)
    (hg : (fourierBasis d 0)ᴴ * fourierBasis d 1 =
      gaugeD d * (Matrix.of fun (a b : Fin d) => (1 : ℂ) / ((d : ℂ) *
        (Real.sin (((a.val : ℝ) - b.val - 1 / 2) * Real.pi / d) : ℂ))) * gaugeF d)
    (x : Fin 2) :
    (measuredBasis d x)ᴴ * transport d =
      Matrix.diagonal (settingPhase d x) * (fourierBasis d x)ᴴ := by
  classical
  let g := Matrix.diagonal (settingPhase d x)
  have hp : g * gᴴ = 1 := by
    ext a b
    simp only [g, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply, Matrix.one_apply, Pi.star_apply, Complex.star_def]
    split_ifs <;> simp only [Complex.mul_conj', setting_phase_norm, one_pow, Complex.ofReal_one]
  have hgd : (gaugeD d)ᴴ * gaugeD d = 1 := by
    ext a b
    simp only [gaugeD, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply, Matrix.one_apply, Pi.star_apply, Complex.star_def, omega_conj]
    split_ifs <;> simp only [omega_mul, neg_add_cancel, omega_zero]
  have hv : transport d * fourierBasis d x = measuredBasis d x * g := by
    fin_cases x
    · change (Matrix.diagonal (fun i : Fin d => if i.val = 0 then -1 else 1) *
        (gaugeD d)ᴴ * (fourierBasis d 0)ᴴ) * fourierBasis d 0 = 1 * g
      rw [Matrix.mul_assoc, hf 0, Matrix.mul_one, Matrix.one_mul]
      change Matrix.diagonal (fun i : Fin d => if i.val = 0 then -1 else 1) *
        (gaugeD d)ᴴ = Matrix.diagonal (settingPhase d 0)
      simp only [gaugeD, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
      congr 1
      funext a
      simp only [settingPhase, ↓reduceIte, Pi.star_apply,
        Complex.star_def, omega_conj]
      congr 2; ring
    · change (Matrix.diagonal (fun i : Fin d => if i.val = 0 then -1 else 1) *
        (gaugeD d)ᴴ * (fourierBasis d 0)ᴴ) * fourierBasis d 1 = twMatrix d * g
      rw [Matrix.mul_assoc, hg]
      have hgf : g = gaugeF d := rfl
      rw [hgf]; unfold twMatrix
      calc
        _ = Matrix.diagonal (fun i : Fin d => if i.val = 0 then -1 else 1) *
            ((gaugeD d)ᴴ * gaugeD d) *
            (Matrix.of fun (a b : Fin d) => (1 : ℂ) / ((d : ℂ) *
              (Real.sin (((a.val : ℝ) - b.val - 1 / 2) * Real.pi / d) : ℂ))) * gaugeF d := by
                noncomm_ring
        _ = _ := by rw [hgd, Matrix.mul_one]
  have hn : measuredBasis d x = transport d * fourierBasis d x * gᴴ := by
    rw [hv, Matrix.mul_assoc, hp, Matrix.mul_one]
  have hl : (transport d)ᴴ * transport d = 1 :=
    mul_eq_one_comm.mp (transport_unitary d (hf 0))
  rw [hn, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  calc
    _ = (g * (fourierBasis d x)ᴴ) * ((transport d)ᴴ * transport d) := by noncomm_ring
    _ = _ := by rw [hl, Matrix.mul_one]
private lemma fourier_probability (d : ℕ) (hd : 2 ≤ d)
    (hf : ∀ x, (fourierBasis d x)ᴴ * fourierBasis d x = 1)
    (hg : (fourierBasis d 0)ᴴ * fourierBasis d 1 =
      gaugeD d * (Matrix.of fun (a b : Fin d) => (1 : ℂ) / ((d : ℂ) *
        (Real.sin (((a.val : ℝ) - b.val - 1 / 2) * Real.pi / d) : ℂ))) * gaugeF d)
    (x y : Fin 2) (a b : Fin d) :
    prob d (state d) x y a b =
      (↑(‖∑ j : Fin d, omegaPow d (-((j.val : ℝ) *
        ((a.val : ℝ) + b.val + offset x + offset y)))‖ ^ 2) : ℂ) / (d : ℂ) ^ 3 := by
  classical
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hs : (Real.sqrt d : ℂ) * Real.sqrt d = d := by
    exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg d)
  let q := transport d * (transport d)ᵀ
  let r := (measuredBasis d x)ᴴ * q * ((measuredBasis d y)ᴴ)ᵀ
  let v : Fin d × Fin d → ℂ := fun ij => measuredBasis d x ij.1 a * measuredBasis d y ij.2 b
  let c : ℂ := star v ⬝ᵥ (state d)
  have hproj : measurement d x a ⊗ₖ measurement d y b = Matrix.vecMulVec v (star v) := by
    rw [measurement_rankone, measurement_rankone]
    ext i j
    change (measuredBasis d x i.1 a * star (measuredBasis d x j.1 a)) *
      (measuredBasis d y i.2 b * star (measuredBasis d y j.2 b)) =
      (measuredBasis d x i.1 a * measuredBasis d y i.2 b) *
        star (measuredBasis d x j.1 a * measuredBasis d y j.2 b)
    rw [star_mul]; ring
  have hb : prob d (state d) x y a b = (↑(‖c‖ ^ 2) : ℂ) := by
    unfold prob
    rw [hproj, Complex.ofReal_pow, ← Complex.conj_mul']
    change (∑ ij, ((Matrix.vecMulVec v (star v)).mulVec (state d)) ij *
      conj (state d ij)) = _
    simp only [Matrix.mulVec, Matrix.vecMulVec_apply, c, dotProduct, Pi.star_apply,
      Complex.star_def, map_sum, map_mul, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i hi; apply Finset.sum_congr rfl
    intro j hj; ring
  have hc : c = r a b / (Real.sqrt d : ℂ) := by
    change (∑ ij : Fin d × Fin d,
      conj (measuredBasis d x ij.1 a * measuredBasis d y ij.2 b) *
        (q ij.1 ij.2 / (Real.sqrt d : ℂ))) = _
    rw [Fintype.sum_prod_type]
    calc
      _ = (∑ i : Fin d, ∑ j : Fin d, conj (measuredBasis d x i a) * q i j *
          conj (measuredBasis d y j b)) / (Real.sqrt d : ℂ) := by
        simp only [Finset.sum_div]
        apply Finset.sum_congr rfl; intro i hi; apply Finset.sum_congr rfl; intro j hj
        rw [map_mul]; ring
      _ = _ := by
        dsimp only [r]
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
          Complex.star_def, Finset.sum_mul]
        rw [Finset.sum_comm]
  have hr : r = Matrix.diagonal (settingPhase d x) *
      ((fourierBasis d x)ᴴ * ((fourierBasis d y)ᴴ)ᵀ) *
        Matrix.diagonal (settingPhase d y) := by
    change (measuredBasis d x)ᴴ * (transport d * (transport d)ᵀ) *
      ((measuredBasis d y)ᴴ)ᵀ = _
    calc
      _ = ((measuredBasis d x)ᴴ * transport d) *
          ((measuredBasis d y)ᴴ * transport d)ᵀ := by
        rw [Matrix.transpose_mul]; noncomm_ring
      _ = _ := by
        rw [transport_readout d hd hf hg x, transport_readout d hd hf hg y,
          Matrix.transpose_mul, Matrix.diagonal_transpose]
        noncomm_ring
  have ht (j : Fin d) : (fourierBasis d x)ᴴ a j * ((fourierBasis d y)ᴴ)ᵀ j b =
      omegaPow d (-((j.val : ℝ) * ((a.val : ℝ) + b.val + offset x + offset y))) / d := by
    change conj (omegaPow d _ / (Real.sqrt d : ℂ)) *
      conj (omegaPow d _ / (Real.sqrt d : ℂ)) = _
    rw [map_div₀, map_div₀, Complex.conj_ofReal, omega_conj, omega_conj,
      div_mul_div_comm, hs, omega_mul]
    congr 2; ring
  rw [hb, hc, hr, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.mul_apply]
  simp_rw [ht]
  rw [← Finset.sum_div]
  simp only [norm_div, norm_mul, setting_phase_norm, one_mul, mul_one,
    Complex.norm_natCast, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    div_pow, Real.sq_sqrt (Nat.cast_nonneg d), Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_natCast]
  field_simp
  ring_nf
  congr 3
  apply Finset.sum_congr rfl; intro j hj; congr 1; ring
private lemma integer_sum (d : ℕ) (hd : 2 ≤ d) (n : ℤ) :
    (∑ a : Fin d, omegaPow d ((a.val : ℝ) * n)) = if (d : ℤ) ∣ n then (d : ℂ) else 0 := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  let e := ZMod.finEquiv d
  have he (a : Fin d) : e a = (a.val : ZMod d) := by
    have hv : (e a).val = a.val := by cases d with | zero => omega | succ d => rfl
    rw [← ZMod.natCast_zmod_val (e a), hv]
  have ht (a : Fin d) : omegaPow d ((a.val : ℝ) * n) =
      ZMod.stdAddChar (e a * (n : ZMod d)) := by
    rw [he, show (a.val : ZMod d) * (n : ZMod d) =
      (((a.val : ℤ) * n : ℤ) : ZMod d) by push_cast; rfl, ZMod.stdAddChar_coe]
    unfold omegaPow; congr 1; push_cast; ring
  simp_rw [ht]
  rw [Fintype.sum_equiv e.toEquiv (fun a => ZMod.stdAddChar (e a * (n : ZMod d)))
    (fun a => ZMod.stdAddChar (a * (n : ZMod d)))
    (fun _ => rfl), AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar d)]
  simp only [ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.card]
private lemma wrapped_sum (d : ℕ) (k : ℕ) (hk : k < d) (s : ℝ) :
    (∑ l : Fin d, ∑ j : Fin d,
      if (d : ℤ) ∣ (j.val : ℤ) - l.val - k then
        omegaPow d (((j.val : ℝ) - l.val) * s) else 0) =
      ((d - k : ℕ) : ℂ) * omegaPow d ((k : ℝ) * s) +
        k * omegaPow d (((k : ℝ) - d) * s) := by
  classical
  have hdv (j l : Fin d) : (d : ℤ) ∣ (j.val : ℤ) - l.val - k ↔
      j.val = l.val + k ∨ j.val + d = l.val + k := by
    constructor
    · rintro ⟨n, hn⟩
      have hn0 : n ≤ 0 := by
        by_contra h
        have : 1 ≤ n := by omega
        have hj : (j.val : ℤ) < d := by exact_mod_cast j.isLt
        nlinarith
      have hn1 : -1 ≤ n := by
        by_contra h
        have : n ≤ -2 := by omega
        have hl : (l.val : ℤ) < d := by exact_mod_cast l.isLt
        nlinarith
      rcases (show n = 0 ∨ n = -1 by omega) with h | h <;> subst n <;>
        norm_num at hn <;> omega
    · rintro (h | h)
      · exact ⟨0, by omega⟩
      · exact ⟨-1, by omega⟩
  have hsum (l : Fin d) :
      (∑ j : Fin d, if (d : ℤ) ∣ (j.val : ℤ) - l.val - k then
        omegaPow d (((j.val : ℝ) - l.val) * s) else 0) =
      if l.val + k < d then omegaPow d ((k : ℝ) * s)
      else omegaPow d (((k : ℝ) - d) * s) := by
    let j0 : Fin d := if h : l.val + k < d then ⟨l.val + k, h⟩
      else ⟨l.val + k - d, by omega⟩
    have hj0 : j0.val = if l.val + k < d then l.val + k else l.val + k - d := by
      dsimp only [j0]
      split_ifs <;> rfl
    have hm : j0.val = l.val + k ∨ j0.val + d = l.val + k := by split_ifs at hj0 <;> omega
    rw [Finset.sum_eq_single j0]
    · rw [ite_eq_left ((hdv j0 l).mpr hm)]
      split_ifs with h
      · congr 1
        have hv : (j0.val : ℝ) = (l.val : ℝ) + k := by
          exact_mod_cast (show j0.val = l.val + k by simp [h] at hj0; omega)
        rw [hv]; ring
      · congr 1
        have hv : (j0.val : ℝ) + d = (l.val : ℝ) + k := by
          exact_mod_cast (show j0.val + d = l.val + k by rcases hm with hm | hm <;> omega)
        linear_combination s * hv
    · intro j hj hne
      rw [ite_eq_right]; intro hdiv
      apply hne
      apply Fin.ext
      have hm' := (hdv j l).mp hdiv
      rcases hm with hm | hm <;> rcases hm' with hm' | hm' <;> omega
    · simp
  simp_rw [hsum]
  change (∑ l : Fin d, (fun l : ℕ => if l + k < d then omegaPow d ((k : ℝ) * s)
    else omegaPow d (((k : ℝ) - d) * s)) l) = _
  rw [Fin.sum_univ_eq_sum_range (fun l : ℕ => if l + k < d then omegaPow d ((k : ℝ) * s)
    else omegaPow d (((k : ℝ) - d) * s)) d]
  have hs := Finset.sum_range_add (fun l : ℕ => if l + k < d then omegaPow d ((k : ℝ) * s)
    else omegaPow d (((k : ℝ) - d) * s)) (d - k) k
  rw [show d - k + k = d by omega] at hs
  rw [hs]
  calc
    _ = (∑ _l ∈ Finset.range (d - k), omegaPow d ((k : ℝ) * s)) +
        (∑ _l ∈ Finset.range k, omegaPow d (((k : ℝ) - d) * s)) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro l hl; rw [ite_eq_left (by have := Finset.mem_range.mp hl; omega)]
      · apply Finset.sum_congr rfl
        intro l hl; rw [ite_eq_right (by have := Finset.mem_range.mp hl; omega)]
    _ = _ := by simp
private lemma fourier_correlator (d : ℕ) (hd : 2 ≤ d)
    (hp : ∀ x y a b, prob d (state d) x y a b =
      (↑(‖∑ j : Fin d, omegaPow d (-((j.val : ℝ) *
        ((a.val : ℝ) + b.val + offset x + offset y)))‖ ^ 2) : ℂ) / (d : ℂ) ^ 3)
    (x y : Fin 2) (k : ℕ) (hk : k ∈ Finset.Icc 1 (d - 1)) :
    correlator d (state d) x y k =
      omegaPow d ((k : ℝ) * (offset x + offset y)) *
        (((d : ℂ) - k) + k * omegaPow d (-(d : ℝ) * (offset x + offset y))) / d := by
  classical
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hklt : k < d := by have := Finset.mem_Icc.mp hk; omega
  let s := offset x + offset y
  let n : Fin d × Fin d → ℤ := fun jl => (jl.1.val : ℤ) - jl.2.val - k
  let f : Fin d × Fin d → ℂ := fun jl => omegaPow d (((jl.1.val : ℝ) - jl.2.val) * s)
  have he (a b : Fin d) :
      omegaPow d (-((k : ℝ) * ((a.val : ℝ) + b.val))) * prob d (state d) x y a b =
      (∑ j : Fin d, ∑ l : Fin d, f (j, l) *
        omegaPow d ((a.val : ℝ) * n (j, l)) * omegaPow d ((b.val : ℝ) * n (j, l))) /
          (d : ℂ) ^ 3 := by
    rw [hp, ← mul_div_assoc]; congr 1; rw [Complex.ofReal_pow, ← Complex.conj_mul']
    simp only [map_sum, omega_conj, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j hj; apply Finset.sum_congr rfl; intro l hl
    simp only [omega_mul]
    congr 1; dsimp only [f, n, s]; push_cast; ring
  calc
    correlator d (state d) x y k =
        (∑ ab : Fin d × Fin d, ∑ jl : Fin d × Fin d, f jl *
          omegaPow d ((ab.1.val : ℝ) * n jl) * omegaPow d ((ab.2.val : ℝ) * n jl)) /
            (d : ℂ) ^ 3 := by
      unfold correlator
      simp_rw [he]
      simp only [Finset.sum_div, Fintype.sum_prod_type]
    _ = (∑ jl : Fin d × Fin d, f jl *
        (∑ a : Fin d, omegaPow d ((a.val : ℝ) * n jl)) *
        (∑ b : Fin d, omegaPow d ((b.val : ℝ) * n jl))) / (d : ℂ) ^ 3 := by
      rw [Finset.sum_comm]; congr 1; apply Finset.sum_congr rfl; intro jl hjl
      simp only [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ = (d : ℂ) ^ 2 * (∑ l : Fin d, ∑ j : Fin d,
        if (d : ℤ) ∣ (j.val : ℤ) - l.val - k then
          omegaPow d (((j.val : ℝ) - l.val) * s) else 0) / (d : ℂ) ^ 3 := by
      simp_rw [integer_sum d hd]
      simp only [Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
      congr 1; apply Finset.sum_congr rfl; intro l hl; apply Finset.sum_congr rfl; intro j hj
      dsimp only [f, n]
      split_ifs <;> ring
    _ = _ := by
      rw [wrapped_sum d k hklt s, Nat.cast_sub (by omega : k ≤ d)]
      have hf : omegaPow d (((k : ℝ) - d) * s) =
          omegaPow d ((k : ℝ) * s) * omegaPow d (-(d : ℝ) * s) := by
        rw [omega_mul]; congr 1; ring
      rw [hf]
      change (d : ℂ) ^ 2 * (((d : ℂ) - k) * omegaPow d ((k : ℝ) * s) +
        k * (omegaPow d ((k : ℝ) * s) * omegaPow d (-(d : ℝ) * s))) / (d : ℂ) ^ 3 = _
      field_simp; ring
private lemma offset_phase (d : ℕ) (hd : 2 ≤ d) (x y : Fin 2) :
    omegaPow d (-(d : ℝ) * (offset x + offset y)) = if x = y then I else -I := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have h7 : omegaPow d (-(d : ℝ) * (7 / 4)) = I := by
    unfold omegaPow
    conv_rhs => rw [← Complex.exp_pi_div_two_mul_I]
    apply Complex.exp_eq_exp_iff_exists_int.mpr
    refine ⟨-2, ?_⟩
    push_cast; field_simp; ring
  have h9 : omegaPow d (-(d : ℝ) * (9 / 4)) = -I := by
    unfold omegaPow
    conv_rhs => rw [← Complex.exp_neg_pi_div_two_mul_I]
    apply Complex.exp_eq_exp_iff_exists_int.mpr
    refine ⟨-2, ?_⟩
    push_cast; field_simp; ring
  have h11 : omegaPow d (-(d : ℝ) * (11 / 4)) = I := by
    unfold omegaPow
    conv_rhs => rw [← Complex.exp_pi_div_two_mul_I]
    apply Complex.exp_eq_exp_iff_exists_int.mpr
    refine ⟨-3, ?_⟩
    push_cast; field_simp; ring
  fin_cases x <;> fin_cases y <;> norm_num [offset] <;>
    first | simpa only [neg_mul] using h7 | simpa only [neg_mul] using h9 |
      simpa only [neg_mul] using h11
private lemma satwap_sum (d : ℕ) (hd : 2 ≤ d)
    (hc : ∀ x y k, k ∈ Finset.Icc 1 (d - 1) →
      correlator d (state d) x y k =
        omegaPow d ((k : ℝ) * (offset x + offset y)) *
          (((d : ℂ) - k) + k * omegaPow d (-(d : ℝ) * (offset x + offset y))) / d) :
    satwapValue d (state d) = 2 * ((d : ℂ) - 1) := by
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  unfold satwapValue
  calc
    _ = ∑ k ∈ Finset.Icc 1 (d - 1), (2 : ℂ) := by
      apply Finset.sum_congr rfl
      intro k hk
      dsimp only
      rw [hc 0 0 k hk, hc 0 1 k hk, hc 1 0 k hk, hc 1 1 k hk]
      simp only [offset_phase d hd]
      norm_num only [offset, Fin.isValue, ↓reduceIte, Fin.zero_eta, Fin.mk_one,
        show (1 : Fin 2) ≠ 0 by decide, show (0 : Fin 2) ≠ 1 by decide]
      rw [map_mul, map_div₀, map_sub, map_one, Complex.conj_I, map_ofNat, omega_conj]
      have h0 : omegaPow d (-2 * (k : ℝ)) * omegaPow d ((k : ℝ) / 4) *
          omegaPow d ((k : ℝ) * (7 / 4)) = 1 := by
        rw [omega_mul, omega_mul, show -2 * (k : ℝ) + k / 4 + k * (7 / 4) = 0 by ring,
          omega_zero]
      have h1 : omegaPow d (-2 * (k : ℝ)) * omegaPow d (-((k : ℝ) / 4)) *
          omegaPow d ((k : ℝ) * (9 / 4)) = 1 := by
        rw [omega_mul, omega_mul, show -2 * (k : ℝ) + -(k / 4) + k * (9 / 4) = 0 by ring,
          omega_zero]
      have h2 : omegaPow d (-3 * (k : ℝ)) * omegaPow d ((k : ℝ) / 4) *
          omegaPow d ((k : ℝ) * (11 / 4)) = 1 := by
        rw [omega_mul, omega_mul, show -3 * (k : ℝ) + k / 4 + k * (11 / 4) = 0 by ring,
          omega_zero]
      calc
        _ = (omegaPow d (-2 * (k : ℝ)) * omegaPow d ((k : ℝ) / 4) *
              omegaPow d ((k : ℝ) * (7 / 4))) * ((1 - I) / 2 * ((d : ℂ) - k + k * I) / d) +
            (omegaPow d (-2 * (k : ℝ)) * omegaPow d (-((k : ℝ) / 4)) *
              omegaPow d ((k : ℝ) * (9 / 4))) * ((1 + I) * ((d : ℂ) - k - k * I) / d) +
            (omegaPow d (-3 * (k : ℝ)) * omegaPow d ((k : ℝ) / 4) *
              omegaPow d ((k : ℝ) * (11 / 4))) * ((1 - I) / 2 * ((d : ℂ) - k + k * I) / d) := by
                ring
        _ = 2 := by
          rw [h0, h1, h2]
          field_simp
          ring_nf
          simp [Complex.I_sq]
    _ = 2 * ((d : ℂ) - 1) := by
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
      rw [show d - 1 + 1 - 1 = d - 1 by omega, Nat.cast_sub (by omega : 1 ≤ d)]; push_cast; ring
theorem result : claim := by
  intro d hd
  have hf := fourier_unitary d hd
  have hl := transport_unitary d (hf 0)
  have hr := state_reduced d hl
  refine ⟨state d, state_norm d hd hr, state_swap d, hr, ?_⟩
  exact satwap_sum d hd
    (fourier_correlator d hd (fourier_probability d hd hf (gauge_identity d hd)))
end D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation
