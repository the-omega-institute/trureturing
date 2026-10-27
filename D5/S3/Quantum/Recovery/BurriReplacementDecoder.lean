/- GID: D5/S3/Quantum/Recovery/BurriReplacementDecoder
   generality: I
   mirror-B: D5/B/S3/Quantum/Recovery/BurriReplacementDecoder
   mirror-E: none(waiver:unfinished-two-direction-comparison)
   anchors: []
   utility: none
   digest: Literal Appendix A objects for a qubit replacement channel and its decoder comparison. -/

import D5.S3.Quantum.Recovery.ReferencePetzChannel
import D5.S3.Quantum.Foundation.FiniteDensityPurification
import Mathlib.Tactic

/-! The replacement instance retains the auxiliary spaces and ordered matrices of
Burri's Appendix A. No assertion of a comparison in the reverse direction is made. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel

namespace D5.S3.Quantum.Recovery.BurriReplacementDecoder

abbrev A := Fin 2
abbrev B := Fin 1
/-- The source environment is literally A times a copy of B. -/
abbrev E := A × B
abbrev P := A × E

local instance : NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix P P ℂ)
    IsSelfAdjoint := IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

def rho : Matrix A A ℂ := Matrix.diagonal ![2 / 3, 1 / 3]
def weight : A → ℝ := ![Real.sqrt 2 / Real.sqrt 3, 1 / Real.sqrt 3]
/-- The reference purification, also used as the allowed fixed R'A' ancilla. -/
def psi (p : P) : ℂ := if p.1 = p.2.1 then (weight p.1 : ℂ) else 0
def X : Matrix P P ℂ := Matrix.vecMulVec psi (star psi)
def sqrtQ : Matrix P P ℂ := Matrix.diagonal fun p =>
  if p.1 = p.2.1 then (if p.1 = 0 then 2 / 3 else 1 / 3)
  else (Real.sqrt 2 : ℂ) / 3
/-- Appendix A.6, with its transpose in the eigenbases of both marginals. -/
def M : Matrix P P ℂ := (sqrtQ * X).transpose

/-- A source right-polar unitary, identity on the two uncorrelated basis vectors. -/
def U : Matrix P P ℂ := fun p q =>
  if p.1 = p.2.1 ∧ q.1 = q.2.1 then
    if p.1 = q.1 then 5 / (3 * (Real.sqrt 3 : ℂ))
    else if p.1 = 0 then (Real.sqrt 2 : ℂ) / (3 * (Real.sqrt 3 : ℂ))
    else -(Real.sqrt 2 : ℂ) / (3 * (Real.sqrt 3 : ℂ))
  else if p = q then 1 else 0

/-- Replacement-channel Stinespring isometry, with the full source environment. -/
def V : Matrix (B × E) A ℂ := fun p i => if p.2.1 = i then 1 else 0
def noiseKraus (e : E) : Matrix B A ℂ := fun b i => V (b, e) i
/-- D' adjoins the fixed unit ancilla psi; B is one dimensional. -/
def prepare : Matrix P B ℂ := fun p _ => psi p
/-- In these literal coordinates W is the identity. -/
def W : Matrix P P ℂ := 1
/-- Appendix A.11, retaining all source environment labels. -/
def sourceKraus (e : E) : Matrix A P ℂ := fun k p => (U * W) (k, e) p
/-- The actual composite D'' D' Kraus operators, before any fidelity evaluation. -/
def swKraus (e : E) : Matrix A B ℂ := sourceKraus e * prepare
def petzKraus (e : E) : Matrix A B ℂ :=
  Matrix.diagonal (fun i => (weight i : ℂ)) * (noiseKraus e)ᴴ

private theorem sqrt_facts :
    (Real.sqrt 2) ^ 2 = 2 ∧ (Real.sqrt 3) ^ 2 = 3 ∧ Real.sqrt 3 ≠ 0 := by
  exact ⟨Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num),
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))⟩

theorem psi_normalized : (∑ p : P, star (psi p) * psi p) = 1 := by
  obtain ⟨h2, h3, ht⟩ := sqrt_facts
  norm_num [psi, weight, Fintype.sum_prod_type, Fin.sum_univ_two,
    Fin.sum_univ_one, Complex.ext_iff, Complex.div_re, Complex.div_im]
  <;> field_simp <;> nlinarith

theorem source_isometry : Vᴴ * V = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [V, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_one]

theorem source_unitary : Uᴴ * U = 1 ∧ U * Uᴴ = 1 := by
  obtain ⟨h2, h3, ht⟩ := sqrt_facts
  constructor <;> ext ⟨i, j, b⟩ ⟨k, l, c⟩
  all_goals fin_cases i <;> fin_cases j <;> fin_cases b <;>
    fin_cases k <;> fin_cases l <;> fin_cases c <;>
    norm_num [U, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_one,
      Complex.ext_iff, Complex.div_re, Complex.div_im]
  all_goals field_simp <;> nlinarith

theorem source_polar_product : M * U = (1 / (Real.sqrt 3 : ℂ)) • X := by
  obtain ⟨h2, h3, ht⟩ := sqrt_facts
  ext ⟨i, j, b⟩ ⟨k, l, c⟩
  fin_cases i <;> fin_cases j <;> fin_cases b <;>
    fin_cases k <;> fin_cases l <;> fin_cases c <;>
    norm_num [M, sqrtQ, X, psi, weight, U, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.vecMulVec_apply, Matrix.smul_apply,
      Matrix.diagonal_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.sum_univ_one, Complex.ext_iff, Complex.div_re, Complex.div_im]
  all_goals field_simp <;> nlinarith

theorem source_square_root :
    CStarMatrix.ofMatrix.symm (CFC.sqrt (CStarMatrix.ofMatrix X)) = X := by
  have hp := Matrix.posSemidef_vecMulVec_self_star psi
  have hn : (star psi) ⬝ᵥ psi = (1 : ℂ) := psi_normalized
  have hsquare : X * X = X := by
    simp only [X, Matrix.vecMulVec_mul_vecMulVec, hn, one_smul]
  have hx : 0 ≤ CStarMatrix.ofMatrix X :=
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hp.nonneg
  have hs : CFC.sqrt (CStarMatrix.ofMatrix X) = CStarMatrix.ofMatrix X := by
    apply CFC.sqrt_unique _ hx
    exact congrArg CStarMatrix.ofMatrix hsquare
  exact congrArg CStarMatrix.ofMatrix.symm hs

theorem source_polar_positive : (M * U).PosSemidef := by
  rw [source_polar_product]
  apply (Matrix.posSemidef_vecMulVec_self_star psi).smul
  exact_mod_cast (one_div_nonneg.mpr (Real.sqrt_nonneg 3))

/-- An actual SVD giving exactly this source unitary, not only a polar label. -/
theorem source_svd :
    ∃ H T : Matrix.unitaryGroup P ℂ, ∃ s : P → ℝ,
      (∀ i, 0 ≤ s i) ∧
      M = (H : Matrix P P ℂ) * Matrix.diagonal (fun i => (s i : ℂ)) * T ∧
      U = (T : Matrix P P ℂ)ᴴ * (H : Matrix P P ℂ)ᴴ := by
  let h := source_polar_positive.isHermitian
  let H := h.eigenvectorUnitary
  let u : Matrix.unitaryGroup P ℂ := ⟨U, by
    simpa only [Unitary.mem_iff, star_eq_conjTranspose] using source_unitary⟩
  have hd : Matrix.diagonal (RCLike.ofReal ∘ h.eigenvalues) =
      Matrix.diagonal (fun i => (h.eigenvalues i : ℂ)) := by
    ext i j
    simp [Matrix.diagonal_apply, Function.comp_apply, RCLike.ofReal_eq_complex_ofReal]
  have hspec : M * U = (H : Matrix P P ℂ) *
      Matrix.diagonal (fun i => (h.eigenvalues i : ℂ)) * (H : Matrix P P ℂ)ᴴ := by
    have hspectral : M * U = (H : Matrix P P ℂ) *
        Matrix.diagonal (RCLike.ofReal ∘ h.eigenvalues) * (H : Matrix P P ℂ)ᴴ := by
      simpa only [Unitary.conjStarAlgAut_apply, H, star_eq_conjTranspose]
        using h.spectral_theorem
    exact hspectral.trans (congrArg
      (fun D : Matrix P P ℂ => (H : Matrix P P ℂ) * D * (H : Matrix P P ℂ)ᴴ) hd)
  refine ⟨H, star H * star u, h.eigenvalues,
    source_polar_positive.eigenvalues_nonneg, ?_, ?_⟩
  · change M = (H : Matrix P P ℂ) * _ * ((H : Matrix P P ℂ)ᴴ * Uᴴ)
    calc
      M = (M * U) * Uᴴ := by
        rw [Matrix.mul_assoc, source_unitary.2, Matrix.mul_one]
      _ = _ := (congrArg (fun Z : Matrix P P ℂ => Z * Uᴴ) hspec).trans
        (Matrix.mul_assoc _ _ _)
  · change U = ((H : Matrix P P ℂ)ᴴ * Uᴴ)ᴴ * (H : Matrix P P ℂ)ᴴ
    have hh : (H : Matrix P P ℂ) * (H : Matrix P P ℂ)ᴴ = 1 := by
      simpa only [star_eq_conjTranspose] using H.prop.2
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, hh, Matrix.mul_one]

def referenceVector (p : A × A) : ℂ :=
  if p.1 = p.2 then (weight p.1 : ℂ) else 0
/-- The physical purification after applying the specified Stinespring map. -/
def sigmaVector (r : A) (b : B) (e : E) : ℂ :=
  ∑ i : A, referenceVector (r, i) * V (b, e) i

/-- Appendix A.9 entrywise, with W=I and the fixed unit ancilla psi. -/
theorem source_purification_identity (r : A) (e : E) (q : P) :
    CStarMatrix.ofMatrix.symm (CFC.sqrt (CStarMatrix.ofMatrix X)) (r, e) q =
      ∑ z : P, W q z * (sigmaVector r 0 e * psi z) := by
  rw [source_square_root]
  have hsigma : sigmaVector r 0 e = psi (r, e) := by
    rcases e with ⟨j, b⟩
    fin_cases r <;> fin_cases j <;> fin_cases b <;>
      simp [sigmaVector, referenceVector, V, psi, Fin.sum_univ_two]
  rw [hsigma]
  change X (r, e) q =
    ((1 : Matrix P P ℂ) *ᵥ (fun z => psi (r, e) * psi z)) q
  rw [Matrix.one_mulVec]
  change psi (r, e) * star (psi q) = psi (r, e) * psi q
  congr 1
  unfold psi
  split_ifs <;> simp

theorem noise_normalization : (∑ e : E, (noiseKraus e)ᴴ * noiseKraus e) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [noiseKraus, V, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_one]

theorem sw_columns (e : E) (k : A) (b : B) :
    swKraus e k b = if k = e.1 then
      (if k = 0 then ((2 * Real.sqrt 2 / 3 : ℝ) : ℂ) else 1 / 3) else 0 := by
  obtain ⟨h2, h3, ht⟩ := sqrt_facts
  rcases e with ⟨j, c⟩
  fin_cases j <;> fin_cases c <;> fin_cases k <;> fin_cases b <;>
    norm_num [swKraus, sourceKraus, prepare, W, Matrix.mul_one, U, psi, weight,
      Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_one,
      Complex.ext_iff, Complex.div_re, Complex.div_im]
  all_goals field_simp <;> nlinarith

theorem decoder_normalizations :
    (∑ e : E, (swKraus e)ᴴ * swKraus e) = 1 ∧
    (∑ e : E, (petzKraus e)ᴴ * petzKraus e) = 1 := by
  obtain ⟨h2, h3, ht⟩ := sqrt_facts
  constructor <;> ext b c
  all_goals fin_cases b <;> fin_cases c
  · norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, sw_columns,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_one,
      Complex.ext_iff, Complex.div_re, Complex.div_im]
    <;> nlinarith
  · norm_num [petzKraus, noiseKraus, V, weight, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.diagonal_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_one,
      Complex.ext_iff, Complex.div_re, Complex.div_im]
    <;> field_simp <;> nlinarith

/-- All three maps use the repository's canonical all-amplification CPTP carrier. -/
theorem actual_channels :
    (∃ channel : QuantumChannel A B, ∀ T : Matrix A A ℂ,
      CStarMatrix.ofMatrix.symm
        (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix T)) =
        ∑ e : E, noiseKraus e * T * (noiseKraus e)ᴴ) ∧
    (∃ channel : QuantumChannel B A, ∀ T : Matrix B B ℂ,
      CStarMatrix.ofMatrix.symm
        (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix T)) =
        ∑ e : E, swKraus e * T * (swKraus e)ᴴ) ∧
    (∃ channel : QuantumChannel B A, ∀ T : Matrix B B ℂ,
      CStarMatrix.ofMatrix.symm
        (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix T)) =
        ∑ e : E, petzKraus e * T * (petzKraus e)ᴴ) := by
  exact ⟨finite_kraus_quantum_channel noiseKraus noise_normalization,
    finite_kraus_quantum_channel swKraus decoder_normalizations.1,
    finite_kraus_quantum_channel petzKraus decoder_normalizations.2⟩


/-- Density matrix of the physical RBE purification produced by V. -/
def physicalState : Matrix (A × (B × E)) (A × (B × E)) ℂ :=
  Matrix.vecMulVec (fun p => sigmaVector p.1 p.2.1 p.2.2)
    (star (fun p => sigmaVector p.1 p.2.1 p.2.2))

/-- The environment marginal in the literal source coordinates. -/
def sigmaE : Matrix E E ℂ := Matrix.diagonal fun e =>
  if e.1 = 0 then 2 / 3 else 1 / 3

theorem physical_marginals :
    (fun p q : P => ∑ b : B, physicalState (p.1, (b, p.2)) (q.1, (b, q.2))) = X ∧
    (fun r t : A => ∑ b : B, ∑ e : E,
      physicalState (r, (b, e)) (t, (b, e))) = rho ∧
    (fun e f : E => ∑ r : A, ∑ b : B,
      physicalState (r, (b, e)) (r, (b, f))) = sigmaE := by
  obtain ⟨h2, h3, ht⟩ := sqrt_facts
  constructor
  · ext ⟨i, j, b⟩ ⟨k, l, c⟩
    fin_cases i <;> fin_cases j <;> fin_cases b <;>
      fin_cases k <;> fin_cases l <;> fin_cases c <;>
      simp [physicalState, sigmaVector, referenceVector, V, X, psi,
        Matrix.vecMulVec_apply, Pi.star_apply, Fin.sum_univ_two, Fin.sum_univ_one]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [physicalState, sigmaVector, referenceVector, V, rho, weight,
        Matrix.vecMulVec_apply, Matrix.diagonal_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_one,
        Complex.ext_iff, Complex.div_re, Complex.div_im]
    all_goals field_simp <;> nlinarith
  · ext ⟨i, b⟩ ⟨j, c⟩
    fin_cases i <;> fin_cases b <;> fin_cases j <;> fin_cases c <;>
      norm_num [physicalState, sigmaVector, referenceVector, V, sigmaE, weight,
        Matrix.vecMulVec_apply, Matrix.diagonal_apply,
        Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_one,
        Complex.ext_iff, Complex.div_re, Complex.div_im]
    all_goals field_simp <;> nlinarith

theorem rho_positive : rho.PosSemidef := by
  rw [rho, Matrix.posSemidef_diagonal_iff]
  intro i
  fin_cases i <;> norm_num [Complex.nonneg_iff]

theorem rho_trace : Matrix.trace rho = 1 := by
  norm_num [rho, Matrix.trace, Fin.sum_univ_two]

/-- The fixed reference state used by the ordinary Petz construction. -/
def referenceState : DensityState A :=
  ⟨CStarMatrix.ofMatrix rho,
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv rho_positive.nonneg, rho_trace⟩

theorem reference_root : cfc Real.sqrt rho =
    Matrix.diagonal (fun i => (weight i : ℂ)) := by
  let S := Matrix.diagonal (fun i => (weight i : ℂ))
  have hS : S.PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    fin_cases i <;> simp [weight, Complex.nonneg_iff]
    all_goals positivity
  have hsquare : S * S = rho := by
    obtain ⟨h2, h3, ht⟩ := sqrt_facts
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [S, weight, rho, Matrix.mul_apply, Matrix.diagonal_apply,
        Fin.sum_univ_two, Complex.ext_iff, Complex.div_re, Complex.div_im]
    all_goals field_simp <;> nlinarith
  have hroot : CFC.sqrt rho = S := CFC.sqrt_unique hsquare hS.nonneg
  rw [CFC.sqrt_eq_real_sqrt _ rho_positive.nonneg, cfcₙ_eq_cfc] at hroot
  exact hroot

/-- sqrtQ is the positive root of the product of the actual physical marginals. -/
theorem product_marginal_root : CFC.sqrt (Matrix.kronecker rho sigmaE) = sqrtQ := by
  have hQ : sqrtQ.PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro ⟨i, j, b⟩
    fin_cases i <;> fin_cases j <;> fin_cases b <;>
      norm_num [Complex.nonneg_iff]
    all_goals positivity
  apply CFC.sqrt_unique _ hQ.nonneg
  obtain ⟨h2, h3, ht⟩ := sqrt_facts
  ext ⟨i, j, b⟩ ⟨k, l, c⟩
  fin_cases i <;> fin_cases j <;> fin_cases b <;>
    fin_cases k <;> fin_cases l <;> fin_cases c <;>
    norm_num [sqrtQ, rho, sigmaE, Matrix.kroneckerMap_apply,
      Matrix.diagonal_apply, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_one, Complex.ext_iff]
  all_goals nlinarith

theorem noise_action (T : Matrix A A ℂ) :
    (∑ e : E, noiseKraus e * T * (noiseKraus e)ᴴ) = Matrix.trace T • 1 := by
  ext b c
  fin_cases b <;> fin_cases c <;>
    simp [noiseKraus, V, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.trace, Matrix.one_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_one]

theorem noise_reference : (∑ e : E, noiseKraus e * rho * (noiseKraus e)ᴴ) = 1 := by
  rw [noise_action, rho_trace, one_smul]

/-- N(rho)=1 is strictly positive on the entire one-dimensional output. -/
theorem petz_output_full_rank :
    (∑ e : E, noiseKraus e * rho * (noiseKraus e)ᴴ).PosDef := by
  rw [noise_reference]
  exact Matrix.PosDef.one

theorem petz_spectral_factors :
    SpectralTransposeRecovery.spectralSupport (1 : Matrix B B ℂ) = 1 ∧
    SpectralTransposeRecovery.spectralInverseSqrt (1 : Matrix B B ℂ) = 1 := by
  constructor <;>
    simp [SpectralTransposeRecovery.spectralSupport,
      SpectralTransposeRecovery.spectralInverseSqrt, cfc_apply_one]

/-- The displayed Kraus operators are exactly the ordinary Petz factors. -/
theorem petz_kraus_identification (e : E) :
    petzKraus e = cfc Real.sqrt rho * (noiseKraus e)ᴴ *
      SpectralTransposeRecovery.spectralInverseSqrt
        (∑ f : E, noiseKraus f * rho * (noiseKraus f)ᴴ) := by
  rw [noise_reference, petz_spectral_factors.2, Matrix.mul_one, reference_root]
  rfl

/-- The canonical reference completion has identically zero defect. The full-rank
Petz factors were identified above, so no singular-branch simplification is needed. -/
theorem ordinary_petz_channel : ∃ recovery : QuantumChannel B A,
    ∀ T : Matrix B B ℂ,
      CStarMatrix.ofMatrix.symm
        (recovery.toCompletelyPositiveMap (CStarMatrix.ofMatrix T)) =
        ∑ e : E, petzKraus e * T * (petzKraus e)ᴴ := by
  have hS : Matrix.trace
      ((Matrix.diagonal fun i => (weight i : ℂ)) *
        (Matrix.diagonal fun i => (weight i : ℂ))ᴴ) = 1 := by
    obtain ⟨h2, h3, ht⟩ := sqrt_facts
    norm_num [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.diagonal_apply, weight, Fin.sum_univ_two,
      Complex.ext_iff, Complex.div_re, Complex.div_im]
    field_simp <;> nlinarith
  obtain ⟨recovery, haction⟩ :=
    ReferencePetzChannel.complete_quantum_channel_with_reference petzKraus
      (1 : Matrix B B ℂ) (Matrix.diagonal fun i => (weight i : ℂ))
      (by simp) (by simp) decoder_normalizations.2 hS
  refine ⟨recovery, fun T => ?_⟩
  simpa only [sub_self, Matrix.zero_mul, Matrix.trace_zero, zero_smul, add_zero]
    using haction T

/-- The canonical purification amplitude is the positive square root of rho. -/
theorem canonical_reference_amplitude (r i : A) :
    cfc Real.sqrt rho r i = referenceVector (r, i) := by
  rw [reference_root]
  simp [referenceVector, Matrix.diagonal_apply]

/-- The actual noise channel, with its finite Kraus realization. -/
def noiseChannel : QuantumChannel A B :=
  (finite_kraus_quantum_channel noiseKraus noise_normalization).choose

theorem noise_channel_action (T : Matrix A A ℂ) :
    CStarMatrix.ofMatrix.symm
      (noiseChannel.toCompletelyPositiveMap (CStarMatrix.ofMatrix T)) =
      Matrix.trace T • 1 := by
  exact ((finite_kraus_quantum_channel noiseKraus noise_normalization).choose_spec T).trans
    (noise_action T)

def swChannel : QuantumChannel B A :=
  (finite_kraus_quantum_channel swKraus decoder_normalizations.1).choose

/-- This channel is chosen from the ordinary, reference-completed Petz theorem. -/
def petzChannel : QuantumChannel B A := ordinary_petz_channel.choose

/-- The source SW output, derived below from U W and the actual ancilla preparation. -/
def swOutput : Matrix A A ℂ := Matrix.diagonal ![8 / 9, 1 / 9]

theorem sw_channel_action (T : Matrix B B ℂ) :
    CStarMatrix.ofMatrix.symm
      (swChannel.toCompletelyPositiveMap (CStarMatrix.ofMatrix T)) =
      Matrix.trace T • swOutput := by
  unfold swChannel
  rw [(finite_kraus_quantum_channel swKraus decoder_normalizations.1).choose_spec T]
  obtain ⟨h2, h3, ht⟩ := sqrt_facts
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, sw_columns,
      swOutput, Matrix.trace, Matrix.diagonal_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_one]
  all_goals push_cast
  all_goals ring_nf
  all_goals simp only [← Complex.ofReal_pow, h2]
  all_goals ring

theorem petz_channel_action (T : Matrix B B ℂ) :
    CStarMatrix.ofMatrix.symm
      (petzChannel.toCompletelyPositiveMap (CStarMatrix.ofMatrix T)) =
      Matrix.trace T • rho := by
  unfold petzChannel
  rw [ordinary_petz_channel.choose_spec T]
  obtain ⟨h2, h3, ht⟩ := sqrt_facts
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [petzKraus, noiseKraus, V, weight, rho, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.diagonal_apply, Matrix.trace,
      Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_one]
  all_goals push_cast; field_simp; ring_nf
  all_goals simp only [← Complex.ofReal_pow, h2, h3]; ring

private theorem composite_reset (decoder : QuantumChannel B A)
    (S : Matrix A A ℂ)
    (h : ∀ T : Matrix B B ℂ, CStarMatrix.ofMatrix.symm
      (decoder.toCompletelyPositiveMap (CStarMatrix.ofMatrix T)) = Matrix.trace T • S)
    (T : Matrix A A ℂ) :
    CStarMatrix.ofMatrix.symm
      ((decoder.comp noiseChannel).toCompletelyPositiveMap (CStarMatrix.ofMatrix T)) =
      Matrix.trace T • S := by
  change CStarMatrix.ofMatrix.symm
    (decoder.toCompletelyPositiveMap
      (noiseChannel.toCompletelyPositiveMap (CStarMatrix.ofMatrix T))) = _
  have hn : noiseChannel.toCompletelyPositiveMap (CStarMatrix.ofMatrix T) =
      CStarMatrix.ofMatrix (Matrix.trace T • (1 : Matrix B B ℂ)) :=
    congrArg CStarMatrix.ofMatrix (noise_channel_action T)
  rw [hn, h]
  simp [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]

/-- The tensor extension acts on the input matrix's reference-indexed blocks.
The channel argument is the actual canonical CPTP composite. -/
def referenceExtension (channel : QuantumChannel A A)
    (T : Matrix (A × A) (A × A) ℂ) : Matrix (A × A) (A × A) ℂ :=
  fun p q => CStarMatrix.ofMatrix.symm
    (channel.toCompletelyPositiveMap
      (CStarMatrix.ofMatrix (fun i j => T (p.1, i) (q.1, j)))) p.2 q.2

/-- The pure density of the canonical reference purification. -/
def referencePure : Matrix (A × A) (A × A) ℂ :=
  Matrix.vecMulVec referenceVector (star referenceVector)

/-- Squared fidelity with a pure reference is its overlap with the actual
recovered density, without an extra square or a square root. -/
def entanglementFidelity (channel : QuantumChannel A A) : ℝ :=
  (star referenceVector ⬝ᵥ (referenceExtension channel referencePure *ᵥ referenceVector)).re

private theorem recovered_purification_of_reset (channel : QuantumChannel A A)
    (S : Matrix A A ℂ)
    (h : ∀ T : Matrix A A ℂ, CStarMatrix.ofMatrix.symm
      (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix T)) = Matrix.trace T • S) :
    referenceExtension channel referencePure = Matrix.kronecker rho S := by
  obtain ⟨h2, h3, ht⟩ := sqrt_facts
  ext ⟨r, i⟩ ⟨t, j⟩
  change (CStarMatrix.ofMatrix.symm (channel.toCompletelyPositiveMap
    (CStarMatrix.ofMatrix (fun k l => referencePure (r, k) (t, l))))) i j = _
  rw [h]
  fin_cases r <;> fin_cases t <;>
    norm_num [referencePure, referenceVector, weight, rho, Matrix.trace,
      Matrix.vecMulVec_apply, Matrix.diagonal_apply, Matrix.kroneckerMap_apply,
      Fin.sum_univ_two]
  all_goals left; apply Complex.ext <;>
    norm_num [Complex.div_re, Complex.div_im] <;> field_simp <;> nlinarith

/-- The full recovered reference-output states, before taking any overlap. -/
theorem actual_recovered_purifications :
    referenceExtension (petzChannel.comp noiseChannel) referencePure =
      Matrix.kronecker rho rho ∧
    referenceExtension (swChannel.comp noiseChannel) referencePure =
      Matrix.kronecker rho swOutput := by
  exact ⟨recovered_purification_of_reset _ _
      (composite_reset petzChannel rho petz_channel_action),
    recovered_purification_of_reset _ _
      (composite_reset swChannel swOutput sw_channel_action)⟩

private theorem pure_kraus_overlap {n : Type*} [Fintype n]
    (v : n → ℂ) (K : Matrix n n ℂ) :
    (star v ⬝ᵥ ((K * Matrix.vecMulVec v (star v) * Kᴴ) *ᵥ v)).re =
      Complex.normSq (star v ⬝ᵥ (K *ᵥ v)) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_conjTranspose]
  simp only [star_star, Matrix.vecMulVec_mulVec, dotProduct_smul]
  have hc : star (K *ᵥ v) ⬝ᵥ v = star (star v ⬝ᵥ (K *ᵥ v)) :=
    star_dotProduct (K *ᵥ v) v
  rw [hc]
  change ((star v ⬝ᵥ (K *ᵥ v)) * star (star v ⬝ᵥ (K *ᵥ v))).re = _
  simp [Complex.normSq_apply, Complex.mul_re]

private theorem reference_extension_kraus {s : Type*} [Fintype s]
    (channel : QuantumChannel A A) (K : s → Matrix A A ℂ)
    (h : ∀ T : Matrix A A ℂ, CStarMatrix.ofMatrix.symm
      (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix T)) =
      ∑ k : s, K k * T * (K k)ᴴ)
    (T : Matrix (A × A) (A × A) ℂ) :
    referenceExtension channel T = ∑ k : s,
      Matrix.kronecker (1 : Matrix A A ℂ) (K k) * T *
        (Matrix.kronecker (1 : Matrix A A ℂ) (K k))ᴴ := by
  ext ⟨r, i⟩ ⟨t, j⟩
  dsimp only [referenceExtension]
  rw [h]
  simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
    Finset.mul_sum, Finset.sum_mul]

/-- The actual tensor-channel overlap is the sum of squared pure amplitudes.
This fixes the squared-fidelity convention without defining fidelity by that sum. -/
theorem actual_fidelity_squared_overlap {s : Type*} [Fintype s]
    (channel : QuantumChannel A A) (K : s → Matrix A A ℂ)
    (h : ∀ T : Matrix A A ℂ, CStarMatrix.ofMatrix.symm
      (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix T)) =
      ∑ k : s, K k * T * (K k)ᴴ) :
    entanglementFidelity channel = ∑ k : s, Complex.normSq
      (star referenceVector ⬝ᵥ
        (Matrix.kronecker (1 : Matrix A A ℂ) (K k) *ᵥ referenceVector)) := by
  unfold entanglementFidelity
  rw [reference_extension_kraus channel K h]
  simp only [Matrix.sum_mulVec, dotProduct_sum, Complex.sum_re]
  exact Finset.sum_congr rfl fun k _ => pure_kraus_overlap referenceVector _

private theorem composite_kraus_action {s : Type*} [Fintype s]
    (decoder : QuantumChannel B A) (D : s → Matrix A B ℂ)
    (hD : ∀ T : Matrix B B ℂ, CStarMatrix.ofMatrix.symm
      (decoder.toCompletelyPositiveMap (CStarMatrix.ofMatrix T)) =
      ∑ e : s, D e * T * (D e)ᴴ) (T : Matrix A A ℂ) :
    CStarMatrix.ofMatrix.symm
      ((decoder.comp noiseChannel).toCompletelyPositiveMap (CStarMatrix.ofMatrix T)) =
      ∑ ef : s × E, (D ef.1 * noiseKraus ef.2) * T *
        (D ef.1 * noiseKraus ef.2)ᴴ := by
  change CStarMatrix.ofMatrix.symm
    (decoder.toCompletelyPositiveMap
      (noiseChannel.toCompletelyPositiveMap (CStarMatrix.ofMatrix T))) = _
  have hn : noiseChannel.toCompletelyPositiveMap (CStarMatrix.ofMatrix T) =
      CStarMatrix.ofMatrix (∑ f : E, noiseKraus f * T * (noiseKraus f)ᴴ) :=
    congrArg CStarMatrix.ofMatrix
      ((finite_kraus_quantum_channel noiseKraus noise_normalization).choose_spec T)
  rw [hn, hD]
  simp only [Fintype.sum_prod_type, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Both actual composites satisfy the squared pure-state overlap formula
with their physical noise and decoder Kraus operators. -/
theorem actual_composite_squared_overlaps :
    entanglementFidelity (petzChannel.comp noiseChannel) =
      ∑ ef : E × E, Complex.normSq (star referenceVector ⬝ᵥ
        (Matrix.kronecker (1 : Matrix A A ℂ)
          (petzKraus ef.1 * noiseKraus ef.2) *ᵥ referenceVector)) ∧
    entanglementFidelity (swChannel.comp noiseChannel) =
      ∑ ef : E × E, Complex.normSq (star referenceVector ⬝ᵥ
        (Matrix.kronecker (1 : Matrix A A ℂ)
          (swKraus ef.1 * noiseKraus ef.2) *ᵥ referenceVector)) := by
  constructor
  · apply actual_fidelity_squared_overlap
    exact composite_kraus_action petzChannel petzKraus ordinary_petz_channel.choose_spec
  · apply actual_fidelity_squared_overlap
    exact composite_kraus_action swChannel swKraus
      (finite_kraus_quantum_channel swKraus decoder_normalizations.1).choose_spec

/-- A strict comparison of the actual Appendix A SW and ordinary Petz channels,
using the nonuniform canonical reference purification. This is one direction only. -/
theorem actual_strict_fidelity :
    entanglementFidelity (petzChannel.comp noiseChannel) = 1 / 3 ∧
    entanglementFidelity (swChannel.comp noiseChannel) = 11 / 27 ∧
    entanglementFidelity (swChannel.comp noiseChannel) -
      entanglementFidelity (petzChannel.comp noiseChannel) = 2 / 27 ∧
    entanglementFidelity (petzChannel.comp noiseChannel) <
      entanglementFidelity (swChannel.comp noiseChannel) := by
  obtain ⟨h2, h3, ht⟩ := sqrt_facts
  have hp : entanglementFidelity (petzChannel.comp noiseChannel) = 1 / 3 := by
    unfold entanglementFidelity
    rw [actual_recovered_purifications.1]
    norm_num [referenceVector, weight, rho, Matrix.mulVec, dotProduct,
      Matrix.kroneckerMap_apply, Matrix.diagonal_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Complex.div_re, Complex.div_im]
    field_simp <;> nlinarith
  have hs : entanglementFidelity (swChannel.comp noiseChannel) = 11 / 27 := by
    unfold entanglementFidelity
    rw [actual_recovered_purifications.2]
    norm_num [referenceVector, weight, rho, swOutput, Matrix.mulVec, dotProduct,
      Matrix.kroneckerMap_apply, Matrix.diagonal_apply, Fintype.sum_prod_type,
      Fin.sum_univ_two, Complex.div_re, Complex.div_im]
    field_simp <;> nlinarith
  exact ⟨hp, hs, by rw [hp, hs]; norm_num, by rw [hp, hs]; norm_num⟩

private theorem polar_product_unique (Uprime : Matrix P P ℂ)
    (hu : Uprime * Uprimeᴴ = 1) (hp : (M * Uprime).PosSemidef) :
    M * Uprime = M * U := by
  have hs (T : Matrix P P ℂ) (hT : T * Tᴴ = 1)
      (hP : (M * T).PosSemidef) : (M * T) * (M * T) = M * Mᴴ := by
    calc
      _ = (M * T) * (M * T)ᴴ := by rw [hP.isHermitian]
      _ = M * Mᴴ := by
        rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
          ← Matrix.mul_assoc T Tᴴ, hT, Matrix.one_mul]
  have h1 := CFC.sqrt_unique (hs Uprime hu hp) hp.nonneg
  have h2 := CFC.sqrt_unique (hs U source_unitary.2 source_polar_positive)
    source_polar_positive.nonneg
  exact h1.symm.trans h2

/-- Every allowed positive right-polar unitary has the same action on the
prepared source vector. Null-space SVD completion cannot change this decoder. -/
theorem source_supported_action_unique (Uprime : Matrix P P ℂ)
    (hu : Uprime * Uprimeᴴ = 1) (hp : (M * Uprime).PosSemidef) :
    Uprime *ᵥ psi = U *ᵥ psi := by
  have hpol := polar_product_unique Uprime hu hp
  have hleft (T : Matrix P P ℂ) (hT : T * Tᴴ = 1) :
      T * (M * T)ᴴ = Mᴴ := by
    rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, hT, Matrix.one_mul]
  have hEq : Uprime * ((1 / (Real.sqrt 3 : ℂ)) • X) =
      U * ((1 / (Real.sqrt 3 : ℂ)) • X) := by
    rw [← source_polar_product, ← hpol, hleft Uprime hu, hpol,
      hleft U source_unitary.2]
  have hx : X *ᵥ psi = psi := by
    rw [X, Matrix.vecMulVec_mulVec]
    have hn : (star psi) ⬝ᵥ psi = (1 : ℂ) := psi_normalized
    rw [hn]
    simp
  have h := congrArg (fun Z : Matrix P P ℂ => Z *ᵥ psi) hEq
  simp only [Matrix.mul_smul, Matrix.smul_mulVec, Matrix.mulVec_mulVec, hx] at h
  have hc : (1 / (Real.sqrt 3 : ℂ)) ≠ 0 := by
    exact one_div_ne_zero (by exact_mod_cast sqrt_facts.2.2)
  funext p
  exact mul_left_cancel₀ hc (congrFun h p)

/-- The actual composite Kraus rows agree for every allowed completion. -/
theorem source_decoder_completion_independent (Uprime : Matrix P P ℂ)
    (hu : Uprime * Uprimeᴴ = 1) (hp : (M * Uprime).PosSemidef) (e : E) :
    (fun k p => Uprime (k, e) p) * prepare = swKraus e := by
  have h := source_supported_action_unique Uprime hu hp
  ext k b
  simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, prepare,
    swKraus, sourceKraus, W, Matrix.mul_one] using congrFun h (k, e)

#print axioms physical_marginals
#print axioms reference_root
#print axioms product_marginal_root
#print axioms ordinary_petz_channel
#print axioms actual_recovered_purifications
#print axioms actual_fidelity_squared_overlap
#print axioms actual_composite_squared_overlaps
#print axioms source_supported_action_unique
#print axioms source_decoder_completion_independent
#print axioms actual_strict_fidelity

#print axioms psi_normalized
#print axioms source_isometry
#print axioms source_unitary
#print axioms source_polar_product
#print axioms source_square_root
#print axioms source_polar_positive
#print axioms source_svd
#print axioms source_purification_identity
#print axioms sw_columns
#print axioms actual_channels

end D5.S3.Quantum.Recovery.BurriReplacementDecoder
