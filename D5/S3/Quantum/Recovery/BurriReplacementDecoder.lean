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
  have hspec : M * U = (H : Matrix P P ℂ) *
      Matrix.diagonal (fun i => (h.eigenvalues i : ℂ)) * (H : Matrix P P ℂ)ᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply, H, Function.comp_apply,
      star_eq_conjTranspose] using h.spectral_theorem
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
  simp only [W, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp [W, X, Matrix.vecMulVec_apply, Matrix.one_apply, psi]

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
