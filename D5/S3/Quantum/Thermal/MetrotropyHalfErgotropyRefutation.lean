/- GID: D5/S3/Quantum/Thermal/MetrotropyHalfErgotropyRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Thermal/MetrotropyHalfErgotropyRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Thermal/MetrotropyHalfErgotropyRefutation.claim; result=D5/S3/Quantum/Thermal/MetrotropyHalfErgotropyRefutation.result; claim=D5/S3/Quantum/Thermal/MetrotropyHalfErgotropyRefutation.claim
   digest: A non-stationary pure state has metrotropy greater than half its ergotropy. -/

import D5.S3.Quantum.Measurement.ErrorDisturbanceEndpointRefutation
import D5.S3.Quantum.QuantumChannels.OutputMaximalCoherenceTensorizationRefutation

/-! Rank-one measurements can extract more than half the energy extractable by unitaries. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Thermal.MetrotropyHalfErgotropyRefutation

open scoped BigOperators ComplexOrder _root_.Matrix
open D5.S3.Quantum.Information.SLDSpectralEnergy (IsDensity)
open D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound (expect)
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics (unitaryEvolution)
open D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation (measurementProjector)
open D5.S3.Quantum.QuantumChannels.OutputMaximalCoherenceTensorizationRefutation
  (krausApply kraus_psd)
open D5.S3.Quantum.Measurement.ErrorDisturbanceEndpointRefutation (sum_projectors)

/-- The non-selective rank-one projective measurement in the columns of a unitary. -/
def measured {d : ℕ} (u : Matrix.unitaryGroup (Fin d) ℂ)
    (ρ : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  krausApply (measurementProjector u) ρ

/-- Energy extracted by an optimal rank-one projective measurement. -/
def metrotropy {d : ℕ} (h ρ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  expect ρ h - sInf {e : ℝ | ∃ u : Matrix.unitaryGroup (Fin d) ℂ,
    e = expect (measured u ρ) h}

/-- Energy extracted by an optimal unitary operation. -/
def ergotropy {d : ℕ} (h ρ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  expect ρ h - sInf {e : ℝ | ∃ v : Matrix.unitaryGroup (Fin d) ℂ,
    e = expect (unitaryEvolution v.val ρ) h}

/-- The proposed half-ergotropy inequality for non-stationary density matrices. -/
def claim : Prop :=
  ∀ (d : ℕ) (h ρ : Matrix (Fin d) (Fin d) ℂ),
    h.IsHermitian → IsDensity ρ → h * ρ ≠ ρ * h →
      metrotropy h ρ ≤ ergotropy h ρ / 2

private def h4 : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![(0 : ℂ), 1, 2, 10]

private def psi4 : Fin 4 → ℂ := ![0, 0, (3 / 5 : ℂ) * Complex.I, 4 / 5]

private def u4 : Matrix (Fin 4) (Fin 4) ℂ :=
  (1 / 2 : ℂ) • !![1, 1, 1, 1; 1, -1, 1, -1; 1, 1, -1, -1; 1, -1, -1, 1]

private lemma rho4_trace : (rankOneDensity psi4).trace = 1 := by
  change (Matrix.vecMulVec (![0, 0, (3 / 5 : ℂ) * Complex.I, 4 / 5] : Fin 4 → ℂ)
    (star ![0, 0, (3 / 5 : ℂ) * Complex.I, 4 / 5])).trace = 1
  rw [Matrix.trace_vecMulVec]
  norm_num [dotProduct, Fin.sum_univ_four, Pi.star_apply, map_div₀, map_mul,
    Complex.star_def, Complex.I_mul_I, map_ofNat]
  ring_nf
  norm_num [Complex.I_sq]

private lemma h4_hermitian : h4.IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  fin_cases i <;> norm_num [IsSelfAdjoint]

private lemma commutator_entry :
    (h4 * rankOneDensity psi4 - rankOneDensity psi4 * h4) 2 3 = (-96 / 25 : ℂ) * Complex.I := by
  change ((Matrix.diagonal ![0, 1, 2, (10 : ℂ)] *
    Matrix.vecMulVec (![0, 0, (3 / 5 : ℂ) * Complex.I, 4 / 5] : Fin 4 → ℂ)
      (star ![0, 0, (3 / 5 : ℂ) * Complex.I, 4 / 5]) -
    Matrix.vecMulVec (![0, 0, (3 / 5 : ℂ) * Complex.I, 4 / 5] : Fin 4 → ℂ)
      (star ![0, 0, (3 / 5 : ℂ) * Complex.I, 4 / 5]) *
      Matrix.diagonal ![0, 1, 2, (10 : ℂ)]) 2 3) = _
  simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.vecMulVec_apply, Pi.star_apply]
  apply Complex.ext <;> norm_num [map_div₀, map_ofNat, Complex.mul_re, Complex.mul_im]

private lemma h4_commutator : h4 * rankOneDensity psi4 ≠ rankOneDensity psi4 * h4 := by
  intro he
  have hz := commutator_entry
  rw [he, sub_self] at hz
  have hi := congrArg Complex.im hz
  norm_num at hi

private lemma u4_unitary : u4 ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  change ((1 / 2 : ℂ) • !![1, 1, 1, 1; 1, -1, 1, -1;
    1, 1, -1, -1; 1, -1, -1, 1]) * star ((1 / 2 : ℂ) •
      !![1, 1, 1, 1; 1, -1, 1, -1; 1, 1, -1, -1; 1, -1, -1, 1]) = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_four, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, map_ofNat]

private lemma measured_source {d : ℕ} (u : Matrix.unitaryGroup (Fin d) ℂ)
    (ρ : Matrix (Fin d) (Fin d) ℂ) :
    measured u ρ = ∑ k : Fin d,
      Matrix.vecMulVec (fun i => (u : Matrix (Fin d) (Fin d) ℂ) i k)
        (star (fun j => (u : Matrix (Fin d) (Fin d) ℂ) j k)) * ρ *
      Matrix.vecMulVec (fun i => (u : Matrix (Fin d) (Fin d) ℂ) i k)
        (star (fun j => (u : Matrix (Fin d) (Fin d) ℂ) j k)) := by
  change krausApply (measurementProjector u) ρ = _
  simp only [krausApply,
    D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus,
    LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro k _
  rw [measurementProjector, rankOneDensity, Matrix.conjTranspose_vecMulVec, star_star]

private lemma measured_pure {d : ℕ} (u : Matrix.unitaryGroup (Fin d) ℂ)
    (ψ : Fin d → ℂ) :
    measured u (Matrix.vecMulVec ψ (star ψ)) =
      ∑ k : Fin d,
        ((star (fun i => (u : Matrix (Fin d) (Fin d) ℂ) i k) ⬝ᵥ ψ) *
          (star ψ ⬝ᵥ (fun i => (u : Matrix (Fin d) (Fin d) ℂ) i k))) •
          Matrix.vecMulVec (fun i => (u : Matrix (Fin d) (Fin d) ℂ) i k)
            (star (fun j => (u : Matrix (Fin d) (Fin d) ℂ) j k)) := by
  rw [measured_source]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul,
    Matrix.smul_mul, smul_smul]

private lemma u4_probability (k : Fin 4) :
    ((star (fun i => u4 i k) ⬝ᵥ psi4) * (star psi4 ⬝ᵥ (fun i => u4 i k))) =
      (1 / 4 : ℂ) := by
  let w : Matrix (Fin 4) (Fin 4) ℂ :=
    (1 / 2 : ℂ) • !![1, 1, 1, 1; 1, -1, 1, -1; 1, 1, -1, -1; 1, -1, -1, 1]
  let ψ : Fin 4 → ℂ := ![0, 0, (3 / 5 : ℂ) * Complex.I, 4 / 5]
  change (star (fun i => w i k) ⬝ᵥ ψ) * (star ψ ⬝ᵥ (fun i => w i k)) = _
  simp only [dotProduct, Pi.star_apply, Fin.sum_univ_four]
  fin_cases k <;>
    norm_num [w, ψ, Matrix.smul_apply, smul_eq_mul, map_mul, map_div₀, map_ofNat,
      Complex.ext_iff, Complex.mul_re, Complex.mul_im]

private lemma measured_u4 : measured ⟨u4, u4_unitary⟩ (rankOneDensity psi4) =
    (1 / 4 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  change measured ⟨u4, u4_unitary⟩ (Matrix.vecMulVec psi4 (star psi4)) = _
  rw [measured_pure]
  simp only [u4_probability, ← Finset.smul_sum]
  exact congrArg (fun a : Matrix (Fin 4) (Fin 4) ℂ => (1 / 4 : ℂ) • a)
    (sum_projectors ⟨u4, u4_unitary⟩)

private lemma energy_rho4 : expect (rankOneDensity psi4) h4 = 178 / 25 := by
  change (Matrix.diagonal ![0, 1, 2, (10 : ℂ)] *
    Matrix.vecMulVec (![0, 0, (3 / 5 : ℂ) * Complex.I, 4 / 5] : Fin 4 → ℂ)
      (star ![0, 0, (3 / 5 : ℂ) * Complex.I, 4 / 5])).trace.re = _
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul,
    Matrix.vecMulVec_apply, Pi.star_apply, Fin.sum_univ_four]
  norm_num [map_div₀, map_mul, map_ofNat, Complex.star_def, Complex.mul_re, Complex.mul_im]

private lemma energy_measured_u4 :
    expect (measured ⟨u4, u4_unitary⟩ (rankOneDensity psi4)) h4 = 13 / 4 := by
  rw [measured_u4]
  change (Matrix.diagonal ![0, 1, 2, (10 : ℂ)] *
    ((1 / 4 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ))).trace.re = _
  norm_num [Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_diagonal,
    Fin.sum_univ_four, Complex.mul_re]

private lemma energy_nonneg {d : ℕ} {h σ : Matrix (Fin d) (Fin d) ℂ}
    (hh : h = Matrix.diagonal (fun i => h i i)) (hσ : σ.PosSemidef)
    (hn : ∀ i, 0 ≤ (h i i).re) : 0 ≤ expect σ h := by
  change 0 ≤ (h * σ).trace.re
  conv_rhs => rw [hh]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul, Complex.re_sum,
    Complex.mul_re]
  apply Finset.sum_nonneg
  intro i _
  have hp := Complex.nonneg_iff.mp (hσ.diag_nonneg (i := i))
  rw [← hp.2, mul_zero, sub_zero]
  exact mul_nonneg (hn i) hp.1

private lemma metrotropy_lower : 387 / 100 ≤ metrotropy h4 (rankOneDensity psi4) := by
  have hb : BddBelow {e : ℝ | ∃ u : Matrix.unitaryGroup (Fin 4) ℂ,
      e = expect (measured u (rankOneDensity psi4)) h4} := by
    refine ⟨0, ?_⟩
    rintro e ⟨u, rfl⟩
    refine energy_nonneg (h := h4) ?_ (kraus_psd (measurementProjector u) _
      (Matrix.posSemidef_vecMulVec_self_star psi4)) ?_
    · change Matrix.diagonal ![0, 1, 2, (10 : ℂ)] =
        Matrix.diagonal (fun i => Matrix.diagonal ![0, 1, 2, (10 : ℂ)] i i)
      simp only [Matrix.diagonal_apply_eq]
    · intro i
      change 0 ≤ (Matrix.diagonal ![0, 1, 2, (10 : ℂ)] i i).re
      fin_cases i <;> norm_num [Matrix.diagonal_apply_eq]
  have hi := csInf_le hb ⟨⟨u4, u4_unitary⟩, rfl⟩
  rw [energy_measured_u4] at hi
  change 387 / 100 ≤ expect (rankOneDensity psi4) h4 - _
  rw [energy_rho4]
  linarith

private lemma ergotropy_upper : ergotropy h4 (rankOneDensity psi4) ≤ 178 / 25 := by
  have hn : {e : ℝ | ∃ v : Matrix.unitaryGroup (Fin 4) ℂ,
      e = expect (unitaryEvolution v.val (rankOneDensity psi4)) h4}.Nonempty :=
    ⟨_, 1, rfl⟩
  have hi : 0 ≤ sInf {e : ℝ | ∃ v : Matrix.unitaryGroup (Fin 4) ℂ,
      e = expect (unitaryEvolution v.val (rankOneDensity psi4)) h4} := by
    apply le_csInf hn
    rintro e ⟨v, rfl⟩
    refine energy_nonneg (h := h4) ?_
      ((Matrix.posSemidef_vecMulVec_self_star psi4).mul_mul_conjTranspose_same v.val) ?_
    · change Matrix.diagonal ![0, 1, 2, (10 : ℂ)] =
        Matrix.diagonal (fun i => Matrix.diagonal ![0, 1, 2, (10 : ℂ)] i i)
      simp only [Matrix.diagonal_apply_eq]
    · intro i
      change 0 ≤ (Matrix.diagonal ![0, 1, 2, (10 : ℂ)] i i).re
      fin_cases i <;> norm_num [Matrix.diagonal_apply_eq]
  change expect (rankOneDensity psi4) h4 - _ ≤ _
  rw [energy_rho4]
  linarith

private lemma instance_violates :
    ¬ metrotropy h4 (rankOneDensity psi4) ≤ ergotropy h4 (rankOneDensity psi4) / 2 := by
  have hm := metrotropy_lower
  have he := ergotropy_upper
  linarith

theorem result : ¬ claim := by
  intro hc
  exact instance_violates (hc 4 h4 (rankOneDensity psi4) h4_hermitian
    ⟨Matrix.posSemidef_vecMulVec_self_star psi4, rho4_trace⟩ h4_commutator)

end D5.S3.Quantum.Thermal.MetrotropyHalfErgotropyRefutation
