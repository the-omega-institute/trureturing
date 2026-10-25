/- GID: D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation.claim; result=D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation.result; claim=D5/S3/Quantum/Decoherence/DephasingTwoClassicalityBlockRefutation.claim
   digest: A block measurement refutes MUB necessity for time-dependent two-classical dephasing. -/

import D5.S3.Quantum.Dynamics.PositivePauliClockOrder
import D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence
import D5.S3.Quantum.Foundation.FuchsLogarithmBasisRefutation
import D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl
import D5.S3.Observer.Existence.EmpiricalReflexiveSeparation

/-! A three-level block measurement has consistent, nonconstant two-time statistics. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation

open scoped BigOperators ComplexOrder Kronecker _root_.Matrix
open D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics
open D5.S3.Quantum.PureState.PureStateHandshake
open D5.S3.Quantum.FiniteDimensional (qubitZ qubit_weyl_star)
open D5.S3.Quantum.Foundation
open D5.S3.Quantum.RandomCircuits
open D5.S3.Quantum.Dynamics.PositivePauliClockOrder (sigma sigma_posDef mixedState)
open D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence (s2)

noncomputable section

/-- The dephasing Hamiltonian on system times bath. -/
def hamiltonian {d m : ℕ} (Hs : Fin d → Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ :=
  ∑ j, basisProjector j ⊗ₖ Hs j

/-- The time-independent joint propagator. -/
def propagator {d m : ℕ} (Hs : Fin d → Matrix (Fin m) (Fin m) ℂ) (t : ℝ) :
    Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ :=
  NormedSpace.exp ((-(t : ℂ) * Complex.I) • hamiltonian Hs)

/-- The rank-one projector onto a column of a unitary measurement matrix. -/
def measurementProjector {d : ℕ} (V : Matrix.unitaryGroup (Fin d) ℂ) (x : Fin d) :
    Matrix (Fin d) (Fin d) ℂ :=
  rankOneDensity (fun i => V.val i x)

/-- A sharp measurement acting trivially on the bath. -/
def luders {d m : ℕ} (V : Matrix.unitaryGroup (Fin d) ℂ) (x : Fin d)
    (X : Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ) :
    Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ :=
  (measurementProjector V x ⊗ₖ 1) * X * (measurementProjector V x ⊗ₖ 1)

/-- The literal one-time joint-system trace formula. -/
def prob1 {d m : ℕ} (Hs : Fin d → Matrix (Fin m) (Fin m) ℂ)
    (σ : Matrix (Fin m) (Fin m) ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (V : Matrix.unitaryGroup (Fin d) ℂ) (t₀ : ℝ) (y : Fin d) (t₁ : ℝ) : ℂ :=
  Matrix.trace (luders V y (unitaryEvolution (propagator Hs (t₁ - t₀)) (ρ ⊗ₖ σ)))

/-- The literal two-time joint-system trace formula. -/
def prob2 {d m : ℕ} (Hs : Fin d → Matrix (Fin m) (Fin m) ℂ)
    (σ : Matrix (Fin m) (Fin m) ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (V : Matrix.unitaryGroup (Fin d) ℂ) (t₀ : ℝ)
    (y : Fin d) (t₂ : ℝ) (x : Fin d) (t₁ : ℝ) : ℂ :=
  Matrix.trace (luders V y (unitaryEvolution (propagator Hs (t₂ - t₁))
    (luders V x (unitaryEvolution (propagator Hs (t₁ - t₀)) (ρ ⊗ₖ σ)))))

/-- All consistency conditions through two measurements, including normalization. -/
def twoClassical {d m : ℕ} (Hs : Fin d → Matrix (Fin m) (Fin m) ℂ)
    (σ : Matrix (Fin m) (Fin m) ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (V : Matrix.unitaryGroup (Fin d) ℂ) (t₀ : ℝ) : Prop :=
  ∀ t₁ t₂ : ℝ, t₀ ≤ t₁ → t₁ ≤ t₂ →
    (∑ x, prob1 Hs σ ρ V t₀ x t₁) = 1 ∧
    (∀ y, (∑ x, prob2 Hs σ ρ V t₀ y t₂ x t₁) = prob1 Hs σ ρ V t₀ y t₂) ∧
    (∀ x, (∑ y, prob2 Hs σ ρ V t₀ y t₂ x t₁) = prob1 Hs σ ρ V t₀ x t₁)

/-- Two ordered time pairs give different statistics for the same outcomes. -/
def timeDependent {d m : ℕ} (Hs : Fin d → Matrix (Fin m) (Fin m) ℂ)
    (σ : Matrix (Fin m) (Fin m) ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (V : Matrix.unitaryGroup (Fin d) ℂ) (t₀ : ℝ) : Prop :=
  ∃ t₁ t₂ t₁' t₂' : ℝ, t₀ ≤ t₁ ∧ t₁ ≤ t₂ ∧ t₀ ≤ t₁' ∧ t₁' ≤ t₂' ∧
    ∃ x y, prob2 Hs σ ρ V t₀ y t₂ x t₁ ≠ prob2 Hs σ ρ V t₀ y t₂' x t₁'

/-- The measurement and dephasing PVMs fail to commute. -/
def notFullyCompatible {d : ℕ} (V : Matrix.unitaryGroup (Fin d) ℂ) : Prop :=
  ∃ x j, measurementProjector V x * basisProjector j ≠
    basisProjector j * measurementProjector V x

/-- Necessity of an unbiased measurement for genuinely time-dependent two-classical dephasing. -/
def claim : Prop :=
  ∀ (d m : ℕ) (Hs : Fin d → Matrix (Fin m) (Fin m) ℂ)
    (σ : Matrix (Fin m) (Fin m) ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (V : Matrix.unitaryGroup (Fin d) ℂ) (t₀ : ℝ),
    (∀ j, (Hs j).IsHermitian) → σ.PosSemidef → Matrix.trace σ = 1 →
    ρ.PosSemidef → Matrix.trace ρ = 1 →
    (∀ i j, i ≠ j → ρ i j = 0) → ρ ≠ (1 / (d : ℂ)) • 1 →
    notFullyCompatible V → twoClassical Hs σ ρ V t₀ → timeDependent Hs σ ρ V t₀ →
    ∀ j x, Complex.normSq (V.val j x) = 1 / (d : ℝ)

private def blocks : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ := ![0, qubitZ, (2 : ℂ) • qubitZ]
private def measurementRaw : Matrix (Fin 3) (Fin 3) ℂ :=
  !![s2, s2, 0; s2, -s2, 0; 0, 0, 1]

private theorem measurementRaw_eq_hadamard :
    measurementRaw = HaarTwoCopyTwirl.Hadamard.hadamard (0 : Fin 3) 1 s2 := by
  rw [measurementRaw.eq_1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [HaarTwoCopyTwirl.Hadamard.hadamard,
      Matrix.single_apply, Matrix.one_apply] <;> ring

private theorem amplitude_star : star s2 = s2 := by
  unfold s2
  simp

private theorem amplitude_sq : s2 ^ 2 = (1 / 2 : ℂ) := by
  have h := D5.S3.Observer.Existence.EmpiricalReflexiveSeparation.complex_sqrt_two_sq
  unfold s2
  rw [Complex.ofReal_div, Complex.ofReal_ofNat, div_pow, h]
  norm_num

private theorem measurement_unitary : measurementRaw ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  rw [measurementRaw_eq_hadamard]
  apply HaarTwoCopyTwirl.Hadamard.hadamard_unitary (0 : Fin 3) 1 (by decide) s2 amplitude_star
  linear_combination 2 * amplitude_sq

private def measurement : Matrix.unitaryGroup (Fin 3) ℂ :=
  ⟨measurementRaw, measurement_unitary⟩

private def projectors (x : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  ![!![1/2, 1/2, 0; 1/2, 1/2, 0; 0, 0, 0],
    !![1/2, -1/2, 0; -1/2, 1/2, 0; 0, 0, 0],
    !![0, 0, 0; 0, 0, 0; 0, 0, 1]] x

private theorem projector_formula (x : Fin 3) :
    measurementProjector measurement x = projectors x := by
  unfold measurementProjector rankOneDensity
  ext i j
  change measurementRaw i x * star (measurementRaw j x) = projectors x i j
  unfold measurementRaw projectors
  fin_cases x <;> fin_cases i <;> fin_cases j <;>
    norm_num [amplitude_star, star_neg] <;>
    linear_combination amplitude_sq

private theorem states_valid :
    sigma.PosSemidef ∧ Matrix.trace sigma = 1 ∧
    FuchsLogarithmBasisRefutation.rho0.PosSemidef ∧
    Matrix.trace FuchsLogarithmBasisRefutation.rho0 = 1 ∧
    (∀ i j, i ≠ j → FuchsLogarithmBasisRefutation.rho0 i j = 0) ∧
    FuchsLogarithmBasisRefutation.rho0 ≠ (1 / (3 : ℂ)) • 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sigma_posDef.posSemidef
  · exact mixedState.property.2
  · exact FuchsLogarithmBasisRefutation.rho0_posDef.posSemidef
  · exact FuchsLogarithmBasisRefutation.rho0_trace
  · intro i j hij
    exact Matrix.diagonal_apply_ne _ hij
  · intro h
    have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 0 0) h
    unfold FuchsLogarithmBasisRefutation.rho0 at hh
    norm_num at hh

private theorem blocks_hermitian : ∀ j, (blocks j).IsHermitian := by
  have hz : qubitZ.IsHermitian := qubit_weyl_star.2.2.1
  intro j
  fin_cases j
  · exact Matrix.isHermitian_zero
  · exact hz
  · exact hz.smul (by change star (2 : ℂ) = 2; norm_num)

private def energies (k : Fin 3 × Fin 2) : ℂ := (k.1 : ℂ) * ![1, -1] k.2

private theorem hamiltonian_diagonal : hamiltonian blocks = Matrix.diagonal energies := by
  ext ⟨i, b⟩ ⟨j, c⟩
  unfold hamiltonian basisProjector blocks energies
  fin_cases i <;> fin_cases b <;> fin_cases j <;> fin_cases c <;>
    norm_num [qubitZ, Fin.sum_univ_succ, Matrix.sum_apply,
      Matrix.kronecker_apply, Matrix.single_apply, Matrix.diagonal_apply]

private theorem propagator_diagonal (t : ℝ) :
    propagator blocks t =
      Matrix.diagonal (fun k => Complex.exp (-(t : ℂ) * Complex.I * energies k)) := by
  unfold propagator
  rw [hamiltonian_diagonal, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  congr 1
  ext k
  simp only [Pi.coe_exp, Pi.smul_apply, smul_eq_mul, ← Complex.exp_eq_exp_ℂ]

private theorem evolution_entries (t : ℝ)
    (X : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) (i j : Fin 3 × Fin 2) :
    unitaryEvolution (propagator blocks t) X i j =
      Complex.exp (-(t : ℂ) * Complex.I * (energies i - energies j)) * X i j := by
  have hj : star (energies j) = energies j := by
    rcases j with ⟨j, b⟩
    unfold energies
    fin_cases j <;> fin_cases b <;> norm_num
  unfold unitaryEvolution
  rw [propagator_diagonal, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Pi.star_apply]
  have hc : star (Complex.exp (-(t : ℂ) * Complex.I * energies j)) =
      Complex.exp ((t : ℂ) * Complex.I * energies j) := by
    change (starRingEnd ℂ) (Complex.exp (-(t : ℂ) * Complex.I * energies j)) = _
    rw [← Complex.exp_conj]
    congr 1
    have hj' : (starRingEnd ℂ) (energies j) = energies j := hj
    simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I, hj']
    ring
  rw [hc]
  calc
    _ = (Complex.exp (-(t : ℂ) * Complex.I * energies i) *
        Complex.exp ((t : ℂ) * Complex.I * energies j)) * X i j := by ring
    _ = _ := by
      rw [← Complex.exp_add]
      congr 2
      ring

private theorem initial_stationary (t : ℝ) :
    unitaryEvolution (propagator blocks t) (FuchsLogarithmBasisRefutation.rho0 ⊗ₖ sigma) =
      FuchsLogarithmBasisRefutation.rho0 ⊗ₖ sigma := by
  ext ⟨i, b⟩ ⟨j, c⟩
  rw [evolution_entries]
  unfold FuchsLogarithmBasisRefutation.rho0 sigma
  fin_cases i <;> fin_cases b <;> fin_cases j <;> fin_cases c <;>
    norm_num [Matrix.kronecker_apply, Matrix.diagonal_apply]

private theorem post_measurement (x : Fin 3) :
    luders measurement x (FuchsLogarithmBasisRefutation.rho0 ⊗ₖ sigma) =
      ![(5/12 : ℂ), 5/12, 1/6] x • (projectors x ⊗ₖ sigma) := by
  unfold luders
  rw [projector_formula, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    one_mul, mul_one, ← Matrix.smul_kronecker]
  congr 1
  ext i j
  change (∑ k : Fin 3, (∑ l : Fin 3, projectors x i l * FuchsLogarithmBasisRefutation.rho0 l k) *
    projectors x k j) = ![(5/12 : ℂ), 5/12, 1/6] x * projectors x i j
  unfold projectors FuchsLogarithmBasisRefutation.rho0
  fin_cases x <;> fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_succ, Matrix.diagonal_apply]

private theorem one_time (t : ℝ) (y : Fin 3) :
    prob1 blocks sigma FuchsLogarithmBasisRefutation.rho0 measurement 0 y t =
      ![(5/12 : ℂ), 5/12, 1/6] y := by
  unfold prob1
  rw [initial_stationary, post_measurement, Matrix.trace_smul, Matrix.trace_kronecker]
  unfold Matrix.trace projectors sigma
  fin_cases y <;> norm_num [Fin.sum_univ_succ]

private def jointLaw (u : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  let a := 5 * (2 + Complex.exp (Complex.I * (u : ℂ)) +
    Complex.exp (-(Complex.I * (u : ℂ)))) / 48
  let b := 5 * (2 - Complex.exp (Complex.I * (u : ℂ)) -
    Complex.exp (-(Complex.I * (u : ℂ)))) / 48
  !![a, b, 0; b, a, 0; 0, 0, 1/6]

private theorem luders_trace (y : Fin 3)
    (X : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) :
    Matrix.trace (luders measurement y X) =
      Matrix.trace ((projectors y ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * X) := by
  have hv : star (fun i => measurement.val i y) ⬝ᵥ (fun i => measurement.val i y) = 1 := by
    have hh := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ => A y y)
      (Matrix.UnitaryGroup.star_mul_self measurement)
    unfold dotProduct
    simpa only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Pi.star_apply] using hh
  have hp := (pure_state_handshake (fun i => measurement.val i y) hv 0).1
  change measurementProjector measurement y * measurementProjector measurement y =
    measurementProjector measurement y at hp
  rw [projector_formula] at hp
  unfold luders
  rw [projector_formula, Matrix.trace_mul_cycle, ← Matrix.mul_kronecker_mul, hp, one_mul]

private theorem two_time (t₁ t₂ : ℝ) (x y : Fin 3) :
    prob2 blocks sigma FuchsLogarithmBasisRefutation.rho0 measurement 0 y t₂ x t₁ =
      jointLaw (t₂ - t₁) y x := by
  unfold prob2
  rw [initial_stationary, post_measurement, luders_trace]
  have he : unitaryEvolution (propagator blocks (t₂ - t₁))
      (![(5/12 : ℂ), 5/12, 1/6] x • (projectors x ⊗ₖ sigma)) =
      fun i j => Complex.exp (-((t₂ - t₁ : ℝ) : ℂ) * Complex.I * (energies i - energies j)) *
        (![(5/12 : ℂ), 5/12, 1/6] x • (projectors x ⊗ₖ sigma)) i j := by
    ext i j
    exact evolution_entries _ _ i j
  rw [he]
  change (∑ i : Fin 3 × Fin 2, ∑ j : Fin 3 × Fin 2,
    (projectors y i.1 j.1 * (1 : Matrix (Fin 2) (Fin 2) ℂ) i.2 j.2) *
      (Complex.exp (-((t₂ - t₁ : ℝ) : ℂ) * Complex.I * (energies j - energies i)) *
        (![(5/12 : ℂ), 5/12, 1/6] x * (projectors x j.1 i.1 * sigma j.2 i.2)))) = _
  unfold energies projectors sigma jointLaw
  fin_cases x <;> fin_cases y <;>
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, Matrix.kroneckerMap_apply,
      neg_mul, mul_comm ((t₂ - t₁ : ℝ) : ℂ) Complex.I] <;> ring

private theorem consistency :
    twoClassical blocks sigma FuchsLogarithmBasisRefutation.rho0 measurement 0 := by
  intro t₁ t₂ _ _
  refine ⟨?_, ?_, ?_⟩
  · simp only [one_time]
    norm_num [Fin.sum_univ_succ]
  · intro y
    simp only [two_time, one_time]
    unfold jointLaw
    fin_cases y <;> norm_num [Fin.sum_univ_succ] <;> ring
  · intro x
    simp only [two_time, one_time]
    unfold jointLaw
    fin_cases x <;> norm_num [Fin.sum_univ_succ] <;> ring

private theorem dependence :
    timeDependent blocks sigma FuchsLogarithmBasisRefutation.rho0 measurement 0 := by
  refine ⟨0, 0, 0, Real.pi, le_refl _, le_refl _, le_refl _, Real.pi_pos.le, 0, 0, ?_⟩
  rw [two_time, two_time]
  unfold jointLaw
  norm_num [Complex.exp_neg, mul_comm Complex.I (Real.pi : ℂ),
    Complex.exp_pi_mul_I]

private theorem incompatible : notFullyCompatible measurement := by
  refine ⟨0, 0, ?_⟩
  rw [projector_formula]
  intro h
  have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M 0 1) h
  unfold basisProjector projectors at hh
  norm_num [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_succ] at hh

private theorem biased : Complex.normSq (measurement.val 2 0) ≠ 1 / (3 : ℝ) := by
  unfold measurement measurementRaw
  norm_num

/-- The block measurement refutes the proposed necessity of mutual unbiasedness. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨hσ, htσ, hρ, htρ, hd, hn⟩ := states_valid
  exact biased (h 3 2 blocks sigma FuchsLogarithmBasisRefutation.rho0 measurement 0 blocks_hermitian
    hσ htσ hρ htρ hd hn incompatible consistency dependence 2 0)

end
end D5.S3.Quantum.Decoherence.DephasingTwoClassicalityBlockRefutation
