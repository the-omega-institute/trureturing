/- GID: D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.claim; result=D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.result; claim=D5/S3/Quantum/SpinChains/ComplexHoppingCoherenceDampingRefutation.claim
   digest: Complex hopping can increase parity-twisted ground-state coherences. -/

import D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreCompression
import D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction
import D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
import D5.S3.Quantum.QuantumChannels.ButterflyLambdaTwoRelativeDesignRefutation
import D5.S3.Weil.ZetaLinear.Sylvester

/-! Complex hopping and parity insertion in occupation-basis partial traces. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option linter.style.longLine false

open scoped BigOperators Matrix ComplexOrder
open Matrix
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner
  (fullC prefixCount)
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.HardCoreCompression (fullC_entry)

namespace D5.S3.Quantum.SpinChains.ComplexHoppingCoherenceDampingRefutation

noncomputable section

/-- Occupation configurations of ordered fermionic modes. -/
abbrev Fock (N : ℕ) :=
  D5.S3.Quantum.QuantumChannels.ButterflyLambdaTwoRelativeDesignRefutation.Mode N

abbrev Operator (N : ℕ) :=
  D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.Operator N

/-- Jordan–Wigner annihilation, in the occupation basis. -/
def annihilator {N : ℕ} (j : Fin N) : Operator N :=
  (fullC j).submatrix (fun s i => finTwoEquiv (s i)) (fun s i => finTwoEquiv (s i))

/-- The number-conserving quadratic Hamiltonian. -/
def hamiltonian {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) : Operator N :=
  ∑ j, ∑ k, h j k • ((annihilator j)ᴴ * annihilator k)

abbrev Normalized {N : ℕ} (ψ : Fock N → ℂ) : Prop :=
  D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction.unitVector ψ

abbrev energy {N : ℕ} (H : Operator N) (ψ : Fock N → ℂ) : ℝ := RHLinalg.hermForm H ψ

/-- Variational minimality over all normalized Fock vectors, without a filling restriction. -/
def IsGroundState {N : ℕ} (H : Operator N) (ψ : Fock N → ℂ) : Prop :=
  Normalized ψ ∧ ∀ φ, Normalized φ → energy H ψ ≤ energy H φ

/-- The complement of three adjacent blocks may lie on both sides. -/
structure AdjacentPartition (N : ℕ) where
  left : ℕ
  a : ℕ
  b : ℕ
  d : ℕ
  right : ℕ
  size : N = left + (a + (b + (d + right)))

def concatenate {N : ℕ} (p : AdjacentPartition N)
    (l : Fock p.left) (a : Fock p.a) (b : Fock p.b)
    (d : Fock p.d) (r : Fock p.right) : Fock N :=
  fun i => Fin.append l (Fin.append a (Fin.append b (Fin.append d r)))
    (Fin.cast p.size i)

/-- Trace over the entire complement E in the occupation basis. -/
def reducedState {R : Type*} [Semiring R] [Star R]
    {N : ℕ} (p : AdjacentPartition N) (ψ : Fock N → R) :
    Matrix (Fock p.a × Fock p.b × Fock p.d) (Fock p.a × Fock p.b × Fock p.d) R :=
  let v : ((Fock p.a × Fock p.b × Fock p.d) × Fock p.left) × Fock p.right → R :=
    fun x => ψ (concatenate p x.1.2 x.1.1.1 x.1.1.2.1 x.1.1.2.2 x.2)
  Matrix.traceRight (Matrix.traceRight (Matrix.vecMulVec v (star v)))

abbrev occupation {N : ℕ} (s : Fock N) : ℕ :=
  D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant.occupationCount
    (fun i => finTwoEquiv (s i))

/-- Ordinary spin partial trace over B. -/
def spinTrace {R : Type*} [Semiring R] [Star R]
    {N : ℕ} (p : AdjacentPartition N) (ψ : Fock N → R) :
    Matrix (Fock p.a × Fock p.d) (Fock p.a × Fock p.d) R :=
  Matrix.traceRight ((reducedState p ψ).submatrix
    (fun x : (Fock p.a × Fock p.d) × Fock p.b => (x.1.1, x.2, x.1.2))
    (fun y : (Fock p.a × Fock p.d) × Fock p.b => (y.1.1, y.2, y.1.2)))

/-- The occupation-basis matrix of tr_B[(-1)^N_B ρ_ABD]. -/
def twistedTrace {R : Type*} [Ring R] [Star R]
    {N : ℕ} (p : AdjacentPartition N) (ψ : Fock N → R) :
    Matrix (Fock p.a × Fock p.d) (Fock p.a × Fock p.d) R :=
  Matrix.traceRight (fun x y : (Fock p.a × Fock p.d) × Fock p.b =>
    (-1 : R) ^ occupation x.2 *
      reducedState p ψ (x.1.1, x.2, x.1.2) (y.1.1, y.2, y.1.2))

def claim : Prop :=
  ∀ (N : ℕ) (h : Matrix (Fin N) (Fin N) ℂ), h.IsHermitian →
    ∀ ψ, IsGroundState (hamiltonian h) ψ → ∀ (p : AdjacentPartition N)
      (x y : Fock p.a × Fock p.d),
      occupation x.2 % 2 ≠ occupation y.2 % 2 →
      ‖twistedTrace p ψ x y‖ ≤ ‖spinTrace p ψ x y‖

private def hoppingG : Matrix (Fin 4) (Fin 4) GaussianInt :=
  !![14, -9 + 16 * (Zsqrtd.sqrtd : GaussianInt), -48, -12 - 12 * (Zsqrtd.sqrtd : GaussianInt);
    -9 - 16 * (Zsqrtd.sqrtd : GaussianInt), 14, -12 + 12 * (Zsqrtd.sqrtd : GaussianInt), -48;
    -48, -12 - 12 * (Zsqrtd.sqrtd : GaussianInt), -14, -16 + 9 * (Zsqrtd.sqrtd : GaussianInt);
    -12 + 12 * (Zsqrtd.sqrtd : GaussianInt), -48, -16 - 9 * (Zsqrtd.sqrtd : GaussianInt), -14]

private def hopping : Matrix (Fin 4) (Fin 4) ℂ :=
  (1 / 50 : ℂ) • hoppingG.map GaussianInt.toComplex

private def eigenmodesG : Matrix (Fin 4) (Fin 4) GaussianInt :=
  !![3, 3, 4, 4; 3, -3, 4, -4;
    4, -4 * (Zsqrtd.sqrtd : GaussianInt), -3, 3 * (Zsqrtd.sqrtd : GaussianInt);
    4, 4 * (Zsqrtd.sqrtd : GaussianInt), -3, -3 * (Zsqrtd.sqrtd : GaussianInt)]

/-- Twice the single-particle energies. -/
private def eigenvaluesG : Fin 4 → GaussianInt := ![-3, -1, 1, 3]

private def annihilatorG (j : Fin 4) : Matrix (Fock 4) (Fock 4) GaussianInt :=
  fun s t =>
    if finTwoEquiv (t j) = true ∧
        (fun i => finTwoEquiv (s i)) = Function.update (fun i => finTwoEquiv (t i)) j false
    then (-1) ^ prefixCount (fun i => finTwoEquiv (t i)) j else 0

private def liftG (h : Matrix (Fin 4) (Fin 4) GaussianInt) :
    Matrix (Fock 4) (Fock 4) GaussianInt :=
  ∑ j, ∑ k, h j k • ((annihilatorG j)ᴴ * annihilatorG k)

private def modeG (k : Fin 4) : Matrix (Fock 4) (Fock 4) GaussianInt :=
  ∑ j, eigenmodesG k j • annihilatorG j

private def gramFactorG (k : Fin 4) : Matrix (Fock 4) (Fock 4) GaussianInt :=
  if k.val < 2 then (modeG k)ᴴ else modeG k

private def weightsG : Fin 4 → GaussianInt := ![3, 1, 1, 3]

private def orbitalAG : Matrix (Fock 4) (Fock 4) GaussianInt :=
  3 • annihilatorG 0 + 4 • annihilatorG 2

private def orbitalBG : Matrix (Fock 4) (Fock 4) GaussianInt :=
  3 • annihilatorG 1 + 4 • annihilatorG 3

/-- The two-particle Slater vector before division by 25. -/
private def psiG : Fock 4 → GaussianInt := orbitalAGᴴ *ᵥ (orbitalBGᴴ *ᵥ Pi.single 0 1)

private def psi : Fock 4 → ℂ := fun s => (1/25 : ℂ) * GaussianInt.toComplex (psiG s)

private theorem diagonalizationG :
    (2 : GaussianInt) • hoppingG =
      eigenmodesGᴴ * Matrix.diagonal eigenvaluesG * eigenmodesG := by
  decide +kernel

private theorem lifted_diagonalizationG :
    (2 : GaussianInt) • liftG hoppingG =
      ∑ k, eigenvaluesG k • ((modeG k)ᴴ * modeG k) := by
  calc
    _ = liftG ((2 : GaussianInt) • hoppingG) := by
      simp only [liftG, Matrix.smul_apply, smul_smul, Finset.smul_sum, smul_eq_mul]
    _ = liftG (eigenmodesGᴴ * Matrix.diagonal eigenvaluesG * eigenmodesG) :=
      congrArg liftG diagonalizationG
    _ = _ := by decide +kernel

private theorem ground_certificateG :
    (2 : GaussianInt) • liftG hoppingG + (200 : GaussianInt) • 1 =
      ∑ k, weightsG k • ((gramFactorG k)ᴴ * gramFactorG k) := by
  rw [lifted_diagonalizationG]
  decide +kernel

private theorem slater_coordinatesG :
    psiG = fun s =>
      if s = ![1, 1, 0, 0] then 9 else
      if s = ![1, 0, 0, 1] then 12 else
      if s = ![0, 1, 1, 0] then -12 else
      if s = ![0, 0, 1, 1] then 16 else 0 := by
  rw [psiG, funext (Pi.single_apply (0 : Fock 4) (1 : GaussianInt))]
  decide +kernel

private theorem psi_normG : star psiG ⬝ᵥ psiG = (625 : GaussianInt) := by
  rw [slater_coordinatesG]
  decide +kernel

private theorem ground_kernelG : ∀ k : Fin 4, gramFactorG k *ᵥ psiG = 0 := by
  rw [slater_coordinatesG]
  decide +kernel

private theorem hamiltonian_cast :
    hamiltonian hopping = (1/50 : ℂ) • GaussianInt.toComplex.mapMatrix (liftG hoppingG) := by
  have hann (j : Fin 4) : (annihilatorG j).map GaussianInt.toComplex = annihilator j := by
    ext s t
    simp only [annihilatorG, Matrix.map_apply, annihilator, Matrix.submatrix_apply,
      fullC_entry]
    split_ifs <;> simp
  unfold hamiltonian hopping liftG
  simp only [map_sum, RingHom.mapMatrix_apply,
    Matrix.map_smul' _ _ _ GaussianInt.toComplex.map_mul, Matrix.map_mul,
    Matrix.conjTranspose_map GaussianInt.toComplex GaussianInt.toComplex_star, hann,
    Finset.smul_sum, Matrix.smul_apply, Matrix.map_apply, smul_smul, smul_eq_mul]

private def gramFactor (k : Fin 4) : Operator 4 := GaussianInt.toComplex.mapMatrix (gramFactorG k)

private theorem ground_certificate :
    hamiltonian hopping + (2 : ℂ) • 1 =
      (1/100 : ℂ) • ∑ k, GaussianInt.toComplex (weightsG k) •
        ((gramFactor k)ᴴ * gramFactor k) := by
  have h := congrArg GaussianInt.toComplex.mapMatrix ground_certificateG
  simp only [map_add, map_sum, RingHom.mapMatrix_apply,
    Matrix.map_one _ GaussianInt.toComplex.map_zero GaussianInt.toComplex.map_one,
    Matrix.map_smul' _ _ _ GaussianInt.toComplex.map_mul, Matrix.map_mul,
    Matrix.conjTranspose_map GaussianInt.toComplex GaussianInt.toComplex_star] at h
  rw [hamiltonian_cast]
  calc
    _ = (1/100 : ℂ) • ((2 : ℂ) • GaussianInt.toComplex.mapMatrix (liftG hoppingG) +
        (200 : ℂ) • (1 : Operator 4)) := by module
    _ = _ := by
      norm_num only [map_ofNat] at h
      exact congrArg ((1/100 : ℂ) • ·) h

private theorem normalized_psi : Normalized psi := by
  have h := congrArg GaussianInt.toComplex psi_normG
  simp only [RingHom.map_dotProduct, Function.comp_def, Pi.star_apply,
    GaussianInt.toComplex_star, map_ofNat] at h
  change star (fun s => GaussianInt.toComplex (psiG s)) ⬝ᵥ
    (fun s => GaussianInt.toComplex (psiG s)) = 625 at h
  change star (fun s => (1/25 : ℂ) • GaussianInt.toComplex (psiG s)) ⬝ᵥ
    (fun s => (1/25 : ℂ) • GaussianInt.toComplex (psiG s)) = 1
  simp only [← Pi.smul_def, star_smul, smul_dotProduct, dotProduct_smul]
  rw [h]
  norm_num

private theorem ground_kernel (k : Fin 4) : gramFactor k *ᵥ psi = 0 := by
  have h := congrArg (fun v : Fock 4 → GaussianInt => GaussianInt.toComplex ∘ v)
    (ground_kernelG k)
  simp only [RingHom.map_mulVec, Function.comp_def, Pi.zero_apply, map_zero] at h
  change GaussianInt.toComplex.mapMatrix (gramFactorG k) *ᵥ
    (fun s => GaussianInt.toComplex (psiG s)) = (0 : Fock 4 → ℂ) at h
  change gramFactor k *ᵥ ((1/25 : ℂ) • (GaussianInt.toComplex ∘ psiG)) = 0
  rw [Matrix.mulVec_smul]
  change (1/25 : ℂ) • (GaussianInt.toComplex.mapMatrix (gramFactorG k) *ᵥ
    (fun s => GaussianInt.toComplex (psiG s))) = 0
  rw [h, smul_zero]

private theorem psi_ground : IsGroundState (hamiltonian hopping) psi := by
  have hp : (hamiltonian hopping + (2 : ℂ) • 1).PosSemidef := by
    rw [ground_certificate]
    apply Matrix.PosSemidef.smul
    · apply Matrix.posSemidef_sum
      intro k _
      apply Matrix.PosSemidef.smul (Matrix.posSemidef_conjTranspose_mul_self _)
      fin_cases k <;> norm_num [weightsG, Complex.le_def, GaussianInt.toComplex_def]
    · norm_num [Complex.le_def]
  have hk : (hamiltonian hopping + (2 : ℂ) • 1) *ᵥ psi = 0 := by
    rw [ground_certificate, Matrix.smul_mulVec, Matrix.sum_mulVec]
    simp only [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, ground_kernel,
      Matrix.mulVec_zero, smul_zero, Finset.sum_const_zero]
  have he : hamiltonian hopping *ᵥ psi = (-2 : ℂ) • psi := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hk
    simpa only [neg_smul] using eq_neg_of_add_eq_zero_left hk
  refine ⟨normalized_psi, ?_⟩
  intro φ hφ
  have hl := hp.re_dotProduct_nonneg φ
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_add, dotProduct_smul, hφ] at hl
  have hψ : energy (hamiltonian hopping) psi = -2 := by
    unfold energy RHLinalg.hermForm
    rw [he, dotProduct_smul, normalized_psi]
    norm_num
  rw [hψ]
  change -2 ≤ (star φ ⬝ᵥ (hamiltonian hopping *ᵥ φ)).re
  change 0 ≤ (star φ ⬝ᵥ (hamiltonian hopping *ᵥ φ) + (2 : ℂ) * 1).re at hl
  norm_num only [mul_one, Complex.add_re, Complex.re_ofNat] at hl
  linarith

private def partition : AdjacentPartition 4 := ⟨0, 1, 1, 1, 1, rfl⟩

private def witnessX : Fock 1 × Fock 1 := (fun _ => 0, fun _ => 1)
private def witnessY : Fock 1 × Fock 1 := (fun _ => 1, fun _ => 0)

private theorem trace_valuesG :
    spinTrace partition psiG witnessX witnessY = (84 : GaussianInt) ∧
    twistedTrace partition psiG witnessX witnessY = (300 : GaussianInt) := by
  rw [slater_coordinatesG]
  decide +kernel

private theorem trace_values :
    spinTrace partition psi witnessX witnessY = (84/625 : ℂ) ∧
    twistedTrace partition psi witnessX witnessY = (12/25 : ℂ) := by
  have hs : spinTrace partition psi witnessX witnessY =
      (1/625 : ℂ) * GaussianInt.toComplex
        (spinTrace partition psiG witnessX witnessY) := by
    change (∑ b, ∑ l, ∑ r,
      psi (concatenate partition l witnessX.1 b witnessX.2 r) *
        star (psi (concatenate partition l witnessY.1 b witnessY.2 r))) =
      (1/625 : ℂ) * GaussianInt.toComplex (∑ b, ∑ l, ∑ r,
        psiG (concatenate partition l witnessX.1 b witnessX.2 r) *
          star (psiG (concatenate partition l witnessY.1 b witnessY.2 r)))
    simp only [psi, map_sum, map_mul, GaussianInt.toComplex_star, star_mul,
      star_div₀, star_one, star_ofNat, Complex.star_def]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro r _
    ring
  have ht : twistedTrace partition psi witnessX witnessY =
      (1/625 : ℂ) * GaussianInt.toComplex
        (twistedTrace partition psiG witnessX witnessY) := by
    change (∑ b, (-1 : ℂ) ^ occupation b * (∑ l, ∑ r,
      psi (concatenate partition l witnessX.1 b witnessX.2 r) *
        star (psi (concatenate partition l witnessY.1 b witnessY.2 r)))) =
      (1/625 : ℂ) * GaussianInt.toComplex (∑ b, (-1 : GaussianInt) ^ occupation b *
        (∑ l, ∑ r, psiG (concatenate partition l witnessX.1 b witnessX.2 r) *
          star (psiG (concatenate partition l witnessY.1 b witnessY.2 r))))
    simp only [psi, map_sum, map_mul, map_pow, map_neg, map_one,
      GaussianInt.toComplex_star, star_mul, star_div₀, star_one, star_ofNat,
      Complex.star_def]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [trace_valuesG.1] at hs
  rw [trace_valuesG.2] at ht
  norm_num [map_ofNat] at hs ht
  exact ⟨hs, ht⟩

theorem result : ¬ claim := by
  intro h
  have hp : occupation witnessX.2 % 2 ≠ occupation witnessY.2 % 2 := by decide +kernel
  have hhG : hoppingG.IsHermitian := by decide +kernel
  have hv := h 4 hopping
    ((hhG.map GaussianInt.toComplex GaussianInt.toComplex_star).smul
      (by norm_num [IsSelfAdjoint] : IsSelfAdjoint (1/50 : ℂ)))
    psi psi_ground partition witnessX witnessY hp
  rw [trace_values.1, trace_values.2] at hv
  norm_num at hv

end

end D5.S3.Quantum.SpinChains.ComplexHoppingCoherenceDampingRefutation
