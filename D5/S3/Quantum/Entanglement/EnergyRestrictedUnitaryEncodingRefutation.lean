/- GID: D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.claim; result=D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.result; claim=D5/S3/Quantum/Entanglement/EnergyRestrictedUnitaryEncodingRefutation.claim
   digest: Four unitary encodings beat every unassisted strategy below half-unit energy. -/

import D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
import D5.S3.Quantum.Reduction.IsometricCompression

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Quantum.Entanglement.EnergyRestrictedUnitaryEncodingRefutation

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation (IsDensity)
open D5.S3.Quantum.Reduction.IsometricCompression (compress)

/-- A POVM on any finite carrier; on `Fin d` this is the existing POVM predicate. -/
def IsPOVM {n B : Type} [Fintype n] [DecidableEq n] [Fintype B]
    (M : B → Matrix n n ℂ) : Prop :=
  (∀ b, (M b).PosSemidef) ∧ ∑ b, M b = 1

/-- A shared unit vector, local unitary encodings, and joint POVMs. -/
def UnitaryStrategy {X Y B : Type} [Fintype B] {dA dB : ℕ}
    (Ψ : Fin dA × Fin dB → ℂ) (_U : X → unitaryGroup (Fin dA) ℂ)
    (M : Y → B → Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) : Prop :=
  (∑ i, Complex.normSq (Ψ i)) = 1 ∧ ∀ y, IsPOVM (M y)

/-- Alice acts on her factor and transmits it to Bob. -/
def encoded {X : Type} {dA dB : ℕ} (Ψ : Fin dA × Fin dB → ℂ)
    (U : X → unitaryGroup (Fin dA) ℂ) (x : X) : Fin dA × Fin dB → ℂ :=
  ((U x : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ)) *ᵥ Ψ

/-- The Born probability of an outcome of the joint measurement. -/
def unitaryProb {X Y B : Type} {dA dB : ℕ} (Ψ : Fin dA × Fin dB → ℂ)
    (U : X → unitaryGroup (Fin dA) ℂ)
    (M : Y → B → Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (b : B) (x : X) (y : Y) : ℝ :=
  (star (encoded Ψ U x) ⬝ᵥ (M y b *ᵥ encoded Ψ U x)).re

/-- The vacuum population of Alice's reduced message. -/
def unitaryVacuum {X : Type} {dA dB : ℕ} [NeZero dA]
    (Ψ : Fin dA × Fin dB → ℂ) (U : X → unitaryGroup (Fin dA) ℂ) (x : X) : ℝ :=
  ∑ j, ‖encoded Ψ U x (0, j)‖ ^ 2

/-- Finite shared randomness, density messages, and conditional POVMs. -/
def QCStrategy {X Y B L : Type} [Fintype B] [Fintype L] {d : ℕ}
    (q : L → ℝ) (ρ : L → X → Matrix (Fin d) (Fin d) ℂ)
    (M : L → Y → B → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ l, 0 ≤ q l) ∧ ∑ l, q l = 1 ∧ (∀ l x, IsDensity (ρ l x)) ∧
    ∀ l y, D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM (M l y)

/-- Shared randomness averages the conditional Born probabilities. -/
def qcProb {X Y B L : Type} [Fintype L] {d : ℕ}
    (q : L → ℝ) (ρ : L → X → Matrix (Fin d) (Fin d) ℂ)
    (M : L → Y → B → Matrix (Fin d) (Fin d) ℂ) (b : B) (x : X) (y : Y) : ℝ :=
  ∑ l, q l * (trace (ρ l x * M l y b)).re

/-- The energy constraint averages vacuum populations over shared randomness. -/
def qcVacuum {X L : Type} [Fintype L] {d : ℕ} [NeZero d]
    (q : L → ℝ) (ρ : L → X → Matrix (Fin d) (Fin d) ℂ) (x : X) : ℝ :=
  ∑ l, q l * (ρ l x 0 0).re

/-- An arbitrary finite linear communication task. -/
def taskValue {X Y B : Type} [Fintype X] [Fintype Y] [Fintype B]
    (c p : B → X → Y → ℝ) : ℝ := ∑ b, ∑ x, ∑ y, c b x y * p b x y

/-- Unitary entanglement assistance would be resourceless for every finite task. -/
def claim : Prop :=
  ∀ (X Y B : Type) [Fintype X] [Fintype Y] [Fintype B]
    (c : B → X → Y → ℝ) (ω : ℝ), 0 ≤ ω → ω < 1 / 2 →
    ∀ (dA dB : ℕ) [NeZero dA] (Ψ : Fin dA × Fin dB → ℂ)
      (U : X → unitaryGroup (Fin dA) ℂ)
      (M : Y → B → Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ),
      UnitaryStrategy Ψ U M → (∀ x, 1 - ω ≤ unitaryVacuum Ψ U x) →
      ∃ (d : ℕ) (_ : NeZero d) (L : Type) (_ : Fintype L)
        (q : L → ℝ) (ρ : L → X → Matrix (Fin d) (Fin d) ℂ)
        (N : L → Y → B → Matrix (Fin d) (Fin d) ℂ),
        QCStrategy q ρ N ∧ (∀ x, 1 - ω ≤ qcVacuum q ρ x) ∧
          taskValue c (unitaryProb Ψ U M) ≤ taskValue c (qcProb q ρ N)

private theorem involution_bound (A N : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian)
    (hAA : A * A = 1) (ht : trace A = 0)
    (hN : N.PosSemidef) (hNc : (1 - N).PosSemidef) :
    (trace (N * A)).re ≤ 1 := by
  let P := (1 / 2 : ℝ) • (1 + A)
  let Q := (1 / 2 : ℝ) • (1 - A)
  have hp : P * P = P := by
    dsimp [P]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one, hAA]
    module
  have hq : Q * Q = Q := by
    dsimp [Q]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, hAA]
    module
  have hph : P.IsHermitian := (isHermitian_one.add hA).smul (by simp [IsSelfAdjoint])
  have hqh : Q.IsHermitian := (isHermitian_one.sub hA).smul (by simp [IsSelfAdjoint])
  have hpp : P.PosSemidef := by
    simpa only [hph.eq, hp] using posSemidef_conjTranspose_mul_self P
  have hqp : Q.PosSemidef := by
    simpa only [hqh.eq, hq] using posSemidef_conjTranspose_mul_self Q
  have hnq := (Complex.nonneg_iff.mp (hN.trace_mul_nonneg hqp)).1
  have hnp := (Complex.nonneg_iff.mp (hNc.trace_mul_nonneg hpp)).1
  have hpt : trace P = 1 := by simp [P, Matrix.trace_smul, Matrix.trace_add, ht]
  have ha : A = P - Q := by dsimp [P, Q]; module
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, hpt] at hnp
  rw [ha, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
  simp only [Complex.sub_re, Complex.one_re] at hnp
  linarith

private theorem two_level_involution (s : ℝ) (c : ℂ) (hs : s ^ 2 + Complex.normSq c = 1) :
    let A : Matrix (Fin 2) (Fin 2) ℂ := !![-(s : ℂ), c; star c, s]
    A.IsHermitian ∧ A * A = 1 ∧ trace A = 0 := by
  dsimp
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    all_goals apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply] at hs ⊢ <;> nlinarith [hs]
  · simp [Matrix.trace, Fin.sum_univ_two]

private theorem two_level_bound (N : Matrix (Fin 2) (Fin 2) ℂ)
    (hN : N.PosSemidef) (hNc : (1 - N).PosSemidef)
    (s : ℝ) (c : ℂ) (hs0 : 0 ≤ s) (hs : s ^ 2 + Complex.normSq c = 1) :
    (star (![c, (s : ℂ)] : Fin 2 → ℂ) ⬝ᵥ (N *ᵥ ![c, (s : ℂ)])).re - (N 0 0).re ≤ s := by
  let A : Matrix (Fin 2) (Fin 2) ℂ := !![-(s : ℂ), c; star c, s]
  obtain ⟨hA, hAA, ht⟩ := two_level_involution s c hs
  have hb := involution_bound A N hA hAA ht hN hNc
  have heq : (star (![c, (s : ℂ)] : Fin 2 → ℂ) ⬝ᵥ (N *ᵥ ![c, (s : ℂ)])).re - (N 0 0).re =
      s * (trace (N * A)).re := by
    simp [A, dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im, Complex.normSq_apply] at hs ⊢
    linear_combination hs * (N 0 0).re
  rw [heq]
  nlinarith

end D5.S3.Quantum.Entanglement.EnergyRestrictedUnitaryEncodingRefutation
