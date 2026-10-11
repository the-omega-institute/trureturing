/- GID: D5/S3/Quantum/Measurement/QubitIncompatibilityRigidity
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/QubitIncompatibilityRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Restricted-state compatibility determines incompatible unbiased qubit pairs. -/

import D5.S3.Quantum.FiniteDimensional
import D5.S3.Quantum.Measurement.FourQubitParentConstruction
noncomputable section
open D5.S3.Quantum.FiniteDimensional
open scoped ComplexOrder
namespace D5.S3.Quantum.ToriiTakakuraImamuraRigidity
abbrev V := EuclideanSpace ℝ (Fin 3)
abbrev Density := {ρ : QubitMatrix // ρ.PosSemidef ∧ Matrix.trace ρ = 1}
def pauliY : QubitMatrix := !![0, -Complex.I; Complex.I, 0]
def pauli (v : V) : QubitMatrix := (v 0 : ℂ) • qubitX + (v 1 : ℂ) • pauliY + (v 2 : ℂ) • qubitZ
def effect (v : V) (s : Fin 2) : QubitMatrix :=
  (1 / 2 : ℂ) • ((1 : QubitMatrix) + (if s = 0 then (1 : ℂ) else -1) • pauli v)
def IsPOVM (G : Fin 2 × Fin 2 → QubitMatrix) : Prop :=
  (∀ q, (G q).PosSemidef) ∧ (∑ s : Fin 2, ∑ t : Fin 2, G (s, t)) = 1
def marginal (G : Fin 2 × Fin 2 → QubitMatrix) (i s : Fin 2) : QubitMatrix :=
  if i = 0 then ∑ t : Fin 2, G (s, t) else ∑ t : Fin 2, G (t, s)
def SCompatible (S : Set Density) (a : Fin 2 → V) : Prop :=
  ∃ G : Fin 2 × Fin 2 → QubitMatrix, IsPOVM G ∧ ∀ ρ ∈ S, ∀ i s : Fin 2,
    bornProbability ρ.1 (marginal G i s) = bornProbability ρ.1 (effect (a i) s)
def Incompatible (a : Fin 2 → V) : Prop := ¬ SCompatible Set.univ a
def SignedPermutation (a b : Fin 2 → V) : Prop :=
  ∃ (π : Equiv.Perm (Fin 2)) (ε : Fin 2 → ℝ),
    (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∀ i, b i = ε i • a (π i)
def claim : Prop :=
  ∀ a b : Fin 2 → V,
    (∀ i, ‖a i‖ ≤ 1) →
    (∀ i, ‖b i‖ ≤ 1) →
    Incompatible a →
    Incompatible b →
    ((∀ S : Set Density, SCompatible S a ↔ SCompatible S b) ↔
      SignedPermutation a b)


open scoped InnerProductSpace
private abbrev B (t : ℝ) (v : V) : QubitMatrix :=
  (1 / 2 : ℂ) • D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB t v

private lemma pauli_eq (v : V) :
    pauli v = D5.S3.Quantum.Measurement.FourQubitParentConstruction.B v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli, pauliY, qubitX, qubitZ,
      D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_formula] <;> ring

private lemma B_formula (t : ℝ) (v : V) :
    B t v = D5.S3.Quantum.Information.ActualPureQubitCostInfimum.blochMatrix t v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B, D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB,
      D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_formula,
      D5.S3.Quantum.Information.ActualPureQubitCostInfimum.blochMatrix] <;> ring

open D5.S3.Quantum.Measurement.FourQubitParentConstruction
  (scalarB_hermitian scalarB_det half_scalarB_posSemidef_iff
    hermitian_decomposition half_scalarB_double trace_B_mul)
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum (bloch blochMatrix)

private lemma B_hermitian (t : ℝ) (v : V) : (B t v).IsHermitian :=
  (scalarB_hermitian t v).smul (by simp [IsSelfAdjoint])

private lemma B_trace (t : ℝ) (v : V) : Matrix.trace (B t v) = (t : ℂ) := by
  rw [B_formula]
  simp [blochMatrix, Matrix.trace, Fin.sum_univ_two]
  ring

private lemma B_det (t : ℝ) (v : V) :
    Matrix.det (B t v) = ((t ^ 2 - ‖v‖ ^ 2) / 4 : ℝ) := by
  simp [B, scalarB_det, Complex.ofReal_div]
  ring

private lemma B_psd (t : ℝ) (v : V) : (B t v).PosSemidef ↔ ‖v‖ ≤ t :=
  half_scalarB_posSemidef_iff t v

private lemma B_rep (M : QubitMatrix) (h : M.IsHermitian) :
    M = B (Matrix.trace M).re (bloch M) := by
  have he := hermitian_decomposition M h
  rw [← half_scalarB_double] at he
  simpa [B, mul_div_cancel₀] using he

private lemma B_born (s t : ℝ) (w v : V) :
    bornProbability (B s w) (B t v) = ((s * t + ⟪w, v⟫_ℝ) / 2 : ℝ) := by
  simp only [B, bornProbability,
    D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, add_mul, mul_add,
    Matrix.trace_add, Matrix.one_mul, Matrix.mul_one, trace_B_mul]
  simp [D5.S3.Quantum.Measurement.FourQubitParentConstruction.B_formula,
    Matrix.trace, Fin.sum_univ_two]
  ring

private lemma effect_B (v : V) (s : Fin 2) :
    effect v s = B 1 ((if s = 0 then (1 : ℝ) else -1) • v) := by
  rw [effect, pauli_eq]
  fin_cases s <;> simp [B, D5.S3.Quantum.Measurement.FourQubitParentConstruction.scalarB]

private def state (r : V) (h : ‖r‖ ≤ 1) : Density :=
  ⟨B 1 r, (B_psd 1 r).mpr h, B_trace 1 r⟩

private lemma tomography (M N : QubitMatrix) (hM : M.IsHermitian)
    (hN : N.IsHermitian)
    (h : ∀ ρ : Density, bornProbability ρ.1 M = bornProbability ρ.1 N) : M = N := by
  have h0 := h (state 0 (by simp))
  dsimp only [state] at h0
  rw [B_rep M hM, B_rep N hN, B_born, B_born] at h0
  have ht : (Matrix.trace M).re = (Matrix.trace N).re := by
    have hr := congrArg Complex.re h0
    simp only [Complex.ofReal_re, inner_zero_left, add_zero, one_mul] at hr
    linarith
  have hv : bloch M = bloch N := by
    ext i
    have he := h (state (EuclideanSpace.single i 1) (by simp))
    dsimp only [state] at he
    rw [B_rep M hM, B_rep N hN, B_born, B_born] at he
    have he' := congrArg Complex.re he
    simp [ht, PiLp.inner_apply] at he'
    linarith
  rw [B_rep M hM, B_rep N hN, ht, hv]

end D5.S3.Quantum.ToriiTakakuraImamuraRigidity
