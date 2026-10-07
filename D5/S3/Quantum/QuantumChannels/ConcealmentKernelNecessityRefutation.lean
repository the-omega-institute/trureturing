/- GID: D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.claim; result=D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.result; claim=D5/S3/Quantum/QuantumChannels/ConcealmentKernelNecessityRefutation.claim
   digest: Dephasing and depolarization conceal all POVM pairs with unequal adjoint kernels. -/

import D5.S3.Quantum.QuantumChannels.PositiveFilterTransposeRefutation
import D5.S3.QuantumChannels.CumulantRenyiDataProcessingRefutation
import D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation (IsDensity)
open D5.S3.Quantum.Measurement.BasisMeasurementProjection (HermitianSpace)
open D5.S3.Quantum.FiniteDimensional (qubitX qubitZ)
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence (Pauli pauliMatrix)
open D5.S3.QuantumChannels.CumulantRenyiDataProcessingRefutation (dephase_apply pinching_kraus)
open D5.S3.QuantumChannels.ProjectionDiagnostics.StaticDynamicScalarSeparation (pinchingEnd)

namespace D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation

/-- A finite positive operator-valued measure. -/
def IsPOVM {d : ℕ} {Ω : Type} [Fintype Ω]
    (M : Ω → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ a, (M a).PosSemidef) ∧ ∑ a, M a = 1

/-- Two POVMs are compatible when they are marginals of a joint POVM. -/
def Compatible {d : ℕ} {Ω Λ : Type} [Fintype Ω] [Fintype Λ]
    (M : Ω → Matrix (Fin d) (Fin d) ℂ) (N : Λ → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  IsPOVM M ∧ IsPOVM N ∧
    ∃ J : Ω × Λ → Matrix (Fin d) (Fin d) ℂ,
      IsPOVM J ∧ (∀ a, ∑ b, J (a, b) = M a) ∧ (∀ b, ∑ a, J (a, b) = N b)

/-- Compatible measurements reproduce the original measurements on every channel output. -/
def Concealed {din dout : ℕ} {Ω Λ : Type} [Fintype Ω] [Fintype Λ]
    (E : MatrixMap (Fin din) (Fin dout) ℂ) (T : Set (Matrix (Fin din) (Fin din) ℂ))
    (M : Ω → Matrix (Fin dout) (Fin dout) ℂ)
    (N : Λ → Matrix (Fin dout) (Fin dout) ℂ) : Prop :=
  ∃ F : Ω → Matrix (Fin dout) (Fin dout) ℂ,
    ∃ G : Λ → Matrix (Fin dout) (Fin dout) ℂ,
      Compatible F G ∧
        (∀ ρ ∈ T, ∀ a, trace (F a * E ρ) = trace (M a * E ρ)) ∧
        (∀ ρ ∈ T, ∀ b, trace (G b * E ρ) = trace (N b * E ρ))

/-- A set of density matrices whose real span is the full Hermitian operator space. -/
def TomographicallyComplete {d : ℕ} (T : Set (Matrix (Fin d) (Fin d) ℂ)) : Prop :=
  (∀ ρ ∈ T, IsDensity ρ) ∧ Submodule.span ℝ T = HermitianSpace d

/-- The kernel of the Heisenberg adjoint, restricted to Hermitian operators. -/
def AdjointKernel {din dout : ℕ} (E : MatrixMap (Fin din) (Fin dout) ℂ) :
    Set (Matrix (Fin dout) (Fin dout) ℂ) :=
  {A | A.IsHermitian ∧ E.dual A = 0}

/-- Concealment equivalence for every finite pair of outcome sets would determine the kernel. -/
def claim : Prop :=
  ∀ (din dout : ℕ) (κ₁ κ₂ : Type) [Fintype κ₁] [Fintype κ₂]
    (K₁ : κ₁ → Matrix (Fin dout) (Fin din) ℂ)
    (K₂ : κ₂ → Matrix (Fin dout) (Fin din) ℂ),
    (∑ j, (K₁ j)ᴴ * K₁ j) = 1 → (∑ j, (K₂ j)ᴴ * K₂ j) = 1 →
    ∀ T : Set (Matrix (Fin din) (Fin din) ℂ), TomographicallyComplete T →
    (∀ (Ω Λ : Type) [Fintype Ω] [Fintype Λ]
      (M : Ω → Matrix (Fin dout) (Fin dout) ℂ)
      (N : Λ → Matrix (Fin dout) (Fin dout) ℂ),
      IsPOVM M → IsPOVM N →
      (Concealed (MatrixMap.of_kraus K₁ K₁) T M N ↔
        Concealed (MatrixMap.of_kraus K₂ K₂) T M N)) →
    AdjointKernel (MatrixMap.of_kraus K₁ K₁) = AdjointKernel (MatrixMap.of_kraus K₂ K₂)

/-- The trace dual of a Kraus map is its Heisenberg Kraus sum. -/
private theorem dual_kraus {din dout : ℕ} {κ : Type} [Fintype κ]
    (K : κ → Matrix (Fin dout) (Fin din) ℂ) (A : Matrix (Fin dout) (Fin dout) ℂ) :
    (MatrixMap.of_kraus K K).dual A = ∑ j, (K j)ᴴ * A * K j := by
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro X
  rw [← MatrixMap.Dual.trace_eq]
  simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (K j) (X * ((K j)ᴴ * A))

/-- All density matrices span the Hermitian operator space over the reals. -/
private theorem all_density_tomographically_complete (d : ℕ) :
    TomographicallyComplete {ρ : Matrix (Fin d) (Fin d) ℂ | IsDensity ρ} := by
  refine ⟨fun _ h => h, le_antisymm ?_ ?_⟩
  · apply Submodule.span_le.mpr
    intro A hA
    exact hA.1.isHermitian
  · let S := Submodule.span ℝ {ρ : Matrix (Fin d) (Fin d) ℂ | IsDensity ρ}
    have positive_mem (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosSemidef) : A ∈ S := by
      by_cases hz : trace A = 0
      · rw [hA.trace_eq_zero_iff.mp hz]
        exact S.zero_mem
      · let r := (trace A).re
        have hrreal : (r : ℂ) = trace A := by
          apply Complex.ext
          · rfl
          · exact (Complex.nonneg_iff.mp hA.trace_nonneg).2
        have hrne : r ≠ 0 := by
          intro hr
          apply hz
          rw [← hrreal, hr, Complex.ofReal_zero]
        have hr : 0 < r := lt_of_le_of_ne (Complex.nonneg_iff.mp hA.trace_nonneg).1
          (Ne.symm hrne)
        have hρ : IsDensity (r⁻¹ • A) := by
          refine ⟨hA.smul (inv_nonneg.mpr hr.le), ?_⟩
          rw [Matrix.trace_smul, ← hrreal, Complex.real_smul]
          simp [hrne]
        have hmem := S.smul_mem r (Submodule.subset_span hρ)
        simpa only [smul_smul, mul_inv_cancel₀ hrne, one_smul] using hmem
    intro A hA
    change IsSelfAdjoint A at hA
    rw [← CFC.posPart_sub_negPart A hA]
    exact S.sub_mem
      (positive_mem _ (Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg A)))
      (positive_mem _ (Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg A)))

/-- Nonnegative normalized real diagonal entries define a POVM. -/
private theorem diagonal_povm {d : ℕ} {Ω : Type} [Fintype Ω]
    (p : Ω → Fin d → ℝ) (hp : ∀ a i, 0 ≤ p a i) (hs : ∀ i, ∑ a, p a i = 1) :
    IsPOVM (fun a => diagonal (fun i => (p a i : ℂ))) := by
  refine ⟨fun a => Matrix.PosSemidef.diagonal
    (fun i => Complex.zero_le_real.mpr (hp a i)), ?_⟩
  ext i j
  by_cases hij : i = j
  · subst j
    simpa [Matrix.sum_apply] using congrArg Complex.ofReal (hs i)
  · simp [Matrix.sum_apply, Matrix.diagonal, hij]

/-- Products of diagonal probability weights give a joint POVM. -/
private theorem diagonal_compatible {d : ℕ} {Ω Λ : Type} [Fintype Ω] [Fintype Λ]
    (p : Ω → Fin d → ℝ) (q : Λ → Fin d → ℝ)
    (hp : ∀ a i, 0 ≤ p a i) (hq : ∀ b i, 0 ≤ q b i)
    (hps : ∀ i, ∑ a, p a i = 1) (hqs : ∀ i, ∑ b, q b i = 1) :
    Compatible (fun a => diagonal (fun i => (p a i : ℂ)))
      (fun b => diagonal (fun i => (q b i : ℂ))) := by
  refine ⟨diagonal_povm p hp hps, diagonal_povm q hq hqs,
    fun ab => diagonal (fun i => ((p ab.1 i * q ab.2 i : ℝ) : ℂ)), ?_, ?_, ?_⟩
  · apply diagonal_povm
    · intro ab i
      exact mul_nonneg (hp ab.1 i) (hq ab.2 i)
    · intro i
      simp only [Fintype.sum_prod_type, ← Finset.mul_sum, hqs, mul_one, hps]
  · intro a
    ext i j
    by_cases hij : i = j
    · subst j
      simpa only [Matrix.sum_apply, Matrix.diagonal_apply_eq, Complex.ofReal_sum,
        Complex.ofReal_mul] using
        congrArg Complex.ofReal (show ∑ b, p a i * q b i = p a i by
          rw [← Finset.mul_sum, hqs, mul_one])
    · simp [Matrix.sum_apply, Matrix.diagonal, hij]
  · intro b
    ext i j
    by_cases hij : i = j
    · subst j
      simpa only [Matrix.sum_apply, Matrix.diagonal_apply_eq, Complex.ofReal_sum,
        Complex.ofReal_mul] using
        congrArg Complex.ofReal (show ∑ a, p a i * q b i = q b i by
          rw [← Finset.sum_mul, hps, one_mul])
    · simp [Matrix.sum_apply, Matrix.diagonal, hij]

/-- Diagonal outputs admit compatible diagonal simulations of every pair of POVMs. -/
private theorem diagonal_output_conceals {din dout : ℕ} {Ω Λ : Type}
    [Fintype Ω] [Fintype Λ] (E : MatrixMap (Fin din) (Fin dout) ℂ)
    (hE : ∀ ρ, E ρ = diagonal (diag (E ρ)))
    (T : Set (Matrix (Fin din) (Fin din) ℂ))
    (M : Ω → Matrix (Fin dout) (Fin dout) ℂ)
    (N : Λ → Matrix (Fin dout) (Fin dout) ℂ) (hM : IsPOVM M) (hN : IsPOVM N) :
    Concealed E T M N := by
  have weights {Γ : Type} [Fintype Γ] (P : Γ → Matrix (Fin dout) (Fin dout) ℂ)
      (hP : IsPOVM P) :
      (∀ a i, 0 ≤ (P a i i).re) ∧ (∀ i, ∑ a, (P a i i).re = 1) := by
    refine ⟨fun a i => (Complex.nonneg_iff.mp (hP.1 a).diag_nonneg).1, ?_⟩
    intro i
    simpa [Matrix.sum_apply] using congrArg (fun A => (A i i).re) hP.2
  have statistics (A : Matrix (Fin dout) (Fin dout) ℂ) (hA : A.IsHermitian) (ρ) :
      trace (diagonal (fun i => ((A i i).re : ℂ)) * E ρ) = trace (A * E ρ) := by
    rw [hE ρ]
    simp only [Matrix.trace, Matrix.mul_diagonal, Matrix.diagonal_apply_eq, Matrix.diag_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [show ((A i i).re : ℂ) = A i i from hA.coe_re_apply_self i]
  refine ⟨fun a => diagonal (fun i => ((M a i i).re : ℂ)),
    fun b => diagonal (fun i => ((N b i i).re : ℂ)),
    diagonal_compatible _ _ (weights M hM).1 (weights N hN).1
      (weights M hM).2 (weights N hN).2,
    fun ρ _ a => statistics _ (hM.1 a).isHermitian ρ,
    fun ρ _ b => statistics _ (hN.1 b).isHermitian ρ⟩

/-- Scalar outputs admit compatible scalar simulations with normalized trace weights. -/
private theorem scalar_output_conceals {din dout : ℕ} {Ω Λ : Type}
    [Fintype Ω] [Fintype Λ] (hdout : dout ≠ 0)
    (E : MatrixMap (Fin din) (Fin dout) ℂ)
    (hE : ∀ ρ, ∃ c : ℂ, E ρ = c • (1 : Matrix (Fin dout) (Fin dout) ℂ))
    (T : Set (Matrix (Fin din) (Fin din) ℂ))
    (M : Ω → Matrix (Fin dout) (Fin dout) ℂ)
    (N : Λ → Matrix (Fin dout) (Fin dout) ℂ) (hM : IsPOVM M) (hN : IsPOVM N) :
    Concealed E T M N := by
  have hd : (dout : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hdout
  have weights {Γ : Type} [Fintype Γ] (P : Γ → Matrix (Fin dout) (Fin dout) ℂ)
      (hP : IsPOVM P) :
      (∀ (a : Γ) (i : Fin dout), 0 ≤ (trace (P a)).re / dout) ∧
      (∀ i : Fin dout, ∑ a, (trace (P a)).re / dout = 1) := by
    refine ⟨fun a _ => div_nonneg (Complex.nonneg_iff.mp (hP.1 a).trace_nonneg).1
      (Nat.cast_nonneg _), ?_⟩
    intro _
    have hs : ∑ a, (trace (P a)).re = dout := by
      simpa only [Matrix.trace_sum, Complex.re_sum, Matrix.trace_one,
        Fintype.card_fin, Complex.natCast_re] using congrArg (fun A => (trace A).re) hP.2
    rw [← Finset.sum_div, hs, div_self hd]
  have statistics (A : Matrix (Fin dout) (Fin dout) ℂ) (hA : A.IsHermitian) (ρ) :
      trace (diagonal (fun _ : Fin dout => (((trace A).re / dout : ℝ) : ℂ)) * E ρ) =
        trace (A * E ρ) := by
    obtain ⟨c, hc⟩ := hE ρ
    rw [hc]
    simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]
    congr 1
    have hr : ((trace A).re : ℂ) = trace A := by
      simp only [Matrix.trace, Complex.re_sum, Complex.ofReal_sum, Matrix.diag_apply]
      exact Finset.sum_congr rfl (fun i _ => hA.coe_re_apply_self i)
    simp only [Matrix.trace_diagonal, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Complex.ofReal_div, Complex.ofReal_natCast, hr]
    field_simp
  refine ⟨fun a => diagonal (fun _ : Fin dout => (((trace (M a)).re / dout : ℝ) : ℂ)),
    fun b => diagonal (fun _ : Fin dout => (((trace (N b)).re / dout : ℝ) : ℂ)),
    diagonal_compatible _ _ (weights M hM).1 (weights N hN).1
      (weights M hM).2 (weights N hN).2,
    fun ρ _ a => statistics _ (hM.1 a).isHermitian ρ,
    fun ρ _ b => statistics _ (hN.1 b).isHermitian ρ⟩

/-- Complete dephasing and complete depolarization refute kernel necessity. -/
theorem result : ¬ claim := by
  intro hclaim
  let KD : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ := fun j => Matrix.single j j 1
  let KR : Pauli → Matrix (Fin 2) (Fin 2) ℂ := fun p => (1 / 2 : ℂ) • pauliMatrix p
  let D := MatrixMap.of_kraus KD KD
  let R := MatrixMap.of_kraus KR KR
  have pauliI : pauliMatrix .I = 1 := rfl
  have pauliX : pauliMatrix .X = qubitX := rfl
  have pauliY : pauliMatrix .Y = Complex.I • (qubitX * qubitZ) := rfl
  have pauliZ : pauliMatrix .Z = qubitZ := rfl
  have hW := D5.S3.Quantum.FiniteDimensional.qubit_weyl_star
  have hXadj : qubitXᴴ = qubitX := by
    simpa only [Matrix.star_eq_conjTranspose] using hW.2.1
  have hZadj : qubitZᴴ = qubitZ := by
    simpa only [Matrix.star_eq_conjTranspose] using hW.2.2.1
  have hYadj : (Complex.I • (qubitX * qubitZ))ᴴ = Complex.I • (qubitX * qubitZ) := by
    simp [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hXadj, hZadj, hW.1]
  have pauli_sum (f : Pauli → ℂ) : ∑ p, f p = f .I + f .X + f .Y + f .Z := by
    change (∑ p ∈ {Pauli.I, .X, .Y, .Z}, f p) = _
    simp [add_assoc]
  have hKD : ∀ j, (KD j)ᴴ = KD j := by
    intro j
    simp [KD]
  have hKR : ∀ p, (KR p)ᴴ = KR p := by
    intro p
    cases p <;> simp [KR, pauliI, pauliX, pauliY, pauliZ, hXadj, hYadj, hZadj]
  have hTPD : (∑ j, (KD j)ᴴ * KD j) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [KD, Matrix.single, Matrix.conjTranspose_apply, Matrix.mul_apply,
        Fin.sum_univ_two]
  have hTPR : (∑ p, (KR p)ᴴ * KR p) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.sum_apply, pauli_sum, KR, pauliI, pauliX, pauliY, pauliZ, qubitX, qubitZ,
        Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two]
  have hD : D = pinchingEnd := by
    exact pinching_kraus.symm
  have hDdiagonal : ∀ ρ, D ρ = diagonal (diag (D ρ)) := by
    intro ρ
    rw [hD, dephase_apply]
    simp
  have hR (ρ : Matrix (Fin 2) (Fin 2) ℂ) : R ρ = (trace ρ / 2) • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [R, MatrixMap.of_kraus, Matrix.sum_apply, pauli_sum, KR,
        pauliI, pauliX, pauliY, pauliZ, qubitX, qubitZ, Matrix.conjTranspose_apply, Matrix.mul_apply,
        Matrix.trace, Fin.sum_univ_two] <;>
      ring_nf <;> simp [Complex.I_sq] <;> ring
  have selfdual {κ : Type} [Fintype κ] (K : κ → Matrix (Fin 2) (Fin 2) ℂ)
      (hK : ∀ j, (K j)ᴴ = K j) (A : Matrix (Fin 2) (Fin 2) ℂ) :
      (MatrixMap.of_kraus K K).dual A = MatrixMap.of_kraus K K A := by
    rw [dual_kraus]
    simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk, hK]
  have hDZ : D.dual qubitZ = qubitZ := by
    rw [selfdual KD hKD]
    change D qubitZ = qubitZ
    rw [hD, dephase_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [qubitZ, Matrix.diagonal]
  have hRZ : R.dual qubitZ = 0 := by
    rw [selfdual KR hKR, hR]
    simp [qubitZ, Matrix.trace, Fin.sum_univ_two]
  have hZ : qubitZ.IsHermitian := by
    exact hZadj
  have hZne : qubitZ ≠ 0 := by
    intro hz
    have := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 0) hz
    norm_num [qubitZ] at this
  have hkernel := hclaim 2 2 (Fin 2) Pauli KD KR hTPD hTPR
    {ρ : Matrix (Fin 2) (Fin 2) ℂ | IsDensity ρ} (all_density_tomographically_complete 2)
    (by
      intro Ω Λ _ _ M N hM hN
      exact ⟨fun _ => scalar_output_conceals (by decide) R
          (fun ρ => ⟨trace ρ / 2, hR ρ⟩) _ M N hM hN,
        fun _ => diagonal_output_conceals D hDdiagonal _ M N hM hN⟩)
  have hzR : qubitZ ∈ AdjointKernel R := ⟨hZ, hRZ⟩
  have hzD : qubitZ ∈ AdjointKernel D := hkernel ▸ hzR
  exact hZne (hDZ.symm.trans hzD.2)

#print axioms result

end D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
