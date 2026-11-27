/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reflection/TwoQubitMarginalReflection
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reflection/TwoQubitMarginalReflection
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reflection.QubitBlochReflection, lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reflection.PeriodicMPSUniformChirality]
   utility: none
   digest: A two-qubit marginal preserved by an antiunitary reflection. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reflection.QubitBlochReflection
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reflection.PeriodicMPSUniformChirality

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.TwoQubitMarginalReflection

open Matrix
open scoped Matrix Kronecker ComplexConjugate
open WithLp
open QubitBlochReflection
open Measurement.FourQubitParentConstruction (B B_formula_core)
open PeriodicMPSUniformChirality (pauli blochVector blochCorrelation)

noncomputable section

abbrev Bits := Fin 2 × Fin 2
abbrev Density := Matrix Bits Bits ℂ

/-- Simultaneous exchange of the two sites in both matrix indices. -/
def ExchangeSymmetric (ρ : Density) : Prop :=
  ∀ p q, ρ p.swap q.swap = ρ p q

private def pauliFrame : Fin 4 → QubitMatrix := Fin.cases 1 pauli

private theorem pauli_explicit (i : Fin 3) :
    pauli i = (![!![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0],
      !![1, 0; 0, -1]] : Fin 3 → QubitMatrix) i := by
  have h : pauli i = GaussianInt.toComplex.mapMatrix
      ((![!![0, 1; 1, 0], !![0, -⟨0, 1⟩; ⟨0, 1⟩, 0],
        !![1, 0; 0, -1]] : Fin 3 → Matrix (Fin 2) (Fin 2) GaussianInt) i) := rfl
  rw [h]
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [RingHom.mapMatrix_apply, GaussianInt.toComplex_def']

private theorem B_eq_sum_pauli (x : BlochVector) :
    B (toLp 2 x) = ∑ i : Fin 3, x i • pauli i := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B_formula_core, pauli_explicit, Fin.sum_univ_three, Complex.real_smul] <;> ring

private theorem pauliFrame_hermitian (i : Fin 4) : (pauliFrame i).IsHermitian := by
  refine Fin.cases (by simp [pauliFrame]) (fun j => ?_) i
  change (pauli j)ᴴ = pauli j
  fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [pauli_explicit, Matrix.conjTranspose_apply]

private theorem frame_completeness (a b c d : Fin 2) :
    ∑ i : Fin 4, pauliFrame i a b * pauliFrame i c d =
      if a = d ∧ b = c then (2 : ℂ) else 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [Fin.sum_univ_succ, pauliFrame, pauli_explicit, Complex.I_mul_I]

private def expect (O ρ : Density) : ℝ := (O * ρ).trace.re

private theorem trace_is_real {O ρ : Density} (hO : O.IsHermitian) (hρ : ρ.IsHermitian) :
    ((O * ρ).trace.re : ℂ) = (O * ρ).trace := by
  rw [← Complex.conj_eq_iff_re]
  change star (O * ρ).trace = _
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hO.eq, hρ.eq, Matrix.trace_mul_comm]

private theorem eq_of_frame_readouts {ρ σ : Density} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (h : ∀ i j, expect (pauliFrame i ⊗ₖ pauliFrame j) ρ =
      expect (pauliFrame i ⊗ₖ pauliFrame j) σ) : ρ = σ := by
  have htrace (i j : Fin 4) : ((pauliFrame i ⊗ₖ pauliFrame j) * ρ).trace =
      ((pauliFrame i ⊗ₖ pauliFrame j) * σ).trace := by
    have hO : (pauliFrame i ⊗ₖ pauliFrame j).IsHermitian := by
      change (pauliFrame i ⊗ₖ pauliFrame j)ᴴ = _
      rw [Matrix.conjTranspose_kronecker, (pauliFrame_hermitian i).eq, (pauliFrame_hermitian j).eq]
    rw [← trace_is_real hO hρ, ← trace_is_real hO hσ]
    exact congrArg Complex.ofReal (h i j)
  have rebuild (τ : Density) (p q : Bits) :
      (∑ i : Fin 4, ∑ j : Fin 4, ((pauliFrame i ⊗ₖ pauliFrame j) * τ).trace *
        (pauliFrame i ⊗ₖ pauliFrame j) p q) = 4 * τ p q := by
    calc
      _ = ∑ a : Bits, ∑ b : Bits, τ b a *
          ((∑ i : Fin 4, pauliFrame i p.1 q.1 * pauliFrame i a.1 b.1) *
           (∑ j : Fin 4, pauliFrame j p.2 q.2 * pauliFrame j a.2 b.2)) := by
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.kroneckerMap_apply,
          Finset.sum_mul, Finset.mul_sum]
        simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 4)))
          (t := (Finset.univ : Finset Bits))]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ = _ := by
        simp_rw [frame_completeness]
        rcases p with ⟨p₁, p₂⟩
        rcases q with ⟨q₁, q₂⟩
        simp [Fintype.sum_prod_type, Fin.sum_univ_two]
        fin_cases p₁ <;> fin_cases p₂ <;> fin_cases q₁ <;> fin_cases q₂ <;> simp <;> ring
  ext p q
  apply mul_left_cancel₀ (show (4 : ℂ) ≠ 0 by norm_num)
  rw [← rebuild ρ p q, ← rebuild σ p q]
  simp_rw [htrace]

private theorem expect_swap {ρ : Density} (hρ : ExchangeSymmetric ρ) (P Q : QubitMatrix) :
    expect (P ⊗ₖ Q) ρ = expect (Q ⊗ₖ P) ρ := by
  unfold expect
  congr 1
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.kroneckerMap_apply]
  let swap := Equiv.prodComm (Fin 2) (Fin 2)
  rw [← swap.sum_comp (fun a : Bits => ∑ b : Bits, Q a.1 b.1 * P a.2 b.2 * ρ b a)]
  apply Finset.sum_congr rfl
  intro a _
  rw [← swap.sum_comp (fun b : Bits => Q (swap a).1 b.1 * P (swap a).2 b.2 * ρ b (swap a))]
  apply Finset.sum_congr rfl
  intro b _
  change P a.1 b.1 * Q a.2 b.2 * ρ b a = Q a.2 b.2 * P a.1 b.1 * ρ b.swap a.swap
  rw [hρ, mul_comm (Q _ _) (P _ _)]

theorem correlation_transpose {ρ : Density} (hρ : ExchangeSymmetric ρ) :
    (blochCorrelation ρ)ᵀ = blochCorrelation ρ := by
  ext i j
  exact expect_swap hρ (pauli j) (pauli i)

private def action {ι : Type*} [Fintype ι] (U M : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  U * conjEntries M * Uᴴ

/-- Density-matrix action of the collective qubit antiunitary at two sites. -/
def reflectMarginal (v : BlochVector) (ρ : Density) : Density :=
  action (reflectionUnitary v ⊗ₖ reflectionUnitary v) ρ

private theorem conjEntries_kronecker (P Q : QubitMatrix) :
    conjEntries (P ⊗ₖ Q) = conjEntries P ⊗ₖ conjEntries Q := by
  ext
  simp [Matrix.kroneckerMap_apply, map_mul]

private theorem action_kronecker (U P Q : QubitMatrix) :
    action (U ⊗ₖ U) (P ⊗ₖ Q) = action U P ⊗ₖ action U Q := by
  rw [action, conjEntries_kronecker, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  rfl

private theorem expect_action (V O ρ : Density) (hV : Vᴴ = conjEntries V) :
    expect O (action V ρ) = expect (action V O) ρ := by
  have hre (M : Density) : (conjEntries M).trace.re = M.trace.re := by
    simp [Matrix.trace, Matrix.diag_apply, Complex.re_sum]
  unfold expect action
  rw [← hre (O * (V * conjEntries ρ * Vᴴ))]
  simp only [conjEntries_mul, conjEntries_conjEntries]
  have hc : conjEntries Vᴴ = V := by rw [hV, conjEntries_conjEntries]
  rw [hc, ← hV]
  congr 1
  rw [← Matrix.mul_assoc (conjEntries O), ← Matrix.mul_assoc (conjEntries O),
    Matrix.trace_mul_comm _ V]
  simp only [Matrix.mul_assoc]

private theorem reflectMarginal_hermitian {v : BlochVector} {ρ : Density}
    (hρ : ρ.IsHermitian) : (reflectMarginal v ρ).IsHermitian := by
  have hc : (conjEntries ρ)ᴴ = conjEntries ρ := by
    change conjEntries ρᴴ = conjEntries ρ
    rw [hρ.eq]
  change (action _ ρ)ᴴ = action _ ρ
  simp [action, Matrix.conjTranspose_mul, hc, Matrix.mul_assoc]

private theorem action_identity (v : BlochVector) (hv : v ⬝ᵥ v = 1) :
    action (reflectionUnitary v) (1 : QubitMatrix) = 1 := by
  have h : conjEntries (1 : QubitMatrix) = 1 := by
    ext i j; simp [Matrix.one_apply]
  rw [action, h, Matrix.mul_one, reflectionUnitary_adjoint, reflectionUnitary_involution v hv]

private theorem action_pauli (v : BlochVector) (hv : v ⬝ᵥ v = 1) (i : Fin 3) :
    action (reflectionUnitary v) (pauli i) =
      ∑ j : Fin 3, reflection v j i • pauli j := by
  rw [← show B (toLp 2 (Pi.single i 1)) = pauli i by
    rw [B_eq_sum_pauli]; simp [Pi.single_apply, ite_smul],
    action, conjugate_bloch v _ hv, B_eq_sum_pauli]
  congr 1
  ext j
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite]

private theorem expect_sum_left {ι : Type*} [Fintype ι]
    (A : ι → Density) (s : ι → ℝ) (ρ : Density) :
    expect (∑ i, s i • A i) ρ = ∑ i, s i * expect (A i) ρ := by
  simp [expect, Matrix.sum_mul, Matrix.trace_sum, Matrix.trace_smul,
    Complex.re_sum, Complex.real_smul, Complex.mul_re]

private theorem expect_reflect_kronecker (v : BlochVector) (P Q : QubitMatrix) (ρ : Density) :
    expect (P ⊗ₖ Q) (reflectMarginal v ρ) =
      expect (action (reflectionUnitary v) P ⊗ₖ action (reflectionUnitary v) Q) ρ := by
  rw [reflectMarginal, expect_action, action_kronecker]
  rw [Matrix.conjTranspose_kronecker, conjEntries_kronecker, reflectionUnitary_adjoint]

private theorem kronecker_sum_left {ι : Type*} [Fintype ι]
    (P : ι → QubitMatrix) (s : ι → ℝ) (Q : QubitMatrix) :
    (∑ i, s i • P i) ⊗ₖ Q = ∑ i, s i • (P i ⊗ₖ Q) := by
  ext
  simp [Matrix.kroneckerMap_apply, Matrix.sum_apply, Finset.sum_mul, mul_assoc, Complex.real_smul]

private theorem kronecker_sum_right {ι : Type*} [Fintype ι]
    (P : QubitMatrix) (s : ι → ℝ) (Q : ι → QubitMatrix) :
    P ⊗ₖ (∑ i, s i • Q i) = ∑ i, s i • (P ⊗ₖ Q i) := by
  ext
  simp [Matrix.kroneckerMap_apply, Matrix.sum_apply, Finset.mul_sum, Complex.real_smul, mul_left_comm]

/-- The reflected marginal has the reflected first Bloch vector. -/
theorem reflectMarginal_blochVector (v : BlochVector) (hv : v ⬝ᵥ v = 1) (ρ : Density) :
    blochVector (reflectMarginal v ρ) = reflection v *ᵥ blochVector ρ := by
  funext i
  change expect (pauli i ⊗ₖ 1) (reflectMarginal v ρ) = _
  rw [expect_reflect_kronecker, action_identity v hv, action_pauli v hv, kronecker_sum_left,
    expect_sum_left]
  change (∑ j, reflection v j i * blochVector ρ j) =
    ∑ j, reflection v i j * blochVector ρ j
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show reflection v j i = reflection v i j from
    congrFun (congrFun (reflection_transpose v) i) j]

/-- The reflected marginal has the congruence transform of the correlation matrix. -/
theorem reflectMarginal_blochCorrelation (v : BlochVector) (hv : v ⬝ᵥ v = 1) (ρ : Density) :
    blochCorrelation (reflectMarginal v ρ) =
      reflection v * blochCorrelation ρ * (reflection v)ᵀ := by
  ext i j
  change expect (pauli i ⊗ₖ pauli j) (reflectMarginal v ρ) = _
  rw [expect_reflect_kronecker, action_pauli v hv, action_pauli v hv,
    kronecker_sum_left, expect_sum_left]
  simp_rw [kronecker_sum_right, expect_sum_left, Matrix.mul_apply, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  have hs (a b : Fin 3) : reflection v a b = reflection v b a :=
    congrFun (congrFun (reflection_transpose v).symm a) b
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
    change reflection v l i * (reflection v k j * blochCorrelation ρ l k) =
      reflection v i l * blochCorrelation ρ l k * reflection v j k
    rw [hs l i, hs k j]
    ring

/-- A unit normal orthogonal to the observed Bloch vector and in an eigenspace
of the correlation matrix fixes the full exchange-symmetric marginal. -/
theorem reflectMarginal_eq (ρ : Density) (hρ : ρ.IsHermitian) (hex : ExchangeSymmetric ρ)
    (v : BlochVector) (hv : v ⬝ᵥ v = 1) (hr : v ⬝ᵥ blochVector ρ = 0)
    {μ : ℝ} (he : blochCorrelation ρ *ᵥ v = μ • v) :
    reflectMarginal v ρ = ρ := by
  have hr' := reflection_fixes_vector v (blochVector ρ) hr
  have hc := reflection_fixes_correlation v _ hv (correlation_transpose hex) he
  apply eq_of_frame_readouts (reflectMarginal_hermitian hρ) hρ
  intro i j
  refine Fin.cases ?_ (fun k => ?_) i <;> refine Fin.cases ?_ (fun l => ?_) j
  · change expect (1 ⊗ₖ 1) (reflectMarginal v ρ) = _
    rw [expect_reflect_kronecker, action_identity v hv]
    rfl
  · change expect (1 ⊗ₖ pauli l) (reflectMarginal v ρ) = expect (1 ⊗ₖ pauli l) ρ
    rw [expect_reflect_kronecker, action_identity v hv, action_pauli v hv, kronecker_sum_right,
      expect_sum_left, expect_swap hex (1 : QubitMatrix) (pauli l)]
    simp_rw [expect_swap hex (1 : QubitMatrix)]
    have hl := congrFun hr' l
    change (∑ k, reflection v l k * expect (pauli k ⊗ₖ 1) ρ) =
      expect (pauli l ⊗ₖ 1) ρ at hl
    have hs (k : Fin 3) : reflection v k l = reflection v l k :=
      congrFun (congrFun (reflection_transpose v) l) k
    simpa only [hs] using hl
  · exact congrFun ((reflectMarginal_blochVector v hv ρ).trans hr') k
  · exact congrFun (congrFun ((reflectMarginal_blochCorrelation v hv ρ).trans hc) k) l

/-- The literal chirality determinant supplies a collective antiunitary fixing
the complete exchange-symmetric Hermitian marginal. -/
theorem exists_reflection_of_det_zero (ρ : Density) (hρ : ρ.IsHermitian)
    (hex : ExchangeSymmetric ρ)
    (hdet : (krylovMatrix (blochVector ρ) (blochCorrelation ρ)).det = 0) :
    ∃ v : BlochVector, v ⬝ᵥ v = 1 ∧ reflectMarginal v ρ = ρ ∧
      reflection v *ᵥ blochVector ρ = blochVector ρ ∧
      reflection v * blochCorrelation ρ * (reflection v)ᵀ = blochCorrelation ρ := by
  obtain ⟨v, hv, hr, μ, he⟩ := exists_unit_eigenvector_of_krylov_det_zero _ _
    (correlation_transpose hex) hdet
  exact ⟨v, hv, reflectMarginal_eq ρ hρ hex v hv hr he, reflection_fixes_vector v _ hr,
    reflection_fixes_correlation v _ hv (correlation_transpose hex) he⟩

end
end D5.S3.Quantum.TensorNetworks.TwoQubitMarginalReflection
