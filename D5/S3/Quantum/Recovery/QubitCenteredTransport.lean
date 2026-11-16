/- GID: D5/S3/Quantum/Recovery/QubitCenteredTransport
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/QubitCenteredTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Attained centered tests and coherent local unitary transport. -/

import D5.S3.Quantum.Recovery.QubitCoefficientGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace D5.S3.Quantum.Information.StrongSubadditivity.MarkovConstructors

open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDensityPurification
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.StrongSubadditivity
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open scoped BigOperators Kronecker

variable {A B C : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]


/-- All four terms are the ordinary entropies of the actual partial traces. -/
theorem qcmi_eq_four_marginals (rho : DensityState (A × (B × C))) :
    qcmi (toMState rho) =
      vonNeumannEntropy (marginalRight (relabelState (Equiv.prodAssoc A B C) rho)) +
      vonNeumannEntropy (marginalLeft rho) -
      vonNeumannEntropy (marginalRight (marginalLeft rho)) - vonNeumannEntropy rho := by
  have ha : toMState (relabelState (Equiv.prodAssoc A B C) rho) =
      (toMState rho).assoc' := MState.ext_m rfl
  have hb : (toMState rho).assoc'.traceRight.traceLeft =
      (toMState rho).traceLeft.traceRight := by
    apply MState.ext_m
    ext i j
    change (∑ a : A, ∑ c : C, rho.1 (a, (i, c)) (a, (j, c))) =
      ∑ c : C, ∑ a : A, rho.1 (a, (i, c)) (a, (j, c))
    exact Finset.sum_comm
  unfold qcmi qConditionalEnt
  rw [hb]
  simp only [← ha, ← toMState_marginalRight, ← toMState_marginalLeft, entropy_toMState]
  ring

private theorem marginalAB_left_product (a : DensityState A) (omega : DensityState (B × C)) :
    marginalRight (relabelState (Equiv.prodAssoc A B C) (productState a omega)) =
      productState a (marginalRight omega) := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  ext p q
  change (∑ c : C, a.1 p.1 q.1 * omega.1 (p.2, c) (q.2, c)) =
    a.1 p.1 q.1 * ∑ c : C, omega.1 (p.2, c) (q.2, c)
  exact (Finset.mul_sum _ _ _).symm

/-- A product across A and BC has zero ordinary conditional mutual information,
including singular states. -/
theorem qcmi_product_left (a : DensityState A) (omega : DensityState (B × C)) :
    qcmi (toMState (productState a omega)) = 0 := by
  rw [qcmi_eq_four_marginals, marginalAB_left_product,
    marginalLeft_productState, vonNeumannEntropy_productState,
    vonNeumannEntropy_productState]
  ring

end D5.S3.Quantum.Information.StrongSubadditivity.MarkovConstructors

end


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Quantum.Recovery.QubitResidualRounding

open _root_.Matrix
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.StrongSubadditivity
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open scoped Matrix Matrix.Norms.L2Operator Kronecker

local notation "traceNorm" => D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm

variable {Q : Type*} [Fintype Q]

section Centered

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The centered matrix uses the two actual marginals of the input state. -/
def centered (P : DensityState (A × Fin 2)) : Matrix (A × Fin 2) (A × Fin 2) ℂ :=
  CStarMatrix.ofMatrix.symm P.1 -
    CStarMatrix.ofMatrix.symm (productState (marginalRight P) (marginalLeft P)).1

/-- A test on A reads every complex B block by its actual trace pairing. -/
def sliceLinear {B : Type*} (D : Matrix (A × B) (A × B) ℂ) :
    CStarMatrix A A ℂ →ₗ[ℂ] CStarMatrix B B ℂ where
  toFun F := CStarMatrix.ofMatrix (fun j k =>
    Matrix.trace (CStarMatrix.ofMatrix.symm F *
      D.submatrix (fun a => (a, j)) (fun a => (a, k))))
  map_add' F G := by
    apply CStarMatrix.ext
    intro j k
    change Matrix.trace ((CStarMatrix.ofMatrix.symm F + CStarMatrix.ofMatrix.symm G) * _) = _
    rw [Matrix.add_mul, Matrix.trace_add]
    rfl
  map_smul' z F := by
    apply CStarMatrix.ext
    intro j k
    change Matrix.trace ((z • CStarMatrix.ofMatrix.symm F) * _) = _
    rw [Matrix.smul_mul, Matrix.trace_smul]
    rfl

private theorem attained_centered_test (P : DensityState (A × Fin 2)) :
    ∃ F : CStarMatrix A A ℂ, IsSelfAdjoint F ∧ ‖F‖ ≤ 1 ∧
      ∀ G : CStarMatrix A A ℂ, IsSelfAdjoint G → ‖G‖ ≤ 1 →
        ‖sliceLinear (centered P) G‖ ≤ ‖sliceLinear (centered P) F‖ := by
  letI : FiniteDimensional ℂ (CStarMatrix A A ℂ) :=
    Module.Finite.equiv (CStarMatrix.ofMatrixₗ (R := ℂ) (m := A) (n := A))
  let S : Set (CStarMatrix A A ℂ) := {F | IsSelfAdjoint F ∧ ‖F‖ ≤ 1}
  have hc : IsCompact S := by
    have hsa : IsClosed {F : CStarMatrix A A ℂ | IsSelfAdjoint F} :=
      isClosed_eq continuous_star continuous_id
    have he : S = {F : CStarMatrix A A ℂ | IsSelfAdjoint F} ∩ Metric.closedBall 0 1 := by
      ext F
      simp [S, Metric.mem_closedBall, dist_zero_right]
    rw [he]
    exact (isCompact_closedBall (0 : CStarMatrix A A ℂ) 1).inter_left hsa
  have hne : S.Nonempty := ⟨0, by simp [S]⟩
  have hcont : Continuous (fun F => ‖sliceLinear (centered P) F‖) :=
    (sliceLinear (centered P)).continuous_of_finiteDimensional.norm
  obtain ⟨F, hF, hmax⟩ := hc.exists_isMaxOn hne hcont.continuousOn
  exact ⟨F, hF.1, hF.2, fun G hG hn => hmax ⟨hG, hn⟩⟩

theorem centered_marginals_zero (P : DensityState (A × Fin 2)) :
    partialTraceLeft (centered P) = 0 ∧ partialTraceRight (centered P) = 0 := by
  constructor
  · have he := marginalLeft_productState (marginalRight P) (marginalLeft P)
    have hr := congrArg (fun S : DensityState (Fin 2) => CStarMatrix.ofMatrix.symm S.1) he
    ext j k
    change (∑ a, (CStarMatrix.ofMatrix.symm P.1 (a, j) (a, k) -
      CStarMatrix.ofMatrix.symm (productState (marginalRight P) (marginalLeft P)).1
        (a, j) (a, k))) = 0
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (congrFun (congrFun hr j) k).symm
  · have he := marginalRight_productState (marginalRight P) (marginalLeft P)
    have hr := congrArg (fun S : DensityState A => CStarMatrix.ofMatrix.symm S.1) he
    ext j k
    change (∑ b, (CStarMatrix.ofMatrix.symm P.1 (j, b) (k, b) -
      CStarMatrix.ofMatrix.symm (productState (marginalRight P) (marginalLeft P)).1
        (j, b) (k, b))) = 0
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (congrFun (congrFun hr j) k).symm

def block {B : Type*} (D : Matrix (A × B) (A × B) ℂ) (j k : B) :
    Matrix A A ℂ := D.submatrix (fun a => (a, j)) (fun a => (a, k))

private def pauliCoefficient (D : Matrix (A × Fin 2) (A × Fin 2) ℂ) :
    Fin 3 → Matrix A A ℂ := ![
      block D 0 1 + block D 1 0,
      Complex.I • (block D 0 1 - block D 1 0),
      block D 0 0 - block D 1 1]

def pauli : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  fun i => D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix
    (![D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.X,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Y,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.Pauli.Z] i)

private theorem pauli_reconstruction (D : Matrix (A × Fin 2) (A × Fin 2) ℂ)
    (hz : partialTraceRight D = 0) :
    D = (1 / 2 : ℝ) • ∑ i : Fin 3, (pauliCoefficient D i) ⊗ₖ pauli i := by
  ext ⟨a, j⟩ ⟨b, k⟩
  have hh := congrFun (congrFun hz a) b
  simp only [partialTraceRight, Fin.sum_univ_two, Matrix.zero_apply] at hh
  fin_cases j <;> fin_cases k <;>
    simp [pauliCoefficient, block, pauli,
      D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix,
      D5.S3.Quantum.FiniteDimensional.qubitX,
      D5.S3.Quantum.FiniteDimensional.qubitZ,
      Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.kronecker_apply, Complex.real_smul] <;>
    ring_nf <;> (try simp only [Complex.I_sq]) <;>
    first | ring | linear_combination (1 / 2 : ℂ) * hh

theorem centered_hermitian (P : DensityState (A × Fin 2)) :
    (centered P).IsHermitian :=
  (density_posSemidef P).isHermitian.sub
    (density_posSemidef (productState (marginalRight P) (marginalLeft P))).isHermitian

private theorem pauliCoefficient_hermitian (D : Matrix (A × Fin 2) (A × Fin 2) ℂ)
    (hD : D.IsHermitian) (i : Fin 3) : (pauliCoefficient D i).IsHermitian := by
  have hb (j k : Fin 2) : (block D j k)ᴴ = block D k j := by
    ext a b
    exact congrFun (congrFun hD.eq (a, k)) (b, j)
  fin_cases i
  · change (block D 0 1 + block D 1 0)ᴴ = block D 0 1 + block D 1 0
    rw [Matrix.conjTranspose_add, hb, hb, add_comm]
  · change (Complex.I • (block D 0 1 - block D 1 0))ᴴ =
      Complex.I • (block D 0 1 - block D 1 0)
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, hb, hb]
    simp only [Complex.star_def, Complex.conj_I, neg_smul, ← smul_neg, neg_sub]
  · change (block D 0 0 - block D 1 1)ᴴ = block D 0 0 - block D 1 1
    rw [Matrix.conjTranspose_sub, hb, hb]

private theorem pauliCoefficient_trace (D : Matrix (A × Fin 2) (A × Fin 2) ℂ)
    (F : Matrix A A ℂ) (i : Fin 3) :
    Matrix.trace (F * pauliCoefficient D i) =
      (![sliceLinear D (CStarMatrix.ofMatrix F) 0 1 + sliceLinear D (CStarMatrix.ofMatrix F) 1 0,
        Complex.I * (sliceLinear D (CStarMatrix.ofMatrix F) 0 1 - sliceLinear D (CStarMatrix.ofMatrix F) 1 0),
        sliceLinear D (CStarMatrix.ofMatrix F) 0 0 - sliceLinear D (CStarMatrix.ofMatrix F) 1 1] i) := by
  fin_cases i <;>
    simp [pauliCoefficient, sliceLinear, block, Matrix.mul_add, Matrix.mul_sub,
      Matrix.mul_smul, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul]

private theorem pauliCoefficient_traceNorm_le (P : DensityState (A × Fin 2))
    (x : ℝ)
    (hx : ∀ F : CStarMatrix A A ℂ, IsSelfAdjoint F → ‖F‖ ≤ 1 →
      ‖sliceLinear (centered P) F‖ ≤ x) (i : Fin 3) :
    traceNorm (pauliCoefficient (centered P) i) ≤ 2 * x := by
  apply D5.S3.Quantum.Foundation.FiniteHermitianTraceDuality.hermitian_traceNorm_le_tests
    _ (pauliCoefficient_hermitian _ (centered_hermitian P) i)
  intro F hF hfn
  have hfc : IsSelfAdjoint (CStarMatrix.ofMatrix F) :=
    (show IsSelfAdjoint F from hF).map CStarMatrix.ofMatrixStarAlgEquiv
  have hn : ‖CStarMatrix.ofMatrix F‖ ≤ 1 := by
    change ‖CStarMatrix.ofMatrixStarAlgEquiv F‖ ≤ 1
    rw [StarAlgEquiv.norm_map]
    exact hfn
  have hk := hx (CStarMatrix.ofMatrix F) hfc hn
  have he (j k : Fin 2) : ‖sliceLinear (centered P) (CStarMatrix.ofMatrix F) j k‖ ≤ x :=
    (CStarMatrix.norm_entry_le_norm (M := sliceLinear (centered P)
      (CStarMatrix.ofMatrix F)) (i := j) (j := k)).trans hk
  rw [pauliCoefficient_trace]
  fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  · exact (Complex.re_le_norm _).trans ((norm_add_le _ _).trans (by linarith [he 0 1, he 1 0]))
  · change (Complex.I * (sliceLinear (centered P) (CStarMatrix.ofMatrix F) 0 1 -
        sliceLinear (centered P) (CStarMatrix.ofMatrix F) 1 0)).re ≤ 2 * x
    apply (Complex.re_le_norm _).trans
    rw [norm_mul, Complex.norm_I, one_mul]
    exact (norm_sub_le _ _).trans (by linarith [he 0 1, he 1 0])
  · exact (Complex.re_le_norm _).trans ((norm_sub_le _ _).trans (by linarith [he 0 0, he 1 1]))

private theorem pauli_traceNorm (i : Fin 3) : traceNorm (pauli i) = 2 := by
  have hg : (pauli i)ᴴ * pauli i = 1 := by
    fin_cases i <;>
      ext a b <;> fin_cases a <;> fin_cases b <;>
      norm_num [pauli,
        D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix,
        D5.S3.Quantum.FiniteDimensional.qubitX,
        D5.S3.Quantum.FiniteDimensional.qubitZ,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  simp [D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm, hg, Matrix.trace]

theorem traceNorm_tensor {B : Type*} [Fintype B] [DecidableEq B]
    (X : Matrix A A ℂ) (Y : Matrix B B ℂ) : traceNorm (X ⊗ₖ Y) = traceNorm X * traceNorm Y := by
  let e := (Fintype.equivFin A).symm
  let d := (Fintype.equivFin B).symm
  let f := e.prodCongr d
  have ht := D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance.traceNorm_submatrix_equiv
    (X ⊗ₖ Y) f f
  have hx := D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance.traceNorm_submatrix_equiv
    X e e
  have hy := D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance.traceNorm_submatrix_equiv
    Y d d
  have he : (X ⊗ₖ Y).submatrix f f = X.submatrix e e ⊗ₖ Y.submatrix d d := rfl
  rw [he, D5.S3.Quantum.Classicalization.XuImaiGuhneSimultaneousUnboundedness.Toolkit.traceNorm_kronecker,
    hx, hy] at ht
  exact ht.symm

/-- The maximum over all Hermitian contractions controls the centered state
without an A or C coordinate count. -/
theorem attained_centered_traceNorm_bound (P : DensityState (A × Fin 2)) :
    ∃ F : CStarMatrix A A ℂ, IsSelfAdjoint F ∧ ‖F‖ ≤ 1 ∧
      (∀ G : CStarMatrix A A ℂ, IsSelfAdjoint G → ‖G‖ ≤ 1 →
        ‖sliceLinear (centered P) G‖ ≤ ‖sliceLinear (centered P) F‖) ∧
      traceNorm (centered P) ≤ 6 * ‖sliceLinear (centered P) F‖ := by
  obtain ⟨F, hf, hfn, hmax⟩ := attained_centered_test P
  refine ⟨F, hf, hfn, hmax, ?_⟩
  let x := ‖sliceLinear (centered P) F‖
  have hc (i : Fin 3) : traceNorm (pauliCoefficient (centered P) i) ≤ 2 * x :=
    pauliCoefficient_traceNorm_le P x hmax i
  have hp (i : Fin 3) :
      traceNorm ((pauliCoefficient (centered P) i) ⊗ₖ pauli i) ≤ 4 * x := by
    rw [traceNorm_tensor, pauli_traceNorm]
    linarith [hc i]
  change traceNorm (centered P) ≤ 6 * x
  conv_lhs => rw [pauli_reconstruction _ (centered_marginals_zero P).2]
  change traceNorm (((1 / 2 : ℝ) : ℂ) •
    ∑ i : Fin 3, (pauliCoefficient (centered P) i) ⊗ₖ pauli i) ≤ 6 * x
  rw [D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.traceNorm_smul_nonneg
    _ (1 / 2 : ℝ) (by norm_num), Fin.sum_univ_three]
  have h := traceNorm_add_le
    ((pauliCoefficient (centered P) 0) ⊗ₖ pauli 0)
    (((pauliCoefficient (centered P) 1) ⊗ₖ pauli 1) +
      ((pauliCoefficient (centered P) 2) ⊗ₖ pauli 2))
  have h' := traceNorm_add_le
    ((pauliCoefficient (centered P) 1) ⊗ₖ pauli 1)
    ((pauliCoefficient (centered P) 2) ⊗ₖ pauli 2)
  change (1 / 2 : ℝ) * traceNorm _ ≤ 6 * x
  rw [add_assoc]
  linarith [hp 0, hp 1, hp 2]

end Centered

section UnitaryTransport

variable {A B C : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

def tensorUnitary (U : Matrix.unitaryGroup A ℂ)
    (V : Matrix.unitaryGroup B ℂ) : Matrix.unitaryGroup (A × B) ℂ :=
  ⟨U.val ⊗ₖ V.val, Matrix.mem_unitaryGroup_iff'.mpr (by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
      ← Matrix.mul_kronecker_mul,
      (show U.valᴴ * U.val = 1 from Unitary.coe_star_mul_self U),
      (show V.valᴴ * V.val = 1 from Unitary.coe_star_mul_self V),
      Matrix.one_kronecker_one])⟩

def conjugateState (U : Matrix.unitaryGroup A ℂ) (rho : DensityState A) :
    DensityState A :=
  D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.unitaryConjugateState
    U.val U.property rho

private theorem conjugateState_value (U : Matrix.unitaryGroup A ℂ) (rho : DensityState A) :
    CStarMatrix.ofMatrix.symm (conjugateState U rho).1 =
      U.val * CStarMatrix.ofMatrix.symm rho.1 * U.valᴴ := rfl

private theorem entropy_conjugateState (U : Matrix.unitaryGroup A ℂ) (rho : DensityState A) :
    vonNeumannEntropy (conjugateState U rho) = vonNeumannEntropy rho :=
  D5.S3.Quantum.Information.CorrelatedGibbsEnergyIdentity.von_neumann_entropy_unitary
    U.val U.property rho

def conjugateAlg (U : Matrix.unitaryGroup A ℂ) :
    CStarMatrix A A ℂ ≃⋆ₐ[ℂ] CStarMatrix A A ℂ :=
  CStarMatrix.ofMatrixStarAlgEquiv.symm.trans
    ((Unitary.conjStarAlgAut ℂ (Matrix A A ℂ) U).trans CStarMatrix.ofMatrixStarAlgEquiv)

private def conjugateChannel (U : Matrix.unitaryGroup A ℂ) : QuantumChannel A A where
  toCompletelyPositiveMap :=
    CompletelyPositiveMapClass.toCompletelyPositiveLinearMap (conjugateAlg U)
  trace_preserving X := by
    change Matrix.trace (U.val * CStarMatrix.ofMatrix.symm X * U.valᴴ) = Matrix.trace _
    rw [Matrix.trace_mul_cycle, (show U.valᴴ * U.val = 1 from Unitary.coe_star_mul_self U),
      Matrix.one_mul]
    rfl

private theorem conjugateState_inverse (U : Matrix.unitaryGroup A ℂ)
    (rho : DensityState A) : conjugateState U (conjugateState (star U) rho) = rho := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  rw [conjugateState_value, conjugateState_value]
  simp only [Unitary.coe_star, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  change U.val * (U.valᴴ * CStarMatrix.ofMatrix.symm rho.1 * U.val) * U.valᴴ = _
  calc
    _ = (U.val * U.valᴴ) * CStarMatrix.ofMatrix.symm rho.1 * (U.val * U.valᴴ) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [show U.val * U.valᴴ = 1 from Unitary.coe_mul_star_self U]; simp

theorem tensor_conjugate_block (U : Matrix C B ℂ)
    (X : Matrix (A × B) (A × B) ℂ) (a b : A) :
    (((1 : Matrix A A ℂ) ⊗ₖ U) * X * ((1 : Matrix A A ℂ) ⊗ₖ U)ᴴ).submatrix
        (fun j => (a, j)) (fun k => (b, k)) =
      U * X.submatrix (fun j => (a, j)) (fun k => (b, k)) * Uᴴ := by
  ext j k
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
    Matrix.one_apply, apply_ite]

private theorem referenceState_conjugate (U : Matrix.unitaryGroup B ℂ)
    (P : DensityState (A × B)) :
    referenceState (conjugateChannel U) P = conjugateState (tensorUnitary 1 U) P := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  ext ⟨a,j⟩ ⟨b,k⟩
  have h := congrFun (congrFun (tensor_conjugate_block U.val
    (CStarMatrix.ofMatrix.symm P.1) a b) j) k
  exact h.symm

private theorem referenceState_comp (T : QuantumChannel B C)
    (S : QuantumChannel A B) {R : Type*} [Fintype R] [DecidableEq R]
    (P : DensityState (R × A)) :
    referenceState (T.comp S) P = referenceState T (referenceState S P) := by
  apply Subtype.ext
  apply CStarMatrix.ext
  rintro ⟨a,j⟩ ⟨b,k⟩
  rfl

/-- Rotate the input and the same output B coordinate of the physical channel. -/
def localBChannel (U : Matrix.unitaryGroup B ℂ) (T : QuantumChannel B (B × C)) :
    QuantumChannel B (B × C) :=
  (conjugateChannel (tensorUnitary (star U) 1)).comp (T.comp (conjugateChannel U))

theorem localBChannel_reference (U : Matrix.unitaryGroup B ℂ)
    (T : QuantumChannel B (B × C)) (P : DensityState (A × B)) :
    referenceState (localBChannel U T) (conjugateState (tensorUnitary 1 (star U)) P) =
      conjugateState (tensorUnitary 1 (tensorUnitary (star U) 1)) (referenceState T P) := by
  rw [localBChannel, referenceState_comp, referenceState_comp,
    referenceState_conjugate, referenceState_conjugate]
  have ht : tensorUnitary (1 : Matrix.unitaryGroup A ℂ) (star U) =
      star (tensorUnitary (1 : Matrix.unitaryGroup A ℂ) U) := by
    apply Subtype.ext
    simp [tensorUnitary, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker]
  rw [ht, conjugateState_inverse]

theorem traceDistance_conjugateState (U : Matrix.unitaryGroup A ℂ)
    (rho sigma : DensityState A) :
    traceDistance (conjugateState U rho) (conjugateState U sigma) =
      traceDistance rho sigma := by
  unfold traceDistance
  rw [conjugateState_value, conjugateState_value]
  rw [← Matrix.sub_mul, ← Matrix.mul_sub]
  rw [D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.traceNorm_isometry
    U.val (Unitary.coe_star_mul_self U)]

private theorem partialTraceLeft_isometries
    (U : Matrix.unitaryGroup A ℂ) (V : Matrix B B ℂ)
    (D : Matrix (A × B) (A × B) ℂ) :
    partialTraceLeft ((U.val ⊗ₖ V) * D * (U.val ⊗ₖ V)ᴴ) =
      V * partialTraceLeft D * Vᴴ := by
  let e := Equiv.prodComm B A
  have hs (M : Matrix (A × B) (A × B) ℂ) :
      partialTraceLeft M = partialTraceRight (M.submatrix e e) := rfl
  rw [hs]
  have ht : ((U.val ⊗ₖ V) * D * (U.val ⊗ₖ V)ᴴ).submatrix e e =
      (V ⊗ₖ U.val) * D.submatrix e e * (V ⊗ₖ U.val)ᴴ := by
    rw [← Matrix.submatrix_mul_equiv _ _ e e e,
      ← Matrix.submatrix_mul_equiv _ _ e e e]
    have hk : (U.val ⊗ₖ V).submatrix e e = V ⊗ₖ U.val := by
      ext i j
      simp [e, mul_comm]
    rw [hk, ← Matrix.conjTranspose_submatrix, hk]
  rw [ht]
  exact D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.partialTrace_isometries
    V U.val (Unitary.coe_star_mul_self U) (D.submatrix e e)

private theorem marginalRight_conjugate (U : Matrix.unitaryGroup A ℂ)
    (V : Matrix.unitaryGroup B ℂ) (P : DensityState (A × B)) :
    marginalRight (conjugateState (tensorUnitary U V) P) =
      conjugateState U (marginalRight P) := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  change partialTraceRight (CStarMatrix.ofMatrix.symm
    (conjugateState (tensorUnitary U V) P).1) = _
  rw [conjugateState_value, conjugateState_value]
  exact D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance.partialTrace_isometries
    U.val V.val (Unitary.coe_star_mul_self V) (CStarMatrix.ofMatrix.symm P.1)

private theorem marginalLeft_conjugate (U : Matrix.unitaryGroup A ℂ)
    (V : Matrix.unitaryGroup B ℂ) (P : DensityState (A × B)) :
    marginalLeft (conjugateState (tensorUnitary U V) P) =
      conjugateState V (marginalLeft P) := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  change partialTraceLeft (CStarMatrix.ofMatrix.symm
    (conjugateState (tensorUnitary U V) P).1) = _
  rw [conjugateState_value, conjugateState_value]
  exact partialTraceLeft_isometries U V.val (CStarMatrix.ofMatrix.symm P.1)

private theorem productState_conjugate (U : Matrix.unitaryGroup A ℂ)
    (V : Matrix.unitaryGroup B ℂ) (a : DensityState A) (b : DensityState B) :
    productState (conjugateState U a) (conjugateState V b) =
      conjugateState (tensorUnitary U V) (productState a b) := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  change CStarMatrix.ofMatrix.symm (conjugateState U a).1 ⊗ₖ
    CStarMatrix.ofMatrix.symm (conjugateState V b).1 = _
  rw [conjugateState_value, conjugateState_value, conjugateState_value]
  change (U.val * CStarMatrix.ofMatrix.symm a.1 * U.valᴴ) ⊗ₖ
      (V.val * CStarMatrix.ofMatrix.symm b.1 * V.valᴴ) =
    (U.val ⊗ₖ V.val) * (CStarMatrix.ofMatrix.symm a.1 ⊗ₖ
      CStarMatrix.ofMatrix.symm b.1) * (U.val ⊗ₖ V.val)ᴴ
  rw [Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]

/-- Change the B coordinate of the same physical ABC density state. -/
def localBState (U : Matrix.unitaryGroup B ℂ) (rho : DensityState (A × (B × C))) :
    DensityState (A × (B × C)) :=
  conjugateState (tensorUnitary 1 (tensorUnitary (star U) 1)) rho

private theorem localBState_assoc (U : Matrix.unitaryGroup B ℂ)
    (rho : DensityState (A × (B × C))) :
    relabelState (Equiv.prodAssoc A B C) (localBState U rho) =
      conjugateState (tensorUnitary (tensorUnitary 1 (star U)) 1)
        (relabelState (Equiv.prodAssoc A B C) rho) := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  change (CStarMatrix.ofMatrix.symm (localBState U rho).1).submatrix
    (Equiv.prodAssoc A B C) (Equiv.prodAssoc A B C) = _
  rw [localBState, conjugateState_value, conjugateState_value]
  rw [← Matrix.submatrix_mul_equiv _ _ _ (Equiv.prodAssoc A B C) _,
    ← Matrix.submatrix_mul_equiv _ _ _ (Equiv.prodAssoc A B C) _]
  have hl : (tensorUnitary 1 (tensorUnitary (star U) (1 : Matrix.unitaryGroup C ℂ))).val.submatrix
      (Equiv.prodAssoc A B C) (Equiv.prodAssoc A B C) =
      (tensorUnitary (tensorUnitary (1 : Matrix.unitaryGroup A ℂ) (star U))
        (1 : Matrix.unitaryGroup C ℂ)).val := by
    ext i j
    simp [tensorUnitary, mul_assoc]
  rw [hl, ← Matrix.conjTranspose_submatrix, hl]
  rfl

theorem localBState_AB (U : Matrix.unitaryGroup B ℂ)
    (rho : DensityState (A × (B × C))) :
    marginalRight (relabelState (Equiv.prodAssoc A B C) (localBState U rho)) =
      conjugateState (tensorUnitary 1 (star U))
        (marginalRight (relabelState (Equiv.prodAssoc A B C) rho)) := by
  rw [localBState_assoc, marginalRight_conjugate]

private theorem localBState_BC (U : Matrix.unitaryGroup B ℂ)
    (rho : DensityState (A × (B × C))) :
    marginalLeft (localBState U rho) =
      conjugateState (tensorUnitary (star U) 1) (marginalLeft rho) := by
  exact marginalLeft_conjugate 1 (tensorUnitary (star U) 1) rho

private theorem localBState_B (U : Matrix.unitaryGroup B ℂ)
    (rho : DensityState (A × (B × C))) :
    marginalRight (marginalLeft (localBState U rho)) =
      conjugateState (star U) (marginalRight (marginalLeft rho)) := by
  rw [localBState_BC, marginalRight_conjugate]

private theorem localBState_inverse (U : Matrix.unitaryGroup B ℂ)
    (rho : DensityState (A × (B × C))) : localBState (star U) (localBState U rho) = rho := by
  unfold localBState
  have ht : tensorUnitary (1 : Matrix.unitaryGroup A ℂ)
      (tensorUnitary (star U) (1 : Matrix.unitaryGroup C ℂ)) =
      star (tensorUnitary (1 : Matrix.unitaryGroup A ℂ)
        (tensorUnitary (star (star U)) (1 : Matrix.unitaryGroup C ℂ))) := by
    apply Subtype.ext
    simp [tensorUnitary, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker]
  rw [ht, conjugateState_inverse]

private theorem qcmi_localBState (U : Matrix.unitaryGroup B ℂ)
    (rho : DensityState (A × (B × C))) :
    qcmi (D5.S3.Quantum.Foundation.FiniteDensityPurification.toMState (localBState U rho)) =
      qcmi (D5.S3.Quantum.Foundation.FiniteDensityPurification.toMState rho) := by
  rw [MarkovConstructors.qcmi_eq_four_marginals, MarkovConstructors.qcmi_eq_four_marginals,
    localBState_AB, localBState_B, localBState_BC]
  simp only [localBState, entropy_conjugateState]

end UnitaryTransport

section PhysicalRepair

variable {A B C : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

def referenceRaw (T : QuantumChannel B C) :
    Matrix (A × B) (A × B) ℂ →ₗ[ℂ] Matrix (A × C) (A × C) ℂ :=
  CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp
    ((referenceLinear T).comp CStarMatrix.ofMatrixₗ.toLinearMap)

private theorem referenceRaw_contract (T : QuantumChannel B C)
    (X : Matrix (A × B) (A × B) ℂ) (hX : X.IsHermitian) :
    traceNorm (referenceRaw T X) ≤ traceNorm X := by
  apply D5.S3.Quantum.Divergence.FaithfulConditionalGap.positive_trace_contraction
    (referenceRaw T) _ _ X hX
  · intro Y hY
    exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm
      (referenceAction_nonneg T (CStarMatrix.ofMatrix Y)
        (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hY))
  · intro Y
    exact referenceAction_trace T (CStarMatrix.ofMatrix Y)

theorem referenceState_contract (T : QuantumChannel B C)
    (P Q : DensityState (A × B)) :
    traceDistance (referenceState T P) (referenceState T Q) ≤ traceDistance P Q := by
  have hc := referenceRaw_contract T
    (CStarMatrix.ofMatrix.symm P.1 - CStarMatrix.ofMatrix.symm Q.1)
    ((density_posSemidef P).isHermitian.sub (density_posSemidef Q).isHermitian)
  have he : referenceRaw T
      (CStarMatrix.ofMatrix.symm P.1 - CStarMatrix.ofMatrix.symm Q.1) =
      CStarMatrix.ofMatrix.symm (referenceState T P).1 -
        CStarMatrix.ofMatrix.symm (referenceState T Q).1 := by
    rw [map_sub]
    rfl
  rw [he] at hc
  exact div_le_div_of_nonneg_right hc (by norm_num)

theorem referenceState_product (T : QuantumChannel B C)
    (a : DensityState A) (b : DensityState B) :
    referenceState T (productState a b) = productState a (T.mapState b) := by
  apply Subtype.ext
  apply CStarMatrix.ext
  rintro ⟨i, u⟩ ⟨j, v⟩
  change T.toCompletelyPositiveMap
    (CStarMatrix.ofMatrix (fun x y => a.1 i j * b.1 x y)) u v =
      a.1 i j * T.toCompletelyPositiveMap b.1 u v
  have he : CStarMatrix.ofMatrix (fun x y => a.1 i j * b.1 x y) =
      a.1 i j • b.1 := rfl
  rw [he, map_smul]
  rfl

theorem cstar_sum_entry {I : Type*} [Fintype I]
    (f : I → CStarMatrix B B ℂ) (i j : B) :
    (∑ k, f k) i j = ∑ k, f k i j := by
  classical
  suffices h : ∀ s : Finset I, (∑ k ∈ s, f k) i j = ∑ k ∈ s, f k i j by
    simpa only [Finset.mem_univ, Finset.sum_const_zero, if_true] using h Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, CStarMatrix.zero_apply]
  | @insert k s hk ih =>
    simp only [Finset.sum_insert hk, CStarMatrix.add_apply, ih]

theorem slice_sub (D E : Matrix (A × B) (A × B) ℂ)
    (F : CStarMatrix A A ℂ) :
    sliceLinear (D - E) F = sliceLinear D F - sliceLinear E F := by
  apply CStarMatrix.ext
  intro j k
  change Matrix.trace (CStarMatrix.ofMatrix.symm F *
    (block D j k - block E j k)) = _
  rw [Matrix.mul_sub, Matrix.trace_sub]
  rfl

private theorem slice_expansion (D : Matrix (A × B) (A × B) ℂ)
    (F : Matrix A A ℂ) : sliceLinear D (CStarMatrix.ofMatrix F) =
      ∑ a : A, ∑ b : A, F a b •
        CStarMatrix.ofMatrix (D.submatrix (fun j => (b, j)) (fun k => (a, k))) := by
  apply CStarMatrix.ext
  intro j k
  change (∑ a : A, ∑ b : A, F a b * D (b, j) (a, k)) =
    (∑ a : A, ∑ b : A, F a b •
      CStarMatrix.ofMatrix (D.submatrix (fun j => (b, j)) (fun k => (a, k)))) j k
  simp only [cstar_sum_entry, CStarMatrix.smul_apply,
    CStarMatrix.ofMatrix_apply, Matrix.submatrix_apply, smul_eq_mul]

theorem slice_reference (T : QuantumChannel B C)
    (D : Matrix (A × B) (A × B) ℂ) (F : Matrix A A ℂ) :
    sliceLinear (referenceRaw T D) (CStarMatrix.ofMatrix F) =
      T.toCompletelyPositiveMap (sliceLinear D (CStarMatrix.ofMatrix F)) := by
  rw [slice_expansion D F]
  simp only [map_sum, map_smul]
  apply CStarMatrix.ext
  intro u v
  change (∑ a : A, ∑ b : A, F a b *
    T.toCompletelyPositiveMap
      (CStarMatrix.ofMatrix (D.submatrix (fun j => (b, j)) (fun k => (a, k)))) u v) =
    (∑ a : A, ∑ b : A, F a b • T.toCompletelyPositiveMap
      (CStarMatrix.ofMatrix (D.submatrix (fun j => (b, j)) (fun k => (a, k))))) u v
  simp only [cstar_sum_entry, CStarMatrix.smul_apply, smul_eq_mul]

private theorem referenceRaw_conjugate (U : Matrix.unitaryGroup B ℂ)
    (D : Matrix (A × B) (A × B) ℂ) :
    referenceRaw (conjugateChannel U) D =
      ((1 : Matrix A A ℂ) ⊗ₖ U.val) * D * ((1 : Matrix A A ℂ) ⊗ₖ U.val)ᴴ := by
  ext ⟨a,j⟩ ⟨b,k⟩
  exact (congrFun (congrFun (tensor_conjugate_block U.val D a b) j) k).symm

private theorem centered_conjugate (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (P : DensityState (A × Fin 2)) :
    centered (conjugateState (tensorUnitary 1 (star U)) P) =
      ((1 : Matrix A A ℂ) ⊗ₖ U.valᴴ) * centered P *
        ((1 : Matrix A A ℂ) ⊗ₖ U.valᴴ)ᴴ := by
  unfold centered
  rw [marginalRight_conjugate, marginalLeft_conjugate,
    productState_conjugate, conjugateState_value, conjugateState_value]
  change ((1 : Matrix A A ℂ) ⊗ₖ U.valᴴ) * CStarMatrix.ofMatrix.symm P.1 *
      ((1 : Matrix A A ℂ) ⊗ₖ U.valᴴ)ᴴ -
    ((1 : Matrix A A ℂ) ⊗ₖ U.valᴴ) *
      CStarMatrix.ofMatrix.symm (productState (marginalRight P) (marginalLeft P)).1 *
        ((1 : Matrix A A ℂ) ⊗ₖ U.valᴴ)ᴴ = _
  rw [Matrix.mul_sub, Matrix.sub_mul]

theorem slice_centered_conjugate (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (P : DensityState (A × Fin 2)) (F : CStarMatrix A A ℂ) :
    sliceLinear (centered (conjugateState (tensorUnitary 1 (star U)) P)) F =
      conjugateAlg (star U) (sliceLinear (centered P) F) := by
  rw [centered_conjugate]
  have hr := referenceRaw_conjugate (A := A) (star U) (centered P)
  simp only [Unitary.coe_star, Matrix.star_eq_conjTranspose] at hr
  rw [← hr]
  exact slice_reference (conjugateChannel (star U)) (centered P) (CStarMatrix.ofMatrix.symm F)

/-- The state, its actual marginals, the channel and its actual recovered state
are transported together. The half trace distance, every centered slice norm,
and the ordinary four-entropy conditional mutual information are preserved. -/
theorem actual_B_unitary_transport (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (rho : DensityState (A × (Fin 2 × C)))
    (T : QuantumChannel (Fin 2) (Fin 2 × C)) :
    let P := marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rho)
    let PU := conjugateState (tensorUnitary 1 (star U)) P
    let rhoU := localBState U rho
    let TU := localBChannel U T
    marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rhoU) = PU ∧
    referenceState TU PU = localBState U (referenceState T P) ∧
    marginalLeft PU = conjugateState (star U) (marginalLeft P) ∧
    (∀ F : CStarMatrix A A ℂ,
      sliceLinear (centered PU) F = conjugateAlg (star U) (sliceLinear (centered P) F) ∧
      ‖sliceLinear (centered PU) F‖ = ‖sliceLinear (centered P) F‖) ∧
    traceDistance rhoU (referenceState TU PU) = traceDistance rho (referenceState T P) ∧
    qcmi (D5.S3.Quantum.Foundation.FiniteDensityPurification.toMState rhoU) =
      qcmi (D5.S3.Quantum.Foundation.FiniteDensityPurification.toMState rho) ∧
    (∀ sigma : DensityState (A × (Fin 2 × C)),
      traceDistance rho (localBState (star U) sigma) = traceDistance rhoU sigma ∧
      qcmi (D5.S3.Quantum.Foundation.FiniteDensityPurification.toMState
        (localBState (star U) sigma)) =
        qcmi (D5.S3.Quantum.Foundation.FiniteDensityPurification.toMState sigma)) := by
  dsimp only
  refine ⟨localBState_AB U rho, localBChannel_reference U T _,
    marginalLeft_conjugate 1 (star U) _, ?_, ?_, qcmi_localBState U rho, ?_⟩
  · intro F
    refine ⟨slice_centered_conjugate U _ F, ?_⟩
    rw [slice_centered_conjugate, StarAlgEquiv.norm_map]
  · rw [localBChannel_reference]
    exact traceDistance_conjugateState _ _ _
  · intro sigma
    refine ⟨?_, qcmi_localBState (star U) sigma⟩
    have h := traceDistance_conjugateState
      (tensorUnitary (1 : Matrix.unitaryGroup A ℂ)
        (tensorUnitary (star U) (1 : Matrix.unitaryGroup C ℂ)))
      rho (localBState (star U) sigma)
    change traceDistance (localBState U rho)
      (localBState U (localBState (star U) sigma)) = _ at h
    rw [show localBState U (localBState (star U) sigma) = sigma from
      by simpa only [star_star] using localBState_inverse (star U) sigma] at h
    exact h.symm

end PhysicalRepair

end D5.S3.Quantum.Recovery.QubitResidualRounding
