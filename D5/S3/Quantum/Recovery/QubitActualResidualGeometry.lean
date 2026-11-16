/- GID: D5/S3/Quantum/Recovery/QubitActualResidualGeometry
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/QubitActualResidualGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual marginal residual geometry and centered product repair. -/

import D5.S3.Quantum.Recovery.QubitCenteredTransport


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

section PhysicalRepair

variable {A B C : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]


private def partialTraceRightLinear :
    Matrix (A × B) (A × B) ℂ →ₗ[ℂ] Matrix A A ℂ where
  toFun := partialTraceRight
  map_add' := partialTraceRight_add
  map_smul' z D := by ext a b; simp [partialTraceRight, Finset.mul_sum]

theorem partialTraceRight_contract (D : Matrix (A × B) (A × B) ℂ)
    (hD : D.IsHermitian) : traceNorm (partialTraceRight D) ≤ traceNorm D := by
  apply D5.S3.Quantum.Divergence.FaithfulConditionalGap.positive_trace_contraction
    partialTraceRightLinear _ _ D hD
  · intro X hX
    exact (partialTraceRight_posSemidef (Matrix.nonneg_iff_posSemidef.mp hX)).nonneg
  · exact trace_partialTraceRight

private def partialTraceLeftLinear :
    Matrix (A × B) (A × B) ℂ →ₗ[ℂ] Matrix B B ℂ where
  toFun := partialTraceLeft
  map_add' := partialTraceLeft_add
  map_smul' z D := by ext a b; simp [partialTraceLeft, Finset.mul_sum]

private theorem partialTraceLeft_contract (D : Matrix (A × B) (A × B) ℂ)
    (hD : D.IsHermitian) : traceNorm (partialTraceLeft D) ≤ traceNorm D := by
  apply D5.S3.Quantum.Divergence.FaithfulConditionalGap.positive_trace_contraction
    partialTraceLeftLinear _ _ D hD
  · intro X hX
    exact (partialTraceLeft_posSemidef (Matrix.nonneg_iff_posSemidef.mp hX)).nonneg
  · exact trace_partialTraceLeft

private def tensorLeft : Matrix A A ℂ →⋆ₐ[ℂ] Matrix (A × B) (A × B) ℂ where
  toFun F := F ⊗ₖ (1 : Matrix B B ℂ)
  map_one' := Matrix.one_kronecker_one
  map_mul' F G := by rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  map_zero' := Matrix.zero_kronecker _
  map_add' F G := Matrix.add_kronecker _ _ _
  commutes' z := by simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_kronecker]
  map_star' F := by simp only [star, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

def tensorRight : Matrix B B ℂ →⋆ₐ[ℂ] Matrix (A × B) (A × B) ℂ where
  toFun F := (1 : Matrix A A ℂ) ⊗ₖ F
  map_one' := Matrix.one_kronecker_one
  map_mul' F G := by rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  map_zero' := Matrix.kronecker_zero _
  map_add' F G := Matrix.kronecker_add _ _ _
  commutes' z := by simp [Algebra.algebraMap_eq_smul_one, Matrix.kronecker_smul]
  map_star' F := by simp only [star, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

private theorem tensor_operatorNorm_le (F : Matrix A A ℂ) (G : Matrix B B ℂ) :
    ‖F ⊗ₖ G‖ ≤ ‖F‖ * ‖G‖ := by
  have he : F ⊗ₖ G = tensorLeft (B := B) F * tensorRight (A := A) G := by
    change F ⊗ₖ G = (F ⊗ₖ 1) * (1 ⊗ₖ G)
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  rw [he]
  exact (norm_mul_le _ _).trans
    (mul_le_mul (NonUnitalStarAlgHom.norm_apply_le tensorLeft F)
      (NonUnitalStarAlgHom.norm_apply_le tensorRight G) (norm_nonneg _) (norm_nonneg _))

private theorem slice_hermitian (D : Matrix (A × B) (A × B) ℂ)
    (hD : D.IsHermitian) (F : Matrix A A ℂ) (hF : F.IsHermitian) :
    (CStarMatrix.ofMatrix.symm (sliceLinear D (CStarMatrix.ofMatrix F))).IsHermitian := by
  have hb (j k : B) : (block D j k)ᴴ = block D k j := by
    ext a b
    exact congrFun (congrFun hD.eq (a, k)) (b, j)
  ext j k
  change star (Matrix.trace (F * block D k j)) = Matrix.trace (F * block D j k)
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hF.eq, hb,
    Matrix.trace_mul_comm]

private theorem slice_trace_zero (P : DensityState (A × Fin 2))
    (F : Matrix A A ℂ) :
    Matrix.trace (CStarMatrix.ofMatrix.symm (sliceLinear (centered P)
      (CStarMatrix.ofMatrix F))) = 0 := by
  have hz := (centered_marginals_zero P).2
  have he : block (centered P) 0 0 + block (centered P) 1 1 = 0 := by
    ext a b
    simpa only [partialTraceRight, Fin.sum_univ_two, block,
      Matrix.add_apply, Matrix.submatrix_apply, Matrix.zero_apply] using
      congrFun (congrFun hz a) b
  rw [Matrix.trace, Fin.sum_univ_two]
  change Matrix.trace (F * block (centered P) 0 0) +
    Matrix.trace (F * block (centered P) 1 1) = 0
  rw [← Matrix.trace_add, ← Matrix.mul_add, he, Matrix.mul_zero, Matrix.trace_zero]

private theorem slice_tensor_pairing (D : Matrix (A × B) (A × B) ℂ)
    (F : Matrix A A ℂ) (G : Matrix B B ℂ) :
    Matrix.trace ((F ⊗ₖ G) * D) =
      Matrix.trace (G * CStarMatrix.ofMatrix.symm (sliceLinear D (CStarMatrix.ofMatrix F))) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply]
  change (∑ a : A, ∑ j : B, ∑ b : A, ∑ k : B,
    F a b * G j k * D (b, k) (a, j)) =
    ∑ j : B, ∑ k : B, G j k *
      ∑ a : A, ∑ b : A, F a b * D (b, k) (a, j)
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]
  calc
    _ = ∑ b : A, ∑ k : B, ∑ a : A,
        G j k * (F a b * D (b, k) (a, j)) := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = _ := by rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro k hk; rw [Finset.sum_comm]

private theorem slice_traceNorm_contract (D : Matrix (A × B) (A × B) ℂ)
    (hD : D.IsHermitian) (F : Matrix A A ℂ) (hF : F.IsHermitian) (hn : ‖F‖ ≤ 1) :
    traceNorm (CStarMatrix.ofMatrix.symm (sliceLinear D (CStarMatrix.ofMatrix F))) ≤
      traceNorm D := by
  apply D5.S3.Quantum.Foundation.FiniteHermitianTraceDuality.hermitian_traceNorm_le_tests
    _ (slice_hermitian D hD F hF)
  intro G hG hgn
  rw [← slice_tensor_pairing]
  have hc : ‖F ⊗ₖ G‖ ≤ 1 :=
    (tensor_operatorNorm_le F G).trans (by nlinarith [norm_nonneg F, norm_nonneg G])
  exact (D5.S3.Quantum.Matrix.UniformVarianceTraceBound.re_trace_mul_le _ D).trans
    (mul_le_of_le_one_left (traceNorm_nonneg D) hc)

private def abTrace : Matrix (A × (B × C)) (A × (B × C)) ℂ →ₗ[ℂ]
    Matrix (A × B) (A × B) ℂ where
  toFun D := partialTraceRight (D.submatrix (Equiv.prodAssoc A B C) (Equiv.prodAssoc A B C))
  map_add' D E := by ext a b; simp [partialTraceRight, Finset.sum_add_distrib]
  map_smul' z D := by ext a b; simp [partialTraceRight, Finset.mul_sum]

private theorem abTrace_contract (D : Matrix (A × (B × C)) (A × (B × C)) ℂ)
    (hD : D.IsHermitian) : traceNorm (abTrace D) ≤ traceNorm D := by
  have h := partialTraceRight_contract
    (D.submatrix (Equiv.prodAssoc A B C) (Equiv.prodAssoc A B C))
    (hD.submatrix _)
  rw [D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance.traceNorm_submatrix_equiv] at h
  exact h

private theorem slice_abTrace (D : Matrix (A × (B × C)) (A × (B × C)) ℂ)
    (F : Matrix A A ℂ) :
    sliceLinear (abTrace D) (CStarMatrix.ofMatrix F) =
      CStarMatrix.ofMatrix (partialTraceRight
        (CStarMatrix.ofMatrix.symm (sliceLinear D (CStarMatrix.ofMatrix F)))) := by
  apply CStarMatrix.ext
  intro j k
  change (∑ a : A, ∑ b : A, F a b * ∑ c : C, D (b, (j, c)) (a, (k, c))) =
    ∑ c : C, ∑ a : A, ∑ b : A, F a b * D (b, (j, c)) (a, (k, c))
  simp_rw [Finset.mul_sum]
  calc
    _ = ∑ a : A, ∑ c : C, ∑ b : A, F a b * D (b, (j, c)) (a, (k, c)) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

def reducedAction (T : QuantumChannel B (B × C)) :
    CStarMatrix B B ℂ →ₗ[ℂ] CStarMatrix B B ℂ :=
  CStarMatrix.ofMatrixₗ.toLinearMap.comp
    (partialTraceRightLinear.comp
      (CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp T.toCompletelyPositiveMap.toLinearMap))

private def reducedReference (T : QuantumChannel B (B × C)) :
    Matrix (A × B) (A × B) ℂ →ₗ[ℂ] Matrix (A × B) (A × B) ℂ :=
  abTrace.comp (referenceRaw T)

private theorem slice_reducedReference (T : QuantumChannel B (B × C))
    (D : Matrix (A × B) (A × B) ℂ) (F : Matrix A A ℂ) :
    sliceLinear (reducedReference T D) (CStarMatrix.ofMatrix F) =
      reducedAction T (sliceLinear D (CStarMatrix.ofMatrix F)) := by
  change sliceLinear (abTrace (referenceRaw T D)) (CStarMatrix.ofMatrix F) = _
  rw [slice_abTrace, slice_reference]
  rfl

private theorem actual_AB_residual (rho : DensityState (A × (B × C)))
    (T : QuantumChannel B (B × C)) :
    let P := marginalRight (relabelState (Equiv.prodAssoc A B C) rho)
    traceNorm (CStarMatrix.ofMatrix.symm P.1 -
      reducedReference T (CStarMatrix.ofMatrix.symm P.1)) ≤
      2 * traceDistance rho (referenceState T P) := by
  dsimp only
  let P := marginalRight (relabelState (Equiv.prodAssoc A B C) rho)
  let tau := referenceState T P
  have hc := abTrace_contract
    (CStarMatrix.ofMatrix.symm rho.1 - CStarMatrix.ofMatrix.symm tau.1)
    ((density_posSemidef rho).isHermitian.sub (density_posSemidef tau).isHermitian)
  rw [map_sub] at hc
  change traceNorm (CStarMatrix.ofMatrix.symm P.1 -
    reducedReference T (CStarMatrix.ofMatrix.symm P.1)) ≤ _ at hc
  change traceNorm _ ≤ 2 * (traceNorm _ / 2)
  linarith

private theorem slice_one (D : Matrix (A × B) (A × B) ℂ) :
    sliceLinear D 1 = CStarMatrix.ofMatrix (partialTraceLeft D) := by
  apply CStarMatrix.ext
  intro j k
  change (∑ a : A, ∑ b : A, (1 : Matrix A A ℂ) a b * D (b, j) (a, k)) =
    ∑ a : A, D (a, j) (a, k)
  simp [Matrix.one_apply]

private theorem reducedReference_left (T : QuantumChannel B (B × C))
    (D : Matrix (A × B) (A × B) ℂ) :
    CStarMatrix.ofMatrix (partialTraceLeft (reducedReference T D)) =
      reducedAction T (CStarMatrix.ofMatrix (partialTraceLeft D)) := by
  have h := slice_reducedReference T D (1 : Matrix A A ℂ)
  simpa only [CStarMatrix.ofMatrix_eq_ofMatrixStarAlgEquiv, map_one, slice_one] using h

theorem actual_B_residual (rho : DensityState (A × (B × C)))
    (T : QuantumChannel B (B × C)) :
    let P := marginalRight (relabelState (Equiv.prodAssoc A B C) rho)
    traceNorm (CStarMatrix.ofMatrix.symm (marginalLeft P).1 -
      CStarMatrix.ofMatrix.symm (reducedAction T (marginalLeft P).1)) ≤
      2 * traceDistance rho (referenceState T P) := by
  dsimp only
  let P := marginalRight (relabelState (Equiv.prodAssoc A B C) rho)
  let tau := referenceState T P
  let Q := marginalRight (relabelState (Equiv.prodAssoc A B C) tau)
  have hab := actual_AB_residual rho T
  have hc := partialTraceLeft_contract
    (CStarMatrix.ofMatrix.symm P.1 - CStarMatrix.ofMatrix.symm Q.1)
    ((density_posSemidef P).isHermitian.sub (density_posSemidef Q).isHermitian)
  have he := reducedReference_left T (CStarMatrix.ofMatrix.symm P.1)
  have hq : CStarMatrix.ofMatrix.symm Q.1 = reducedReference T (CStarMatrix.ofMatrix.symm P.1) := rfl
  have ht : partialTraceLeft
      (CStarMatrix.ofMatrix.symm P.1 - CStarMatrix.ofMatrix.symm Q.1) =
      CStarMatrix.ofMatrix.symm (marginalLeft P).1 -
        CStarMatrix.ofMatrix.symm (reducedAction T (marginalLeft P).1) := by
    change partialTraceLeftLinear (_ - _) = _
    rw [map_sub, hq]
    have he' := congrArg CStarMatrix.ofMatrix.symm he
    change partialTraceLeft _ = _ at he'
    change partialTraceLeft _ - partialTraceLeft _ = _
    rw [he']
    rfl
  rw [ht] at hc
  exact hc.trans hab

private theorem reducedReference_product (T : QuantumChannel B (B × C))
    (a : DensityState A) (b : DensityState B) :
    reducedReference T (CStarMatrix.ofMatrix.symm (productState a b).1) =
      CStarMatrix.ofMatrix.symm a.1 ⊗ₖ CStarMatrix.ofMatrix.symm (reducedAction T b.1) := by
  have h := referenceState_product T a b
  have he := congrArg (fun rho : DensityState (A × (B × C)) =>
    abTrace (CStarMatrix.ofMatrix.symm rho.1)) h
  change reducedReference T (CStarMatrix.ofMatrix.symm (productState a b).1) = _ at he
  rw [he]
  ext ⟨i, j⟩ ⟨k, l⟩
  change (∑ c : C, a.1 i k * T.toCompletelyPositiveMap b.1 (j, c) (l, c)) =
    a.1 i k * ∑ c : C, T.toCompletelyPositiveMap b.1 (j, c) (l, c)
  exact (Finset.mul_sum _ _ _).symm

/-- Every Hermitian contraction on A inherits approximate fixedness under the
actual reduced recovery channel, with the half trace-distance convention. -/
theorem all_centered_tests_residual (rho : DensityState (A × (Fin 2 × C)))
    (T : QuantumChannel (Fin 2) (Fin 2 × C))
    (F : Matrix A A ℂ) (hF : F.IsHermitian) (hn : ‖F‖ ≤ 1) :
    let P := marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rho)
    let K := sliceLinear (centered P) (CStarMatrix.ofMatrix F)
    traceNorm (CStarMatrix.ofMatrix.symm (reducedAction T K - K)) ≤
      4 * traceDistance rho (referenceState T P) := by
  dsimp only
  let P := marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rho)
  let Q := marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) (referenceState T P))
  let a := marginalRight P
  let b := marginalLeft P
  let D := CStarMatrix.ofMatrix.symm P.1 - CStarMatrix.ofMatrix.symm Q.1
  let E := CStarMatrix.ofMatrix.symm b.1 - CStarMatrix.ofMatrix.symm (reducedAction T b.1)
  have hD : D.IsHermitian := (density_posSemidef P).isHermitian.sub
    (density_posSemidef Q).isHermitian
  have hE : E.IsHermitian := by
    have he := reducedReference_left T (CStarMatrix.ofMatrix.symm P.1)
    have he' := congrArg CStarMatrix.ofMatrix.symm he
    change CStarMatrix.ofMatrix.symm (marginalLeft Q).1 =
      CStarMatrix.ofMatrix.symm (reducedAction T b.1) at he'
    rw [show E = CStarMatrix.ofMatrix.symm b.1 -
      CStarMatrix.ofMatrix.symm (marginalLeft Q).1 from congrArg
        (fun X => CStarMatrix.ofMatrix.symm b.1 - X) he'.symm]
    exact (density_posSemidef b).isHermitian.sub (density_posSemidef (marginalLeft Q)).isHermitian
  have hd := actual_AB_residual rho T
  have hb := actual_B_residual rho T
  have he : centered P - reducedReference T (centered P) =
      D - (CStarMatrix.ofMatrix.symm a.1 ⊗ₖ E) := by
    unfold centered
    rw [map_sub, reducedReference_product]
    change (_ - _) - (_ - _) = _ - _
    ext ⟨i, j⟩ ⟨k, l⟩
    change (P.1 (i, j) (k, l) - a.1 i k * b.1 j l) -
      (Q.1 (i, j) (k, l) - a.1 i k * reducedAction T b.1 j l) =
      (P.1 (i, j) (k, l) - Q.1 (i, j) (k, l)) -
        a.1 i k * (b.1 j l - reducedAction T b.1 j l)
    ring
  have hs := slice_traceNorm_contract D hD F hF hn
  have ht := slice_traceNorm_contract (CStarMatrix.ofMatrix.symm a.1 ⊗ₖ E)
    (isHermitian_kronecker (density_posSemidef a).isHermitian hE) F hF hn
  have ha : traceNorm (CStarMatrix.ofMatrix.symm a.1) = 1 := by
    have h := traceNorm_of_posSemidef (density_posSemidef a)
    have hr := congrArg Complex.re h
    change traceNorm (CStarMatrix.ofMatrix.symm a.1) =
      (Matrix.trace (CStarMatrix.ofMatrix.symm a.1)).re at hr
    exact hr.trans (congrArg Complex.re a.2.2)
  rw [traceNorm_tensor, ha, one_mul] at ht
  have hpair := traceNorm_add_le
    (CStarMatrix.ofMatrix.symm (sliceLinear D (CStarMatrix.ofMatrix F)))
    (-CStarMatrix.ofMatrix.symm (sliceLinear (CStarMatrix.ofMatrix.symm a.1 ⊗ₖ E)
      (CStarMatrix.ofMatrix F)))
  rw [traceNorm_neg] at hpair
  have hk : CStarMatrix.ofMatrix.symm
      (reducedAction T (sliceLinear (centered P) (CStarMatrix.ofMatrix F)) -
        sliceLinear (centered P) (CStarMatrix.ofMatrix F)) =
      -(CStarMatrix.ofMatrix.symm (sliceLinear D (CStarMatrix.ofMatrix F)) -
        CStarMatrix.ofMatrix.symm (sliceLinear (CStarMatrix.ofMatrix.symm a.1 ⊗ₖ E)
          (CStarMatrix.ofMatrix F))) := by
    rw [← slice_reducedReference]
    have hh := congrArg (fun X => sliceLinear X (CStarMatrix.ofMatrix F)) he
    rw [slice_sub, slice_sub] at hh
    have hh' := congrArg CStarMatrix.ofMatrix.symm hh
    have hhentry := fun j k => congrArg (fun M : CStarMatrix (Fin 2) (Fin 2) ℂ => M j k) hh
    ext j k
    have h := hhentry j k
    change sliceLinear (centered P) (CStarMatrix.ofMatrix F) j k -
      sliceLinear (reducedReference T (centered P)) (CStarMatrix.ofMatrix F) j k =
      sliceLinear D (CStarMatrix.ofMatrix F) j k -
        sliceLinear (CStarMatrix.ofMatrix.symm a.1 ⊗ₖ E) (CStarMatrix.ofMatrix F) j k at h
    change sliceLinear (reducedReference T (centered P)) (CStarMatrix.ofMatrix F) j k -
      sliceLinear (centered P) (CStarMatrix.ofMatrix F) j k =
      -(sliceLinear D (CStarMatrix.ofMatrix F) j k -
        sliceLinear (CStarMatrix.ofMatrix.symm a.1 ⊗ₖ E) (CStarMatrix.ofMatrix F) j k)
    linear_combination -h
  rw [hk, traceNorm_neg, sub_eq_add_neg]
  change traceNorm D ≤ _ at hd
  change traceNorm E ≤ _ at hb
  linarith

private theorem traceless_qubit_diagonalization
    (K : Matrix (Fin 2) (Fin 2) ℂ) (hK : K.IsHermitian) (ht : Matrix.trace K = 0) :
    ∃ U : Matrix.unitaryGroup (Fin 2) ℂ,
      U.valᴴ * K * U.val = Matrix.diagonal ![(‖K‖ : ℂ), -(‖K‖ : ℂ)] := by
  let V := hK.eigenvectorUnitary
  let d := hK.eigenvalues
  have hsum : d 0 + d 1 = 0 := by
    have hh := congrArg RCLike.re hK.trace_eq_sum_eigenvalues
    rw [ht] at hh
    simpa only [Fin.sum_univ_two, map_add, RCLike.ofReal_re,
      map_zero] using hh.symm
  have hd : d 1 = -d 0 := by linarith
  have hv : V.valᴴ * K * V.val = Matrix.diagonal (fun i => (d i : ℂ)) := by
    simpa only [V, d, Function.comp_def, RCLike.ofReal_eq_complex_ofReal,
      Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose] using
      hK.conjStarAlgAut_star_eigenvectorUnitary
  have hnorm : ‖K‖ = |d 0| := by
    have he : ‖K‖ = ‖fun i => (d i : ℂ)‖ := by
      conv_lhs => rw [hK.spectral_theorem]
      simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
        CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
        Matrix.l2_opNorm_diagonal]
      rfl
    rw [he]
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (abs_nonneg (d 0))).mpr
      intro i
      fin_cases i <;> simp [hd, Complex.norm_real, Real.norm_eq_abs]
    · simpa only [Complex.norm_real, Real.norm_eq_abs] using
        (norm_le_pi_norm (fun i => (d i : ℂ)) (0 : Fin 2))
  by_cases hp : 0 ≤ d 0
  · refine ⟨V, hv.trans ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal_apply, hnorm, abs_of_nonneg hp, hd]
  · have hn : d 0 < 0 := lt_of_not_ge hp
    let S : Matrix.unitaryGroup (Fin 2) ℂ := ⟨pauli 0, by
      apply Matrix.mem_unitaryGroup_iff'.mpr
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [pauli,
          D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix,
          D5.S3.Quantum.FiniteDimensional.qubitX, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.conjTranspose_apply]⟩
    refine ⟨V * S, ?_⟩
    change (V.val * S.val)ᴴ * K * (V.val * S.val) = _
    rw [Matrix.conjTranspose_mul]
    have he : S.valᴴ * V.valᴴ * K * (V.val * S.val) =
        S.valᴴ * (V.valᴴ * K * V.val) * S.val := by simp only [Matrix.mul_assoc]
    rw [he, hv]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [S, pauli,
        D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix,
        D5.S3.Quantum.FiniteDimensional.qubitX, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply, Matrix.diagonal_apply, hnorm, abs_of_neg hn, hd]

/-- Rotate the same input and output qubit coordinate to the eigenbasis of
its nonzero test, retaining the full actual physical isometry. -/
theorem diagonalized_residual_geometry {E : Type*} [Fintype E] [DecidableEq E]
    (W : Matrix (Fin 2 × E) (Fin 2) ℂ) (hW : Wᴴ * W = 1)
    (K : Matrix (Fin 2) (Fin 2) ℂ) (hK : K.IsHermitian) (ht : Matrix.trace K = 0)
    (hx : 0 < ‖K‖) (e : ℝ) (he : traceNorm (reduced W K - K) ≤ e) :
    ∃ (U : Matrix.unitaryGroup (Fin 2) ℂ)
      (V : Matrix (Fin 2 × E) (Fin 2) ℂ),
      Vᴴ * V = 1 ∧
      U.valᴴ * K * U.val = Matrix.diagonal ![(‖K‖ : ℂ), -(‖K‖ : ℂ)] ∧
      (∀ M : Matrix (Fin 2) (Fin 2) ℂ,
        reduced V M = U.valᴴ * reduced W (U.val * M * U.valᴴ) * U.val) ∧
      ‖column V 1 0‖ ^ 2 + ‖column V 0 1‖ ^ 2 ≤ (e / ‖K‖) / 2 ∧
      ‖inner ℂ (column V 1 0) (column V 0 0) -
        inner ℂ (column V 1 1) (column V 0 1)‖ ≤ (e / ‖K‖) / 2 := by
  obtain ⟨U, hu⟩ := traceless_qubit_diagonalization K hK ht
  obtain ⟨V, hv, hcov⟩ := rotated_dilation W hW U
  have huU : U.val * U.valᴴ = 1 := Unitary.coe_mul_star_self U
  refine ⟨U, V, hv, hu, hcov, ?_⟩
  let Z : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1, -1]
  have hku : U.valᴴ * K * U.val = (‖K‖ : ℂ) • Z := by
    rw [hu]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Z]
  have hk : U.val * ((‖K‖ : ℂ) • Z) * U.valᴴ = K := by
    rw [← hku]
    calc
      _ = (U.val * U.valᴴ) * K * (U.val * U.valᴴ) := by simp [Matrix.mul_assoc]
      _ = K := by rw [huU]; simp
  have hs : (‖K‖ : ℂ) • (reduced V Z - Z) =
      U.valᴴ * (reduced W K - K) * U.val := by
    have hr : reduced V ((‖K‖ : ℂ) • Z) = (‖K‖ : ℂ) • reduced V Z := by
      ext i j
      simp [reduced, partialTraceRight, Matrix.mul_smul, Matrix.smul_mul,
        Finset.mul_sum]
    rw [smul_sub, ← hr, hcov, hk, Matrix.mul_sub, Matrix.sub_mul, hku]
  have htN : ‖K‖ * traceNorm (reduced V Z - Z) ≤ e := by
    rw [← D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.traceNorm_smul_nonneg
      _ ‖K‖ (norm_nonneg _), hs]
    have hi :=
      D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.traceNorm_isometry
        U.valᴴ (by simpa only [Matrix.conjTranspose_conjTranspose] using huU) (reduced W K - K)
    simpa only [Matrix.conjTranspose_conjTranspose] using hi.le.trans he
  apply diagonal_residual_controls_coefficients V hv (e / ‖K‖)
  exact (le_div_iff₀ hx).mpr (by simpa [mul_comm] using htN)

/-- Hermitian testing of the complex off-diagonal block retains the factor
of two in complex trace duality. The isometry and all tests refer to the same
centered matrix. -/
theorem complex_block_bound_of_diagonal_geometry
    {E : Type*} [Fintype E]
    (P : DensityState (A × Fin 2))
    (W : Matrix (Fin 2 × E) (Fin 2) ℂ) (hW : Wᴴ * W = 1)
    (x r : ℝ) (hx : 0 < x) (hr : 0 ≤ r)
    (hmax : ∀ F : CStarMatrix A A ℂ, IsSelfAdjoint F → ‖F‖ ≤ 1 →
      ‖sliceLinear (centered P) F‖ ≤ x)
    (hres : ∀ F : Matrix A A ℂ, F.IsHermitian → ‖F‖ ≤ 1 →
      traceNorm (reduced W (CStarMatrix.ofMatrix.symm
        (sliceLinear (centered P) (CStarMatrix.ofMatrix F))) -
        CStarMatrix.ofMatrix.symm (sliceLinear (centered P) (CStarMatrix.ofMatrix F))) ≤ 4 * r)
    (hflip : ‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2 ≤ 2 * r / x)
    (hdiff : ‖inner ℂ (column W 1 0) (column W 0 0) -
      inner ℂ (column W 1 1) (column W 0 1)‖ ≤ 2 * r / x)
    (hg : 0 < ‖1 - inner ℂ (column W 1 1) (column W 0 0)‖) :
    traceNorm (block (centered P) 0 1) ≤
      16 * r / ‖1 - inner ℂ (column W 1 1) (column W 0 0)‖ := by
  have hdual : traceNorm (block (centered P) 0 1) ≤
      2 * (8 * r / ‖1 - inner ℂ (column W 1 1) (column W 0 0)‖) := by
    apply D5.S3.Quantum.Foundation.FiniteHermitianTraceDuality.complex_traceNorm_le_twice_tests
    intro F hF hFn
    let K := CStarMatrix.ofMatrix.symm (sliceLinear (centered P) (CStarMatrix.ofMatrix F))
    have hfc : IsSelfAdjoint (CStarMatrix.ofMatrix F) :=
      (show IsSelfAdjoint F from hF).map CStarMatrix.ofMatrixStarAlgEquiv
    have hfn : ‖CStarMatrix.ofMatrix F‖ ≤ 1 := by
      change ‖CStarMatrix.ofMatrixStarAlgEquiv F‖ ≤ 1
      rw [StarAlgEquiv.norm_map]
      exact hFn
    have hkn : ‖K‖ ≤ x := by
      have hn : ‖K‖ = ‖sliceLinear (centered P) (CStarMatrix.ofMatrix F)‖ := by
        change ‖CStarMatrix.ofMatrixStarAlgEquiv.symm _‖ = _
        exact StarAlgEquiv.norm_map _ _
      rw [hn]
      exact hmax _ hfc hfn
    have hk := offDiagonal_gap_bound W hW K
      (slice_hermitian _ (centered_hermitian P) F hF) (slice_trace_zero P F)
      x (4 * r) (2 * r / x) (2 * r / x) hkn (hres F hF hFn) hflip hdiff
    have hs : ‖1 - inner ℂ (column W 1 1) (column W 0 0)‖ * ‖K 0 1‖ ≤ 8 * r := by
      have hd : x ≠ 0 := ne_of_gt hx
      have h1 : (2 * r / x) * x = 2 * r := by field_simp
      have h2 : ((2 * r / x) / 2) * x = r := by field_simp
      rw [h1, h2] at hk
      linarith
    change ‖K 0 1‖ ≤ _
    exact (le_div_iff₀ hg).mpr (by simpa [mul_comm] using hs)
  calc
    _ ≤ _ := hdual
    _ = _ := by ring

/-- The attained centered direction and the diagonal coefficient geometry
belong to one coherently transported physical state and channel. -/
theorem actual_diagonal_geometry {C : Type*} [Fintype C] [DecidableEq C]
    (rho : DensityState (A × (Fin 2 × C)))
    (T : QuantumChannel (Fin 2) (Fin 2 × C))
    (F : CStarMatrix A A ℂ) (hF : IsSelfAdjoint F) (hFn : ‖F‖ ≤ 1)
    (hmax : ∀ G : CStarMatrix A A ℂ, IsSelfAdjoint G → ‖G‖ ≤ 1 →
      ‖sliceLinear (centered
        (marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rho))) G‖ ≤
      ‖sliceLinear (centered
        (marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rho))) F‖)
    (hx : 0 < ‖sliceLinear (centered
      (marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rho))) F‖) :
    let P := marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rho)
    let x := ‖sliceLinear (centered P) F‖
    let r := traceDistance rho (referenceState T P)
    ∃ (U : Matrix.unitaryGroup (Fin 2) ℂ)
      (W : Matrix (Fin 2 × (C × ((Fin 2 × Fin (Fintype.card C)) × Fin 2))) (Fin 2) ℂ),
      Wᴴ * W = 1 ∧
      (∀ (M : Matrix (Fin 2) (Fin 2) ℂ) (j k : Fin 2) (c d : C),
        (∑ e : (Fin 2 × Fin (Fintype.card C)) × Fin 2,
          (W * M * Wᴴ) (j, (c, e)) (k, (d, e))) =
            CStarMatrix.ofMatrix.symm
              ((localBChannel U T).toCompletelyPositiveMap (CStarMatrix.ofMatrix M))
                (j, c) (k, d)) ∧
      let PU := marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) (localBState U rho))
      (∀ G : CStarMatrix A A ℂ, IsSelfAdjoint G → ‖G‖ ≤ 1 →
        ‖sliceLinear (centered PU) G‖ ≤ x) ∧
      (∀ G : Matrix A A ℂ, G.IsHermitian → ‖G‖ ≤ 1 →
        traceNorm (reduced W (CStarMatrix.ofMatrix.symm
          (sliceLinear (centered PU) (CStarMatrix.ofMatrix G))) -
          CStarMatrix.ofMatrix.symm (sliceLinear (centered PU) (CStarMatrix.ofMatrix G))) ≤
            4 * r) ∧
      ‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2 ≤ 2 * r / x ∧
      ‖inner ℂ (column W 1 0) (column W 0 0) -
        inner ℂ (column W 1 1) (column W 0 1)‖ ≤ 2 * r / x ∧
      (0 < ‖1 - inner ℂ (column W 1 1) (column W 0 0)‖ →
        traceNorm (block (centered PU) 0 1) ≤
          16 * r / ‖1 - inner ℂ (column W 1 1) (column W 0 0)‖) := by
  dsimp only
  let P := marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rho)
  let K := CStarMatrix.ofMatrix.symm (sliceLinear (centered P) F)
  let x := ‖sliceLinear (centered P) F‖
  let r := traceDistance rho (referenceState T P)
  have hFH : (CStarMatrix.ofMatrix.symm F).IsHermitian := by
    exact hF.map CStarMatrix.ofMatrixStarAlgEquiv.symm
  have hFN : ‖CStarMatrix.ofMatrix.symm F‖ ≤ 1 := by
    change ‖CStarMatrix.ofMatrixStarAlgEquiv.symm F‖ ≤ 1
    rw [StarAlgEquiv.norm_map]
    exact hFn
  have hkn : ‖K‖ = x := StarAlgEquiv.norm_map CStarMatrix.ofMatrixStarAlgEquiv.symm _
  have hkh : K.IsHermitian := slice_hermitian _ (centered_hermitian P)
    (CStarMatrix.ofMatrix.symm F) hFH
  have hkt : Matrix.trace K = 0 := slice_trace_zero P (CStarMatrix.ofMatrix.symm F)
  obtain ⟨W0, hw0, _, hr0⟩ := actual_dilation T
  have hres0 : traceNorm (reduced W0 K - K) ≤ 4 * r := by
    rw [hr0]
    exact all_centered_tests_residual rho T _ hFH hFN
  obtain ⟨U, _, _, hdiag, _, _, _⟩ := diagonalized_residual_geometry W0 hw0 K hkh hkt
    (by simpa only [hkn] using hx) (4 * r) hres0
  obtain ⟨W, hw, hout, hred⟩ := actual_dilation (localBChannel U T)
  let PU := marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) (localBState U rho))
  have hp : PU = conjugateState (tensorUnitary 1 (star U)) P := localBState_AB U rho
  have hru : traceDistance (localBState U rho)
      (referenceState (localBChannel U T) PU) = r := by
    rw [hp, localBChannel_reference]
    exact traceDistance_conjugateState _ _ _
  have hm : ∀ G : CStarMatrix A A ℂ, IsSelfAdjoint G → ‖G‖ ≤ 1 →
      ‖sliceLinear (centered PU) G‖ ≤ x := by
    intro G hG hn
    rw [hp, slice_centered_conjugate, StarAlgEquiv.norm_map]
    exact hmax G hG hn
  have hr : ∀ G : Matrix A A ℂ, G.IsHermitian → ‖G‖ ≤ 1 →
      traceNorm (reduced W (CStarMatrix.ofMatrix.symm
        (sliceLinear (centered PU) (CStarMatrix.ofMatrix G))) -
        CStarMatrix.ofMatrix.symm (sliceLinear (centered PU) (CStarMatrix.ofMatrix G))) ≤
          4 * r := by
    intro G hG hn
    rw [hred]
    exact (all_centered_tests_residual (localBState U rho) (localBChannel U T) G hG hn).trans_eq
      (by rw [hru])
  let Z : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1,-1]
  have hku : CStarMatrix.ofMatrix.symm (sliceLinear (centered PU) F) = (x : ℂ) • Z := by
    rw [hp, slice_centered_conjugate]
    simp only [conjugateAlg, StarAlgEquiv.trans_apply, Unitary.conjStarAlgAut_apply,
      Unitary.coe_star, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    change U.valᴴ * K * U.val = _
    rw [hdiag, hkn]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Z]
  have hscale : traceNorm (reduced W Z - Z) ≤ 4 * r / x := by
    have he := hr (CStarMatrix.ofMatrix.symm F) hFH hFN
    change traceNorm (reduced W (CStarMatrix.ofMatrix.symm (sliceLinear (centered PU) F)) -
      CStarMatrix.ofMatrix.symm (sliceLinear (centered PU) F)) ≤ _ at he
    rw [hku] at he
    have heq : reduced W ((x : ℂ) • Z) - (x : ℂ) • Z = (x : ℂ) • (reduced W Z - Z) := by
      ext i j
      simp [reduced, partialTraceRight, Matrix.mul_smul, Matrix.smul_mul,
        Finset.mul_sum, mul_sub]
    rw [heq, D5.S3.Quantum.Entanglement.ConicalDesignConcurrenceComparability.traceNorm_smul_nonneg
      _ x (le_of_lt hx)] at he
    exact (le_div_iff₀ hx).mpr (by simpa only [mul_comm] using he)
  obtain ⟨hflip, hdiff⟩ := diagonal_residual_controls_coefficients W hw (4 * r / x) hscale
  have hf' : ‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2 ≤ 2 * r / x := by
    convert hflip using 1 <;> ring
  have hd' : ‖inner ℂ (column W 1 0) (column W 0 0) -
      inner ℂ (column W 1 1) (column W 0 1)‖ ≤ 2 * r / x := by
    convert hdiff using 1 <;> ring
  refine ⟨U, W, hw, hout, hm, hr, hf', hd', ?_⟩
  intro hg
  exact complex_block_bound_of_diagonal_geometry PU W hw x r hx
    (traceDistance_nonneg _ _) hm hr hf' hd' hg

/-- A small centered correlation gives a product state on the actual system. -/
theorem product_repair_of_centered_correlation
    (rho : DensityState (A × (Fin 2 × C)))
    (T : QuantumChannel (Fin 2) (Fin 2 × C)) :
    let P := marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rho)
    ∃ F : CStarMatrix A A ℂ, IsSelfAdjoint F ∧ ‖F‖ ≤ 1 ∧
      (∀ G : CStarMatrix A A ℂ, IsSelfAdjoint G → ‖G‖ ≤ 1 →
        ‖sliceLinear (centered P) G‖ ≤ ‖sliceLinear (centered P) F‖) ∧
      ∃ sigma : DensityState (A × (Fin 2 × C)),
        qcmi (D5.S3.Quantum.Foundation.FiniteDensityPurification.toMState sigma) = 0 ∧
        traceDistance rho sigma ≤ traceDistance rho (referenceState T P) +
          3 * ‖sliceLinear (centered P) F‖ := by
  dsimp only
  let P := marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rho)
  obtain ⟨F, hf, hfn, hmax, hbound⟩ := attained_centered_traceNorm_bound P
  let sigma := productState (marginalRight P) (T.mapState (marginalLeft P))
  refine ⟨F, hf, hfn, hmax, sigma,
    D5.S3.Quantum.Information.StrongSubadditivity.MarkovConstructors.qcmi_product_left _ _, ?_⟩
  have hc := referenceState_contract T P
    (productState (marginalRight P) (marginalLeft P))
  rw [referenceState_product] at hc
  have hp : traceDistance P (productState (marginalRight P) (marginalLeft P)) ≤
      3 * ‖sliceLinear (centered P) F‖ := by
    change traceNorm (centered P) / 2 ≤ _
    linarith
  exact (traceDistance_triangle rho (referenceState T P) sigma).trans
    (add_le_add le_rfl (hc.trans hp))

end PhysicalRepair

end D5.S3.Quantum.Recovery.QubitResidualRounding
