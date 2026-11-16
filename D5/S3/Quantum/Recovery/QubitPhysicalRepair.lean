/- GID: D5/S3/Quantum/Recovery/QubitPhysicalRepair
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/QubitPhysicalRepair
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Normalized physical isometries and product or pointer repairs. -/

import D5.S3.Quantum.Recovery.QubitActualResidualGeometry

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


private theorem marginalBC_right_product (P : DensityState (A × B)) (gamma : DensityState C) :
    marginalLeft (relabelState (Equiv.prodAssoc A B C).symm (productState P gamma)) =
      productState (marginalLeft P) gamma := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  ext p q
  change (∑ a : A, P.1 (a, p.1) (a, q.1) * gamma.1 p.2 q.2) =
    (∑ a : A, P.1 (a, p.1) (a, q.1)) * gamma.1 p.2 q.2
  exact (Finset.sum_mul _ _ _).symm

private theorem marginalAB_right_product (P : DensityState (A × B)) (gamma : DensityState C) :
    marginalRight (relabelState (Equiv.prodAssoc A B C)
      (relabelState (Equiv.prodAssoc A B C).symm (productState P gamma))) = P := by
  have he : relabelState (Equiv.prodAssoc A B C)
      (relabelState (Equiv.prodAssoc A B C).symm (productState P gamma)) =
        productState P gamma := by
    apply Subtype.ext
    apply CStarMatrix.ofMatrix.symm.injective
    rfl
  rw [he, marginalRight_productState]

/-- A product across AB and C, expressed on the original associated ABC carrier. -/
theorem qcmi_product_right (P : DensityState (A × B)) (gamma : DensityState C) :
    qcmi (toMState (relabelState (Equiv.prodAssoc A B C).symm
      (productState P gamma))) = 0 := by
  rw [qcmi_eq_four_marginals, marginalAB_right_product,
    marginalBC_right_product, marginalRight_productState, entropy_relabelState,
    vonNeumannEntropy_productState, vonNeumannEntropy_productState]
  ring

open D5.S3.Quantum.Information.OrthogonalRecordEntropy
open D5.S3.Quantum.Information.MarginalCalculus
open D5.S3.Entropy.MaxEntropy

/-- Conditional product states with a classical B pointer. Zero weights require
no conditional inverse and are included in the same normalized mixture. -/
def classicalMarkovState (p : B → ℝ) (hp : ∀ j, 0 ≤ p j) (hs : ∑ j, p j = 1)
    (alpha : B → DensityState A) (gamma : B → DensityState C) :
    DensityState (A × (B × C)) :=
  mixtureState p hp hs (fun j => productState (alpha j)
    (productState (pointerState j) (gamma j)))

private theorem classical_to_record (p : B → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hs : ∑ j, p j = 1) (alpha : B → DensityState A) (gamma : B → DensityState C) :
    classicalMarkovState p hp hs alpha gamma =
      relabelState centerSplit (recordState p hp hs (fun j => productState (alpha j) (gamma j))) := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  change (∑ j, p j • (CStarMatrix.ofMatrix.symm (alpha j).1 ⊗ₖ
    (CStarMatrix.ofMatrix.symm (pointerState j).1 ⊗ₖ CStarMatrix.ofMatrix.symm (gamma j).1))) =
    (∑ j, p j • (CStarMatrix.ofMatrix.symm (pointerState j).1 ⊗ₖ
      (CStarMatrix.ofMatrix.symm (alpha j).1 ⊗ₖ CStarMatrix.ofMatrix.symm (gamma j).1))).submatrix
      (fun q : A × (B × C) => (q.2.1, (q.1, q.2.2)))
      (fun q : A × (B × C) => (q.2.1, (q.1, q.2.2)))
  ext ⟨a, b, c⟩ ⟨d, e, f⟩
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.submatrix_apply,
    Matrix.kronecker_apply]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Complex.real_smul]
  ring

private theorem classical_marginalBC (p : B → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hs : ∑ j, p j = 1) (alpha : B → DensityState A) (gamma : B → DensityState C) :
    marginalLeft (classicalMarkovState p hp hs alpha gamma) = recordState p hp hs gamma := by
  unfold classicalMarkovState recordState
  rw [marginalLeft_mixture]
  simp only [marginalLeft_productState]

private theorem classical_marginalAB (p : B → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hs : ∑ j, p j = 1) (alpha : B → DensityState A) (gamma : B → DensityState C) :
    marginalRight (relabelState (Equiv.prodAssoc A B C)
      (classicalMarkovState p hp hs alpha gamma)) =
        relabelState (Equiv.prodComm A B) (recordState p hp hs alpha) := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  change partialTraceRight
    ((∑ j, p j • (CStarMatrix.ofMatrix.symm (alpha j).1 ⊗ₖ
      (CStarMatrix.ofMatrix.symm (pointerState j).1 ⊗ₖ CStarMatrix.ofMatrix.symm (gamma j).1))).submatrix
        (Equiv.prodAssoc A B C) (Equiv.prodAssoc A B C)) =
    (∑ j, p j • (CStarMatrix.ofMatrix.symm (pointerState j).1 ⊗ₖ
      CStarMatrix.ofMatrix.symm (alpha j).1)).submatrix (Equiv.prodComm A B) (Equiv.prodComm A B)
  ext ⟨a, b⟩ ⟨d, e⟩
  simp only [partialTraceRight, Matrix.submatrix_apply, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.kronecker_apply, Equiv.prodAssoc_apply, Equiv.prodComm_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have ht : (∑ c : C, (gamma j).1 c c) = 1 := (gamma j).2.2
  simp only [Complex.real_smul]
  change (∑ c : C, (p j : ℂ) * ((alpha j).1 a d *
    ((pointerState j).1 b e * (gamma j).1 c c))) =
      (p j : ℂ) * ((pointerState j).1 b e * (alpha j).1 a d)
  calc
    _ = ((p j : ℂ) * (alpha j).1 a d * (pointerState j).1 b e) *
        ∑ c : C, (gamma j).1 c c := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro c hc; ring
    _ = _ := by rw [ht]; ring

/-- Classical B conditional products have zero ordinary CMI at every rank
and for all probability weights, including zero weights. -/
theorem qcmi_classicalMarkovState (p : B → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hs : ∑ j, p j = 1) (alpha : B → DensityState A) (gamma : B → DensityState C) :
    qcmi (toMState (classicalMarkovState p hp hs alpha gamma)) = 0 := by
  have hb : marginalRight (recordState p hp hs gamma) =
      mixtureState p hp hs pointerState := by
    unfold recordState
    rw [marginalRight_mixture]
    simp only [marginalRight_productState]
  have heB : vonNeumannEntropy (mixtureState p hp hs pointerState) = shannonEntropy p := by
    rw [orthogonal_mixture_entropy p hp hs pointerState pointerState_orthogonal]
    simp only [entropy_pointerState, mul_zero, Finset.sum_const_zero, add_zero]
  rw [qcmi_eq_four_marginals, classical_marginalAB, classical_marginalBC,
    hb, entropy_relabelState, entropy_recordState, entropy_recordState, heB,
    classical_to_record, entropy_relabelState, entropy_recordState]
  simp only [vonNeumannEntropy_productState, mul_add, Finset.sum_add_distrib]
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

section IsometryComparison

variable {I O R : Type*} [Fintype I] [DecidableEq I]
  [Fintype O] [DecidableEq O] [Fintype R] [DecidableEq R]

theorem isometry_operatorNorm_le (V : Matrix O I ℂ) (hV : Vᴴ * V = 1) :
    ‖V‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self V
  rw [hV] at h
  have ho : ‖(1 : Matrix I I ℂ)‖ ≤ 1 := by
    rcases isEmpty_or_nonempty I with hi | hi
    · have hz : (1 : Matrix I I ℂ) = 0 := Subsingleton.elim _ _
      simp [hz]
    · exact (norm_one : ‖(1 : Matrix I I ℂ)‖ = 1).le
  nlinarith [norm_nonneg V]

private def isometryState (V : Matrix O I ℂ) (hV : Vᴴ * V = 1)
    (P : DensityState I) : DensityState O := by
  refine ⟨CStarMatrix.ofMatrix (V * CStarMatrix.ofMatrix.symm P.1 * Vᴴ), ?_, ?_⟩
  · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      ((density_posSemidef P).mul_mul_conjTranspose_same V).nonneg
  · change Matrix.trace (V * CStarMatrix.ofMatrix.symm P.1 * Vᴴ) = 1
    rw [Matrix.trace_mul_cycle, hV, Matrix.one_mul]
    exact P.2.2

private theorem isometryState_distance (V W : Matrix O I ℂ)
    (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1) (P : DensityState I) :
    traceDistance (isometryState V hV P) (isometryState W hW P) ≤ ‖V - W‖ := by
  let X := V * CStarMatrix.ofMatrix.symm P.1 * Vᴴ -
    W * CStarMatrix.ofMatrix.symm P.1 * Wᴴ
  obtain ⟨U, hU⟩ := (traceNorm_eq_max_re_tr_U X).1
  let B := Vᴴ * U.val * V - Wᴴ * U.val * W
  have hb : B = (V-W)ᴴ * U.val * V + Wᴴ * U.val * (V-W) := by
    simp only [B, Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub]
    abel
  have hn : ‖B‖ ≤ 2 * ‖V-W‖ := by
    rw [hb]
    have hu : ‖U.val‖ ≤ 1 := isometry_operatorNorm_le U.val (Unitary.coe_star_mul_self U)
    have hv := isometry_operatorNorm_le V hV
    have hw := isometry_operatorNorm_le W hW
    have h1 := (Matrix.l2_opNorm_mul ((V-W)ᴴ * U.val) V).trans
      (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul (V-W)ᴴ U.val) (norm_nonneg V))
    have h2 := (Matrix.l2_opNorm_mul (Wᴴ * U.val) (V-W)).trans
      (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul Wᴴ U.val) (norm_nonneg (V-W)))
    rw [Matrix.l2_opNorm_conjTranspose] at h1 h2
    have hp1 : ‖V-W‖ * ‖U.val‖ * ‖V‖ ≤ ‖V-W‖ := by
      calc
        _ ≤ ‖V-W‖ * 1 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hu (norm_nonneg _)) hv
            (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have hp2 : ‖W‖ * ‖U.val‖ * ‖V-W‖ ≤ ‖V-W‖ := by
      have hh : ‖W‖ * ‖U.val‖ ≤ 1 :=
        (mul_le_mul hw hu (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
      nlinarith [norm_nonneg (V-W)]
    exact (norm_add_le _ _).trans (by linarith)
  have ht : Matrix.trace (U.val * X) = Matrix.trace (B * CStarMatrix.ofMatrix.symm P.1) := by
    simp only [X, B, Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub]
    congr 1
    · simp only [← Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm _ Vᴴ]
      simp only [Matrix.mul_assoc]
    · simp only [← Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm _ Wᴴ]
      simp only [Matrix.mul_assoc]
  have hp : traceNorm (CStarMatrix.ofMatrix.symm P.1) = 1 := by
    have h := traceNorm_of_posSemidef (density_posSemidef P)
    exact (congrArg Complex.re h).trans (congrArg Complex.re P.2.2)
  have he : traceNorm X ≤ 2 * ‖V-W‖ := by
    rw [← hU, ht]
    exact (D5.S3.Quantum.Matrix.UniformVarianceTraceBound.re_trace_mul_le _ _).trans
      (by rw [hp, mul_one]; exact hn)
  change traceNorm X / 2 ≤ _
  linarith

private theorem reference_isometry_norm_le (V : Matrix O I ℂ) :
    ‖(1 : Matrix R R ℂ) ⊗ₖ V‖ ≤ ‖V‖ := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self ((1 : Matrix R R ℂ) ⊗ₖ V)
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul] at h
  have hb : ‖(1 : Matrix R R ℂ) ⊗ₖ (Vᴴ * V)‖ ≤ ‖Vᴴ * V‖ :=
    NonUnitalStarAlgHom.norm_apply_le tensorRight _
  rw [h, Matrix.l2_opNorm_conjTranspose_mul_self] at hb
  nlinarith [norm_nonneg ((1 : Matrix R R ℂ) ⊗ₖ V), norm_nonneg V]

private theorem reference_isometry (V : Matrix O I ℂ) (hV : Vᴴ * V = 1) :
    (((1 : Matrix R R ℂ) ⊗ₖ V)ᴴ * ((1 : Matrix R R ℂ) ⊗ₖ V)) = 1 := by
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, hV, Matrix.one_kronecker_one]

private theorem reference_isometryState_distance (V W : Matrix O I ℂ)
    (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1) (P : DensityState (R × I)) :
    traceDistance (isometryState ((1 : Matrix R R ℂ) ⊗ₖ V) (reference_isometry V hV) P)
      (isometryState ((1 : Matrix R R ℂ) ⊗ₖ W) (reference_isometry W hW) P) ≤ ‖V-W‖ := by
  exact (isometryState_distance _ _ _ _ P).trans (by
    have he : (1 : Matrix R R ℂ) ⊗ₖ V - (1 : Matrix R R ℂ) ⊗ₖ W =
        (1 : Matrix R R ℂ) ⊗ₖ (V-W) := by ext i j; simp [mul_sub]
    rw [he]
    exact reference_isometry_norm_le (R := R) (V-W))

end IsometryComparison

section NormalizedColumns

variable [DecidableEq Q]

private theorem qubit_operatorNorm_sq_le_columns
    (D : Matrix (Fin 2 × Q) (Fin 2) ℂ) :
    ‖D‖ ^ 2 ≤ ‖column D 0 0‖ ^ 2 + ‖column D 1 0‖ ^ 2 +
      ‖column D 0 1‖ ^ 2 + ‖column D 1 1‖ ^ 2 := by
  let H := Dᴴ * D
  have hH : H.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self D
  have ht : (Matrix.trace H).re = ‖column D 0 0‖ ^ 2 + ‖column D 1 0‖ ^ 2 +
      ‖column D 0 1‖ ^ 2 + ‖column D 1 1‖ ^ 2 := by
    simp [H, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, column, EuclideanSpace.norm_sq_eq,
      Complex.mul_re, Complex.sq_norm, Complex.normSq_apply, ← Finset.sum_add_distrib]
    <;> ring
  have hn : ‖H‖ ≤ (Matrix.trace H).re := by
    have hs : (Matrix.trace H).re = ∑ i, hH.isHermitian.eigenvalues i := by
      simpa [Fin.sum_univ_two] using
        congrArg Complex.re hH.isHermitian.trace_eq_sum_eigenvalues
    have hp : 0 ≤ (Matrix.trace H).re := by
      rw [hs]
      exact Finset.sum_nonneg (fun i _ => hH.eigenvalues_nonneg i)
    have he : ‖H‖ = ‖fun i => (hH.isHermitian.eigenvalues i : ℂ)‖ := by
      conv_lhs => rw [hH.isHermitian.spectral_theorem]
      simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
        CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
        Matrix.l2_opNorm_diagonal]
      rfl
    rw [he]
    apply (pi_norm_le_iff_of_nonneg hp).mpr
    intro i
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hH.eigenvalues_nonneg i), hs]
    exact Finset.single_le_sum (fun j _ => hH.eigenvalues_nonneg j) (Finset.mem_univ i)
  have he : ‖H‖ = ‖D‖ ^ 2 := by
    dsimp only [H]
    rw [Matrix.l2_opNorm_conjTranspose_mul_self]
    ring
  rw [he, ht] at hn
  exact hn

private theorem normalize_retained_vector (v : EuclideanSpace ℂ Q) (t : ℝ)
    (ht : 0 ≤ t) (hvt : ‖v‖ ^ 2 + t ^ 2 = 1) (ht1 : t ^ 2 < 1) :
    let n := ‖v‖⁻¹ • v
    ‖n‖ = 1 ∧ ‖v-n‖ ^ 2 ≤ t ^ 2 := by
  have hv : 0 < ‖v‖ := by nlinarith [norm_nonneg v]
  have hv1 : ‖v‖ ≤ 1 := by nlinarith [sq_nonneg t, norm_nonneg v]
  dsimp only
  constructor
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hv), inv_mul_cancel₀ (ne_of_gt hv)]
  · have he : v - ‖v‖⁻¹ • v = (1 - ‖v‖⁻¹) • v := by
      rw [sub_smul, one_smul]
    rw [he, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have hid : (1 - ‖v‖⁻¹) * ‖v‖ = ‖v‖-1 := by
      rw [sub_mul, one_mul, inv_mul_cancel₀ (ne_of_gt hv)]
    nlinarith [sq_nonneg t]

/-- The normalized retained vectors define a physical pointer isometry. -/
def pointerIsometry (v : Fin 2 → EuclideanSpace ℂ Q) :
    Matrix (Fin 2 × Q) (Fin 2) ℂ := fun p i => if p.1 = i then v i p.2 else 0

private theorem pointerIsometry_column (v : Fin 2 → EuclideanSpace ℂ Q) (j i : Fin 2) :
    column (pointerIsometry v) j i = if j = i then v i else 0 := by
  ext q
  by_cases h : j = i <;> simp [column, pointerIsometry, h]

private theorem pointerIsometry_isometry (v : Fin 2 → EuclideanSpace ℂ Q)
    (hv : ∀ i, ‖v i‖ = 1) : (pointerIsometry v)ᴴ * pointerIsometry v = 1 := by
  ext i k
  by_cases hi : i = k
  · subst k
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, ite_true]
    simp only [Fintype.sum_prod_type, pointerIsometry, apply_ite, star_zero,
      ite_mul, zero_mul, mul_ite, mul_zero, ite_self, Finset.sum_ite_irrel,
      Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have h : inner ℂ (v i) (v i) = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hv]
      norm_num
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, mul_comm] using h
  · simp [Matrix.mul_apply, Matrix.conjTranspose_apply, pointerIsometry,
      Matrix.one_apply, Fintype.sum_prod_type, hi, Ne.symm hi]

/-- When the total flip probability is below one, normalize both retained
columns and remove the flips, without a rank or spectral-floor premise. -/
theorem normalized_pointer_isometry
    (W : Matrix (Fin 2 × Q) (Fin 2) ℂ) (hW : Wᴴ * W = 1)
    (hs : ‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2 < 1) :
    ∃ v : Fin 2 → EuclideanSpace ℂ Q,
      (∀ i, ‖v i‖ = 1) ∧
      (pointerIsometry v)ᴴ * pointerIsometry v = 1 ∧
      ‖W-pointerIsometry v‖ ≤
        2 * Real.sqrt (‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2) := by
  obtain ⟨h0,h1⟩ := retained_flip_norms W hW
  let v : Fin 2 → EuclideanSpace ℂ Q :=
    ![‖column W 0 0‖⁻¹ • column W 0 0, ‖column W 1 1‖⁻¹ • column W 1 1]
  have he0 := normalize_retained_vector (column W 0 0) ‖column W 1 0‖
    (norm_nonneg _) h0 (by nlinarith [sq_nonneg ‖column W 0 1‖])
  have he1 := normalize_retained_vector (column W 1 1) ‖column W 0 1‖
    (norm_nonneg _) h1 (by nlinarith [sq_nonneg ‖column W 1 0‖])
  have hv : ∀ i, ‖v i‖ = 1 := by
    intro i
    fin_cases i
    · exact he0.1
    · exact he1.1
  refine ⟨v,hv,pointerIsometry_isometry v hv,?_⟩
  have hd := qubit_operatorNorm_sq_le_columns (W-pointerIsometry v)
  have hc (j i : Fin 2) : column (W-pointerIsometry v) j i =
      column W j i - column (pointerIsometry v) j i := by ext q; rfl
  simp only [hc, pointerIsometry_column] at hd
  simp only [show (1 : Fin 2) ≠ 0 by decide, show (0 : Fin 2) ≠ 1 by decide,
    if_false, sub_zero, ite_true] at hd
  have hs0 : 0 ≤ ‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2 := by positivity
  have hsq := Real.sq_sqrt hs0
  have hsum : ‖W-pointerIsometry v‖ ^ 2 ≤
      2 * (‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2) := by
    have ha : ‖column W 0 0 - v 0‖ ^ 2 ≤ ‖column W 1 0‖ ^ 2 := he0.2
    have hb : ‖column W 1 1 - v 1‖ ^ 2 ≤ ‖column W 0 1‖ ^ 2 := he1.2
    linarith
  nlinarith [norm_nonneg (W-pointerIsometry v), Real.sqrt_nonneg
    (‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2)]

end NormalizedColumns

section PhysicalOutput

variable {A B C E : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype E] [DecidableEq E]

private def environmentLast : ((A × (B × C)) × E) ≃ (A × (B × (C × E))) where
  toFun p := (p.1.1,(p.1.2.1,(p.1.2.2,p.2)))
  invFun p := ((p.1,(p.2.1,p.2.2.1)),p.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

private def physicalOutput (W : Matrix (B × (C × E)) B ℂ) (hW : Wᴴ * W = 1)
    (P : DensityState (A × B)) : DensityState (A × (B × C)) :=
  D5.S3.Quantum.Information.MarginalCalculus.reduceState environmentLast
    (isometryState ((1 : Matrix A A ℂ) ⊗ₖ W) (reference_isometry W hW) P)

private theorem physicalOutput_entry (W : Matrix (B × (C × E)) B ℂ)
    (hW : Wᴴ * W = 1) (P : DensityState (A × B)) (a b : A) (j k : B) (c d : C) :
    (physicalOutput W hW P).1 (a,(j,c)) (b,(k,d)) =
      ∑ e : E, (W * (CStarMatrix.ofMatrix.symm P.1).submatrix
        (fun l => (a,l)) (fun l => (b,l)) * Wᴴ) (j,(c,e)) (k,(d,e)) := by
  have h := tensor_conjugate_block W (CStarMatrix.ofMatrix.symm P.1) a b
  change (∑ e : E, (((1 : Matrix A A ℂ) ⊗ₖ W) * CStarMatrix.ofMatrix.symm P.1 *
    ((1 : Matrix A A ℂ) ⊗ₖ W)ᴴ) (a,(j,(c,e))) (b,(k,(d,e)))) = _
  apply Finset.sum_congr rfl
  intro e _
  exact congrFun (congrFun h (j,(c,e))) (k,(d,e))

private theorem reduceState_distance {N K R : Type*} [Fintype N] [DecidableEq N]
    [Fintype K] [DecidableEq K] [Fintype R] [DecidableEq R]
    (e : (K × R) ≃ N) (rho sigma : DensityState N) :
    traceDistance (D5.S3.Quantum.Information.MarginalCalculus.reduceState e rho)
      (D5.S3.Quantum.Information.MarginalCalculus.reduceState e sigma) ≤
        traceDistance rho sigma := by
  let D := CStarMatrix.ofMatrix.symm rho.1 - CStarMatrix.ofMatrix.symm sigma.1
  have hh : D.IsHermitian := (density_posSemidef rho).isHermitian.sub
    (density_posSemidef sigma).isHermitian
  have h := partialTraceRight_contract (D.submatrix e e) (hh.submatrix e)
  rw [D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance.traceNorm_submatrix_equiv]
    at h
  have he : CStarMatrix.ofMatrix.symm
      (D5.S3.Quantum.Information.MarginalCalculus.reduceState e rho).1 -
      CStarMatrix.ofMatrix.symm
      (D5.S3.Quantum.Information.MarginalCalculus.reduceState e sigma).1 =
        partialTraceRight (D.submatrix e e) := by
    ext i j
    simp only [D5.S3.Quantum.Information.MarginalCalculus.reduceState_entry,
      partialTraceRight, D, Matrix.sub_apply, Matrix.submatrix_apply,
      Finset.sum_sub_distrib]
  unfold traceDistance
  rw [he]
  exact div_le_div_of_nonneg_right h (by norm_num)

/-- Discarding the common physical environment preserves the comparison of
the two normalized isometries, with no reference-dimension factor. -/
theorem physicalOutput_distance
    (V W : Matrix (B × (C × E)) B ℂ) (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1)
    (P : DensityState (A × B)) :
    traceDistance (physicalOutput V hV P) (physicalOutput W hW P) ≤ ‖V-W‖ :=
  (reduceState_distance environmentLast _ _).trans
    (reference_isometryState_distance V W hV hW P)

private theorem physicalOutput_actual (T : QuantumChannel B (B × C))
    (W : Matrix (B × (C × E)) B ℂ) (hW : Wᴴ * W = 1)
    (hT : ∀ (M : Matrix B B ℂ) (j k : B) (c d : C),
      (∑ e : E, (W * M * Wᴴ) (j,(c,e)) (k,(d,e))) =
        CStarMatrix.ofMatrix.symm (T.toCompletelyPositiveMap (CStarMatrix.ofMatrix M))
          (j,c) (k,d)) (P : DensityState (A × B)) :
    physicalOutput W hW P = referenceState T P := by
  apply Subtype.ext
  apply CStarMatrix.ext
  rintro ⟨a,j,c⟩ ⟨b,k,d⟩
  rw [physicalOutput_entry]
  exact hT _ j k c d

private def normalizedEnvironment (v : EuclideanSpace ℂ (C × E)) (hv : ‖v‖ = 1) :
    DensityState C :=
  marginalRight (pureState v.ofLp (by
    have h : inner ℂ v v = 1 := by rw [inner_self_eq_norm_sq_to_K,hv]; norm_num
    rw [dotProduct_comm]
    simpa only [EuclideanSpace.inner_eq_star_dotProduct] using h))

end PhysicalOutput

section PointerRepair

variable {A B C : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

private def blockWeight (P : DensityState (A × B)) (j : B) : ℝ :=
  (Matrix.trace (block (CStarMatrix.ofMatrix.symm P.1) j j)).re

private theorem diagonalBlock_positive (P : DensityState (A × B)) (j : B) :
    (block (CStarMatrix.ofMatrix.symm P.1) j j).PosSemidef :=
  (density_posSemidef P).submatrix _

private theorem blockWeight_nonneg (P : DensityState (A × B)) (j : B) :
    0 ≤ blockWeight P j :=
  (Complex.nonneg_iff.mp (diagonalBlock_positive P j).trace_nonneg).1

private theorem blockWeight_trace (P : DensityState (A × B)) (j : B) :
    Matrix.trace (block (CStarMatrix.ofMatrix.symm P.1) j j) = (blockWeight P j : ℂ) := by
  have hi := (Complex.nonneg_iff.mp (diagonalBlock_positive P j).trace_nonneg).2
  apply Complex.ext <;> simp [blockWeight, hi]

private theorem blockWeight_sum (P : DensityState (A × B)) : ∑ j, blockWeight P j = 1 := by
  have ht := congrArg Complex.re P.2.2
  change (∑ p : A × B, P.1 p p).re = 1 at ht
  rw [Fintype.sum_prod_type_right] at ht
  simpa only [Complex.re_sum, blockWeight, Matrix.trace, Matrix.diag_apply,
    block, Matrix.submatrix_apply, CStarMatrix.ofMatrix_symm_apply] using ht

private def conditionalBlock (P : DensityState (A × B)) (j : B) : DensityState A := by
  classical
  by_cases hp : 0 < blockWeight P j
  · refine ⟨CStarMatrix.ofMatrix ((blockWeight P j)⁻¹ •
      block (CStarMatrix.ofMatrix.symm P.1) j j), ?_, ?_⟩
    · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
        ((diagonalBlock_positive P j).smul (inv_nonneg.mpr (le_of_lt hp))).nonneg
    · change Matrix.trace ((blockWeight P j)⁻¹ •
        block (CStarMatrix.ofMatrix.symm P.1) j j) = 1
      rw [Matrix.trace_smul, blockWeight_trace]
      simp [Complex.real_smul, ne_of_gt hp]
  · exact marginalRight P

private theorem conditionalBlock_weighted (P : DensityState (A × B)) (j : B) :
    blockWeight P j • CStarMatrix.ofMatrix.symm (conditionalBlock P j).1 =
      block (CStarMatrix.ofMatrix.symm P.1) j j := by
  classical
  by_cases hp : 0 < blockWeight P j
  · simp only [conditionalBlock, dif_pos hp]
    change blockWeight P j • ((blockWeight P j)⁻¹ •
      block (CStarMatrix.ofMatrix.symm P.1) j j) = _
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hp), one_smul]
  · have hz : blockWeight P j = 0 := le_antisymm (le_of_not_gt hp) (blockWeight_nonneg P j)
    have hb : block (CStarMatrix.ofMatrix.symm P.1) j j = 0 :=
      (diagonalBlock_positive P j).trace_eq_zero_iff.mp (by rw [blockWeight_trace,hz]; simp)
    rw [hz, zero_smul, hb]

private def pointerInput (P : DensityState (A × B)) : DensityState (A × B) :=
  D5.S3.Quantum.Information.OrthogonalRecordEntropy.mixtureState
    (blockWeight P) (blockWeight_nonneg P) (blockWeight_sum P)
    (fun j => productState (conditionalBlock P j)
      (D5.S3.Quantum.Information.OrthogonalRecordEntropy.pointerState j))

private theorem pointerInput_entry (P : DensityState (A × B)) (a b : A) (j k : B) :
    (pointerInput P).1 (a,j) (b,k) = if j = k then P.1 (a,j) (b,j) else 0 := by
  unfold pointerInput D5.S3.Quantum.Information.OrthogonalRecordEntropy.mixtureState
  simp only [cstar_sum_entry, CStarMatrix.smul_apply]
  simp only [productState, CStarMatrix.ofMatrix_apply,
    D5.S3.Quantum.Information.OrthogonalRecordEntropy.pointerState,
    Matrix.kronecker_apply,Matrix.diagonal_apply]
  change (∑ l : B, (blockWeight P l : ℂ) *
    ((conditionalBlock P l).1 a b *
      (if j = k then if j = l then (1 : ℂ) else 0 else 0))) = _
  by_cases h : j = k
  · subst k
    simp only [ite_true, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    exact congrFun (congrFun (conditionalBlock_weighted P j) a) b
  · simp [h]

private theorem qubit_single_traceNorm (j k : Fin 2) :
    traceNorm (Matrix.single j k (1 : ℂ)) = 1 := by
  let M : Matrix (Fin 2) (Fin 2) ℂ := Matrix.single j k 1
  let D : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal (fun i => if i = k then 1 else 0)
  have hg : Mᴴ * M = D := by
    ext a b
    fin_cases j <;> fin_cases k <;> fin_cases a <;> fin_cases b <;>
      norm_num [M,D,Matrix.single,Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_two]
  have hp : 0 ≤ D := (Matrix.posSemidef_diagonal_iff.mpr (fun i => by
    split_ifs <;> norm_num)).nonneg
  have hs : D * D = D := by
    dsimp only [D]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    split_ifs <;> norm_num
  have hr : CFC.sqrt D = D := CFC.sqrt_unique hs hp
  change (CFC.sqrt (Mᴴ * M)).trace.re = 1
  rw [hg,hr]
  simp [D,Matrix.trace]

/-- Pinching the actual AB state in the pointer basis costs at most the
trace norm of its complex off-diagonal block in half trace distance. -/
theorem pointerInput_distance (P : DensityState (A × Fin 2)) :
    traceDistance P (pointerInput P) ≤ traceNorm (block (CStarMatrix.ofMatrix.symm P.1) 0 1) := by
  let X := block (CStarMatrix.ofMatrix.symm P.1) 0 1
  have hx : Xᴴ = block (CStarMatrix.ofMatrix.symm P.1) 1 0 := by
    ext a b
    exact congrFun (congrFun (density_posSemidef P).isHermitian.eq (a,1)) (b,0)
  have he : CStarMatrix.ofMatrix.symm P.1 - CStarMatrix.ofMatrix.symm (pointerInput P).1 =
      X ⊗ₖ Matrix.single 0 1 1 + Xᴴ ⊗ₖ Matrix.single 1 0 1 := by
    ext ⟨a,j⟩ ⟨b,k⟩
    simp only [Matrix.sub_apply, CStarMatrix.ofMatrix_symm_apply, pointerInput_entry, hx]
    fin_cases j <;> fin_cases k <;>
      simp [X,block,Matrix.single,Matrix.kronecker_apply]
  have h := traceNorm_add_le (X ⊗ₖ Matrix.single (0 : Fin 2) 1 (1 : ℂ))
    (Xᴴ ⊗ₖ Matrix.single (1 : Fin 2) 0 (1 : ℂ))
  rw [traceNorm_tensor,traceNorm_tensor,qubit_single_traceNorm,qubit_single_traceNorm,
    D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance.traceNorm_conjTranspose,
    mul_one] at h
  unfold traceDistance
  rw [he]
  dsimp only [X] at h
  linarith

private def pointerRepair (P : DensityState (A × B)) (gamma : B → DensityState C) :
    DensityState (A × (B × C)) :=
  MarkovConstructors.classicalMarkovState (blockWeight P) (blockWeight_nonneg P)
    (blockWeight_sum P) (conditionalBlock P) gamma

private theorem pointerRepair_entry (P : DensityState (A × B)) (gamma : B → DensityState C)
    (a b : A) (j k : B) (c d : C) :
    (pointerRepair P gamma).1 (a,(j,c)) (b,(k,d)) =
      if j = k then P.1 (a,j) (b,j) * (gamma j).1 c d else 0 := by
  unfold pointerRepair MarkovConstructors.classicalMarkovState
    D5.S3.Quantum.Information.OrthogonalRecordEntropy.mixtureState
  simp only [cstar_sum_entry, CStarMatrix.smul_apply]
  simp only [productState, CStarMatrix.ofMatrix_apply,
    D5.S3.Quantum.Information.OrthogonalRecordEntropy.pointerState,
    Matrix.kronecker_apply,Matrix.diagonal_apply]
  change (∑ l : B, (blockWeight P l : ℂ) * ((conditionalBlock P l).1 a b *
    ((if j = k then if j = l then (1 : ℂ) else 0 else 0) * (gamma l).1 c d))) = _
  by_cases h : j = k
  · subst k
    simp only [ite_true, ite_mul, one_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq,Finset.mem_univ,if_true]
    have h := congrFun (congrFun (conditionalBlock_weighted P j) a) b
    change (blockWeight P j : ℂ) * (conditionalBlock P j).1 a b = P.1 (a,j) (b,j) at h
    rw [← mul_assoc,h]
  · simp [h]

private theorem pointerRepair_qcmi (P : DensityState (A × B)) (gamma : B → DensityState C) :
    qcmi (D5.S3.Quantum.Foundation.FiniteDensityPurification.toMState
      (pointerRepair P gamma)) = 0 :=
  MarkovConstructors.qcmi_classicalMarkovState _ _ _ _ _

private theorem physicalOutput_pointer {E : Type*} [Fintype E] [DecidableEq E]
    (v : Fin 2 → EuclideanSpace ℂ (C × E)) (hv : ∀ j, ‖v j‖ = 1)
    (P : DensityState (A × Fin 2)) :
    physicalOutput (pointerIsometry v) (pointerIsometry_isometry v hv) (pointerInput P) =
      pointerRepair P (fun j => normalizedEnvironment (v j) (hv j)) := by
  apply Subtype.ext
  apply CStarMatrix.ext
  rintro ⟨a,j,c⟩ ⟨b,k,d⟩
  rw [physicalOutput_entry,pointerRepair_entry]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, pointerIsometry,
    Matrix.submatrix_apply, CStarMatrix.ofMatrix_symm_apply, pointerInput_entry]
  by_cases h : j = k
  · subst k
    simp only [ite_true,apply_ite,star_zero,mul_ite,mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
      if_true,ite_mul,zero_mul,ite_self]
    simp only [normalizedEnvironment, marginalRight, pureState,
      CStarMatrix.ofMatrix_apply, partialTraceRight, Matrix.vecMulVec_apply]
    change (∑ e : E, v j (c,e) * (P.1 (a,j) (b,j)) * star (v j (d,e))) =
      P.1 (a,j) (b,j) * ∑ e : E, v j (c,e) * star (v j (d,e))
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  · simp [h, Ne.symm h,apply_ite]

/-- Normalizing the actual retained columns and pinching the actual AB input
gives a same-system classical Markov repair, including zero block weights. -/
theorem classical_pointer_repair {E : Type*} [Fintype E] [DecidableEq E]
    (rho : DensityState (A × (Fin 2 × C)))
    (T : QuantumChannel (Fin 2) (Fin 2 × C))
    (W : Matrix (Fin 2 × (C × E)) (Fin 2) ℂ) (hW : Wᴴ * W = 1)
    (hT : ∀ (M : Matrix (Fin 2) (Fin 2) ℂ) (j k : Fin 2) (c d : C),
      (∑ e : E, (W * M * Wᴴ) (j,(c,e)) (k,(d,e))) =
        CStarMatrix.ofMatrix.symm (T.toCompletelyPositiveMap (CStarMatrix.ofMatrix M))
          (j,c) (k,d))
    (hs : ‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2 < 1) :
    let P := marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rho)
    ∃ sigma : DensityState (A × (Fin 2 × C)),
      qcmi (D5.S3.Quantum.Foundation.FiniteDensityPurification.toMState sigma) = 0 ∧
      traceDistance rho sigma ≤ traceDistance rho (referenceState T P) +
        traceNorm (block (CStarMatrix.ofMatrix.symm P.1) 0 1) +
        2 * Real.sqrt (‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2) := by
  dsimp only
  let P := marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rho)
  obtain ⟨v,hv,hvi,hd⟩ := normalized_pointer_isometry W hW hs
  let gamma := fun j => normalizedEnvironment (v j) (hv j)
  let sigma := pointerRepair P gamma
  refine ⟨sigma,pointerRepair_qcmi P gamma,?_⟩
  have hpin : traceDistance (referenceState T P) (referenceState T (pointerInput P)) ≤
      traceNorm (block (CStarMatrix.ofMatrix.symm P.1) 0 1) :=
    (referenceState_contract T P (pointerInput P)).trans (pointerInput_distance P)
  have hiso : traceDistance (referenceState T (pointerInput P)) sigma ≤
      2 * Real.sqrt (‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2) := by
    rw [← physicalOutput_actual T W hW hT]
    change traceDistance (physicalOutput W hW (pointerInput P))
      (pointerRepair P (fun j => normalizedEnvironment (v j) (hv j))) ≤ _
    rw [← physicalOutput_pointer v hv P]
    exact (physicalOutput_distance W (pointerIsometry v) hW hvi (pointerInput P)).trans hd
  have ht := traceDistance_triangle rho (referenceState T P) sigma
  have ht' := traceDistance_triangle (referenceState T P)
    (referenceState T (pointerInput P)) sigma
  linarith

end PointerRepair


section CommonEnvironmentRepair

variable {A C E : Type*} [Fintype A] [DecidableEq A]
  [Fintype C] [DecidableEq C] [Fintype E] [DecidableEq E]

private theorem normalized_common_isometry
    (W : Matrix (Fin 2 × (C × E)) (Fin 2) ℂ) (hW : Wᴴ * W = 1)
    (hs : ‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2 < 1) :
    ∃ v : EuclideanSpace ℂ (C × E), ‖v‖ = 1 ∧
      ‖W - pointerIsometry (fun _ => v)‖ ≤
        2 * Real.sqrt (‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2) +
        Real.sqrt (2 * ‖1 - inner ℂ (column W 1 1) (column W 0 0)‖) := by
  let s := Real.sqrt (‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2)
  let d := Real.sqrt (2 * ‖1 - inner ℂ (column W 1 1) (column W 0 0)‖)
  let v := ‖column W 0 0‖⁻¹ • column W 0 0
  obtain ⟨h0,h1⟩ := retained_flip_norms W hW
  have hv := normalize_retained_vector (column W 0 0) ‖column W 1 0‖
    (norm_nonneg _) h0 (by nlinarith [sq_nonneg ‖column W 0 1‖])
  refine ⟨v,hv.1,?_⟩
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hd0 : 0 ≤ d := Real.sqrt_nonneg _
  have hss : s ^ 2 = ‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hdd : d ^ 2 = 2 * ‖1 - inner ℂ (column W 1 1) (column W 0 0)‖ :=
    Real.sq_sqrt (by positivity)
  have hflip : ‖column W 1 0‖ ≤ s := by
    nlinarith [sq_nonneg ‖column W 0 1‖, norm_nonneg (column W 1 0)]
  have ha : ‖column W 0 0 - v‖ ≤ ‖column W 1 0‖ := by
    nlinarith [hv.2, norm_nonneg (column W 1 0), norm_nonneg (column W 0 0-v)]
  have hdiff : ‖column W 1 1 - column W 0 0‖ ≤ d := by
    nlinarith [retained_gap W hW, norm_nonneg (column W 1 1-column W 0 0)]
  have hb : ‖column W 1 1 - v‖ ≤ d + ‖column W 1 0‖ :=
    (norm_sub_le_norm_sub_add_norm_sub (column W 1 1) (column W 0 0) v).trans
      (add_le_add hdiff ha)
  have hc (j i : Fin 2) : column (W-pointerIsometry (fun _ => v)) j i =
      column W j i - column (pointerIsometry (fun _ => v)) j i := by ext q; rfl
  have hn := qubit_operatorNorm_sq_le_columns (W-pointerIsometry (fun _ => v))
  simp only [hc, pointerIsometry_column, ite_true,
    show (1 : Fin 2) ≠ 0 by decide, show (0 : Fin 2) ≠ 1 by decide,
    ite_false, sub_zero] at hn
  have ha2 : ‖column W 0 0-v‖ ^ 2 ≤ ‖column W 1 0‖ ^ 2 := hv.2
  have hb2 : ‖column W 1 1-v‖ ^ 2 ≤ (d+‖column W 1 0‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hcross : d * ‖column W 1 0‖ ≤ d * s := mul_le_mul_of_nonneg_left hflip hd0
  change ‖W-pointerIsometry (fun _ => v)‖ ≤ 2*s+d
  nlinarith [sq_nonneg ‖column W 0 1‖,
    norm_nonneg (W-pointerIsometry (fun _ => v))]

private theorem physicalOutput_common (v : EuclideanSpace ℂ (C × E)) (hv : ‖v‖ = 1)
    (P : DensityState (A × Fin 2)) :
    physicalOutput (pointerIsometry (fun _ => v))
      (pointerIsometry_isometry _ (fun _ => hv)) P =
      relabelState (Equiv.prodAssoc A (Fin 2) C).symm
        (productState P (normalizedEnvironment v hv)) := by
  apply Subtype.ext
  apply CStarMatrix.ext
  rintro ⟨a,j,c⟩ ⟨b,k,d⟩
  rw [physicalOutput_entry]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, pointerIsometry,
    Matrix.submatrix_apply, CStarMatrix.ofMatrix_symm_apply, apply_ite, star_zero,
    mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  change (∑ e : E, v (c,e) * P.1 (a,j) (b,k) * star (v (d,e))) =
    P.1 (a,j) (b,k) * ∑ e : E, v (c,e) * star (v (d,e))
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- A small phase-sensitive retained-column gap produces a product across AB
and C on the original physical carrier. -/
theorem common_environment_product_repair
    (rho : DensityState (A × (Fin 2 × C)))
    (T : QuantumChannel (Fin 2) (Fin 2 × C))
    (W : Matrix (Fin 2 × (C × E)) (Fin 2) ℂ) (hW : Wᴴ * W = 1)
    (hT : ∀ (M : Matrix (Fin 2) (Fin 2) ℂ) (j k : Fin 2) (c d : C),
      (∑ e : E, (W * M * Wᴴ) (j,(c,e)) (k,(d,e))) =
        CStarMatrix.ofMatrix.symm (T.toCompletelyPositiveMap (CStarMatrix.ofMatrix M))
          (j,c) (k,d))
    (hs : ‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2 < 1) :
    let P := marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rho)
    ∃ sigma : DensityState (A × (Fin 2 × C)),
      qcmi (D5.S3.Quantum.Foundation.FiniteDensityPurification.toMState sigma) = 0 ∧
      traceDistance rho sigma ≤ traceDistance rho (referenceState T P) +
        2 * Real.sqrt (‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2) +
        Real.sqrt (2 * ‖1 - inner ℂ (column W 1 1) (column W 0 0)‖) := by
  dsimp only
  let P := marginalRight (relabelState (Equiv.prodAssoc A (Fin 2) C) rho)
  obtain ⟨v,hv,hd⟩ := normalized_common_isometry W hW hs
  let sigma := relabelState (Equiv.prodAssoc A (Fin 2) C).symm
    (productState P (normalizedEnvironment v hv))
  refine ⟨sigma,MarkovConstructors.qcmi_product_right P _,?_⟩
  have ht : traceDistance (referenceState T P) sigma ≤
      2 * Real.sqrt (‖column W 1 0‖ ^ 2 + ‖column W 0 1‖ ^ 2) +
      Real.sqrt (2 * ‖1 - inner ℂ (column W 1 1) (column W 0 0)‖) := by
    rw [← physicalOutput_actual T W hW hT]
    change traceDistance (physicalOutput W hW P)
      (relabelState (Equiv.prodAssoc A (Fin 2) C).symm
        (productState P (normalizedEnvironment v hv))) ≤ _
    rw [← physicalOutput_common v hv P]
    exact (physicalOutput_distance W _ hW _ P).trans hd
  exact (traceDistance_triangle rho (referenceState T P) sigma).trans (by linarith)

end CommonEnvironmentRepair

end D5.S3.Quantum.Recovery.QubitResidualRounding
