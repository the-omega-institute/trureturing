/- GID: D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation
   generality: G
   mirror-B: D5/B/S3/Quantum/Subentropy/StrongSubadditivityRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation.conjecture; result=D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation.result; claim=D5/S3/Quantum/Subentropy/StrongSubadditivityRefutation.conjecture
   digest: Canonical density states and partial traces for a Bell pair with an independent qubit. -/

import D5.S3.Quantum.Subentropy.SpectralFormula
import D5.S3.Quantum.Subentropy.DensityKernel
import D5.S3.Quantum.Information.InputInformationBalance
import D5.S3.Quantum.Subentropy.UniformValues
import D5.S3.Quantum.Foundation.FiniteStateChannel
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.Quantum.Entanglement.BellPureStateMixedMarginal

/-! Density-state relabelling and the exact marginals of the Bell-pair witness. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace D5.S3.Quantum.Subentropy.StrongSubadditivityRefutation

open scoped BigOperators ComplexOrder MatrixOrder Kronecker Topology
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.QuantumBounds.CHSHWitness
open D5.S3.Quantum.Entanglement.BellPureStateMixedMarginal
open D5.S3.Quantum.Subentropy.Basic
open D5.S3.Quantum.Subentropy.UniformValues

/-- The associativity bijection only changes the grouping of subsystem labels. -/
def reassocState {A B C : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (rho : DensityState ((A × B) × C)) : DensityState (A × (B × C)) :=
  D5.S3.Quantum.Information.InputInformationBalance.relabel
    (Equiv.prodAssoc A B C).symm rho

/-- The maximally mixed qubit density. -/
def uniformTwo : DensityState (Fin 2) := by
  refine ⟨CStarMatrix.ofMatrix (Matrix.diagonal fun _ : Fin 2 => (1 / 2 : ℂ)), ?_, ?_⟩
  · apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
    exact (Matrix.PosSemidef.diagonal (fun _ => by norm_num [Complex.le_def])).nonneg
  · change Matrix.trace (Matrix.diagonal fun _ : Fin 2 => (1 / 2 : ℂ)) = 1
    norm_num [Matrix.trace, Fin.sum_univ_two]

/-- The existing normalized Bell density, packaged in the canonical state carrier. -/
def bellState : DensityState (Fin 2 × Fin 2) :=
  ⟨CStarMatrix.ofMatrix bellDensity,
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv bell_density_is_state.1.nonneg,
    bell_density_is_state.2⟩

/-- A Bell pair on the first two qubits and an independent maximally mixed third qubit. -/
def witness : DensityState ((Fin 2 × Fin 2) × Fin 2) :=
  productState bellState uniformTwo

/-- Tracing out the first Bell qubit leaves the maximally mixed second qubit. -/
private theorem marginalLeft_bellState : marginalLeft bellState = uniformTwo := by
  have h := bell_pure_state_has_maximally_mixed_marginal
  have hright := h.2.2.2.2.2.1
  apply Subtype.ext
  apply congrArg CStarMatrix.ofMatrix
  change partialTraceLeft bellDensity = Matrix.diagonal (fun _ : Fin 2 => (1 / 2 : ℂ))
  have hsym : partialTraceLeft bellDensity = partialTraceRight bellDensity := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [partialTraceLeft, partialTraceRight, Fin.sum_univ_two,
        bellDensity, bellVector, D5.S3.Quantum.QubitWitnesses.bellCoefficients,
        Matrix.vecMulVec_apply]
  rw [hsym]
  change D5.S3.Quantum.EnvironmentRecords.traceEnvironment bellDensity = _
  rw [hright]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

/-- An independent third subsystem stays independent after tracing out the first one. -/
private theorem marginalLeft_reassoc_productState {A B C : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] (rho : DensityState (A × B)) (sigma : DensityState C) :
    marginalLeft (reassocState (productState rho sigma)) =
      productState (marginalLeft rho) sigma := by
  apply Subtype.ext
  apply congrArg CStarMatrix.ofMatrix
  ext ⟨b, c⟩ ⟨d, e⟩
  change (∑ a : A, rho.1 (a, b) (a, d) * sigma.1 c e) =
    (∑ a : A, rho.1 (a, b) (a, d)) * sigma.1 c e
  exact (Finset.sum_mul ..).symm

/-- The three marginal states of the Bell-pair counterexample. -/
private theorem witness_marginals :
    marginalRight witness = bellState ∧
      marginalLeft (marginalRight witness) = uniformTwo ∧
      marginalLeft (reassocState witness) = productState uniformTwo uniformTwo := by
  have hab : marginalRight witness = bellState :=
    marginalRight_productState bellState uniformTwo
  refine ⟨hab, ?_, ?_⟩
  · exact (congrArg marginalLeft hab).trans marginalLeft_bellState
  · exact (marginalLeft_reassoc_productState bellState uniformTwo).trans
      (congrArg (fun rho : DensityState (Fin 2) => productState rho uniformTwo)
        marginalLeft_bellState)

private theorem uniform_product_matrix :
    CStarMatrix.ofMatrix.symm (productState uniformTwo uniformTwo).1 =
      Matrix.diagonal (fun _ : Fin 2 × Fin 2 => (1 / 4 : ℂ)) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [uniformTwo, productState, Matrix.kroneckerMap_apply,
      CStarMatrix.ofMatrix_apply]

/-- The Bell pair embeds a third-qubit amplitude isometrically into three qubits. -/
private def bellEmbedding : Matrix ((Fin 2 × Fin 2) × Fin 2) (Fin 2) ℂ :=
  fun row col => if row.2 = col then bellVector row.1 else 0

private theorem bellEmbedding_isometry :
    bellEmbedding.conjTranspose * bellEmbedding = 1 := by
  have hv : (∑ i, star (bellVector i) * bellVector i) = 1 :=
    bell_pure_state_has_maximally_mixed_marginal.1
  ext c d
  fin_cases c <;> fin_cases d <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, bellEmbedding,
      Fintype.sum_prod_type, Fin.sum_univ_two] <;>
    simpa [Fintype.sum_prod_type, Fin.sum_univ_two] using hv

private theorem witness_isometric :
    CStarMatrix.ofMatrix.symm witness.1 =
      bellEmbedding * (CStarMatrix.ofMatrix.symm uniformTwo.1) *
        bellEmbedding.conjTranspose := by
  ext ⟨ij, c⟩ ⟨kl, d⟩
  fin_cases c <;> fin_cases d <;>
    simp [witness, productState, bellState, uniformTwo,
      Matrix.mul_apply, Matrix.conjTranspose_apply, bellEmbedding,
      Fin.sum_univ_two, bellDensity, Matrix.vecMulVec_apply,
      Matrix.kroneckerMap_apply, CStarMatrix.ofMatrix_apply] <;> ring

local instance {ι : Type} [Fintype ι] [DecidableEq ι] :
    TopologicalSpace (DensityState ι) := by
  unfold DensityState
  infer_instance

/-- A spectral functional family with the paper's continuous-extension convention.
The coordinate types are in `Type`, so the settlement proposition is closed. -/
structure SubentropyLike where
  value : {ι : Type} → [Fintype ι] → [DecidableEq ι] → DensityState ι → ℝ
  continuous : ∀ {ι : Type} [Fintype ι] [DecidableEq ι], Continuous (@value ι _ _)
  invariant : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (rho sigma : DensityState ι) (U : Matrix.unitaryGroup ι ℂ),
    CStarMatrix.ofMatrix.symm rho.1 =
      (U : Matrix ι ι ℂ) * CStarMatrix.ofMatrix.symm sigma.1 * star (U : Matrix ι ι ℂ) →
    value rho = value sigma
  formula : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (rho : DensityState ι) (p : ι → ℝ),
    CStarMatrix.ofMatrix.symm rho.1 = Matrix.diagonal (fun i => (p i : ℂ)) →
    (∀ i, 0 < p i) → (∑ i, p i = 1) → Function.Injective p →
    value rho = -(∑ i, p i ^ Fintype.card ι * Real.log (p i) /
      (∏ j ∈ Finset.univ.erase i, (p i - p j)))

private theorem continuous_subentropy {ι : Type} [Fintype ι] [DecidableEq ι] :
    Continuous (@subentropy ι _ _) := by
  exact DensityKernel.continuousOn_matrixSubentropy.comp_continuous
    (CStarMatrix.ofMatrixL.symm.continuous.comp continuous_subtype_val)
    (fun sigma => ⟨density_posSemidef sigma, sigma.2.2⟩)

private def canonicalSubentropy : SubentropyLike where
  value := subentropy
  continuous := @continuous_subentropy
  invariant := by
    intro ι _ _ rho sigma U h
    unfold subentropy
    rw [h]
    exact matrixSubentropy_isometric_embedding _ _ (Unitary.coe_star_mul_self U)
  formula := by
    intro ι _ _ rho p h hp hs hi
    unfold subentropy
    rw [h]
    exact SpectralFormula.matrixSubentropy_diagonal_eq_distinct_formula p hp hs hi

private def diagonalState {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) : DensityState ι := by
  refine ⟨CStarMatrix.ofMatrix (Matrix.diagonal fun i => (p i : ℂ)), ?_, ?_⟩
  · apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
    exact (Matrix.PosSemidef.diagonal (fun i => by simpa [Complex.le_def] using hp i)).nonneg
  · change Matrix.trace (Matrix.diagonal fun i => (p i : ℂ)) = 1
    rw [Matrix.trace_diagonal]
    rw [← Complex.ofReal_sum, hs, Complex.ofReal_one]

private def unitaryState {ι : Type} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (rho : DensityState ι) : DensityState ι := by
  refine ⟨CStarMatrix.ofMatrix
    ((U : Matrix ι ι ℂ) * CStarMatrix.ofMatrix.symm rho.1 * star (U : Matrix ι ι ℂ)), ?_, ?_⟩
  · apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
    exact ((density_posSemidef rho).mul_mul_conjTranspose_same _).nonneg
  · change Matrix.trace ((U : Matrix ι ι ℂ) * _ * star (U : Matrix ι ι ℂ)) = 1
    rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]
    exact rho.2.2

/-- Ordered positive perturbations identify every continuous invariant spectral
functional, including at repeated and zero eigenvalues. -/
private theorem subentropyLike_eq (Q : SubentropyLike) {ι : Type}
    [Fintype ι] [DecidableEq ι] (rho : DensityState ι) : Q.value rho = subentropy rho := by
  classical
  let A := CStarMatrix.ofMatrix.symm rho.1
  have hA := density_posSemidef rho
  haveI : Nonempty ι := by
    by_contra h
    haveI : IsEmpty ι := not_nonempty_iff.mp h
    have ht := rho.2.2
    simp [Matrix.trace] at ht
  let e : ι ≃ Fin (Fintype.card ι) :=
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))).symm
  let p := hA.isHermitian.eigenvalues
  have hp : ∀ i, 0 ≤ p i := hA.eigenvalues_nonneg
  have hs : ∑ i, p i = 1 := by
    have ht := hA.isHermitian.trace_eq_sum_eigenvalues
    rw [show A.trace = 1 from rho.2.2] at ht
    simpa using (congrArg Complex.re ht).symm
  let w : ι → ℝ := fun i => (Fintype.card ι : ℝ) - (e i).val
  have hw : ∀ i, 0 < w i := by
    intro i
    exact sub_pos.mpr (by exact_mod_cast (e i).isLt)
  let S : ℝ := ∑ i, w i
  have hS : 0 < S := Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty
  let q : ι → ℝ := fun i => w i / S
  have hq : ∀ i, 0 < q i := fun i => div_pos (hw i) hS
  have hqs : ∑ i, q i = 1 := by
    simp only [q, ← Finset.sum_div]
    exact div_self hS.ne'
  let eps : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have heps : ∀ k, 0 < eps k ∧ eps k ≤ 1 := by
    intro k
    dsimp [eps]
    constructor
    · positivity
    · exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) k])
  let r : ℕ → ι → ℝ := fun k i => (1 - eps k) * p i + eps k * q i
  have hr : ∀ k i, 0 < r k i := by
    intro k i
    exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr (heps k).2) (hp i))
      (mul_pos (heps k).1 (hq i))
  have hrs : ∀ k, ∑ i, r k i = 1 := by
    intro k
    simp only [r, Finset.sum_add_distrib, ← Finset.mul_sum, hs, hqs]
    ring
  have hri : ∀ k, Function.Injective (r k) := by
    intro k i j hij
    have horder (a b : ι) (hab : (e a).val < (e b).val) : r k b < r k a := by
      have hpp : p b ≤ p a := hA.isHermitian.eigenvalues₀_antitone (le_of_lt hab)
      have hqq : q b < q a := by
        apply (div_lt_div_iff_of_pos_right hS).mpr
        dsimp [w]
        exact sub_lt_sub_left (by exact_mod_cast hab) _
      have hmul := mul_pos (heps k).1 (sub_pos.mpr hqq)
      have hmul' := mul_nonneg (sub_nonneg.mpr (heps k).2) (sub_nonneg.mpr hpp)
      dsimp [r]
      nlinarith
    apply e.injective
    apply Fin.ext
    rcases lt_trichotomy (e i).val (e j).val with h | h | h
    · exact False.elim ((ne_of_gt (horder i j h)) hij)
    · exact h
    · exact False.elim ((ne_of_lt (horder j i h)) hij)
  let U := hA.isHermitian.eigenvectorUnitary
  let states : ℕ → DensityState ι := fun k =>
    unitaryState U (diagonalState (r k) (fun i => (hr k i).le) (hrs k))
  have hlim : Filter.Tendsto states Filter.atTop (𝓝 rho) := by
    apply tendsto_subtype_rng.mpr
    change Filter.Tendsto
      (fun k => CStarMatrix.ofMatrix
        ((U : Matrix ι ι ℂ) * Matrix.diagonal (fun i => (r k i : ℂ)) *
          star (U : Matrix ι ι ℂ))) _ (𝓝 rho.1)
    have he : Filter.Tendsto eps Filter.atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hm : Filter.Tendsto (fun k => Matrix.diagonal (fun i => (r k i : ℂ)))
        Filter.atTop (𝓝 (Matrix.diagonal (fun i => (p i : ℂ)))) := by
      apply tendsto_pi_nhds.mpr
      intro i
      apply tendsto_pi_nhds.mpr
      intro j
      by_cases hij : i = j
      · subst j
        simp only [Matrix.diagonal_apply_eq]
        apply Complex.continuous_ofReal.continuousAt.tendsto.comp
        simpa [r] using (((tendsto_const_nhds (x := (1 : ℝ))).sub he).mul_const (p i)).add
          (he.mul_const (q i))
      · simp [Matrix.diagonal_apply_ne _ hij]
    have hconj := ((tendsto_const_nhds (x := (U : Matrix ι ι ℂ))).mul hm).mul
      (tendsto_const_nhds (x := star (U : Matrix ι ι ℂ)))
    have hspec : (U : Matrix ι ι ℂ) * Matrix.diagonal (fun i => (p i : ℂ)) *
        star (U : Matrix ι ι ℂ) = A := hA.isHermitian.spectral_theorem.symm
    rw [hspec] at hconj
    exact CStarMatrix.ofMatrixL.continuous.continuousAt.tendsto.comp hconj
  have heq : ∀ k, Q.value (states k) = subentropy (states k) := by
    intro k
    have hmat : CStarMatrix.ofMatrix.symm (states k).1 =
        (U : Matrix ι ι ℂ) *
          CStarMatrix.ofMatrix.symm (diagonalState (r k) (fun i => (hr k i).le) (hrs k)).1 *
          star (U : Matrix ι ι ℂ) := rfl
    change Q.value (states k) = canonicalSubentropy.value (states k)
    rw [Q.invariant _ _ U hmat, canonicalSubentropy.invariant _ _ U hmat]
    exact (Q.formula _ (r k) rfl (hr k) (hrs k) (hri k)).trans
      (canonicalSubentropy.formula _ (r k) rfl (hr k) (hrs k) (hri k)).symm
  exact tendsto_nhds_unique ((Q.continuous.tendsto rho).comp hlim)
    (((continuous_subentropy.tendsto rho).comp hlim).congr (fun k => (heq k).symm))

/-- Strong subadditivity for every family with the paper's spectral formula,
unitary invariance and continuous extension to all density states. -/
def conjecture : Prop :=
  ∀ Q : SubentropyLike,
  ∀ (A B C : Type) [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (rho : DensityState ((A × B) × C)),
    Q.value rho + Q.value (marginalLeft (marginalRight rho)) ≤
      Q.value (marginalRight rho) + Q.value (marginalLeft (reassocState rho))

private theorem witness_gap :
    subentropy witness + subentropy (marginalLeft (marginalRight witness)) -
      (subentropy (marginalRight witness) + subentropy (marginalLeft (reassocState witness))) =
        1 / 12 := by
  have hu : subentropy uniformTwo = Real.log 2 - 1 / 2 := by
    simpa [subentropy, uniformTwo] using
      (subentropy_uniformTwo (ι := Fin 2) (by decide))
  have hpure : subentropy bellState = 0 := by
    unfold subentropy
    change matrixSubentropy bellDensity = 0
    exact matrixSubentropy_pure bellVector
      bell_pure_state_has_maximally_mixed_marginal.1
  have hw : subentropy witness = subentropy uniformTwo := by
    unfold subentropy
    rw [witness_isometric]
    exact matrixSubentropy_isometric_embedding _ _ bellEmbedding_isometry
  have hfour : subentropy (productState uniformTwo uniformTwo) = Real.log 4 - 13 / 12 := by
    unfold subentropy
    rw [uniform_product_matrix]
    simpa using (subentropy_uniformFour (ι := Fin 2 × Fin 2) (by decide))
  have hlog : Real.log 4 = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h
    exact h
  rcases witness_marginals with ⟨hab, hb, hbc⟩
  rw [hb, hab, hbc, hw, hu, hpure, hfour, hlog]
  ring

/-- The Bell-pair witness violates strong subadditivity by exactly one twelfth. -/
theorem result : ¬ conjecture := by
  intro h
  have hssa := h canonicalSubentropy (Fin 2) (Fin 2) (Fin 2) witness
  simp only [subentropyLike_eq] at hssa
  have hgap := witness_gap
  linarith

end D5.S3.Quantum.Subentropy.StrongSubadditivityRefutation
