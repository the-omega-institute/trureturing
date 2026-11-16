/- GID: D5/S3/Quantum/Information/StrongSubadditivity/MarkovConstructors
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/StrongSubadditivity/MarkovConstructors
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual-marginal ordinary conditional mutual information of normalized product states. -/

import D5.S3.Quantum.Information.MarginalCalculus

/-! Product and orthogonal-record entropy identities for actual finite states. -/

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
