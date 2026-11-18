/- GID: D5/S3/Quantum/Divergence/UmegakiReferenceTransport
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/UmegakiReferenceTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual amplified channel adjunction and strict positivity for correlated matrices. -/

import D5.S3.Quantum.Divergence.UmegakiConditionalKernel
import D5.S3.Quantum.Divergence.UniversalPositiveScalarizer
import D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction

/-! Matrix transport for the canonical reference-amplified channel and its trace adjoint. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Divergence.CanonicalChannelDPI
open D5.S3.Quantum.Divergence.UniversalPositiveScalarizer
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction

namespace D5.S3.Quantum.Divergence.UmegakiReferenceTransport
universe u
variable {a b R : Type u} [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b] [Fintype R] [DecidableEq R]

lemma partialTraceRight_posDef [Nonempty a]
    (Z : Matrix (R × a) (R × a) ℂ) (hZ : Z.PosDef) :
    (partialTraceRight Z).PosDef := by
  have he : partialTraceRight Z =
      ∑ i : a, Z.submatrix (fun r => (r,i)) (fun r => (r,i)) := by
    ext r s
    simp [partialTraceRight, Matrix.sum_apply]
  rw [he]
  exact Matrix.posDef_sum Finset.univ_nonempty (fun i _ =>
    hZ.submatrix (fun r s h => (Prod.mk.inj h).1))

lemma partialTraceRight_mul_embed (Z : Matrix (R × a) (R × a) ℂ)
    (X : Matrix R R ℂ) :
    partialTraceRight (Z * (X ⊗ₖ (1 : Matrix a a ℂ))) = partialTraceRight Z * X := by
  ext r s
  simp only [partialTraceRight, Matrix.mul_apply, Matrix.kronecker_apply,
    Fintype.sum_prod_type, Matrix.one_apply, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]

lemma partialTraceRight_embed_mul (Z : Matrix (R × a) (R × a) ℂ)
    (X : Matrix R R ℂ) :
    partialTraceRight ((X ⊗ₖ (1 : Matrix a a ℂ)) * Z) = X * partialTraceRight Z := by
  ext r s
  simp only [partialTraceRight, Matrix.mul_apply, Matrix.kronecker_apply,
    Fintype.sum_prod_type, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

/-- Ordinary complex trace adjunction for the partial trace. -/
lemma trace_embed_pair (X : Matrix R R ℂ) (V : Matrix (R × a) (R × a) ℂ) :
    ((X ⊗ₖ (1 : Matrix a a ℂ))ᴴ * V).trace = (Xᴴ * partialTraceRight V).trace := by
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← trace_partialTraceRight, partialTraceRight_embed_mul]

lemma amp_kronecker (N : QuantumChannel a b) (X : Matrix R R ℂ)
    (Z : Matrix a a ℂ) : amp N (X ⊗ₖ Z) = X ⊗ₖ act N Z := by
  ext ⟨r,i⟩ ⟨s,j⟩
  rw [amp_entry]
  change (N.toCompletelyPositiveMap ((X r s) • CStarMatrix.ofMatrix Z)) i j = _
  rw [map_smul]
  rfl

lemma amp_mono (N : QuantumChannel a b)
    {X Z : Matrix (R × a) (R × a) ℂ} (h : X ≤ Z) : amp N X ≤ amp N Z := by
  have hp := referenceAction_nonneg N (CStarMatrix.ofMatrix (Z-X))
    (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (sub_nonneg.mpr h))
  have hn := map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm hp
  change 0 ≤ amp N (Z-X) at hn
  have he : amp N (Z-X) = amp N Z - amp N X := by
    exact (CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp
      ((referenceLinear N).comp CStarMatrix.ofMatrixₗ.toLinearMap)).map_sub Z X
  rw [he] at hn
  exact sub_nonneg.mp hn

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
lemma positive_floor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Z : Matrix ι ι ℂ) (hZ : Z.PosDef) :
    ∃ m : ℝ, 0 < m ∧ m • (1 : Matrix ι ι ℂ) ≤ Z := by
  cases isEmpty_or_nonempty ι with
  | inl h => exact ⟨1, zero_lt_one, le_of_eq (Subsingleton.elim _ _)⟩
  | inr h =>
    obtain ⟨m,hm,hfloor⟩ := (CFC.exists_pos_algebraMap_le_iff Z).mpr
      (fun x hx => hZ.isStrictlyPositive.spectrum_pos hx)
    exact ⟨m,hm,by simpa only [Algebra.algebraMap_eq_smul_one] using hfloor⟩

set_option maxHeartbeats 1200000 in
/-- Positivity of the channel image of the identity gives strict positivity
on every correlated positive-definite reference input. -/
lemma amp_posDef (N : QuantumChannel a b) (hN : (act N 1).PosDef)
    (Z : Matrix (R × a) (R × a) ℂ) (hZ : Z.PosDef) : (amp N Z).PosDef := by
  obtain ⟨m,hm,hfloor⟩ := positive_floor Z hZ
  have hmon : amp N (m • (1 : Matrix (R × a) (R × a) ℂ)) ≤ amp N Z :=
    amp_mono N hfloor
  have he : amp N (m • (1 : Matrix (R × a) (R × a) ℂ)) =
      m • ((1 : Matrix R R ℂ) ⊗ₖ act N 1) := by
    rw [amp_smul, ← Matrix.one_kronecker_one, amp_kronecker]
  rw [he] at hmon
  have hp : ((1 : Matrix R R ℂ) ⊗ₖ act N 1).PosDef :=
    (Matrix.PosDef.one (n := R)).kronecker hN
  exact ((hp.isStrictlyPositive.smul hm).of_le hmon).posDef

lemma amp_mul_embed (N : QuantumChannel a b)
    (Z : Matrix (R × a) (R × a) ℂ) (X : Matrix R R ℂ) :
    amp N (Z * (X ⊗ₖ (1 : Matrix a a ℂ))) = amp N Z * (X ⊗ₖ (1 : Matrix b b ℂ)) := by
  ext ⟨r,i⟩ ⟨s,j⟩
  rw [amp_entry]
  have h (p q : a) : (Z * (X ⊗ₖ (1 : Matrix a a ℂ))) (r,p) (s,q) =
      ∑ t, Z (r,p) (t,q) * X t s := by
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker_apply, Matrix.one_apply,
      mul_ite, mul_assoc]
  have hblock : (fun p q => (Z * (X ⊗ₖ (1 : Matrix a a ℂ))) (r,p) (s,q)) =
      ∑ t, X t s • (fun p q => Z (r,p) (t,q)) := by
    ext p q
    simp [h, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_comm]
  rw [hblock]
  let L : Matrix a a ℂ →ₗ[ℂ] Matrix b b ℂ := CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp
    (N.toCompletelyPositiveMap.toLinearMap.comp CStarMatrix.ofMatrixₗ.toLinearMap)
  change L (∑ t, X t s • (fun p q => Z (r,p) (t,q))) i j = _
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp [show ∀ Q, L Q = act N Q from fun _ => rfl, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker_apply,
    Matrix.one_apply, mul_ite, mul_assoc, amp_entry, mul_comm]

lemma amp_embed_mul (N : QuantumChannel a b)
    (Z : Matrix (R × a) (R × a) ℂ) (X : Matrix R R ℂ) :
    amp N ((X ⊗ₖ (1 : Matrix a a ℂ)) * Z) = (X ⊗ₖ (1 : Matrix b b ℂ)) * amp N Z := by
  ext ⟨r,i⟩ ⟨s,j⟩
  rw [amp_entry]
  have h (p q : a) : ((X ⊗ₖ (1 : Matrix a a ℂ)) * Z) (r,p) (s,q) =
      ∑ t, X r t * Z (t,p) (s,q) := by
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker_apply, Matrix.one_apply,
      ite_mul, mul_ite]
  have hblock : (fun p q => ((X ⊗ₖ (1 : Matrix a a ℂ)) * Z) (r,p) (s,q)) =
      ∑ t, X r t • (fun p q => Z (t,p) (s,q)) := by
    ext p q
    simp [h, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hblock]
  let L : Matrix a a ℂ →ₗ[ℂ] Matrix b b ℂ := CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp
    (N.toCompletelyPositiveMap.toLinearMap.comp CStarMatrix.ofMatrixₗ.toLinearMap)
  change L (∑ t, X r t • (fun p q => Z (t,p) (s,q))) i j = _
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp [show ∀ Q, L Q = act N Q from fun _ => rfl, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kronecker_apply,
    Matrix.one_apply, ite_mul, mul_ite, amp_entry]


section Adjoint
variable [Nonempty a] [Nonempty b]

private lemma Phi_eq_sum (N : QuantumChannel a b) (Y : Matrix b b ℂ) :
    Phi N Y = ∑ j, (K N j)ᴴ * Y * K N j := by
  ext x y
  simp only [Phi, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]

private lemma Phi_trace_pair (N : QuantumChannel a b) (Y : Matrix b b ℂ)
    (Z : Matrix a a ℂ) : (Phi N Y * Z).trace = (Y * act N Z).trace := by
  rw [Phi_eq_sum]
  change _ = (Y * CStarMatrix.ofMatrix.symm
    (N.toCompletelyPositiveMap (CStarMatrix.ofMatrix Z))).trace
  rw [(actual_kraus_representation N).haction]
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro j _
  change ((K N j)ᴴ * Y * K N j * Z).trace = (Y * (K N j * Z * (K N j)ᴴ)).trace
  rw [show (K N j)ᴴ * Y * K N j * Z = (K N j)ᴴ * (Y * K N j * Z) by
    simp only [Matrix.mul_assoc], Matrix.trace_mul_comm (K N j)ᴴ]
  simp only [Matrix.mul_assoc]

/-- The normalized canonical Kraus adjoint pairs with the actual channel
action on every complex joint matrix and every finite quantum reference. -/
lemma PhiR_trace_pair (N : QuantumChannel a b)
    (Y : Matrix (R × b) (R × b) ℂ) (Z : Matrix (R × a) (R × a) ℂ) :
    (PhiR N Y * Z).trace = (Y * amp N Z).trace := by
  change (∑ p, ∑ q, PhiR N Y p q * Z q p) =
    ∑ p, ∑ q, Y p q * amp N Z q p
  simp only [Fintype.sum_prod_type]
  calc
    (∑ r, ∑ x, ∑ s, ∑ y, PhiR N Y (r,x) (s,y) * Z (s,y) (r,x)) =
        ∑ r, ∑ s, (Phi N (Y.submatrix (fun i => (r,i)) (fun j => (s,j))) *
          Z.submatrix (fun i => (s,i)) (fun j => (r,j))).trace := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
      rfl
    _ = ∑ r, ∑ s, ((Y.submatrix (fun i => (r,i)) (fun j => (s,j))) *
        act N (Z.submatrix (fun i => (s,i)) (fun j => (r,j)))).trace := by
      simp_rw [Phi_trace_pair]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
      rfl

lemma PhiR_hs_pair (N : QuantumChannel a b)
    (Y : Matrix (R × b) (R × b) ℂ) (Z : Matrix (R × a) (R × a) ℂ) :
    ((PhiR N Y)ᴴ * Z).trace = (Yᴴ * amp N Z).trace := by
  rw [← PhiR_star, PhiR_trace_pair]


end Adjoint
end D5.S3.Quantum.Divergence.UmegakiReferenceTransport
