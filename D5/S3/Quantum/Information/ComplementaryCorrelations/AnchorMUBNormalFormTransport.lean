/- GID: D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMUBNormalFormTransport
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/ComplementaryCorrelations/AnchorMUBNormalFormTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual anchor quadratic and its marginal-free directions transport under local unitaries. -/

import D5.S3.Quantum.Information.ComplementaryCorrelations.AnchorMUBNormalFormHadamard
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
import D5.S3.Quantum.Recovery.BKMSpectralVariance

/-! Covariance of Qian's readouts, resolvent quadratic form and anchor data. -/

noncomputable section

namespace AnchorMeasurement

open Matrix MeasureTheory
open scoped BigOperators Kronecker Matrix Matrix.Norms.L2Operator
open D5.S3.Divergence.LogDerivTrace (logDeriv)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition (DensityState)
open D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity (unitaryConjugateState)
open D5.S3.Quantum.Recovery.BKMSpectralVariance (trace_conjStarAlgAut_symm)

namespace MUBNormalForm

section OneBasis

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Each column of the first basis is a column of the second up to a unit phase,
with the columns matched by a permutation of outcomes. -/
def BasisRelabel (U V : Matrix.unitaryGroup n ℂ) : Prop :=
  ∃ (e : Equiv.Perm n) (c : n → ℂ), (∀ j, Complex.normSq (c j) = 1) ∧
    ∀ i j, (U : Mat n) i j = (V : Mat n) i (e j) * c j

private theorem readout_relabel (U V : Matrix.unitaryGroup n ℂ)
    (e : Equiv.Perm n) (c : n → ℂ) (hc : ∀ j, Complex.normSq (c j) = 1)
    (h : ∀ i j, (U : Mat n) i j = (V : Mat n) i (e j) * c j)
    (X : Mat n) (j : n) :
    readout U X j = readout V X (e j) := by
  have hleft (k : n) :
      ((U : Mat n)ᴴ * X) j k = star (c j) * ((V : Mat n)ᴴ * X) (e j) k := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, h, star_mul,
      Finset.mul_sum, mul_assoc]
  have hdiag :
      ((U : Mat n)ᴴ * X * (U : Mat n)) j j =
        ((V : Mat n)ᴴ * X * (V : Mat n)) (e j) (e j) := by
    calc
      _ = ∑ k, ((U : Mat n)ᴴ * X) j k * (U : Mat n) k j := rfl
      _ = ∑ k, star (c j) * (((V : Mat n)ᴴ * X) (e j) k * (V : Mat n) k (e j)) * c j := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hleft, h]
        ring
      _ = star (c j) * (((V : Mat n)ᴴ * X * (V : Mat n)) (e j) (e j)) * c j := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]; rfl
      _ = (c j * star (c j)) * (((V : Mat n)ᴴ * X * (V : Mat n)) (e j) (e j)) := by
        ring
      _ = _ := by rw [phase_mul_star (hc j), one_mul]
  exact congrArg Complex.re hdiag

private theorem inBasis_mul (W U : Matrix.unitaryGroup n ℂ) (X : Mat n) :
    inBasis (W * U) X = inBasis U (inBasis W X) := by
  change star ((W : Mat n) * (U : Mat n)) * X * (W * U : Mat n) =
    star (U : Mat n) * (star (W : Mat n) * X * (W : Mat n)) * (U : Mat n)
  rw [star_mul]
  noncomm_ring

attribute [-instance] instTopologicalSpaceMatrix Matrix.instUniformSpace in
/-- Unitary covariance of the actual resolvent integral, using the continuous
real-linear equivalence on the finite matrix space. -/
theorem logDeriv_inBasis (U : Matrix.unitaryGroup n ℂ) (S D : Mat n) :
    inBasis U (logDeriv S D) = logDeriv (inBasis U S) (inBasis U D) := by
  let F := (Unitary.conjStarAlgAut ℝ (Mat n) U).symm
  let E := F.toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv
  have hU : (U : Mat n)⁻¹ = star (U : Mat n) := by
    apply Matrix.inv_eq_right_inv
    exact Unitary.coe_mul_star_self U
  have hUstar : (star (U : Mat n))⁻¹ = (U : Mat n) := by
    apply Matrix.inv_eq_right_inv
    exact Unitary.coe_star_mul_self U
  have hinv (X : Mat n) : F X⁻¹ = (F X)⁻¹ := by
    change star (U : Mat n) * X⁻¹ * (U : Mat n) =
      (star (U : Mat n) * X * (U : Mat n))⁻¹
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hU, hUstar, Matrix.mul_assoc]
  unfold D5.S3.Divergence.LogDerivTrace.logDeriv
  change E (∫ t in Set.Ioi (0 : ℝ), (S + t • 1)⁻¹ * D * (S + t • 1)⁻¹) =
    ∫ t in Set.Ioi (0 : ℝ), (F S + t • 1)⁻¹ * F D * (F S + t • 1)⁻¹
  rw [← E.integral_comp_comm]
  apply integral_congr_ae
  filter_upwards [] with t
  change F ((S + t • 1)⁻¹ * D * (S + t • 1)⁻¹) = _
  simp only [map_mul, hinv, map_add, map_smul, map_one]

private theorem trace_inBasis (U : Matrix.unitaryGroup n ℂ) (X : Mat n) :
    (inBasis U X).trace = X.trace :=
  trace_conjStarAlgAut_symm U X

/-- BKM inverse-metric quadratic form, with the same trace and logarithmic
derivative as in the staged anchor quadratic expression. -/
theorem bkmQuadratic_inBasis (U : Matrix.unitaryGroup n ℂ) (S D : Mat n) :
    (inBasis U D * logDeriv (inBasis U S) (inBasis U D)).trace.re =
      (D * logDeriv S D).trace.re := by
  rw [← logDeriv_inBasis]
  have hmul : inBasis U D * inBasis U (logDeriv S D) = inBasis U (D * logDeriv S D) :=
    (map_mul (Unitary.conjStarAlgAut ℂ (Mat n) U).symm D (logDeriv S D)).symm
  rw [hmul, trace_inBasis]

/-- The same density operator after changing coordinates by the given basis. -/
def stateInBasis (W : Matrix.unitaryGroup n ℂ) (ρ : DensityState n) : DensityState n :=
  unitaryConjugateState (star W : Matrix.unitaryGroup n ℂ).val
    (star W : Matrix.unitaryGroup n ℂ).property ρ

theorem densityMatrix_stateInBasis (W : Matrix.unitaryGroup n ℂ) (ρ : DensityState n) :
    densityMatrix (stateInBasis W ρ) = inBasis W (densityMatrix ρ) := by
  change (star (W : Mat n)) * densityMatrix ρ * star (star (W : Mat n)) =
    (star (W : Mat n)) * densityMatrix ρ * (W : Mat n)
  rw [star_star]

end OneBasis

section ProductBasis

private theorem productBasis_mul
    (W U : Matrix.unitaryGroup Alice ℂ) (Z V : Matrix.unitaryGroup Bob ℂ) :
    productBasis (W * U) (Z * V) = productBasis W Z * productBasis U V := by
  apply Subtype.ext
  change (((W : Mat Alice) * (U : Mat Alice)) ⊗ₖ ((Z : Mat Bob) * (V : Mat Bob))) =
    ((W : Mat Alice) ⊗ₖ (Z : Mat Bob)) * ((U : Mat Alice) ⊗ₖ (V : Mat Bob))
  rw [Matrix.mul_kronecker_mul]

theorem productBasis_relabel
    {U U' : Matrix.unitaryGroup Alice ℂ} {V V' : Matrix.unitaryGroup Bob ℂ}
    (hU : BasisRelabel U U') (hV : BasisRelabel V V') :
    BasisRelabel (productBasis U V) (productBasis U' V') := by
  obtain ⟨e, a, ha, h⟩ := hU
  obtain ⟨f, b, hb, k⟩ := hV
  refine ⟨e.prodCongr f, (fun j => a j.1 * b j.2), ?_, ?_⟩
  · intro j
    simp [Complex.normSq_mul, ha, hb]
  · intro i j
    change (U : Mat Alice) i.1 j.1 * (V : Mat Bob) i.2 j.2 =
      ((U' : Mat Alice) i.1 (e j.1) * (V' : Mat Bob) i.2 (f j.2)) * (a j.1 * b j.2)
    rw [h, k]
    ring

theorem measurementFisher_relabel
    {U U' : Matrix.unitaryGroup Alice ℂ} {V V' : Matrix.unitaryGroup Bob ℂ}
    (hU : BasisRelabel U U') (hV : BasisRelabel V V') (S D : JointMatrix) :
    measurementFisher U V S D = measurementFisher U' V' S D := by
  obtain ⟨e, c, hc, h⟩ := productBasis_relabel hU hV
  simp only [measurementFisher, readout_relabel _ _ e c hc h]
  exact Equiv.sum_comp e (fun j =>
    readout (productBasis U' V') D j ^ 2 / readout (productBasis U' V') S j)

theorem measurementFisher_local_inBasis
    (W U : Matrix.unitaryGroup Alice ℂ) (Z V : Matrix.unitaryGroup Bob ℂ)
    (S D : JointMatrix) :
    measurementFisher (W * U) (Z * V) S D =
      measurementFisher U V (inBasis (productBasis W Z) S) (inBasis (productBasis W Z) D) := by
  simp only [measurementFisher, readout, productBasis_mul, inBasis_mul]

theorem productState_inBasis
    (W : Matrix.unitaryGroup Alice ℂ) (Z : Matrix.unitaryGroup Bob ℂ)
    (α : DensityState Alice) (β : DensityState Bob) :
    densityMatrix (productState (stateInBasis W α) (stateInBasis Z β)) =
      inBasis (productBasis W Z) (densityMatrix (productState α β)) := by
  change densityMatrix (stateInBasis W α) ⊗ₖ densityMatrix (stateInBasis Z β) =
    inBasis (productBasis W Z) (densityMatrix α ⊗ₖ densityMatrix β)
  rw [inBasis_product, densityMatrix_stateInBasis, densityMatrix_stateInBasis]

theorem marginalFree_inBasis
    (W : Matrix.unitaryGroup Alice ℂ) (Z : Matrix.unitaryGroup Bob ℂ)
    {D : JointMatrix} (hD : MarginalFree D) :
    MarginalFree (inBasis (productBasis W Z) D) := by
  refine ⟨?_, ?_, ?_⟩
  · let F := (Unitary.conjStarAlgAut ℂ (Mat Joint) (productBasis W Z)).symm
    change star (F D) = F D
    rw [← map_star, hD.1.star_eq]
  · rw [partialTraceRight_inBasis, hD.2.1]
    exact map_zero (Unitary.conjStarAlgAut ℂ (Mat Alice) W).symm
  · rw [partialTraceLeft_inBasis, hD.2.2]
    exact map_zero (Unitary.conjStarAlgAut ℂ (Mat Bob) Z).symm

/-- Both settings may independently relabel and rephase their outcomes.
The two local coordinate changes act jointly on the actual anchor and tangent. -/
theorem anchorQuadraticIn_normalForm
    (W : Matrix.unitaryGroup Alice ℂ) (Z : Matrix.unitaryGroup Bob ℂ)
    {UQ UR UQ' UR' : Matrix.unitaryGroup Alice ℂ}
    {VQ VR VQ' VR' : Matrix.unitaryGroup Bob ℂ}
    (hUQ : BasisRelabel UQ (W * UQ')) (hUR : BasisRelabel UR (W * UR'))
    (hVQ : BasisRelabel VQ (Z * VQ')) (hVR : BasisRelabel VR (Z * VR'))
    (α : DensityState Alice) (β : DensityState Bob) (D : JointMatrix) :
    anchorQuadraticIn UQ UR VQ VR α β D =
      anchorQuadraticIn UQ' UR' VQ' VR' (stateInBasis W α) (stateInBasis Z β)
        (inBasis (productBasis W Z) D) := by
  simp only [anchorQuadraticIn, productState_inBasis,
    bkmQuadratic_inBasis,
    measurementFisher_relabel hUQ hVQ, measurementFisher_relabel hUR hVR,
    measurementFisher_local_inBasis]

end ProductBasis

end MUBNormalForm
end AnchorMeasurement
