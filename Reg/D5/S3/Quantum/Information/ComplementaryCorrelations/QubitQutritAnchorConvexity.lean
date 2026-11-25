import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Information.ComplementaryCorrelations.QubitQutritAnchorConvexity

/-! Read the anchor quadratic on the actual variation for a fixed product and basis pairs. -/

namespace Reg.D5.S3.Quantum.Information.ComplementaryCorrelations.QubitQutritAnchorConvexity

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
open _root_.D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition (DensityState)
open _root_.D5.S3.Divergence.LogDerivTrace (logDeriv trace_mul_logDeriv)
open AnchorMeasurement AnchorMeasurement.MUBNormalForm LeanInformationAudit Matrix
open scoped ComplexOrder MatrixOrder Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

private abbrev Parameters :=
  Matrix.unitaryGroup Alice ℂ × Matrix.unitaryGroup Alice ℂ ×
    Matrix.unitaryGroup Bob ℂ × Matrix.unitaryGroup Bob ℂ × DensityState Alice × DensityState Bob

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Parameters (fun _ => JointMatrix) (fun _ => ℝ)

private def actual : Realization signature :=
  realize signature (fun _ p D =>
    anchorQuadraticIn p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 D)
    (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (UQ UR : Matrix.unitaryGroup Alice ℂ) (VQ VR : Matrix.unitaryGroup Bob ℂ),
    (∀ i j, Complex.normSq (((UQ : Mat Alice)ᴴ * (UR : Mat Alice)) i j) = (1 / 2 : ℝ)) →
    (∀ i j, Complex.normSq (((VQ : Mat Bob)ᴴ * (VR : Mat Bob)) i j) = (1 / 3 : ℝ)) →
    ∀ (α : DensityState Alice) (β : DensityState Bob),
      (densityMatrix α).PosDef → (densityMatrix β).PosDef →
      ∀ D : JointMatrix, MarginalFree D → 0 ≤ R.readout () (UQ, UR, VQ, VR, α, β) D

private theorem uniform_posDef (n : Type) [Fintype n] [DecidableEq n] [Nonempty n] :
    (Matrix.diagonal fun _ : n => ((Fintype.card n : ℂ)⁻¹)).PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  have hc : (0 : ℝ) < Fintype.card n := Nat.cast_pos.mpr Fintype.card_pos
  exact Complex.pos_iff.mpr ⟨by simpa [← Complex.ofReal_inv] using inv_pos.mpr hc, by simp⟩

private def uniform (n : Type) [Fintype n] [DecidableEq n] [Nonempty n] : DensityState n :=
  ⟨CStarMatrix.ofMatrix (Matrix.diagonal fun _ : n => ((Fintype.card n : ℂ)⁻¹)),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (uniform_posDef n).posSemidef.nonneg, by
      change (Matrix.diagonal fun _ : n => ((Fintype.card n : ℂ)⁻¹)).trace = 1
      simp [Matrix.trace_diagonal, nsmul_eq_mul, Nat.cast_ne_zero.mpr Fintype.card_ne_zero]⟩

open private scaled_aliceR_entry scaled_bobR_entry from
  D5.S3.Quantum.Information.ComplementaryCorrelations.AnchorMUBNormalFormHadamard

private theorem normSq_of_scaled {n : Type} {m : ℕ} {H : Mat n}
    {i j : n} (h : Complex.normSq (scaled m H i j) = 1) :
    Complex.normSq (H i j) = (m : ℝ)⁻¹ := by
  have hm : (m : ℝ) * Complex.normSq (H i j) = 1 := by
    simpa only [scaled, Matrix.smul_apply, smul_eq_mul, Complex.normSq_mul,
      Complex.normSq_ofReal, Real.mul_self_sqrt (Nat.cast_nonneg m)] using h
  have hm0 : (m : ℝ) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hm
    exact zero_ne_one hm
  apply mul_left_cancel₀ hm0
  rw [hm, mul_inv_cancel₀ hm0]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hA : ∀ i j, Complex.normSq (((1 : Mat Alice)ᴴ * (aliceR : Mat Alice)) i j) =
      (1 / 2 : ℝ) := by
    intro i j
    rw [Matrix.conjTranspose_one, Matrix.one_mul, one_div]
    apply normSq_of_scaled (m := 2)
    rw [scaled_aliceR_entry]
    split <;> simp
  have hB : ∀ i j, Complex.normSq (((1 : Mat Bob)ᴴ * (bobR : Mat Bob)) i j) =
      (1 / 3 : ℝ) := by
    intro i j
    rw [Matrix.conjTranspose_one, Matrix.one_mul, one_div]
    apply normSq_of_scaled (m := 3)
    rw [scaled_bobR_entry]
    exact Circle.normSq_coe (ZMod.toCircle (-(i * j)))
  have hzero : MarginalFree 0 := by
    refine ⟨Matrix.isHermitian_zero, ?_, ?_⟩
    · ext i j
      simp [partialTraceRight]
    · ext i j
      simp [partialTraceLeft]
  have hbad := h 1 aliceR 1 bobR hA hB (uniform Alice) (uniform Bob)
    (uniform_posDef Alice) (uniform_posDef Bob) 0 hzero
  exact (by norm_num : ¬ (0 : ℝ) ≤ -1) hbad

open private trace_inBasis from
  D5.S3.Quantum.Information.ComplementaryCorrelations.AnchorMUBNormalFormTransport

private theorem fisher_self (U : Matrix.unitaryGroup Alice ℂ) (V : Matrix.unitaryGroup Bob ℂ)
    (S : JointMatrix) (hS : S.PosDef) (htr : S.trace = 1) :
    measurementFisher U V S S = 1 := by
  unfold measurementFisher
  have he (i : Joint) : readout (productBasis U V) S i ^ 2 /
      readout (productBasis U V) S i = readout (productBasis U V) S i := by
    field_simp [(readout_pos (productBasis U V) hS i).ne']
  simp only [he]
  unfold readout
  have h := congrArg Complex.re ((trace_inBasis (productBasis U V) S).trans htr)
  simpa only [Matrix.trace, Matrix.diag_apply, Complex.re_sum, Complex.one_re] using h

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let α := uniform Alice
  let β := uniform Bob
  let S := densityMatrix (productState α β)
  have hS := productMatrix_posDef α β (uniform_posDef Alice) (uniform_posDef Bob)
  have htr : S.trace = 1 := (productState α β).2.2
  refine ⟨(1, aliceR, 1, bobR, α, β), 0, S, ?_⟩
  change anchorQuadraticIn 1 aliceR 1 bobR α β 0 ≠ anchorQuadraticIn 1 aliceR 1 bobR α β S
  have hz : anchorQuadraticIn 1 aliceR 1 bobR α β 0 = 0 := by
    simp [anchorQuadraticIn, measurementFisher, readout, inBasis]
  have ht := trace_mul_logDeriv S S hS hS.isHermitian
  rw [hz]
  change (0 : ℝ) ≠ (S * logDeriv S S).trace.re - measurementFisher 1 1 S S -
    measurementFisher aliceR bobR S S
  rw [ht, htr, fisher_self 1 1 S hS htr, fisher_self aliceR bobR S hS htr]
  norm_num

def family : Registration arena (type_of% @qubit_qutrit_anchor_convexity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@qubit_qutrit_anchor_convexity, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@qubit_qutrit_anchor_convexity) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Information.ComplementaryCorrelations.QubitQutritAnchorConvexity.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Information.ComplementaryCorrelations.QubitQutritAnchorConvexity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p D =>
    anchorQuadraticIn p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2 D)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.ComplementaryCorrelations.QubitQutritAnchorConvexity
    definition := some {
      owner := `D5.S3.Quantum.Information.ComplementaryCorrelations.AnchorMeasurement
      name := `AnchorMeasurement.ACC₂₃AllBases
      path := #[] }
    coordinates := #[0, 1, 2, 3, 6, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Quantum.Information.ComplementaryCorrelations.QubitQutritAnchorConvexity
