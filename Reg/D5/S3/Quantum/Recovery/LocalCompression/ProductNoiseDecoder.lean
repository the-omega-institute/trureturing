import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Recovery.LocalCompression.ProductNoiseDecoder

/-! Source-bound observation of the finite joint trace-distance comparison. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Quantum.Recovery.LocalCompression.ProductNoiseDecoder

open LeanInformationAudit Matrix
open scoped CStarAlgebra ComplexOrder MatrixOrder Kronecker
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Foundation.FinitePreparationChannel (finite_preparation_quantum_channel)
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm traceDistance)
open _root_.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (act amp)
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation (marginalRight productState)
open _root_.D5.S3.Quantum.Recovery.LocalCompression.ProductNoiseDecoder
open UnitaryReconstruction.GibbsHiddenProcess (mix identity reset)

universe ur ub um

private abbrev raw {n : Type*} [Fintype n] [DecidableEq n] (ρ : DensityState n) :
    Matrix n n ℂ := CStarMatrix.ofMatrix.symm ρ.1

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law F := ∀ {R : Type ur} {B : Type ub} {M : Type um}
    [Fintype R] [DecidableEq R] [Fintype B] [DecidableEq B] [Fintype M] [DecidableEq M],
    ∀
    (E : QuantumChannel B M) (D : QuantumChannel M B)
    (τ : DensityState B) (_hτ : (CStarMatrix.ofMatrix.symm τ.1).PosDef)
    (_hfix : (D.comp E).mapState τ = τ)
    (K : Matrix B B ℂ) (_hK : K.IsHermitian) (_htr : K.trace = 0),
    ∃ (L : ℝ) (hL : 0 < L) (σ : DensityState B),
      CStarMatrix.ofMatrix.symm σ.1 = CStarMatrix.ofMatrix.symm τ.1 - L⁻¹ • K ∧
      ∀ (ε : ℝ) (hε : 0 < ε) (_hε' : ε ≤ 1) (hp : ε * L ≤ 1),
        let T := D.comp E
        let Dε := (mix (ε * L) (mul_nonneg hε.le hL.le) hp
          (reset σ) identity).comp D
        let Tε := Dε.comp E
        act Tε (CStarMatrix.ofMatrix.symm τ.1) = CStarMatrix.ofMatrix.symm τ.1 - ε • K ∧
        ∀ (ω : DensityState R) (ρ : DensityState (R × B)),
          let ρR : DensityState R := marginalRight ρ
          let X := (1 - ε) • (raw ω ⊗ₖ raw τ) + ε • raw ρ
          let H := raw ρ - amp T (raw ρ) + raw ω ⊗ₖ K
          let Hε := ε⁻¹ • (X - amp Tε X)
          Hε = H + (ε * L) • (amp T (raw ρ) - raw ρR ⊗ₖ raw τ) +
              ε • ((raw ρR - raw ω) ⊗ₖ K) ∧
          F.readout () () (traceNorm (Hε - H) / 2)
            (ε * (L + traceDistance ρR ω * traceNorm K))

private abbrev Q := ULift Unit

private def singletonDensity : DensityState Q.{ub} :=
  ⟨CStarMatrix.ofMatrix 1, map_nonneg CStarMatrix.ofMatrixStarAlgEquiv zero_le_one, by
    change (1 : Matrix Q Q ℂ).trace = 1
    simp [Matrix.trace]⟩

private lemma singletonDensity_unique (τ : DensityState Q.{ub}) : τ = singletonDensity := by
  apply Subtype.ext
  apply CStarMatrix.ext
  intro i j
  have hij : j = i := Subsingleton.elim _ _
  subst j
  have ht := τ.trace_eq_one
  have hi : i = default := Subsingleton.elim _ _
  subst i
  change τ.1 default default = 1
  change (∑ i : Q, τ.1 i i) = 1 at ht
  simpa using ht

private theorem rejected_law : ¬ arena.{ur, ub, um}.Law rejected := by
  intro h
  let τ : DensityState Q.{ub} := singletonDensity
  let ω : DensityState Q.{ur} := singletonDensity
  obtain ⟨E, _⟩ := finite_preparation_quantum_channel (fun _ : Q.{ub} => singletonDensity.{um})
  obtain ⟨D, _⟩ := finite_preparation_quantum_channel (fun _ : Q.{um} => τ)
  have hτ : (raw τ).PosDef := Matrix.PosDef.one
  obtain ⟨L, hL, σ, _, hbound⟩ :=
    @h Q.{ur} Q.{ub} Q.{um} _ _ _ _ _ _ E D τ hτ
      (singletonDensity_unique _) 0 Matrix.isHermitian_zero (by simp)
  let ε : ℝ := min 1 L⁻¹
  have hε : 0 < ε := lt_min zero_lt_one (inv_pos.mpr hL)
  have hp : ε * L ≤ 1 := by
    convert mul_le_mul_of_nonneg_right (min_le_right (1 : ℝ) L⁻¹) hL.le using 1
    rw [inv_mul_cancel₀ hL.ne']
  exact (hbound ε hε (min_le_left _ _) hp).2 ω (productState ω τ) |>.2

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he : ((0 : ℝ) ≤ 0) = ((1 : ℝ) ≤ 0) := congrFun h 0
  exact (not_le_of_gt zero_lt_one) (he.mp le_rfl)

def decoderShiftFamily : Registration arena.{ur, ub, um}
    (type_of% @faithful_decoder_marginal_shift.{ur, ub, um}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@faithful_decoder_marginal_shift, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

set_option linter.style.longLine false in
def decoderShiftAudit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@faithful_decoder_marginal_shift.{ur, ub, um}) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Recovery.LocalCompression.ProductNoiseDecoder.faithful_decoder_marginal_shift.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.LocalCompression.ProductNoiseDecoder.decoderShiftFamily
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{ur, ub, um}⟩
  objectArena := .source ⟨arena.{ur, ub, um}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{ur, ub, um} ⟨decoderShiftFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.LocalCompression.ProductNoiseDecoder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "body", "arg",
        "body", "body", "body", "body", "body", "body", "body", "arg",
        "body", "body", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Recovery.LocalCompression.ProductNoiseDecoder
