import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.ConditionalExpansion.FilteredBellRestriction

/-! Source equivalence for the three-dimensional filtered-channel counterexample. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

noncomputable section

open Matrix LeanInformationAudit
open scoped CStarAlgebra ComplexOrder MatrixOrder
open _root_.FilteredBellRestriction (threeByTwoFilter threeByTwo_strict_bell_bound)
open _root_.FilteredChannelConditionalGap (filterAction)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (act ratios)
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel (QuantumChannel)
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceLeft)
open RHLinalg (rtrace)

namespace Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.FilteredBellRestriction

open _root_.Reg.Support.SingleDependentReadout (signature sensitivity)

private abbrev observation := signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization observation :=
  realize observation (fun _ _ x y => x < y) (fun e => nomatch e)

private def rejected : Realization observation :=
  realize observation (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := observation
  Law R := ∃ N : QuantumChannel (Bool ⊕ Unit) ((Bool ⊕ Unit) × Bool),
    (∀ X, act N X = filterAction threeByTwoFilter X) ∧
    sInf (ratios N 1 false) = 3 / 4 ∧
    rtrace (((Fintype.card (Bool ⊕ Unit) : ℝ)⁻¹ • partialTraceLeft threeByTwoFilter⁻¹)⁻¹) /
      Fintype.card Bool = 9 / 11 ∧
    R.readout () () (sInf (ratios N 1 false))
      (rtrace (((Fintype.card (Bool ⊕ Unit) : ℝ)⁻¹ • partialTraceLeft threeByTwoFilter⁻¹)⁻¹) /
        Fintype.card Bool)

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨_, _, _, _, h⟩
  exact h

private theorem dependence : ObservationalDependence observation actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hbad := congrFun he 1
  norm_num [actual, realize] at hbad

def family : Registration arena (type_of% @threeByTwo_strict_bell_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@threeByTwo_strict_bell_bound, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@threeByTwo_strict_bell_bound) (Realization observation) Unit Unit where
  unitName := `FilteredBellRestriction.threeByTwo_strict_bell_bound.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.FilteredBellRestriction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize observation (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.ConditionalExpansion.FilteredBellRestriction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.FilteredBellRestriction
