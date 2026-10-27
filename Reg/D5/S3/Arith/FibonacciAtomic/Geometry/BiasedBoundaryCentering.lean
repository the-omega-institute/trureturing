import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCentering
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! The actual mean as a readout in the complete centered suffix family. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCentering

open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCentering
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryPathSplit (constG S)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrace (Omega M G)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryConditionalLaw (pullback)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceHardy (H)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory

abbrev signature : Signature where
  Params := Unit
  State _ := G
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ F => mean F) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ F : G, R.readout () () F = ∫ ω, F ω ∂M) ∧
    (∀ c : ℝ, R.readout () () (constG c) = c) ∧
    (∀ F : G, Pi F = F-constG (R.readout () () F)) ∧
    (∀ F : G, ‖Pi F‖ ≤ ‖F‖) ∧
    (∀ (p : Address) (z : H), Pi (pullback p (C z)) = C (S p z)) ∧
    (∀ (p : Address) (z : H),
      ‖Pi (pullback p (C z))‖^2 ≤ Real.goldenRatio*‖S p z‖^2)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h.2.1 (1:ℝ)
  change (0:ℝ) = 1 at he
  norm_num at he

def familyRegistration : Registration arena (type_of% centered_suffix_residual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨centered_suffix_residual, rejected, rejected_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), constG 0, constG 1, ?_⟩
    change mean (constG 0) ≠ mean (constG 1)
    rw [centered_suffix_residual.2.1, centered_suffix_residual.2.1]
    norm_num

def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@centered_suffix_residual)
    (type_of% (realize signature (fun _ _ F => mean F) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCentering.centeringUnit,
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCentering.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ F => mean F) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCentering,
    definition := none, coordinates := #[],
    readouts := #[{
      path := #["fn", "arg", "body", "fn", "arg"],
      stateBinder := 0, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryCentering
