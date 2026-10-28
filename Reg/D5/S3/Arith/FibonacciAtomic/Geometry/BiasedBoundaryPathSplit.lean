import D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryPathSplit
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! The original strict suffix operator as a readout of the all-vector path split. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryPathSplit

open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryPathSplit
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryTrace (Omega M G J)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryConditionalLaw (pullback)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceHardy (Edge H)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory

abbrev signature : Signature where
  Params := Address
  State _ := H
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := H
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p z => S p z) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ (p : Address) (z : H) (u : Edge), R.readout () p z u = z (descendant p u)) ∧
    (∀ (p : Address) (z : H), ‖R.readout () p z‖ ≤ ‖z‖) ∧
    (∀ (p : Address) (z : H), prefixSum p z = ∑ u ∈ prefixes p, z u) ∧
    (∀ c : ℝ, constG c =ᵐ[M] (fun _ : Omega => c)) ∧
    (∀ (p : Address) (z : H),
      pullback p (J z) = constG (prefixSum p z) + J (R.readout () p z))

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : H)) (fun e => nomatch e)

private def edge : Edge := ⟨[false], by simp⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h.1 [] (lp.single 2 edge (1 : ℝ)) edge
  change 0 = (lp.single 2 edge (1 : ℝ) : H) edge at he
  simpa [lp.single_apply_self] using he

def familyRegistration : Registration arena (type_of% boundary_path_split) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨boundary_path_split, rejected, rejected_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨[], (0 : H), lp.single 2 edge (1 : ℝ), ?_⟩
    intro he
    have hh := congrArg (fun z : H => z edge) he
    change 0 = (lp.single 2 edge (1 : ℝ) : H) edge at hh
    simpa [lp.single_apply_self] using hh

def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@boundary_path_split)
    (type_of% (realize signature (fun _ p z => S p z) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryPathSplit.pathSplitUnit,
  realizationName :=
    `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryPathSplit.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p z => S p z) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryPathSplit,
    definition := none, coordinates := #[0],
    readouts := #[{
      path := #["arg", "fn", "arg", "body", "body", "fn", "arg", "arg"],
      stateBinder := 1, functionOperand := false, stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.BiasedBoundaryPathSplit
