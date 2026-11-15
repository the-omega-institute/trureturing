import D5.S3.Quantum.Algebra.PositiveWordRayDescent
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Full infinite-word transport family and its genuine readout intervention. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Algebra.PositiveWordRayDescent

noncomputable section
namespace Reg.D5.S3.Quantum.Algebra.PositiveWordRayDescent.Transport

abbrev signature : Signature where
  Params := Law
  State _ := Word
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Row
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ L a => L.row a) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ a => BoundedContinuousFunction.const Coordinate (a.length : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law F := ∀ (L : Law), L.R10 → ∀ a b,
    dist (F.readout () L a) (F.readout () L b) =
      dist (F.readout () L (a ++ inverseWord b)) (F.readout () L [])

private def zeroLaw : Law := ⟨fun _ => 0, fun _ => ⟨le_rfl, zero_le_one⟩⟩

private theorem const_distance (x y : ℝ) :
    dist (BoundedContinuousFunction.const Coordinate x)
      (BoundedContinuousFunction.const Coordinate y) = dist x y := by
  apply le_antisymm
  · exact (BoundedContinuousFunction.dist_le dist_nonneg).2 (fun _ => le_rfl)
  · exact BoundedContinuousFunction.dist_coe_le_dist
      (f := BoundedContinuousFunction.const Coordinate x)
      (g := BoundedContinuousFunction.const Coordinate y) none

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : zeroLaw.R10 := fun _ _ _ => rfl
  have hh := h zeroLaw hz [] [0]
  have hh' : dist (BoundedContinuousFunction.const Coordinate (0 : ℝ))
      (BoundedContinuousFunction.const Coordinate 1) =
    dist (BoundedContinuousFunction.const Coordinate (9 : ℝ))
      (BoundedContinuousFunction.const Coordinate 0) := by
    simpa [rejected, realize, inverseWord] using hh
  norm_num [const_distance, Real.dist_eq] at hh'

private def separatingLaw : Law where
  probability a := if a = [] then 0 else 1
  bounds a := by split_ifs <;> norm_num

/-- Whole-family reconstruction and intervention; raw occurrence binding is separate. -/
def family : Registration arena (type_of% (@row_return_transport)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨row_return_transport, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨separatingLaw, [], [0], ?_⟩
    intro heq
    have hh := congrArg (fun z : Row => z (some [])) heq
    norm_num [actual, realize, Law.row, Law.value, separatingLaw] at hh

/-- Whole-family evidence without a raw source-selection descriptor. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@row_return_transport) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Algebra.PositiveWordRayDescent.row_return_transport.information_unit
  realizationName := `Reg.D5.S3.Quantum.Algebra.PositiveWordRayDescent.Transport.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ L a => L.row a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Algebra.PositiveWordRayDescent.Transport
