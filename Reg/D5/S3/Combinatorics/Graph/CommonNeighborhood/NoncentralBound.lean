import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.CommonNeighborhood.NoncentralBound
import Reg.Support.SingleDependentReadout
import Mathlib.Data.Fintype.Perm

namespace Reg.D5.S3.Combinatorics.Graph.CommonNeighborhood.NoncentralBound

open _root_.D5.S3.Combinatorics.Graph.CommonNeighborhood.NoncentralBound
open _root_.D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation (graphEnergy)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- The original group telescope and both numerical operands are retained. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (G : Type) [Group G] [Fintype G],
    (∃ a b : G, a * b ≠ b * a) →
      R.readout () () (graphEnergy (commutingGraph G) .commonNeighbour)
        (2 * ((Fintype.card (Vertex G) : ℝ) - 1) *
          ((Fintype.card (Vertex G) : ℝ) - 2))

private theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro h
  have hn : ∃ a b : Equiv.Perm (Fin 3), a * b ≠ b * a := by
    refine ⟨Equiv.swap 0 1, Equiv.swap 1 2, ?_⟩
    decide
  exact h (Equiv.Perm (Fin 3)) hn

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have hh := congrFun h (0 : ℝ)
  norm_num [actual, realize] at hh

def family : Registration arena (type_of% (@result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@result) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.CommonNeighborhood.NoncentralBound.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.CommonNeighborhood.NoncentralBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.CommonNeighborhood.NoncentralBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end
end Reg.D5.S3.Combinatorics.Graph.CommonNeighborhood.NoncentralBound
