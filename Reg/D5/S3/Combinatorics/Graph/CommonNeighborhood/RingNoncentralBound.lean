import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.CommonNeighborhood.RingNoncentralBound
import Reg.Support.SingleDependentReadout
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Defs

namespace Reg.D5.S3.Combinatorics.Graph.CommonNeighborhood.RingNoncentralBound

open _root_.D5.S3.Combinatorics.Graph.CommonNeighborhood.RingNoncentralBound
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

/-- The original ring telescope is retained; the readout observes the per-vertex energy bound. -/
abbrev arena : Arena where
  signature := signature
  Law Q := ∀ (R : Type) [NonUnitalNonAssocRing R] [Fintype R],
    (∃ a b : R, a * b ≠ b * a) →
      1 ≤ Fintype.card (ringCenter R) ∧
      3 * Fintype.card (ringCenter R) ≤ Fintype.card (Vertex R) ∧
      Fintype.card (ringCenter R) + 2 ≤ Fintype.card (Vertex R) ∧
      3 ≤ Fintype.card (Vertex R) ∧
      Fintype.card (ringCenter R) ∣ Fintype.card (Vertex R) ∧
      Q.readout () () (graphEnergy (commutingGraph R) .commonNeighbour)
        (2 * ∑ x : Vertex R,
          max ((centralizerCard R x.val : ℝ) - Fintype.card (ringCenter R) - 2) 0) ∧
      2 * ∑ x : Vertex R,
          max ((centralizerCard R x.val : ℝ) - Fintype.card (ringCenter R) - 2) 0 ≤
        (Fintype.card (Vertex R) : ℝ) *
          max (2 * ((Fintype.card (Vertex R) : ℝ) + Fintype.card (ringCenter R)) /
              (Fintype.card R).minFac - 2 * Fintype.card (ringCenter R) - 4) 0 ∧
      (Fintype.card (Vertex R) : ℝ) *
          max (2 * ((Fintype.card (Vertex R) : ℝ) + Fintype.card (ringCenter R)) /
              (Fintype.card R).minFac - 2 * Fintype.card (ringCenter R) - 4) 0 ≤
        (Fintype.card (Vertex R) : ℝ) *
          max ((Fintype.card (Vertex R) : ℝ) - Fintype.card (ringCenter R) - 4) 0 ∧
      (Fintype.card (Vertex R) : ℝ) *
          max ((Fintype.card (Vertex R) : ℝ) - Fintype.card (ringCenter R) - 4) 0 ≤
        (Fintype.card (Vertex R) : ℝ) *
          ((Fintype.card (Vertex R) : ℝ) - Fintype.card (ringCenter R) - 2) ∧
      (Fintype.card (Vertex R) : ℝ) *
          ((Fintype.card (Vertex R) : ℝ) - Fintype.card (ringCenter R) - 2) <
        2 * ((Fintype.card (Vertex R) : ℝ) - 1) * ((Fintype.card (Vertex R) : ℝ) - 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro h
  have hn : ∃ a b : Matrix (Fin 2) (Fin 2) (ZMod 2), a * b ≠ b * a := by
    refine ⟨!![1, 0; 0, 0], !![0, 1; 0, 0], fun hab => ?_⟩
    have h01 := congrFun (congrFun hab 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h01
  exact (h (Matrix (Fin 2) (Fin 2) (ZMod 2)) hn).2.2.2.2.2.1

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
  unitName := `D5.S3.Combinatorics.Graph.CommonNeighborhood.RingNoncentralBound.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.CommonNeighborhood.RingNoncentralBound.family
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
    owner := `D5.S3.Combinatorics.Graph.CommonNeighborhood.RingNoncentralBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "fn", "arg",
        "fn", "fn"]
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
end Reg.D5.S3.Combinatorics.Graph.CommonNeighborhood.RingNoncentralBound
