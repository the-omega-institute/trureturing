import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Geometry.Ultrametric.FourCentralMinimum
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Combinatorics.Geometry.Ultrametric.FourCentralMinimum

open _root_.D5.S3.Combinatorics.Geometry.Ultrametric.FourCentralMinimum
open _root_.D5.S3.Combinatorics.Geometry.DovgosheyRovenskaCentralEdges
open _root_.D5.S3.Combinatorics.Geometry.CentralEdgeCover
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- The original statement is retained; the readout observes the lower bound on the number of
central edges. -/
abbrev arena : Arena where
  signature := signature
  Law Q := ∀ n : ℕ,
    (∀ (X : Type) [Fintype X] [MetricSpace X] [IsUltrametricDist X], Fintype.card X = n →
      Nat.card (center X) = 4 →
      8 ≤ n ∧ Q.readout () () (6 * n - 16 - 4 * (n / 4) + (n + 1) / 2)
          (centralGraph X).edgeFinset.card ∧
      ∀ a b D : ℝ, 0 < a → a < b → b < D → center X = {0, a, b, D} →
        (centralGraph X).edgeFinset.card =
          (lengthEdges X D).card + (lengthEdges X b).card + (lengthEdges X a).card ∧
        4 * (n - 4) ≤ (lengthEdges X D).card ∧ 2 * n - 4 * (n / 4) ≤ (lengthEdges X b).card ∧
        (n + 1) / 2 ≤ (lengthEdges X a).card) ∧
    (8 ≤ n → ∃ (X : Type) (_ : Fintype X) (_ : MetricSpace X) (_ : IsUltrametricDist X),
      Fintype.card X = n ∧ Nat.card (center X) = 4 ∧
      (centralGraph X).edgeFinset.card = 6 * n - 16 - 4 * (n / 4) + (n + 1) / 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨X, i1, i2, i3, hX, hk, -⟩ := (ultra_four_central_minimum 8).2 le_rfl
  exact (@(h 8).1 X i1 i2 i3 hX hk).2.1

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 0, ?_⟩
  intro h
  have hh := congrFun h (0 : ℕ)
  norm_num [actual, realize] at hh

def family : Registration arena (type_of% (@ultra_four_central_minimum)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@ultra_four_central_minimum, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@ultra_four_central_minimum) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.Geometry.Ultrametric.FourCentralMinimum.ultra_four_central_minimum.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Geometry.Ultrametric.FourCentralMinimum.family
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
    owner := `D5.S3.Combinatorics.Geometry.Ultrametric.FourCentralMinimum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "body", "body", "body", "body", "body", "body", "arg", "fn",
        "arg", "fn", "fn"]
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
end Reg.D5.S3.Combinatorics.Geometry.Ultrametric.FourCentralMinimum
