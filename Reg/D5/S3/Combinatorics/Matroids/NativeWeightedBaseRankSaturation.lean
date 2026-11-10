import Reg.D5.S3.Combinatorics.Matroids.LocalSearchRobustness

/-! Source-bound audit of the exposed original single-exchange weight identity. -/

namespace Reg.D5.S3.Combinatorics.Matroids.NativeWeightedBaseRankSaturation

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Matroids.NativeWeightedBaseRankSaturation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Combinatorics.Matroids.LocalSearchRobustness
open Set

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {E : Type u} [hE : Finite E] (w : E → ℝ) {B : Set E} {e b : E}
    (_heB : e ∉ B) (_hbB : b ∈ B),
    R.readout () ⟨E,hE⟩ w (insert e (B \ {b})) = baseWeight w B - w b + w e

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h (E := ULift.{u} Bool) (fun _ => 0)
    (B := {ULift.up false}) (e := ULift.up true) (b := ULift.up false)
      (by simp) (by simp)
  norm_num [rejected,realize,baseWeight] at hh

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} Unit, inferInstance⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hh := congrFun h ({ULift.up ()} : Set (ULift.{u} Unit))
  norm_num [actual,realize,baseWeight] at hh

def source_registration : Registration arena.{u}
    (type_of% (@baseWeight_exchange.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@baseWeight_exchange, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
      (@baseWeight_exchange.{u}) (Realization signature.{u}) Type Unit where
  unitName := `D5.S3.Combinatorics.Matroids.NativeWeightedBaseRankSaturation.baseWeight_exchange.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.NativeWeightedBaseRankSaturation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Matroids.NativeWeightedBaseRankSaturation
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
end
end Reg.D5.S3.Combinatorics.Matroids.NativeWeightedBaseRankSaturation
