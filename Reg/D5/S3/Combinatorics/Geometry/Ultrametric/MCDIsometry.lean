import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Geometry.Ultrametric.MCDIsometry
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Combinatorics.Geometry.Ultrametric.MCDIsometry

open _root_.D5.S3.Combinatorics.Geometry.DovgosheyRovenskaCentralEdges (center)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Set ℝ)
    (fun _ => Set ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- The original statement is retained; the readout observes the equality of centers. -/
abbrev arena : Arena where
  signature := signature
  Law Q :=
    ∀ {X Y : Type} [MetricSpace X] [IsUltrametricDist X] [Finite X]
      [MetricSpace Y] [IsUltrametricDist Y] [Finite Y],
      Nat.card X = 2 ^ ((center X).ncard - 1) →
      (Nat.card X = Nat.card Y ∨ Nat.card Y = 2 ^ ((center Y).ncard - 1)) →
      (Q.readout () () (center X) (center Y) ↔ Nonempty (X ≃ᵢ Y))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hlaw
  obtain ⟨X, hF, hM, hU, -, hC, hcard⟩ :=
    ((_root_.D5.S3.Combinatorics.Geometry.UltrametricCenterMinimumOrder.result {0}).2
      (Finset.mem_singleton_self 0) (by simp)).2
  have hX : Nat.card X = 2 ^ ((center X).ncard - 1) := by
    rw [hC, Set.ncard_coe_finset, Nat.card_eq_fintype_card, hcard]
  exact (hlaw (X := X) (Y := X) hX (Or.inl rfl)).mpr ⟨IsometryEquiv.refl X⟩

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (Set.univ : Set ℝ), (∅ : Set ℝ), ?_⟩
  intro h
  have hh := congrFun h (∅ : Set ℝ)
  simp [actual, realize] at hh

def family : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Geometry.Ultrametric.MCDIsometry.result))
    where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S3.Combinatorics.Geometry.Ultrametric.MCDIsometry.result, rejected,
      rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Geometry.Ultrametric.MCDIsometry.result)
    (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.Geometry.Ultrametric.MCDIsometry.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Geometry.Ultrametric.MCDIsometry.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Geometry.Ultrametric.MCDIsometry
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "fn"]
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
end Reg.D5.S3.Combinatorics.Geometry.Ultrametric.MCDIsometry
