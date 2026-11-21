import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Geometry.Ultrametric.MCDWeakSimilarity
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Combinatorics.Geometry.Ultrametric.MCDWeakSimilarity

open _root_.D5.S3.Combinatorics.Geometry.DovgosheyRovenskaCentralEdges (center)
open _root_.D5.S3.Combinatorics.Geometry.Ultrametric.MCDWeakSimilarity (WeaklySimilar)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- The original statement is retained; the readout observes the preserved center size. -/
abbrev arena : Arena where
  signature := signature
  Law Q :=
    (∀ {X Y : Type} [MetricSpace X] [IsUltrametricDist X] [Finite X]
      [MetricSpace Y] [IsUltrametricDist Y] [Finite Y],
      Nat.card X = 2 ^ ((center X).ncard - 1) → Nat.card Y = 2 ^ ((center Y).ncard - 1) →
      Nat.card X = Nat.card Y → WeaklySimilar X Y) ∧
    (∀ {X Y : Type} [MetricSpace X] [MetricSpace Y],
      WeaklySimilar X Y → Q.readout () () (center X).ncard (center Y).ncard) ∧
    (∀ {X Y : Type} [MetricSpace X] [IsUltrametricDist X] [Finite X]
      [MetricSpace Y] [IsUltrametricDist Y] [Finite Y] (h : ℕ),
      Nat.card X = 2 ^ h → Nat.card Y = 2 ^ h → (center X).ncard = h + 1 →
      ((center Y).ncard = h + 1 ↔ WeaklySimilar X Y))

private theorem rejected_law : ¬ arena.Law rejected := fun hlaw =>
  hlaw.2.1 (X := ℝ) (Y := ℝ) ⟨Equiv.refl ℝ, id, strictMono_id.strictMonoOn _, fun _ _ => rfl⟩

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 0, ?_⟩
  intro h
  have hh := congrFun h (0 : ℕ)
  norm_num [actual, realize] at hh

def family : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Geometry.Ultrametric.MCDWeakSimilarity.result))
    where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S3.Combinatorics.Geometry.Ultrametric.MCDWeakSimilarity.result, rejected,
      rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Combinatorics.Geometry.Ultrametric.MCDWeakSimilarity.result)
    (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.Geometry.Ultrametric.MCDWeakSimilarity.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Geometry.Ultrametric.MCDWeakSimilarity.family
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
    owner := `D5.S3.Combinatorics.Geometry.Ultrametric.MCDWeakSimilarity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "fn", "arg", "body", "body", "body", "body", "body", "fn", "fn"]
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
end Reg.D5.S3.Combinatorics.Geometry.Ultrametric.MCDWeakSimilarity
