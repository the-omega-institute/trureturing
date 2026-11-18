import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.BridgeGraph.RectangularBlockPartition
import Reg.Support.SingleDependentReadout

/-! The complete source telescope with the arbitrary-factor lower-bound observation. -/

namespace Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.RectangularBlockPartition

open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.RectangularBlockPartition
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped BigOperators Classical
noncomputable section
universe u v w z

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℕ) (fun _ => ℕ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law O := ∀ {X : Type u} {Y : Type v} {T : Type w}
    [Fintype X] [Fintype Y] [Fintype T] [DecidableEq X] [DecidableEq Y]
    (I : T → Finset X) (J : T → Finset Y)
    (φ : ∀ t, {y // y ∈ J t} ≃ {x // x ∈ I t})
    (_h : ∀ x y, ∃! t, x ∈ I t ∧ y ∈ J t),
    (operator I J φ)ᴴ * operator I J φ = 1 ∧
    operator I J φ * (operator I J φ)ᴴ = 1 ∧
    (realign (operator I J φ)).rank = Fintype.card (Active J) ∧
    operator I J φ =
      ∑ t : Active J, kronecker (block I J φ t.val) (block I J φ t.val)ᴴ ∧
    (∃ (rows : Active J → X × Y) (cols : Active J → Y × X),
      (realign (operator I J φ)).submatrix rows cols = 1) ∧
    ∀ (R : Type z) [Fintype R] (M : R → Matrix X Y ℂ) (N : R → Matrix Y X ℂ),
      operator I J φ = ∑ r, kronecker (M r) (N r) →
        O.readout () () (Fintype.card (Active J)) (Fintype.card R)

private theorem rejected_law : ¬ arena.{u,v,w,z}.Law rejected := by
  intro h
  let I : ULift.{w} Empty → Finset (ULift.{u} Empty) := fun t => nomatch t.down
  let J : ULift.{w} Empty → Finset (ULift.{v} Empty) := fun t => nomatch t.down
  let φ : ∀ t, {y // y ∈ J t} ≃ {x // x ∈ I t} := fun t => nomatch t.down
  have hp : ∀ x y, ∃! t, x ∈ I t ∧ y ∈ J t := fun x => nomatch x.down
  have hh := h I J φ hp
  exact hh.2.2.2.2.2 (ULift.{z} Empty)
    (fun r => nomatch r.down) (fun r => nomatch r.down)
    (by ext p; exact nomatch p.1.down)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  have hn : ¬ ((1 : ℕ) ≤ 0) := by omega
  exact hn (Eq.mp he (Nat.zero_le 0))

def family : Registration arena.{u,v,w,z}
    (type_of% @unitary_exact_width.{u,v,w,z}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@unitary_exact_width.{u,v,w,z}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@unitary_exact_width.{u,v,w,z}) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.BridgeGraph.RectangularBlockPartition.unitary_exact_width.information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.RectangularBlockPartition.family
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
    owner := `D5.S3.Quantum.TensorNetworks.BridgeGraph.RectangularBlockPartition
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "arg", "arg", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.RectangularBlockPartition
