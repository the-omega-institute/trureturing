import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Combinatorics.Geometry.RowmotionIncomparableToggles
import Mathlib.Order.ULift

/-! A source-bound audit of incomparable interval-closed toggles. -/

namespace Reg.D5.S3.Combinatorics.Geometry.RowmotionIncomparableToggles
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Geometry.RowmotionEndpointTransport
open _root_.D5.S3.Combinatorics.Geometry.RowmotionIncomparableToggles
open scoped symmDiff
noncomputable section
universe u

abbrev Inputs := Σ P : Type u, Σ _ : PartialOrder P, P
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Inputs
  (fun p => Set p.1) (fun p => Set p.1)

/-- The original toggle readout retains its source partial-order instance. -/
def observed : ∀ (i : signature.{u}.Role) (p : signature.{u}.Params),
    signature.{u}.State p → signature.{u}.Output i p :=
  fun _ p => letI := p.2.1; toggle p.2.2

def noAnchor : ∀ (e : signature.{u}.Anchor) (p : signature.{u}.Params), signature.{u}.State p :=
  fun e => Empty.elim e

def actual : Realization signature := realize signature.{u} observed.{u} noAnchor.{u}

def rejected : Realization signature := realize signature
  (fun _ p _ => {p.2.2}) (fun e => Empty.elim e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {P : Type u} [order : PartialOrder P] (x y : P),
    ¬ x ≤ y → ¬ y ≤ x → ∀ (S : Set P), S.OrdConnected →
    R.readout () ⟨P, order, x⟩ (toggle y S) = toggle y (toggle x S)

/-- This order is used only to test intervention and actual dependence. -/
@[instance_reducible] def equalityOrder (P : Type u) : PartialOrder P where
  le := Eq
  le_refl _ := rfl
  le_trans _ _ _ := Eq.trans
  le_antisymm _ _ h _ := h

theorem equalityOrder_connected {P : Type u} (S : Set P) :
    @Set.OrdConnected P (equalityOrder P).toPreorder S := by
  apply (@Set.ordConnected_def P (equalityOrder P).toPreorder S).mpr
  intro a ha b hb z hz
  exact (show a = z from hz.1) ▸ ha

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let P := ULift.{u} Bool
  let x : P := ⟨false⟩
  let y : P := ⟨true⟩
  have hxy : ¬ @LE.le P (equalityOrder P).toPreorder.toLE x y := by
    change ¬ (x = y)
    intro he
    have bad := congrArg ULift.down he
    cases bad
  have hyx : ¬ @LE.le P (equalityOrder P).toPreorder.toLE y x := by
    change ¬ (y = x)
    intro he
    have bad := congrArg ULift.down he
    cases bad
  have bad := @h P (equalityOrder P) x y hxy hyx ∅ (equalityOrder_connected ∅)
  have member := congrArg (fun T : Set P => y ∈ T) bad
  simp [rejected, realize, toggle, equalityOrder_connected, Set.mem_symmDiff,
    x, y] at member

theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  classical
  intro _
  let P := ULift.{u} Unit
  let x : P := ⟨()⟩
  refine ⟨⟨P, equalityOrder P, x⟩, ∅, Set.univ, ?_⟩
  change @toggle P (equalityOrder P) x ∅ ≠ @toggle P (equalityOrder P) x Set.univ
  intro h
  have member := congrArg (fun T : Set P => x ∈ T) h
  simp [toggle, equalityOrder_connected, Set.mem_symmDiff] at member

def source_registration :
    Registration arena.{u} (type_of% @incomparable_toggles_commute.{u}) where
  actual := realize signature.{u} observed.{u} noAnchor.{u}
  bridge := Iff.rfl
  variation := ⟨@incomparable_toggles_commute.{u}, rejected, rejected_fails⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@incomparable_toggles_commute.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Geometry.RowmotionIncomparableToggles.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Geometry.RowmotionIncomparableToggles.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} observed.{u} noAnchor.{u})
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Geometry.RowmotionIncomparableToggles
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace FlipOtherAudit

abbrev Inputs := Σ P : Type u, Σ _ : P, P
abbrev signature : Signature := Reg.Support.UniverseSingleReadout.signature Inputs
  (fun p => Set p.1) (fun _ => Bool)

def observed : ∀ (i : signature.{u}.Role) (p : signature.{u}.Params),
    signature.{u}.State p → signature.{u}.Output i p := by
  classical
  exact fun _ p S => decide (p.2.2 ∈ S ∆ {p.2.1})

def noAnchor : ∀ (e : signature.{u}.Anchor) (p : signature.{u}.Params),
    signature.{u}.State p := fun e => Empty.elim e

def actual : Realization signature := realize signature.{u} observed.{u} noAnchor.{u}
def rejected : Realization signature := realize signature
  (fun _ _ _ => true) (fun e => Empty.elim e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {P : Type u} (S : Set P) (x z : P), z ≠ x →
    (R.readout () ⟨P, x, z⟩ S = true ↔ z ∈ S)

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  intro h
  let P := ULift.{u} Bool
  let x : P := ⟨false⟩
  let z : P := ⟨true⟩
  have hzx : z ≠ x := by
    intro he
    have bad := congrArg ULift.down he
    cases bad
  have bad := @h P ∅ x z hzx
  simp [rejected, realize] at bad

private theorem actual_dependence : ObservationalDependence signature.{u} actual := by
  classical
  intro _
  let P := ULift.{u} Unit
  let x : P := ⟨()⟩
  refine ⟨⟨P, x, x⟩, ∅, Set.univ, ?_⟩
  change decide (x ∈ (∅ : Set P) ∆ {x}) ≠ decide (x ∈ (Set.univ : Set P) ∆ {x})
  simp [Set.mem_symmDiff]

def source_registration : Registration arena.{u} (type_of% @flip_other.{u}) where
  actual := realize signature.{u} observed.{u} noAnchor.{u}
  bridge := by simp [arena, realize, observed]
  variation := ⟨by
    intro P S x z hzx
    simpa [realize, observed] using (@flip_other P S x z hzx),
    rejected, rejected_fails⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@flip_other.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Geometry.RowmotionIncomparableToggles.flip_other_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Geometry.RowmotionIncomparableToggles.FlipOtherAudit.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} observed.{u} noAnchor.{u})
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Geometry.RowmotionIncomparableToggles
    definition := none
    coordinates := #[0, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FlipOtherAudit

namespace ToggleConnectedAudit

def rejected : Realization signature := realize signature
  (fun _ p S => S ∆ {p.2.2}) (fun e => Empty.elim e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {P : Type u} [order : PartialOrder P] (x : P) {S : Set P},
    S.OrdConnected → (R.readout () ⟨P, order, x⟩ S).OrdConnected

private theorem rejected_fails : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let P := ULift.{u} ℕ
  let x : P := ⟨0⟩
  let z : P := ⟨1⟩
  let t : P := ⟨2⟩
  have bad := @h P inferInstance x {t} Set.ordConnected_singleton
  change (({t} : Set P) ∆ {x}).OrdConnected at bad
  have hx : x ∈ ({t} : Set P) ∆ {x} := by simp [Set.mem_symmDiff, x, t]
  have ht : t ∈ ({t} : Set P) ∆ {x} := by simp [Set.mem_symmDiff, x, t]
  have hz : z ∈ ({t} : Set P) ∆ {x} :=
    bad.out hx ht (show x ≤ z ∧ z ≤ t from by
      change (0 : ℕ) ≤ 1 ∧ (1 : ℕ) ≤ 2
      decide)
  simp [Set.mem_symmDiff, x, z, t] at hz

def source_registration :
    Registration arena.{u} (type_of% @toggle_connected.{u}) where
  actual := realize signature.{u} observed.{u} noAnchor.{u}
  bridge := Iff.rfl
  variation := ⟨@toggle_connected.{u}, rejected, rejected_fails⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := actual_dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@toggle_connected.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Geometry.RowmotionIncomparableToggles.toggle_connected_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Geometry.RowmotionIncomparableToggles.ToggleConnectedAudit.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} observed.{u} noAnchor.{u})
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Geometry.RowmotionIncomparableToggles
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ToggleConnectedAudit

end
end Reg.D5.S3.Combinatorics.Geometry.RowmotionIncomparableToggles
