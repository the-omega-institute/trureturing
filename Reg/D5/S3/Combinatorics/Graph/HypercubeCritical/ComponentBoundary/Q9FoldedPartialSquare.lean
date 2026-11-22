import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedPartialSquare

/-! The centre row readout observes the vertex switch. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedPartialSquare

open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedPartialSquare
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSignedRows
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

private abbrev centerSignature.{u} : Signature where
  Params := Σ V : Type u, Σ _ : V → Finset V, Σ _ : Signing V, V
  State p := p.1 → ZMod 2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

private def centerActual.{u} : Realization centerSignature.{u} :=
  realize centerSignature (fun _ p z => rowSum p.2.1 p.2.2.1 z p.2.2.2) Empty.elim

private def centerRejected.{u} : Realization centerSignature.{u} :=
  realize centerSignature (fun _ _ _ => 0) Empty.elim

private abbrev centerArena.{u} : Arena where
  signature := centerSignature.{u}
  Law R := ∀ {V : Type u} [DecidableEq V]
    (neighbors : V → Finset V) (s : Signing V) (z : V → ZMod 2)
    (u b : V) (c d : Fin 3 → V) (target : ℤ),
    (∀ i, s.bit b (d i) = s.bit (d i) b ∧ s.bit (c i) u = s.bit u (c i)) →
    b ∈ neighbors u → (∀ i, c i ∈ neighbors u) →
    (∀ i, b ≠ c i) → Function.Injective c →
    (∀ i, neighbors (d i) = {b, c i}) →
    (∀ i, s.bit u b + s.bit b (d i) + s.bit (d i) (c i) + s.bit (c i) u = 1) →
    (∀ i, rowSum neighbors s z (d i) = 0) →
    (neighbors u).card ≤ 5 → |target| ≤ 2 →
    R.readout () ⟨V, neighbors, s, u⟩ z ≠ target

private abbrev Site.{u} := ULift.{u} (Fin 8)

private def neighborsFixture.{u} (v : Site.{u}) : Finset Site.{u} :=
  if v.down = 0 then {⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩}
  else if v.down = 1 then {⟨0⟩, ⟨5⟩, ⟨6⟩, ⟨7⟩}
  else if v.down = 2 then {⟨0⟩, ⟨5⟩}
  else if v.down = 3 then {⟨0⟩, ⟨6⟩}
  else if v.down = 4 then {⟨0⟩, ⟨7⟩}
  else if v.down = 5 then {⟨1⟩, ⟨2⟩}
  else if v.down = 6 then {⟨1⟩, ⟨3⟩}
  else {⟨1⟩, ⟨4⟩}

private def signingFixture.{u} : Signing Site.{u} :=
  ⟨fun x y => if x.down.val ∈ Finset.Icc 2 4 ∧ y.down.val = x.down.val + 3 ∨
      y.down.val ∈ Finset.Icc 2 4 ∧ x.down.val = y.down.val + 3 then 1 else 0⟩

private def side.{u} (i : Fin 3) : Site.{u} := ⟨⟨i.val + 2, by omega⟩⟩

private def corner.{u} (i : Fin 3) : Site.{u} := ⟨⟨i.val + 5, by omega⟩⟩

private theorem centerRejected_law.{u} : ¬ centerArena.{u}.Law centerRejected.{u} := by
  intro h
  have bad := h neighborsFixture.{u} signingFixture (fun _ => 0) ⟨0⟩ ⟨1⟩ side corner 0
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
  exact bad rfl

def centerEvidence.{u} : Registration centerArena.{u}
    (type_of% (@three_negative_squares_obstruct_row.{u})) where
  actual := centerActual
  bridge := Iff.rfl
  variation := ⟨three_negative_squares_obstruct_row, centerRejected, centerRejected_law⟩
  sensitivity := by
    constructor
    · intro role
      exact ⟨centerRejected, fun other h => (h (Subsingleton.elim other role)).elim,
        rfl, centerRejected_law⟩
    · intro anchor
      exact nomatch anchor
  dependence := by
    rintro ⟨⟩
    refine ⟨⟨ULift.{u} Bool, fun _ => {⟨true⟩}, ⟨fun _ _ => 0⟩, ⟨false⟩⟩,
      (fun _ => 0), (fun v => if v.down then 1 else 0), ?_⟩
    decide

def centerRegistration.{u} : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@three_negative_squares_obstruct_row.{u}) (Realization centerSignature.{u}) Unit Unit where
  unitName :=
    `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedPartialSquare.three_negative_squares_obstruct_row.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedPartialSquare.centerEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨centerArena.{u}⟩
  objectArena := .source ⟨centerArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source centerArena.{u} ⟨centerEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize centerSignature.{u}
    (fun _ p z => rowSum p.2.1 p.2.2.1 z p.2.2.2) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedPartialSquare
    definition := none
    coordinates := #[0, 2, 3, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedPartialSquare
