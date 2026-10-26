import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.MutualVisibility.Model
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Graph.MutualVisibility

universe u
namespace Reg.D5.S3.Combinatorics.Graph.MutualVisibility.Model

abbrev visibilitySignature : Signature where
  Params := Sigma fun V : Type u => DecidableEq V
  State p := SimpleGraph p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Finset p.1 → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def visibilityActual : Realization visibilitySignature :=
  realize visibilitySignature (fun _ p H S => @Visible p.1 p.2 H S) (fun e => nomatch e)

abbrev visibilityArena : Arena where
  signature := visibilitySignature
  Law r := ∀ p, letI := p.2; ∀ H S T, S ⊆ T → r.readout () p H T → r.readout () p H S

def monotonicityEvidence : Registration visibilityArena (type_of% (@visible_mono.{u})) where
  actual := visibilityActual
  bridge := by
    constructor
    · intro h p H S T hST hT
      exact @h p.1 p.2 H S T hST hT
    · intro h V inst H S T hST hT
      exact h ⟨V, inst⟩ H S T hST hT

noncomputable def registration : Contract.Registration (@visible_mono.{u})
    (type_of% (realize visibilitySignature
      (fun _ p H S => @Visible p.1 p.2 H S) (fun e => nomatch e)))
    (type_of% (@Visible.{u})) Unit := {
  unitName := `D5.S3.Combinatorics.Graph.MutualVisibility.visible_mono,
  realizationName := `Reg.D5.S3.Combinatorics.Graph.MutualVisibility.Model.monotonicityEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨visibilityArena⟩,
  objectArena := .source ⟨visibilityArena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source visibilityArena ⟨monotonicityEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize visibilitySignature
    (fun _ p H S => @Visible p.1 p.2 H S) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := some (@Visible.{u}),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[] }



abbrev visible_emptyArena : Arena where
  signature := visibilitySignature
  Law r := ∀ p, letI := p.2; ∀ H, r.readout () p H ∅

def visible_emptyEvidence : Registration visible_emptyArena (type_of% (@visible_empty.{u})) where
  actual := visibilityActual
  bridge := by
    constructor
    · intro h p H; exact @h p.1 p.2 H
    · intro h V inst H; exact h ⟨V, inst⟩ H

abbrev visible_singletonArena : Arena where
  signature := visibilitySignature
  Law r := ∀ p, letI := p.2; ∀ H x, r.readout () p H {x}

def visible_singletonEvidence : Registration visible_singletonArena (type_of% (@visible_singleton.{u})) where
  actual := visibilityActual
  bridge := by
    constructor
    · intro h p H x; exact @h p.1 p.2 H x
    · intro h V inst H x; exact h ⟨V, inst⟩ H x

abbrev visible_pairArena : Arena where
  signature := visibilitySignature
  Law r := ∀ p, letI := p.2; ∀ H, H.Connected → ∀ x y, r.readout () p H {x, y}

def visible_pairEvidence : Registration visible_pairArena (type_of% (@visible_pair.{u})) where
  actual := visibilityActual
  bridge := by
    constructor
    · intro h p H hH x y; exact @h p.1 p.2 H hH x y
    · intro h V inst H hH x y; exact h ⟨V, inst⟩ H hH x y

abbrev moveSignature : Signature where
  Params := Sigma fun V : Type u => DecidableEq V
  State p := SimpleGraph p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Finset p.1 → Finset p.1 → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def moveActual : Realization moveSignature :=
  realize moveSignature (fun _ p H S T => @MixedMove p.1 p.2 H S T) (fun e => nomatch e)

abbrev mixedMove_insertArena : Arena where
  signature := moveSignature
  Law r := ∀ p, letI := p.2; ∀ H S x, x ∉ S → r.readout () p H S (insert x S)

def mixedMove_insertEvidence : Registration mixedMove_insertArena (type_of% (@mixedMove_insert.{u})) where
  actual := moveActual
  bridge := by
    constructor
    · intro h p H S x hx; exact @h p.1 p.2 H S x hx
    · intro h V inst H S x hx; exact h ⟨V, inst⟩ H S x hx

abbrev mixedMove_eraseArena : Arena where
  signature := moveSignature
  Law r := ∀ p, letI := p.2; ∀ H S x, x ∈ S → r.readout () p H S (S.erase x)

def mixedMove_eraseEvidence : Registration mixedMove_eraseArena (type_of% (@mixedMove_erase.{u})) where
  actual := moveActual
  bridge := by
    constructor
    · intro h p H S x hx; exact @h p.1 p.2 H S x hx
    · intro h V inst H S x hx; exact h ⟨V, inst⟩ H S x hx

abbrev graphSignature : Signature where
  Params := Sigma fun V : Type u => DecidableEq V
  State p := SimpleGraph p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Sigma fun H : SimpleGraph p.1 => SimpleGraph (@Configuration p.1 p.2 H)
  Anchor := Empty
  finiteAnchor := inferInstance

def graphActual : Realization graphSignature :=
  realize graphSignature (fun _ p H => ⟨H, @reconfiguration p.1 p.2 H⟩) (fun e => nomatch e)

abbrev connectedArena : Arena where
  signature := graphSignature
  Law r := ∀ p, letI := p.2; ∀ H, (r.readout () p H).2.Connected

def connectedEvidence : Registration connectedArena (type_of% (@reconfiguration_connected.{u})) where
  actual := graphActual
  bridge := by
    constructor
    · intro h p H; exact @h p.1 p.2 H
    · intro h V inst H; exact h ⟨V, inst⟩ H



noncomputable def visible_emptyRegistration : Contract.Registration (@visible_empty.{u})
    (type_of% (visibilityActual)) (type_of% (@Visible.{u})) Unit := {
  unitName := `D5.S3.Combinatorics.Graph.MutualVisibility.visible_empty,
  realizationName := `Reg.D5.S3.Combinatorics.Graph.MutualVisibility.Model.visible_emptyEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨visible_emptyArena⟩, objectArena := .source ⟨visible_emptyArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source visible_emptyArena ⟨visible_emptyEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some visibilityActual,
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := some (@Visible.{u}), sourceSelection := none,
  continuation := .unknown, familyRecord := none, options := #[] }

noncomputable def visible_singletonRegistration : Contract.Registration (@visible_singleton.{u})
    (type_of% (visibilityActual)) (type_of% (@Visible.{u})) Unit := {
  unitName := `D5.S3.Combinatorics.Graph.MutualVisibility.visible_singleton,
  realizationName := `Reg.D5.S3.Combinatorics.Graph.MutualVisibility.Model.visible_singletonEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨visible_singletonArena⟩, objectArena := .source ⟨visible_singletonArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source visible_singletonArena ⟨visible_singletonEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some visibilityActual,
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := some (@Visible.{u}), sourceSelection := none,
  continuation := .unknown, familyRecord := none, options := #[] }

noncomputable def visible_pairRegistration : Contract.Registration (@visible_pair.{u})
    (type_of% (visibilityActual)) (type_of% (@Visible.{u})) Unit := {
  unitName := `D5.S3.Combinatorics.Graph.MutualVisibility.visible_pair,
  realizationName := `Reg.D5.S3.Combinatorics.Graph.MutualVisibility.Model.visible_pairEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨visible_pairArena⟩, objectArena := .source ⟨visible_pairArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source visible_pairArena ⟨visible_pairEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some visibilityActual,
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := some (@Visible.{u}), sourceSelection := none,
  continuation := .unknown, familyRecord := none, options := #[] }

noncomputable def mixedMove_insertRegistration : Contract.Registration (@mixedMove_insert.{u})
    (type_of% (moveActual)) (type_of% (@MixedMove.{u})) Unit := {
  unitName := `D5.S3.Combinatorics.Graph.MutualVisibility.mixedMove_insert,
  realizationName := `Reg.D5.S3.Combinatorics.Graph.MutualVisibility.Model.mixedMove_insertEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨mixedMove_insertArena⟩, objectArena := .source ⟨mixedMove_insertArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source mixedMove_insertArena ⟨mixedMove_insertEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some moveActual,
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := some (@MixedMove.{u}), sourceSelection := none,
  continuation := .unknown, familyRecord := none, options := #[] }

noncomputable def mixedMove_eraseRegistration : Contract.Registration (@mixedMove_erase.{u})
    (type_of% (moveActual)) (type_of% (@MixedMove.{u})) Unit := {
  unitName := `D5.S3.Combinatorics.Graph.MutualVisibility.mixedMove_erase,
  realizationName := `Reg.D5.S3.Combinatorics.Graph.MutualVisibility.Model.mixedMove_eraseEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨mixedMove_eraseArena⟩, objectArena := .source ⟨mixedMove_eraseArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source mixedMove_eraseArena ⟨mixedMove_eraseEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some moveActual,
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := some (@MixedMove.{u}), sourceSelection := none,
  continuation := .unknown, familyRecord := none, options := #[] }

noncomputable def reconfiguration_connectedRegistration : Contract.Registration (@reconfiguration_connected.{u})
    (type_of% (graphActual)) (type_of% (@reconfiguration.{u})) Unit := {
  unitName := `D5.S3.Combinatorics.Graph.MutualVisibility.reconfiguration_connected,
  realizationName := `Reg.D5.S3.Combinatorics.Graph.MutualVisibility.Model.connectedEvidence,
  realizationSource := none, generated := false,
  arena := .source ⟨connectedArena⟩, objectArena := .source ⟨connectedArena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source connectedArena ⟨connectedEvidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some graphActual,
  variation := .absent, sensitivity := .absent, partialSensitivity := none,
  escapeFrom := some (@reconfiguration.{u}), sourceSelection := none,
  continuation := .unknown, familyRecord := none, options := #[] }

end Reg.D5.S3.Combinatorics.Graph.MutualVisibility.Model
