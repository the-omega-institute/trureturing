import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.TripartiteH1Repair
import Reg.Support.DependentFamily

noncomputable section
namespace Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair
open _root_.D5.S3.Combinatorics.Graph.TripartiteH1Repair
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u v w

abbrev AParams : Type (max (u + 1) (max (v + 1) (w + 1))) :=
  Σ A : Type u, Σ B : Type v, Type w
abbrev ASig : Signature where
  Params := AParams.{u, v, w}
  State p := Potential p.1 p.2.1 p.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Edge p.1 p.2.1 p.2.2
  Anchor := Empty
  finiteAnchor := inferInstance

def aActual : Realization ASig.{u, v, w} :=
  realize ASig.{u, v, w} (fun _ _ g => d0 g) (fun e => nomatch e)
def aRejected : Realization ASig.{u, v, w} :=
  realize ASig.{u, v, w} (fun _ _ _ => 0) (fun e => nomatch e)

def aArena : Arena where
  signature := ASig.{u, v, w}
  Law r := ∀ {A : Type u} {B : Type v} {C : Type w} [Nonempty A] [Nonempty B] [Nonempty C]
    (f : Edge A B C),
    (∀ a b c, d1 f a b c = 0) ↔
      ∃ g : Potential A B C, r.readout () ⟨A, ⟨B, C⟩⟩ g = f

theorem aRejectedLaw : ¬ aArena.{u, v, w}.Law aRejected.{u, v, w} := by
  intro h
  let A := ULift.{u} Unit
  let B := ULift.{v} Unit
  let C := ULift.{w} Unit
  let f : Edge A B C := (fun _ _ => 1, fun _ _ => 1, fun _ _ => 0)
  have hz : ∀ a b c, d1 f a b c = 0 := by
    intro a b c
    simp [f, d1, CharTwo.add_self_eq_zero]
  obtain ⟨g, hg⟩ := (h f).mp hz
  have hv := congrArg (fun e : Edge A B C => e.1 (ULift.up ()) (ULift.up ())) hg
  simpa [aRejected, realize, f] using hv

theorem aDependence : ObservationalDependence ASig.{u, v, w} aActual.{u, v, w} := by
  intro i
  let A := ULift.{u} Unit
  let B := ULift.{v} Unit
  let C := ULift.{w} Unit
  let p : AParams := ⟨A, ⟨B, C⟩⟩
  let g0 : Potential A B C := (fun _ => 0, fun _ => 0, fun _ => 0)
  let g1 : Potential A B C := (fun _ => 1, fun _ => 0, fun _ => 0)
  refine ⟨p, g0, g1, ?_⟩
  intro h
  have hv := congrArg (fun e : Edge A B C => e.1 (ULift.up ()) (ULift.up ())) h
  simpa [aActual, realize, p, g0, g1, d0] using hv

def aRegistration : Registration aArena.{u, v, w} (aArena.{u, v, w}.Law aActual.{u, v, w}) where
  actual := aActual
  bridge := Iff.rfl
  variation := ⟨ker_d1_eq_im_d0, aRejected, aRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨aRejected, ?_, rfl, aRejectedLaw⟩
      intro j h
      cases i
      cases j
      exact (h rfl).elim
    · intro i
      exact nomatch i
  dependence := aDependence

noncomputable def registration_1.{u_1, u_2, u_3} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Combinatorics.Graph.TripartiteH1Repair.ker_d1_eq_im_d0.{u_1, u_2, u_3}) (type_of% (realize.{max (max (u_1 + 1) (u_2 + 1)) (u_3 + 1), max (max u_1 u_2) u_3, 0, max (max u_1 u_2) u_3, 0} ASig.{u_1, u_2, u_3} (fun _ _ g => d0.{u_1, u_2, u_3} g) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Combinatorics") "Graph") "TripartiteH1Repair") "ker_d1_eq_im_d0") "Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair/Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.aArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.aRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(aArena.{u_1, u_2, u_3})⟩,
  objectArena := .source ⟨(aArena.{u_1, u_2, u_3})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (aArena.{u_1, u_2, u_3}) ⟨(aRegistration.{u_1, u_2, u_3})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{max (max (u_1 + 1) (u_2 + 1)) (u_3 + 1), max (max u_1 u_2) u_3, 0, max (max u_1 u_2) u_3, 0} ASig.{u_1, u_2, u_3} (fun _ _ g => d0.{u_1, u_2, u_3} g) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Combinatorics.Graph.TripartiteH1Repair, definition := none, coordinates := #[0, 1, 2], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg", "body", "fn", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `D5.S3.Combinatorics.Graph.TripartiteH1Repair.ker_d1_eq_im_d0, part := .type, path := [], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] }], facts := [`Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_1.canonicalArenaFact, `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_1.sourceBridgeFact, `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_1.observationFact0, `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_1.anchorEnumeration }


abbrev BSig : Signature where
  Params := Unit
  State _ := BitEdge
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def bActual : Realization BSig :=
  realize BSig (fun _ _ f => weight f) (fun e => nomatch e)
def bRejected : Realization BSig :=
  realize BSig (fun _ _ _ => 0) (fun e => nomatch e)

def bArena : Arena where
  signature := BSig
  Law r :=
    (∀ (f : BitEdge) (x : Cube),
      (∀ a b c, d1 f a b c ≠ 0 ↔
        (a, b, c) = x ∨ (a, b, c) = antipode x) →
      let w := cubePath x (antipode x)
      (∀ g : BitPotential, 3 ≤ weight (f + d0 g)) ∧
      (∃ g : BitPotential, f + d0 g = w) ∧
      (∀ a b, w.1 a b ≠ 0 ↔ a = !x.1 ∧ b = !x.2.1) ∧
      (∀ a c, w.2.1 a c ≠ 0 ↔ a = !x.1 ∧ c = x.2.2) ∧
      (∀ b c, w.2.2 b c ≠ 0 ↔ b = x.2.1 ∧ c = x.2.2) ∧
      (∀ a b c, d1 w a b c ≠ 0 ↔
        (a, b, c) = x ∨ (a, b, c) = antipode x) ∧
      weight w = 3 ∧ defects w = 2) ∧
    (∀ a b, witness.1 a b ≠ 0 ↔ a = false ∧ b = true) ∧
    (∀ a c, witness.2.1 a c ≠ 0 ↔ a = false ∧ c = false) ∧
    (∀ b c, witness.2.2 b c ≠ 0 ↔ b = false ∧ c = false) ∧
    (∀ a b c, d1 witness a b c ≠ 0 ↔
      (a, b, c) = (false, true, true) ∨
      (a, b, c) = (true, false, false)) ∧
    weight witness = 3 ∧ defects witness = 2 ∧
    (∀ g : BitPotential, 3 ≤ r.readout () () (witness + d0 g))

theorem bRejectedLaw : ¬ bArena.Law bRejected := by
  intro h
  have hf := h.2.2.2.2.2.2.2 (0 : BitPotential)
  simpa [bRejected, realize] using hf

theorem bDependence : ObservationalDependence BSig bActual := by
  intro i
  refine ⟨(), 0, witness, ?_⟩
  intro h
  have hw := congrArg id h
  simpa [bActual, realize, weight, witness] using hw

def bRegistration : Registration bArena (bArena.Law bActual) where
  actual := bActual
  bridge := Iff.rfl
  variation := ⟨sharp_three_edge_witness, bRejected, bRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bRejected, ?_, rfl, bRejectedLaw⟩
      intro j h
      cases i
      cases j
      exact (h rfl).elim
    · intro i
      exact nomatch i
  dependence := bDependence

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Combinatorics.Graph.TripartiteH1Repair.sharp_three_edge_witness) (type_of% (realize.{0, 0, 0, 0, 0} BSig (fun _ _ f => weight f) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Combinatorics") "Graph") "TripartiteH1Repair") "sharp_three_edge_witness") "Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair/Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.bArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.bRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(bArena)⟩,
  objectArena := .source ⟨(bArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (bArena) ⟨(bRegistration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} BSig (fun _ _ f => weight f) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Combinatorics.Graph.TripartiteH1Repair, definition := none, coordinates := #[], readouts := #[{ path := #["arg", "arg", "arg", "arg", "arg", "arg", "arg", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `D5.S3.Combinatorics.Graph.TripartiteH1Repair.sharp_three_edge_witness, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_2.canonicalArenaFact, `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_2.canonicalObjectArenaFact, `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_2.sourceBridgeFact, `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_2.observationFact0, `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_2.anchorEnumeration }


abbrev CSig : Signature where
  Params := Unit
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def cActual : Realization CSig := realize CSig (fun _ _ n => 3 * n) (fun e => nomatch e)
def cRejected : Realization CSig := realize CSig (fun _ _ _ => 0) (fun e => nomatch e)

def cArena : Arena where
  signature := CSig
  Law r := ∀ p q : Nat,
    (∀ f : BitEdge, ∃ g : BitPotential,
      q * weight (f + d0 g) ≤ p * defects f) ↔
      r.readout () () q ≤ 2 * p

theorem cRejectedLaw : ¬ cArena.Law cRejected := by
  intro h
  have hp := (h 0 1).mpr (by simp [cRejected, realize])
  have bad := (universal_repair 0 1).mp hp
  norm_num at bad

theorem cDependence : ObservationalDependence CSig cActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [cActual, realize]

def cRegistration : Registration cArena (cArena.Law cActual) where
  actual := cActual
  bridge := Iff.rfl
  variation := ⟨universal_repair, cRejected, cRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨cRejected, ?_, rfl, cRejectedLaw⟩
      intro j h
      cases i
      cases j
      exact (h rfl).elim
    · intro i
      exact nomatch i
  dependence := cDependence

noncomputable def registration_3 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Combinatorics.Graph.TripartiteH1Repair.universal_repair) (type_of% (realize.{0, 0, 0, 0, 0} CSig (fun _ _ n => 3 * n) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Combinatorics") "Graph") "TripartiteH1Repair") "universal_repair") "Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair/Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.cArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.cRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(cArena)⟩,
  objectArena := .source ⟨(cArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (cArena) ⟨(cRegistration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} CSig (fun _ _ n => 3 * n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Combinatorics.Graph.TripartiteH1Repair, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `D5.S3.Combinatorics.Graph.TripartiteH1Repair.universal_repair, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_3.canonicalArenaFact, `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_3.canonicalObjectArenaFact, `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_3.sourceBridgeFact, `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_3.observationFact0, `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_3.descriptorFact] },
  exclusion := some `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_3.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_3.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_3.anchorEnumeration }


#print axioms aRegistration
#print axioms bRegistration
#print axioms cRegistration
end Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair


noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_1.canonicalArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (max (u_1 + 1) (u_2 + 1)) (u_3 + 1),
  max (max u_1 u_2) u_3, 0, max (max u_1 u_2) u_3, 0} :=
  Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.aArena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_1.canonicalArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence
noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_1.canonicalObjectArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (max (u_1 + 1) (u_2 + 1)) (u_3 + 1),
  max (max u_1 u_2) u_3, 0, max (max u_1 u_2) u_3, 0} :=
  Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.aArena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_1.canonicalObjectArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence

noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_2.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.bArena
noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_2.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_2.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.bArena
noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_2.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_3.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.cArena
noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_3.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"registration_3\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_3.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_3.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.cArena
noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_3.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"registration_3\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_3.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_1.sourceLaw.{u_1, u_2, u_3} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{max (max (u_1 + 1) (u_2 + 1)) (u_3 + 1),
    max (max u_1 u_2) u_3, 0, max (max u_1 u_2) u_3, 0}
  Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.aArena.{u_1, u_2, u_3}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{max (max (u_1 + 1) (u_2 + 1))
          (u_3 + 1),
        max (max u_1 u_2) u_3, 0, max (max u_1 u_2) u_3, 0}
    Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.aArena.{u_1, u_2, u_3}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{max (max (u_1 + 1) (u_2 + 1)) (u_3 + 1),
        max (max u_1 u_2) u_3, 0, max (max u_1 u_2) u_3, 0}
      Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.aArena.{u_1, u_2, u_3}
      Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.aActual.{u_1, u_2, u_3})
    Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.aRegistration.{u_1, u_2, u_3})

noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_1.sourceBridgeFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"ker_d1_eq_im_d0\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `D5.S3.Combinatorics.Graph.TripartiteH1Repair.ker_d1_eq_im_d0, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{max (max (u_1 + 1) (u_2 + 1)) (u_3 + 1),
      max (max u_1 u_2) u_3, 0, max (max u_1 u_2) u_3, 0}
  Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.aArena.{u_1, u_2, u_3}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{max (max (u_1 + 1) (u_2 + 1)) (u_3 + 1),
      max (max u_1 u_2) u_3, 0, max (max u_1 u_2) u_3, 0}
    Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.aArena.{u_1, u_2, u_3}
    Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.aActual.{u_1, u_2, u_3})
  Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.aRegistration.{u_1, u_2, u_3})

noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_1.observation0.{u_1, u_2, u_3} : {A : Type u_1} →
  {B : Type u_2} →
    {C : Type u_3} →
      [Nonempty.{u_1 + 1} A] →
        [Nonempty.{u_2 + 1} B] →
          [Nonempty.{u_3 + 1} C] →
            (f : D5.S3.Combinatorics.Graph.TripartiteH1Repair.Edge.{u_1, u_2, u_3} A B C) →
              (g : D5.S3.Combinatorics.Graph.TripartiteH1Repair.Potential.{u_1, u_2, u_3} A B C) →
                D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.State.{max (max (u_1 + 1) (u_2 + 1))
                        (u_3 + 1),
                      max (max u_1 u_2) u_3, 0, max (max u_1 u_2) u_3, 0}
                    Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.ASig.{u_1, u_2, u_3}
                    (@Sigma.mk.{u_1 + 1, max (u_3 + 1) (u_2 + 1)} (Type u_1)
                      (fun (A : Type u_1) => @Sigma.{u_2 + 1, u_3 + 1} (Type u_2) fun (B : Type u_2) => Type u_3) A
                      (@Sigma.mk.{u_2 + 1, u_3 + 1} (Type u_2) (fun (B : Type u_2) => Type u_3) B C)) →
                  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{max
                        (max (u_1 + 1) (u_2 + 1)) (u_3 + 1),
                      max (max u_1 u_2) u_3, 0, max (max u_1 u_2) u_3, 0}
                    Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.ASig.{u_1, u_2, u_3} PUnit.unit.{1}
                    (@Sigma.mk.{u_1 + 1, max (u_3 + 1) (u_2 + 1)} (Type u_1)
                      (fun (A : Type u_1) => @Sigma.{u_2 + 1, u_3 + 1} (Type u_2) fun (B : Type u_2) => Type u_3) A
                      (@Sigma.mk.{u_2 + 1, u_3 + 1} (Type u_2) (fun (B : Type u_2) => Type u_3) B C)) :=
  fun {A : Type u_1} {B : Type u_2} {C : Type u_3} [Nonempty.{u_1 + 1} A] [Nonempty.{u_2 + 1} B] [Nonempty.{u_3 + 1} C]
    (f : D5.S3.Combinatorics.Graph.TripartiteH1Repair.Edge.{u_1, u_2, u_3} A B C)
    (g : D5.S3.Combinatorics.Graph.TripartiteH1Repair.Potential.{u_1, u_2, u_3} A B C) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{max (max (u_1 + 1) (u_2 + 1)) (u_3 + 1),
        max (max u_1 u_2) u_3, 0, max (max u_1 u_2) u_3, 0}
    Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.ASig.{u_1, u_2, u_3}
    Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.aActual.{u_1, u_2, u_3} PUnit.unit.{1}
    (@Sigma.mk.{u_1 + 1, max (u_3 + 1) (u_2 + 1)} (Type u_1)
      (fun (A : Type u_1) => @Sigma.{u_2 + 1, u_3 + 1} (Type u_2) fun (B : Type u_2) => Type u_3) A
      (@Sigma.mk.{u_2 + 1, u_3 + 1} (Type u_2) (fun (B : Type u_2) => Type u_3) B C))

noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_1.observationFact0.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"ker_d1_eq_im_d0\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"body\",\"function\",\"argument\",\"function\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `D5.S3.Combinatorics.Graph.TripartiteH1Repair.ker_d1_eq_im_d0, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .argument, .argument, .body, .function, .argument, .function], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_1.varyingLawInput.{u_1, u_2, u_3} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_1.canonicalArenaOperand.{u_1, u_2, u_3})
noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_1.varyingLaw.{u_1, u_2, u_3}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"

noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_1.statementExclusion.{u_1, u_2, u_3} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"ker_d1_eq_im_d0\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  statementLocation := { owner := `D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `D5.S3.Combinatorics.Graph.TripartiteH1Repair.ker_d1_eq_im_d0, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.aRegistration.{u_1, u_2, u_3}).actual (Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.aRegistration.{u_1, u_2, u_3}).variation.2.choose (Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.aRegistration.{u_1, u_2, u_3}).variation.1 (Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.aRegistration.{u_1, u_2, u_3}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_1.descriptorFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"aRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.aRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_2.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.bArena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.bArena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.bArena Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.bActual)
    Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.bRegistration)

noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_2.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"sharp_three_edge_witness\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `D5.S3.Combinatorics.Graph.TripartiteH1Repair.sharp_three_edge_witness, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_2.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.bArena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.bArena Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.bActual)
  Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.bRegistration)

noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_2.observation0 : (g : D5.S3.Combinatorics.Graph.TripartiteH1Repair.BitPotential) →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
    Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.BSig PUnit.unit.{1} PUnit.unit.{1} :=
  fun (g : D5.S3.Combinatorics.Graph.TripartiteH1Repair.BitPotential) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.BSig Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.bActual
    PUnit.unit.{1} PUnit.unit.{1}
    (@HAdd.hAdd.{0, 0, 0} D5.S3.Combinatorics.Graph.TripartiteH1Repair.BitEdge
      (D5.S3.Combinatorics.Graph.TripartiteH1Repair.Edge.{0, 0, 0} Bool Bool Bool)
      D5.S3.Combinatorics.Graph.TripartiteH1Repair.BitEdge
      (@instHAdd.{0} D5.S3.Combinatorics.Graph.TripartiteH1Repair.BitEdge
        (@Prod.instAdd.{0, 0} (Bool → Bool → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Prod.{0, 0} (Bool → Bool → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Bool → Bool → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@Pi.instAdd.{0, 0} Bool
            (fun (a : Bool) => Bool → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            fun (i : Bool) =>
            @Pi.instAdd.{0, 0} Bool
              (fun (a : Bool) => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun (i : Bool) =>
              @Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@instDistribOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@DivisionSemiring.toSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@Semifield.toDivisionSemiring.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          Nat.fact_prime_two))))))
          (@Prod.instAdd.{0, 0} (Bool → Bool → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Bool → Bool → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@Pi.instAdd.{0, 0} Bool
              (fun (a : Bool) => Bool → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              fun (i : Bool) =>
              @Pi.instAdd.{0, 0} Bool
                (fun (a : Bool) => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun (i : Bool) =>
                @Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@instDistribOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@DivisionSemiring.toSemiring.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Semifield.toDivisionSemiring.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            Nat.fact_prime_two))))))
            (@Pi.instAdd.{0, 0} Bool
              (fun (a : Bool) => Bool → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              fun (i : Bool) =>
              @Pi.instAdd.{0, 0} Bool
                (fun (a : Bool) => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun (i : Bool) =>
                @Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@instDistribOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@DivisionSemiring.toSemiring.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Semifield.toDivisionSemiring.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            Nat.fact_prime_two)))))))))
      D5.S3.Combinatorics.Graph.TripartiteH1Repair.witness
      (@D5.S3.Combinatorics.Graph.TripartiteH1Repair.d0.{0, 0, 0} Bool Bool Bool g))

noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_2.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"sharp_three_edge_witness\"],\"part\":\"type\",\"path\":[\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `D5.S3.Combinatorics.Graph.TripartiteH1Repair.sharp_three_edge_witness, part := .type, path := [.argument, .argument, .argument, .argument, .argument, .argument, .argument, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_2.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_2.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_2.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_2.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_2.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"sharp_three_edge_witness\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_2.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `D5.S3.Combinatorics.Graph.TripartiteH1Repair.sharp_three_edge_witness, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.bRegistration).actual (Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.bRegistration).variation.2.choose (Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.bRegistration).variation.1 (Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.bRegistration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_2.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"bRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.bRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_3.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.cArena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.cArena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.cArena Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.cActual)
    Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.cRegistration)

noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_3.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"universal_repair\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"registration_3\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `D5.S3.Combinatorics.Graph.TripartiteH1Repair.universal_repair, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_3.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.cArena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.cArena Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.cActual)
  Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.cRegistration)

noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_3.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_3.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_3.observation0 : (p q : Nat) →
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
    Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.CSig PUnit.unit.{1} PUnit.unit.{1} :=
  fun (p q : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.CSig Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.cActual
    PUnit.unit.{1} PUnit.unit.{1} q

noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_3.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"universal_repair\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"registration_3\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `D5.S3.Combinatorics.Graph.TripartiteH1Repair.universal_repair, part := .type, path := [.body, .body, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_3.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_3.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_3.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_3.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"registration_3\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_3.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"registration_3\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"universal_repair\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_3.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `D5.S3.Combinatorics.Graph.TripartiteH1Repair.universal_repair, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.cRegistration).actual (Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.cRegistration).variation.2.choose (Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.cRegistration).variation.1 (Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.cRegistration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_3.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Combinatorics\",\"Graph\",\"TripartiteH1Repair\",\"cRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair, declaration := `Reg.D5.S3.Combinatorics.Graph.TripartiteH1Repair.cRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
