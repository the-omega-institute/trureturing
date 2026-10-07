import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (SuccessfulWord)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Lean LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion

noncomputable section

abbrev signature : Signature where
  Params := Σ H : Nat, Σ _u : ZMod H, ZMod H
  State p := KnownRowFiber p.1 p.2.1 p.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ZMod p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p source => (sourceNumber source.val : ZMod p.1))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p _ => (0 : ZMod p.1))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (H : Nat) (hH : 2 ≤ H) (u v : ZMod H)
    (hrow : ∃ source : ActualPrefix,
      ((nextRow source).1 : ZMod H) = u ∧
      ((nextRow source).2 : ZMod H) = v),
    ∃ j : Nat, ∀ r : ZMod H, ∃ source : KnownRowFiber H u v,
      source.val.past.length = j ∧
      R.readout () ⟨H, u, v⟩ source = r

theorem actual_law : arena.Law actual := by
  intro H hH u v hrow
  simpa only [actual, realize] using actual_common_depth_fullness H hH u v hrow

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let source : ActualPrefix := ⟨true, [], rfl⟩
  have hrow : ∃ source : ActualPrefix,
      ((nextRow source).1 : ZMod 2) = 0 ∧
      ((nextRow source).2 : ZMod 2) = 1 := by
    refine ⟨source, ?_⟩
    decide
  obtain ⟨j, hj⟩ := h 2 (by omega) 0 1 hrow
  obtain ⟨x, _, hx⟩ := hj 1
  have hfalse : (0 : ZMod 2) = 1 := by
    simpa only [rejected, realize] using hx
  exact (by decide : (0 : ZMod 2) ≠ 1) hfalse

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    let source : ActualPrefix := ⟨true, [], rfl⟩
    have hrow : ∃ source : ActualPrefix,
        ((nextRow source).1 : ZMod 2) = 0 ∧
        ((nextRow source).2 : ZMod 2) = 1 := by
      refine ⟨source, ?_⟩
      decide
    obtain ⟨j, hj⟩ := actual_common_depth_fullness 2 (by omega) 0 1 hrow
    obtain ⟨x, _, hx⟩ := hj 0
    obtain ⟨y, _, hy⟩ := hj 1
    refine ⟨⟨2, 0, 1⟩, x, y, ?_⟩
    change (sourceNumber x.val : ZMod 2) ≠ (sourceNumber y.val : ZMod 2)
    rw [hx,hy]
    decide

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.actual_common_depth_fullness) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ p source => (sourceNumber source.val : ZMod p.1))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "FibonacciAtomic") "BottomSiblingBlockCriterion") "actual_common_depth_fullness") "Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion/Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ p source => (sourceNumber source.val : ZMod p.1))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, definition := none, coordinates := #[0, 2, 3], readouts := #[{ path := #["body", "body", "body", "body", "body", "arg", "body", "body", "arg", "body", "arg", "fn", "arg"], stateBinder := 7, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.actual_common_depth_fullness, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_1.observationFact0, `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_1.anchorEnumeration }


#print axioms registration

abbrev nonconverseSignature : Signature where
  Params := Unit
  State _ := Finset (SuccessfulWord 2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Finset (ZMod 4)
  Anchor := Empty
  finiteAnchor := inferInstance

def nonconverseActual : Realization nonconverseSignature :=
  realize nonconverseSignature (fun _ _ available => centers 2 4 0 1 available)
    (fun e => nomatch e)

def nonconverseRejected : Realization nonconverseSignature :=
  realize nonconverseSignature (fun _ _ _ => ∅)
    (fun e => nomatch e)

abbrev nonconverseArena : Arena where
  signature := nonconverseSignature
  Law R := ∃ source : KnownRowFiber 4 0 1,
    sourceNumber source.val = 5 ∧
    ∃ available : Finset (SuccessfulWord 2),
      (R.readout () () available).card = 2 ∧
      ¬ BottomBlocks 2 4 0 1 available

theorem nonconverse_actual_law : nonconverseArena.Law nonconverseActual := by
  simpa only [nonconverseActual, realize] using actual_nonconverse

theorem nonconverse_rejected_law : ¬ nonconverseArena.Law nonconverseRejected := by
  rintro ⟨source, hs, available, hcard, _⟩
  simp [nonconverseRejected, realize] at hcard

def nonconverseRegistration :
    Registration nonconverseArena (nonconverseArena.Law nonconverseActual) where
  actual := nonconverseActual
  bridge := Iff.rfl
  variation := ⟨nonconverse_actual_law, nonconverseRejected,
    nonconverse_rejected_law⟩
  sensitivity := ⟨fun i => ⟨nonconverseRejected,
    fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, nonconverse_rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    obtain ⟨source, hs, available, hcard, _⟩ := actual_nonconverse
    refine ⟨(), ∅, available, ?_⟩
    change centers 2 4 0 1 ∅ ≠ centers 2 4 0 1 available
    intro heq
    have hz : (centers 2 4 0 1 (∅ : Finset (SuccessfulWord 2))).card = 0 := by
      simp [centers]
    have hc : (centers 2 4 0 1 available).card = 0 := by
      rw [← heq]
      exact hz
    omega

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.actual_nonconverse) (type_of% (realize.{0, 0, 0, 0, 0} nonconverseSignature
    (fun _ _ available => centers 2 4 0 1 available)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "FibonacciAtomic") "BottomSiblingBlockCriterion") "actual_nonconverse") "Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion/Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.nonconverseArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.nonconverseRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(nonconverseArena)⟩,
  objectArena := .source ⟨(nonconverseArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (nonconverseArena) ⟨(nonconverseRegistration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} nonconverseSignature
    (fun _ _ available => centers 2 4 0 1 available)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, definition := none, coordinates := #[], readouts := #[{ path := #["arg", "body", "arg", "arg", "body", "fn", "arg", "fn", "arg", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.actual_nonconverse, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_2.canonicalArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_2.canonicalObjectArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_2.sourceBridgeFact, `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_2.observationFact0, `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_2.anchorEnumeration }


#print axioms nonconverseRegistration

abbrev futureSignature : Signature where
  Params := Σ H : Nat, Σ u : ZMod H, ZMod H
  State p := KnownRowFiber p.1 p.2.1 p.2.2
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ZMod p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def futureActual : Realization futureSignature :=
  realize futureSignature (fun _ p source => (sourceNumber source.val : ZMod p.1))
    (fun e => nomatch e)

def futureRejected : Realization futureSignature :=
  realize futureSignature (fun _ p _ => (0 : ZMod p.1))
    (fun e => nomatch e)

abbrev futureArena : Arena where
  signature := futureSignature
  Law R := ∀ (H : Nat) (hH : 2 ≤ H) (u v : ZMod H)
    (hrow : ∃ source : ActualPrefix,
      ((nextRow source).1 : ZMod H) = u ∧
      ((nextRow source).2 : ZMod H) = v)
    (x y : KnownRowFiber H u v),
    CompleteFuture H x.val y.val ↔
      R.readout false ⟨H,u,v⟩ x = R.readout true ⟨H,u,v⟩ y

theorem future_actual_law : futureArena.Law futureActual := by
  intro H hH u v hrow x y
  simpa only [futureActual, realize] using
    actual_future_residue_equivalence H hH u v hrow x y

theorem future_rejected_law : ¬ futureArena.Law futureRejected := by
  intro h
  let source : ActualPrefix := ⟨true, [], rfl⟩
  have hrow : ∃ source : ActualPrefix,
      ((nextRow source).1 : ZMod 2) = 0 ∧
      ((nextRow source).2 : ZMod 2) = 1 := by
    refine ⟨source, ?_⟩
    decide
  obtain ⟨j, hj⟩ := actual_common_depth_fullness 2 (by omega) 0 1 hrow
  obtain ⟨x, _, hx⟩ := hj 0
  obtain ⟨y, _, hy⟩ := hj 1
  have hfuture : CompleteFuture 2 x.val y.val :=
    (h 2 (by omega) 0 1 hrow x y).2 (by rfl)
  have heq := (actual_future_residue_equivalence 2 (by omega) 0 1 hrow x y).1 hfuture
  rw [hx,hy] at heq
  exact (by decide : (0 : ZMod 2) ≠ 1) heq

def futureIntervene (i : Bool) : Realization futureSignature :=
  realize futureSignature
    (fun role p source => if role = i then 0 else futureActual.readout role p source)
    (fun e => nomatch e)

theorem future_intervene_rejected (i : Bool) : ¬ futureArena.Law (futureIntervene i) := by
  intro h
  let source : ActualPrefix := ⟨true, [], rfl⟩
  have hrow : ∃ source : ActualPrefix,
      ((nextRow source).1 : ZMod 2) = 0 ∧
      ((nextRow source).2 : ZMod 2) = 1 := by
    refine ⟨source, ?_⟩
    decide
  obtain ⟨j, hj⟩ := actual_common_depth_fullness 2 (by omega) 0 1 hrow
  obtain ⟨x, _, hx⟩ := hj 1
  have heq := (h 2 (by omega) 0 1 hrow x x).1 (by intro suffix; rfl)
  cases i <;> simp [futureIntervene, futureActual, realize, hx] at heq

def futureRegistration : Registration futureArena (futureArena.Law futureActual) where
  actual := futureActual
  bridge := Iff.rfl
  variation := ⟨future_actual_law, futureRejected, future_rejected_law⟩
  sensitivity := ⟨fun i => ⟨futureIntervene i, by
      intro j hji
      funext p source
      simp [futureIntervene, realize, hji], rfl,
    future_intervene_rejected i⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    let source : ActualPrefix := ⟨true, [], rfl⟩
    have hrow : ∃ source : ActualPrefix,
        ((nextRow source).1 : ZMod 2) = 0 ∧
        ((nextRow source).2 : ZMod 2) = 1 := by
      refine ⟨source, ?_⟩
      decide
    obtain ⟨j, hj⟩ := actual_common_depth_fullness 2 (by omega) 0 1 hrow
    obtain ⟨x, _, hx⟩ := hj 0
    obtain ⟨y, _, hy⟩ := hj 1
    refine ⟨⟨2,0,1⟩, x, y, ?_⟩
    change (sourceNumber x.val : ZMod 2) ≠ (sourceNumber y.val : ZMod 2)
    rw [hx,hy]
    decide

noncomputable def registration_3 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.actual_future_residue_equivalence) (type_of% (realize.{0, 0, 0, 0, 0} futureSignature
    (fun _ p source => (sourceNumber source.val : ZMod p.1))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "FibonacciAtomic") "BottomSiblingBlockCriterion") "actual_future_residue_equivalence") "Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion/Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.futureArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.futureRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(futureArena)⟩,
  objectArena := .source ⟨(futureArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (futureArena) ⟨(futureRegistration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} futureSignature
    (fun _ p source => (sourceNumber source.val : ZMod p.1))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, definition := none, coordinates := #[0, 2, 3], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }, { path := #["body", "body", "body", "body", "body", "body", "body", "arg", "arg"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.actual_future_residue_equivalence, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3.canonicalArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3.canonicalObjectArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3.sourceBridgeFact, `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3.observationFact0, `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3.observationFact1, `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3.anchorEnumeration }


#print axioms futureRegistration

end

end Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.futureArena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"registration_3\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.futureArena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"registration_3\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.arena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.arena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_2.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.nonconverseArena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_2.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_2.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.nonconverseArena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_2.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.futureArena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.futureArena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.futureArena
      Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.futureActual)
    Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.futureRegistration)

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"actual_future_residue_equivalence\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"registration_3\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.actual_future_residue_equivalence, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.futureArena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.futureArena
    Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.futureActual)
  Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.futureRegistration)

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Bool) where
  values := [Bool.true, Bool.false]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3.observation0 : (H : Nat) →
  (hH : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) H) →
    (u v : ZMod H) →
      (_hrow :
          @Exists.{1} D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.ActualPrefix
            fun (source : D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.ActualPrefix) =>
            And
              (@Eq.{1} (ZMod H)
                (@Nat.cast.{0} (ZMod H)
                  (@AddMonoidWithOne.toNatCast.{0} (ZMod H)
                    (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod H)
                      (@Ring.toAddGroupWithOne.{0} (ZMod H) (@CommRing.toRing.{0} (ZMod H) (ZMod.commRing H)))))
                  (@Prod.fst.{0, 0} Nat Nat (D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.nextRow source)))
                u)
              (@Eq.{1} (ZMod H)
                (@Nat.cast.{0} (ZMod H)
                  (@AddMonoidWithOne.toNatCast.{0} (ZMod H)
                    (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod H)
                      (@Ring.toAddGroupWithOne.{0} (ZMod H) (@CommRing.toRing.{0} (ZMod H) (ZMod.commRing H)))))
                  (@Prod.snd.{0, 0} Nat Nat (D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.nextRow source)))
                v)) →
        (x y : D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.KnownRowFiber H u v) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
            Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.futureSignature Bool.true
            (@Sigma.mk.{0, 0} Nat (fun (H : Nat) => @Sigma.{0, 0} (ZMod H) fun (u : ZMod H) => ZMod H) H
              (@Sigma.mk.{0, 0} (ZMod H) (fun (u : ZMod H) => ZMod H) u v)) :=
  fun (H : Nat) (hH : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) H)
    (u v : ZMod H)
    (_hrow :
      @Exists.{1} D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.ActualPrefix
        fun (source : D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.ActualPrefix) =>
        And
          (@Eq.{1} (ZMod H)
            (@Nat.cast.{0} (ZMod H)
              (@AddMonoidWithOne.toNatCast.{0} (ZMod H)
                (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod H)
                  (@Ring.toAddGroupWithOne.{0} (ZMod H) (@CommRing.toRing.{0} (ZMod H) (ZMod.commRing H)))))
              (@Prod.fst.{0, 0} Nat Nat (D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.nextRow source)))
            u)
          (@Eq.{1} (ZMod H)
            (@Nat.cast.{0} (ZMod H)
              (@AddMonoidWithOne.toNatCast.{0} (ZMod H)
                (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod H)
                  (@Ring.toAddGroupWithOne.{0} (ZMod H) (@CommRing.toRing.{0} (ZMod H) (ZMod.commRing H)))))
              (@Prod.snd.{0, 0} Nat Nat (D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.nextRow source)))
            v))
    (x y : D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.KnownRowFiber H u v) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.futureSignature
    Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.futureActual Bool.true
    (@Sigma.mk.{0, 0} Nat (fun (H : Nat) => @Sigma.{0, 0} (ZMod H) fun (u : ZMod H) => ZMod H) H
      (@Sigma.mk.{0, 0} (ZMod H) (fun (u : ZMod H) => ZMod H) u v))
    x

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"actual_future_residue_equivalence\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"registration_3\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.actual_future_residue_equivalence, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3.observation1 : (H : Nat) →
  (hH : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) H) →
    (u v : ZMod H) →
      (_hrow :
          @Exists.{1} D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.ActualPrefix
            fun (source : D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.ActualPrefix) =>
            And
              (@Eq.{1} (ZMod H)
                (@Nat.cast.{0} (ZMod H)
                  (@AddMonoidWithOne.toNatCast.{0} (ZMod H)
                    (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod H)
                      (@Ring.toAddGroupWithOne.{0} (ZMod H) (@CommRing.toRing.{0} (ZMod H) (ZMod.commRing H)))))
                  (@Prod.fst.{0, 0} Nat Nat (D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.nextRow source)))
                u)
              (@Eq.{1} (ZMod H)
                (@Nat.cast.{0} (ZMod H)
                  (@AddMonoidWithOne.toNatCast.{0} (ZMod H)
                    (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod H)
                      (@Ring.toAddGroupWithOne.{0} (ZMod H) (@CommRing.toRing.{0} (ZMod H) (ZMod.commRing H)))))
                  (@Prod.snd.{0, 0} Nat Nat (D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.nextRow source)))
                v)) →
        (x y : D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.KnownRowFiber H u v) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
            Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.futureSignature Bool.false
            (@Sigma.mk.{0, 0} Nat (fun (H : Nat) => @Sigma.{0, 0} (ZMod H) fun (u : ZMod H) => ZMod H) H
              (@Sigma.mk.{0, 0} (ZMod H) (fun (u : ZMod H) => ZMod H) u v)) :=
  fun (H : Nat) (hH : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) H)
    (u v : ZMod H)
    (_hrow :
      @Exists.{1} D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.ActualPrefix
        fun (source : D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.ActualPrefix) =>
        And
          (@Eq.{1} (ZMod H)
            (@Nat.cast.{0} (ZMod H)
              (@AddMonoidWithOne.toNatCast.{0} (ZMod H)
                (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod H)
                  (@Ring.toAddGroupWithOne.{0} (ZMod H) (@CommRing.toRing.{0} (ZMod H) (ZMod.commRing H)))))
              (@Prod.fst.{0, 0} Nat Nat (D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.nextRow source)))
            u)
          (@Eq.{1} (ZMod H)
            (@Nat.cast.{0} (ZMod H)
              (@AddMonoidWithOne.toNatCast.{0} (ZMod H)
                (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod H)
                  (@Ring.toAddGroupWithOne.{0} (ZMod H) (@CommRing.toRing.{0} (ZMod H) (ZMod.commRing H)))))
              (@Prod.snd.{0, 0} Nat Nat (D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.nextRow source)))
            v))
    (x y : D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.KnownRowFiber H u v) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.futureSignature
    Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.futureActual Bool.false
    (@Sigma.mk.{0, 0} Nat (fun (H : Nat) => @Sigma.{0, 0} (ZMod H) fun (u : ZMod H) => ZMod H) H
      (@Sigma.mk.{0, 0} (ZMod H) (fun (u : ZMod H) => ZMod H) u v))
    y

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3.observationFact1 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"actual_future_residue_equivalence\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"registration_3\",\"observation1\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.actual_future_residue_equivalence, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3.observation1, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"registration_3\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"registration_3\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"actual_future_residue_equivalence\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.actual_future_residue_equivalence, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.futureRegistration).actual (Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.futureRegistration).variation.2.choose (Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.futureRegistration).variation.1 (Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.futureRegistration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"futureRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.futureRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.arena
      Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.actual)
    Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration)

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"actual_common_depth_fullness\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.actual_common_depth_fullness, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.arena
    Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.actual)
  Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration)

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_1.observation0 : (H : Nat) →
  (hH : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) H) →
    (u v : ZMod H) →
      (hrow :
          @Exists.{1} D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.ActualPrefix
            fun (source : D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.ActualPrefix) =>
            And
              (@Eq.{1} (ZMod H)
                (@Nat.cast.{0} (ZMod H)
                  (@AddMonoidWithOne.toNatCast.{0} (ZMod H)
                    (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod H)
                      (@Ring.toAddGroupWithOne.{0} (ZMod H) (@CommRing.toRing.{0} (ZMod H) (ZMod.commRing H)))))
                  (@Prod.fst.{0, 0} Nat Nat (D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.nextRow source)))
                u)
              (@Eq.{1} (ZMod H)
                (@Nat.cast.{0} (ZMod H)
                  (@AddMonoidWithOne.toNatCast.{0} (ZMod H)
                    (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod H)
                      (@Ring.toAddGroupWithOne.{0} (ZMod H) (@CommRing.toRing.{0} (ZMod H) (ZMod.commRing H)))))
                  (@Prod.snd.{0, 0} Nat Nat (D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.nextRow source)))
                v)) →
        (j : Nat) →
          (r : ZMod H) →
            (source : D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.KnownRowFiber H u v) →
              D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.signature PUnit.unit.{1}
                (@Sigma.mk.{0, 0} Nat (fun (H : Nat) => @Sigma.{0, 0} (ZMod H) fun (_u : ZMod H) => ZMod H) H
                  (@Sigma.mk.{0, 0} (ZMod H) (fun (_u : ZMod H) => ZMod H) u v)) :=
  fun (H : Nat) (hH : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) H)
    (u v : ZMod H)
    (hrow :
      @Exists.{1} D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.ActualPrefix
        fun (source : D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.ActualPrefix) =>
        And
          (@Eq.{1} (ZMod H)
            (@Nat.cast.{0} (ZMod H)
              (@AddMonoidWithOne.toNatCast.{0} (ZMod H)
                (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod H)
                  (@Ring.toAddGroupWithOne.{0} (ZMod H) (@CommRing.toRing.{0} (ZMod H) (ZMod.commRing H)))))
              (@Prod.fst.{0, 0} Nat Nat (D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.nextRow source)))
            u)
          (@Eq.{1} (ZMod H)
            (@Nat.cast.{0} (ZMod H)
              (@AddMonoidWithOne.toNatCast.{0} (ZMod H)
                (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod H)
                  (@Ring.toAddGroupWithOne.{0} (ZMod H) (@CommRing.toRing.{0} (ZMod H) (ZMod.commRing H)))))
              (@Prod.snd.{0, 0} Nat Nat (D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.nextRow source)))
            v))
    (j : Nat) (r : ZMod H) (source : D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.KnownRowFiber H u v) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.signature
    Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat (fun (H : Nat) => @Sigma.{0, 0} (ZMod H) fun (_u : ZMod H) => ZMod H) H
      (@Sigma.mk.{0, 0} (ZMod H) (fun (_u : ZMod H) => ZMod H) u v))
    source

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"actual_common_depth_fullness\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"body\",\"argument\",\"body\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.actual_common_depth_fullness, part := .type, path := [.body, .body, .body, .body, .body, .argument, .body, .body, .argument, .body, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"actual_common_depth_fullness\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.actual_common_depth_fullness, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration).actual (Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration).variation.2.choose (Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration).variation.1 (Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_2.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.nonconverseArena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.nonconverseArena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.nonconverseArena
      Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.nonconverseActual)
    Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.nonconverseRegistration)

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_2.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"actual_nonconverse\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.actual_nonconverse, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_2.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.nonconverseArena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.nonconverseArena
    Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.nonconverseActual)
  Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.nonconverseRegistration)

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_2.observation0 : (_source :
    D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.KnownRowFiber
      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
      (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 0)
        (@Zero.toOfNat0.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (@MulZeroClass.toZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (@instMulZeroClassOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (@CommSemiring.toSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (@CommRing.toCommSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))))))
      (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 1)
        (@One.toOfNat1.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (@AddMonoidWithOne.toOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (@AddGroupWithOne.toAddMonoidWithOne.{0}
              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))))))) →
  (available :
      Finset.{0}
        (D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.SuccessfulWord
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
      Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.nonconverseSignature PUnit.unit.{1} PUnit.unit.{1} :=
  fun
    (_source :
      D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.KnownRowFiber
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 0)
          (@Zero.toOfNat0.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (@MulZeroClass.toZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (@instMulZeroClassOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (@CommSemiring.toSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (@CommRing.toCommSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))))))
        (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) (nat_lit 1)
          (@One.toOfNat1.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (@AddMonoidWithOne.toOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (@AddGroupWithOne.toAddMonoidWithOne.{0}
                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))))))
    (available :
      Finset.{0}
        (D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.SuccessfulWord
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.nonconverseSignature
    Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.nonconverseActual PUnit.unit.{1} PUnit.unit.{1}
    available

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_2.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"actual_nonconverse\"],\"part\":\"type\",\"path\":[\"argument\",\"body\",\"argument\",\"argument\",\"body\",\"function\",\"argument\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.actual_nonconverse, part := .type, path := [.argument, .body, .argument, .argument, .body, .function, .argument, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_2.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_2.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_2.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_2.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_2.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"actual_nonconverse\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_2.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.actual_nonconverse, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.nonconverseRegistration).actual (Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.nonconverseRegistration).variation.2.choose (Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.nonconverseRegistration).variation.1 (Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.nonconverseRegistration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_2.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BottomSiblingBlockCriterion\",\"nonconverseRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.nonconverseRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
