import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.KrausCompletion
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Recovery.KrausCompletion
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open LeanInformationAudit Lean Elab Command
open scoped BigOperators ComplexOrder MatrixOrder Matrix
noncomputable section
namespace Reg.D5.S3.Quantum.Recovery.KrausCompletion
universe u v w z

namespace RowReset
abbrev signature : Signature where
  Params := Type u
  State p := Matrix p p ℂ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ p := Matrix p p ℂ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro e; exact nomatch e⟩

def actual : Realization signature :=
  realize signature (fun _ _ X => X) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {a : Type u} {b : Type v} {c : Type w}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (v : b) (B : Matrix c a ℂ) (X : Matrix a a ℂ),
    (∑ j, rowReset v B j * X * (rowReset v B j)ᴴ) =
      Matrix.trace (B * R.readout () a X * Bᴴ) • Matrix.single v v (1 : ℂ)

theorem actual_law : arena.{u,v,w}.Law actual := by
  exact @row_reset_action.{u,v,w}

theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let a := ULift.{u} (Fin 1)
  let b := ULift.{v} (Fin 1)
  let c := ULift.{w} (Fin 1)
  let v : b := ⟨0⟩
  let B : Matrix c a ℂ := fun _ _ => 1
  have hh := h (a := a) (b := b) (c := c) v B 1
  rw [row_reset_action] at hh
  have he := congrArg (fun M : Matrix b b ℂ => M v v) hh
  simp only [rejected, realize, signature, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.trace_zero, zero_smul, Matrix.mul_one] at he
  norm_num [B, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.single, Fintype.sum_unique] at he
  change (∑ _ : a, (1 : ℂ) * star 1) = 0 at he
  norm_num at he

def registration : Registration arena.{u,v,w} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h; exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro role
    let a := ULift.{u} (Fin 1)
    let i : a := ⟨0⟩
    refine ⟨a, (0 : Matrix a a ℂ), (fun _ _ => (1 : ℂ)), ?_⟩
    intro h
    have he := congrArg (fun M : Matrix a a ℂ => M i i) h
    norm_num [actual, realize, signature] at he

noncomputable def registration_1.{u_1, u_2, u_3} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Recovery.KrausCompletion.row_reset_action.{u_1, u_2, u_3}) (type_of% (realize.{u_1 + 1, u_1, 0, u_1, 0} signature.{u_1} (fun _ _ X => X) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Recovery") "KrausCompletion") "row_reset_action") "Reg.D5.S3.Quantum.Recovery.KrausCompletion/Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2, u_3}) ⟨(registration.{u_1, u_2, u_3})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_1 + 1, u_1, 0, u_1, 0} signature.{u_1} (fun _ _ X => X) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Recovery.KrausCompletion, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "arg", "fn", "arg", "arg"], stateBinder := 11, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Recovery.KrausCompletion, declaration := `D5.S3.Quantum.Recovery.KrausCompletion.row_reset_action, part := .type, path := [], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] }], facts := [`Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration_1.observationFact0, `Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration_1.anchorEnumeration }

#print axioms registration
end RowReset

namespace CompleteAction
abbrev signature : Signature where
  Params := Type u
  State p := Matrix p p ℂ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ p := Matrix p p ℂ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro e; exact nomatch e⟩

def actual : Realization signature :=
  realize signature (fun _ _ X => X) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {a : Type u} {b : Type v} {s : Type w}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype s]
    (K : s → Matrix b a ℂ) (P : Matrix a a ℂ)
    (v : b) (hP : Pᴴ = P) (hPP : P * P = P) (X : Matrix a a ℂ),
    (∑ i, completeKraus K P v i * X * (completeKraus K P v i)ᴴ) =
      (∑ i, K i * X * (K i)ᴴ) +
        Matrix.trace ((1 - P) * R.readout () a X) • Matrix.single v v (1 : ℂ)

theorem actual_law : arena.{u,v,w}.Law actual := by
  exact @complete_kraus_action.{u,v,w}

theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let a := ULift.{u} (Fin 1)
  let b := ULift.{v} (Fin 1)
  let s := ULift.{w} (Fin 1)
  let v : b := ⟨0⟩
  have hh := h (a := a) (b := b) (s := s) 0 0 v (by simp) (by simp) 1
  rw [complete_kraus_action _ _ _ (by simp) (by simp)] at hh
  have he := congrArg (fun M : Matrix b b ℂ => M v v) hh
  norm_num [rejected, realize, signature, Matrix.trace, Matrix.single] at he

def registration : Registration arena.{u,v,w} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h; exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro role
    let a := ULift.{u} (Fin 1)
    let i : a := ⟨0⟩
    refine ⟨a, (0 : Matrix a a ℂ), (fun _ _ => (1 : ℂ)), ?_⟩
    intro h
    have he := congrArg (fun M : Matrix a a ℂ => M i i) h
    norm_num [actual, realize, signature] at he

noncomputable def registration_2.{u_1, u_2, u_4} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Recovery.KrausCompletion.complete_kraus_action.{u_1, u_2, u_4}) (type_of% (realize.{u_1 + 1, u_1, 0, u_1, 0} signature.{u_1} (fun _ _ X => X) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Recovery") "KrausCompletion") "complete_kraus_action") "Reg.D5.S3.Quantum.Recovery.KrausCompletion/Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2, u_4})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2, u_4})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2, u_4}) ⟨(registration.{u_1, u_2, u_4})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_1 + 1, u_1, 0, u_1, 0} signature.{u_1} (fun _ _ X => X) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Recovery.KrausCompletion, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "arg", "arg"], stateBinder := 13, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Recovery.KrausCompletion, declaration := `D5.S3.Quantum.Recovery.KrausCompletion.complete_kraus_action, part := .type, path := [], levels := [.param `u_1, .param `u_2, .param `u_4] },
    { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_4] },
    { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_4] },
    { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_4] },
    { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2, .param `u_4] }], facts := [`Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration_2.canonicalArenaFact, `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration_2.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration_2.sourceBridgeFact, `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration_2.observationFact0, `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration_2.anchorEnumeration }

#print axioms registration
end CompleteAction

namespace CompleteChannel
abbrev signature : Signature where
  Params := Type u
  State p := Matrix p p ℂ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ p := Matrix p p ℂ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro e; exact nomatch e⟩

def actual : Realization signature :=
  realize signature (fun _ _ X => X) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {a : Type u} {b : Type v} {s : Type w}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype s]
    (K : s → Matrix b a ℂ) (P : Matrix a a ℂ)
    (v : b) (hP : Pᴴ = P) (hPP : P * P = P)
    (hK : (∑ i, (K i)ᴴ * K i) = P),
    ∃ channel : QuantumChannel a b, ∀ X : Matrix a a ℂ,
      CStarMatrix.ofMatrix.symm
        (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix (R.readout () a X))) =
      (∑ i, K i * X * (K i)ᴴ) +
        Matrix.trace ((1 - P) * X) • Matrix.single v v (1 : ℂ)

theorem actual_law : arena.{u,v,w}.Law actual := by
  exact @complete_quantum_channel.{u,v,w}

theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let a := ULift.{u} (Fin 1)
  let b := ULift.{v} (Fin 1)
  let s := ULift.{w} (Fin 1)
  let v : b := ⟨0⟩
  obtain ⟨channel, hc⟩ := h (a := a) (b := b) (s := s) 0 0 v
    (by simp) (by simp) (by simp)
  have hh := hc (1 : Matrix a a ℂ)
  have he := congrArg (fun M : Matrix b b ℂ => M v v) hh
  norm_num [rejected, realize, signature, Matrix.trace, Matrix.single] at he

def registration : Registration arena.{u,v,w} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h; exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro role
    let a := ULift.{u} (Fin 1)
    let i : a := ⟨0⟩
    refine ⟨a, (0 : Matrix a a ℂ), (fun _ _ => (1 : ℂ)), ?_⟩
    intro h
    have he := congrArg (fun M : Matrix a a ℂ => M i i) h
    norm_num [actual, realize, signature] at he

noncomputable def registration_3.{u_1, u_2, u_4} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Recovery.KrausCompletion.complete_quantum_channel.{u_1, u_2, u_4}) (type_of% (realize.{u_1 + 1, u_1, 0, u_1, 0} signature.{u_1} (fun _ _ X => X) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Recovery") "KrausCompletion") "complete_quantum_channel") "Reg.D5.S3.Quantum.Recovery.KrausCompletion/Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2, u_4})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2, u_4})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2, u_4}) ⟨(registration.{u_1, u_2, u_4})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_1 + 1, u_1, 0, u_1, 0} signature.{u_1} (fun _ _ X => X) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Recovery.KrausCompletion, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "fn", "arg", "arg", "arg", "arg"], stateBinder := 15, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Recovery.KrausCompletion, declaration := `D5.S3.Quantum.Recovery.KrausCompletion.complete_quantum_channel, part := .type, path := [], levels := [.param `u_1, .param `u_2, .param `u_4] },
    { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_4] },
    { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_4] },
    { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_4] },
    { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2, .param `u_4] }], facts := [`Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration_3.canonicalArenaFact, `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration_3.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration_3.sourceBridgeFact, `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration_3.observationFact0, `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration_3.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration_3.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration_3.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration_3.anchorEnumeration }

#print axioms registration
end CompleteChannel

end Reg.D5.S3.Quantum.Recovery.KrausCompletion


noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration_3.canonicalArenaOperand.{u_1, u_2, u_4} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, u_1, 0} :=
  Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.arena.{u_1, u_2, u_4}
noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration_3.canonicalArenaFact.{u_1, u_2, u_4} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"CompleteChannel\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_4\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"CompleteChannel\",\"registration_3\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_4\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_4)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration_3.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_4)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration_3.canonicalObjectArenaOperand.{u_1, u_2, u_4} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, u_1, 0} :=
  Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.arena.{u_1, u_2, u_4}
noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration_3.canonicalObjectArenaFact.{u_1, u_2, u_4} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"CompleteChannel\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_4\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"CompleteChannel\",\"registration_3\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_4\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_4)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration_3.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_4)] }
  .evidence

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration_1.canonicalArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, u_1, 0} :=
  Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.arena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration_1.canonicalArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"RowReset\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"RowReset\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration_1.canonicalObjectArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, u_1, 0} :=
  Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.arena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration_1.canonicalObjectArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"RowReset\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"RowReset\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration_2.canonicalArenaOperand.{u_1, u_2, u_4} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, u_1, 0} :=
  Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.arena.{u_1, u_2, u_4}
noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration_2.canonicalArenaFact.{u_1, u_2, u_4} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"CompleteAction\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_4\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"CompleteAction\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_4\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_4)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_4)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration_2.canonicalObjectArenaOperand.{u_1, u_2, u_4} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, u_1, 0} :=
  Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.arena.{u_1, u_2, u_4}
noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration_2.canonicalObjectArenaFact.{u_1, u_2, u_4} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"CompleteAction\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_4\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"CompleteAction\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_4\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_4)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_4)] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration_3.sourceLaw.{u_1, u_2, u_4} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_1 + 1, u_1, 0, u_1, 0} (Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.arena.) (Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration.{u_1, u_2, u_4}).actual

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration_3.sourceBridgeFact.{u_1, u_2, u_4} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"complete_quantum_channel\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_4\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"CompleteChannel\",\"registration_3\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_4\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.KrausCompletion, declaration := `D5.S3.Quantum.Recovery.KrausCompletion.complete_quantum_channel, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_4)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration_3.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_4)] }
  (Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration.{u_1, u_2, u_4}).bridge

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration_3.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration_3.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration_3.observation0.{u_1, u_2, u_4} : {a : Type u_1} →
  {b : Type u_2} →
    {s : Type u_4} →
      [inst : Fintype.{u_1} a] →
        [inst_1 : DecidableEq.{u_1 + 1} a] →
          [inst_2 : Fintype.{u_2} b] →
            [inst_3 : DecidableEq.{u_2 + 1} b] →
              [inst_4 : Fintype.{u_4} s] →
                (K : s → Matrix.{u_2, u_1, 0} b a Complex) →
                  (P : Matrix.{u_1, u_1, 0} a a Complex) →
                    (v : b) →
                      (hP :
                          @Eq.{u_1 + 1} (Matrix.{u_1, u_1, 0} a a Complex)
                            (@Matrix.conjTranspose.{0, u_1, u_1} a a Complex
                              (@InvolutiveStar.toStar.{0} Complex
                                (@StarAddMonoid.toInvolutiveStar.{0} Complex
                                  (@AddCommMonoid.toAddMonoid.{0} Complex
                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                                      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                                            Complex.instNonUnitalCommRing)))))
                                  (@StarRing.toStarAddMonoid.{0} Complex
                                    (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                                          Complex.instNonUnitalCommRing)))
                                    Complex.instStarRing)))
                              P)
                            P) →
                        (hPP :
                            @Eq.{u_1 + 1} (Matrix.{u_1, u_1, 0} a a Complex)
                              (@HMul.hMul.{u_1, u_1, u_1} (Matrix.{u_1, u_1, 0} a a Complex)
                                (Matrix.{u_1, u_1, 0} a a Complex) (Matrix.{u_1, u_1, 0} a a Complex)
                                (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_1, u_1, u_1} a a a Complex inst
                                  Complex.instMul Complex.instAddCommMonoid)
                                P P)
                              P) →
                          (hK :
                              @Eq.{u_1 + 1} (Matrix.{u_1, u_1, 0} a a Complex)
                                (@Finset.sum.{u_4, u_1} s (Matrix.{u_1, u_1, 0} a a Complex)
                                  (@Matrix.addCommMonoid.{0, u_1, u_1} a a Complex Complex.instAddCommMonoid)
                                  (@Finset.univ.{u_4} s inst_4) fun (i : s) =>
                                  @HMul.hMul.{max u_1 u_2, max u_1 u_2, u_1} (Matrix.{u_1, u_2, 0} a b Complex)
                                    (Matrix.{u_2, u_1, 0} b a Complex) (Matrix.{u_1, u_1, 0} a a Complex)
                                    (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_1, u_2, u_1} a b a Complex
                                      inst_2 Complex.instMul Complex.instAddCommMonoid)
                                    (@Matrix.conjTranspose.{0, u_2, u_1} b a Complex
                                      (@InvolutiveStar.toStar.{0} Complex
                                        (@StarAddMonoid.toInvolutiveStar.{0} Complex
                                          (@AddCommMonoid.toAddMonoid.{0} Complex
                                            (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                                              (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                                                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                                                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                                                    Complex.instNonUnitalCommRing)))))
                                          (@StarRing.toStarAddMonoid.{0} Complex
                                            (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                                              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                                                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                                                  Complex.instNonUnitalCommRing)))
                                            Complex.instStarRing)))
                                      (K i))
                                    (K i))
                                P) →
                            (channel :
                                @D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.{u_1, u_2} a b inst inst_1
                                  inst_2 inst_3) →
                              (X : Matrix.{u_1, u_1, 0} a a Complex) →
                                D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u_1 + 1, u_1,
                                    0, u_1, 0}
                                  Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.signature.{u_1} Unit.unit a :=
  fun {a : Type u_1} {b : Type u_2} {s : Type u_4} [Fintype.{u_1} a] [DecidableEq.{u_1 + 1} a] [Fintype.{u_2} b]
    [DecidableEq.{u_2 + 1} b] [Fintype.{u_4} s] (K : s → Matrix.{u_2, u_1, 0} b a Complex)
    (P : Matrix.{u_1, u_1, 0} a a Complex) (v : b)
    (hP :
      @Eq.{u_1 + 1} (Matrix.{u_1, u_1, 0} a a Complex)
        (@Matrix.conjTranspose.{0, u_1, u_1} a a Complex
          (@InvolutiveStar.toStar.{0} Complex
            (@StarAddMonoid.toInvolutiveStar.{0} Complex
              (@AddCommMonoid.toAddMonoid.{0} Complex
                (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                  (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                    (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                      (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))))
              (@StarRing.toStarAddMonoid.{0} Complex
                (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                  (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                    (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))
                Complex.instStarRing)))
          P)
        P)
    (hPP :
      @Eq.{u_1 + 1} (Matrix.{u_1, u_1, 0} a a Complex)
        (@HMul.hMul.{u_1, u_1, u_1} (Matrix.{u_1, u_1, 0} a a Complex) (Matrix.{u_1, u_1, 0} a a Complex)
          (Matrix.{u_1, u_1, 0} a a Complex)
          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_1, u_1, u_1} a a a Complex inst Complex.instMul
            Complex.instAddCommMonoid)
          P P)
        P)
    (hK :
      @Eq.{u_1 + 1} (Matrix.{u_1, u_1, 0} a a Complex)
        (@Finset.sum.{u_4, u_1} s (Matrix.{u_1, u_1, 0} a a Complex)
          (@Matrix.addCommMonoid.{0, u_1, u_1} a a Complex Complex.instAddCommMonoid) (@Finset.univ.{u_4} s inst_4)
          fun (i : s) =>
          @HMul.hMul.{max u_1 u_2, max u_1 u_2, u_1} (Matrix.{u_1, u_2, 0} a b Complex)
            (Matrix.{u_2, u_1, 0} b a Complex) (Matrix.{u_1, u_1, 0} a a Complex)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_1, u_2, u_1} a b a Complex inst_2 Complex.instMul
              Complex.instAddCommMonoid)
            (@Matrix.conjTranspose.{0, u_2, u_1} b a Complex
              (@InvolutiveStar.toStar.{0} Complex
                (@StarAddMonoid.toInvolutiveStar.{0} Complex
                  (@AddCommMonoid.toAddMonoid.{0} Complex
                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))))
                  (@StarRing.toStarAddMonoid.{0} Complex
                    (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))
                    Complex.instStarRing)))
              (K i))
            (K i))
        P)
    (channel : @D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.{u_1, u_2} a b inst inst_1 inst_2 inst_3)
    (X : Matrix.{u_1, u_1, 0} a a Complex) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u_1 + 1, u_1, 0, u_1, 0}
    Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.signature.{u_1}
    Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.actual.{u_1} Unit.unit a X

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration_3.observationFact0.{u_1, u_2, u_4} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"complete_quantum_channel\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"body\",\"function\",\"argument\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_4\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"CompleteChannel\",\"registration_3\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_4\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.KrausCompletion, declaration := `D5.S3.Quantum.Recovery.KrausCompletion.complete_quantum_channel, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .body, .body, .function, .argument, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_4)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration_3.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_4)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration_3.varyingLawInput.{u_1, u_2, u_4} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration_3.canonicalArenaOperand.{u_1, u_2, u_4})
noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration_3.varyingLaw.{u_1, u_2, u_4}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"CompleteChannel\",\"registration_3\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_4\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration_3.statementExclusion.{u_1, u_2, u_4} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"CompleteChannel\",\"registration_3\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_4\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"complete_quantum_channel\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_4\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration_3.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_4)] }
  statementLocation := { owner := `D5.S3.Quantum.Recovery.KrausCompletion, declaration := `D5.S3.Quantum.Recovery.KrausCompletion.complete_quantum_channel, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_4)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration.{u_1, u_2, u_4}).actual (Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration.{u_1, u_2, u_4}).variation.2.choose (Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration.{u_1, u_2, u_4}).variation.1 (Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration.{u_1, u_2, u_4}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration_3.descriptorFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"CompleteChannel\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_4\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"CompleteChannel\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_4\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_4)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteChannel.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_4)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration_1.sourceLaw.{u_1, u_2, u_3} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_1 + 1, u_1, 0, u_1, 0} (Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.arena.) (Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration.{u_1, u_2, u_3}).actual

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration_1.sourceBridgeFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"row_reset_action\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"RowReset\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.KrausCompletion, declaration := `D5.S3.Quantum.Recovery.KrausCompletion.row_reset_action, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration.{u_1, u_2, u_3}).bridge

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration_1.observation0.{u_1, u_2, u_3} : {a : Type u_1} →
  {b : Type u_2} →
    {c : Type u_3} →
      [Fintype.{u_1} a] →
        [DecidableEq.{u_1 + 1} a] →
          [Fintype.{u_2} b] →
            [DecidableEq.{u_2 + 1} b] →
              [Fintype.{u_3} c] →
                [DecidableEq.{u_3 + 1} c] →
                  (v : b) →
                    (B : Matrix.{u_3, u_1, 0} c a Complex) →
                      (X : Matrix.{u_1, u_1, 0} a a Complex) →
                        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u_1 + 1, u_1, 0, u_1,
                            0}
                          Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.signature.{u_1} Unit.unit a :=
  fun {a : Type u_1} {b : Type u_2} {c : Type u_3} [Fintype.{u_1} a] [DecidableEq.{u_1 + 1} a] [Fintype.{u_2} b]
    [DecidableEq.{u_2 + 1} b] [Fintype.{u_3} c] [DecidableEq.{u_3 + 1} c] (v : b) (B : Matrix.{u_3, u_1, 0} c a Complex)
    (X : Matrix.{u_1, u_1, 0} a a Complex) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u_1 + 1, u_1, 0, u_1, 0}
    Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.signature.{u_1}
    Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.actual.{u_1} Unit.unit a X

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration_1.observationFact0.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"row_reset_action\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"function\",\"argument\",\"argument\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"RowReset\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.KrausCompletion, declaration := `D5.S3.Quantum.Recovery.KrausCompletion.row_reset_action, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .function, .argument, .argument, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration_1.varyingLawInput.{u_1, u_2, u_3} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration_1.canonicalArenaOperand.{u_1, u_2, u_3})
noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration_1.varyingLaw.{u_1, u_2, u_3}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"RowReset\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration_1.statementExclusion.{u_1, u_2, u_3} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"RowReset\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"row_reset_action\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  statementLocation := { owner := `D5.S3.Quantum.Recovery.KrausCompletion, declaration := `D5.S3.Quantum.Recovery.KrausCompletion.row_reset_action, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration.{u_1, u_2, u_3}).actual (Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration.{u_1, u_2, u_3}).variation.2.choose (Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration.{u_1, u_2, u_3}).variation.1 (Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration.{u_1, u_2, u_3}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration_1.descriptorFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"RowReset\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"RowReset\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.RowReset.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration_2.sourceLaw.{u_1, u_2, u_4} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_1 + 1, u_1, 0, u_1, 0} (Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.arena.) (Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration.{u_1, u_2, u_4}).actual

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration_2.sourceBridgeFact.{u_1, u_2, u_4} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"complete_kraus_action\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_4\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"CompleteAction\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_4\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.KrausCompletion, declaration := `D5.S3.Quantum.Recovery.KrausCompletion.complete_kraus_action, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_4)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration_2.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_4)] }
  (Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration.{u_1, u_2, u_4}).bridge

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration_2.observation0.{u_1, u_2, u_4} : {a : Type u_1} →
  {b : Type u_2} →
    {s : Type u_4} →
      [inst : Fintype.{u_1} a] →
        [DecidableEq.{u_1 + 1} a] →
          [Fintype.{u_2} b] →
            [DecidableEq.{u_2 + 1} b] →
              [Fintype.{u_4} s] →
                (K : s → Matrix.{u_2, u_1, 0} b a Complex) →
                  (P : Matrix.{u_1, u_1, 0} a a Complex) →
                    (v : b) →
                      (hP :
                          @Eq.{u_1 + 1} (Matrix.{u_1, u_1, 0} a a Complex)
                            (@Matrix.conjTranspose.{0, u_1, u_1} a a Complex
                              (@InvolutiveStar.toStar.{0} Complex
                                (@StarAddMonoid.toInvolutiveStar.{0} Complex
                                  (@AddCommMonoid.toAddMonoid.{0} Complex
                                    (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                                      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                                            Complex.instNonUnitalCommRing)))))
                                  (@StarRing.toStarAddMonoid.{0} Complex
                                    (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex
                                          Complex.instNonUnitalCommRing)))
                                    Complex.instStarRing)))
                              P)
                            P) →
                        (hPP :
                            @Eq.{u_1 + 1} (Matrix.{u_1, u_1, 0} a a Complex)
                              (@HMul.hMul.{u_1, u_1, u_1} (Matrix.{u_1, u_1, 0} a a Complex)
                                (Matrix.{u_1, u_1, 0} a a Complex) (Matrix.{u_1, u_1, 0} a a Complex)
                                (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_1, u_1, u_1} a a a Complex inst
                                  Complex.instMul Complex.instAddCommMonoid)
                                P P)
                              P) →
                          (X : Matrix.{u_1, u_1, 0} a a Complex) →
                            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u_1 + 1, u_1, 0,
                                u_1, 0}
                              Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.signature.{u_1} Unit.unit a :=
  fun {a : Type u_1} {b : Type u_2} {s : Type u_4} [Fintype.{u_1} a] [DecidableEq.{u_1 + 1} a] [Fintype.{u_2} b]
    [DecidableEq.{u_2 + 1} b] [Fintype.{u_4} s] (K : s → Matrix.{u_2, u_1, 0} b a Complex)
    (P : Matrix.{u_1, u_1, 0} a a Complex) (v : b)
    (hP :
      @Eq.{u_1 + 1} (Matrix.{u_1, u_1, 0} a a Complex)
        (@Matrix.conjTranspose.{0, u_1, u_1} a a Complex
          (@InvolutiveStar.toStar.{0} Complex
            (@StarAddMonoid.toInvolutiveStar.{0} Complex
              (@AddCommMonoid.toAddMonoid.{0} Complex
                (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                  (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                    (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                      (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))))
              (@StarRing.toStarAddMonoid.{0} Complex
                (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                  (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                    (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))
                Complex.instStarRing)))
          P)
        P)
    (hPP :
      @Eq.{u_1 + 1} (Matrix.{u_1, u_1, 0} a a Complex)
        (@HMul.hMul.{u_1, u_1, u_1} (Matrix.{u_1, u_1, 0} a a Complex) (Matrix.{u_1, u_1, 0} a a Complex)
          (Matrix.{u_1, u_1, 0} a a Complex)
          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_1, u_1, u_1} a a a Complex inst Complex.instMul
            Complex.instAddCommMonoid)
          P P)
        P)
    (X : Matrix.{u_1, u_1, 0} a a Complex) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u_1 + 1, u_1, 0, u_1, 0}
    Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.signature.{u_1}
    Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.actual.{u_1} Unit.unit a X

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration_2.observationFact0.{u_1, u_2, u_4} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"complete_kraus_action\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_4\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"CompleteAction\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_4\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.KrausCompletion, declaration := `D5.S3.Quantum.Recovery.KrausCompletion.complete_kraus_action, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .argument, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_4)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration_2.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_4)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration_2.varyingLawInput.{u_1, u_2, u_4} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration_2.canonicalArenaOperand.{u_1, u_2, u_4})
noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration_2.varyingLaw.{u_1, u_2, u_4}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"CompleteAction\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_4\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration_2.statementExclusion.{u_1, u_2, u_4} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"CompleteAction\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_4\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"complete_kraus_action\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_4\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration_2.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_4)] }
  statementLocation := { owner := `D5.S3.Quantum.Recovery.KrausCompletion, declaration := `D5.S3.Quantum.Recovery.KrausCompletion.complete_kraus_action, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_4)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration.{u_1, u_2, u_4}).actual (Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration.{u_1, u_2, u_4}).variation.2.choose (Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration.{u_1, u_2, u_4}).variation.1 (Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration.{u_1, u_2, u_4}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration_2.descriptorFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"CompleteAction\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_4\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"KrausCompletion\",\"CompleteAction\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_4\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_4)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.KrausCompletion, declaration := `Reg.D5.S3.Quantum.Recovery.KrausCompletion.CompleteAction.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_4)] }
  (by first | rfl | (ext <;> rfl))
