import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.SpectralTransposeRecovery
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Recovery.SpectralTransposeRecovery
open LeanInformationAudit
open scoped Matrix BigOperators ComplexOrder MatrixOrder
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
noncomputable section
namespace Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery
universe u v w

namespace Support

abbrev signature : Signature where
  Params := Σ _ : Type u, Σ _ : Type v, Type w
  State p := p.2.2 → Matrix p.1 p.2.1 ℂ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ p := p.2.2 → Matrix p.1 p.2.1 ℂ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro x; cases x⟩

def actual : Realization signature.{u,v,w} :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)

def rejected : Realization signature.{u,v,w} :=
  realize signature (fun _ _ _ _ _ _ => (1 : ℂ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u,v,w}
  Law r := ∀ {n : Type u} {d : Type v} {s : Type w}
    [Fintype n] [DecidableEq n] [Fintype d] [DecidableEq d] [Fintype s]
    (E : s → Matrix n d ℂ) (a : s),
    spectralSupport (∑ b, E b * (E b)ᴴ) * E a = r.readout () ⟨n,d,s⟩ E a

theorem actual_law : arena.{u,v,w}.Law actual := by
  intro n d s _ _ _ _ _ E a
  exact spectral_support_on_kraus E a

theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  have heq := h (n := ULift.{u} (Fin 1)) (d := ULift.{v} (Fin 1))
    (s := ULift.{w} (Fin 1)) (fun _ => 0) (ULift.up 0)
  have hz : (0 : Matrix (ULift.{u} (Fin 1)) (ULift.{v} (Fin 1)) ℂ) =
      (fun _ _ => 1) := by simpa [rejected, realize] using heq
  exact zero_ne_one (congrFun (congrFun hz (ULift.up 0)) (ULift.up 0))

def registration : Registration arena.{u,v,w} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      cases i; cases j
      exact (h rfl).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} (Fin 1), ULift.{v} (Fin 1), ULift.{w} (Fin 1)⟩,
      (fun _ _ _ => (0 : ℂ)), (fun _ _ _ => (1 : ℂ)), ?_⟩
    intro h
    exact zero_ne_one (congrFun (congrFun (congrFun h (ULift.up 0))
      (ULift.up 0)) (ULift.up 0))

noncomputable def registration_1.{u_1, u_2, u_3} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.spectral_support_on_kraus.{u_1, u_2, u_3}) (type_of% (realize.{max (max (u_1 + 1) (u_2 + 1)) (u_3 + 1), max (max u_1 u_2) u_3, 0, max (max u_1 u_2) u_3, 0} signature.{u_1, u_2, u_3} (fun _ _ x => x) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Recovery") "SpectralTransposeRecovery") "spectral_support_on_kraus") "Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery/Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2, u_3}) ⟨(registration.{u_1, u_2, u_3})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{max (max (u_1 + 1) (u_2 + 1)) (u_3 + 1), max (max u_1 u_2) u_3, 0, max (max u_1 u_2) u_3, 0} signature.{u_1, u_2, u_3} (fun _ _ x => x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Recovery.SpectralTransposeRecovery, definition := none, coordinates := #[0, 1, 2], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn"], stateBinder := 8, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Recovery.SpectralTransposeRecovery, declaration := `D5.S3.Quantum.Recovery.SpectralTransposeRecovery.spectral_support_on_kraus, part := .type, path := [], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] }], facts := [`Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration_1.observationFact0, `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration_1.anchorEnumeration }


#print axioms registration
end Support

namespace Candidate

abbrev signature : Signature where
  Params := Type v
  State p := CStarMatrix p p ℂ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ p := Matrix p p ℂ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro x; cases x⟩

def actual : Realization signature.{v} :=
  realize signature (fun _ _ x => CStarMatrix.ofMatrix.symm x) (fun e => nomatch e)

def rejected : Realization signature.{v} :=
  realize signature (fun _ _ _ _ _ => (1 : ℂ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{v}
  Law r := ∀ {n : Type u} {d : Type v} {s : Type w}
    [Fintype n] [DecidableEq n] [Fintype d] [DecidableEq d] [Fintype s]
    (E : s → Matrix n d ℂ) (v : d),
    let Q := ∑ a, E a * (E a)ᴴ
    let P := spectralSupport Q
    let W := spectralInverseSqrt Q
    ∃ recovery : QuantumChannel n d, ∀ X : Matrix n n ℂ,
      r.readout () d (recovery.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
      (∑ a, (E a)ᴴ * W * X * W * E a) +
        Matrix.trace ((1 - P) * X) • Matrix.single v v 1

theorem actual_law : arena.{u,v,w}.Law actual := by
  intro n d s _ _ _ _ _ E v
  exact spectral_transpose_candidate E v

theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  obtain ⟨recovery, hr⟩ := h (n := ULift.{u} (Fin 1)) (d := ULift.{v} (Fin 1))
    (s := ULift.{w} (Fin 1)) (fun _ => 0) (ULift.up 0)
  have heq := hr 0
  have hz : (show Matrix (ULift.{v} (Fin 1)) (ULift.{v} (Fin 1)) ℂ from
      fun _ _ => 1) = 0 := by
    simpa [rejected, realize] using heq
  exact one_ne_zero (congrFun (congrFun hz (ULift.up 0)) (ULift.up 0))

def registration : Registration arena.{u,v,w} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      cases i; cases j
      exact (h rfl).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨ULift.{v} (Fin 1), CStarMatrix.ofMatrix (fun _ _ => (0 : ℂ)),
      CStarMatrix.ofMatrix (fun _ _ => (1 : ℂ)), ?_⟩
    intro h
    exact zero_ne_one (congrFun (congrFun h (ULift.up 0)) (ULift.up 0))

noncomputable def registration_2.{u_1, u_2, u_3} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.spectral_transpose_candidate.{u_1, u_2, u_3}) (type_of% (realize.{u_2 + 1, u_2, 0, u_2, 0} signature.{u_2}
    (fun _ _ x => CStarMatrix.ofMatrix.symm x) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Recovery") "SpectralTransposeRecovery") "spectral_transpose_candidate") "Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery/Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2, u_3}) ⟨(registration.{u_1, u_2, u_3})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_2 + 1, u_2, 0, u_2, 0} signature.{u_2}
    (fun _ _ x => CStarMatrix.ofMatrix.symm x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Recovery.SpectralTransposeRecovery, definition := none, coordinates := #[1], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Recovery.SpectralTransposeRecovery, declaration := `D5.S3.Quantum.Recovery.SpectralTransposeRecovery.spectral_transpose_candidate, part := .type, path := [], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] }], facts := [`Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration_2.canonicalArenaFact, `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration_2.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration_2.sourceBridgeFact, `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration_2.observationFact0, `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration_2.anchorEnumeration }


#print axioms registration
end Candidate

end Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery


noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration_1.canonicalArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (max (u_1 + 1) (u_2 + 1)) (u_3 + 1),
  max (max u_1 u_2) u_3, 0, max (max u_1 u_2) u_3, 0} :=
  Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.arena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration_1.canonicalArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralTransposeRecovery\",\"Support\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralTransposeRecovery\",\"Support\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration_1.canonicalObjectArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (max (u_1 + 1) (u_2 + 1)) (u_3 + 1),
  max (max u_1 u_2) u_3, 0, max (max u_1 u_2) u_3, 0} :=
  Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.arena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration_1.canonicalObjectArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralTransposeRecovery\",\"Support\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralTransposeRecovery\",\"Support\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence

noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration_2.canonicalArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_2 + 1, u_2, 0, u_2, 0} :=
  Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.arena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration_2.canonicalArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralTransposeRecovery\",\"Candidate\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralTransposeRecovery\",\"Candidate\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration_2.canonicalObjectArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_2 + 1, u_2, 0, u_2, 0} :=
  Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.arena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration_2.canonicalObjectArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralTransposeRecovery\",\"Candidate\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralTransposeRecovery\",\"Candidate\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration_1.sourceLaw.{u_1, u_2, u_3} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{max (max (u_1 + 1) (u_2 + 1)) (u_3 + 1),
    max (max u_1 u_2) u_3, 0, max (max u_1 u_2) u_3, 0}
  Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.arena.{u_1, u_2, u_3}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{max (max (u_1 + 1) (u_2 + 1))
          (u_3 + 1),
        max (max u_1 u_2) u_3, 0, max (max u_1 u_2) u_3, 0}
    Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.arena.{u_1, u_2, u_3}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{max (max (u_3 + 1) (u_2 + 1)) (u_1 + 1),
        max (max u_3 u_2) u_1, 0, max (max u_3 u_2) u_1, 0}
      Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.arena.{u_1, u_2, u_3}
      Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.actual.{u_1, u_2, u_3})
    Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration.{u_1, u_2, u_3})

noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration_1.sourceBridgeFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralTransposeRecovery\",\"spectral_support_on_kraus\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralTransposeRecovery\",\"Support\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.SpectralTransposeRecovery, declaration := `D5.S3.Quantum.Recovery.SpectralTransposeRecovery.spectral_support_on_kraus, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{max (max (u_1 + 1) (u_2 + 1)) (u_3 + 1),
      max (max u_1 u_2) u_3, 0, max (max u_1 u_2) u_3, 0}
  Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.arena.{u_1, u_2, u_3}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{max (max (u_3 + 1) (u_2 + 1)) (u_1 + 1),
      max (max u_3 u_2) u_1, 0, max (max u_3 u_2) u_1, 0}
    Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.arena.{u_1, u_2, u_3}
    Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.actual.{u_1, u_2, u_3})
  Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration.{u_1, u_2, u_3})

noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration_1.observation0.{u_1, u_2, u_3} : {n : Type u_1} →
  {d : Type u_2} →
    {s : Type u_3} →
      [Fintype.{u_1} n] →
        [DecidableEq.{u_1 + 1} n] →
          [Fintype.{u_2} d] →
            [DecidableEq.{u_2 + 1} d] →
              [Fintype.{u_3} s] →
                (E : s → Matrix.{u_1, u_2, 0} n d Complex) →
                  (a : s) →
                    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{max
                          (max (u_1 + 1) (u_2 + 1)) (u_3 + 1),
                        max (max u_1 u_2) u_3, 0, max (max u_1 u_2) u_3, 0}
                      Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.signature.{u_1, u_2, u_3} Unit.unit
                      (@Sigma.mk.{u_1 + 1, max (u_3 + 1) (u_2 + 1)} (Type u_1)
                        (fun (x : Type u_1) => @Sigma.{u_2 + 1, u_3 + 1} (Type u_2) fun (x : Type u_2) => Type u_3) n
                        (@Sigma.mk.{u_2 + 1, u_3 + 1} (Type u_2) (fun (x : Type u_2) => Type u_3) d s)) :=
  fun {n : Type u_1} {d : Type u_2} {s : Type u_3} [Fintype.{u_1} n] [DecidableEq.{u_1 + 1} n] [Fintype.{u_2} d]
    [DecidableEq.{u_2 + 1} d] [Fintype.{u_3} s] (E : s → Matrix.{u_1, u_2, 0} n d Complex) (a : s) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{max (max (u_1 + 1) (u_2 + 1)) (u_3 + 1),
        max (max u_1 u_2) u_3, 0, max (max u_1 u_2) u_3, 0}
    Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.signature.{u_1, u_2, u_3}
    Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.actual.{u_1, u_2, u_3} Unit.unit
    (@Sigma.mk.{u_1 + 1, max (u_3 + 1) (u_2 + 1)} (Type u_1)
      (fun (x : Type u_1) => @Sigma.{u_2 + 1, u_3 + 1} (Type u_2) fun (x : Type u_2) => Type u_3) n
      (@Sigma.mk.{u_2 + 1, u_3 + 1} (Type u_2) (fun (x : Type u_2) => Type u_3) d s))
    E

noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration_1.observationFact0.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralTransposeRecovery\",\"spectral_support_on_kraus\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"function\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralTransposeRecovery\",\"Support\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.SpectralTransposeRecovery, declaration := `D5.S3.Quantum.Recovery.SpectralTransposeRecovery.spectral_support_on_kraus, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .function], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration_1.varyingLawInput.{u_1, u_2, u_3} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration_1.canonicalArenaOperand.{u_1, u_2, u_3})
noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration_1.varyingLaw.{u_1, u_2, u_3}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralTransposeRecovery\",\"Support\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration_1.statementExclusion.{u_1, u_2, u_3} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralTransposeRecovery\",\"Support\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralTransposeRecovery\",\"spectral_support_on_kraus\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  statementLocation := { owner := `D5.S3.Quantum.Recovery.SpectralTransposeRecovery, declaration := `D5.S3.Quantum.Recovery.SpectralTransposeRecovery.spectral_support_on_kraus, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration.{u_1, u_2, u_3}).actual (Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration.{u_1, u_2, u_3}).variation.2.choose (Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration.{u_1, u_2, u_3}).variation.1 (Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration.{u_1, u_2, u_3}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration_1.descriptorFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralTransposeRecovery\",\"Support\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralTransposeRecovery\",\"Support\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Support.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration_2.sourceLaw.{u_1, u_2, u_3} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_2 + 1, u_2, 0, u_2, 0}
  Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.arena.{u_1, u_2, u_3}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{u_2 + 1, u_2, 0, u_2, 0}
    Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.arena.{u_1, u_2, u_3}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_2 + 1, u_2, 0, u_2, 0}
      Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.arena.{u_1, u_2, u_3}
      Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.actual.{u_2})
    Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration.{u_1, u_2, u_3})

noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration_2.sourceBridgeFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralTransposeRecovery\",\"spectral_transpose_candidate\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralTransposeRecovery\",\"Candidate\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.SpectralTransposeRecovery, declaration := `D5.S3.Quantum.Recovery.SpectralTransposeRecovery.spectral_transpose_candidate, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration_2.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{u_2 + 1, u_2, 0, u_2, 0}
  Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.arena.{u_1, u_2, u_3}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_2 + 1, u_2, 0, u_2, 0}
    Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.arena.{u_1, u_2, u_3}
    Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.actual.{u_2})
  Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration.{u_1, u_2, u_3})

noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration_2.observation0.{u_1, u_2, u_3} : {n : Type u_1} →
  {d : Type u_2} →
    {s : Type u_3} →
      [inst : Fintype.{u_1} n] →
        [inst_1 : DecidableEq.{u_1 + 1} n] →
          [inst_2 : Fintype.{u_2} d] →
            [inst_3 : DecidableEq.{u_2 + 1} d] →
              [Fintype.{u_3} s] →
                (E : s → Matrix.{u_1, u_2, 0} n d Complex) →
                  (v : d) →
                    (recovery :
                        @D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.{u_1, u_2} n d inst inst_1 inst_2
                          inst_3) →
                      (X : Matrix.{u_1, u_1, 0} n n Complex) →
                        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u_2 + 1, u_2, 0, u_2,
                            0}
                          Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.signature.{u_2} Unit.unit d :=
  fun {n : Type u_1} {d : Type u_2} {s : Type u_3} [inst : Fintype.{u_1} n] [inst_1 : DecidableEq.{u_1 + 1} n]
    [inst_2 : Fintype.{u_2} d] [inst_3 : DecidableEq.{u_2 + 1} d] [inst_4 : Fintype.{u_3} s]
    (E : s → Matrix.{u_1, u_2, 0} n d Complex) (v : d) =>
  have Q : Matrix.{u_1, u_1, 0} n n Complex :=
    @Finset.sum.{u_3, u_1} s (Matrix.{u_1, u_1, 0} n n Complex)
      (@Matrix.addCommMonoid.{0, u_1, u_1} n n Complex Complex.instAddCommMonoid) (@Finset.univ.{u_3} s inst_4)
      fun (a : s) =>
      @HMul.hMul.{max u_1 u_2, max u_1 u_2, u_1} (Matrix.{u_1, u_2, 0} n d Complex) (Matrix.{u_2, u_1, 0} d n Complex)
        (Matrix.{u_1, u_1, 0} n n Complex)
        (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_1, u_2, u_1} n d n Complex inst_2 Complex.instMul
          Complex.instAddCommMonoid)
        (E a)
        (@Matrix.conjTranspose.{0, u_1, u_2} n d Complex
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
          (E a));
  have P : Matrix.{u_1, u_1, 0} n n Complex :=
    @D5.S3.Quantum.Recovery.SpectralTransposeRecovery.spectralSupport.{u_1} n inst inst_1 Q;
  have W : Matrix.{u_1, u_1, 0} n n Complex :=
    @D5.S3.Quantum.Recovery.SpectralTransposeRecovery.spectralInverseSqrt.{u_1} n inst inst_1 Q;
  fun (recovery : @D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.{u_1, u_2} n d inst inst_1 inst_2 inst_3)
    (X : Matrix.{u_1, u_1, 0} n n Complex) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u_2 + 1, u_2, 0, u_2, 0}
    Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.signature.{u_2}
    Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.actual.{u_2} Unit.unit d
    (@DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, u_2 + 1}
      (@CompletelyPositiveMap.{u_1, u_2} (CStarMatrix.{u_1, u_1, 0} n n Complex) (CStarMatrix.{u_2, u_2, 0} d d Complex)
        (@CStarMatrix.instNonUnitalCStarAlgebra.{0, u_1} Complex
          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
          Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) n inst)
        (@CStarMatrix.instNonUnitalCStarAlgebra.{0, u_2} Complex
          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
          Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) d inst_2)
        (@CStarMatrix.instPartialOrder.{0, u_1} Complex
          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
          Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) n inst)
        (@CStarMatrix.instPartialOrder.{0, u_2} Complex
          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
          Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) d inst_2)
        (@CStarMatrix.instStarOrderedRing.{0, u_1} Complex
          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
          Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) n inst)
        (@CStarMatrix.instStarOrderedRing.{0, u_2} Complex
          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
          Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) d inst_2))
      (CStarMatrix.{u_1, u_1, 0} n n Complex)
      (fun (x : CStarMatrix.{u_1, u_1, 0} n n Complex) => CStarMatrix.{u_2, u_2, 0} d d Complex)
      (@CompletelyPositiveMap.instFunLike.{u_1, u_2} (CStarMatrix.{u_1, u_1, 0} n n Complex)
        (CStarMatrix.{u_2, u_2, 0} d d Complex)
        (@CStarMatrix.instNonUnitalCStarAlgebra.{0, u_1} Complex
          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
          Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) n inst)
        (@CStarMatrix.instNonUnitalCStarAlgebra.{0, u_2} Complex
          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
          Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) d inst_2)
        (@CStarMatrix.instPartialOrder.{0, u_1} Complex
          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
          Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) n inst)
        (@CStarMatrix.instPartialOrder.{0, u_2} Complex
          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
          Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) d inst_2)
        (@CStarMatrix.instStarOrderedRing.{0, u_1} Complex
          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
          Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) n inst)
        (@CStarMatrix.instStarOrderedRing.{0, u_2} Complex
          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
          Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) d inst_2))
      (@D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.toCompletelyPositiveMap.{u_1, u_2} n d inst inst_1
        inst_2 inst_3 recovery)
      (@DFunLike.coe.{max 1 (u_1 + 1), max 1 (u_1 + 1), max 1 (u_1 + 1)}
        (Equiv.{max 1 (u_1 + 1), max 1 (u_1 + 1)} (Matrix.{u_1, u_1, 0} n n Complex)
          (CStarMatrix.{u_1, u_1, 0} n n Complex))
        (Matrix.{u_1, u_1, 0} n n Complex)
        (fun (x : Matrix.{u_1, u_1, 0} n n Complex) => CStarMatrix.{u_1, u_1, 0} n n Complex)
        (@EquivLike.toFunLike.{max 1 (u_1 + 1), max 1 (u_1 + 1), max 1 (u_1 + 1)}
          (Equiv.{max 1 (u_1 + 1), max 1 (u_1 + 1)} (Matrix.{u_1, u_1, 0} n n Complex)
            (CStarMatrix.{u_1, u_1, 0} n n Complex))
          (Matrix.{u_1, u_1, 0} n n Complex) (CStarMatrix.{u_1, u_1, 0} n n Complex)
          (@Equiv.instEquivLike.{max 1 (u_1 + 1), max 1 (u_1 + 1)} (Matrix.{u_1, u_1, 0} n n Complex)
            (CStarMatrix.{u_1, u_1, 0} n n Complex)))
        (@CStarMatrix.ofMatrix.{u_1, u_1, 0} n n Complex) X))

noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration_2.observationFact0.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralTransposeRecovery\",\"spectral_transpose_candidate\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"letBody\",\"letBody\",\"letBody\",\"argument\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralTransposeRecovery\",\"Candidate\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Quantum.Recovery.SpectralTransposeRecovery, declaration := `D5.S3.Quantum.Recovery.SpectralTransposeRecovery.spectral_transpose_candidate, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .letBody, .letBody, .letBody, .argument, .body, .body, .function, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration_2.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration_2.varyingLawInput.{u_1, u_2, u_3} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration_2.canonicalArenaOperand.{u_1, u_2, u_3})
noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration_2.varyingLaw.{u_1, u_2, u_3}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralTransposeRecovery\",\"Candidate\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration_2.statementExclusion.{u_1, u_2, u_3} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralTransposeRecovery\",\"Candidate\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralTransposeRecovery\",\"spectral_transpose_candidate\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration_2.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  statementLocation := { owner := `D5.S3.Quantum.Recovery.SpectralTransposeRecovery, declaration := `D5.S3.Quantum.Recovery.SpectralTransposeRecovery.spectral_transpose_candidate, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration.{u_1, u_2, u_3}).actual (Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration.{u_1, u_2, u_3}).variation.2.choose (Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration.{u_1, u_2, u_3}).variation.1 (Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration.{u_1, u_2, u_3}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration_2.descriptorFact.{u_2} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralTransposeRecovery\",\"Candidate\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"SpectralTransposeRecovery\",\"Candidate\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery, declaration := `Reg.D5.S3.Quantum.Recovery.SpectralTransposeRecovery.Candidate.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))
