import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Transport.MatrixUnitGenerator
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Transport.MatrixUnitGenerator
open LeanInformationAudit
open scoped Matrix BigOperators ComplexOrder MatrixOrder
open _root_.D5.S3.Quantum.Recovery.MatrixUnitDecoder
noncomputable section
namespace Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator
universe u v w z

namespace Algebraic

abbrev signature : Signature where
  Params := Σ _ : Type u, Type v
  State p := p.1 → p.1 → Matrix p.2 p.2 ℂ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ p := p.1 → p.1 → Matrix p.2 p.2 ℂ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro x; cases x⟩

def actual : Realization signature.{u,v} :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ _ _ _ _ => (1 : ℂ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u,v}
  Law r := ∀ {d : Type u} {n : Type v}
    [Fintype d] [DecidableEq d] [Nonempty d] [Fintype n] [DecidableEq n]
    (F D : d → d → Matrix n n ℂ)
    (hmul : ∀ i j k l, F i j * F k l = if j = k then F i l else 0)
    (hstar : ∀ i j, (F i j)ᴴ = F j i)
    (hD : ∀ i j k l, D i j * F k l + F i j * D k l =
      if j = k then D i l else 0)
    (hDstar : ∀ i j, (D i j)ᴴ = D j i),
    (transportGenerator F D)ᴴ = -transportGenerator F D ∧
      (∀ i j, transportGenerator F D * F i j - F i j * transportGenerator F D =
        r.readout () ⟨d,n⟩ D i j) ∧
      transportGenerator F D * unitSupport F - unitSupport F * transportGenerator F D =
        supportVelocity D

theorem actual_law : arena.{u,v}.Law actual := by
  intro d n _ _ _ _ _ F D hmul hstar hD hDstar
  exact matrix_unit_transport_generator F D hmul hstar hD hDstar

theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have hr := h (d := ULift.{u} (Fin 1)) (n := ULift.{v} (Fin 1))
    (fun _ _ => 0) (fun _ _ => 0)
    (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp)
  have heq := hr.2.1 (ULift.up 0) (ULift.up 0)
  have hz : (0 : Matrix (ULift.{v} (Fin 1)) (ULift.{v} (Fin 1)) ℂ) =
      (fun _ _ => 1) := by simpa [rejected, realize] using heq
  exact zero_ne_one (congrFun (congrFun hz (ULift.up 0)) (ULift.up 0))

def registration : Registration arena.{u,v} (arena.Law actual) where
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
    refine ⟨⟨ULift.{u} (Fin 1), ULift.{v} (Fin 1)⟩,
      (fun _ _ _ _ => (0 : ℂ)), (fun _ _ _ _ => (1 : ℂ)), ?_⟩
    intro h
    exact zero_ne_one (congrFun (congrFun (congrFun (congrFun h
      (ULift.up 0)) (ULift.up 0)) (ULift.up 0)) (ULift.up 0))

noncomputable def registration_1.{u_1, u_2} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Transport.MatrixUnitGenerator.matrix_unit_transport_generator.{u_1, u_2}) (type_of% (realize.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, max u_1 u_2, 0} signature.{u_1, u_2} (fun _ _ x => x) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Transport") "MatrixUnitGenerator") "matrix_unit_transport_generator") "Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator/Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2}) ⟨(registration.{u_1, u_2})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, max u_1 u_2, 0} signature.{u_1, u_2} (fun _ _ x => x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Transport.MatrixUnitGenerator, definition := none, coordinates := #[0, 1], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "body", "body", "arg", "fn", "fn"], stateBinder := 8, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Transport.MatrixUnitGenerator, declaration := `D5.S3.Quantum.Transport.MatrixUnitGenerator.matrix_unit_transport_generator, part := .type, path := [], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator, declaration := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator, declaration := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator, declaration := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator, declaration := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2] }], facts := [`Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration_1.observationFact0, `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration_1.anchorEnumeration }


#print axioms registration
end Algebraic

namespace RealPath

abbrev signature : Signature where
  Params := Σ _ : Type u, Type v
  State p := p.1 → p.1 → Matrix p.2 p.2 ℂ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ p := p.1 → p.1 → Matrix p.2 p.2 ℂ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro x; cases x⟩

def actual : Realization signature.{u,v} :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ _ _ _ _ => (1 : ℂ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u,v}
  Law r := ∀ {d : Type u} {n : Type v}
    [Fintype d] [DecidableEq d] [Nonempty d] [Fintype n] [DecidableEq n]
    (F : ℝ → d → d → Matrix n n ℂ) (D : d → d → Matrix n n ℂ) (t : ℝ)
    (hmul : ∀ u i j k l, F u i j * F u k l = if j = k then F u i l else 0)
    (hstar : ∀ u i j, (F u i j)ᴴ = F u j i)
    (hderiv : ∀ i j a b, HasDerivAt (fun u => F u i j a b) (D i j a b) t),
    (transportGenerator (F t) D)ᴴ = -transportGenerator (F t) D ∧
      (∀ i j, transportGenerator (F t) D * F t i j - F t i j * transportGenerator (F t) D =
        r.readout () ⟨d,n⟩ D i j) ∧
      transportGenerator (F t) D * unitSupport (F t) -
        unitSupport (F t) * transportGenerator (F t) D = supportVelocity D

theorem actual_law : arena.{u,v}.Law actual := by
  intro d n _ _ _ _ _ F D t hmul hstar hderiv
  exact generator_from_real_path F D t hmul hstar hderiv

theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have hr := h (d := ULift.{u} (Fin 1)) (n := ULift.{v} (Fin 1))
    (fun _ _ _ => 0) (fun _ _ => 0) 0
    (by intros; simp) (by intros; simp)
    (by intros; exact hasDerivAt_const _ _)
  have heq := hr.2.1 (ULift.up 0) (ULift.up 0)
  have hz : (0 : Matrix (ULift.{v} (Fin 1)) (ULift.{v} (Fin 1)) ℂ) =
      (fun _ _ => 1) := by simpa [rejected, realize] using heq
  exact zero_ne_one (congrFun (congrFun hz (ULift.up 0)) (ULift.up 0))

def registration : Registration arena.{u,v} (arena.Law actual) where
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
    refine ⟨⟨ULift.{u} (Fin 1), ULift.{v} (Fin 1)⟩,
      (fun _ _ _ _ => (0 : ℂ)), (fun _ _ _ _ => (1 : ℂ)), ?_⟩
    intro h
    exact zero_ne_one (congrFun (congrFun (congrFun (congrFun h
      (ULift.up 0)) (ULift.up 0)) (ULift.up 0)) (ULift.up 0))

noncomputable def registration_2.{u_1, u_2} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Transport.MatrixUnitGenerator.generator_from_real_path.{u_1, u_2}) (type_of% (realize.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, max u_1 u_2, 0} signature.{u_1, u_2} (fun _ _ x => x) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Transport") "MatrixUnitGenerator") "generator_from_real_path") "Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator/Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2}) ⟨(registration.{u_1, u_2})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, max u_1 u_2, 0} signature.{u_1, u_2} (fun _ _ x => x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Transport.MatrixUnitGenerator, definition := none, coordinates := #[0, 1], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "body", "body", "arg", "fn", "fn"], stateBinder := 8, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Transport.MatrixUnitGenerator, declaration := `D5.S3.Quantum.Transport.MatrixUnitGenerator.generator_from_real_path, part := .type, path := [], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator, declaration := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator, declaration := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator, declaration := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator, declaration := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2] }], facts := [`Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration_2.canonicalArenaFact, `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration_2.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration_2.sourceBridgeFact, `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration_2.observationFact0, `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration_2.anchorEnumeration }


#print axioms registration
end RealPath

end Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator


noncomputable def Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration_2.canonicalArenaOperand.{u_1, u_2} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, max u_1 u_2, 0} :=
  Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.arena.{u_1, u_2}
noncomputable def Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration_2.canonicalArenaFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Transport\",\"MatrixUnitGenerator\",\"RealPath\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Transport\",\"MatrixUnitGenerator\",\"RealPath\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator, declaration := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator, declaration := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration_2.canonicalObjectArenaOperand.{u_1, u_2} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, max u_1 u_2, 0} :=
  Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.arena.{u_1, u_2}
noncomputable def Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration_2.canonicalObjectArenaFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Transport\",\"MatrixUnitGenerator\",\"RealPath\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Transport\",\"MatrixUnitGenerator\",\"RealPath\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator, declaration := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator, declaration := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  .evidence

noncomputable def Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration_1.canonicalArenaOperand.{u_1, u_2} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, max u_1 u_2, 0} :=
  Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.arena.{u_1, u_2}
noncomputable def Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration_1.canonicalArenaFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Transport\",\"MatrixUnitGenerator\",\"Algebraic\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Transport\",\"MatrixUnitGenerator\",\"Algebraic\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator, declaration := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator, declaration := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration_1.canonicalObjectArenaOperand.{u_1, u_2} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, max u_1 u_2, 0} :=
  Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.arena.{u_1, u_2}
noncomputable def Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration_1.canonicalObjectArenaFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Transport\",\"MatrixUnitGenerator\",\"Algebraic\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Transport\",\"MatrixUnitGenerator\",\"Algebraic\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator, declaration := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator, declaration := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration_2.sourceLaw.{u_1, u_2} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, max u_1 u_2,
    0} (Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.arena.) (Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration.{u_1, u_2}).actual

noncomputable def Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration_2.sourceBridgeFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Transport\",\"MatrixUnitGenerator\",\"generator_from_real_path\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Transport\",\"MatrixUnitGenerator\",\"RealPath\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `D5.S3.Quantum.Transport.MatrixUnitGenerator, declaration := `D5.S3.Quantum.Transport.MatrixUnitGenerator.generator_from_real_path, part := .type, path := [], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator, declaration := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration_2.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  (Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration.{u_1, u_2}).bridge

noncomputable def Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration_2.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration_2.observation0.{u_1, u_2} : {d : Type u_1} →
  {n : Type u_2} →
    [Fintype.{u_1} d] →
      [inst : DecidableEq.{u_1 + 1} d] →
        [Nonempty.{u_1 + 1} d] →
          [inst_2 : Fintype.{u_2} n] →
            [DecidableEq.{u_2 + 1} n] →
              (F : Real → d → d → Matrix.{u_2, u_2, 0} n n Complex) →
                (D : d → d → Matrix.{u_2, u_2, 0} n n Complex) →
                  (t : Real) →
                    (hmul :
                        ∀ (u : Real) (i j k l : d),
                          @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
                            (@HMul.hMul.{u_2, u_2, u_2} (Matrix.{u_2, u_2, 0} n n Complex)
                              (Matrix.{u_2, u_2, 0} n n Complex) (Matrix.{u_2, u_2, 0} n n Complex)
                              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_2, u_2, u_2} n n n Complex inst_2
                                Complex.instMul Complex.instAddCommMonoid)
                              (F u i j) (F u k l))
                            (@ite.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex) (@Eq.{u_1 + 1} d j k) (inst j k)
                              (F u i l)
                              (@OfNat.ofNat.{u_2} (Matrix.{u_2, u_2, 0} n n Complex) (nat_lit 0)
                                (@Zero.toOfNat0.{u_2} (Matrix.{u_2, u_2, 0} n n Complex)
                                  (@Matrix.zero.{0, u_2, u_2} n n Complex Complex.instZero))))) →
                      (hstar :
                          ∀ (u : Real) (i j : d),
                            @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
                              (@Matrix.conjTranspose.{0, u_2, u_2} n n Complex
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
                                (F u i j))
                              (F u j i)) →
                        (hderiv :
                            ∀ (i j : d) (a b : n),
                              @HasDerivAt.{0, 0} Real
                                (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Complex
                                Complex.addCommGroup
                                (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                        (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                            instCommCStarAlgebraComplex)))))
                                  (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                          (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                            (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                              instCommCStarAlgebraComplex)))))
                                    instInnerProductSpaceRealComplex))
                                (@UniformSpace.toTopologicalSpace.{0} Complex
                                  (@PseudoMetricSpace.toUniformSpace.{0} Complex
                                    (@SeminormedRing.toPseudoMetricSpace.{0} Complex
                                      (@SeminormedCommRing.toSeminormedRing.{0} Complex
                                        (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                          (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                            instCommCStarAlgebraComplex))))))
                                (@IsBoundedSMul.continuousSMul.{0, 0} Real Complex Real.pseudoMetricSpace
                                  (@SeminormedRing.toPseudoMetricSpace.{0} Complex
                                    (@SeminormedCommRing.toSeminormedRing.{0} Complex
                                      (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                        (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex))))
                                  Real.instZero Complex.instZero
                                  (@SMulZeroClass.toSMul.{0, 0} Real Complex
                                    (@AddZero.toZero.{0} Complex
                                      (@AddZeroClass.toAddZero.{0} Complex
                                        (@AddMonoid.toAddZeroClass.{0} Complex
                                          (@SubNegMonoid.toAddMonoid.{0} Complex
                                            (@AddGroup.toSubNegMonoid.{0} Complex
                                              (@AddCommGroup.toAddGroup.{0} Complex Complex.addCommGroup))))))
                                    (@DistribSMul.toSMulZeroClass.{0, 0} Real Complex
                                      (@AddMonoid.toAddZeroClass.{0} Complex
                                        (@SubNegMonoid.toAddMonoid.{0} Complex
                                          (@AddGroup.toSubNegMonoid.{0} Complex
                                            (@AddCommGroup.toAddGroup.{0} Complex Complex.addCommGroup))))
                                      (@DistribMulAction.toDistribSMul.{0, 0} Real Complex
                                        (@Semiring.toMonoid.{0} Real
                                          (@DivisionSemiring.toSemiring.{0} Real
                                            (@Semifield.toDivisionSemiring.{0} Real
                                              (@Field.toSemifield.{0} Real
                                                (@NormedField.toField.{0} Real
                                                  (@NontriviallyNormedField.toNormedField.{0} Real
                                                    (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                                      Real.denselyNormedField)))))))
                                        (@SubNegMonoid.toAddMonoid.{0} Complex
                                          (@AddGroup.toSubNegMonoid.{0} Complex
                                            (@AddCommGroup.toAddGroup.{0} Complex Complex.addCommGroup)))
                                        (@Module.toDistribMulAction.{0, 0} Real Complex
                                          (@DivisionSemiring.toSemiring.{0} Real
                                            (@Semifield.toDivisionSemiring.{0} Real
                                              (@Field.toSemifield.{0} Real
                                                (@NormedField.toField.{0} Real
                                                  (@NontriviallyNormedField.toNormedField.{0} Real
                                                    (@DenselyNormedField.toNontriviallyNormedField.{0} Real
                                                      Real.denselyNormedField))))))
                                          (@AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup)
                                          (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                                            (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                              (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                                (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                                  (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                                    (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                                      instCommCStarAlgebraComplex)))))
                                            (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                              (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                                (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                                  (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                                    (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                                      (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                                        instCommCStarAlgebraComplex)))))
                                              instInnerProductSpaceRealComplex))))))
                                  (@NormedSpace.toIsBoundedSMul.{0, 0} Real Complex Real.normedField
                                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                          (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                            (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                              instCommCStarAlgebraComplex)))))
                                    (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                                      (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                                        (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                                          (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                                            (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                              (@CommCStarAlgebra.toNormedCommRing.{0} Complex
                                                instCommCStarAlgebraComplex)))))
                                      instInnerProductSpaceRealComplex)))
                                (fun (u : Real) => F u i j a b) (D i j a b) t) →
                          (i j : d) →
                            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{max (u_1 + 1)
                                  (u_2 + 1),
                                max u_1 u_2, 0, max u_1 u_2, 0}
                              Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.signature.{u_1, u_2} Unit.unit
                              (@Sigma.mk.{u_1 + 1, u_2 + 1} (Type u_1) (fun (x : Type u_1) => Type u_2) d n) :=
  fun {d : Type u_1} {n : Type u_2} [Fintype.{u_1} d] [DecidableEq.{u_1 + 1} d] [Nonempty.{u_1 + 1} d] [Fintype.{u_2} n]
    [DecidableEq.{u_2 + 1} n] (F : Real → d → d → Matrix.{u_2, u_2, 0} n n Complex)
    (D : d → d → Matrix.{u_2, u_2, 0} n n Complex) (t : Real)
    (hmul :
      ∀ (u : Real) (i j k l : d),
        @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
          (@HMul.hMul.{u_2, u_2, u_2} (Matrix.{u_2, u_2, 0} n n Complex) (Matrix.{u_2, u_2, 0} n n Complex)
            (Matrix.{u_2, u_2, 0} n n Complex)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_2, u_2, u_2} n n n Complex inst_3 Complex.instMul
              Complex.instAddCommMonoid)
            (F u i j) (F u k l))
          (@ite.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex) (@Eq.{u_1 + 1} d j k) (inst_1 j k) (F u i l)
            (@OfNat.ofNat.{u_2} (Matrix.{u_2, u_2, 0} n n Complex) (nat_lit 0)
              (@Zero.toOfNat0.{u_2} (Matrix.{u_2, u_2, 0} n n Complex)
                (@Matrix.zero.{0, u_2, u_2} n n Complex Complex.instZero)))))
    (hstar :
      ∀ (u : Real) (i j : d),
        @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
          (@Matrix.conjTranspose.{0, u_2, u_2} n n Complex
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
            (F u i j))
          (F u j i))
    (hderiv :
      ∀ (i j : d) (a b : n),
        @HasDerivAt.{0, 0} Real (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField) Complex
          Complex.addCommGroup
          (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
            (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
              (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                  (@NormedCommRing.toSeminormedCommRing.{0} Complex
                    (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex)))))
            (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
              (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                  (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                    (@NormedCommRing.toSeminormedCommRing.{0} Complex
                      (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex)))))
              instInnerProductSpaceRealComplex))
          (@UniformSpace.toTopologicalSpace.{0} Complex
            (@PseudoMetricSpace.toUniformSpace.{0} Complex
              (@SeminormedRing.toPseudoMetricSpace.{0} Complex
                (@SeminormedCommRing.toSeminormedRing.{0} Complex
                  (@NormedCommRing.toSeminormedCommRing.{0} Complex
                    (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex))))))
          (@IsBoundedSMul.continuousSMul.{0, 0} Real Complex Real.pseudoMetricSpace
            (@SeminormedRing.toPseudoMetricSpace.{0} Complex
              (@SeminormedCommRing.toSeminormedRing.{0} Complex
                (@NormedCommRing.toSeminormedCommRing.{0} Complex
                  (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex))))
            Real.instZero Complex.instZero
            (@SMulZeroClass.toSMul.{0, 0} Real Complex
              (@AddZero.toZero.{0} Complex
                (@AddZeroClass.toAddZero.{0} Complex
                  (@AddMonoid.toAddZeroClass.{0} Complex
                    (@SubNegMonoid.toAddMonoid.{0} Complex
                      (@AddGroup.toSubNegMonoid.{0} Complex
                        (@AddCommGroup.toAddGroup.{0} Complex Complex.addCommGroup))))))
              (@DistribSMul.toSMulZeroClass.{0, 0} Real Complex
                (@AddMonoid.toAddZeroClass.{0} Complex
                  (@SubNegMonoid.toAddMonoid.{0} Complex
                    (@AddGroup.toSubNegMonoid.{0} Complex (@AddCommGroup.toAddGroup.{0} Complex Complex.addCommGroup))))
                (@DistribMulAction.toDistribSMul.{0, 0} Real Complex
                  (@Semiring.toMonoid.{0} Real
                    (@DivisionSemiring.toSemiring.{0} Real
                      (@Semifield.toDivisionSemiring.{0} Real
                        (@Field.toSemifield.{0} Real
                          (@NormedField.toField.{0} Real
                            (@NontriviallyNormedField.toNormedField.{0} Real
                              (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField)))))))
                  (@SubNegMonoid.toAddMonoid.{0} Complex
                    (@AddGroup.toSubNegMonoid.{0} Complex (@AddCommGroup.toAddGroup.{0} Complex Complex.addCommGroup)))
                  (@Module.toDistribMulAction.{0, 0} Real Complex
                    (@DivisionSemiring.toSemiring.{0} Real
                      (@Semifield.toDivisionSemiring.{0} Real
                        (@Field.toSemifield.{0} Real
                          (@NormedField.toField.{0} Real
                            (@NontriviallyNormedField.toNormedField.{0} Real
                              (@DenselyNormedField.toNontriviallyNormedField.{0} Real Real.denselyNormedField))))))
                    (@AddCommGroup.toAddCommMonoid.{0} Complex Complex.addCommGroup)
                    (@NormedSpace.toModule.{0, 0} Real Complex Real.normedField
                      (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                        (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                          (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                            (@NormedCommRing.toSeminormedCommRing.{0} Complex
                              (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex)))))
                      (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                            (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                              (@NormedCommRing.toSeminormedCommRing.{0} Complex
                                (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex)))))
                        instInnerProductSpaceRealComplex))))))
            (@NormedSpace.toIsBoundedSMul.{0, 0} Real Complex Real.normedField
              (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                  (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                    (@NormedCommRing.toSeminormedCommRing.{0} Complex
                      (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex)))))
              (@InnerProductSpace.toNormedSpace.{0, 0} Real Complex Real.instRCLike
                (@NonUnitalSeminormedRing.toSeminormedAddCommGroup.{0} Complex
                  (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing.{0} Complex
                    (@SeminormedCommRing.toNonUnitalSeminormedCommRing.{0} Complex
                      (@NormedCommRing.toSeminormedCommRing.{0} Complex
                        (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex)))))
                instInnerProductSpaceRealComplex)))
          (fun (u : Real) => F u i j a b) (D i j a b) t)
    (i j : d) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0,
        max u_1 u_2, 0}
    Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.signature.{u_1, u_2}
    Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.actual.{u_1, u_2} Unit.unit
    (@Sigma.mk.{u_1 + 1, u_2 + 1} (Type u_1) (fun (x : Type u_1) => Type u_2) d n) D

noncomputable def Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration_2.observationFact0.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Transport\",\"MatrixUnitGenerator\",\"generator_from_real_path\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"function\",\"argument\",\"body\",\"body\",\"argument\",\"function\",\"function\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Transport\",\"MatrixUnitGenerator\",\"RealPath\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `D5.S3.Quantum.Transport.MatrixUnitGenerator, declaration := `D5.S3.Quantum.Transport.MatrixUnitGenerator.generator_from_real_path, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .function, .argument, .body, .body, .argument, .function, .function], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator, declaration := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration_2.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration_2.varyingLawInput.{u_1, u_2} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration_2.canonicalArenaOperand.{u_1, u_2})
noncomputable def Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration_2.varyingLaw.{u_1, u_2}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Transport\",\"MatrixUnitGenerator\",\"RealPath\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration_2.statementExclusion.{u_1, u_2} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Transport\",\"MatrixUnitGenerator\",\"RealPath\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Transport\",\"MatrixUnitGenerator\",\"generator_from_real_path\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator, declaration := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration_2.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  statementLocation := { owner := `D5.S3.Quantum.Transport.MatrixUnitGenerator, declaration := `D5.S3.Quantum.Transport.MatrixUnitGenerator.generator_from_real_path, part := .type, path := [], levels := [(.param `u_1), (.param `u_2)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration.{u_1, u_2}).actual (Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration.{u_1, u_2}).variation.2.choose (Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration.{u_1, u_2}).variation.1 (Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration.{u_1, u_2}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration_2.descriptorFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Transport\",\"MatrixUnitGenerator\",\"RealPath\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Transport\",\"MatrixUnitGenerator\",\"RealPath\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator, declaration := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator, declaration := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.RealPath.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration_1.sourceLaw.{u_1, u_2} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, max u_1 u_2,
    0} (Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.arena.) (Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration.{u_1, u_2}).actual

noncomputable def Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration_1.sourceBridgeFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Transport\",\"MatrixUnitGenerator\",\"matrix_unit_transport_generator\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Transport\",\"MatrixUnitGenerator\",\"Algebraic\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `D5.S3.Quantum.Transport.MatrixUnitGenerator, declaration := `D5.S3.Quantum.Transport.MatrixUnitGenerator.matrix_unit_transport_generator, part := .type, path := [], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator, declaration := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  (Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration.{u_1, u_2}).bridge

noncomputable def Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration_1.observation0.{u_1, u_2} : {d : Type u_1} →
  {n : Type u_2} →
    [Fintype.{u_1} d] →
      [inst : DecidableEq.{u_1 + 1} d] →
        [Nonempty.{u_1 + 1} d] →
          [inst_2 : Fintype.{u_2} n] →
            [DecidableEq.{u_2 + 1} n] →
              (F D : d → d → Matrix.{u_2, u_2, 0} n n Complex) →
                (hmul :
                    ∀ (i j k l : d),
                      @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
                        (@HMul.hMul.{u_2, u_2, u_2} (Matrix.{u_2, u_2, 0} n n Complex)
                          (Matrix.{u_2, u_2, 0} n n Complex) (Matrix.{u_2, u_2, 0} n n Complex)
                          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_2, u_2, u_2} n n n Complex inst_2
                            Complex.instMul Complex.instAddCommMonoid)
                          (F i j) (F k l))
                        (@ite.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex) (@Eq.{u_1 + 1} d j k) (inst j k) (F i l)
                          (@OfNat.ofNat.{u_2} (Matrix.{u_2, u_2, 0} n n Complex) (nat_lit 0)
                            (@Zero.toOfNat0.{u_2} (Matrix.{u_2, u_2, 0} n n Complex)
                              (@Matrix.zero.{0, u_2, u_2} n n Complex Complex.instZero))))) →
                  (hstar :
                      ∀ (i j : d),
                        @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
                          (@Matrix.conjTranspose.{0, u_2, u_2} n n Complex
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
                            (F i j))
                          (F j i)) →
                    (hD :
                        ∀ (i j k l : d),
                          @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
                            (@HAdd.hAdd.{u_2, u_2, u_2} (Matrix.{u_2, u_2, 0} n n Complex)
                              (Matrix.{u_2, u_2, 0} n n Complex) (Matrix.{u_2, u_2, 0} n n Complex)
                              (@instHAdd.{u_2} (Matrix.{u_2, u_2, 0} n n Complex)
                                (@Matrix.add.{0, u_2, u_2} n n Complex Complex.instAdd))
                              (@HMul.hMul.{u_2, u_2, u_2} (Matrix.{u_2, u_2, 0} n n Complex)
                                (Matrix.{u_2, u_2, 0} n n Complex) (Matrix.{u_2, u_2, 0} n n Complex)
                                (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_2, u_2, u_2} n n n Complex inst_2
                                  Complex.instMul Complex.instAddCommMonoid)
                                (D i j) (F k l))
                              (@HMul.hMul.{u_2, u_2, u_2} (Matrix.{u_2, u_2, 0} n n Complex)
                                (Matrix.{u_2, u_2, 0} n n Complex) (Matrix.{u_2, u_2, 0} n n Complex)
                                (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_2, u_2, u_2} n n n Complex inst_2
                                  Complex.instMul Complex.instAddCommMonoid)
                                (F i j) (D k l)))
                            (@ite.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex) (@Eq.{u_1 + 1} d j k) (inst j k) (D i l)
                              (@OfNat.ofNat.{u_2} (Matrix.{u_2, u_2, 0} n n Complex) (nat_lit 0)
                                (@Zero.toOfNat0.{u_2} (Matrix.{u_2, u_2, 0} n n Complex)
                                  (@Matrix.zero.{0, u_2, u_2} n n Complex Complex.instZero))))) →
                      (hDstar :
                          ∀ (i j : d),
                            @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
                              (@Matrix.conjTranspose.{0, u_2, u_2} n n Complex
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
                                (D i j))
                              (D j i)) →
                        (i j : d) →
                          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{max (u_1 + 1)
                                (u_2 + 1),
                              max u_1 u_2, 0, max u_1 u_2, 0}
                            Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.signature.{u_1, u_2} Unit.unit
                            (@Sigma.mk.{u_1 + 1, u_2 + 1} (Type u_1) (fun (x : Type u_1) => Type u_2) d n) :=
  fun {d : Type u_1} {n : Type u_2} [Fintype.{u_1} d] [DecidableEq.{u_1 + 1} d] [Nonempty.{u_1 + 1} d] [Fintype.{u_2} n]
    [DecidableEq.{u_2 + 1} n] (F D : d → d → Matrix.{u_2, u_2, 0} n n Complex)
    (hmul :
      ∀ (i j k l : d),
        @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
          (@HMul.hMul.{u_2, u_2, u_2} (Matrix.{u_2, u_2, 0} n n Complex) (Matrix.{u_2, u_2, 0} n n Complex)
            (Matrix.{u_2, u_2, 0} n n Complex)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_2, u_2, u_2} n n n Complex inst_3 Complex.instMul
              Complex.instAddCommMonoid)
            (F i j) (F k l))
          (@ite.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex) (@Eq.{u_1 + 1} d j k) (inst_1 j k) (F i l)
            (@OfNat.ofNat.{u_2} (Matrix.{u_2, u_2, 0} n n Complex) (nat_lit 0)
              (@Zero.toOfNat0.{u_2} (Matrix.{u_2, u_2, 0} n n Complex)
                (@Matrix.zero.{0, u_2, u_2} n n Complex Complex.instZero)))))
    (hstar :
      ∀ (i j : d),
        @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
          (@Matrix.conjTranspose.{0, u_2, u_2} n n Complex
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
            (F i j))
          (F j i))
    (hD :
      ∀ (i j k l : d),
        @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
          (@HAdd.hAdd.{u_2, u_2, u_2} (Matrix.{u_2, u_2, 0} n n Complex) (Matrix.{u_2, u_2, 0} n n Complex)
            (Matrix.{u_2, u_2, 0} n n Complex)
            (@instHAdd.{u_2} (Matrix.{u_2, u_2, 0} n n Complex) (@Matrix.add.{0, u_2, u_2} n n Complex Complex.instAdd))
            (@HMul.hMul.{u_2, u_2, u_2} (Matrix.{u_2, u_2, 0} n n Complex) (Matrix.{u_2, u_2, 0} n n Complex)
              (Matrix.{u_2, u_2, 0} n n Complex)
              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_2, u_2, u_2} n n n Complex inst_3 Complex.instMul
                Complex.instAddCommMonoid)
              (D i j) (F k l))
            (@HMul.hMul.{u_2, u_2, u_2} (Matrix.{u_2, u_2, 0} n n Complex) (Matrix.{u_2, u_2, 0} n n Complex)
              (Matrix.{u_2, u_2, 0} n n Complex)
              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_2, u_2, u_2} n n n Complex inst_3 Complex.instMul
                Complex.instAddCommMonoid)
              (F i j) (D k l)))
          (@ite.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex) (@Eq.{u_1 + 1} d j k) (inst_1 j k) (D i l)
            (@OfNat.ofNat.{u_2} (Matrix.{u_2, u_2, 0} n n Complex) (nat_lit 0)
              (@Zero.toOfNat0.{u_2} (Matrix.{u_2, u_2, 0} n n Complex)
                (@Matrix.zero.{0, u_2, u_2} n n Complex Complex.instZero)))))
    (hDstar :
      ∀ (i j : d),
        @Eq.{u_2 + 1} (Matrix.{u_2, u_2, 0} n n Complex)
          (@Matrix.conjTranspose.{0, u_2, u_2} n n Complex
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
            (D i j))
          (D j i))
    (i j : d) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0,
        max u_1 u_2, 0}
    Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.signature.{u_1, u_2}
    Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.actual.{u_1, u_2} Unit.unit
    (@Sigma.mk.{u_1 + 1, u_2 + 1} (Type u_1) (fun (x : Type u_1) => Type u_2) d n) D

noncomputable def Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration_1.observationFact0.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Transport\",\"MatrixUnitGenerator\",\"matrix_unit_transport_generator\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"function\",\"argument\",\"body\",\"body\",\"argument\",\"function\",\"function\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Transport\",\"MatrixUnitGenerator\",\"Algebraic\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `D5.S3.Quantum.Transport.MatrixUnitGenerator, declaration := `D5.S3.Quantum.Transport.MatrixUnitGenerator.matrix_unit_transport_generator, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .function, .argument, .body, .body, .argument, .function, .function], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator, declaration := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration_1.varyingLawInput.{u_1, u_2} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration_1.canonicalArenaOperand.{u_1, u_2})
noncomputable def Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration_1.varyingLaw.{u_1, u_2}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Transport\",\"MatrixUnitGenerator\",\"Algebraic\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration_1.statementExclusion.{u_1, u_2} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Transport\",\"MatrixUnitGenerator\",\"Algebraic\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Transport\",\"MatrixUnitGenerator\",\"matrix_unit_transport_generator\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator, declaration := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  statementLocation := { owner := `D5.S3.Quantum.Transport.MatrixUnitGenerator, declaration := `D5.S3.Quantum.Transport.MatrixUnitGenerator.matrix_unit_transport_generator, part := .type, path := [], levels := [(.param `u_1), (.param `u_2)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration.{u_1, u_2}).actual (Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration.{u_1, u_2}).variation.2.choose (Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration.{u_1, u_2}).variation.1 (Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration.{u_1, u_2}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration_1.descriptorFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Transport\",\"MatrixUnitGenerator\",\"Algebraic\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Transport\",\"MatrixUnitGenerator\",\"Algebraic\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator, declaration := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator, declaration := `Reg.D5.S3.Quantum.Transport.MatrixUnitGenerator.Algebraic.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2)] }
  (by first | rfl | (ext <;> rfl))
