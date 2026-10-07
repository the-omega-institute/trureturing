import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix

noncomputable section
namespace Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse
universe u v

abbrev Params := Σ (_ : Type u), Type v

abbrev signature : Signature where
  Params := Params.{u,v}
  State p := Matrix p.1 p.2 ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix p.1 p.2 ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ _ matrix => matrix) (fun anchor => nomatch anchor)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ => fun _ _ => 1) (fun anchor => nomatch anchor)

def arena : Arena where
  signature := signature.{u,v}
  Law realization := ∀ {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A : Matrix m n ℤ) (_hA : A.IsTotallyUnimodular),
      ∃ B : Matrix n m ℤ, A * B * A = realization.readout () ⟨m, n⟩ A

theorem rejected_law : ¬ arena.Law rejected.{u,v} := by
  classical
  intro law
  have hzero : (0 : Matrix (ULift.{u} Unit) (ULift.{v} Unit) ℤ).IsTotallyUnimodular := by
    intro size rows cols _ _
    cases size with
    | zero => exact ⟨1, by simp⟩
    | succ size => exact ⟨0, by simp⟩
  obtain ⟨inverse, heq⟩ := law (0 : Matrix (ULift.{u} Unit) (ULift.{v} Unit) ℤ) hzero
  have hentry := congrArg (fun matrix => matrix ⟨()⟩ ⟨()⟩) heq
  simp [rejected, realize] at hentry

theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro role
  refine ⟨⟨ULift.{u} Unit, ULift.{v} Unit⟩, 0, (fun _ _ => 1), ?_⟩
  intro heq
  have hentry := congrArg (fun matrix => matrix ⟨()⟩ ⟨()⟩) heq
  change (0 : ℤ) = 1 at hentry
  exact zero_ne_one hentry

def registration : Registration arena.{u,v} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨
    @_root_.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.exists_integer_inner_inverse.{u,v},
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (show other = role from @Subsingleton.elim Unit _ other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := dependence

noncomputable def registration_1.{u_1, u_2} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.exists_integer_inner_inverse.{u_1, u_2}) (type_of% (realize.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, max u_1 u_2, 0} signature.{u_1, u_2} (fun _ _ matrix => matrix) (fun anchor => nomatch anchor))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "HomologicalAlgebra") "IntegerMatrixInnerInverse") "exists_integer_inner_inverse") "Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse/Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2}) ⟨(registration.{u_1, u_2})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, max u_1 u_2, 0} signature.{u_1, u_2} (fun _ _ matrix => matrix) (fun anchor => nomatch anchor)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse, definition := none, coordinates := #[0, 1], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse, declaration := `D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.exists_integer_inner_inverse, part := .type, path := [], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse, declaration := `Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse, declaration := `Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse, declaration := `Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse, declaration := `Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2] }], facts := [`Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration_1.canonicalArenaFact, `Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration_1.sourceBridgeFact, `Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration_1.observationFact0, `Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration_1.anchorEnumeration }


#print axioms registration
end Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse


noncomputable def Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration_1.canonicalArenaOperand.{u_1, u_2} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, max u_1 u_2, 0} :=
  Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.arena.{u_1, u_2}
noncomputable def Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration_1.canonicalArenaFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"HomologicalAlgebra\",\"IntegerMatrixInnerInverse\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"HomologicalAlgebra\",\"IntegerMatrixInnerInverse\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse, declaration := `Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse, declaration := `Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  .evidence
noncomputable def Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration_1.canonicalObjectArenaOperand.{u_1, u_2} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, max u_1 u_2, 0} :=
  Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.arena.{u_1, u_2}
noncomputable def Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration_1.canonicalObjectArenaFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"HomologicalAlgebra\",\"IntegerMatrixInnerInverse\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"HomologicalAlgebra\",\"IntegerMatrixInnerInverse\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse, declaration := `Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse, declaration := `Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  .evidence


noncomputable def Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration_1.sourceLaw.{u_1, u_2} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, max u_1 u_2,
    0}
  Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.arena.{u_1, u_2}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{max (u_1 + 1) (u_2 + 1), max u_1 u_2,
        0, max u_1 u_2, 0}
    Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.arena.{u_1, u_2}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{max (u_2 + 1) (u_1 + 1), max u_2 u_1, 0,
        max u_2 u_1, 0}
      Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.arena.{u_1, u_2}
      Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.actual.{u_1, u_2})
    Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration.{u_1, u_2})

noncomputable def Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration_1.sourceBridgeFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"HomologicalAlgebra\",\"IntegerMatrixInnerInverse\",\"exists_integer_inner_inverse\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"HomologicalAlgebra\",\"IntegerMatrixInnerInverse\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse, declaration := `D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.exists_integer_inner_inverse, part := .type, path := [], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse, declaration := `Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0,
      max u_1 u_2, 0}
  Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.arena.{u_1, u_2}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{max (u_2 + 1) (u_1 + 1), max u_2 u_1, 0,
      max u_2 u_1, 0}
    Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.arena.{u_1, u_2}
    Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.actual.{u_1, u_2})
  Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration.{u_1, u_2})

noncomputable def Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration_1.observation0.{u_1, u_2} : {m : Type u_1} →
  {n : Type u_2} →
    [Fintype.{u_1} m] →
      [Fintype.{u_2} n] →
        (A : Matrix.{u_1, u_2, 0} m n Int) →
          (hA : @Matrix.IsTotallyUnimodular.{u_1, u_2, 0} m n Int Int.instCommRing A) →
            (B : Matrix.{u_2, u_1, 0} n m Int) →
              D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{max (u_1 + 1) (u_2 + 1),
                  max u_1 u_2, 0, max u_1 u_2, 0}
                Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.signature.{u_1, u_2} PUnit.unit.{1}
                (@Sigma.mk.{u_1 + 1, u_2 + 1} (Type u_1) (fun (x : Type u_1) => Type u_2) m n) :=
  fun {m : Type u_1} {n : Type u_2} [Fintype.{u_1} m] [Fintype.{u_2} n] (A : Matrix.{u_1, u_2, 0} m n Int)
    (hA : @Matrix.IsTotallyUnimodular.{u_1, u_2, 0} m n Int Int.instCommRing A) (B : Matrix.{u_2, u_1, 0} n m Int) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0,
        max u_1 u_2, 0}
    Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.signature.{u_1, u_2}
    Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.actual.{u_1, u_2} PUnit.unit.{1}
    (@Sigma.mk.{u_1 + 1, u_2 + 1} (Type u_1) (fun (x : Type u_1) => Type u_2) m n) A

noncomputable def Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration_1.observationFact0.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"HomologicalAlgebra\",\"IntegerMatrixInnerInverse\",\"exists_integer_inner_inverse\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"HomologicalAlgebra\",\"IntegerMatrixInnerInverse\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse, declaration := `D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.exists_integer_inner_inverse, part := .type, path := [.body, .body, .body, .body, .body, .body, .argument, .body, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse, declaration := `Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration_1.varyingLawInput.{u_1, u_2} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration_1.canonicalArenaOperand.{u_1, u_2})
noncomputable def Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration_1.varyingLaw.{u_1, u_2}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"HomologicalAlgebra\",\"IntegerMatrixInnerInverse\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"

noncomputable def Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration_1.statementExclusion.{u_1, u_2} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"HomologicalAlgebra\",\"IntegerMatrixInnerInverse\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"HomologicalAlgebra\",\"IntegerMatrixInnerInverse\",\"exists_integer_inner_inverse\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse, declaration := `Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2)] }
  statementLocation := { owner := `D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse, declaration := `D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.exists_integer_inner_inverse, part := .type, path := [], levels := [(.param `u_1), (.param `u_2)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration.{u_1, u_2}).actual (Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration.{u_1, u_2}).variation.2.choose (Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration.{u_1, u_2}).variation.1 (Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration.{u_1, u_2}).variation.2.choose_spec

noncomputable def Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration_1.descriptorFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"HomologicalAlgebra\",\"IntegerMatrixInnerInverse\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"HomologicalAlgebra\",\"IntegerMatrixInnerInverse\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]]]}"))
  { owner := `Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse, declaration := `Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2)] }
  { owner := `Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse, declaration := `Reg.D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2)] }
  (by first | rfl | (ext <;> rfl))
