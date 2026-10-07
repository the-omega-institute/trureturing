import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Reduction.IsometricCompression
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Reduction.IsometricCompression
open LeanInformationAudit
open scoped Matrix BigOperators

noncomputable section
namespace Reg.D5.S3.Quantum.Reduction.IsometricCompression
universe u v w

abbrev signature : Signature where
  Params := Σ _ : Type u, Type v
  State p := Matrix p.1 p.2 ℂ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ p := Matrix p.1 p.2 ℂ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro x; cases x⟩

def actual : Realization signature.{u,v} :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u,v}
  Law r := ∀ {n : Type u} {d : Type v}
    [Fintype n] [DecidableEq n] [Fintype d] [DecidableEq d]
    {ι : Type w} (U : Matrix n d ℂ)
    (K : ι → Matrix n n ℂ) (k : ι → Matrix d d ℂ)
    (h : ∀ a, K a * U = U * k a) (w : List ι),
    (w.map K).prod * U = r.readout () ⟨n,d⟩ U * (w.map k).prod

theorem actual_law : arena.{u,v,w}.Law actual := by
  intro n d _ _ _ _ ι U K k h w
  exact word_intertwines U K k h w

theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let U : Matrix (ULift.{u} (Fin 1)) (ULift.{v} (Fin 1)) ℂ := fun _ _ => 1
  have heq := h U (fun _ : ULift.{w} (Fin 1) => 0) (fun _ => 0)
    (by intro a; simp) []
  have hz : U = 0 := by simpa [rejected, realize] using heq
  have hentry := congrFun (congrFun hz (ULift.up 0)) (ULift.up 0)
  exact one_ne_zero (show (1 : ℂ) = 0 from hentry)

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
    refine ⟨⟨ULift.{u} (Fin 1), ULift.{v} (Fin 1)⟩, (fun _ _ => (0 : ℂ)), (fun _ _ => (1 : ℂ)), ?_⟩
    intro h
    exact zero_ne_one (congrFun (congrFun h (ULift.up 0)) (ULift.up 0))

noncomputable def registration_1.{u_1, u_2, u_5} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Reduction.IsometricCompression.word_intertwines.{u_1, u_2, u_5}) (type_of% (realize.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, max u_1 u_2, 0} signature.{u_1, u_2} (fun _ _ x => x) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Reduction") "IsometricCompression") "word_intertwines") "Reg.D5.S3.Quantum.Reduction.IsometricCompression/Reg.D5.S3.Quantum.Reduction.IsometricCompression.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2, u_5})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2, u_5})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2, u_5}) ⟨(registration.{u_1, u_2, u_5})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, max u_1 u_2, 0} signature.{u_1, u_2} (fun _ _ x => x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Reduction.IsometricCompression, definition := none, coordinates := #[0, 1], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"], stateBinder := 7, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Reduction.IsometricCompression, declaration := `D5.S3.Quantum.Reduction.IsometricCompression.word_intertwines, part := .type, path := [], levels := [.param `u_1, .param `u_2, .param `u_5] },
    { owner := `Reg.D5.S3.Quantum.Reduction.IsometricCompression, declaration := `Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_5] },
    { owner := `Reg.D5.S3.Quantum.Reduction.IsometricCompression, declaration := `Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_5] },
    { owner := `Reg.D5.S3.Quantum.Reduction.IsometricCompression, declaration := `Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_5] },
    { owner := `Reg.D5.S3.Quantum.Reduction.IsometricCompression, declaration := `Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2, .param `u_5] }], facts := [`Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration_1.observationFact0, `Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration_1.anchorEnumeration }


#print axioms registration
end Reg.D5.S3.Quantum.Reduction.IsometricCompression


noncomputable def Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration_1.canonicalArenaOperand.{u_1, u_2, u_5} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, max u_1 u_2, 0} :=
  Reg.D5.S3.Quantum.Reduction.IsometricCompression.arena.{u_1, u_2, u_5}
noncomputable def Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration_1.canonicalArenaFact.{u_1, u_2, u_5} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Reduction\",\"IsometricCompression\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_5\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Reduction\",\"IsometricCompression\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_5\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Reduction.IsometricCompression, declaration := `Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_5)] }
  { owner := `Reg.D5.S3.Quantum.Reduction.IsometricCompression, declaration := `Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_5)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration_1.canonicalObjectArenaOperand.{u_1, u_2, u_5} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, max u_1 u_2, 0} :=
  Reg.D5.S3.Quantum.Reduction.IsometricCompression.arena.{u_1, u_2, u_5}
noncomputable def Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration_1.canonicalObjectArenaFact.{u_1, u_2, u_5} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Reduction\",\"IsometricCompression\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_5\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Reduction\",\"IsometricCompression\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_5\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Reduction.IsometricCompression, declaration := `Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_5)] }
  { owner := `Reg.D5.S3.Quantum.Reduction.IsometricCompression, declaration := `Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_5)] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration_1.sourceLaw.{u_1, u_2, u_5} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0, max u_1 u_2,
    0} (Reg.D5.S3.Quantum.Reduction.IsometricCompression.arena.) (Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration.{u_1, u_2, u_5}).actual

noncomputable def Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration_1.sourceBridgeFact.{u_1, u_2, u_5} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Reduction\",\"IsometricCompression\",\"word_intertwines\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_5\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Reduction\",\"IsometricCompression\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_5\"]]]}"))
  { owner := `D5.S3.Quantum.Reduction.IsometricCompression, declaration := `D5.S3.Quantum.Reduction.IsometricCompression.word_intertwines, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_5)] }
  { owner := `Reg.D5.S3.Quantum.Reduction.IsometricCompression, declaration := `Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_5)] }
  (Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration.{u_1, u_2, u_5}).bridge

noncomputable def Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration_1.observation0.{u_1, u_2, u_5} : {n : Type u_1} →
  {d : Type u_2} →
    [inst : Fintype.{u_1} n] →
      [DecidableEq.{u_1 + 1} n] →
        [inst_2 : Fintype.{u_2} d] →
          [DecidableEq.{u_2 + 1} d] →
            {ι : Type u_5} →
              (U : Matrix.{u_1, u_2, 0} n d Complex) →
                (K : ι → Matrix.{u_1, u_1, 0} n n Complex) →
                  (k : ι → Matrix.{u_2, u_2, 0} d d Complex) →
                    (h :
                        ∀ (a : ι),
                          @Eq.{max (u_1 + 1) (u_2 + 1)} (Matrix.{u_1, u_2, 0} n d Complex)
                            (@HMul.hMul.{u_1, max u_1 u_2, max u_1 u_2} (Matrix.{u_1, u_1, 0} n n Complex)
                              (Matrix.{u_1, u_2, 0} n d Complex) (Matrix.{u_1, u_2, 0} n d Complex)
                              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_1, u_1, u_2} n n d Complex inst
                                Complex.instMul Complex.instAddCommMonoid)
                              (K a) U)
                            (@HMul.hMul.{max u_1 u_2, u_2, max u_1 u_2} (Matrix.{u_1, u_2, 0} n d Complex)
                              (Matrix.{u_2, u_2, 0} d d Complex) (Matrix.{u_1, u_2, 0} n d Complex)
                              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_1, u_2, u_2} n d d Complex inst_2
                                Complex.instMul Complex.instAddCommMonoid)
                              U (k a))) →
                      (w : List.{u_5} ι) →
                        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{max (u_1 + 1)
                              (u_2 + 1),
                            max u_1 u_2, 0, max u_1 u_2, 0}
                          Reg.D5.S3.Quantum.Reduction.IsometricCompression.signature.{u_1, u_2} Unit.unit
                          (@Sigma.mk.{u_1 + 1, u_2 + 1} (Type u_1) (fun (x : Type u_1) => Type u_2) n d) :=
  fun {n : Type u_1} {d : Type u_2} [Fintype.{u_1} n] [DecidableEq.{u_1 + 1} n] [Fintype.{u_2} d]
    [DecidableEq.{u_2 + 1} d] {ι : Type u_5} (U : Matrix.{u_1, u_2, 0} n d Complex)
    (K : ι → Matrix.{u_1, u_1, 0} n n Complex) (k : ι → Matrix.{u_2, u_2, 0} d d Complex)
    (h :
      ∀ (a : ι),
        @Eq.{max (u_1 + 1) (u_2 + 1)} (Matrix.{u_1, u_2, 0} n d Complex)
          (@HMul.hMul.{u_1, max u_1 u_2, max u_1 u_2} (Matrix.{u_1, u_1, 0} n n Complex)
            (Matrix.{u_1, u_2, 0} n d Complex) (Matrix.{u_1, u_2, 0} n d Complex)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_1, u_1, u_2} n n d Complex inst Complex.instMul
              Complex.instAddCommMonoid)
            (K a) U)
          (@HMul.hMul.{max u_1 u_2, u_2, max u_1 u_2} (Matrix.{u_1, u_2, 0} n d Complex)
            (Matrix.{u_2, u_2, 0} d d Complex) (Matrix.{u_1, u_2, 0} n d Complex)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.{0, u_1, u_2, u_2} n d d Complex inst_2 Complex.instMul
              Complex.instAddCommMonoid)
            U (k a)))
    (w : List.{u_5} ι) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{max (u_1 + 1) (u_2 + 1), max u_1 u_2, 0,
        max u_1 u_2, 0}
    Reg.D5.S3.Quantum.Reduction.IsometricCompression.signature.{u_1, u_2}
    Reg.D5.S3.Quantum.Reduction.IsometricCompression.actual.{u_1, u_2} Unit.unit
    (@Sigma.mk.{u_1 + 1, u_2 + 1} (Type u_1) (fun (x : Type u_1) => Type u_2) n d) U

noncomputable def Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration_1.observationFact0.{u_1, u_2, u_5} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Reduction\",\"IsometricCompression\",\"word_intertwines\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_5\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Reduction\",\"IsometricCompression\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_5\"]]]}"))
  { owner := `D5.S3.Quantum.Reduction.IsometricCompression, declaration := `D5.S3.Quantum.Reduction.IsometricCompression.word_intertwines, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .function, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_5)] }
  { owner := `Reg.D5.S3.Quantum.Reduction.IsometricCompression, declaration := `Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_5)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration_1.varyingLawInput.{u_1, u_2, u_5} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration_1.canonicalArenaOperand.{u_1, u_2, u_5})
noncomputable def Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration_1.varyingLaw.{u_1, u_2, u_5}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Reduction\",\"IsometricCompression\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_5\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration_1.statementExclusion.{u_1, u_2, u_5} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Reduction\",\"IsometricCompression\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_5\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Reduction\",\"IsometricCompression\",\"word_intertwines\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_5\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Reduction.IsometricCompression, declaration := `Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_5)] }
  statementLocation := { owner := `D5.S3.Quantum.Reduction.IsometricCompression, declaration := `D5.S3.Quantum.Reduction.IsometricCompression.word_intertwines, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_5)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration.{u_1, u_2, u_5}).actual (Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration.{u_1, u_2, u_5}).variation.2.choose (Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration.{u_1, u_2, u_5}).variation.1 (Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration.{u_1, u_2, u_5}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration_1.descriptorFact.{u_1, u_2} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Reduction\",\"IsometricCompression\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_5\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Reduction\",\"IsometricCompression\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_5\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Reduction.IsometricCompression, declaration := `Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_5)] }
  { owner := `Reg.D5.S3.Quantum.Reduction.IsometricCompression, declaration := `Reg.D5.S3.Quantum.Reduction.IsometricCompression.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_5)] }
  (by first | rfl | (ext <;> rfl))
