import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Transport.FibonacciPrefix
import Reg.Support.DependentFamily

open _root_.D5.S3.Quantum.Transport.FibonacciPrefix
open _root_.D5.S0.Carrier
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Matrix Kronecker
noncomputable section
namespace Reg.D5.S3.Quantum.Transport.FibonacciPrefix

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := (ZMod d × ZMod d) ≃ (ZMod d × ZMod d)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ d t => lowTrajectory d t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => Equiv.refl _) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (d e : ℕ) [NeZero d] [NeZero e] (_ : 2 ≤ d) (_ : 2 ≤ e),
    (∀ N (a b : ZMod d × ZMod d), carryPrefix d N a = carryPrefix d N b →
      ∀ j ≤ N, integerTrajectory d j a - integerTrajectory d j b =
        phi ^ j * (integerTrajectory d 0 a - integerTrajectory d 0 b)) ∧
    (∀ N (a b : ZMod d × ZMod d), 1 ≤ N → a ≠ b →
      carryPrefix d N a = carryPrefix d N b →
      Real.goldenRatio ^ N ≤ Real.goldenRatio ^ 3 * ((d : ℝ) - 1) ^ 2) ∧
    (∀ P, 1 ≤ P → (∀ a, r.readout () d P a = a) →
      Function.Injective (carryPrefix d P)) ∧
    (∀ N : ℕ, 3 + 2 * Real.logb Real.goldenRatio ((d : ℝ) - 1) < (N : ℝ) →
      Function.Injective (carryPrefix d N)) ∧
    (∀ a b : ZMod d × ZMod d,
      (∀ j, carryHistory d a j = carryHistory d b j) → a = b) ∧
    (prefixThreshold d : ℤ) = ⌊3 + 2 * Real.logb Real.goldenRatio ((d : ℝ) - 1)⌋ + 1 ∧
    (∀ N, prefixThreshold d ≤ N → Function.Injective (carryPrefix d N)) ∧
    prefixThreshold 2 = 4 ∧
    (∀ t (B : Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ),
      movingPullback d e t B =
        (D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.jointUnitary d e ^ t)ᴴ *
          (((D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.lowUnitary d) ^ t * B *
            ((D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.lowUnitary d) ^ t)ᴴ) ⊗ₖ
              (1 : Matrix (ZMod e × ZMod e) (ZMod e × ZMod e) ℂ)) *
          D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.jointUnitary d e ^ t) ∧
    (∀ N (B : Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ),
      B ∈ prefixAlgebra d e N ↔
        ∀ a b, carryPrefix d N a ≠ carryPrefix d N b → B a b = 0) ∧
    (∀ N (B : Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ),
      B ∈ prefixAlgebra d e N → ∀ t, 1 ≤ t → t ≤ N →
        movingPullback d e t B = D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.lowTensor d e B) ∧
    Antitone (prefixAlgebra d e) ∧
    (⨅ N : ℕ, ⨅ (_ : 1 ≤ N), prefixAlgebra d e N) = diagonalAlgebra d ∧
    (∀ P, 1 ≤ P → (∀ a, lowTrajectory d P a = a) →
      prefixAlgebra d e P = diagonalAlgebra d) ∧
    (∀ N, prefixThreshold d ≤ N → prefixAlgebra d e N = diagonalAlgebra d)

theorem actual_law : arena.Law actual := by
  intro d e _ _ hd he
  exact fibonacci_prefix_transport d e hd he

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hi := (h 2 2 (by norm_num) (by norm_num)).2.2.1
    1 (by norm_num) (by intro a; rfl)
  have heq : carryPrefix 2 1 ((0,0) : ZMod 2 × ZMod 2) =
      carryPrefix 2 1 ((1,0) : ZMod 2 × ZMod 2) := by
    funext j
    have hj : j = 0 := Fin.eq_zero j
    subst j
    norm_num [carryPrefix, carryHistory, lowTrajectory,
      D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.carry,
      D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.fibonacci,
      ZMod.val_one_eq_one_mod]
  have hx := congrArg Prod.fst (hi heq)
  exact zero_ne_one hx

def registration : Registration arena (arena.Law actual) where
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
    refine ⟨(2 : ℕ), (0 : ℕ), (1 : ℕ), ?_⟩
    intro h
    change lowTrajectory 2 0 = lowTrajectory 2 1 at h
    have hx := congrArg (fun q : (ZMod 2 × ZMod 2) ≃ (ZMod 2 × ZMod 2) =>
      (q ((1,0) : ZMod 2 × ZMod 2)).1) h
    norm_num [lowTrajectory,
      D5.S3.Quantum.Algebra.CarryTransport.FibonacciOutputAlgebra.fibonacci] at hx

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Transport.FibonacciPrefix.fibonacci_prefix_transport) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ d t => lowTrajectory d t) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Transport") "FibonacciPrefix") "fibonacci_prefix_transport") "Reg.D5.S3.Quantum.Transport.FibonacciPrefix/Reg.D5.S3.Quantum.Transport.FibonacciPrefix.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ d t => lowTrajectory d t) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Transport.FibonacciPrefix, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "body", "body", "domain", "body", "fn", "arg", "fn"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Transport.FibonacciPrefix, declaration := `D5.S3.Quantum.Transport.FibonacciPrefix.fibonacci_prefix_transport, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Transport.FibonacciPrefix, declaration := `Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Transport.FibonacciPrefix, declaration := `Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Transport.FibonacciPrefix, declaration := `Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Transport.FibonacciPrefix, declaration := `Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration_1.anchorEnumeration }


#print axioms registration
end Reg.D5.S3.Quantum.Transport.FibonacciPrefix


noncomputable def Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Transport.FibonacciPrefix.arena
noncomputable def Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Transport\",\"FibonacciPrefix\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Transport\",\"FibonacciPrefix\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Transport.FibonacciPrefix, declaration := `Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Transport.FibonacciPrefix, declaration := `Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Transport.FibonacciPrefix.arena
noncomputable def Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Transport\",\"FibonacciPrefix\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Transport\",\"FibonacciPrefix\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Transport.FibonacciPrefix, declaration := `Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Transport.FibonacciPrefix, declaration := `Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Quantum.Transport.FibonacciPrefix.arena) (Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration).actual

noncomputable def Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Transport\",\"FibonacciPrefix\",\"fibonacci_prefix_transport\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Transport\",\"FibonacciPrefix\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Transport.FibonacciPrefix, declaration := `D5.S3.Quantum.Transport.FibonacciPrefix.fibonacci_prefix_transport, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Transport.FibonacciPrefix, declaration := `Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration).bridge

noncomputable def Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Transport\",\"FibonacciPrefix\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Transport\",\"FibonacciPrefix\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Transport\",\"FibonacciPrefix\",\"fibonacci_prefix_transport\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Transport.FibonacciPrefix, declaration := `Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Quantum.Transport.FibonacciPrefix, declaration := `D5.S3.Quantum.Transport.FibonacciPrefix.fibonacci_prefix_transport, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration).actual (Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration).variation.2.choose (Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration).variation.1 (Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Transport\",\"FibonacciPrefix\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Transport\",\"FibonacciPrefix\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Transport.FibonacciPrefix, declaration := `Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Transport.FibonacciPrefix, declaration := `Reg.D5.S3.Quantum.Transport.FibonacciPrefix.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
