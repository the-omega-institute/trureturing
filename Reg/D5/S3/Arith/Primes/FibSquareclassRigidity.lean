import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Primes.FibSquareclassRigidity
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.FibSquareclassRigidity

open _root_.D5.S3.Arith.Primes.FibSquareclassRigidity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℕ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ m n => Nat.fib m * Nat.fib n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (m n : ℕ) (_hm : 0 < m) (_hn : 0 < n),
    IsSquare (r.readout () m n) ↔
      m = n ∨
      ((m = 1 ∨ m = 2 ∨ m = 12) ∧ (n = 1 ∨ n = 2 ∨ n = 12)) ∨
      ((m = 3 ∨ m = 6) ∧ (n = 3 ∨ n = 6))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs : IsSquare (rejected.readout () 1 4) := ⟨0, rfl⟩
  have hb := (h 1 4 (by decide) (by decide)).mp hs
  norm_num at hb

def registration : Registration arena
    (∀ (m n : ℕ) (_hm : 0 < m) (_hn : 0 < n),
      IsSquare (Nat.fib m * Nat.fib n) ↔
        m = n ∨
        ((m = 1 ∨ m = 2 ∨ m = 12) ∧ (n = 1 ∨ n = 2 ∨ n = 12)) ∨
        ((m = 3 ∨ m = 6) ∧ (n = 3 ∨ n = 6))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fibonacci_squareclass_pairs, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨1, (1 : ℕ), (3 : ℕ), ?_⟩
    change Nat.fib 1 * Nat.fib 1 ≠ Nat.fib 1 * Nat.fib 3
    decide

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Primes.FibSquareclassRigidity.fibonacci_squareclass_pairs) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ m n => Nat.fib m * Nat.fib n)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Primes") "FibSquareclassRigidity") "fibonacci_squareclass_pairs") "Reg.D5.S3.Arith.Primes.FibSquareclassRigidity/Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ m n => Nat.fib m * Nat.fib n)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Primes.FibSquareclassRigidity, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.Primes.FibSquareclassRigidity, declaration := `D5.S3.Arith.Primes.FibSquareclassRigidity.fibonacci_squareclass_pairs, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibSquareclassRigidity, declaration := `Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibSquareclassRigidity, declaration := `Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibSquareclassRigidity, declaration := `Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibSquareclassRigidity, declaration := `Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration_1.observationFact0, `Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration_1.anchorEnumeration }


end Reg.D5.S3.Arith.Primes.FibSquareclassRigidity


noncomputable def Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.arena
noncomputable def Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibSquareclassRigidity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibSquareclassRigidity\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.FibSquareclassRigidity, declaration := `Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibSquareclassRigidity, declaration := `Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.arena
noncomputable def Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibSquareclassRigidity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibSquareclassRigidity\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.FibSquareclassRigidity, declaration := `Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibSquareclassRigidity, declaration := `Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.arena
    (∀ (m n : Nat) (_hm : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m)
      (_hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n),
      Iff
        (@IsSquare.{0} Nat instMulNat
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (Nat.fib m) (Nat.fib n)))
        (Or (@Eq.{1} Nat m n)
          (Or
            (And
              (Or (@Eq.{1} Nat m (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (Or (@Eq.{1} Nat m (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@Eq.{1} Nat m (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))))
              (Or (@Eq.{1} Nat n (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (Or (@Eq.{1} Nat n (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@Eq.{1} Nat n (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))))))
            (And
              (Or (@Eq.{1} Nat m (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (@Eq.{1} Nat m (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
              (Or (@Eq.{1} Nat n (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (@Eq.{1} Nat n (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))))
    Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration)

noncomputable def Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibSquareclassRigidity\",\"fibonacci_squareclass_pairs\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibSquareclassRigidity\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.FibSquareclassRigidity, declaration := `D5.S3.Arith.Primes.FibSquareclassRigidity.fibonacci_squareclass_pairs, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibSquareclassRigidity, declaration := `Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.arena
  (∀ (m n : Nat) (_hm : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m)
    (_hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n),
    Iff
      (@IsSquare.{0} Nat instMulNat
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (Nat.fib m) (Nat.fib n)))
      (Or (@Eq.{1} Nat m n)
        (Or
          (And
            (Or (@Eq.{1} Nat m (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (Or (@Eq.{1} Nat m (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@Eq.{1} Nat m (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))))
            (Or (@Eq.{1} Nat n (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (Or (@Eq.{1} Nat n (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@Eq.{1} Nat n (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))))))
          (And
            (Or (@Eq.{1} Nat m (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (@Eq.{1} Nat m (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
            (Or (@Eq.{1} Nat n (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (@Eq.{1} Nat n (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))))
  Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration)

noncomputable def Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration_1.observation0 : (m n : Nat) →
  (hm : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m) →
    (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
        Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.signature PUnit.unit.{1} m :=
  fun (m n : Nat) (hm : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m)
    (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.signature Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.actual
    PUnit.unit.{1} m n

noncomputable def Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibSquareclassRigidity\",\"fibonacci_squareclass_pairs\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibSquareclassRigidity\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.FibSquareclassRigidity, declaration := `D5.S3.Arith.Primes.FibSquareclassRigidity.fibonacci_squareclass_pairs, part := .type, path := [.body, .body, .body, .body, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibSquareclassRigidity, declaration := `Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibSquareclassRigidity\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibSquareclassRigidity\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibSquareclassRigidity\",\"fibonacci_squareclass_pairs\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.Primes.FibSquareclassRigidity, declaration := `Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.Primes.FibSquareclassRigidity, declaration := `D5.S3.Arith.Primes.FibSquareclassRigidity.fibonacci_squareclass_pairs, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration).actual (Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration).variation.2.choose (Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration).variation.1 (Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibSquareclassRigidity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibSquareclassRigidity\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.FibSquareclassRigidity, declaration := `Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibSquareclassRigidity, declaration := `Reg.D5.S3.Arith.Primes.FibSquareclassRigidity.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
