import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Primes.FibonacciFiveAdicDepth
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth

open _root_.D5.S3.Arith.Primes.FibonacciFiveAdicDepth
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => padicValNat 5 (Nat.fib n)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (n : ℕ) (_hn : 0 < n),
    r.readout () () n = padicValNat 5 n

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 1 (by decide)
  change 1 = padicValNat 5 1 at hbad
  norm_num at hbad

def registration : Registration arena
    (∀ (n : ℕ) (_hn : 0 < n),
      padicValNat 5 (Nat.fib n) = padicValNat 5 n) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fibonacci_five_adic_depth, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨(), (1 : ℕ), (5 : ℕ), ?_⟩
    change padicValNat 5 (Nat.fib 1) ≠ padicValNat 5 (Nat.fib 5)
    norm_num [padicValNat]

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.fibonacci_five_adic_depth) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => padicValNat 5 (Nat.fib n))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Primes") "FibonacciFiveAdicDepth") "fibonacci_five_adic_depth") "Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth/Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => padicValNat 5 (Nat.fib n))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Primes.FibonacciFiveAdicDepth, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.Primes.FibonacciFiveAdicDepth, declaration := `D5.S3.Arith.Primes.FibonacciFiveAdicDepth.fibonacci_five_adic_depth, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth, declaration := `Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth, declaration := `Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth, declaration := `Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth, declaration := `Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration_1.observationFact0, `Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration_1.anchorEnumeration }


end Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth


noncomputable def Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.arena
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciFiveAdicDepth\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciFiveAdicDepth\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth, declaration := `Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth, declaration := `Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.arena
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciFiveAdicDepth\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciFiveAdicDepth\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth, declaration := `Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth, declaration := `Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.arena
    (∀ (n : Nat) (_hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n),
      @Eq.{1} Nat (padicValNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) (Nat.fib n))
        (padicValNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) n))
    Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration)

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciFiveAdicDepth\",\"fibonacci_five_adic_depth\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciFiveAdicDepth\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.FibonacciFiveAdicDepth, declaration := `D5.S3.Arith.Primes.FibonacciFiveAdicDepth.fibonacci_five_adic_depth, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth, declaration := `Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.arena
  (∀ (n : Nat) (_hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n),
    @Eq.{1} Nat (padicValNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) (Nat.fib n))
      (padicValNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) n))
  Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration)

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration_1.observation0 : (n : Nat) →
  (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
      Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (n : Nat) (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.signature Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.actual
    PUnit.unit.{1} PUnit.unit.{1} n

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciFiveAdicDepth\",\"fibonacci_five_adic_depth\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciFiveAdicDepth\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.FibonacciFiveAdicDepth, declaration := `D5.S3.Arith.Primes.FibonacciFiveAdicDepth.fibonacci_five_adic_depth, part := .type, path := [.body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth, declaration := `Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciFiveAdicDepth\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciFiveAdicDepth\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciFiveAdicDepth\",\"fibonacci_five_adic_depth\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth, declaration := `Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.Primes.FibonacciFiveAdicDepth, declaration := `D5.S3.Arith.Primes.FibonacciFiveAdicDepth.fibonacci_five_adic_depth, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration).actual (Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration).variation.2.choose (Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration).variation.1 (Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciFiveAdicDepth\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciFiveAdicDepth\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth, declaration := `Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth, declaration := `Reg.D5.S3.Arith.Primes.FibonacciFiveAdicDepth.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
