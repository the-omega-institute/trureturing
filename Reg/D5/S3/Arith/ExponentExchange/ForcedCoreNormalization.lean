import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.ExponentExchange.ForcedCoreNormalization
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman
open _root_.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization

abbrev signature : Signature where
  Params := Unit
  State _ := List ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ ell => suffixNumber 1 0 ell) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (ell : List ℕ) (_hell : Ordered (ell.headD 0) ell) (B : ℕ),
    let M := R.readout () () ell
    (B < M ↔ ¬∃ n : ℕ, 1 ≤ n ∧ n ≤ B ∧ M ∣ n) ∧
    (M ≤ B → ∃ (n : ℕ) (t : List ℕ),
      1 ≤ n ∧ n ≤ B ∧ M ∣ n ∧
      (∀ p q : ℕ, p.Prime → q.Prime → p < q →
        n.factorization q ≤ n.factorization p) ∧
      Ordered (rootCap 1 B) t ∧ suffixNumber 1 0 t = n ∧
      (ArithmeticFunction.sigma 1 n : ℝ) / n = suffixWeight 1 0 t ∧
      (∀ m : ℕ, 1 ≤ m → m ≤ B → M ∣ m →
        (ArithmeticFunction.sigma 1 m : ℝ) / m ≤
          (ArithmeticFunction.sigma 1 n : ℝ) / n))

theorem actual_law : arena.Law actual := by
  exact forced_core_normalization

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h [] (by trivial) 0).1
  norm_num [rejected, realize] at hbad

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), [], [1], ?_⟩
    simpa only [actual, realize, suffixNumber, pow_one, mul_one,
      prime, Nat.add_zero] using
      (Nat.prime_nth_prime (Nat.primeCounting 1)).ne_one.symm

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.forced_core_normalization) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ ell => suffixNumber 1 0 ell)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "ExponentExchange") "ForcedCoreNormalization") "forced_core_normalization") "Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization/Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ ell => suffixNumber 1 0 ell)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.ExponentExchange.ForcedCoreNormalization, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "value"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.ExponentExchange.ForcedCoreNormalization, declaration := `D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.forced_core_normalization, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization, declaration := `Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization, declaration := `Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization, declaration := `Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization, declaration := `Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration_1.observationFact0, `Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization


noncomputable def Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.arena
noncomputable def Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"ForcedCoreNormalization\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"ForcedCoreNormalization\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization, declaration := `Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization, declaration := `Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.arena
noncomputable def Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"ForcedCoreNormalization\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"ForcedCoreNormalization\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization, declaration := `Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization, declaration := `Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.arena
      Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.actual)
    Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration)

noncomputable def Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"ForcedCoreNormalization\",\"forced_core_normalization\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"ForcedCoreNormalization\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.ExponentExchange.ForcedCoreNormalization, declaration := `D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.forced_core_normalization, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization, declaration := `Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.arena
    Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.actual)
  Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration)

noncomputable def Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration_1.observation0 : (ell : List.{0} Nat) →
  (hell :
      D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.Ordered
        (@List.headD.{0} Nat ell (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) ell) →
    (B : Nat) →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
        Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (ell : List.{0} Nat)
    (hell :
      D5.S3.Arith.ExponentExchange.RoughPrimeSuffixBellman.Ordered
        (@List.headD.{0} Nat ell (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) ell)
    (B : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.signature
    Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.actual PUnit.unit.{1} PUnit.unit.{1} ell

noncomputable def Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"ForcedCoreNormalization\",\"forced_core_normalization\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"letValue\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"ForcedCoreNormalization\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.ExponentExchange.ForcedCoreNormalization, declaration := `D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.forced_core_normalization, part := .type, path := [.body, .body, .body, .letValue], levels := [] }
  { owner := `Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization, declaration := `Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"ForcedCoreNormalization\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"ForcedCoreNormalization\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"ForcedCoreNormalization\",\"forced_core_normalization\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization, declaration := `Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.ExponentExchange.ForcedCoreNormalization, declaration := `D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.forced_core_normalization, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration).actual (Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration).variation.2.choose (Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration).variation.1 (Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"ForcedCoreNormalization\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"ExponentExchange\",\"ForcedCoreNormalization\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization, declaration := `Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization, declaration := `Reg.D5.S3.Arith.ExponentExchange.ForcedCoreNormalization.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
