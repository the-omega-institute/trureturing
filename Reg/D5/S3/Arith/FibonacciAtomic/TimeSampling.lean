import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.TimeSampling
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.FibonacciAtomic.TimeSampling
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling

@[reducible] def signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => recoveryLimit n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ), 2 ≤ n →
    PairwiseRecovery n (Finset.range (recoveryLimit n)) ∧
      ∀ T : Finset ℕ, PairwiseRecovery n T → T.card ≤ R.readout () () n

theorem actual_law : arena.Law actual := pairwise_recovery_maximum

theorem singleton_recovery (n : ℕ) : PairwiseRecovery n {0} := by
  intro s hs t ht hst
  simp only [Finset.mem_singleton] at hs ht
  omega

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := (h 2 le_rfl).2 {0} (singleton_recovery 2)
  change ({0} : Finset ℕ).card ≤ 0 at bad
  simp at bad

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    change recoveryLimit 1 ≠ recoveryLimit 2
    have hset : {p : ℕ | p.Prime ∧ p ∣ 1} = ∅ := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hp, hdiv⟩
      have heq := Nat.dvd_one.mp hdiv
      exact hp.ne_one heq
    have h1 : recoveryLimit 1 = 0 := by
      unfold recoveryLimit
      rw [hset]
      simp
    have h2 := (pairwise_recovery_maximum 2 le_rfl).2 {0} (singleton_recovery 2)
    simp only [Finset.card_singleton] at h2
    omega

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.FibonacciAtomic.TimeSampling.pairwise_recovery_maximum) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => recoveryLimit n) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "FibonacciAtomic") "TimeSampling") "pairwise_recovery_maximum") "Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling/Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => recoveryLimit n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.FibonacciAtomic.TimeSampling, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "arg", "body", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.FibonacciAtomic.TimeSampling, declaration := `D5.S3.Arith.FibonacciAtomic.TimeSampling.pairwise_recovery_maximum, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration_1.observationFact0, `Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.arena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"TimeSampling\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"TimeSampling\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.arena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"TimeSampling\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"TimeSampling\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.arena Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.actual)
    Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration)

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"TimeSampling\",\"pairwise_recovery_maximum\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"TimeSampling\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.TimeSampling, declaration := `D5.S3.Arith.FibonacciAtomic.TimeSampling.pairwise_recovery_maximum, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.arena Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.actual)
  Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration)

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration_1.observation0 : (n : Nat) →
  (hn : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n) →
    (T : Finset.{0} Nat) →
      D5.S3.Arith.FibonacciAtomic.TimeSampling.PairwiseRecovery n T →
        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
          Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (n : Nat) (hn : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
    (T : Finset.{0} Nat) (a : D5.S3.Arith.FibonacciAtomic.TimeSampling.PairwiseRecovery n T) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.signature Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.actual
    PUnit.unit.{1} PUnit.unit.{1} n

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"TimeSampling\",\"pairwise_recovery_maximum\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"argument\",\"body\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"TimeSampling\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.TimeSampling, declaration := `D5.S3.Arith.FibonacciAtomic.TimeSampling.pairwise_recovery_maximum, part := .type, path := [.body, .body, .argument, .body, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"TimeSampling\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"TimeSampling\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"TimeSampling\",\"pairwise_recovery_maximum\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.FibonacciAtomic.TimeSampling, declaration := `D5.S3.Arith.FibonacciAtomic.TimeSampling.pairwise_recovery_maximum, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration).actual (Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration).variation.2.choose (Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration).variation.1 (Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"TimeSampling\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"TimeSampling\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.TimeSampling.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
