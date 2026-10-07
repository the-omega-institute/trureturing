import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Primes.FiniteFibonacciRankClosure
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure

open _root_.D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State := fun _ => Finset ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Finset ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ S => fibonacciRankClosure S) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (S : Finset ℕ) (_hS : ∀ p ∈ S, p.Prime ∧ 5 < p),
    let H := r.readout () () S
    rankClosureSeed S ⊆ H ∧
    (∀ p ∈ H, p.Prime) ∧
    (∀ p ∈ H, p ≤ max 5 (S.sup id)) ∧
    rankClosureStep H = H ∧
    (∀ K : Finset ℕ, rankClosureSeed S ⊆ K → rankClosureStep K ⊆ K → H ⊆ K)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h ∅ (by simp)).1
  have htwo : 2 ∈ rankClosureSeed (∅ : Finset ℕ) := by
    simp [rankClosureSeed]
  have hfalse : 2 ∈ (∅ : Finset ℕ) := by
    exact hbad htwo
  simp at hfalse

def registration : Registration arena
    (∀ (S : Finset ℕ) (_hS : ∀ p ∈ S, p.Prime ∧ 5 < p),
      let H := fibonacciRankClosure S
      rankClosureSeed S ⊆ H ∧
      (∀ p ∈ H, p.Prime) ∧
      (∀ p ∈ H, p ≤ max 5 (S.sup id)) ∧
      rankClosureStep H = H ∧
      (∀ K : Finset ℕ, rankClosureSeed S ⊆ K → rankClosureStep K ⊆ K → H ⊆ K)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finite_fibonacci_rank_closure, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    have hS7 : ∀ p ∈ ({7} : Finset ℕ), p.Prime ∧ 5 < p := by
      intro p hp
      simp only [Finset.mem_singleton] at hp
      subst p
      decide
    have h7 : 7 ∈ fibonacciRankClosure ({7} : Finset ℕ) :=
      (finite_fibonacci_rank_closure {7} hS7).1 (by simp [rankClosureSeed])
    have hEmpty : ∀ p ∈ fibonacciRankClosure (∅ : Finset ℕ), p ≤ 5 := by
      intro p hp
      have h := (finite_fibonacci_rank_closure ∅ (by simp)).2.2.1 p hp
      simpa using h
    refine ⟨(), (∅ : Finset ℕ), ({7} : Finset ℕ), ?_⟩
    change fibonacciRankClosure ∅ ≠ fibonacciRankClosure {7}
    intro heq
    rw [← heq] at h7
    have hbad := hEmpty 7 h7
    omega

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.finite_fibonacci_rank_closure) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ S => fibonacciRankClosure S) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Primes") "FiniteFibonacciRankClosure") "finite_fibonacci_rank_closure") "Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure/Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ S => fibonacciRankClosure S) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Primes.FiniteFibonacciRankClosure, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "value"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.Primes.FiniteFibonacciRankClosure, declaration := `D5.S3.Arith.Primes.FiniteFibonacciRankClosure.finite_fibonacci_rank_closure, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure, declaration := `Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure, declaration := `Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure, declaration := `Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure, declaration := `Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration_1.observationFact0, `Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration_1.anchorEnumeration }


end Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure


noncomputable def Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.arena
noncomputable def Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FiniteFibonacciRankClosure\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FiniteFibonacciRankClosure\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure, declaration := `Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure, declaration := `Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.arena
noncomputable def Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FiniteFibonacciRankClosure\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FiniteFibonacciRankClosure\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure, declaration := `Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure, declaration := `Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.arena) (Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration).actual

noncomputable def Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"FiniteFibonacciRankClosure\",\"finite_fibonacci_rank_closure\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FiniteFibonacciRankClosure\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.FiniteFibonacciRankClosure, declaration := `D5.S3.Arith.Primes.FiniteFibonacciRankClosure.finite_fibonacci_rank_closure, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure, declaration := `Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration).bridge

noncomputable def Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration_1.observation0 : (S : Finset.{0} Nat) →
  (hS :
      ∀ (p : Nat),
        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) S p →
          And (Nat.Prime p)
            (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) p)) →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
      Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (S : Finset.{0} Nat)
    (hS :
      ∀ (p : Nat),
        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) S p →
          And (Nat.Prime p)
            (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) p)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.signature Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.actual
    PUnit.unit.{1} PUnit.unit.{1} S

noncomputable def Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"FiniteFibonacciRankClosure\",\"finite_fibonacci_rank_closure\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"letValue\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FiniteFibonacciRankClosure\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.FiniteFibonacciRankClosure, declaration := `D5.S3.Arith.Primes.FiniteFibonacciRankClosure.finite_fibonacci_rank_closure, part := .type, path := [.body, .body, .letValue], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure, declaration := `Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FiniteFibonacciRankClosure\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FiniteFibonacciRankClosure\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"FiniteFibonacciRankClosure\",\"finite_fibonacci_rank_closure\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure, declaration := `Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.Primes.FiniteFibonacciRankClosure, declaration := `D5.S3.Arith.Primes.FiniteFibonacciRankClosure.finite_fibonacci_rank_closure, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration).actual (Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration).variation.2.choose (Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration).variation.1 (Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FiniteFibonacciRankClosure\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FiniteFibonacciRankClosure\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure, declaration := `Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure, declaration := `Reg.D5.S3.Arith.Primes.FiniteFibonacciRankClosure.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
