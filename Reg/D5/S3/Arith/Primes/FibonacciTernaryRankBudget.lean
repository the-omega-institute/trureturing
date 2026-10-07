import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Primes.FibonacciTernaryRankBudget
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget

open _root_.D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open _root_.D5.S3.Arith.Primes.FibonacciTernaryRankBudget
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

abbrev signature : Signature where
  Params := Finset ℕ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => padicValNat 3 n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature
    (fun _ H _ => padicValNat 3 (H.lcm fibonacciRank) + 1)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (H : Finset ℕ) (n : ℕ)
    (_hH : ∀ p ∈ H, p.Prime) (_hTwo : 2 ∈ H) (_hn : 0 < n)
    (_hIndex : ∀ p : ℕ, p.Prime → p ∣ n → p ∈ H)
    (_hOdd : ∀ p : ℕ, p.Prime → p ∣ Nat.fib n →
      Odd (padicValNat p (Nat.fib n)) → p ∈ H),
    r.readout () H n ≤ padicValNat 3 (H.lcm fibonacciRank)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hH : ∀ p ∈ ({2} : Finset ℕ), p.Prime := by
    intro p hp
    simp only [Finset.mem_singleton] at hp
    subst p
    decide
  have hIndex : ∀ p : ℕ, p.Prime → p ∣ 1 → p ∈ ({2} : Finset ℕ) := by
    intro p hp hpOne
    exact (hp.ne_one (Nat.dvd_one.mp hpOne)).elim
  have hOdd : ∀ p : ℕ, p.Prime → p ∣ Nat.fib 1 →
      Odd (padicValNat p (Nat.fib 1)) → p ∈ ({2} : Finset ℕ) := by
    intro p hp hpFib _
    have hpOne : p ∣ 1 := by simpa using hpFib
    exact (hp.ne_one (Nat.dvd_one.mp hpOne)).elim
  have hbad := h {2} 1 hH (by simp) (by decide) hIndex hOdd
  change padicValNat 3 (({2} : Finset ℕ).lcm fibonacciRank) + 1 ≤
    padicValNat 3 (({2} : Finset ℕ).lcm fibonacciRank) at hbad
  omega

def registration : Registration arena
    (∀ (H : Finset ℕ) (n : ℕ)
      (_hH : ∀ p ∈ H, p.Prime) (_hTwo : 2 ∈ H) (_hn : 0 < n)
      (_hIndex : ∀ p : ℕ, p.Prime → p ∣ n → p ∈ H)
      (_hOdd : ∀ p : ℕ, p.Prime → p ∣ Nat.fib n →
        Odd (padicValNat p (Nat.fib n)) → p ∈ H),
      padicValNat 3 n ≤ padicValNat 3 (H.lcm fibonacciRank)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fibonacci_ternary_rank_budget, rejected, rejected_law⟩
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
    refine ⟨(∅ : Finset ℕ), (3 : ℕ), (9 : ℕ), ?_⟩
    change padicValNat 3 3 ≠ padicValNat 3 9
    have h3 : padicValNat 3 3 = 1 := by
      change padicValNat 3 (3 ^ 1) = 1
      exact padicValNat.prime_pow 1
    have h9 : padicValNat 3 9 = 2 := by
      change padicValNat 3 (3 ^ 2) = 2
      exact padicValNat.prime_pow 2
    omega

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.fibonacci_ternary_rank_budget) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => padicValNat 3 n)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Primes") "FibonacciTernaryRankBudget") "fibonacci_ternary_rank_budget") "Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget/Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => padicValNat 3 n)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Primes.FibonacciTernaryRankBudget, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.Primes.FibonacciTernaryRankBudget, declaration := `D5.S3.Arith.Primes.FibonacciTernaryRankBudget.fibonacci_ternary_rank_budget, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget, declaration := `Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget, declaration := `Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget, declaration := `Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget, declaration := `Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration_1.observationFact0, `Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration_1.anchorEnumeration }


end Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget


noncomputable def Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.arena
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciTernaryRankBudget\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciTernaryRankBudget\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget, declaration := `Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget, declaration := `Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.arena
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciTernaryRankBudget\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciTernaryRankBudget\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget, declaration := `Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget, declaration := `Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.arena) (Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration).actual

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciTernaryRankBudget\",\"fibonacci_ternary_rank_budget\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciTernaryRankBudget\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.FibonacciTernaryRankBudget, declaration := `D5.S3.Arith.Primes.FibonacciTernaryRankBudget.fibonacci_ternary_rank_budget, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget, declaration := `Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration).bridge

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration_1.observation0 : (H : Finset.{0} Nat) →
  (n : Nat) →
    (hH :
        ∀ (p : Nat),
          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) H p →
            Nat.Prime p) →
      (hTwo :
          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) H
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
        (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) →
          (hIndex :
              ∀ (p : Nat),
                Nat.Prime p →
                  @Dvd.dvd.{0} Nat Nat.instDvd p n →
                    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) H p) →
            (hOdd :
                ∀ (p : Nat),
                  Nat.Prime p →
                    @Dvd.dvd.{0} Nat Nat.instDvd p (Nat.fib n) →
                      @Odd.{0} Nat Nat.instSemiring (padicValNat p (Nat.fib n)) →
                        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) H p) →
              D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.signature PUnit.unit.{1} H :=
  fun (H : Finset.{0} Nat) (n : Nat)
    (hH :
      ∀ (p : Nat),
        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) H p →
          Nat.Prime p)
    (hTwo :
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) H
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
    (hIndex :
      ∀ (p : Nat),
        Nat.Prime p →
          @Dvd.dvd.{0} Nat Nat.instDvd p n →
            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) H p)
    (hOdd :
      ∀ (p : Nat),
        Nat.Prime p →
          @Dvd.dvd.{0} Nat Nat.instDvd p (Nat.fib n) →
            @Odd.{0} Nat Nat.instSemiring (padicValNat p (Nat.fib n)) →
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) H p) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.signature Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.actual
    PUnit.unit.{1} H n

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciTernaryRankBudget\",\"fibonacci_ternary_rank_budget\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciTernaryRankBudget\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.FibonacciTernaryRankBudget, declaration := `D5.S3.Arith.Primes.FibonacciTernaryRankBudget.fibonacci_ternary_rank_budget, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget, declaration := `Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciTernaryRankBudget\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciTernaryRankBudget\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciTernaryRankBudget\",\"fibonacci_ternary_rank_budget\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget, declaration := `Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.Primes.FibonacciTernaryRankBudget, declaration := `D5.S3.Arith.Primes.FibonacciTernaryRankBudget.fibonacci_ternary_rank_budget, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration).actual (Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration).variation.2.choose (Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration).variation.1 (Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciTernaryRankBudget\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciTernaryRankBudget\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget, declaration := `Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget, declaration := `Reg.D5.S3.Arith.Primes.FibonacciTernaryRankBudget.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
