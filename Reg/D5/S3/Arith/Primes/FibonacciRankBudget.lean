import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Primes.FibonacciRankBudget
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.FibonacciRankBudget

open _root_.D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open _root_.D5.S3.Arith.Primes.FibonacciRankBudget
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

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
  realize signature (fun _ _ n => n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (H : Finset ℕ) (n : ℕ)
    (_hH : ∀ p ∈ H, p.Prime)
    (_hTwo : 2 ∈ H) (_hThree : 3 ∈ H) (_hFive : 5 ∈ H)
    (_hClosed : rankClosureStep H = H) (_hn : 0 < n)
    (_hOdd : ∀ p : ℕ, p.Prime → p ∣ Nat.fib n →
      Odd (padicValNat p (Nat.fib n)) → p ∈ H),
    r.readout () H n ∣ 5 * H.lcm fibonacciRank ∧
      (∀ q : ℕ, q.Prime → q ≠ 5 →
        padicValNat q n ≤ padicValNat q (H.lcm fibonacciRank)) ∧
      padicValNat 5 n ≤ padicValNat 5 (H.lcm fibonacciRank) + 1

theorem rejected_law : ¬ arena.Law rejected := by
  classical
  intro h
  let H := fibonacciRankClosure ∅
  have hs : ∀ p ∈ (∅ : Finset ℕ), p.Prime ∧ 5 < p := by simp
  have hc := finite_fibonacci_rank_closure ∅ hs
  have hTwo : 2 ∈ H := hc.1 (by simp [rankClosureSeed])
  have hThree : 3 ∈ H := hc.1 (by simp [rankClosureSeed])
  have hFive : 5 ∈ H := hc.1 (by simp [rankClosureSeed])
  have hOdd : ∀ p : ℕ, p.Prime → p ∣ Nat.fib 1 →
      Odd (padicValNat p (Nat.fib 1)) → p ∈ H := by
    intro p hp hpFib _
    have hpOne : p ∣ 1 := by simpa using hpFib
    exact (hp.ne_one (Nat.dvd_one.mp hpOne)).elim
  have hbad := (h H 1 hc.2.1 hTwo hThree hFive hc.2.2.2.1 (by decide) hOdd).1
  change 0 ∣ 5 * H.lcm fibonacciRank at hbad
  have hR : H.lcm fibonacciRank ≠ 0 := by
    rw [Finset.lcm_ne_zero_iff]
    intro p hp
    simp only [fibonacciRank, hc.2.1 p hp, dite_true]
    exact (rankWitness p (hc.2.1 p hp)).property.1.ne'
  exact (mul_ne_zero (by decide : (5 : ℕ) ≠ 0) hR) (Nat.zero_dvd.mp hbad)

def registration : Registration arena
    (∀ (H : Finset ℕ) (n : ℕ)
      (_hH : ∀ p ∈ H, p.Prime)
      (_hTwo : 2 ∈ H) (_hThree : 3 ∈ H) (_hFive : 5 ∈ H)
      (_hClosed : rankClosureStep H = H) (_hn : 0 < n)
      (_hOdd : ∀ p : ℕ, p.Prime → p ∣ Nat.fib n →
        Odd (padicValNat p (Nat.fib n)) → p ∈ H),
      n ∣ 5 * H.lcm fibonacciRank ∧
        (∀ q : ℕ, q.Prime → q ≠ 5 →
          padicValNat q n ≤ padicValNat q (H.lcm fibonacciRank)) ∧
        padicValNat 5 n ≤ padicValNat 5 (H.lcm fibonacciRank) + 1) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fibonacci_rank_budget, rejected, rejected_law⟩
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
    exact ⟨(∅ : Finset ℕ), (1 : ℕ), (2 : ℕ), by change (1 : ℕ) ≠ 2; decide⟩

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Primes.FibonacciRankBudget.fibonacci_rank_budget) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => n) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Primes") "FibonacciRankBudget") "fibonacci_rank_budget") "Reg.D5.S3.Arith.Primes.FibonacciRankBudget/Reg.D5.S3.Arith.Primes.FibonacciRankBudget.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ n => n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Primes.FibonacciRankBudget, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.Primes.FibonacciRankBudget, declaration := `D5.S3.Arith.Primes.FibonacciRankBudget.fibonacci_rank_budget, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciRankBudget, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciRankBudget, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciRankBudget, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciRankBudget, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration_1.observationFact0, `Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration_1.anchorEnumeration }


end Reg.D5.S3.Arith.Primes.FibonacciRankBudget


noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.FibonacciRankBudget.arena
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRankBudget\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRankBudget\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciRankBudget, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciRankBudget, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.FibonacciRankBudget.arena
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRankBudget\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRankBudget\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciRankBudget, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciRankBudget, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Arith.Primes.FibonacciRankBudget.arena) (Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration).actual

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRankBudget\",\"fibonacci_rank_budget\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRankBudget\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.FibonacciRankBudget, declaration := `D5.S3.Arith.Primes.FibonacciRankBudget.fibonacci_rank_budget, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciRankBudget, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration).bridge

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration_1.observation0 : (H : Finset.{0} Nat) →
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
        (hThree :
            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) H
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) →
          (hFive :
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) H
                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) →
            (hClosed : @Eq.{1} (Finset.{0} Nat) (D5.S3.Arith.Primes.FiniteFibonacciRankClosure.rankClosureStep H) H) →
              (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) →
                (hOdd :
                    ∀ (p : Nat),
                      Nat.Prime p →
                        @Dvd.dvd.{0} Nat Nat.instDvd p (Nat.fib n) →
                          @Odd.{0} Nat Nat.instSemiring (padicValNat p (Nat.fib n)) →
                            @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) H p) →
                  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                    Reg.D5.S3.Arith.Primes.FibonacciRankBudget.signature PUnit.unit.{1} H :=
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
    (hThree :
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) H
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
    (hFive :
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
        (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) H
        (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
    (hClosed : @Eq.{1} (Finset.{0} Nat) (D5.S3.Arith.Primes.FiniteFibonacciRankClosure.rankClosureStep H) H)
    (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
    (hOdd :
      ∀ (p : Nat),
        Nat.Prime p →
          @Dvd.dvd.{0} Nat Nat.instDvd p (Nat.fib n) →
            @Odd.{0} Nat Nat.instSemiring (padicValNat p (Nat.fib n)) →
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) H p) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Primes.FibonacciRankBudget.signature Reg.D5.S3.Arith.Primes.FibonacciRankBudget.actual
    PUnit.unit.{1} H n

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRankBudget\",\"fibonacci_rank_budget\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRankBudget\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.FibonacciRankBudget, declaration := `D5.S3.Arith.Primes.FibonacciRankBudget.fibonacci_rank_budget, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .function, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciRankBudget, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRankBudget\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRankBudget\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRankBudget\",\"fibonacci_rank_budget\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.Primes.FibonacciRankBudget, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.Primes.FibonacciRankBudget, declaration := `D5.S3.Arith.Primes.FibonacciRankBudget.fibonacci_rank_budget, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration).actual (Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration).variation.2.choose (Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration).variation.1 (Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRankBudget\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciRankBudget\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciRankBudget, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciRankBudget, declaration := `Reg.D5.S3.Arith.Primes.FibonacciRankBudget.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
