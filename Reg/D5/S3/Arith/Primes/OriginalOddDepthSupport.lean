import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Primes.OriginalOddDepthSupport
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport

open _root_.D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open _root_.D5.S3.Arith.Primes.OriginalOddDepthSupport
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
  Law r := ∀ (S : Finset ℕ) (_hS : ∀ p ∈ S, p.Prime ∧ 5 < p)
    (n : ℕ) (_hn : 0 < n) (_hBlock : PrimeIndexOddFactor n)
    (_hExternal : ∀ p : ℕ, p.Prime → 5 < p → p ∣ Nat.fib n → ¬ p ∣ n →
      Odd (padicValNat p (Nat.fib (fibonacciRank p))) → p ∈ S),
    let H := r.readout () () S
    (∀ ell : ℕ, ell.Prime → ell ∣ n → ell ∈ H) ∧
    oddDepthKernel n ∣ H.prod id

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hBlock2 : PrimeIndexOddFactor 2 := by
    intro ell _ hlarge hdiv
    have hle : ell ≤ 2 := Nat.le_of_dvd (by decide) hdiv
    omega
  have hExternal2 : ∀ p : ℕ, p.Prime → 5 < p → p ∣ Nat.fib 2 →
      ¬ p ∣ 2 → Odd (padicValNat p (Nat.fib (fibonacciRank p))) →
      p ∈ (∅ : Finset ℕ) := by
    intro p hp _ hdiv _ _
    have hpOne : p ∣ 1 := by simpa using hdiv
    exact (hp.ne_one (Nat.dvd_one.mp hpOne)).elim
  have hbad := (h ∅ (by simp) 2 (by decide) hBlock2 hExternal2).1
    2 Nat.prime_two (dvd_refl 2)
  change 2 ∈ (∅ : Finset ℕ) at hbad
  simp at hbad

def registration : Registration arena
    (∀ (S : Finset ℕ) (_hS : ∀ p ∈ S, p.Prime ∧ 5 < p)
      (n : ℕ) (_hn : 0 < n) (_hBlock : PrimeIndexOddFactor n)
      (_hExternal : ∀ p : ℕ, p.Prime → 5 < p → p ∣ Nat.fib n → ¬ p ∣ n →
        Odd (padicValNat p (Nat.fib (fibonacciRank p))) → p ∈ S),
      let H := fibonacciRankClosure S
      (∀ ell : ℕ, ell.Prime → ell ∣ n → ell ∈ H) ∧
      oddDepthKernel n ∣ H.prod id) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨original_odd_depth_support, rejected, rejected_law⟩
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

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Primes.OriginalOddDepthSupport.original_odd_depth_support) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ S => fibonacciRankClosure S) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Primes") "OriginalOddDepthSupport") "original_odd_depth_support") "Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport/Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration,
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
  sourceSelection := some { owner := `D5.S3.Arith.Primes.OriginalOddDepthSupport, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "value"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.Primes.OriginalOddDepthSupport, declaration := `D5.S3.Arith.Primes.OriginalOddDepthSupport.original_odd_depth_support, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport, declaration := `Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport, declaration := `Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport, declaration := `Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport, declaration := `Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration_1.observationFact0, `Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration_1.anchorEnumeration }


end Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport


noncomputable def Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.arena
noncomputable def Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"OriginalOddDepthSupport\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"OriginalOddDepthSupport\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport, declaration := `Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport, declaration := `Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.arena
noncomputable def Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"OriginalOddDepthSupport\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"OriginalOddDepthSupport\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport, declaration := `Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport, declaration := `Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.arena) (Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration).actual

noncomputable def Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"OriginalOddDepthSupport\",\"original_odd_depth_support\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"OriginalOddDepthSupport\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.OriginalOddDepthSupport, declaration := `D5.S3.Arith.Primes.OriginalOddDepthSupport.original_odd_depth_support, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport, declaration := `Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration).bridge

noncomputable def Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration_1.observation0 : (S : Finset.{0} Nat) →
  (hS :
      ∀ (p : Nat),
        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) S p →
          And (Nat.Prime p)
            (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) p)) →
    (n : Nat) →
      (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n) →
        (hBlock : D5.S3.Arith.Primes.OriginalOddDepthSupport.PrimeIndexOddFactor n) →
          (hExternal :
              ∀ (p : Nat),
                Nat.Prime p →
                  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) p →
                    @Dvd.dvd.{0} Nat Nat.instDvd p (Nat.fib n) →
                      Not (@Dvd.dvd.{0} Nat Nat.instDvd p n) →
                        @Odd.{0} Nat Nat.instSemiring
                            (padicValNat p (Nat.fib (D5.S3.Arith.Primes.FiniteFibonacciRankClosure.fibonacciRank p))) →
                          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) S p) →
            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (S : Finset.{0} Nat)
    (hS :
      ∀ (p : Nat),
        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) S p →
          And (Nat.Prime p) (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) p))
    (n : Nat) (hn : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n)
    (hBlock : D5.S3.Arith.Primes.OriginalOddDepthSupport.PrimeIndexOddFactor n)
    (hExternal :
      ∀ (p : Nat),
        Nat.Prime p →
          @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) p →
            @Dvd.dvd.{0} Nat Nat.instDvd p (Nat.fib n) →
              Not (@Dvd.dvd.{0} Nat Nat.instDvd p n) →
                @Odd.{0} Nat Nat.instSemiring
                    (padicValNat p (Nat.fib (D5.S3.Arith.Primes.FiniteFibonacciRankClosure.fibonacciRank p))) →
                  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                    (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) S p) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.signature Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.actual
    PUnit.unit.{1} PUnit.unit.{1} S

noncomputable def Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"OriginalOddDepthSupport\",\"original_odd_depth_support\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"letValue\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"OriginalOddDepthSupport\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.OriginalOddDepthSupport, declaration := `D5.S3.Arith.Primes.OriginalOddDepthSupport.original_odd_depth_support, part := .type, path := [.body, .body, .body, .body, .body, .body, .letValue], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport, declaration := `Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"OriginalOddDepthSupport\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"OriginalOddDepthSupport\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"OriginalOddDepthSupport\",\"original_odd_depth_support\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport, declaration := `Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.Primes.OriginalOddDepthSupport, declaration := `D5.S3.Arith.Primes.OriginalOddDepthSupport.original_odd_depth_support, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration).actual (Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration).variation.2.choose (Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration).variation.1 (Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"OriginalOddDepthSupport\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"OriginalOddDepthSupport\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport, declaration := `Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport, declaration := `Reg.D5.S3.Arith.Primes.OriginalOddDepthSupport.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
