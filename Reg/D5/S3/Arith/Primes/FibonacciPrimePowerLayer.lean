import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Primes.FibonacciPrimePowerLayer
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer

open _root_.D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open _root_.D5.S3.Arith.Primes.FibonacciPrimePowerLayer
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
  realize signature (fun _ q s => Nat.fib (q ^ s) / Nat.fib (q ^ (s - 1)))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (q s : ℕ) (_hq : q.Prime) (_hq5 : q ≠ 5) (_hs : 1 ≤ s)
    (_hexclude : ¬ (q = 2 ∧ s = 1)),
    let C := r.readout () q s
    1 < C ∧ Nat.Coprime C (Nat.fib (q ^ (s - 1))) ∧ ¬ IsSquare C ∧
      (∀ p : ℕ, p.Prime → p ∣ C →
        fibonacciRank p = q ^ s ∧ p ≠ q ∧
          padicValNat p C = padicValNat p (Nat.fib (fibonacciRank p))) ∧
      (∃ p : ℕ, p.Prime ∧ p ∣ C ∧
        Odd (padicValNat p (Nat.fib (fibonacciRank p))))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := (h 3 1 (by decide) (by decide) (by decide) (by decide)).1
  change 1 < 1 at hb
  exact Nat.lt_irrefl 1 hb

def registration : Registration arena
    (∀ (q s : ℕ) (_hq : q.Prime) (_hq5 : q ≠ 5) (_hs : 1 ≤ s)
      (_hexclude : ¬ (q = 2 ∧ s = 1)),
      let C := Nat.fib (q ^ s) / Nat.fib (q ^ (s - 1))
      1 < C ∧ Nat.Coprime C (Nat.fib (q ^ (s - 1))) ∧ ¬ IsSquare C ∧
        (∀ p : ℕ, p.Prime → p ∣ C →
          fibonacciRank p = q ^ s ∧ p ≠ q ∧
            padicValNat p C = padicValNat p (Nat.fib (fibonacciRank p))) ∧
        (∃ p : ℕ, p.Prime ∧ p ∣ C ∧
          Odd (padicValNat p (Nat.fib (fibonacciRank p))))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fibonacci_prime_power_layer, rejected, rejected_law⟩
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
    refine ⟨(3 : ℕ), (1 : ℕ), (2 : ℕ), ?_⟩
    change Nat.fib (3 ^ 1) / Nat.fib (3 ^ (1 - 1)) ≠
      Nat.fib (3 ^ 2) / Nat.fib (3 ^ (2 - 1))
    norm_num

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.fibonacci_prime_power_layer) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ q s => Nat.fib (q ^ s) / Nat.fib (q ^ (s - 1))) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Primes") "FibonacciPrimePowerLayer") "fibonacci_prime_power_layer") "Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer/Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ q s => Nat.fib (q ^ s) / Nat.fib (q ^ (s - 1))) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Primes.FibonacciPrimePowerLayer, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "value"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.Primes.FibonacciPrimePowerLayer, declaration := `D5.S3.Arith.Primes.FibonacciPrimePowerLayer.fibonacci_prime_power_layer, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration_1.observationFact0, `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration_1.anchorEnumeration }


end Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer


noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.arena
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerLayer\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerLayer\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.arena
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerLayer\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerLayer\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.arena
    (∀ (q s : Nat) (_hq : Nat.Prime q)
      (_hq5 : @Ne.{1} Nat q (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
      (_hs : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) s)
      (_hexclude :
        Not
          (And (@Eq.{1} Nat q (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@Eq.{1} Nat s (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))),
      have C : Nat :=
        @HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
          (Nat.fib
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q s))
          (Nat.fib
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) s
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))));
      And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) C)
        (And
          (Nat.Coprime C
            (Nat.fib
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) s
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
          (And (Not (@IsSquare.{0} Nat instMulNat C))
            (And
              (∀ (p : Nat),
                Nat.Prime p →
                  @Dvd.dvd.{0} Nat Nat.instDvd p C →
                    And
                      (@Eq.{1} Nat (D5.S3.Arith.Primes.FiniteFibonacciRankClosure.fibonacciRank p)
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q s))
                      (And (@Ne.{1} Nat p q)
                        (@Eq.{1} Nat (padicValNat p C)
                          (padicValNat p (Nat.fib (D5.S3.Arith.Primes.FiniteFibonacciRankClosure.fibonacciRank p))))))
              (@Exists.{1} Nat fun (p : Nat) =>
                And (Nat.Prime p)
                  (And (@Dvd.dvd.{0} Nat Nat.instDvd p C)
                    (@Odd.{0} Nat Nat.instSemiring
                      (padicValNat p (Nat.fib (D5.S3.Arith.Primes.FiniteFibonacciRankClosure.fibonacciRank p))))))))))
    Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration)

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerLayer\",\"fibonacci_prime_power_layer\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerLayer\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.FibonacciPrimePowerLayer, declaration := `D5.S3.Arith.Primes.FibonacciPrimePowerLayer.fibonacci_prime_power_layer, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.arena
  (∀ (q s : Nat) (_hq : Nat.Prime q)
    (_hq5 : @Ne.{1} Nat q (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
    (_hs : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) s)
    (_hexclude :
      Not
        (And (@Eq.{1} Nat q (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@Eq.{1} Nat s (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))),
    have C : Nat :=
      @HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
        (Nat.fib
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q s))
        (Nat.fib
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) s
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))));
    And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) C)
      (And
        (Nat.Coprime C
          (Nat.fib
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) s
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
        (And (Not (@IsSquare.{0} Nat instMulNat C))
          (And
            (∀ (p : Nat),
              Nat.Prime p →
                @Dvd.dvd.{0} Nat Nat.instDvd p C →
                  And
                    (@Eq.{1} Nat (D5.S3.Arith.Primes.FiniteFibonacciRankClosure.fibonacciRank p)
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q s))
                    (And (@Ne.{1} Nat p q)
                      (@Eq.{1} Nat (padicValNat p C)
                        (padicValNat p (Nat.fib (D5.S3.Arith.Primes.FiniteFibonacciRankClosure.fibonacciRank p))))))
            (@Exists.{1} Nat fun (p : Nat) =>
              And (Nat.Prime p)
                (And (@Dvd.dvd.{0} Nat Nat.instDvd p C)
                  (@Odd.{0} Nat Nat.instSemiring
                    (padicValNat p (Nat.fib (D5.S3.Arith.Primes.FiniteFibonacciRankClosure.fibonacciRank p))))))))))
  Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration)

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration_1.observation0 : (q s : Nat) →
  (hq : Nat.Prime q) →
    (hq5 : @Ne.{1} Nat q (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) →
      (hs : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) s) →
        (hexclude :
            Not
              (And (@Eq.{1} Nat q (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@Eq.{1} Nat s (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
            Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.signature PUnit.unit.{1} q :=
  fun (q s : Nat) (hq : Nat.Prime q) (hq5 : @Ne.{1} Nat q (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
    (hs : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) s)
    (hexclude :
      Not
        (And (@Eq.{1} Nat q (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@Eq.{1} Nat s (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.signature Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.actual
    PUnit.unit.{1} q s

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerLayer\",\"fibonacci_prime_power_layer\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"letValue\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerLayer\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.FibonacciPrimePowerLayer, declaration := `D5.S3.Arith.Primes.FibonacciPrimePowerLayer.fibonacci_prime_power_layer, part := .type, path := [.body, .body, .body, .body, .body, .body, .letValue], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerLayer\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerLayer\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerLayer\",\"fibonacci_prime_power_layer\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.Primes.FibonacciPrimePowerLayer, declaration := `D5.S3.Arith.Primes.FibonacciPrimePowerLayer.fibonacci_prime_power_layer, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration).actual (Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration).variation.2.choose (Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration).variation.1 (Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerLayer\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerLayer\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerLayer.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
