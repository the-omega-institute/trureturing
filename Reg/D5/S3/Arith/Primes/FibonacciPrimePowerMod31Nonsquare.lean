import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare

open _root_.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare
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
  realize signature (fun _ q k => Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (q k : ℕ) (_hq : q.Prime) (_hqge : 7 ≤ q)
      (_hclass : q % 120 = 49 ∨ q % 120 = 71),
    0 < r.readout () q k ∧
      (r.readout () q k) % 31 = (if k % 2 = 0 then 27 else 23) ∧
      ¬ IsSquare (r.readout () q k)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h 71 0 (by decide) (by decide) (by decide)).2.1
  norm_num [rejected, realize] at hbad

def registration : Registration arena
    (∀ (q k : ℕ) (_hq : q.Prime) (_hqge : 7 ≤ q)
      (_hclass : q % 120 = 49 ∨ q % 120 = 71),
      0 < Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k) ∧
        (Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k)) % 31 =
          (if k % 2 = 0 then 27 else 23) ∧
        ¬ IsSquare (Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    intro q k hq hqge hclass
    exact fibonacci_prime_power_mod31_nonsquare q k hq hqge hclass,
    rejected, rejected_law⟩
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
    refine ⟨2, (0 : ℕ), (1 : ℕ), ?_⟩
    change Nat.fib (2 ^ (0 + 1)) / Nat.fib (2 ^ 0) ≠
      Nat.fib (2 ^ (1 + 1)) / Nat.fib (2 ^ 1)
    decide

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.fibonacci_prime_power_mod31_nonsquare) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ q k => Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Primes") "FibonacciPrimePowerMod31Nonsquare") "fibonacci_prime_power_mod31_nonsquare") "Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare/Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration,
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
    (fun _ q k => Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "arg", "arg", "arg", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare, declaration := `D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.fibonacci_prime_power_mod31_nonsquare, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration_1.observationFact0, `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration_1.anchorEnumeration }


end Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare


noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.arena
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerMod31Nonsquare\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerMod31Nonsquare\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.arena
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerMod31Nonsquare\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerMod31Nonsquare\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.arena
    (∀ (q k : Nat) (_hq : Nat.Prime q)
      (_hqge : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) q)
      (_hclass :
        Or
          (@Eq.{1} Nat
            (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) q
              (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120))))
            (@OfNat.ofNat.{0} Nat (nat_lit 49) (instOfNatNat (nat_lit 49))))
          (@Eq.{1} Nat
            (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) q
              (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120))))
            (@OfNat.ofNat.{0} Nat (nat_lit 71) (instOfNatNat (nat_lit 71))))),
      And
        (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
            (Nat.fib
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (Nat.fib
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q k))))
        (And
          (@Eq.{1} Nat
            (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod)
              (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                (Nat.fib
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (Nat.fib
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q k)))
              (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31))))
            (@ite.{1} Nat
              (@Eq.{1} Nat
                (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) k
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (instDecidableEqNat
                (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) k
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@OfNat.ofNat.{0} Nat (nat_lit 27) (instOfNatNat (nat_lit 27)))
              (@OfNat.ofNat.{0} Nat (nat_lit 23) (instOfNatNat (nat_lit 23)))))
          (Not
            (@IsSquare.{0} Nat instMulNat
              (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                (Nat.fib
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (Nat.fib
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q k)))))))
    Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration)

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerMod31Nonsquare\",\"fibonacci_prime_power_mod31_nonsquare\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerMod31Nonsquare\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare, declaration := `D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.fibonacci_prime_power_mod31_nonsquare, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.arena
  (∀ (q k : Nat) (_hq : Nat.Prime q)
    (_hqge : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) q)
    (_hclass :
      Or
        (@Eq.{1} Nat
          (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) q
            (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120))))
          (@OfNat.ofNat.{0} Nat (nat_lit 49) (instOfNatNat (nat_lit 49))))
        (@Eq.{1} Nat
          (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) q
            (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120))))
          (@OfNat.ofNat.{0} Nat (nat_lit 71) (instOfNatNat (nat_lit 71))))),
    And
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
          (Nat.fib
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (Nat.fib
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q k))))
      (And
        (@Eq.{1} Nat
          (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod)
            (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
              (Nat.fib
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (Nat.fib
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q k)))
            (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31))))
          (@ite.{1} Nat
            (@Eq.{1} Nat
              (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) k
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (instDecidableEqNat
              (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) k
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (@OfNat.ofNat.{0} Nat (nat_lit 27) (instOfNatNat (nat_lit 27)))
            (@OfNat.ofNat.{0} Nat (nat_lit 23) (instOfNatNat (nat_lit 23)))))
        (Not
          (@IsSquare.{0} Nat instMulNat
            (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
              (Nat.fib
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (Nat.fib
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) q k)))))))
  Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration)

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration_1.observation0 : (q k : Nat) →
  (hq : Nat.Prime q) →
    (hqge : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) q) →
      (hclass :
          Or
            (@Eq.{1} Nat
              (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) q
                (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120))))
              (@OfNat.ofNat.{0} Nat (nat_lit 49) (instOfNatNat (nat_lit 49))))
            (@Eq.{1} Nat
              (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) q
                (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120))))
              (@OfNat.ofNat.{0} Nat (nat_lit 71) (instOfNatNat (nat_lit 71))))) →
        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
          Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.signature PUnit.unit.{1} q :=
  fun (q k : Nat) (hq : Nat.Prime q)
    (hqge : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) q)
    (hclass :
      Or
        (@Eq.{1} Nat
          (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) q
            (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120))))
          (@OfNat.ofNat.{0} Nat (nat_lit 49) (instOfNatNat (nat_lit 49))))
        (@Eq.{1} Nat
          (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) q
            (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120))))
          (@OfNat.ofNat.{0} Nat (nat_lit 71) (instOfNatNat (nat_lit 71))))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.signature
    Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.actual PUnit.unit.{1} q k

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerMod31Nonsquare\",\"fibonacci_prime_power_mod31_nonsquare\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerMod31Nonsquare\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare, declaration := `D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.fibonacci_prime_power_mod31_nonsquare, part := .type, path := [.body, .body, .body, .body, .body, .argument, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerMod31Nonsquare\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerMod31Nonsquare\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerMod31Nonsquare\",\"fibonacci_prime_power_mod31_nonsquare\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare, declaration := `D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.fibonacci_prime_power_mod31_nonsquare, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration).actual (Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration).variation.2.choose (Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration).variation.1 (Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerMod31Nonsquare\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerMod31Nonsquare\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerMod31Nonsquare.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
