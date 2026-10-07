import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare

open _root_.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare
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
      (_h1 : q % 120 ≠ 1) (_h49 : q % 120 ≠ 49)
      (_h71 : q % 120 ≠ 71) (_h119 : q % 120 ≠ 119),
    0 < Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k) ∧
      ¬ IsSquare (r.readout () q k)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h 7 0 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).2
  apply hbad
  change IsSquare (1 : ℕ)
  exact ⟨1, by norm_num⟩

def registration : Registration arena
    (∀ (q k : ℕ) (_hq : q.Prime) (_hqge : 7 ≤ q)
      (_h1 : q % 120 ≠ 1) (_h49 : q % 120 ≠ 49)
      (_h71 : q % 120 ≠ 71) (_h119 : q % 120 ≠ 119),
      0 < Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k) ∧
        ¬ IsSquare (Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨by
    intro q k hq hqge h1 h49 h71 h119
    exact fibonacci_prime_power_modular_nonsquare q k hq hqge h1 h49 h71 h119,
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
    refine ⟨7, (0 : ℕ), (1 : ℕ), ?_⟩
    change Nat.fib (7 ^ (0 + 1)) / Nat.fib (7 ^ 0) ≠
      Nat.fib (7 ^ (1 + 1)) / Nat.fib (7 ^ 1)
    decide

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.fibonacci_prime_power_modular_nonsquare) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ q k => Nat.fib (q ^ (k + 1)) / Nat.fib (q ^ k))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Primes") "FibonacciPrimePowerModularNonsquare") "fibonacci_prime_power_modular_nonsquare") "Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare/Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration,
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
  sourceSelection := some { owner := `D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare, declaration := `D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.fibonacci_prime_power_modular_nonsquare, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration_1.observationFact0, `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration_1.anchorEnumeration }


end Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare


noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.arena
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerModularNonsquare\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerModularNonsquare\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.arena
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerModularNonsquare\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerModularNonsquare\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.arena) (Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration).actual

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerModularNonsquare\",\"fibonacci_prime_power_modular_nonsquare\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerModularNonsquare\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare, declaration := `D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.fibonacci_prime_power_modular_nonsquare, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration).bridge

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration_1.observation0 : (q k : Nat) →
  (hq : Nat.Prime q) →
    (hqge : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) q) →
      (h1 :
          @Ne.{1} Nat
            (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) q
              (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        (h49 :
            @Ne.{1} Nat
              (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) q
                (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120))))
              (@OfNat.ofNat.{0} Nat (nat_lit 49) (instOfNatNat (nat_lit 49)))) →
          (h71 :
              @Ne.{1} Nat
                (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) q
                  (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120))))
                (@OfNat.ofNat.{0} Nat (nat_lit 71) (instOfNatNat (nat_lit 71)))) →
            (h119 :
                @Ne.{1} Nat
                  (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) q
                    (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 119) (instOfNatNat (nat_lit 119)))) →
              D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.signature PUnit.unit.{1} q :=
  fun (q k : Nat) (hq : Nat.Prime q)
    (hqge : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) q)
    (h1 :
      @Ne.{1} Nat
        (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) q
          (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (h49 :
      @Ne.{1} Nat
        (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) q
          (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120))))
        (@OfNat.ofNat.{0} Nat (nat_lit 49) (instOfNatNat (nat_lit 49))))
    (h71 :
      @Ne.{1} Nat
        (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) q
          (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120))))
        (@OfNat.ofNat.{0} Nat (nat_lit 71) (instOfNatNat (nat_lit 71))))
    (h119 :
      @Ne.{1} Nat
        (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) q
          (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120))))
        (@OfNat.ofNat.{0} Nat (nat_lit 119) (instOfNatNat (nat_lit 119)))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.signature
    Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.actual PUnit.unit.{1} q k

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerModularNonsquare\",\"fibonacci_prime_power_modular_nonsquare\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerModularNonsquare\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare, declaration := `D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.fibonacci_prime_power_modular_nonsquare, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerModularNonsquare\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerModularNonsquare\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerModularNonsquare\",\"fibonacci_prime_power_modular_nonsquare\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare, declaration := `D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.fibonacci_prime_power_modular_nonsquare, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration).actual (Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration).variation.2.choose (Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration).variation.1 (Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerModularNonsquare\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciPrimePowerModularNonsquare\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciPrimePowerModularNonsquare.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
