import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare

open _root_.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare
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
  realize signature (fun _ _ k => Nat.fib (2 ^ (k + 1)) / Nat.fib (2 ^ k))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ k => Nat.fib (2 ^ (k + 1)) / Nat.fib (2 ^ k) + 1)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (k : ℕ) (_hk : 1 ≤ k),
    let q := r.readout () () k
    (k = 1 → q % 5 = 3) ∧ (2 ≤ k → q % 5 = 2) ∧ ¬ IsSquare q

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h 1 (by decide)).1 rfl
  change (Nat.fib (2 ^ (1 + 1)) / Nat.fib (2 ^ 1) + 1) % 5 = 3 at hbad
  norm_num at hbad

def registration : Registration arena
    (∀ (k : ℕ) (_hk : 1 ≤ k),
      let q := Nat.fib (2 ^ (k + 1)) / Nat.fib (2 ^ k)
      (k = 1 → q % 5 = 3) ∧ (2 ≤ k → q % 5 = 2) ∧ ¬ IsSquare q) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fibonacci_dyadic_quotient_nonsquare, rejected, rejected_law⟩
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
    refine ⟨(), (1 : ℕ), (2 : ℕ), ?_⟩
    change Nat.fib (2 ^ (1 + 1)) / Nat.fib (2 ^ 1) ≠
      Nat.fib (2 ^ (2 + 1)) / Nat.fib (2 ^ 2)
    norm_num

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.fibonacci_dyadic_quotient_nonsquare) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ _ k => Nat.fib (2 ^ (k + 1)) / Nat.fib (2 ^ k))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Primes") "FibonacciDyadicQuotientNonsquare") "fibonacci_dyadic_quotient_nonsquare") "Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare/Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration,
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
    (fun _ _ k => Nat.fib (2 ^ (k + 1)) / Nat.fib (2 ^ k))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "value"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare, declaration := `D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.fibonacci_dyadic_quotient_nonsquare, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration_1.observationFact0, `Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration_1.anchorEnumeration }


end Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare


noncomputable def Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.arena
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciDyadicQuotientNonsquare\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciDyadicQuotientNonsquare\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.arena
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciDyadicQuotientNonsquare\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciDyadicQuotientNonsquare\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.arena
    (∀ (k : Nat) (_hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k),
      have q : Nat :=
        @HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
          (Nat.fib
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (Nat.fib
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k));
      And
        (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @Eq.{1} Nat
            (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) q
              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (And
          (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k →
            @Eq.{1} Nat
              (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) q
                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Not (@IsSquare.{0} Nat instMulNat q))))
    Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration)

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciDyadicQuotientNonsquare\",\"fibonacci_dyadic_quotient_nonsquare\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciDyadicQuotientNonsquare\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare, declaration := `D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.fibonacci_dyadic_quotient_nonsquare, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.arena
  (∀ (k : Nat) (_hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k),
    have q : Nat :=
      @HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
        (Nat.fib
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (Nat.fib
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k));
    And
      (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        @Eq.{1} Nat
          (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) q
            (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (And
        (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k →
          @Eq.{1} Nat
            (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) q
              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (Not (@IsSquare.{0} Nat instMulNat q))))
  Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration)

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration_1.observation0 : (k : Nat) →
  (hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k) →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
      Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (k : Nat) (hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.signature
    Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.actual PUnit.unit.{1} PUnit.unit.{1} k

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciDyadicQuotientNonsquare\",\"fibonacci_dyadic_quotient_nonsquare\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"letValue\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciDyadicQuotientNonsquare\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare, declaration := `D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.fibonacci_dyadic_quotient_nonsquare, part := .type, path := [.body, .body, .letValue], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciDyadicQuotientNonsquare\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciDyadicQuotientNonsquare\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciDyadicQuotientNonsquare\",\"fibonacci_dyadic_quotient_nonsquare\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare, declaration := `D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.fibonacci_dyadic_quotient_nonsquare, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration).actual (Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration).variation.2.choose (Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration).variation.1 (Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciDyadicQuotientNonsquare\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"FibonacciDyadicQuotientNonsquare\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare, declaration := `Reg.D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
