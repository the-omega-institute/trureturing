import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon

@[reducible] def signature : Signature where
  Params := Σ _p : ℕ, Σ _z : ℤ, ℕ
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ q n => Nat.gcd (signedObservation q.2.2 n q.2.1).natAbs q.1)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ q n => if q.2.2 = horizon q.1 + 1 then n.natAbs else 0)
    (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (p : ℕ), p.Prime →
    (∀ n z n' z' : ℤ,
      (∀ k : ℕ, 1 ≤ k → k ≤ horizon p →
        R.readout () ⟨p, z, k⟩ n = R.readout () ⟨p, z', k⟩ n') →
      ∀ k : ℕ, 1 ≤ k →
        R.readout () ⟨p, z, k⟩ n = R.readout () ⟨p, z', k⟩ n') ∧
    (∀ a b c d : ℕ,
      (∀ k : ℕ, 1 ≤ k → k ≤ horizon p →
        Nat.gcd (observation k a b) p = Nat.gcd (observation k c d) p) →
      ∀ k : ℕ, 1 ≤ k →
        Nat.gcd (observation k a b) p = Nat.gcd (observation k c d) p) ∧
    (∃ a b c d : ℕ, a < p ∧ b < p ∧ c < p ∧ d < p ∧
      (∀ k : ℕ, 1 ≤ k → k < horizon p →
        Nat.gcd (observation k a b) p = Nat.gcd (observation k c d) p) ∧
      Nat.gcd (observation (horizon p) a b) p ≠
        Nat.gcd (observation (horizon p) c d) p)

theorem actual_law : arena.Law actual := sharp_prime_gcd_horizon

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hprefix : ∀ k : ℕ, 1 ≤ k → k ≤ horizon 2 →
      rejected.readout () ⟨2, 0, k⟩ 0 = rejected.readout () ⟨2, 0, k⟩ 1 := by
    intro k _ hk
    have hne : k ≠ horizon 2 + 1 := by omega
    simp [rejected, realize, hne]
  have hlast := (h 2 Nat.prime_two).1 0 0 1 0 hprefix (horizon 2 + 1) (by omega)
  simp [rejected, realize] at hlast

def registration : Registration arena
    (∀ (p : ℕ) (hp : p.Prime),
      (∀ n z n' z' : ℤ,
        (∀ k : ℕ, 1 ≤ k → k ≤ horizon p →
          Nat.gcd (signedObservation k n z).natAbs p =
            Nat.gcd (signedObservation k n' z').natAbs p) →
        ∀ k : ℕ, 1 ≤ k →
          Nat.gcd (signedObservation k n z).natAbs p =
            Nat.gcd (signedObservation k n' z').natAbs p) ∧
      (∀ a b c d : ℕ,
        (∀ k : ℕ, 1 ≤ k → k ≤ horizon p →
          Nat.gcd (observation k a b) p = Nat.gcd (observation k c d) p) →
        ∀ k : ℕ, 1 ≤ k →
          Nat.gcd (observation k a b) p = Nat.gcd (observation k c d) p) ∧
      (∃ a b c d : ℕ, a < p ∧ b < p ∧ c < p ∧ d < p ∧
        (∀ k : ℕ, 1 ≤ k → k < horizon p →
          Nat.gcd (observation k a b) p = Nat.gcd (observation k c d) p) ∧
        Nat.gcd (observation (horizon p) a b) p ≠
          Nat.gcd (observation (horizon p) c d) p)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    cases i
    refine ⟨⟨2, 0, 2⟩, 0, 1, ?_⟩
    decide

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.sharp_prime_gcd_horizon) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ q n => Nat.gcd (signedObservation q.2.2 n q.2.1).natAbs q.1)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "FibonacciAtomic") "PrimeGcdHorizon") "sharp_prime_gcd_horizon") "Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon/Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration,
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
    (fun _ q n => Nat.gcd (signedObservation q.2.2 n q.2.1).natAbs q.1)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon, definition := none, coordinates := #[0, 3, 6], readouts := #[{ path := #["body", "body", "fn", "arg", "body", "body", "body", "body", "domain", "body", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg", "arg", "fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon, declaration := `D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.sharp_prime_gcd_horizon, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration_1.observationFact0, `Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.arena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimeGcdHorizon\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimeGcdHorizon\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.arena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimeGcdHorizon\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimeGcdHorizon\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.arena) (Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration).actual

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimeGcdHorizon\",\"sharp_prime_gcd_horizon\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimeGcdHorizon\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon, declaration := `D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.sharp_prime_gcd_horizon, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration).bridge

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration_1.observation0 : (p : Nat) →
  (hp : Nat.Prime p) →
    (n z n' z' : Int) →
      (k : Nat) →
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k →
          @LE.le.{0} Nat instLENat k (D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.horizon p) →
            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.signature PUnit.unit.{1}
              (@Sigma.mk.{0, 0} Nat (fun (_p : Nat) => @Sigma.{0, 0} Int fun (_z : Int) => Nat) p
                (@Sigma.mk.{0, 0} Int (fun (_z : Int) => Nat) z k)) :=
  fun (p : Nat) (hp : Nat.Prime p) (n z n' z' : Int) (k : Nat)
    (a : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k)
    (a_1 : @LE.le.{0} Nat instLENat k (D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.horizon p)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.signature Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.actual
    PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat (fun (_p : Nat) => @Sigma.{0, 0} Int fun (_z : Int) => Nat) p
      (@Sigma.mk.{0, 0} Int (fun (_z : Int) => Nat) z k))
    n

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimeGcdHorizon\",\"sharp_prime_gcd_horizon\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"function\",\"argument\",\"body\",\"body\",\"body\",\"body\",\"domain\",\"body\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimeGcdHorizon\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon, declaration := `D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.sharp_prime_gcd_horizon, part := .type, path := [.body, .body, .function, .argument, .body, .body, .body, .body, .domain, .body, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimeGcdHorizon\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimeGcdHorizon\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimeGcdHorizon\",\"sharp_prime_gcd_horizon\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon, declaration := `D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.sharp_prime_gcd_horizon, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration).actual (Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration).variation.2.choose (Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration).variation.1 (Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimeGcdHorizon\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimeGcdHorizon\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimeGcdHorizon.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
