import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon
open _root_.D5.S3.Arith.FibonacciAtomic.TimeSampling
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon

abbrev signature : Signature where
  Params := Σ _p : ℕ, ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ parameters value => Nat.gcd value (parameters.1 ^ parameters.2))
    (fun anchor => nomatch anchor)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun anchor => nomatch anchor)

abbrev arena : Arena where
  signature := signature
  Law observation := ∀ (p e : ℕ) (hp : p.Prime) (he : 2 ≤ e),
    (∀ j : ℕ, 0 < zeroRank (p ^ j) ∧ p ^ j ∣ Nat.fib (zeroRank (p ^ j)) ∧
      ∀ k : ℕ, 0 < k → p ^ j ∣ Nat.fib k → zeroRank (p ^ j) ≤ k) ∧
    (zeroRank (p ^ e) = zeroRank (p ^ (e - 1)) ∨
      zeroRank (p ^ e) = p * zeroRank (p ^ (e - 1))) ∧
    (∀ n z n2 z2 : ℤ,
      (∀ k : ℕ, 1 ≤ k → k ≤ horizon p e →
        Nat.gcd (signedObservation n z k).natAbs (p ^ e) =
          Nat.gcd (signedObservation n2 z2 k).natAbs (p ^ e)) →
      ∀ k : ℕ, 1 ≤ k →
        Nat.gcd (signedObservation n z k).natAbs (p ^ e) =
          Nat.gcd (signedObservation n2 z2 k).natAbs (p ^ e)) ∧
    (∀ a b a2 b2 : ℕ,
      (∀ k : ℕ, 1 ≤ k → k ≤ horizon p e →
        Nat.gcd (sourceObservation a b k) (p ^ e) =
          Nat.gcd (sourceObservation a2 b2 k) (p ^ e)) →
      ∀ k : ℕ, 1 ≤ k →
        Nat.gcd (sourceObservation a b k) (p ^ e) =
          Nat.gcd (sourceObservation a2 b2 k) (p ^ e)) ∧
    (∃ a b a2 b2 : ℕ, a < p ^ e ∧ b < p ^ e ∧ a2 < p ^ e ∧ b2 < p ^ e ∧
      (∀ k : ℕ, 1 ≤ k → k < horizon p e →
        Nat.gcd (sourceObservation a b k) (p ^ e) =
          Nat.gcd (sourceObservation a2 b2 k) (p ^ e)) ∧
      Nat.gcd (sourceObservation a b (horizon p e)) (p ^ e) = p ^ e ∧
      observation.readout () ⟨p, e⟩ (sourceObservation a2 b2 (horizon p e)) = p ^ (e - 1))

theorem actual_law : arena.Law actual := sharp_prime_power_gcd_horizon

theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨a, b, a2, b2, aBound, bBound, a2Bound, b2Bound, agreement,
    terminal, terminal2⟩ := (law 2 2 Nat.prime_two le_rfl).2.2.2.2
  change 0 = 2 ^ (2 - 1) at terminal2
  norm_num at terminal2

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun role => ⟨rejected,
    fun other different => (different (Subsingleton.elim other role)).elim,
    rfl, rejected_law⟩, fun anchor => nomatch anchor⟩
  dependence := by
    intro role
    refine ⟨⟨2, 2⟩, 0, 1, ?_⟩
    change Nat.gcd 0 (2 ^ 2) ≠ Nat.gcd 1 (2 ^ 2)
    norm_num

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.sharp_prime_power_gcd_horizon) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ parameters value => Nat.gcd value (parameters.1 ^ parameters.2))
    (fun anchor => nomatch anchor))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "FibonacciAtomic") "PrimePowerGcdHorizon") "sharp_prime_power_gcd_horizon") "Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon/Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration,
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
    (fun _ parameters value => Nat.gcd value (parameters.1 ^ parameters.2))
    (fun anchor => nomatch anchor)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon, definition := none, coordinates := #[0, 1], readouts := #[{ path := #["body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon, declaration := `D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.sharp_prime_power_gcd_horizon, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration_1.observationFact0, `Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.arena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimePowerGcdHorizon\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimePowerGcdHorizon\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.arena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimePowerGcdHorizon\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimePowerGcdHorizon\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.arena
      Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.actual)
    Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration)

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimePowerGcdHorizon\",\"sharp_prime_power_gcd_horizon\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimePowerGcdHorizon\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon, declaration := `D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.sharp_prime_power_gcd_horizon, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.arena
    Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.actual)
  Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration)

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration_1.observation0 : (p e : Nat) →
  (hp : Nat.Prime p) →
    (he : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) e) →
      (a b a2 b2 : Nat) →
        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
          Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.signature PUnit.unit.{1}
          (@Sigma.mk.{0, 0} Nat (fun (_p : Nat) => Nat) p e) :=
  fun (p e : Nat) (hp : Nat.Prime p)
    (he : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) e) (a b a2 b2 : Nat) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.signature
    Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat (fun (_p : Nat) => Nat) p e)
    (D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.sourceObservation a2 b2
      (D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.horizon p e))

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimePowerGcdHorizon\",\"sharp_prime_power_gcd_horizon\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimePowerGcdHorizon\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon, declaration := `D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.sharp_prime_power_gcd_horizon, part := .type, path := [.body, .body, .body, .body, .argument, .argument, .argument, .argument, .argument, .body, .argument, .body, .argument, .body, .argument, .body, .argument, .argument, .argument, .argument, .argument, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimePowerGcdHorizon\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimePowerGcdHorizon\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimePowerGcdHorizon\",\"sharp_prime_power_gcd_horizon\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon, declaration := `D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.sharp_prime_power_gcd_horizon, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration).actual (Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration).variation.2.choose (Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration).variation.1 (Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimePowerGcdHorizon\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"PrimePowerGcdHorizon\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.PrimePowerGcdHorizon.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
