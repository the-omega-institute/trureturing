import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods

open scoped Matrix
open _root_.D5.S1.Scale
open _root_.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ p b =>
      let C := (goldenLucas (3 ^ p.1) ^ 2 + 1).natAbs
      let B := (goldenLucas (3 ^ p.1) ^ 2 + 3).natAbs
      4 * 3 ^ (p.1 + 1) * C ^ (p.2 - 1) * B ^ (b - 1))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature
    (fun _ p b =>
      let C := (goldenLucas (3 ^ p.1) ^ 2 + 1).natAbs
      let B := (goldenLucas (3 ^ p.1) ^ 2 + 3).natAbs
      4 * 3 ^ (p.1 + 1) * C ^ (p.2 - 1) * B ^ (b - 1) + 1)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r :=
    let C := fun j : ℕ => (goldenLucas (3 ^ j) ^ 2 + 1).natAbs
    let B := fun j : ℕ => (goldenLucas (3 ^ j) ^ 2 + 3).natAbs
    let π := fun m : ℕ => orderOf
      (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod m))
    (∀ i j : ℕ, 1 ≤ i → 1 ≤ j → i ≠ j → (C i).Coprime (C j)) ∧
    (∀ i j : ℕ, 1 ≤ i → 1 ≤ j → i ≠ j → (B i).Coprime (B j)) ∧
    (∀ i j : ℕ, 1 ≤ i → 1 ≤ j → (C i).Coprime (B j)) ∧
    (∀ j a b : ℕ, 1 ≤ j → 1 ≤ a → 1 ≤ b →
      π (C j ^ a) = 4 * 3 ^ (j + 1) * C j ^ (a - 1) ∧
      π (B j ^ b) = 2 * 3 ^ (j + 1) * B j ^ (b - 1) ∧
      π (C j ^ a * B j ^ b) = r.readout () ⟨j, a⟩ b)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hgood := (cubic_block_native_power_periods).2.2.2
    1 1 1 (by decide) (by decide) (by decide)
  have hbad := (h.2.2.2 1 1 1 (by decide) (by decide) (by decide))
  have hcontradiction := hgood.2.2.symm.trans hbad.2.2
  change 4 * 3 ^ (1 + 1) *
      (goldenLucas (3 ^ 1) ^ 2 + 1).natAbs ^ (1 - 1) *
      (goldenLucas (3 ^ 1) ^ 2 + 3).natAbs ^ (1 - 1) =
    4 * 3 ^ (1 + 1) *
      (goldenLucas (3 ^ 1) ^ 2 + 1).natAbs ^ (1 - 1) *
      (goldenLucas (3 ^ 1) ^ 2 + 3).natAbs ^ (1 - 1) + 1 at hcontradiction
  omega

def registration : Registration arena
    (let C := fun j : ℕ => (goldenLucas (3 ^ j) ^ 2 + 1).natAbs
     let B := fun j : ℕ => (goldenLucas (3 ^ j) ^ 2 + 3).natAbs
     let π := fun m : ℕ => orderOf
       (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod m))
     (∀ i j : ℕ, 1 ≤ i → 1 ≤ j → i ≠ j → (C i).Coprime (C j)) ∧
     (∀ i j : ℕ, 1 ≤ i → 1 ≤ j → i ≠ j → (B i).Coprime (B j)) ∧
     (∀ i j : ℕ, 1 ≤ i → 1 ≤ j → (C i).Coprime (B j)) ∧
     (∀ j a b : ℕ, 1 ≤ j → 1 ≤ a → 1 ≤ b →
       π (C j ^ a) = 4 * 3 ^ (j + 1) * C j ^ (a - 1) ∧
       π (B j ^ b) = 2 * 3 ^ (j + 1) * B j ^ (b - 1) ∧
       π (C j ^ a * B j ^ b) =
         4 * 3 ^ (j + 1) * C j ^ (a - 1) * B j ^ (b - 1))) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cubic_block_native_power_periods, rejected, rejected_law⟩
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
    refine ⟨⟨1, 1⟩, 1, 2, ?_⟩
    change 4 * 3 ^ (1 + 1) *
        (goldenLucas (3 ^ 1) ^ 2 + 1).natAbs ^ (1 - 1) *
        (goldenLucas (3 ^ 1) ^ 2 + 3).natAbs ^ (1 - 1) ≠
      4 * 3 ^ (1 + 1) *
        (goldenLucas (3 ^ 1) ^ 2 + 1).natAbs ^ (1 - 1) *
        (goldenLucas (3 ^ 1) ^ 2 + 3).natAbs ^ (2 - 1)
    norm_num [goldenLucas, D5.S0.Carrier.trace, D5.S0.Carrier.phi, pow_succ]

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.cubic_block_native_power_periods) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ p b =>
      let C := (goldenLucas (3 ^ p.1) ^ 2 + 1).natAbs
      let B := (goldenLucas (3 ^ p.1) ^ 2 + 3).natAbs
      4 * 3 ^ (p.1 + 1) * C ^ (p.2 - 1) * B ^ (b - 1))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Primes") "GoldenCubicBlockNativePowerPeriods") "cubic_block_native_power_periods") "Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods/Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration,
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
    (fun _ p b =>
      let C := (goldenLucas (3 ^ p.1) ^ 2 + 1).natAbs
      let B := (goldenLucas (3 ^ p.1) ^ 2 + 3).natAbs
      4 * 3 ^ (p.1 + 1) * C ^ (p.2 - 1) * B ^ (b - 1))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods, definition := none, coordinates := #[3, 4], readouts := #[{ path := #["body", "body", "body", "arg", "arg", "arg", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods, declaration := `D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.cubic_block_native_power_periods, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration_1.observationFact0, `Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration_1.anchorEnumeration }


end
end Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods


noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.arena
noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockNativePowerPeriods\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockNativePowerPeriods\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.arena
noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockNativePowerPeriods\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockNativePowerPeriods\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.arena) (Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration).actual

noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockNativePowerPeriods\",\"cubic_block_native_power_periods\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockNativePowerPeriods\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods, declaration := `D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.cubic_block_native_power_periods, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration).bridge

noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration_1.observation0 : (j a b : Nat) →
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) a →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) b →
        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
          Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.signature PUnit.unit.{1}
          (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => Nat) j a) :=
  have C : (j : Nat) → Nat := fun (j : Nat) =>
  Int.natAbs
    (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
      (@HPow.hPow.{0, 0, 0} Int Nat Int
        (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
        (D5.S1.Scale.goldenLucas
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))));
have B : (j : Nat) → Nat := fun (j : Nat) =>
  Int.natAbs
    (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
      (@HPow.hPow.{0, 0, 0} Int Nat Int
        (@instHPow.{0, 0} Int Nat (@NPow.toPow.{0} Int (@Monoid.toNPow.{0} Int Int.instMonoid)))
        (D5.S1.Scale.goldenLucas
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@OfNat.ofNat.{0} Int (nat_lit 3) (@instOfNat (nat_lit 3))));
have π : (m : Nat) → Nat := fun (m : Nat) =>
  @orderOf.{0}
    (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod m))
    (@Semiring.toMonoid.{0}
      (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod m))
      (@Matrix.semiring.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod m)
        (@CommSemiring.toSemiring.{0} (ZMod m) (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))
        (Fin.fintype (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (@DFunLike.coe.{1, 1, 1}
      (Equiv.{1, 1}
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
          Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod m)
        (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod m)))
      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
        Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod m)
      (fun
          (x :
            Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
              Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod m) =>
        Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod m))
      (@EquivLike.toFunLike.{1, 1, 1}
        (Equiv.{1, 1}
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
            Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod m)
          (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod m)))
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
          Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod m)
        (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod m))
        (@Equiv.instEquivLike.{1, 1}
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
            Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod m)
          (Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod m))))
      (@Matrix.of.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (ZMod m))
      (@Matrix.vecCons.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod m)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@Matrix.vecCons.{0} (ZMod m) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@OfNat.ofNat.{0} (ZMod m) (nat_lit 1)
            (@One.toOfNat1.{0} (ZMod m)
              (@AddMonoidWithOne.toOne.{0} (ZMod m)
                (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod m)
                  (@Ring.toAddGroupWithOne.{0} (ZMod m) (@CommRing.toRing.{0} (ZMod m) (ZMod.commRing m)))))))
          (@Matrix.vecCons.{0} (ZMod m) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@OfNat.ofNat.{0} (ZMod m) (nat_lit 1)
              (@One.toOfNat1.{0} (ZMod m)
                (@AddMonoidWithOne.toOne.{0} (ZMod m)
                  (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod m)
                    (@Ring.toAddGroupWithOne.{0} (ZMod m) (@CommRing.toRing.{0} (ZMod m) (ZMod.commRing m)))))))
            (@Matrix.vecEmpty.{0} (ZMod m))))
        (@Matrix.vecCons.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod m)
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@Matrix.vecCons.{0} (ZMod m) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@OfNat.ofNat.{0} (ZMod m) (nat_lit 1)
              (@One.toOfNat1.{0} (ZMod m)
                (@AddMonoidWithOne.toOne.{0} (ZMod m)
                  (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod m)
                    (@Ring.toAddGroupWithOne.{0} (ZMod m) (@CommRing.toRing.{0} (ZMod m) (ZMod.commRing m)))))))
            (@Matrix.vecCons.{0} (ZMod m) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@OfNat.ofNat.{0} (ZMod m) (nat_lit 0)
                (@Zero.toOfNat0.{0} (ZMod m)
                  (@MulZeroClass.toZero.{0} (ZMod m)
                    (@instMulZeroClassOfSemiring.{0} (ZMod m)
                      (@CommSemiring.toSemiring.{0} (ZMod m)
                        (@CommRing.toCommSemiring.{0} (ZMod m) (ZMod.commRing m)))))))
              (@Matrix.vecEmpty.{0} (ZMod m))))
          (@Matrix.vecEmpty.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → ZMod m)))));
fun (j a b : Nat) (a_1 : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) j)
  (a_2 : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) a)
  (a_3 : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) b) =>
@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.signature
  Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.actual PUnit.unit.{1}
  (@Sigma.mk.{0, 0} Nat (fun (x : Nat) => Nat) j a) b

noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockNativePowerPeriods\",\"cubic_block_native_power_periods\"],\"part\":\"type\",\"path\":[\"letBody\",\"letBody\",\"letBody\",\"argument\",\"argument\",\"argument\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockNativePowerPeriods\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods, declaration := `D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.cubic_block_native_power_periods, part := .type, path := [.letBody, .letBody, .letBody, .argument, .argument, .argument, .body, .body, .body, .body, .body, .body, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockNativePowerPeriods\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockNativePowerPeriods\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockNativePowerPeriods\",\"cubic_block_native_power_periods\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods, declaration := `D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.cubic_block_native_power_periods, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration).actual (Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration).variation.2.choose (Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration).variation.1 (Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockNativePowerPeriods\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"GoldenCubicBlockNativePowerPeriods\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods, declaration := `Reg.D5.S3.Arith.Primes.GoldenCubicBlockNativePowerPeriods.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
