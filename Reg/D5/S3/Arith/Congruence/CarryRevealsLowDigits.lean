import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Congruence.CarryRevealsLowDigits
import Reg.Support.DependentFamily

open _root_.D5.S3.Arith.Congruence.CarryRevealsLowDigits
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits

@[reducible] def signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p v => v % p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- The full original law; only the outer modulo in the bounded carry formula varies. -/
@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {p : ℕ} [hp : Fact p.Prime] (k : ℕ) (x y : ℤ_[p]),
    (∀ n, n ≤ p ^ k - 1 →
      highDigit k (x + ((n : ℕ) : ℤ_[p])) =
        R.readout () p ((PadicInt.toZModPow (k + 1) x).val / p ^ k +
          ((PadicInt.toZModPow (k + 1) x).val % p ^ k + n) / p ^ k)) ∧
    ((PadicInt.toZModPow (k + 1) x).val % p ^ k = 0 →
      ∀ n, 1 ≤ n → n ≤ p ^ k - 1 → highDigit k (x + ((n : ℕ) : ℤ_[p])) = highDigit k x) ∧
    (0 < (PadicInt.toZModPow (k + 1) x).val % p ^ k →
      highDigit k (x + ((p ^ k - (PadicInt.toZModPow (k + 1) x).val % p ^ k : ℕ) : ℤ_[p])) ≠
          highDigit k x ∧
        ∀ n, 1 ≤ n → n < p ^ k - (PadicInt.toZModPow (k + 1) x).val % p ^ k →
          highDigit k (x + ((n : ℕ) : ℤ_[p])) = highDigit k x) ∧
    (digitProtocol k (p ^ k - 1) x = digitProtocol k (p ^ k - 1) y ↔
      PadicInt.toZModPow (k + 1) x = PadicInt.toZModPow (k + 1) y) ∧
    ∀ N, 1 ≤ k → N < p ^ k - 1 →
      digitProtocol k N (0 : ℤ_[p]) = digitProtocol k N (1 : ℤ_[p]) ∧
        PadicInt.toZModPow (k + 1) (0 : ℤ_[p]) ≠ PadicInt.toZModPow (k + 1) (1 : ℤ_[p])

theorem actual_law : arena.Law actual := by
  exact carry_reveals_low_digits

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have impossible := (h (p := 2) 0 0 0).1 0 (by norm_num)
  norm_num [rejected, realize, highDigit] at impossible

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    exact ⟨2, 0, 1, by change (0 : ℕ) % 2 ≠ 1 % 2; norm_num⟩

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Congruence.CarryRevealsLowDigits.carry_reveals_low_digits) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ p v => v % p) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Congruence") "CarryRevealsLowDigits") "carry_reveals_low_digits") "Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits/Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ p v => v % p) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Congruence.CarryRevealsLowDigits, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg", "body", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.Congruence.CarryRevealsLowDigits, declaration := `D5.S3.Arith.Congruence.CarryRevealsLowDigits.carry_reveals_low_digits, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits, declaration := `Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits, declaration := `Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits, declaration := `Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits, declaration := `Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration_1.observationFact0, `Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits


noncomputable def Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.arena
noncomputable def Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Congruence\",\"CarryRevealsLowDigits\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Congruence\",\"CarryRevealsLowDigits\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits, declaration := `Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits, declaration := `Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.arena
noncomputable def Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Congruence\",\"CarryRevealsLowDigits\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Congruence\",\"CarryRevealsLowDigits\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits, declaration := `Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits, declaration := `Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.arena) (Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration).actual

noncomputable def Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Congruence\",\"CarryRevealsLowDigits\",\"carry_reveals_low_digits\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Congruence\",\"CarryRevealsLowDigits\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Congruence.CarryRevealsLowDigits, declaration := `D5.S3.Arith.Congruence.CarryRevealsLowDigits.carry_reveals_low_digits, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits, declaration := `Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration).bridge

noncomputable def Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration_1.observation0 : {p : Nat} →
  [hp : Fact (Nat.Prime p)] →
    (k : Nat) →
      (x y : @PadicInt p hp) →
        (n : Nat) →
          @LE.le.{0} Nat instLENat n
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p k)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.signature PUnit.unit.{1} p :=
  fun {p : Nat} [hp : Fact (Nat.Prime p)] (k : Nat) (x y : @PadicInt p hp) (n : Nat)
    (a :
      @LE.le.{0} Nat instLENat n
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p k)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.signature Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.actual
    PUnit.unit.{1} p
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
        (@ZMod.val
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@DFunLike.coe.{1, 1, 1}
            (@RingHom.{0, 0} (@PadicInt p hp)
              (ZMod
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (@Semiring.toNonAssocSemiring.{0} (@PadicInt p hp)
                (@CommSemiring.toSemiring.{0} (@PadicInt p hp)
                  (@CommRing.toCommSemiring.{0} (@PadicInt p hp) (@PadicInt.instCommRing p hp))))
              (@Semiring.toNonAssocSemiring.{0}
                (ZMod
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (@CommSemiring.toSemiring.{0}
                  (ZMod
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (@CommRing.toCommSemiring.{0}
                    (ZMod
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    (ZMod.commRing
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))
            (@PadicInt p hp)
            (fun (x : @PadicInt p hp) =>
              ZMod
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (@RingHom.instFunLike.{0, 0} (@PadicInt p hp)
              (ZMod
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
              (@Semiring.toNonAssocSemiring.{0} (@PadicInt p hp)
                (@CommSemiring.toSemiring.{0} (@PadicInt p hp)
                  (@CommRing.toCommSemiring.{0} (@PadicInt p hp) (@PadicInt.instCommRing p hp))))
              (@Semiring.toNonAssocSemiring.{0}
                (ZMod
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (@CommSemiring.toSemiring.{0}
                  (ZMod
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (@CommRing.toCommSemiring.{0}
                    (ZMod
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    (ZMod.commRing
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))
            (@PadicInt.toZModPow p hp
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            x))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p k))
      (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod)
            (@ZMod.val
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@DFunLike.coe.{1, 1, 1}
                (@RingHom.{0, 0} (@PadicInt p hp)
                  (ZMod
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (@Semiring.toNonAssocSemiring.{0} (@PadicInt p hp)
                    (@CommSemiring.toSemiring.{0} (@PadicInt p hp)
                      (@CommRing.toCommSemiring.{0} (@PadicInt p hp) (@PadicInt.instCommRing p hp))))
                  (@Semiring.toNonAssocSemiring.{0}
                    (ZMod
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    (@CommSemiring.toSemiring.{0}
                      (ZMod
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                      (@CommRing.toCommSemiring.{0}
                        (ZMod
                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                        (ZMod.commRing
                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))
                (@PadicInt p hp)
                (fun (x : @PadicInt p hp) =>
                  ZMod
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (@RingHom.instFunLike.{0, 0} (@PadicInt p hp)
                  (ZMod
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (@Semiring.toNonAssocSemiring.{0} (@PadicInt p hp)
                    (@CommSemiring.toSemiring.{0} (@PadicInt p hp)
                      (@CommRing.toCommSemiring.{0} (@PadicInt p hp) (@PadicInt.instCommRing p hp))))
                  (@Semiring.toNonAssocSemiring.{0}
                    (ZMod
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    (@CommSemiring.toSemiring.{0}
                      (ZMod
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                      (@CommRing.toCommSemiring.{0}
                        (ZMod
                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                        (ZMod.commRing
                          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))
                (@PadicInt.toZModPow p hp
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                x))
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p k))
          n)
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p k)))

noncomputable def Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Congruence\",\"CarryRevealsLowDigits\",\"carry_reveals_low_digits\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"body\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Congruence\",\"CarryRevealsLowDigits\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Congruence.CarryRevealsLowDigits, declaration := `D5.S3.Arith.Congruence.CarryRevealsLowDigits.carry_reveals_low_digits, part := .type, path := [.body, .body, .body, .body, .body, .function, .argument, .body, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits, declaration := `Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Congruence\",\"CarryRevealsLowDigits\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Congruence\",\"CarryRevealsLowDigits\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Congruence\",\"CarryRevealsLowDigits\",\"carry_reveals_low_digits\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits, declaration := `Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.Congruence.CarryRevealsLowDigits, declaration := `D5.S3.Arith.Congruence.CarryRevealsLowDigits.carry_reveals_low_digits, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration).actual (Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration).variation.2.choose (Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration).variation.1 (Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Congruence\",\"CarryRevealsLowDigits\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Congruence\",\"CarryRevealsLowDigits\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits, declaration := `Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits, declaration := `Reg.D5.S3.Arith.Congruence.CarryRevealsLowDigits.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
