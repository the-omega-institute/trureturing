import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue
import Reg.Support.DependentFamily

set_option autoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue
open _root_.D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd
open _root_.D5.S3.Arith.ZeckendorfFutureKernel (value)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue

noncomputable section

abbrev responseSignature : Signature where
  Params := Σ _H : Nat, List Window
  State _ := ActualPrefix
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def responseActual : Realization responseSignature :=
  realize responseSignature (fun _ params source => rawIndex params.1 source params.2)
    (fun e => nomatch e)

def responseRejected : Realization responseSignature :=
  realize responseSignature (fun _ _ _ => none) (fun e => nomatch e)

abbrev responseArena : Arena where
  signature := responseSignature
  Law R := ∀ H p a L : Nat, 2 ≤ H → p.Prime → 1 ≤ a → H.factorization p = a →
    1 ≤ L → envelope L + 1 < p ^ a - p ^ a / p →
    ∃ j : Nat, ∃ x y : ActualPrefix,
      x.past.length = j ∧ y.past.length = j ∧ nextRow x = nextRow y ∧
      ((nextRow x).1 : ZMod H) = Int.fib (-3 * (L / 2 : Nat)) ∧
      ((nextRow x).2 : ZMod H) = Int.fib (-3 * (L / 2 : Nat) + 1) ∧
      0 < sourceNumber x ∧ 0 < sourceNumber y ∧
      (∀ w : List Window, w.length ≤ L → R.readout () ⟨H,w⟩ x = R.readout () ⟨H,w⟩ y) ∧
      ¬ (∀ w : List Window, R.readout () ⟨H,w⟩ x = R.readout () ⟨H,w⟩ y)

theorem response_rejected_law : ¬ responseArena.Law responseRejected := by
  intro h
  have hfull : (7 : Nat).factorization 7 = 1 := Nat.Prime.factorization_self (by decide)
  have hsmall : envelope 1 + 1 < 7 ^ 1 - 7 ^ 1 / 7 := by norm_num [envelope]
  obtain ⟨j, x, y, _, _, _, _, _, _, _, _, impossible⟩ :=
    h 7 7 1 1 (by decide) (by decide) (by decide) hfull (by decide) hsmall
  exact impossible (fun _ => rfl)

def responseRegistration : Registration responseArena (responseArena.Law responseActual) where
  actual := responseActual
  bridge := Iff.rfl
  variation := ⟨result, responseRejected, response_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨responseRejected, ?_, rfl, response_rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    exact ⟨⟨5, []⟩, ⟨true, [], rfl⟩, ⟨false, [.high], rfl⟩, by decide⟩

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.result) (type_of% (realize.{0, 0, 0, 0, 0} responseSignature
    (fun _ params source => rawIndex params.1 source params.2) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "FibonacciAtomic") "BalancedPhaseMissingResidue") "result") "Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue/Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.responseArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.responseRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(responseArena)⟩,
  objectArena := .source ⟨(responseArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (responseArena) ⟨(responseRegistration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} responseSignature
    (fun _ params source => rawIndex params.1 source params.2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue, definition := none, coordinates := #[0, 13], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue, declaration := `D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.registration_1.observationFact0, `Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.registration_1.anchorEnumeration }


#print axioms responseRegistration

end

end Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.responseArena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BalancedPhaseMissingResidue\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BalancedPhaseMissingResidue\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.responseArena
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BalancedPhaseMissingResidue\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BalancedPhaseMissingResidue\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.responseArena) (Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.responseRegistration).actual

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BalancedPhaseMissingResidue\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BalancedPhaseMissingResidue\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue, declaration := `D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.responseRegistration).bridge

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.registration_1.observation0 : (H p a L : Nat) →
  (hH : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) H) →
    (hp : Nat.Prime p) →
      (ha : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) a) →
        (hfull :
            @Eq.{1} Nat
              (@DFunLike.coe.{1, 1, 1} (@Finsupp.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) Nat
                (fun (x : Nat) => Nat)
                (@Finsupp.instFunLike.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                (Nat.factorization H) p)
              a) →
          (hL : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) L) →
            (hsmall :
                @LT.lt.{0} Nat instLTNat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.envelope L)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p a)
                    (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p a)
                      p))) →
              (j : Nat) →
                (x y : D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.ActualPrefix) →
                  (w : List.{0} D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window) →
                    @LE.le.{0} Nat instLENat (@List.length.{0} D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window w)
                        L →
                      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                        Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.responseSignature PUnit.unit.{1}
                        (@Sigma.mk.{0, 0} Nat
                          (fun (_H : Nat) => List.{0} D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window) H w) :=
  fun (H p a L : Nat) (hH : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) H)
    (hp : Nat.Prime p) (ha : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) a)
    (hfull :
      @Eq.{1} Nat
        (@DFunLike.coe.{1, 1, 1} (@Finsupp.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) Nat
          (fun (x : Nat) => Nat)
          (@Finsupp.instFunLike.{0, 0} Nat Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
          (Nat.factorization H) p)
        a)
    (hL : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) L)
    (hsmall :
      @LT.lt.{0} Nat instLTNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.envelope L)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p a)
          (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p a)
            p)))
    (j : Nat) (x y : D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion.ActualPrefix)
    (w : List.{0} D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window)
    (a_1 : @LE.le.{0} Nat instLENat (@List.length.{0} D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window w) L) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.responseSignature
    Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.responseActual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat (fun (_H : Nat) => List.{0} D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd.Window) H w) x

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BalancedPhaseMissingResidue\",\"result\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"function\",\"argument\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BalancedPhaseMissingResidue\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue, declaration := `D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.result, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .body, .argument, .body, .argument, .body, .argument, .argument, .argument, .argument, .argument, .argument, .argument, .function, .argument, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BalancedPhaseMissingResidue\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BalancedPhaseMissingResidue\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BalancedPhaseMissingResidue\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue, declaration := `D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.responseRegistration).actual (Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.responseRegistration).variation.2.choose (Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.responseRegistration).variation.1 (Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.responseRegistration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BalancedPhaseMissingResidue\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"FibonacciAtomic\",\"BalancedPhaseMissingResidue\",\"responseRegistration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue, declaration := `Reg.D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue.responseRegistration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
