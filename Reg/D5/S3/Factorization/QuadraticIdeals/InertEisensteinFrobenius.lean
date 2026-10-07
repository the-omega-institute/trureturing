import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius

open _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open _root_.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

def signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def quotientCard (ell : ℕ) : ℕ :=
  Nat.card (EisensteinOrder ⧸ Ideal.span {(ell : EisensteinOrder)})

def actual : Realization signature :=
  realize signature (fun _ _ ell => quotientCard ell) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℕ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (ell : ℕ) [Fact ell.Prime] (_hell3 : ell % 3 = 2),
    let I : Ideal EisensteinOrder := Ideal.span {(ell : EisensteinOrder)}
    I.IsMaximal ∧ R.readout () () ell = ell ^ 2 ∧
      CharP (EisensteinOrder ⧸ I) ell ∧
      ∃ e : EisensteinOrder ⧸ I ≃+* QuadraticAlgebra (ZMod ell) (-1) (-1),
        (∀ z : EisensteinOrder,
          (e (Ideal.Quotient.mk I z)).re = (z.re : ZMod ell) ∧
          (e (Ideal.Quotient.mk I z)).im = (z.im : ZMod ell)) ∧
        ∀ z : EisensteinOrder,
          (Ideal.Quotient.mk I z) ^ ell = Ideal.Quotient.mk I (star z)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard := (h 2 (by decide)).2.1
  change (0 : ℕ) = 2 ^ 2 at hcard
  norm_num at hcard

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨?_, rejected, rejected_law⟩
    intro ell _ hell3
    exact inert_eisenstein_quotient_frobenius ell hell3
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
    change ∃ (_ : Unit) (x y : ℕ), quotientCard x ≠ quotientCard y
    refine ⟨(), 2, 5, ?_⟩
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
    have htwo : quotientCard 2 = 2 ^ 2 :=
      (inert_eisenstein_quotient_frobenius 2 (by decide)).2.1
    have hfive : quotientCard 5 = 5 ^ 2 :=
      (inert_eisenstein_quotient_frobenius 5 (by decide)).2.1
    intro h
    have hcontr : (2 : ℕ) ^ 2 = 5 ^ 2 := htwo.symm.trans (h.trans hfive)
    norm_num at hcontr

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.inert_eisenstein_quotient_frobenius) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ ell => quotientCard ell) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Factorization") "QuadraticIdeals") "InertEisensteinFrobenius") "inert_eisenstein_quotient_frobenius") "Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius/Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ ell => quotientCard ell) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius, declaration := `D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.inert_eisenstein_quotient_frobenius, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration_1.canonicalArenaFact, `Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration_1.sourceBridgeFact, `Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration_1.observationFact0, `Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration_1.anchorEnumeration }


#print axioms registration

end

end Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius


noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.arena
noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"InertEisensteinFrobenius\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"InertEisensteinFrobenius\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.arena
noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"InertEisensteinFrobenius\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"InertEisensteinFrobenius\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.arena) (Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration).actual

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"InertEisensteinFrobenius\",\"inert_eisenstein_quotient_frobenius\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"InertEisensteinFrobenius\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius, declaration := `D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.inert_eisenstein_quotient_frobenius, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration).bridge

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration_1.observation0 : (ell : Nat) →
  [Fact (Nat.Prime ell)] →
    (hell3 :
        @Eq.{1} Nat
          (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) ell
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
        Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (ell : Nat) [Fact (Nat.Prime ell)]
    (hell3 :
      @Eq.{1} Nat
        (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) ell
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) =>
  have I :
    @Ideal.{0} D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.EisensteinOrder
      (@CommSemiring.toSemiring.{0} D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.EisensteinOrder
        (@QuadraticAlgebra.instCommSemiring.{0} Int
          (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          Int.instCommSemiring)) :=
    @Ideal.span.{0} D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.EisensteinOrder
      (@CommSemiring.toSemiring.{0} D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.EisensteinOrder
        (@QuadraticAlgebra.instCommSemiring.{0} Int
          (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          Int.instCommSemiring))
      (@Singleton.singleton.{0, 0} D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.EisensteinOrder
        (Set.{0} D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.EisensteinOrder)
        (@Set.instSingletonSet.{0} D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.EisensteinOrder)
        (@Nat.cast.{0} D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.EisensteinOrder
          (@AddMonoidWithOne.toNatCast.{0} D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.EisensteinOrder
            (@AddGroupWithOne.toAddMonoidWithOne.{0}
              D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.EisensteinOrder
              (@Ring.toAddGroupWithOne.{0} D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.EisensteinOrder
                (@CommRing.toRing.{0} D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.EisensteinOrder
                  (@QuadraticAlgebra.instCommRing.{0} Int
                    (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    Int.instCommRing)))))
          ell));
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.signature
    Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.actual PUnit.unit.{1} PUnit.unit.{1} ell

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"InertEisensteinFrobenius\",\"inert_eisenstein_quotient_frobenius\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"letBody\",\"argument\",\"function\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"InertEisensteinFrobenius\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius, declaration := `D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.inert_eisenstein_quotient_frobenius, part := .type, path := [.body, .body, .body, .letBody, .argument, .function, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"InertEisensteinFrobenius\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"InertEisensteinFrobenius\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"InertEisensteinFrobenius\",\"inert_eisenstein_quotient_frobenius\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius, declaration := `D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.inert_eisenstein_quotient_frobenius, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration).actual (Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration).variation.2.choose (Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration).variation.1 (Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"InertEisensteinFrobenius\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"InertEisensteinFrobenius\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.InertEisensteinFrobenius.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
