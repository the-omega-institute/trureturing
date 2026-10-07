import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate

open _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State := fun _ => EisensteinOrder
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => EisensteinOrder
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : EisensteinOrder)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (z : EisensteinOrder)
      (hz : ((QuadraticAlgebra.norm z : ℤ) : ZMod 3) = 1),
    ∃ u : EisensteinOrder, IsUnit u ∧ QuadraticAlgebra.norm u = 1 ∧
      (3 : EisensteinOrder) ∣ u * R.readout () () z - 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨u, _, _, hdiv⟩ := h 1 (by
    norm_num [QuadraticAlgebra.norm_def, QuadraticAlgebra.re_one,
      QuadraticAlgebra.im_one])
  have hdiv' : (3 : EisensteinOrder) ∣ (-1 : EisensteinOrder) := by
    simpa [rejected, realize] using hdiv
  have hcoord : (3 : ℤ) ∣ (-1 : ℤ) :=
    (QuadraticAlgebra.algebraMap_dvd_iff.mp hdiv').1
  norm_num at hcoord

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨?_, rejected, rejected_law⟩
    intro z hz
    exact exists_primary_associate z hz
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
    change ∃ (_ : Unit) (x y : EisensteinOrder), x ≠ y
    exact ⟨(), 0, 1, zero_ne_one⟩

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.exists_primary_associate) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ z => z) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Factorization") "QuadraticIdeals") "EisensteinPrimaryAssociate") "exists_primary_associate") "Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate/Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ z => z) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "arg", "body", "arg", "arg", "arg", "fn", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate, declaration := `D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.exists_primary_associate, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration_1.canonicalArenaFact, `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration_1.sourceBridgeFact, `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration_1.observationFact0, `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration_1.anchorEnumeration }


#print axioms registration

end

end Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate


noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.arena
noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinPrimaryAssociate\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinPrimaryAssociate\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.arena
noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinPrimaryAssociate\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinPrimaryAssociate\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.arena
      Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.actual)
    Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration)

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinPrimaryAssociate\",\"exists_primary_associate\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinPrimaryAssociate\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate, declaration := `D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.exists_primary_associate, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.arena
    Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.actual)
  Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration)

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration_1.observation0 : (z : D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.EisensteinOrder) →
  (hz :
      @Eq.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@Int.cast.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@AddGroupWithOne.toIntCast.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (@DivisionRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (@Field.toDivisionRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                    Nat.fact_prime_three)))))
          (@DFunLike.coe.{1, 1, 1}
            (@MonoidHom.{0, 0}
              (QuadraticAlgebra.{0} Int
                (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
              Int
              (@MulOneClass.toMulOne.{0}
                (QuadraticAlgebra.{0} Int
                  (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                  (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                (@MulZeroOneClass.toMulOneClass.{0}
                  (QuadraticAlgebra.{0} Int
                    (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                  (@instMulZeroOneClassOfSemiring.{0}
                    (QuadraticAlgebra.{0} Int
                      (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                      (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                    (@CommSemiring.toSemiring.{0}
                      (QuadraticAlgebra.{0} Int
                        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                      (@QuadraticAlgebra.instCommSemiring.{0} Int
                        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@CommRing.toCommSemiring.{0} Int Int.instCommRing))))))
              (@MulOneClass.toMulOne.{0} Int
                (@MulZeroOneClass.toMulOneClass.{0} Int
                  (@instMulZeroOneClassOfSemiring.{0} Int
                    (@CommSemiring.toSemiring.{0} Int (@CommRing.toCommSemiring.{0} Int Int.instCommRing))))))
            (QuadraticAlgebra.{0} Int
              (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
              (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
            (fun
                (x :
                  QuadraticAlgebra.{0} Int
                    (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))) =>
              Int)
            (@MonoidHom.instFunLike.{0, 0}
              (QuadraticAlgebra.{0} Int
                (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
              Int
              (@MulOneClass.toMulOne.{0}
                (QuadraticAlgebra.{0} Int
                  (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                  (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                (@MulZeroOneClass.toMulOneClass.{0}
                  (QuadraticAlgebra.{0} Int
                    (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                  (@instMulZeroOneClassOfSemiring.{0}
                    (QuadraticAlgebra.{0} Int
                      (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                      (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                    (@CommSemiring.toSemiring.{0}
                      (QuadraticAlgebra.{0} Int
                        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                      (@QuadraticAlgebra.instCommSemiring.{0} Int
                        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@CommRing.toCommSemiring.{0} Int Int.instCommRing))))))
              (@MulOneClass.toMulOne.{0} Int
                (@MulZeroOneClass.toMulOneClass.{0} Int
                  (@instMulZeroOneClassOfSemiring.{0} Int
                    (@CommSemiring.toSemiring.{0} Int (@CommRing.toCommSemiring.{0} Int Int.instCommRing))))))
            (@QuadraticAlgebra.norm.{0} Int
              (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
              (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
              Int.instCommRing)
            z))
        (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 1)
          (@One.toOfNat1.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (@AddMonoidWithOne.toOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (@AddGroupWithOne.toAddMonoidWithOne.{0}
                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (@DivisionRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (@Field.toDivisionRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                        Nat.fact_prime_three))))))))) →
    (u : D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.EisensteinOrder) →
      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
        Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (z : D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.EisensteinOrder)
    (hz :
      @Eq.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@Int.cast.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@AddGroupWithOne.toIntCast.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (@DivisionRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (@Field.toDivisionRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                    Nat.fact_prime_three)))))
          (@DFunLike.coe.{1, 1, 1}
            (@MonoidHom.{0, 0}
              (QuadraticAlgebra.{0} Int
                (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
              Int
              (@MulOneClass.toMulOne.{0}
                (QuadraticAlgebra.{0} Int
                  (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                  (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                (@MulZeroOneClass.toMulOneClass.{0}
                  (QuadraticAlgebra.{0} Int
                    (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                  (@instMulZeroOneClassOfSemiring.{0}
                    (QuadraticAlgebra.{0} Int
                      (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                      (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                    (@CommSemiring.toSemiring.{0}
                      (QuadraticAlgebra.{0} Int
                        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                      (@QuadraticAlgebra.instCommSemiring.{0} Int
                        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@CommRing.toCommSemiring.{0} Int Int.instCommRing))))))
              (@MulOneClass.toMulOne.{0} Int
                (@MulZeroOneClass.toMulOneClass.{0} Int
                  (@instMulZeroOneClassOfSemiring.{0} Int
                    (@CommSemiring.toSemiring.{0} Int (@CommRing.toCommSemiring.{0} Int Int.instCommRing))))))
            (QuadraticAlgebra.{0} Int
              (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
              (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
            (fun
                (x :
                  QuadraticAlgebra.{0} Int
                    (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))) =>
              Int)
            (@MonoidHom.instFunLike.{0, 0}
              (QuadraticAlgebra.{0} Int
                (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
              Int
              (@MulOneClass.toMulOne.{0}
                (QuadraticAlgebra.{0} Int
                  (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                  (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                (@MulZeroOneClass.toMulOneClass.{0}
                  (QuadraticAlgebra.{0} Int
                    (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                    (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                  (@instMulZeroOneClassOfSemiring.{0}
                    (QuadraticAlgebra.{0} Int
                      (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                      (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                    (@CommSemiring.toSemiring.{0}
                      (QuadraticAlgebra.{0} Int
                        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
                      (@QuadraticAlgebra.instCommSemiring.{0} Int
                        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                        (@CommRing.toCommSemiring.{0} Int Int.instCommRing))))))
              (@MulOneClass.toMulOne.{0} Int
                (@MulZeroOneClass.toMulOneClass.{0} Int
                  (@instMulZeroOneClassOfSemiring.{0} Int
                    (@CommSemiring.toSemiring.{0} Int (@CommRing.toCommSemiring.{0} Int Int.instCommRing))))))
            (@QuadraticAlgebra.norm.{0} Int
              (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
              (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
              Int.instCommRing)
            z))
        (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 1)
          (@One.toOfNat1.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (@AddMonoidWithOne.toOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (@AddGroupWithOne.toAddMonoidWithOne.{0}
                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (@DivisionRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (@Field.toDivisionRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                        Nat.fact_prime_three)))))))))
    (u : D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.EisensteinOrder) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.signature
    Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.actual PUnit.unit.{1} PUnit.unit.{1} z

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinPrimaryAssociate\",\"exists_primary_associate\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"argument\",\"body\",\"argument\",\"argument\",\"argument\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinPrimaryAssociate\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate, declaration := `D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.exists_primary_associate, part := .type, path := [.body, .body, .argument, .body, .argument, .argument, .argument, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinPrimaryAssociate\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinPrimaryAssociate\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinPrimaryAssociate\",\"exists_primary_associate\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate, declaration := `D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.exists_primary_associate, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration).actual (Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration).variation.2.choose (Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration).variation.1 (Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinPrimaryAssociate\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinPrimaryAssociate\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinPrimaryAssociate.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
