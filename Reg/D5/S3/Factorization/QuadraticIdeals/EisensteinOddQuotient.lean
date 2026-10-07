import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient

open _root_.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

def signature : Signature where
  Params := ℕ
  State := fun _ => ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ b => OrientedQuotient b
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ b n => scalarMap b n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ b _ => (0 : OrientedQuotient b)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (b : ℕ) (_hb : Odd b),
    (∀ n : ℤ, orientedFactor b ∣ (QuadraticAlgebra.C n : EisensteinOrder) ↔
      (blockNorm b : ℤ) ∣ n) ∧
    ∃ e : ZMod (blockNorm b) ≃+* OrientedQuotient b,
      ∀ n : ℤ, e (n : ZMod (blockNorm b)) = R.readout () b n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨e, he⟩ := (h 1 (by decide)).2
  have hzero := he 0
  have hone := he 1
  change e (0 : ZMod (blockNorm 1)) = 0 at hzero
  change e (1 : ZMod (blockNorm 1)) = 0 at hone
  have hcontr : (0 : ZMod (blockNorm 1)) = 1 :=
    e.injective (hzero.trans hone.symm)
  exact (by decide : (0 : ZMod (blockNorm 1)) ≠ 1) hcontr

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨?_, rejected, rejected_law⟩
    intro b hb
    exact eisenstein_odd_scalar_quotient b hb
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
    change ∃ (b : ℕ) (x y : ℤ), scalarMap b x ≠ scalarMap b y
    refine ⟨1, (0 : ℤ), 1, ?_⟩
    intro heq
    obtain ⟨_, e, he⟩ := eisenstein_odd_scalar_quotient 1 (by decide)
    change scalarMap 1 0 = scalarMap 1 1 at heq
    have h01 : e (0 : ZMod (blockNorm 1)) =
        e (1 : ZMod (blockNorm 1)) := by
      calc
        e (0 : ZMod (blockNorm 1)) = scalarMap 1 0 := by
          simpa only [Int.cast_zero] using he 0
        _ = scalarMap 1 1 := heq
        _ = e (1 : ZMod (blockNorm 1)) := by
          simpa only [Int.cast_one] using (he 1).symm
    have hcontr : (0 : ZMod (blockNorm 1)) = 1 := e.injective h01
    exact (by decide : (0 : ZMod (blockNorm 1)) ≠ 1) hcontr

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.eisenstein_odd_scalar_quotient) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ b n => scalarMap b n) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Factorization") "QuadraticIdeals") "EisensteinOddQuotient") "eisenstein_odd_scalar_quotient") "Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient/Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ b n => scalarMap b n) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "arg", "arg", "body", "body", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient, declaration := `D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.eisenstein_odd_scalar_quotient, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration_1.canonicalArenaFact, `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration_1.sourceBridgeFact, `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration_1.observationFact0, `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration_1.anchorEnumeration }


#print axioms registration

end

end Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient


noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.arena
noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinOddQuotient\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinOddQuotient\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.arena
noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinOddQuotient\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinOddQuotient\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.arena) (Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration).actual

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinOddQuotient\",\"eisenstein_odd_scalar_quotient\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinOddQuotient\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient, declaration := `D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.eisenstein_odd_scalar_quotient, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration).bridge

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration_1.observation0 : (b : Nat) →
  (hb : @Odd.{0} Nat Nat.instSemiring b) →
    (e :
        @RingEquiv.{0, 0} (ZMod (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.blockNorm b))
          (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.OrientedQuotient b)
          (@Distrib.toMul.{0} (ZMod (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.blockNorm b))
            (@instDistribOfSemiring.{0} (ZMod (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.blockNorm b))
              (@CommSemiring.toSemiring.{0}
                (ZMod (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.blockNorm b))
                (@CommRing.toCommSemiring.{0}
                  (ZMod (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.blockNorm b))
                  (ZMod.commRing (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.blockNorm b))))))
          (@Distrib.toMul.{0} (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.OrientedQuotient b)
            (@instDistribOfSemiring.{0} (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.OrientedQuotient b)
              (@Ideal.Quotient.semiring.{0} D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.EisensteinOrder
                (@QuadraticAlgebra.instCommRing.{0} Int
                  (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                  (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                  Int.instCommRing)
                (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.orientedIdeal b))))
          (@Distrib.toAdd.{0} (ZMod (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.blockNorm b))
            (@instDistribOfSemiring.{0} (ZMod (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.blockNorm b))
              (@CommSemiring.toSemiring.{0}
                (ZMod (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.blockNorm b))
                (@CommRing.toCommSemiring.{0}
                  (ZMod (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.blockNorm b))
                  (ZMod.commRing (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.blockNorm b))))))
          (@Distrib.toAdd.{0} (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.OrientedQuotient b)
            (@instDistribOfSemiring.{0} (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.OrientedQuotient b)
              (@Ideal.Quotient.semiring.{0} D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.EisensteinOrder
                (@QuadraticAlgebra.instCommRing.{0} Int
                  (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                  (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                  Int.instCommRing)
                (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.orientedIdeal b))))) →
      (n : Int) →
        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
          Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.signature PUnit.unit.{1} b :=
  fun (b : Nat) (hb : @Odd.{0} Nat Nat.instSemiring b)
    (e :
      @RingEquiv.{0, 0} (ZMod (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.blockNorm b))
        (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.OrientedQuotient b)
        (@Distrib.toMul.{0} (ZMod (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.blockNorm b))
          (@instDistribOfSemiring.{0} (ZMod (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.blockNorm b))
            (@CommSemiring.toSemiring.{0} (ZMod (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.blockNorm b))
              (@CommRing.toCommSemiring.{0}
                (ZMod (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.blockNorm b))
                (ZMod.commRing (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.blockNorm b))))))
        (@Distrib.toMul.{0} (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.OrientedQuotient b)
          (@instDistribOfSemiring.{0} (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.OrientedQuotient b)
            (@Ideal.Quotient.semiring.{0} D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.EisensteinOrder
              (@QuadraticAlgebra.instCommRing.{0} Int
                (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                Int.instCommRing)
              (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.orientedIdeal b))))
        (@Distrib.toAdd.{0} (ZMod (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.blockNorm b))
          (@instDistribOfSemiring.{0} (ZMod (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.blockNorm b))
            (@CommSemiring.toSemiring.{0} (ZMod (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.blockNorm b))
              (@CommRing.toCommSemiring.{0}
                (ZMod (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.blockNorm b))
                (ZMod.commRing (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.blockNorm b))))))
        (@Distrib.toAdd.{0} (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.OrientedQuotient b)
          (@instDistribOfSemiring.{0} (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.OrientedQuotient b)
            (@Ideal.Quotient.semiring.{0} D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.EisensteinOrder
              (@QuadraticAlgebra.instCommRing.{0} Int
                (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
                Int.instCommRing)
              (D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.orientedIdeal b)))))
    (n : Int) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.signature
    Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.actual PUnit.unit.{1} b n

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinOddQuotient\",\"eisenstein_odd_scalar_quotient\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"argument\",\"argument\",\"body\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinOddQuotient\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient, declaration := `D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.eisenstein_odd_scalar_quotient, part := .type, path := [.body, .body, .argument, .argument, .body, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinOddQuotient\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinOddQuotient\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinOddQuotient\",\"eisenstein_odd_scalar_quotient\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient, declaration := `D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.eisenstein_odd_scalar_quotient, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration).actual (Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration).variation.2.choose (Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration).variation.1 (Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinOddQuotient\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Factorization\",\"QuadraticIdeals\",\"EisensteinOddQuotient\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient, declaration := `Reg.D5.S3.Factorization.QuadraticIdeals.EisensteinOddQuotient.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
