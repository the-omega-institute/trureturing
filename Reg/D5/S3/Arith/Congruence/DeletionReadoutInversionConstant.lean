import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Congruence.DeletionReadoutInversionConstant
import Reg.Support.DependentFamily
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses

open _root_.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Lean Elab Command
open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant

@[reducible] def signature : Signature where
  Params := Σ r : ℕ, Fin r → ℕ
  State p := (∀ i, Fin (p.2 i)) → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (∀ i, Fin (p.2 i)) → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z ↦ z) (fun e ↦ nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ z c ↦ z c + 1) (fun e ↦ nomatch e)

def arena : Arena where
  signature := signature
  Law readout := ∀ (r : ℕ) (m : Fin r → ℕ) (hm : ∀ i, 2 ≤ m i)
      (z : (∀ i, Fin (m i)) → ℝ),
    (∀ c, |(readout.readout () ⟨r, m⟩ z) c| ≤ kappa m * obsNorm m hm z) ∧
      ∀ cstar : ∀ i, Fin (m i),
        let w : (∀ i, Fin (m i)) → ℝ := fun c ↦
          ∏ i, if c i = cstar i then 2 * (m i : ℝ) - 3 else -1
        obsNorm m hm w = ∏ i, ((m i : ℝ) - 1) ∧
          |w cstar| = kappa m * obsNorm m hm w

theorem actual_law : arena.Law actual := by
  intro r m hm z
  simpa only [actual, realize] using deletion_readout_inversion_constant r m hm z

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let m : Fin 0 → ℕ := fun i ↦ nomatch i
  let point : ∀ i, Fin (m i) := fun i ↦ nomatch i
  let zero : (∀ i, Fin (m i)) → ℝ := fun _ ↦ 0
  have hbound := (h 0 m (fun i ↦ nomatch i) zero).1 point
  norm_num [rejected, realize, signature, kappa, obsNorm, R, m, point, zero] at hbound

theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    cases i
    cases j
    exact (hji rfl).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro _
  let p : signature.Params := ⟨0, fun i ↦ nomatch i⟩
  let zero : signature.State p := fun _ ↦ 0
  let one : signature.State p := fun _ ↦ 1
  refine ⟨p, zero, one, ?_⟩
  intro h
  have hvalue := congrFun h (fun i ↦ nomatch i)
  norm_num [actual, realize, zero, one] at hvalue

def registration : Registration arena
    (∀ (r : ℕ) (m : Fin r → ℕ) (hm : ∀ i, 2 ≤ m i)
      (z : (∀ i, Fin (m i)) → ℝ),
      (∀ c, |z c| ≤ kappa m * obsNorm m hm z) ∧
        ∀ cstar : ∀ i, Fin (m i),
          let w : (∀ i, Fin (m i)) → ℝ := fun c ↦
            ∏ i, if c i = cstar i then 2 * (m i : ℝ) - 3 else -1
          obsNorm m hm w = ∏ i, ((m i : ℝ) - 1) ∧
            |w cstar| = kappa m * obsNorm m hm w) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof



noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.deletion_readout_inversion_constant) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ z ↦ z) (fun e ↦ nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Congruence") "DeletionReadoutInversionConstant") "deletion_readout_inversion_constant") "Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant/Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ z ↦ z) (fun e ↦ nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Congruence.DeletionReadoutInversionConstant, definition := none, coordinates := #[0, 1], readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "body", "fn", "arg", "arg", "fn"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.Congruence.DeletionReadoutInversionConstant, declaration := `D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.deletion_readout_inversion_constant, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant, declaration := `Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant, declaration := `Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant, declaration := `Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant, declaration := `Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration_1.observationFact0, `Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration_1.anchorEnumeration }


#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof


end Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant


noncomputable def Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.arena
noncomputable def Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Congruence\",\"DeletionReadoutInversionConstant\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Congruence\",\"DeletionReadoutInversionConstant\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant, declaration := `Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant, declaration := `Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.arena
noncomputable def Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Congruence\",\"DeletionReadoutInversionConstant\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Congruence\",\"DeletionReadoutInversionConstant\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant, declaration := `Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant, declaration := `Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.arena
    (∀ (r : Nat) (m : Fin r → Nat)
      (hm : ∀ (i : Fin r), @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (m i))
      (z : ((i : Fin r) → Fin (m i)) → Real),
      And
        (∀ (c : (i : Fin r) → Fin (m i)),
          @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (z c))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.kappa r m)
              (@D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.obsNorm r m hm z)))
        (∀ (cstar : (i : Fin r) → Fin (m i)),
          have w : ((i : Fin r) → Fin (m i)) → Real := fun (c : (i : Fin r) → Fin (m i)) =>
            @Finset.prod.{0, 0} (Fin r) Real Real.instCommMonoid (@Finset.univ.{0} (Fin r) (Fin.fintype r))
              fun (i : Fin r) =>
              @ite.{1} Real (@Eq.{1} (Fin (m i)) (c i) (cstar i)) (instDecidableEqFin (m i) (c i) (cstar i))
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    (@Nat.cast.{0} Real Real.instNatCast (m i)))
                  (@OfNat.ofNat.{0} Real (nat_lit 3)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
                (@Neg.neg.{0} Real Real.instNeg
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)));
          And
            (@Eq.{1} Real (@D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.obsNorm r m hm w)
              (@Finset.prod.{0, 0} (Fin r) Real Real.instCommMonoid (@Finset.univ.{0} (Fin r) (Fin.fintype r))
                fun (i : Fin r) =>
                @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@Nat.cast.{0} Real Real.instNatCast (m i))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
            (@Eq.{1} Real (@abs.{0} Real Real.lattice Real.instAddGroup (w cstar))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.kappa r m)
                (@D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.obsNorm r m hm w)))))
    Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration)

noncomputable def Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Congruence\",\"DeletionReadoutInversionConstant\",\"deletion_readout_inversion_constant\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Congruence\",\"DeletionReadoutInversionConstant\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Congruence.DeletionReadoutInversionConstant, declaration := `D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.deletion_readout_inversion_constant, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant, declaration := `Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.arena
  (∀ (r : Nat) (m : Fin r → Nat)
    (hm : ∀ (i : Fin r), @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (m i))
    (z : ((i : Fin r) → Fin (m i)) → Real),
    And
      (∀ (c : (i : Fin r) → Fin (m i)),
        @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (z c))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.kappa r m)
            (@D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.obsNorm r m hm z)))
      (∀ (cstar : (i : Fin r) → Fin (m i)),
        have w : ((i : Fin r) → Fin (m i)) → Real := fun (c : (i : Fin r) → Fin (m i)) =>
          @Finset.prod.{0, 0} (Fin r) Real Real.instCommMonoid (@Finset.univ.{0} (Fin r) (Fin.fintype r))
            fun (i : Fin r) =>
            @ite.{1} Real (@Eq.{1} (Fin (m i)) (c i) (cstar i)) (instDecidableEqFin (m i) (c i) (cstar i))
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  (@Nat.cast.{0} Real Real.instNatCast (m i)))
                (@OfNat.ofNat.{0} Real (nat_lit 3)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
              (@Neg.neg.{0} Real Real.instNeg
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)));
        And
          (@Eq.{1} Real (@D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.obsNorm r m hm w)
            (@Finset.prod.{0, 0} (Fin r) Real Real.instCommMonoid (@Finset.univ.{0} (Fin r) (Fin.fintype r))
              fun (i : Fin r) =>
              @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@Nat.cast.{0} Real Real.instNatCast (m i))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
          (@Eq.{1} Real (@abs.{0} Real Real.lattice Real.instAddGroup (w cstar))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.kappa r m)
              (@D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.obsNorm r m hm w)))))
  Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration)

noncomputable def Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration_1.observation0 : (r : Nat) →
  (m : Fin r → Nat) →
    (hm : ∀ (i : Fin r), @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (m i)) →
      (z : ((i : Fin r) → Fin (m i)) → Real) →
        (c : (i : Fin r) → Fin (m i)) →
          D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
            Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.signature PUnit.unit.{1}
            (@Sigma.mk.{0, 0} Nat (fun (r : Nat) => Fin r → Nat) r m) :=
  fun (r : Nat) (m : Fin r → Nat)
    (hm : ∀ (i : Fin r), @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (m i))
    (z : ((i : Fin r) → Fin (m i)) → Real) (c : (i : Fin r) → Fin (m i)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.signature
    Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat (fun (r : Nat) => Fin r → Nat) r m) z

noncomputable def Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Congruence\",\"DeletionReadoutInversionConstant\",\"deletion_readout_inversion_constant\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"body\",\"function\",\"argument\",\"argument\",\"function\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Congruence\",\"DeletionReadoutInversionConstant\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Congruence.DeletionReadoutInversionConstant, declaration := `D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.deletion_readout_inversion_constant, part := .type, path := [.body, .body, .body, .body, .function, .argument, .body, .function, .argument, .argument, .function], levels := [] }
  { owner := `Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant, declaration := `Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Congruence\",\"DeletionReadoutInversionConstant\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Congruence\",\"DeletionReadoutInversionConstant\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Congruence\",\"DeletionReadoutInversionConstant\",\"deletion_readout_inversion_constant\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant, declaration := `Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.Congruence.DeletionReadoutInversionConstant, declaration := `D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.deletion_readout_inversion_constant, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration).actual (Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration).variation.2.choose (Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration).variation.1 (Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Congruence\",\"DeletionReadoutInversionConstant\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Congruence\",\"DeletionReadoutInversionConstant\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant, declaration := `Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant, declaration := `Reg.D5.S3.Arith.Congruence.DeletionReadoutInversionConstant.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
