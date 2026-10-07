import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency
open _root_.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity
open _root_.D5.S3.Estimation.SequentialDecisionRisk.FiniteDeficiencyRiskTransfer
open _root_.D5.S3.Divergence.ClassicalDPI
open _root_.D5.S3.Estimation.DecisionRisk.DescentDefectBounds
open _root_.D5.S3.TotalVariation.Pinsker
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency

abbrev signature : Signature where
  Params := Σ _a : ℝ, Σ _M : ℝ, ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ENNReal
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ p dTwo =>
      let L := p.2.1 - p.1
      let QOne := asymmetricExperiment p.1 p.2.2 (L - p.2.2)
      let QTwo := asymmetricExperiment p.1 dTwo (L - dTwo)
      finiteDeficiency QOne QTwo)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature
    (fun _ _ _ => 0)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (a M dOne dTwo : ℝ),
    0 < 2 * a → M < 1 → a ≤ dOne → dOne < dTwo → dTwo < M - a →
    let D := 1 - M
    let L := M - a
    let QOne := asymmetricExperiment a dOne (L - dOne)
    let QTwo := asymmetricExperiment a dTwo (L - dTwo)
    let gamma := D * (dTwo - dOne) / (2 * dTwo + D)
    let h := 2 * (dTwo - dOne) / (2 * dTwo + D)
    finiteDeficiency QTwo QOne = 0 ∧
      R.readout () ⟨a, M, dOne⟩ dTwo = ENNReal.ofReal gamma ∧
      0 < gamma ∧
      0 < (dTwo - dOne) / (L - dOne) ∧
      (dTwo - dOne) / (L - dOne) < 1 ∧
      0 < h ∧
      h < 1 ∧
      (∃ K : FiniteMarkovKernel (Fin 3) (Fin 3),
        K.1 = !![1 - (dTwo - dOne) / (L - dOne), 0, (dTwo - dOne) / (L - dOne);
                 0, 1, 0;
                 0, 0, 1] ∧
        ∀ state : Fin 2, channelOutput K.1 (QOne state) = QTwo state) ∧
      ∃ reverseKernel : FiniteMarkovKernel (Fin 3) (Fin 3),
        reverseKernel.1 = !![1, 0, 0;
                             0, 1, 0;
                             h, 0, 1 - h] ∧
        (∀ state : Fin 2,
          totalVariation (QOne state)
            (channelOutput reverseKernel.1 (QTwo state)) = gamma) ∧
        uniformSimulationError QOne QTwo reverseKernel = gamma

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad :=
    (h (1 / 8) (3 / 4) (1 / 4) (1 / 2)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)).2.1
  simp only [rejected, realize, signature] at hbad
  exact (ENNReal.ofReal_ne_zero_iff.mpr (by norm_num)) hbad.symm

theorem actual_law : arena.Law actual := by
  intro a M dOne dTwo ha hM hadOne hdOneTwo hdTwo
  simpa only [actual, realize, signature] using
    asymmetric_family_deficiency a M dOne dTwo ha hM hadOne hdOneTwo hdTwo

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
  intro i
  cases i
  let p : signature.Params := ⟨1 / 8, 3 / 4, 1 / 4⟩
  refine ⟨p, 3 / 8, 1 / 2, ?_⟩
  intro heq
  have hx :=
    (asymmetric_family_deficiency (1 / 8) (3 / 4) (1 / 4) (3 / 8)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)).2.1
  have hy :=
    (asymmetric_family_deficiency (1 / 8) (3 / 4) (1 / 4) (1 / 2)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)).2.1
  simp only [actual, realize, signature, p] at heq
  rw [hx, hy] at heq
  norm_num at heq

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.asymmetric_family_deficiency) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ p dTwo =>
      let L := p.2.1 - p.1
      let QOne := asymmetricExperiment p.1 p.2.2 (L - p.2.2)
      let QTwo := asymmetricExperiment p.1 dTwo (L - dTwo)
      finiteDeficiency.{0, 0, 0} QOne QTwo)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Estimation") "DecisionRisk") "AsymmetricFamilyDeficiency") "asymmetric_family_deficiency") "Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency/Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration,
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
    (fun _ p dTwo =>
      let L := p.2.1 - p.1
      let QOne := asymmetricExperiment p.1 p.2.2 (L - p.2.2)
      let QTwo := asymmetricExperiment p.1 dTwo (L - dTwo)
      finiteDeficiency.{0, 0, 0} QOne QTwo)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency, definition := none, coordinates := #[0, 1, 2], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg"], stateBinder := 3, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency, declaration := `D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.asymmetric_family_deficiency, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency, declaration := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency, declaration := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency, declaration := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency, declaration := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration_1.canonicalArenaFact, `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration_1.sourceBridgeFact, `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration_1.observationFact0, `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration_1.anchorEnumeration }


#print axioms rejected_law
#print axioms actual_law
#print axioms sensitivity_proof
#print axioms dependence_proof

end Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency


noncomputable def Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.arena
noncomputable def Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"AsymmetricFamilyDeficiency\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"AsymmetricFamilyDeficiency\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency, declaration := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency, declaration := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.arena
noncomputable def Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"AsymmetricFamilyDeficiency\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"AsymmetricFamilyDeficiency\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency, declaration := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency, declaration := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.arena
      Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.actual)
    Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration)

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"AsymmetricFamilyDeficiency\",\"asymmetric_family_deficiency\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"AsymmetricFamilyDeficiency\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency, declaration := `D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.asymmetric_family_deficiency, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency, declaration := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.arena
    Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.actual)
  Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration)

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration_1.observation0 : (a M dOne dTwo : Real) →
  (ha :
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          a)) →
    (hM : @LT.lt.{0} Real Real.instLT M (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
      (hadOne : @LE.le.{0} Real Real.instLE a dOne) →
        (hdOneTwo : @LT.lt.{0} Real Real.instLT dOne dTwo) →
          (hdTwo :
              @LT.lt.{0} Real Real.instLT dTwo
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) M a)) →
            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.signature PUnit.unit.{1}
              (@Sigma.mk.{0, 0} Real (fun (_a : Real) => @Sigma.{0, 0} Real fun (_M : Real) => Real) a
                (@Sigma.mk.{0, 0} Real (fun (_M : Real) => Real) M dOne)) :=
  fun (a M dOne dTwo : Real)
    (ha :
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          a))
    (hM : @LT.lt.{0} Real Real.instLT M (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (hadOne : @LE.le.{0} Real Real.instLE a dOne) (hdOneTwo : @LT.lt.{0} Real Real.instLT dOne dTwo)
    (hdTwo :
      @LT.lt.{0} Real Real.instLT dTwo (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) M a)) =>
  have D : Real :=
    @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) M;
  have L : Real := @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) M a;
  have QOne :
    Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real :=
    D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.asymmetricExperiment a dOne
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) L dOne);
  have QTwo :
    Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Real :=
    D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.asymmetricExperiment a dTwo
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) L dTwo);
  have gamma : Real :=
    @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) D
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) dTwo dOne))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          dTwo)
        D);
  have h : Real :=
    @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) dTwo dOne))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          dTwo)
        D);
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.signature
    Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Real (fun (_a : Real) => @Sigma.{0, 0} Real fun (_M : Real) => Real) a
      (@Sigma.mk.{0, 0} Real (fun (_M : Real) => Real) M dOne))
    dTwo

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"AsymmetricFamilyDeficiency\",\"asymmetric_family_deficiency\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"letBody\",\"letBody\",\"letBody\",\"letBody\",\"letBody\",\"letBody\",\"argument\",\"function\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"AsymmetricFamilyDeficiency\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency, declaration := `D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.asymmetric_family_deficiency, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .letBody, .letBody, .letBody, .letBody, .letBody, .letBody, .argument, .function, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency, declaration := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"AsymmetricFamilyDeficiency\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"AsymmetricFamilyDeficiency\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"AsymmetricFamilyDeficiency\",\"asymmetric_family_deficiency\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency, declaration := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency, declaration := `D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.asymmetric_family_deficiency, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration).actual (Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration).variation.2.choose (Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration).variation.1 (Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"AsymmetricFamilyDeficiency\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"AsymmetricFamilyDeficiency\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency, declaration := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency, declaration := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyDeficiency.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
