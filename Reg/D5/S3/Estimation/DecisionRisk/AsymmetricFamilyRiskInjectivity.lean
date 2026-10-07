import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity
open LeanInformationAudit
open Set

noncomputable section
namespace Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity

abbrev signature : Signature where
  Params := Σ _aOne : ℝ, Σ _dOne : ℝ, Σ _bOne : ℝ, Σ _piOne : ℝ,
    Σ _aTwo : ℝ, Σ _MTwo : ℝ, ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ p d => asymmetricFiberRisk p.2.2.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.2 d)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature
    (fun _ p d =>
      asymmetricFiberRisk p.2.2.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.2 d + 1)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (aOne dOne bOne piOne aTwo MTwo piTwo : ℝ),
    ((0 < aOne ∧ aOne ≤ dOne ∧ 0 < bOne ∧ bOne + aOne + dOne < 1 ∧
        piOne ∈ Set.Icc (0 : ℝ) 1) →
      let M := bOne + aOne + dOne
      let D := 1 - M
      let tMinus := aOne / (2 * aOne + D)
      let tPlus := (dOne + D) / (2 * dOne + D)
      (0 < tMinus ∧ tMinus < 1 / 2 ∧ 1 / 2 < tPlus ∧ tPlus < 1) ∧
      (piOne ∈ Set.Icc 0 tMinus → asymmetricBayesRisk aOne dOne bOne piOne = piOne) ∧
      (piOne ∈ Set.Icc tMinus (1 / 2) →
        asymmetricBayesRisk aOne dOne bOne piOne =
          aOne + piOne * (M - 2 * aOne)) ∧
      (piOne ∈ Set.Icc (1 / 2) tPlus →
        asymmetricBayesRisk aOne dOne bOne piOne =
          M * (1 - piOne) + (2 * piOne - 1) * dOne) ∧
      (piOne ∈ Set.Icc tPlus 1 →
        asymmetricBayesRisk aOne dOne bOne piOne = 1 - piOne)) ∧
    ((0 < 2 * aTwo ∧ 2 * aTwo < MTwo ∧ MTwo < 1 ∧
        1 / 2 < piTwo ∧ piTwo ≤ 1) →
      let D := 1 - MTwo
      let L := MTwo - aTwo
      let U := 2 * L + D
      let s := 2 * piTwo - 1
      let c := MTwo * (1 - piTwo)
      let t := D * (1 - s) / (2 * s)
      (∀ d ∈ Set.Ico aTwo L,
        R.readout () ⟨aOne, dOne, bOne, piOne, aTwo, MTwo, piTwo⟩ d =
          c + s * min d t) ∧
      (Set.InjOn (asymmetricFiberRisk MTwo aTwo piTwo) (Set.Ico aTwo L) ↔
        piTwo ≤ (L + D) / (2 * L + D)) ∧
      (L + D) / (2 * L + D) = (1 + D / U) / 2 ∧
      (Set.InjOn (asymmetricFiberRisk MTwo aTwo piTwo) (Set.Ico aTwo L) →
        s ≤ D / U) ∧
      Set.InjOn
        (asymmetricFiberRisk MTwo aTwo ((L + D) / (2 * L + D)))
        (Set.Ico aTwo L) ∧
      2 * ((L + D) / (2 * L + D)) - 1 = D / U)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbadAll := (h 0 0 0 0 (1 / 8) (1 / 2) (3 / 4)).2 (by norm_num)
  have hbad := hbadAll.1 (1 / 8) (by norm_num)
  have hgoodAll :=
    (asymmetric_family_risk_and_injective_queries 0 0 0 0 (1 / 8) (1 / 2) (3 / 4)).2
      (by norm_num)
  have hgood := hgoodAll.1 (1 / 8) (by norm_num)
  simp only [rejected, realize, signature] at hbad
  linarith

theorem actual_law : arena.Law actual := by
  intro aOne dOne bOne piOne aTwo MTwo piTwo
  simpa only [actual, realize, signature] using
    asymmetric_family_risk_and_injective_queries
      aOne dOne bOne piOne aTwo MTwo piTwo

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
  let p : signature.Params := ⟨0, 0, 0, 0, 1 / 8, 1 / 2, 3 / 4⟩
  refine ⟨p, 1 / 8, 1 / 4, ?_⟩
  intro heq
  have hgoodAll :=
    (asymmetric_family_risk_and_injective_queries 0 0 0 0 (1 / 8) (1 / 2) (3 / 4)).2
      (by norm_num)
  have hx := hgoodAll.1 (1 / 8) (by norm_num)
  have hy := hgoodAll.1 (1 / 4) (by norm_num)
  simp only [actual, realize, signature, p] at heq
  norm_num at hx hy
  linarith

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.asymmetric_family_risk_and_injective_queries) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ p d => asymmetricFiberRisk p.2.2.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.2 d)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Estimation") "DecisionRisk") "AsymmetricFamilyRiskInjectivity") "asymmetric_family_risk_and_injective_queries") "Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity/Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration,
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
    (fun _ p d => asymmetricFiberRisk p.2.2.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.2 d)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity, definition := none, coordinates := #[0, 1, 2, 3, 4, 5, 6], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "body", "fn", "arg"], stateBinder := 14, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity, declaration := `D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.asymmetric_family_risk_and_injective_queries, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity, declaration := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity, declaration := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity, declaration := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity, declaration := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration_1.canonicalArenaFact, `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration_1.sourceBridgeFact, `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration_1.observationFact0, `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration_1.anchorEnumeration }


#print axioms rejected_law
#print axioms actual_law
#print axioms sensitivity_proof
#print axioms dependence_proof

end Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity


noncomputable def Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.arena
noncomputable def Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"AsymmetricFamilyRiskInjectivity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"AsymmetricFamilyRiskInjectivity\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity, declaration := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity, declaration := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.arena
noncomputable def Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"AsymmetricFamilyRiskInjectivity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"AsymmetricFamilyRiskInjectivity\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity, declaration := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity, declaration := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.arena
      Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.actual)
    Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration)

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"AsymmetricFamilyRiskInjectivity\",\"asymmetric_family_risk_and_injective_queries\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"AsymmetricFamilyRiskInjectivity\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity, declaration := `D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.asymmetric_family_risk_and_injective_queries, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity, declaration := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.arena
    Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.actual)
  Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration)

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration_1.observation0 : (aOne dOne bOne piOne aTwo MTwo piTwo : Real) →
  And
      (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          aTwo))
      (And
        (@LT.lt.{0} Real Real.instLT
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            aTwo)
          MTwo)
        (And
          (@LT.lt.{0} Real Real.instLT MTwo (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
          (And
            (@LT.lt.{0} Real Real.instLT
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
              piTwo)
            (@LE.le.{0} Real Real.instLE piTwo
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))) →
    have L : Real := @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) MTwo aTwo;
    (d : Real) →
      @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
          (@Set.Ico.{0} Real Real.instPreorder aTwo L) d →
        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
          Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.signature PUnit.unit.{1}
          (@Sigma.mk.{0, 0} Real
            (fun (_aOne : Real) =>
              @Sigma.{0, 0} Real fun (_dOne : Real) =>
                @Sigma.{0, 0} Real fun (_bOne : Real) =>
                  @Sigma.{0, 0} Real fun (_piOne : Real) =>
                    @Sigma.{0, 0} Real fun (_aTwo : Real) => @Sigma.{0, 0} Real fun (_MTwo : Real) => Real)
            aOne
            (@Sigma.mk.{0, 0} Real
              (fun (_dOne : Real) =>
                @Sigma.{0, 0} Real fun (_bOne : Real) =>
                  @Sigma.{0, 0} Real fun (_piOne : Real) =>
                    @Sigma.{0, 0} Real fun (_aTwo : Real) => @Sigma.{0, 0} Real fun (_MTwo : Real) => Real)
              dOne
              (@Sigma.mk.{0, 0} Real
                (fun (_bOne : Real) =>
                  @Sigma.{0, 0} Real fun (_piOne : Real) =>
                    @Sigma.{0, 0} Real fun (_aTwo : Real) => @Sigma.{0, 0} Real fun (_MTwo : Real) => Real)
                bOne
                (@Sigma.mk.{0, 0} Real
                  (fun (_piOne : Real) =>
                    @Sigma.{0, 0} Real fun (_aTwo : Real) => @Sigma.{0, 0} Real fun (_MTwo : Real) => Real)
                  piOne
                  (@Sigma.mk.{0, 0} Real (fun (_aTwo : Real) => @Sigma.{0, 0} Real fun (_MTwo : Real) => Real) aTwo
                    (@Sigma.mk.{0, 0} Real (fun (_MTwo : Real) => Real) MTwo piTwo)))))) :=
  fun (aOne dOne bOne piOne aTwo MTwo piTwo : Real)
    (a :
      And
        (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            aTwo))
        (And
          (@LT.lt.{0} Real Real.instLT
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              aTwo)
            MTwo)
          (And
            (@LT.lt.{0} Real Real.instLT MTwo (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
            (And
              (@LT.lt.{0} Real Real.instLT
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                piTwo)
              (@LE.le.{0} Real Real.instLE piTwo
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))))) =>
  have D : Real :=
    @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) MTwo;
  have L : Real := @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) MTwo aTwo;
  have U : Real :=
    @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        L)
      D;
  have s : Real :=
    @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        piTwo)
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne));
  have c : Real :=
    @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) MTwo
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) piTwo);
  have t : Real :=
    @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) D
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) s))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        s);
  fun (d : Real)
    (a :
      @Membership.mem.{0, 0} Real (Set.{0} Real) (@Set.instMembership.{0} Real)
        (@Set.Ico.{0} Real Real.instPreorder aTwo L) d) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.signature
    Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Real
      (fun (_aOne : Real) =>
        @Sigma.{0, 0} Real fun (_dOne : Real) =>
          @Sigma.{0, 0} Real fun (_bOne : Real) =>
            @Sigma.{0, 0} Real fun (_piOne : Real) =>
              @Sigma.{0, 0} Real fun (_aTwo : Real) => @Sigma.{0, 0} Real fun (_MTwo : Real) => Real)
      aOne
      (@Sigma.mk.{0, 0} Real
        (fun (_dOne : Real) =>
          @Sigma.{0, 0} Real fun (_bOne : Real) =>
            @Sigma.{0, 0} Real fun (_piOne : Real) =>
              @Sigma.{0, 0} Real fun (_aTwo : Real) => @Sigma.{0, 0} Real fun (_MTwo : Real) => Real)
        dOne
        (@Sigma.mk.{0, 0} Real
          (fun (_bOne : Real) =>
            @Sigma.{0, 0} Real fun (_piOne : Real) =>
              @Sigma.{0, 0} Real fun (_aTwo : Real) => @Sigma.{0, 0} Real fun (_MTwo : Real) => Real)
          bOne
          (@Sigma.mk.{0, 0} Real
            (fun (_piOne : Real) =>
              @Sigma.{0, 0} Real fun (_aTwo : Real) => @Sigma.{0, 0} Real fun (_MTwo : Real) => Real)
            piOne
            (@Sigma.mk.{0, 0} Real (fun (_aTwo : Real) => @Sigma.{0, 0} Real fun (_MTwo : Real) => Real) aTwo
              (@Sigma.mk.{0, 0} Real (fun (_MTwo : Real) => Real) MTwo piTwo))))))
    d

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"AsymmetricFamilyRiskInjectivity\",\"asymmetric_family_risk_and_injective_queries\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"letBody\",\"letBody\",\"letBody\",\"letBody\",\"letBody\",\"letBody\",\"function\",\"argument\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"AsymmetricFamilyRiskInjectivity\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity, declaration := `D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.asymmetric_family_risk_and_injective_queries, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .argument, .body, .letBody, .letBody, .letBody, .letBody, .letBody, .letBody, .function, .argument, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity, declaration := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"AsymmetricFamilyRiskInjectivity\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"AsymmetricFamilyRiskInjectivity\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"AsymmetricFamilyRiskInjectivity\",\"asymmetric_family_risk_and_injective_queries\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity, declaration := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity, declaration := `D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.asymmetric_family_risk_and_injective_queries, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration).actual (Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration).variation.2.choose (Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration).variation.1 (Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"AsymmetricFamilyRiskInjectivity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"AsymmetricFamilyRiskInjectivity\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity, declaration := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity, declaration := `Reg.D5.S3.Estimation.DecisionRisk.AsymmetricFamilyRiskInjectivity.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
