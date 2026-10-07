import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments
open LeanInformationAudit
open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments

abbrev signature : Signature where
  Params := ℕ
  State k := Fin k → ℤˣ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ k eta =>
      (∑ i : Fin k, ∑ j : Fin k,
        if i < j then
          (((eta i : ℤˣ) : ℤ) : ℝ) * (((eta j : ℤˣ) : ℤ) : ℝ)
        else 0) / (Nat.choose k 2 : ℝ))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature
    (fun _ k eta =>
      (∑ i : Fin k, ∑ j : Fin k,
        if i < j then
          (((eta i : ℤˣ) : ℤ) : ℝ) * (((eta j : ℤˣ) : ℤ) : ℝ)
        else 0) / (Nat.choose k 2 : ℝ) + 1)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (k : ℕ) (mu : ℝ), 2 ≤ k → -1 ≤ mu → mu ≤ 1 →
    (∀ eta : Fin k → ℤˣ,
      signPairUStatistic eta = R.readout () k eta) ∧
    (∑ eta : Fin k → ℤˣ, signPairWeight mu eta * signPairUStatistic eta) =
      mu ^ 2 ∧
    (∑ eta : Fin k → ℤˣ, signPairWeight mu eta * signPairUStatistic eta ^ 2) -
        (∑ eta : Fin k → ℤˣ, signPairWeight mu eta * signPairUStatistic eta) ^ 2 =
      4 * mu ^ 2 * (1 - mu ^ 2) / k +
        2 * (1 - mu ^ 2) ^ 2 / ((k : ℝ) * ((k : ℝ) - 1))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hcase := (h 2 0 (by norm_num) (by norm_num) (by norm_num)).1
    (fun _ : Fin 2 => (1 : ℤˣ))
  norm_num [rejected, realize, signature, signPairUStatistic, Fin.sum_univ_succ] at hcase
  have hc :
      (Finset.filter (fun x : Fin 2 => 0 < x) Finset.univ).card +
        (Finset.filter (fun x : Fin 2 => 1 < x) Finset.univ).card = 1 := by
    decide
  have hz :
      (Finset.filter (fun x : Fin 2 => 0 < x) Finset.univ).card +
        (Finset.filter (fun x : Fin 2 => 1 < x) Finset.univ).card = 0 := by
    exact_mod_cast hcase
  omega

theorem actual_law : arena.Law actual := by
  intro k mu hk hmu_lower hmu_upper
  simpa [actual, realize, signature] using
    sign_pair_u_statistic_moments k mu hk hmu_lower hmu_upper

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
  let plus : Fin 2 → ℤˣ := fun _ => 1
  let mixed : Fin 2 → ℤˣ := fun j => if j = 0 then 1 else -1
  refine ⟨2, plus, mixed, ?_⟩
  norm_num [actual, realize, signature, plus, mixed, Fin.sum_univ_succ]
  have hc :
      (Finset.filter (fun x : Fin 2 => 0 < x) Finset.univ).card +
        (Finset.filter (fun x : Fin 2 => 1 < x) Finset.univ).card = 1 := by
    decide
  have hreal :
      ((Finset.filter (fun x : Fin 2 => 0 < x) Finset.univ).card : ℝ) +
        (Finset.filter (fun x : Fin 2 => 1 < x) Finset.univ).card = 1 := by
    exact_mod_cast hc
  norm_num [hreal]

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.sign_pair_u_statistic_moments) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ k eta =>
      (∑ i : Fin k, ∑ j : Fin k,
        if i < j then
          (((eta i : ℤˣ) : ℤ) : ℝ) * (((eta j : ℤˣ) : ℤ) : ℝ)
        else 0) / (Nat.choose k 2 : ℝ))
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Estimation") "DecisionRisk") "SignPairUStatisticMoments") "sign_pair_u_statistic_moments") "Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments/Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration,
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
    (fun _ k eta =>
      (∑ i : Fin k, ∑ j : Fin k,
        if i < j then
          (((eta i : ℤˣ) : ℤ) : ℝ) * (((eta j : ℤˣ) : ℤ) : ℝ)
        else 0) / (Nat.choose k 2 : ℝ))
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg", "body", "arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments, declaration := `D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.sign_pair_u_statistic_moments, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments, declaration := `Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments, declaration := `Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments, declaration := `Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments, declaration := `Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration_1.canonicalArenaFact, `Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration_1.sourceBridgeFact, `Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration_1.observationFact0, `Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration_1.anchorEnumeration }


#print axioms rejected_law
#print axioms actual_law
#print axioms sensitivity_proof
#print axioms dependence_proof

end Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments


noncomputable def Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.arena
noncomputable def Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"SignPairUStatisticMoments\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"SignPairUStatisticMoments\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments, declaration := `Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments, declaration := `Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.arena
noncomputable def Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"SignPairUStatisticMoments\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"SignPairUStatisticMoments\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments, declaration := `Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments, declaration := `Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.arena
      Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.actual)
    Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration)

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"SignPairUStatisticMoments\",\"sign_pair_u_statistic_moments\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"SignPairUStatisticMoments\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments, declaration := `D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.sign_pair_u_statistic_moments, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments, declaration := `Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.arena
    Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.actual)
  Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration)

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration_1.observation0 : (k : Nat) →
  (mu : Real) →
    (hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k) →
      (_hmu_lower :
          @LE.le.{0} Real Real.instLE
            (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
            mu) →
        (_hmu_upper :
            @LE.le.{0} Real Real.instLE mu (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
          (eta : Fin k → @Units.{0} Int Int.instMonoid) →
            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.signature PUnit.unit.{1} k :=
  fun (k : Nat) (mu : Real)
    (hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)
    (_hmu_lower :
      @LE.le.{0} Real Real.instLE
        (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) mu)
    (_hmu_upper :
      @LE.le.{0} Real Real.instLE mu (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (eta : Fin k → @Units.{0} Int Int.instMonoid) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.signature
    Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.actual PUnit.unit.{1} k eta

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"SignPairUStatisticMoments\",\"sign_pair_u_statistic_moments\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"SignPairUStatisticMoments\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments, declaration := `D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.sign_pair_u_statistic_moments, part := .type, path := [.body, .body, .body, .body, .body, .function, .argument, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments, declaration := `Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"SignPairUStatisticMoments\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"SignPairUStatisticMoments\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"SignPairUStatisticMoments\",\"sign_pair_u_statistic_moments\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments, declaration := `Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments, declaration := `D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.sign_pair_u_statistic_moments, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration).actual (Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration).variation.2.choose (Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration).variation.1 (Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"SignPairUStatisticMoments\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Estimation\",\"DecisionRisk\",\"SignPairUStatisticMoments\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments, declaration := `Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments, declaration := `Reg.D5.S3.Estimation.DecisionRisk.SignPairUStatisticMoments.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
