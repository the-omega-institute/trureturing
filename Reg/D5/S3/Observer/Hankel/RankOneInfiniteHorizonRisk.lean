import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk

open _root_.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Filter
open scoped ENNReal Topology

noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ T η => minimaxRisk T η) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (T : ℕ) (_hT : 1 ≤ T) (η : ℝ) (_hη : 0 < η),
    R.readout () T η = ENNReal.ofReal (1 / 2 : ℝ) ∧
    (∀ a ∈ Set.Ioo (0 : ℝ) 1,
      Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0) ∧
      ∀ N, (hankel a N).PosSemidef ∧ (hankel a N).rank = 1)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h 1 le_rfl 1 zero_lt_one).1
  have hp : (0 : ℝ≥0∞) < ENNReal.ofReal (1 / 2 : ℝ) :=
    ENNReal.ofReal_pos.mpr (by norm_num)
  exact (ne_of_gt hp) he.symm

/-- Exact observation of the first response determines the parameter. -/
theorem noiseless_risk : minimaxRisk 1 0 = 0 := by
  apply bot_unique
  refine (iInf_le (fun Ψ => risk 1 0 Ψ)
    (fun y n => y (1 : Fin 2) ^ n.val)).trans ?_
  refine iSup_le fun a => iSup_le fun y => iSup_le fun hy => iSup_le fun n => ?_
  have he : y (1 : Fin 2) = a.val := by
    have hh := hy (1 : Fin 2)
    have hz : |y (1 : Fin 2) - a.val| = 0 := by
      apply le_antisymm
      · simpa using hh
      · exact abs_nonneg _
    exact sub_eq_zero.mp (abs_eq_zero.mp hz)
  simp [he]

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨rank_one_infinite_horizon_risk, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨(1 : ℕ), (0 : ℝ), (1 : ℝ), ?_⟩
    change minimaxRisk 1 0 ≠ minimaxRisk 1 1
    rw [noiseless_risk, (rank_one_infinite_horizon_risk 1 le_rfl 1 zero_lt_one).1]
    exact (ne_of_gt (ENNReal.ofReal_pos.mpr (by norm_num))).symm

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.rank_one_infinite_horizon_risk) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ T η => minimaxRisk T η) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Observer") "Hankel") "RankOneInfiniteHorizonRisk") "rank_one_infinite_horizon_risk") "Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk/Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ T η => minimaxRisk T η) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg"], stateBinder := 2, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk, declaration := `D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.rank_one_infinite_horizon_risk, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk, declaration := `Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk, declaration := `Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk, declaration := `Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk, declaration := `Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration_1.canonicalArenaFact, `Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration_1.sourceBridgeFact, `Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration_1.observationFact0, `Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration_1.anchorEnumeration }


#print axioms registration
end
end Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk


noncomputable def Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.arena
noncomputable def Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Hankel\",\"RankOneInfiniteHorizonRisk\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Hankel\",\"RankOneInfiniteHorizonRisk\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk, declaration := `Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk, declaration := `Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.arena
noncomputable def Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Hankel\",\"RankOneInfiniteHorizonRisk\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Hankel\",\"RankOneInfiniteHorizonRisk\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk, declaration := `Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk, declaration := `Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.arena
      Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.actual)
    Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration)

noncomputable def Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Hankel\",\"RankOneInfiniteHorizonRisk\",\"rank_one_infinite_horizon_risk\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Hankel\",\"RankOneInfiniteHorizonRisk\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk, declaration := `D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.rank_one_infinite_horizon_risk, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk, declaration := `Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.arena
    Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.actual)
  Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration)

noncomputable def Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration_1.observation0 : (T : Nat) →
  (_hT : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) T) →
    (η : Real) →
      (hη : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) η) →
        D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
          Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.signature PUnit.unit.{1} T :=
  fun (T : Nat) (_hT : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) T)
    (η : Real)
    (hη : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) η) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.signature
    Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.actual PUnit.unit.{1} T η

noncomputable def Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Hankel\",\"RankOneInfiniteHorizonRisk\",\"rank_one_infinite_horizon_risk\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Hankel\",\"RankOneInfiniteHorizonRisk\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk, declaration := `D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.rank_one_infinite_horizon_risk, part := .type, path := [.body, .body, .body, .body, .function, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk, declaration := `Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Hankel\",\"RankOneInfiniteHorizonRisk\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Hankel\",\"RankOneInfiniteHorizonRisk\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Hankel\",\"RankOneInfiniteHorizonRisk\",\"rank_one_infinite_horizon_risk\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk, declaration := `Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk, declaration := `D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.rank_one_infinite_horizon_risk, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration).actual (Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration).variation.2.choose (Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration).variation.1 (Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Hankel\",\"RankOneInfiniteHorizonRisk\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Hankel\",\"RankOneInfiniteHorizonRisk\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk, declaration := `Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk, declaration := `Reg.D5.S3.Observer.Hankel.RankOneInfiniteHorizonRisk.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
