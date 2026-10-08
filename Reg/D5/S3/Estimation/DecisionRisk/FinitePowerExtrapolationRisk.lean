import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Estimation.DecisionRisk.FinitePowerExtrapolationRisk
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Estimation.DecisionRisk.FinitePowerExtrapolationRisk

open _root_.D5.S3.Estimation.DecisionRisk.FinitePowerExtrapolationRisk
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped ENNReal

noncomputable section

abbrev signature : Signature where
  Params := Σ _T : ℕ, ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p η => minimaxRisk p.1 p.2 η) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (T H : ℕ) (_hT : 1 ≤ T) (_hTH : T ≤ H) (η : ℝ) (_hη : 0 < η),
    let r := R.readout () ⟨T, H⟩ η
    (ENNReal.ofReal (min (η * H / (2 * T)) (1 / 16)) ≤ r ∧
      r ≤ ENNReal.ofReal (min (1 / 2) (η * H / T))) ∧
    (ENNReal.ofReal ((1 / 16) * min 1 (η * H / T)) ≤ r ∧
      r ≤ ENNReal.ofReal (min 1 (η * H / T)))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h 1 1 le_rfl le_rfl 1 zero_lt_one).1.1
  norm_num [rejected, realize, signature] at hh

theorem noiseless_risk : minimaxRisk 1 1 0 = 0 := by
  apply bot_unique
  refine (iInf_le (fun Ψ => risk 1 1 0 Ψ) (fun y => y (1 : Fin 2))).trans ?_
  refine iSup_le fun a => iSup_le fun y => iSup_le fun hy => ?_
  have hh : |y (1 : Fin 2) - a.val ^ (1 : ℕ)| ≤ (0 : ℝ) := hy (1 : Fin 2)
  simpa using ENNReal.ofReal_le_ofReal hh

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finite_power_extrapolation_risk, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨1, 1⟩, (0 : ℝ), (1 : ℝ), ?_⟩
    change minimaxRisk 1 1 0 ≠ minimaxRisk 1 1 1
    rw [noiseless_risk]
    have hl := (finite_power_extrapolation_risk 1 1 le_rfl le_rfl 1 zero_lt_one).1.1
    have hp : 0 < minimaxRisk 1 1 1 := lt_of_lt_of_le (by norm_num) hl
    exact (ne_of_gt hp).symm

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Estimation.DecisionRisk.FinitePowerExtrapolationRisk.finite_power_extrapolation_risk) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ p η => minimaxRisk p.1 p.2 η) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Estimation") "DecisionRisk") "FinitePowerExtrapolationRisk") "finite_power_extrapolation_risk") "Reg.D5.S3.Estimation.DecisionRisk.FinitePowerExtrapolationRisk/Reg.D5.S3.Estimation.DecisionRisk.FinitePowerExtrapolationRisk.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Estimation.DecisionRisk.FinitePowerExtrapolationRisk.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ p η => minimaxRisk p.1 p.2 η) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Estimation.DecisionRisk.FinitePowerExtrapolationRisk, definition := none, coordinates := #[0, 1], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


#print axioms registration

end
end Reg.D5.S3.Estimation.DecisionRisk.FinitePowerExtrapolationRisk
