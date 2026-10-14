import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Periodic.ScaledLogColumnPeriodicity
import Reg.Support.DependentFamily

noncomputable section
namespace Reg.D5.S1.Recurrence.Periodic.ScaledLogColumnPeriodicity
open _root_.D5.S1.Recurrence.Periodic.ScaledLogColumnPeriodicity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => coeff n (derivative (R := ℚ) (log ℚ) * (1 + X)))
    (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout () () n = coeff n (1 : PowerSeries ℚ)
private theorem rejected_bad : ¬ arena.Law rejected := by
  intro h
  have hh := h 0
  norm_num [rejected, realize] at hh

def family : Registration arena (type_of% log_derivative_mul) where
  actual := actual
  bridge := by
    constructor
    · intro h n
      exact congrArg (coeff n) h
    · intro h
      ext n
      exact h n
  variation := ⟨by intro n; exact congrArg (coeff n) log_derivative_mul,
    rejected, rejected_bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_bad⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
    change (coeff (R := ℚ) 0 (derivative (R := ℚ) (log ℚ) * (1 + X)) : ℚ) ≠
      coeff (R := ℚ) 1 (derivative (R := ℚ) (log ℚ) * (1 + X))
    erw [log_derivative_mul]
    norm_num

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} log_derivative_mul (Realization signature) Unit Unit where
  unitName := Lean.Name.str
    `D5.S1.Recurrence.Periodic.ScaledLogColumnPeriodicity.log_derivative_mul "__information_unit"
  realizationName := `Reg.D5.S1.Recurrence.Periodic.ScaledLogColumnPeriodicity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S1.Recurrence.Periodic.ScaledLogColumnPeriodicity
