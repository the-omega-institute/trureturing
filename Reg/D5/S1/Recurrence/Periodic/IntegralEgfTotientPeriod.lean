import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Periodic.IntegralEgfTotientPeriod
import Reg.Support.DependentFamily

noncomputable section
namespace Reg.D5.S1.Recurrence.Periodic.IntegralEgfTotientPeriod
open _root_.D5.S1.Recurrence.Periodic.IntegralEgfTotientPeriod
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ s => (s.1.factorial : ℚ) * coeff s.1 ((exp ℚ - 1) ^ s.2))
    (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ n k : ℕ, R.readout () () (n, k) =
    (k.factorial : ℚ) * (Nat.stirlingSecond n k : ℚ)
private theorem rejected_bad : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 0
  norm_num [rejected, realize] at hh

def family : Registration arena (type_of% exp_shift_power) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exp_shift_power, rejected, rejected_bad⟩
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
    refine ⟨(), (0, 0), (0, 1), ?_⟩
    change ((0 : ℕ).factorial : ℚ) * coeff 0 ((exp ℚ - 1) ^ 0) ≠
      ((0 : ℕ).factorial : ℚ) * coeff 0 ((exp ℚ - 1) ^ 1)
    rw [exp_shift_power, exp_shift_power]
    norm_num

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} exp_shift_power (Realization signature) Unit Unit where
  unitName := Lean.Name.str
    `D5.S1.Recurrence.Periodic.IntegralEgfTotientPeriod.exp_shift_power "__information_unit"
  realizationName := `Reg.D5.S1.Recurrence.Periodic.IntegralEgfTotientPeriod.family
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
end Reg.D5.S1.Recurrence.Periodic.IntegralEgfTotientPeriod
