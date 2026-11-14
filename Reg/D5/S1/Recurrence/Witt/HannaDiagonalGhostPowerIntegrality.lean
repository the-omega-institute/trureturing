import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality
import Reg.Support.SingleDependentReadout

/-! The Fermat difference readout retains every prime, natural lift exponent and integer base. -/

namespace Reg.D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality
open _root_.D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℕ × ℕ)
    (fun _ => ℤ) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ ps z => z ^ (ps.1 ^ (ps.2 + 1)) - z ^ (ps.1 ^ ps.2)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ p s : ℕ, p.Prime → ∀ z : ℤ, (p : ℤ) ^ (s + 1) ∣ R.readout () (p, s) z

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 2 0 (by norm_num) 0
  norm_num [rejected, realize] at hh

def family : Registration arena (type_of% fermat_lift) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fermat_lift, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(2, 0), 0, 2, ?_⟩
    norm_num [actual, realize]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    fermat_lift (Realization signature) Unit Unit where
  unitName := `Reg.D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality.auditUnit
  realizationName := `Reg.D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ ps z => z ^ (ps.1 ^ (ps.2 + 1)) - z ^ (ps.1 ^ ps.2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S1.Recurrence.Witt.HannaDiagonalGhostPowerIntegrality
