import D5.S1.Recurrence.Algebraic.HannaA300595Integrality
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! The entire rational source event, with the ordinary coefficient as readout. -/

namespace Reg.D5.S1.Recurrence.Algebraic.HannaA300595Integrality

open _root_.D5.S1.Recurrence.Algebraic.HannaA300595Integrality
open _root_.D5.S1.Recurrence.Algebraic.HannaA300591RationalModel (expSeries)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℕ × PowerSeries ℚ) (fun _ => ℚ)

def actual : Realization signature :=
  realize signature (fun _ _ I => coeff I.1 I.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 / 2 : ℚ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∃! F : PowerSeries ℚ, IsSource F) ∧
    ∀ F : PowerSeries ℚ, IsSource F →
      (∀ m : ℕ, 1 ≤ m → ∃ z : ℤ, R.readout () () (m, F) = (z : ℚ)) ∧
      IsCompanion (expSeries 1 F) ∧ logOf (expSeries 1 F) = F ∧
      (∀ n : ℕ, expSeries ((n : ℚ) ^ 3) F = expSeries 1 F ^ (n ^ 3)) ∧
      (∀ B : PowerSeries ℚ, IsCompanion B → B = expSeries 1 F) ∧
      (mk (fun r =>
        _root_.D5.S1.Recurrence.Residue.IntegralEGFComposition.eCoeff (expSeries 1 F) r /
          (r.factorial : ℚ)) = expSeries 1 F)

private theorem actual_law : arena.Law actual := result

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨F, hF, _⟩ := h.1
  obtain ⟨z, hz⟩ := (h.2 F hF).1 1 (by exact le_rfl)
  change (1 / 2 : ℚ) = (z : ℚ) at hz
  have hd := congrArg Rat.den hz
  norm_num at hd

def family : Registration arena (type_of% result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (0, (0 : PowerSeries ℚ)), (0, (1 : PowerSeries ℚ)), ?_⟩
    norm_num [actual, realize]

/-- Scoped occurrence reconstruction for the full coefficient family remains unresolved. -/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    result (Realization signature) Unit Unit where
  unitName := `D5.S1.Recurrence.Algebraic.HannaA300595Integrality.result.audit
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.HannaA300595Integrality.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ I => coeff I.1 I.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S1.Recurrence.Algebraic.HannaA300595Integrality
