import D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality
open _root_.D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun _ => PowerSeries ℚ) (fun _ => ℚ)
def actual : Realization signature :=
  realize signature (fun _ N f => coeff N f) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1/2) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ f : ℕ → PowerSeries ℤ,
    (∀ p : ℕ, p.Prime → ∀ n : ℕ, n ≠ 0 →
      (p : PowerSeries ℤ)^padicValNat p n ∣
        f n - if p ∣ n then (f (n/p)).subst ((X : PowerSeries ℤ)^p) else 0) →
    ∀ N, ∃ z : ℤ, R.readout () N
      ((exp ℚ).subst (logSum fun n => (f n).map (Int.castRingHom ℚ))) = (z : ℚ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz : ∀ p : ℕ, p.Prime → ∀ n : ℕ, n ≠ 0 →
      (p : PowerSeries ℤ)^padicValNat p n ∣
        (0 : PowerSeries ℤ) - if p ∣ n then (0 : PowerSeries ℤ).subst (X^p) else 0 := by
    intro p hp n hn
    have hz0 : (0 : PowerSeries ℤ).subst ((X : PowerSeries ℤ)^p) = (0 : PowerSeries ℤ) := by
      simpa using (PowerSeries.subst_C (a := (X : PowerSeries ℤ)^p) (0 : ℤ))
    simp [hz0]
  obtain ⟨z,he⟩ := h (fun _ => 0) hz 0
  change (1/2 : ℚ) = (z : ℚ) at he
  have hd := congrArg Rat.den he
  norm_num at hd

def family : Registration arena (type_of% @exp_logSum_integral_of_divisibility) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exp_logSum_integral_of_divisibility, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    change coeff 0 (0 : PowerSeries ℚ) ≠ coeff 0 (1 : PowerSeries ℚ)
    simp

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    exp_logSum_integral_of_divisibility (Realization signature) Unit Unit where
  unitName := `Reg.D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.unit
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S1.Recurrence.Algebraic.HannaSelfSubstitutionIntegrality
