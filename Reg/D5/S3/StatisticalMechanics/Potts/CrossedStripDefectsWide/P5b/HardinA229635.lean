import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! The literal array count is the observation at each recurrence index. -/

namespace Reg.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635

open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635 (result)
open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635Residual (coefficients)
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229637RowColumn (T)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)

private def actual : Realization signature :=
  realize signature (fun _ _ n => (T n 6 : ℤ)) (fun e => nomatch e)

private def shifted : Realization signature :=
  realize signature (fun _ _ n => (T n 6 : ℤ) + 1) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ), 31 ≤ n →
    R.readout () () n = ∑ j : Fin 27, coefficients j * (T (n - (j.val + 1)) 6 : ℤ)

private theorem rejected : ¬ arena.Law shifted := by
  intro h
  have wrong := h 31 (by omega)
  have right := result 31 (by omega)
  change (T 31 6 : ℤ) + 1 = _ at wrong
  omega

private theorem empty_count : T 0 6 = 0 := by
  unfold T
  decide +kernel

private theorem positive_count : 0 < T 1 6 := by
  unfold T
  apply Finset.card_pos.mpr
  refine ⟨(fun x => ![0, 0, 0, 1, 0, 1] x.2), ?_⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, by decide +kernel⟩

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, shifted, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual shifted rejected
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (T 0 6 : ℤ) ≠ (T 1 6 : ℤ)
    exact_mod_cast (show T 0 6 ≠ T 1 6 by rw [empty_count]; exact Nat.ne_of_lt positive_count)

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.HardinA229635.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (T n 6 : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635
