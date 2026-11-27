import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Asymptotics.GammaVerticalReciprocalBounds
import Reg.Support.SingleDependentReadout

noncomputable section
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Complex Filter
open scoped Topology BigOperators
namespace Reg.D5.S3.Analytic.Asymptotics.GammaVerticalReciprocalBounds
open _root_.D5.S3.Analytic.Asymptotics.GammaVerticalReciprocalBounds

namespace ProductLower
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ)
    (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ p x => gammaVertProd p x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => (0 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ x y : ℝ, 1 ≤ R.readout () x y
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have := h 1 0
  norm_num [rejected, realize] at this
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  change gammaVertProd 1 0 ≠ gammaVertProd 1 1
  have hs : Summable (fun k : ℕ => (1 : ℝ) / (1 + k) ^ 2) := by
    have h := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa [Nat.cast_add, add_comm] using h
  have hm := Real.multipliable_one_add_of_summable hs
  have hl : 2 ≤ gammaVertProd 1 1 := by
    simp only [gammaVertProd, one_pow]
    apply ge_of_tendsto'
      (hm.hasProd.tendsto_prod_nat.comp (tendsto_add_atTop_nat 1))
    intro n
    dsimp only [Function.comp_def]
    rw [Finset.prod_range_succ']
    have hp : 1 ≤ ∏ k ∈ Finset.range n,
        (1 + (1 : ℝ) / (1 + (k + 1 : ℕ)) ^ 2) := by
      exact Finset.one_le_prod₀ fun k _ => le_add_of_nonneg_right (by positivity)
    norm_num only [Nat.cast_zero, add_zero, one_pow, div_one] at *
    nlinarith
  have h0 : gammaVertProd 1 0 = 1 := by simp [gammaVertProd]
  rw [h0]
  exact ne_of_lt (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hl)

def family : Registration arena (type_of% @one_le_gammaVertProd) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@one_le_gammaVertProd, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@one_le_gammaVertProd) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.Analytic.Asymptotics.GammaVerticalReciprocalBounds.one_le_gammaVertProd
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.Analytic.Asymptotics.GammaVerticalReciprocalBounds.ProductLower.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p x => gammaVertProd p x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Asymptotics.GammaVerticalReciprocalBounds
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ProductLower

namespace GammaNorm
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ)
    (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ x => ‖Complex.Gamma x‖) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ x => (0 : ℝ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {x : ℝ} (_hx : 0 < x) (y : ℝ),
    (R.readout () () (x + I * y)) ^ 2 = Real.Gamma x ^ 2 / gammaVertProd x y
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (x := 1) (by norm_num) 0
  norm_num [rejected, realize, gammaVertProd] at hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]
def family : Registration arena (type_of% @norm_Gamma_sq_eq) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@norm_Gamma_sq_eq, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@norm_Gamma_sq_eq) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.Analytic.Asymptotics.GammaVerticalReciprocalBounds.norm_Gamma_sq_eq
    "__information_unit"
  realizationName := `Reg.D5.S3.Analytic.Asymptotics.GammaVerticalReciprocalBounds.GammaNorm.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => ‖Complex.Gamma x‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Asymptotics.GammaVerticalReciprocalBounds
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end GammaNorm

end Reg.D5.S3.Analytic.Asymptotics.GammaVerticalReciprocalBounds
