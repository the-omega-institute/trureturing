import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZeroData.CumulativeRvmError
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Weil.ZeroData.CumulativeRvmError

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZeroData.CumulativeRvmError
open _root_.D5.S3.Weil.ZeroData.ZetaOrdinatePhaseStiffness
open LeanInformationAudit
open Filter

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.log x) (fun e => nomatch e)

def negativeSquare : Realization signature :=
  realize signature (fun _ _ x => -x^2) (fun e => nomatch e)

def positiveSquare : Realization signature :=
  realize signature (fun _ _ x => x^2) (fun e => nomatch e)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (1:ℝ), Real.exp 1, ?_⟩
  simp [actual,realize]

private theorem single_sensitivity (law : Realization signature → Prop)
    (bad : Realization signature) (hbad : ¬law bad) :
    Sensitivity ⟨signature,law⟩ actual := by
  constructor
  · intro i
    refine ⟨bad, ?_, ?_, hbad⟩
    · intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

namespace Cumulative

def arena : Arena where
  signature := signature
  Law R := ∃ U D : ℝ, 1 < U ∧ 0 ≤ D ∧ ∀ Y, U ≤ Y →
    |(Zeta23.Ncount 0 Y : ℝ) -
      (1/(2*Real.pi))*Y*(R.readout () () (Y/(2*Real.pi))-1)| ≤ D*(Real.log Y)^2

private theorem rejected_law : ¬ arena.Law negativeSquare := by
  rintro ⟨U,D,hU,hD,h⟩
  let c : ℝ := 1/(2*Real.pi)
  have hc : 0 < c := by dsimp [c]; positivity
  let Y := max U (max 2 (D/c^3+1))
  have hUY : U ≤ Y := le_max_left _ _
  have hY : 1 < Y := hU.trans_le hUY
  have hY0 : 0 < Y := by linarith
  have hDlt : D < c^3*Y := by
    have hh : D/c^3+1 ≤ Y := (le_max_right 2 _).trans (le_max_right U _)
    have hlt : D/c^3 < Y := by linarith
    have hdiv := (div_lt_iff₀ (show 0 < c^3 by positivity)).mp hlt
    simpa [mul_comm] using hdiv
  have hlog0 : 0 ≤ Real.log Y := Real.log_nonneg hY.le
  have hlog : Real.log Y ≤ Y := by linarith [Real.log_le_sub_one_of_pos hY0]
  have hlogBound : D*(Real.log Y)^2 ≤ D*Y^2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 hlog 2) hD
  have hbound := h Y hUY
  change |(Zeta23.Ncount 0 Y : ℝ) - c*Y*(-(Y/(2*Real.pi))^2-1)| ≤
    D*(Real.log Y)^2 at hbound
  have heq : Y/(2*Real.pi)=c*Y := by dsimp [c]; ring
  rw [heq] at hbound
  have hN : 0 ≤ (Zeta23.Ncount 0 Y : ℝ) := Nat.cast_nonneg _
  have hres : c^3*Y^3 ≤ |(Zeta23.Ncount 0 Y : ℝ)-c*Y*(-(c*Y)^2-1)| := by
    exact (show c^3*Y^3 ≤ (Zeta23.Ncount 0 Y : ℝ)-c*Y*(-(c*Y)^2-1) by
      nlinarith only [hN,mul_nonneg hc.le hY0.le]).trans (le_abs_self _)
  have hh := hres.trans (hbound.trans hlogBound)
  have hmul := mul_lt_mul_of_pos_right hDlt (sq_pos_of_pos hY0)
  nlinarith only [hh,hmul]

def family : Registration arena (type_of% (@cumulative_rvm_error)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cumulative_rvm_error,negativeSquare,rejected_law⟩
  sensitivity := single_sensitivity arena.Law negativeSquare rejected_law
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@cumulative_rvm_error) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.ZeroData.CumulativeRvmError.cumulative_rvm_error.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZeroData.CumulativeRvmError.Cumulative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.log x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZeroData.CumulativeRvmError
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg","body","arg","body","arg","arg","body","body","fn","arg","arg","arg","arg","fn","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Cumulative

namespace ShortWindow

def arena : Arena where
  signature := signature
  Law R := ∃ L K : ℝ, 1 < L ∧ 0 < K ∧ ∀ x y : ℝ,
    L ≤ x → x+K*Real.log x ≤ y → y ≤ 2*x →
    (y-x)*R.readout () () x/(8*Real.pi) ≤ (Zeta23.Ncount x y : ℝ)

private theorem rejected_law : ¬ arena.Law positiveSquare := by
  rintro ⟨L,K,hL,hK,h⟩
  obtain ⟨U,D,hU,hD,hcoarse⟩ := zeta_cumulative_count_coarse
  let c : ℝ := 1/(2*Real.pi)
  have hc : 0 < c := by dsimp [c]; positivity
  have hsmall := Real.isLittleO_log_id_atTop.bound (show 0 < 1/K by positivity)
  obtain ⟨A,hA⟩ := eventually_atTop.1 hsmall
  let x := max (max L U) (max A (max 2 (4*(4*c+2*D)/c+1)))
  have hLx : L ≤ x := (le_max_left L U).trans (le_max_left _ _)
  have hUx : U ≤ x := (le_max_right L U).trans (le_max_left _ _)
  have hAx : A ≤ x := (le_max_left _ _).trans (le_max_right _ _)
  have hx2 : 2 ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hwidth : x+K*Real.log x ≤ 2*x := by
    have hh := hA x hAx
    change ‖Real.log x‖ ≤ (1/K)*‖x‖ at hh
    rw [Real.norm_eq_abs,abs_of_nonneg hlog,Real.norm_eq_abs,abs_of_pos hx0] at hh
    have hmul := mul_le_mul_of_nonneg_left hh hK.le
    have he : K*(1/K*x)=x := by field_simp
    rw [he] at hmul
    linarith
  have hlarge : 4*(4*c+2*D)/c < x := by
    have hh : 4*(4*c+2*D)/c+1 ≤ x :=
      (le_max_right 2 _).trans ((le_max_right _ _).trans (le_max_right _ _))
    linarith
  have hlarge' : 4*(4*c+2*D) < c*x := by
    simpa [mul_comm] using (div_lt_iff₀ hc).mp hlarge
  have hbad := h x (2*x) hLx hwidth le_rfl
  change (2*x-x)*x^2/(8*Real.pi) ≤ (Zeta23.Ncount x (2*x) : ℝ) at hbad
  have hlo : c*x^3/4 ≤ (Zeta23.Ncount x (2*x):ℝ) := by
    convert hbad using 1
    dsimp [c]
    ring
  have hcount : (Zeta23.Ncount x (2*x):ℝ) ≤ (Zeta23.Ncount 0 (2*x):ℝ) := by
    exact_mod_cast Zeta23.Ncount_mono (a := x) (c := 0) hx0.le le_rfl
  have hupper := (abs_le.mp (hcoarse (2*x) (by linarith))).2
  change (Zeta23.Ncount 0 (2*x):ℝ)-c*(2*x)*Real.log (2*x) ≤ D*(2*x) at hupper
  have hlog2 : Real.log (2*x) ≤ 2*x := by linarith [Real.log_le_sub_one_of_pos (by positivity : 0 < 2*x)]
  have hterm := mul_le_mul_of_nonneg_left hlog2 (by positivity : 0 ≤ c*(2*x))
  have hDterm : D*(2*x) ≤ 2*D*x^2 := by
    nlinarith only [mul_nonneg hD (mul_nonneg hx0.le (show 0 ≤ x-1 by linarith))]
  have hhi : (Zeta23.Ncount 0 (2*x):ℝ) ≤ (4*c+2*D)*x^2 := by
    nlinarith only [hupper,hterm,hDterm]
  have hcontr := hlo.trans (hcount.trans hhi)
  have hh := mul_lt_mul_of_pos_right hlarge' (sq_pos_of_pos hx0)
  nlinarith only [hcontr,hh]

def family : Registration arena (type_of% (@short_window_count_lower)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@short_window_count_lower,positiveSquare,rejected_law⟩
  sensitivity := single_sensitivity arena.Law positiveSquare rejected_law
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@short_window_count_lower) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.ZeroData.CumulativeRvmError.short_window_count_lower.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZeroData.CumulativeRvmError.ShortWindow.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.log x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZeroData.CumulativeRvmError
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg","body","arg","body","arg","arg","body","body","body","body","body","fn","arg","fn","arg","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end ShortWindow

end Reg.D5.S3.Weil.ZeroData.CumulativeRvmError
