import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Laplace.CriticalGammaWindow
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Real Set Filter
open _root_.D5.S3.Analytic.Laplace.CriticalGammaWindow
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Analytic.Laplace.CriticalGammaWindow

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℕ)

/-- The integer moment order selected from the real cutoff. -/
def actual : Realization signature :=
  realize signature (fun _ _ a => ⌊640*a⌋₊) (fun e => nomatch e)

def zeroOrder : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {a : ℝ} (ha : 1 ≤ a) {g : ℝ → ℝ} (hg : Measurable g)
    {M : ℝ} (hM : ∀ u, 0 ≤ u → |g u| ≤ M * exp (2*u)),
    let k := V.readout () () a
    let f := fun u : ℝ => |g u| * (u ^ k * exp (-(512*u)) / k.factorial)
    let S := Ioi (0:ℝ) \ Icc a (3*a/2)
    a ≤ (k:ℝ) ∧ IntegrableOn f S ∧
      (∫ u in S, f u) ≤ M * (1/542 + 1/478) * (512:ℝ)⁻¹ ^ k

private theorem zero_fails : ¬ arena.Law zeroOrder := by
  intro h
  have h0 : ∀ u : ℝ, 0 ≤ u → |(fun _ : ℝ => (0 : ℝ)) u| ≤ 1 * exp (2*u) := by
    intro u _
    simpa only [abs_zero, one_mul] using (Real.exp_pos (2*u)).le
  have hs := (h (a := 1) le_rfl (g := fun _ : ℝ => (0 : ℝ)) measurable_const (M := 1) h0).1
  change (1 : ℝ) ≤ (0 : ℕ) at hs
  norm_num at hs

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), (1:ℝ), (2:ℝ), ?_⟩
  change ⌊640*(1:ℝ)⌋₊ ≠ ⌊640*(2:ℝ)⌋₊
  norm_num

def family : Registration arena (type_of% @critical_window_off_mass) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@critical_window_off_mass, zeroOrder, zero_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual zeroOrder zero_fails
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@critical_window_off_mass) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.Analytic.Laplace.CriticalGammaWindow.critical_window_off_mass
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.Analytic.Laplace.CriticalGammaWindow "family"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ a => ⌊640*a⌋₊) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Laplace.CriticalGammaWindow
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Adjustable

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ h σ => σ*(h*log h-h+1)-2) (fun e => nomatch e)

def zeroDecay : Realization signature :=
  realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law V := ∀ {h b : ℝ}, 1 < h → h < b →
    let L := V.readout () () h
    let R := fun σ : ℝ => σ*(b-h-h*log (b/h))-2*b
    (∀ T : ℝ, ∀ᶠ σ : ℝ in Filter.atTop, 2 < σ*(1-h/b) ∧ T < L σ ∧ T < R σ) ∧
    ∀ {σ : ℝ}, 2 < σ*(1-h/b) → ∀ {a : ℝ}, 0 < a → ∀ {g : ℝ → ℝ}, Measurable g →
      ∀ {M : ℝ}, (∀ u, 0 ≤ u → |g u| ≤ M * exp (2*u)) →
      let k := ⌊σ*h*a⌋₊
      let f := fun u : ℝ => |g u| * (u ^ k * exp (-(σ*u)) / k.factorial)
      let S := Ioi (0:ℝ) \ Icc a (b*a)
      IntegrableOn f S ∧ (∫ u in S, f u) ≤ M * σ⁻¹ ^ k *
        (exp (-L σ*a) / σ + b/(h*σ)*exp (-R σ*a))

private theorem zero_fails : ¬ arena.Law zeroDecay := by
  intro law
  have ev := (law (h := 2) (b := 3) (by norm_num) (by norm_num)).1 0
  rcases ev.exists with ⟨σ, _, bad, _⟩
  exact lt_irrefl (0 : ℝ) bad

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), exp 1, exp 2, ?_⟩
  intro heq
  have he := congrFun heq 1
  change 1*(exp 1*log (exp 1)-exp 1+1)-2 = 1*(exp 2*log (exp 2)-exp 2+1)-2 at he
  simp only [log_exp] at he
  linarith [exp_pos (2 : ℝ)]

def family : Registration arena (type_of% @adjustable_window_off_mass) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@adjustable_window_off_mass, zeroDecay, zero_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual zeroDecay zero_fails
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@adjustable_window_off_mass) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.Analytic.Laplace.CriticalGammaWindow.adjustable_window_off_mass
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.Analytic.Laplace.CriticalGammaWindow.Adjustable "family"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ h σ => σ*(h*log h-h+1)-2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Laplace.CriticalGammaWindow
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Adjustable

namespace MomentIntegrable

abbrev sig : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ)
    (fun _ => Set ℝ → Measure ℝ → Prop)

def actual : Realization sig :=
  realize sig (fun _ _ f S μ => IntegrableOn f S μ) (fun e => nomatch e)

def rejected : Realization sig :=
  realize sig (fun _ _ _ _ _ => False) (fun e => nomatch e)

def arena : Arena where
  signature := sig
  Law V := ∀ (k : ℕ) {r : ℝ}, 0 < r → V.readout () () (moment k r) (Ioi 0) volume

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  exact h 0 (r := 1) zero_lt_one

private theorem dependence : ObservationalDependence sig actual := by
  intro _
  refine ⟨(), (fun _ : ℝ => (0 : ℝ)), (fun _ : ℝ => (1 : ℝ)), ?_⟩
  intro h
  have he := congrFun (congrFun h (Ici (0 : ℝ))) volume
  have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ici (0 : ℝ)) := by
    change IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ici (0 : ℝ)) =
      IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ici (0 : ℝ)) at he
    rw [← he]
    simp
  simpa [integrableOn_const_iff, Real.volume_Ici] using hi

def family : Registration arena (type_of% @moment_integrable) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@moment_integrable, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@moment_integrable) (Realization sig) Unit Unit where
  unitName := .str
    `D5.S3.Analytic.Laplace.CriticalGammaWindow.moment_integrable
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.Analytic.Laplace.CriticalGammaWindow.MomentIntegrable "family"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Laplace.CriticalGammaWindow
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MomentIntegrable

namespace MomentIntegral

abbrev sig : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ → ℝ) (fun _ => ℝ)

def actual : Realization sig :=
  realize sig (fun _ _ f => ∫ u in Ioi (0 : ℝ), f u) (fun e => nomatch e)

def rejected : Realization sig :=
  realize sig (fun _ _ f => (∫ u in Ioi (0 : ℝ), f u) + 1) (fun e => nomatch e)

def arena : Arena where
  signature := sig
  Law V := ∀ (k : ℕ) {r : ℝ}, 0 < r →
    V.readout () () (moment k r) = r⁻¹ ^ (k+1)

private theorem rejected_fails : ¬ arena.Law rejected := by
  intro h
  have bad := h 0 (r := 1) zero_lt_one
  change (∫ u in Ioi 0, moment 0 1 u) + 1 = _ at bad
  rw [moment_integral 0 zero_lt_one] at bad
  linarith

private theorem dependence : ObservationalDependence sig actual := by
  intro _
  refine ⟨(), (fun _ => 0), moment 0 1, ?_⟩
  change (∫ _ : ℝ in Ioi 0, (0 : ℝ)) ≠ ∫ u in Ioi 0, moment 0 1 u
  rw [integral_zero, moment_integral 0 zero_lt_one]
  norm_num

def family : Registration arena (type_of% @moment_integral) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@moment_integral, rejected, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_fails
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@moment_integral) (Realization sig) Unit Unit where
  unitName := .str
    `D5.S3.Analytic.Laplace.CriticalGammaWindow.moment_integral
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.Analytic.Laplace.CriticalGammaWindow.MomentIntegral "family"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sig actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Laplace.CriticalGammaWindow
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MomentIntegral

end Reg.D5.S3.Analytic.Laplace.CriticalGammaWindow
