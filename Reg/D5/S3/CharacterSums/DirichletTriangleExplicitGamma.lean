import D5.S3.CharacterSums.DirichletTriangleExplicitGamma
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source-aligned observations of the parity corrections and their transforms. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Complex Filter Topology
open scoped Classical
open _root_.D5.S3.CharacterSums.DirichletTriangleExplicit
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.CharacterSums.DirichletTriangleExplicitGamma

local instance sourceMeasurableSpace : MeasurableSpace ℝ :=
  Real.measureSpace.toMeasurableSpace

namespace Nonnegative
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x => fun y : ℝ => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ : ℝ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (y : ℝ), R.readout () () 0 (evenT y)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 0
  exact he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h (0 : ℝ)
  norm_num [actual, realize] at he

def family : Registration arena (type_of% @evenT_nonneg) where
  actual := actual
  bridge := by simp only [arena, actual, realize]
  variation := ⟨by simpa only [arena, actual, realize]
      using @evenT_nonneg, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@evenT_nonneg) (Realization signature) Unit Unit where
  unitName := (`D5.S3.CharacterSums.DirichletTriangleExplicit.evenT_nonneg).str
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletTriangleExplicitGamma.Nonnegative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ x => fun y : ℝ => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletTriangleExplicitGamma
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Nonnegative

namespace Mass
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x => fun y : ℝ => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ : ℝ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {y : ℝ} (hy : 0 ≤ y),
    Summable (fun n : ℕ => evenCoeff n * Real.exp (-(2 * ((n : ℝ) + 1)) * y)) ∧
      evenT 0 = Real.log 2 ∧ R.readout () () (evenT y) (Real.log 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (y := 0) le_rfl
  exact he.2.2

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h (0 : ℝ)
  norm_num [actual, realize] at he

def family : Registration arena (type_of% @evenT_le_mass) where
  actual := actual
  bridge := by simp only [arena, actual, realize]
  variation := ⟨by simpa only [arena, actual, realize]
      using @evenT_le_mass, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@evenT_le_mass) (Realization signature) Unit Unit where
  unitName := (`D5.S3.CharacterSums.DirichletTriangleExplicit.evenT_le_mass).str
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletTriangleExplicitGamma.Mass.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ x => fun y : ℝ => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletTriangleExplicitGamma
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Mass

namespace Endpoint
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    Unit (fun _ => ℂ) (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ _ z => @decide (z = 0) (Classical.propDecidable _)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {q : ℕ} (χ : DirichletCharacter ℂ q),
    R.readout () () (parityCorrection χ 1) = true

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (1 : DirichletCharacter ℂ 1)
  change false = true at he
  cases he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def family : Registration arena (type_of% @parityCorrection_one) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq]
      using @parityCorrection_one, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@parityCorrection_one) (Realization signature) Unit Unit where
  unitName := (`D5.S3.CharacterSums.DirichletTriangleExplicit.parityCorrection_one).str
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletTriangleExplicitGamma.Endpoint.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ z => @decide (z = 0) (Classical.propDecidable _)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletTriangleExplicitGamma
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Endpoint

namespace Continuity
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ y => Real.exp y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ y => if y = 0 then 1 else 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {q : ℕ} (χ : DirichletCharacter ℂ q),
    ContinuousOn (fun y : ℝ => parityCorrection χ (R.readout () () y)) (Ici 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let χ : DirichletCharacter ℂ 1 := 1
  have hχ : χ.Even := by
    change (1 : DirichletCharacter ℂ 1) (-1) = 1
    exact MulChar.one_apply isUnit_neg_one
  have he := congrArg Complex.re (parityCorrection_one χ)
  have heT : evenT 0 = Real.log 2 := by
    have hg : (Real.log 2 - evenT 0 : ℝ) = 0 := by
      simpa [parityCorrection, hχ, Complex.log_re] using he
    linarith
  have hc := (h χ) 0 (by simp)
  simp only [ContinuousWithinAt, rejected, realize, if_pos rfl] at hc
  change Tendsto (fun y : ℝ => parityCorrection χ (if y = 0 then 1 else 0))
    (𝓝[Ici 0] 0) (𝓝 (parityCorrection χ 1)) at hc
  rw [parityCorrection_one] at hc
  have hc' := hc.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)
  have hz : (fun y : ℝ => parityCorrection χ (if y = 0 then 1 else 0)) =ᶠ[𝓝[>] 0]
      (fun _ => ((1 - Real.log 2 : ℝ) : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    change 0 < y at hy
    simp [ne_of_gt hy, parityCorrection, hχ, heT]
  have hlim : Tendsto (fun y : ℝ => parityCorrection χ (if y = 0 then 1 else 0))
      (𝓝[>] 0) (𝓝 ((1 - Real.log 2 : ℝ) : ℂ)) :=
    (tendsto_congr' hz).2 tendsto_const_nhds
  have hzero := congrArg Complex.re (tendsto_nhds_unique hc' hlim)
  norm_num [Complex.log_re] at hzero
  linarith [Real.log_two_lt_d9]

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change Real.exp 0 ≠ Real.exp 1
  exact Real.exp_injective.ne (by norm_num)

def family : Registration arena (type_of% @parityCorrection_continuousOn) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq]
      using @parityCorrection_continuousOn, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@parityCorrection_continuousOn) (Realization signature) Unit Unit where
  unitName := (`D5.S3.CharacterSums.DirichletTriangleExplicit.parityCorrection_continuousOn).str
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletTriangleExplicitGamma.Continuity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ y => Real.exp y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletTriangleExplicitGamma
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Continuity

namespace ExpIntegrable
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    Unit (fun _ => ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ z => Complex.exp z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {s : ℂ} (hs : 0 < s.re),
    IntegrableOn (fun y : ℝ => R.readout () () (-s * y)) (Ioi 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (s := 1) (by norm_num)
  change IntegrableOn (fun _ : ℝ => (1 : ℂ)) (Ioi 0) at he
  simpa [IntegrableOn, integrable_const_iff, isFiniteMeasure_iff] using he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, (Real.log 2 : ℂ), ?_⟩
  change Complex.exp 0 ≠ Complex.exp (Real.log 2 : ℂ)
  rw [Complex.exp_zero, ← Complex.ofReal_exp,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

def family : Registration arena (type_of% @exp_integrable) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq]
      using @exp_integrable, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exp_integrable) (Realization signature) Unit Unit where
  unitName := (`D5.S3.CharacterSums.DirichletTriangleExplicit.exp_integrable).str
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletTriangleExplicitGamma.ExpIntegrable.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ z => Complex.exp z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletTriangleExplicitGamma
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn", "arg", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ExpIntegrable

namespace ExpIntegral
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    Unit (fun _ => ℝ → ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ f => ∫ y : ℝ in Ioi 0, f y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ f => (∫ y : ℝ in Ioi 0, f y) + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {s : ℂ} (hs : 0 < s.re),
    R.readout () () (fun y : ℝ => Complex.exp (-s * y)) = 1 / s

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (s := 1) (by norm_num)
  change _ + 1 = 1 / (1 : ℂ) at he
  rw [exp_integral (by norm_num : 0 < (1 : ℂ).re)] at he
  norm_num at he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun y : ℝ => Complex.exp ((-1 : ℂ) * y)), ?_⟩
  change (∫ y : ℝ in Ioi 0, (0 : ℂ)) ≠
    ∫ y : ℝ in Ioi 0, Complex.exp ((-1 : ℂ) * y)
  rw [integral_zero, integral_exp_mul_complex_Ioi (by norm_num)]
  norm_num

def family : Registration arena (type_of% @exp_integral) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq]
      using @exp_integral, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exp_integral) (Realization signature) Unit Unit where
  unitName := (`D5.S3.CharacterSums.DirichletTriangleExplicit.exp_integral).str
    "__information_unit"
  realizationName := `Reg.D5.S3.CharacterSums.DirichletTriangleExplicitGamma.ExpIntegral.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ f => ∫ y : ℝ in Ioi 0, f y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletTriangleExplicitGamma
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ExpIntegral

namespace CorrectionIntegrable
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    Unit (fun _ => ℂ) (fun _ => ℂ → ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ z => fun w : ℂ => z * w) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ : ℂ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re),
    IntegrableOn (fun y : ℝ => R.readout () () (Complex.exp (-s * y))
      (parityCorrection χ (Real.exp y))) (Ioi 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (1 : DirichletCharacter ℂ 1) (s := 1) (by norm_num)
  change IntegrableOn (fun _ : ℝ => (1 : ℂ)) (Ioi 0) at he
  simpa [IntegrableOn, integrable_const_iff, isFiniteMeasure_iff] using he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h (1 : ℂ)
  norm_num [actual, realize] at he

def family : Registration arena (type_of% @parityCorrection_laplace_integrable) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq]
      using @parityCorrection_laplace_integrable, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@parityCorrection_laplace_integrable)
      (Realization signature) Unit Unit where
  unitName := ((`D5.S3.CharacterSums.DirichletTriangleExplicit).str
    "parityCorrection_laplace_integrable").str "__information_unit"
  realizationName := ((`Reg.D5.S3.CharacterSums.DirichletTriangleExplicitGamma).str
    "CorrectionIntegrable").str "family"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ z => fun w : ℂ => z * w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletTriangleExplicitGamma
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn", "arg", "body", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CorrectionIntegrable

namespace CorrectionIntegral
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    Unit (fun _ => ℝ → ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ f => ∫ y : ℝ in Ioi 0, f y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ f => (∫ y : ℝ in Ioi 0, f y) + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {q : ℕ} (χ : DirichletCharacter ℂ q) {t : ℝ} (ht : t ≠ 0),
    R.readout () () (fun y : ℝ => Complex.exp (-transformLine t * y) *
      parityCorrection χ (Real.exp y)) =
        (Complex.digamma ((transformLine t + parity χ) / 2) -
          Complex.digamma ((2 + parity χ) / 2)) /
            (2 * transformLine t * (transformLine t + 1))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (1 : DirichletCharacter ℂ 1) (t := 1) (by norm_num)
  have hf := parityCorrection_laplace (1 : DirichletCharacter ℂ 1)
    (t := 1) (by norm_num)
  change _ + 1 = _ at he
  rw [hf] at he
  have hz : (1 : ℂ) = 0 := by linear_combination he
  exact one_ne_zero hz

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun y : ℝ => Complex.exp ((-1 : ℂ) * y)), ?_⟩
  change (∫ y : ℝ in Ioi 0, (0 : ℂ)) ≠
    ∫ y : ℝ in Ioi 0, Complex.exp ((-1 : ℂ) * y)
  rw [integral_zero, integral_exp_mul_complex_Ioi (by norm_num)]
  norm_num

def family : Registration arena (type_of% @parityCorrection_laplace) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq]
      using @parityCorrection_laplace, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@parityCorrection_laplace) (Realization signature) Unit Unit where
  unitName := (`D5.S3.CharacterSums.DirichletTriangleExplicit.parityCorrection_laplace).str
    "__information_unit"
  realizationName := ((`Reg.D5.S3.CharacterSums.DirichletTriangleExplicitGamma).str
    "CorrectionIntegral").str "family"
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ f => ∫ y : ℝ in Ioi 0, f y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.CharacterSums.DirichletTriangleExplicitGamma
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CorrectionIntegral

end Reg.D5.S3.CharacterSums.DirichletTriangleExplicitGamma
