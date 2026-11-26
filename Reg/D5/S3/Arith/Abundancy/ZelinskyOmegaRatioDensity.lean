import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Abundancy.ZelinskyOmegaRatioDensity
import Reg.Support.SingleDependentReadout

/-! The complete parameter family of the Euler-form relative lower bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Abundancy.StrongPseudoperfectEulerDensity
open _root_.D5.S3.Arith.Abundancy.ZelinskyOmegaRatioDensity

namespace Reg.D5.S3.Arith.Abundancy.ZelinskyOmegaRatioDensity

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ α β : ℝ, ∃ c : ℝ, 0 < c ∧
    ∀ᶠ X : ℕ in atTop, R.readout () () (c * (eulerCount X : ℝ)) (orCount α β X)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨c, hc, hbound⟩ := h 0 0
  obtain ⟨X, hX⟩ := hbound.exists
  exact hX

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hh := congrFun he (0 : ℝ)
  change ((0 : ℝ) ≤ 0) = ((1 : ℝ) ≤ 0) at hh
  have hbad : (1 : ℝ) ≤ 0 := Eq.mp hh le_rfl
  norm_num at hbad

def family : Registration arena (type_of% @relative_density_pos) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨relative_density_pos, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@relative_density_pos) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Abundancy.ZelinskyOmegaRatioDensity.relative_density_pos.audit
  realizationName := `Reg.D5.S3.Arith.Abundancy.ZelinskyOmegaRatioDensity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Abundancy.ZelinskyOmegaRatioDensity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace EulerUpper

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ)
    (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
    R.readout () () (eulerCount X : ℝ) (C * ((X : ℝ) / Real.log X))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨c, hc, hbound⟩ := h
  obtain ⟨X, hX⟩ := hbound.exists
  exact hX

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hh := congrFun he (0 : ℝ)
  change ((0 : ℝ) ≤ 0) = ((1 : ℝ) ≤ 0) at hh
  have hbad : (1 : ℝ) ≤ 0 := Eq.mp hh le_rfl
  norm_num at hbad

def family : Registration arena (type_of% @euler_count_upper) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨euler_count_upper, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@euler_count_upper) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Abundancy.ZelinskyOmegaRatioDensity.euler_count_upper.audit
  realizationName := `Reg.D5.S3.Arith.Abundancy.ZelinskyOmegaRatioDensity.EulerUpper.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Abundancy.ZelinskyOmegaRatioDensity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end EulerUpper

end Reg.D5.S3.Arith.Abundancy.ZelinskyOmegaRatioDensity
