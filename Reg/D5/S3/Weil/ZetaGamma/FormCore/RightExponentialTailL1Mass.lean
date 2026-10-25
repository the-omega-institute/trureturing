/- Faithful source registrations: original telescopes, actual outer-tail
integrability and literal mass identities are retained in full. -/
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTailL1Mass
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail
open LeanInformationAudit

namespace Reg.D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTailL1Mass

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

private def indicatorInput : ℝ → ℂ :=
  (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ))

private theorem indicator_mass :
    (∫ t : ℝ in Ioi 0, indicatorInput t) = 1 := by
  rw [indicatorInput, setIntegral_indicator measurableSet_Ioc,
    inter_eq_right.mpr Ioc_subset_Ioi_self, setIntegral_const]
  norm_num

def actual : Realization signature :=
  realize signature (fun _ _ u => u) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => indicatorInput) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {k : ℝ} (_hk : 0 < k) (u : ℝ → ℂ)
      (_hu : IntegrableOn u (Ioi (0 : ℝ))),
    IntegrableOn (rightExponentialTail k u) (Ioi (0 : ℝ)) ∧
      (∫ t : ℝ in Ioi 0, rightExponentialTail k u t) =
        ((k⁻¹ : ℝ) : ℂ) *
          ((∫ t : ℝ in Ioi 0, r.readout () () u t) - rightExponentialTail k u 0)

private theorem source_reconstruction :
    (type_of% (@right_exponential_tail_l1_integrable_and_mass)) ↔ arena.Law actual :=
  Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hh := hall (k := 1) (by norm_num) (fun _ : ℝ => (0 : ℂ)) integrableOn_zero
  have hbad := hh.2
  norm_num [rejected, realize, rightExponentialTail, indicator_mass] at hbad

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ : ℝ => (0 : ℂ)), indicatorInput, ?_⟩
  change (fun _ : ℝ => (0 : ℂ)) ≠ indicatorInput
  intro h
  have hpoint := congrFun h 1
  norm_num [indicatorInput] at hpoint

def familyRegistration : Registration arena
    (type_of% (@right_exponential_tail_l1_integrable_and_mass)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@right_exponential_tail_l1_integrable_and_mass, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- Four original binders k,hk,u,hu. Select the original input function
inside the right-hand input mass. The tail, integrability premise and
endpoint remain literal. No source coordinate is fixed; u is state binder 2. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@right_exponential_tail_l1_integrable_and_mass) (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail.right_exponential_tail_l1_integrable_and_mass.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTailL1Mass.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ u => u)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTailL1Mass
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

namespace Sharp

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
  realize signature (fun _ _ C => C) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {k : ℝ} (_hk : 0 < k) (C : ℝ),
    (∀ (u : ℝ → ℂ), IntegrableOn u (Ioi (0 : ℝ)) →
      (∫ t : ℝ in Ioi 0, ‖rightExponentialTail k u t‖) ≤
        r.readout () () C * ∫ t : ℝ in Ioi 0, ‖u t‖) ↔ k⁻¹ ≤ C

private theorem source_reconstruction :
    (type_of% (@right_exponential_tail_l1_bound_iff)) ↔ arena.Law actual :=
  Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hbad := (hall (k := 1) (by norm_num) 1).mpr (by norm_num)
  have hfalse := (right_exponential_tail_l1_bound_iff
    (k := 1) (by norm_num) (-1)).mp
      (by simpa only [rejected, realize] using hbad)
  norm_num at hfalse

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change (0 : ℝ) ≠ 1
  norm_num

def familyRegistration : Registration arena
    (type_of% (@right_exponential_tail_l1_bound_iff)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@right_exponential_tail_l1_bound_iff, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- The full original k,hk,C telescope remains. The readout is C in the
uniform upper bound, while the opposite iff side retains literal C.
Thus varying the bound cannot silently change the claimed threshold. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@right_exponential_tail_l1_bound_iff) (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail.right_exponential_tail_l1_bound_iff.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTailL1Mass.Sharp.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ C => C) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTailL1Mass
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "body", "body", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end Sharp


end Reg.D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTailL1Mass

