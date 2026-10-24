import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTailL2
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail
open LeanInformationAudit

namespace Reg.D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTailL2

abbrev signature : Signature where
  Params := ℝ → ℂ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ u t => ∫ x : ℝ in Ioi t, ‖u x‖ ^ 2)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {k : ℝ} (_hk : 0 < k)
      (u : ℝ → ℂ) (_hu : MemLp u 2 (volume.restrict (Ioi 0)))
      (t : ℝ) (_ht : 0 ≤ t),
    Integrable (fun s : ℝ => (Real.exp (-k * s) : ℂ) * u (t + s))
        (volume.restrict (Ioi 0)) ∧
      ‖rightExponentialTail k u t‖ ^ 2 ≤ (1 / (2 * k)) * r.readout () u t

private theorem source_reconstruction :
    (type_of% (@right_exponential_tail_l2_integrable_and_sq_le)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hh := hall (k := 1) (by norm_num) (fun _ : ℝ => (0 : ℂ)) MemLp.zero'
    0 (by norm_num)
  have hbad := hh.2
  norm_num [rejected, realize, rightExponentialTail] at hbad

private def indicatorInput : ℝ → ℂ :=
  (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ))

private theorem indicator_mass_zero :
    (∫ x : ℝ in Ioi 0, ‖indicatorInput x‖ ^ 2) = 1 := by
  have heq : (fun x : ℝ => ‖indicatorInput x‖ ^ 2) =
      (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ Ioc (0 : ℝ) 1 <;> simp [indicatorInput, hx]
  rw [heq, setIntegral_indicator measurableSet_Ioc,
    inter_eq_right.mpr Ioc_subset_Ioi_self, setIntegral_const]
  norm_num

private theorem indicator_mass_one :
    (∫ x : ℝ in Ioi 1, ‖indicatorInput x‖ ^ 2) = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hnot : x ∉ Ioc (0 : ℝ) 1 := fun h => (not_le_of_gt hx) h.2
  simp [indicatorInput, hnot]

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨indicatorInput, (0 : ℝ), (1 : ℝ), ?_⟩
  change (∫ x : ℝ in Ioi 0, ‖indicatorInput x‖ ^ 2) ≠
    ∫ x : ℝ in Ioi 1, ‖indicatorInput x‖ ^ 2
  rw [indicator_mass_zero, indicator_mass_one]
  norm_num

def familyRegistration : Registration arena
    (type_of% (@right_exponential_tail_l2_integrable_and_sq_le)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@right_exponential_tail_l2_integrable_and_sq_le, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- Six original binders k,hk,u,hu,t,ht. The selected actual mass occurs in
the integrability-and-bound conjunction's right conjunct, then the right side
of the inequality, then the right factor of scalar multiplication. Original
u binder 2 is the parameter; later original t binder 4 is the state. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@right_exponential_tail_l2_integrable_and_sq_le)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail.right_exponential_tail_l2_integrable_and_sq_le.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTailL2.familyRegistration
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
    (fun _ u t => ∫ x : ℝ in Ioi t, ‖u x‖ ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTailL2
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end Reg.D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTailL2
