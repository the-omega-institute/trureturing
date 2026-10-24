/- Faithful source registration for the original half-line balance.
The selected readout is exactly the original right-hand-side half-line mass.
The entire original telescope and the literal tail on the left are retained. -/
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail
open LeanInformationAudit

namespace Reg.D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ u => ∫ t : ℝ in Ioi 0, Complex.normSq (u t))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (u : ℝ → ℂ) (_hu : Continuous u) (_hs : HasCompactSupport u) (k c : ℝ),
    (∫ t : ℝ in Ioi 0,
      Complex.normSq (u t - (c : ℂ) * rightExponentialTail k u t)) +
      c * (2 * k - c) *
        (∫ t : ℝ in Ioi 0, Complex.normSq (rightExponentialTail k u t)) +
      c * Complex.normSq (rightExponentialTail k u 0) = r.readout () () u

private theorem source_reconstruction :
    (type_of% (@right_exponential_tail_energy_balance)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hh := hall (fun _ : ℝ => (0 : ℂ)) continuous_const HasCompactSupport.zero 0 0
  have hbad : (0 : ℝ) = -1 := by simpa [rejected, realize] using hh
  norm_num at hbad

private def indicatorInput : ℝ → ℂ :=
  (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ))

private theorem indicator_mass :
    (∫ t : ℝ in Ioi 0, Complex.normSq (indicatorInput t)) = 1 := by
  have heq : (fun t : ℝ => Complex.normSq (indicatorInput t)) =
      (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) := by
    funext t
    by_cases ht : t ∈ Ioc (0 : ℝ) 1 <;> simp [indicatorInput, ht]
  rw [heq, setIntegral_indicator measurableSet_Ioc,
    inter_eq_right.mpr Ioc_subset_Ioi_self, setIntegral_const]
  norm_num

/- The original state type contains every complex-valued function. The
continuity and compact-support conditions remain law premises, not a state
subtype. This computed mass distinguishes two genuine states of that type. -/
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ : ℝ => (0 : ℂ)), indicatorInput, ?_⟩
  change (∫ t : ℝ in Ioi 0, Complex.normSq (0 : ℂ)) ≠
    ∫ t : ℝ in Ioi 0, Complex.normSq (indicatorInput t)
  rw [indicator_mass]
  simp

def familyRegistration : Registration arena
    (type_of% (@right_exponential_tail_energy_balance)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@right_exponential_tail_energy_balance, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- Source occurrence: five original forall binders, then
the right operand of equality. The original u is lexical state binder zero.
No source coordinate is selected; every real k/c stays universally quantified. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@right_exponential_tail_energy_balance) (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail.right_exponential_tail_energy_balance.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail.familyRegistration
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
    (fun _ _ u => ∫ t : ℝ in Ioi 0, Complex.normSq (u t)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end Reg.D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail
