import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaGamma.FormCore.CarlemanL2
import Reg.Support.DependentFamily
import Mathlib.Tactic.NormNum

/-!
# Full source registration for the actual Carleman L2 domain

The actual positive-half-line L2 mass is selected once in each complete
source law. Actual absolute integrability and the complete Carleman
integral bound remain in the law. Binding evidence is supplied by the canonical scoped report.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Weil.ZetaGamma.FormCore.CarlemanL2
open LeanInformationAudit

namespace Reg.D5.S3.Weil.ZetaGamma.FormCore.CarlemanL2

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
  realize signature (fun _ _ u => ∫ s : ℝ, ‖u s‖ ^ 2 ∂halfline)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

private def indicatorInput : ℝ → ℂ :=
  (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ))

private theorem indicator_mass :
    (∫ s : ℝ, ‖indicatorInput s‖ ^ 2 ∂halfline) = 1 := by
  have heq : (fun s : ℝ => ‖indicatorInput s‖ ^ 2) =
      (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) := by
    funext s
    by_cases hs : s ∈ Ioc (0 : ℝ) 1 <;> simp [indicatorInput, hs]
  rw [heq, setIntegral_indicator measurableSet_Ioc,
    inter_eq_right.mpr Ioc_subset_Ioi_self, setIntegral_const]
  norm_num

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ : ℝ => (0 : ℂ)), indicatorInput, ?_⟩
  change (∫ s : ℝ, ‖(0 : ℂ)‖ ^ 2 ∂halfline) ≠
    ∫ s : ℝ, ‖indicatorInput s‖ ^ 2 ∂halfline
  rw [indicator_mass]
  simp

namespace Carleman

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (u : ℝ → ℂ) (_hu : MemLp u 2 halfline),
    Integrable (carlemanAbsolute u) (halfline.prod halfline) ∧
          (∫ z : ℝ × ℝ, carlemanAbsolute u z ∂halfline.prod halfline) ≤
            Real.pi * r.readout () () u

private theorem source_reconstruction :
    (type_of% (@carleman_actual_l2_domain)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hh := hall (fun _ : ℝ => (0 : ℂ)) MemLp.zero'
  have hbad := hh.2
  norm_num [rejected, realize, carlemanAbsolute] at hbad <;>
    nlinarith [Real.pi_pos]

def familyRegistration : Registration arena
    (type_of% (@carleman_actual_l2_domain)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@carleman_actual_l2_domain, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- Full original telescope: 2 binders. The sole selected occurrence
is the actual L2 mass in the first absolute-integral bound. All other
conjuncts are retained verbatim, including the original final form bound.
The original profile u is state binder 0; no source coordinate is fixed.
The readout path below selects this original mass occurrence. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@carleman_actual_l2_domain) (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.ZetaGamma.FormCore.CarlemanL2.carleman_actual_l2_domain.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.CarlemanL2.Carleman.familyRegistration
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
    (fun _ _ u => ∫ s : ℝ, ‖u s‖ ^ 2 ∂halfline) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.CarlemanL2
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end Carleman

end Reg.D5.S3.Weil.ZetaGamma.FormCore.CarlemanL2
