import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiMeanZeroTrace
import D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiFiniteGammaEnergy
import D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiFiniteMeanZeroWitness
import Reg.Support.DependentFamily
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
open D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample.Symbol
open D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiFiniteGammaEnergy
open D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail
open LeanInformationAudit

namespace Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiMeanZeroTrace

private theorem zero_source_h6 :
    originalPhysicalH6 (fun _ : ℝ => (0 : ℂ)) := by
  constructor
  · exact MemLp.zero'
  · simp

private theorem zero_actual_profile :
    actualGammaProfile (fun _ : ℝ => (0 : ℂ)) = fun _ : ℝ => (0 : ℂ) := by
  funext t
  simp [actualGammaProfile, fullTheta, physicalTerm]

private theorem zero_actual_mean :
    (∫ r : ℝ, actualSuzukiEvenBProfile (fun _ : ℝ => (0 : ℂ)) r) = 0 := by
  simp [actualSuzukiEvenBProfile, actualSuzukiBProfile,
    zero_actual_profile, rightExponentialTail]

namespace Moments

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
  realize signature (fun _ _ F => ∫ x : ℝ in Ioi Real.pi,
    ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖fullTheta F x‖ ^ 2)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

/- The readout is the fullTheta excess D; both L1 clauses, both moments,
all three estimates and the actual mean-zero hypothesis are retained. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (F : ℝ → ℂ) (_hF : originalPhysicalH6 F)
      (_hmean : (∫ r : ℝ, actualSuzukiEvenBProfile F r) = 0),
    let L0 := ∫ t : ℝ in Ioi 0,
      (Real.exp (-(5 / 4 : ℝ) * t) : ℂ) * actualGammaProfile F t
    let Lt := ∫ t : ℝ in Ioi 0,
      ((t * Real.exp (-(5 / 4 : ℝ) * t) : ℝ) : ℂ) * actualGammaProfile F t
    let D := r.readout () () F
    IntegrableOn (fun t : ℝ => (Real.exp (-(5 / 4 : ℝ) * t) : ℂ) *
      actualGammaProfile F t) (Ioi (0 : ℝ)) ∧
      IntegrableOn (fun t : ℝ => ((t * Real.exp (-(5 / 4 : ℝ) * t) : ℝ) : ℂ) *
        actualGammaProfile F t) (Ioi (0 : ℝ)) ∧
      ‖L0‖ ^ 2 ≤ (3 / 1000 : ℝ) * Real.pi ^ (7 / 2 : ℝ) * D ∧
      ‖Lt‖ ^ 2 ≤ (3 / 160 : ℝ) * Real.pi ^ (7 / 2 : ℝ) * D ∧
      ‖L0‖ * ‖Lt‖ ≤ (3 / 400 : ℝ) * Real.pi ^ (7 / 2 : ℝ) * D

private theorem source_reconstruction :
    (type_of% (@actual_h6_mean_zero_physical_moment_bounds)) ↔
      arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hbad := (hall (fun _ : ℝ => (0 : ℂ)) zero_source_h6 zero_actual_mean).2.2.1
  have hnegative : (0 : ℝ) ≤
      (3 / 1000 : ℝ) * Real.pi ^ (7 / 2 : ℝ) * (-1 : ℝ) := by
    simpa [rejected, realize, zero_actual_profile] using hbad
  have hpositive : 0 < Real.pi ^ (7 / 2 : ℝ) :=
    Real.rpow_pos_of_pos Real.pi_pos _
  nlinarith only [hnegative, hpositive]

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨F, _hF, _hmean, _hGamma, _hHasSum, _hOriginal, hTheta⟩ :=
    actual_h6_mean_zero_positive_fullTheta_excess_all_gamma_domains
  refine ⟨(), (fun _ : ℝ => (0 : ℂ)), F, ?_⟩
  change (∫ x : ℝ in Ioi Real.pi,
      ((x / Real.pi) ^ (6 : ℕ) - 1) *
        ‖fullTheta (fun _ : ℝ => (0 : ℂ)) x‖ ^ 2) ≠
    ∫ x : ℝ in Ioi Real.pi,
      ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖fullTheta F x‖ ^ 2
  have hzero : (∫ x : ℝ in Ioi Real.pi,
      ((x / Real.pi) ^ (6 : ℕ) - 1) *
        ‖fullTheta (fun _ : ℝ => (0 : ℂ)) x‖ ^ 2) = 0 := by
    simp [fullTheta, physicalTerm]
  rw [hzero]
  exact ne_of_lt hTheta

def familyRegistration : Registration arena
    (type_of% (@actual_h6_mean_zero_physical_moment_bounds)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@actual_h6_mean_zero_physical_moment_bounds, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- Raw source path: three forall bodies F,hF,hmean,
then the L0 and Lt let bodies, then D's value. The integral lambda is NOT
entered. F is lexical binder 0; no parameter coordinates are fixed. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_h6_mean_zero_physical_moment_bounds)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample.actual_h6_mean_zero_physical_moment_bounds.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiMeanZeroTrace.Moments.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ F => ∫ x : ℝ in Ioi Real.pi,
    ((x / Real.pi) ^ (6 : ℕ) - 1) * ‖fullTheta F x‖ ^ 2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiMeanZeroTrace
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end Moments

namespace ProfileDomains

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ F => actualGammaProfile F) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (fun _ : ℝ => (1 : ℂ))) (fun e => nomatch e)

/- The readout is the profile in the L1 clause; the original H6 premise
and the actual-profile MemLp clause are retained. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (F : ℝ → ℂ) (_hF : originalPhysicalH6 F),
    IntegrableOn (r.readout () () F) (Ioi (0 : ℝ)) ∧
      MemLp (actualGammaProfile F) 2 (volume.restrict (Ioi (0 : ℝ)))

private theorem source_reconstruction :
    (type_of% (@actual_h6_gamma_profile_l1_l2)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hbad := (hall (fun _ : ℝ => (0 : ℂ)) zero_source_h6).1
  change IntegrableOn (fun _ : ℝ => (1 : ℂ)) (Ioi (0 : ℝ)) at hbad
  simpa [integrableOn_const_iff, Real.volume_Ioi] using hbad

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨F, _hF, _hreal, _hHasSum, _hGamma, _hmass, _hcap, henergy, _hsequence⟩ :=
    actual_h6_finite_gamma_energy_unbounded (2 : ℝ) (0 : ℝ) (by norm_num)
  refine ⟨(), (fun _ : ℝ => (0 : ℂ)), F, ?_⟩
  change actualGammaProfile (fun _ : ℝ => (0 : ℂ)) ≠ actualGammaProfile F
  rw [zero_actual_profile]
  intro heq
  have hp : actualGammaProfile F = fun _ : ℝ => (0 : ℂ) := heq.symm
  rw [hp] at henergy
  norm_num [unitarySourceFourier_eq_integral] at henergy

def familyRegistration : Registration arena
    (type_of% (@actual_h6_gamma_profile_l1_l2)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@actual_h6_gamma_profile_l1_l2, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- Raw source path: F,hF bodies; And's first argument; IntegrableOn's
function argument (two trailing explicit arguments: set and measure).
F is lexical binder 0. No integral or pointwise state is introduced. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_h6_gamma_profile_l1_l2)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample.actual_h6_gamma_profile_l1_l2.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiMeanZeroTrace.ProfileDomains.familyRegistration
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
    (fun _ _ F => actualGammaProfile F) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiMeanZeroTrace
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end ProfileDomains
end Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiMeanZeroTrace
