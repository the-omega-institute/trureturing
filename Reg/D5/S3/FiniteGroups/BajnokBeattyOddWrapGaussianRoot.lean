import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot
import Reg.D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

/-! Faithful source registrations for exactly the two functional
GaussianRoot theorems `gaussian_secant` and `gaussian_strictMonoOn`.

Both registrations use Params := Unit, the native real argument as the full
state space, Role := Unit, real output, and Empty anchors.  The actual sole
readout is the complete source function `gaussian`; the rejected sole readout
is the zero function on every real state.  Thus no auxiliary state or
observable is introduced.  The two Laws retain every source restriction and
the full real domain exactly.

The source-occurrence binding remains unfinished under
https://github.com/the-omega-institute/trureturing/issues/25856 . These are
typed source records; source binding evidence is assessed separately.  The four
other public Root scalar theorems are not covered by these two functional
templates; the native-family templates below handle those four targets.
-/

namespace Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot

open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

abbrev gaussianRootFunctionalSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def gaussianSecantActual : Realization gaussianRootFunctionalSignature :=
  realize gaussianRootFunctionalSignature
    (fun _ _ s => gaussian s)
    (fun e => nomatch e)

noncomputable def gaussianSecantRejected : Realization gaussianRootFunctionalSignature :=
  realize gaussianRootFunctionalSignature
    (fun _ _ _ => 0)
    (fun e => nomatch e)

abbrev gaussianSecantArena : Arena where
  signature := gaussianRootFunctionalSignature
  Law R := ∀ {a b : ℝ},
    (2 / 3 : ℝ) ≤ a → a ≤ b →
      R.readout () () a + (98 / 75 : ℝ) * (b - a) ≤ R.readout () () b

private theorem gaussianSecant_actual_bridge :
    (type_of% (@gaussian_secant)) ↔
      gaussianSecantArena.Law gaussianSecantActual := Iff.rfl

private theorem gaussianSecant_actual_law :
    gaussianSecantArena.Law gaussianSecantActual :=
  gaussianSecant_actual_bridge.mp (@gaussian_secant)

private theorem gaussianSecant_rejected_law :
    ¬ gaussianSecantArena.Law gaussianSecantRejected := by
  intro h
  have hh := h (a := (2 / 3 : ℝ)) (b := (1 : ℝ)) (by norm_num) (by norm_num)
  change (0 : ℝ) + (98 / 75 : ℝ) * (1 - 2 / 3) ≤ 0 at hh
  norm_num at hh

private theorem gaussianSecant_actual_dependence :
    ObservationalDependence gaussianRootFunctionalSignature gaussianSecantActual := by
  intro i
  refine ⟨(), (2 / 3 : ℝ), (1 : ℝ), ?_⟩
  change gaussian (2 / 3 : ℝ) ≠ gaussian 1
  have h : gaussian (2 / 3 : ℝ) < gaussian 1 :=
    gaussian_strictMonoOn (by norm_num [Set.mem_Ici])
      (by norm_num [Set.mem_Ici]) (by norm_num)
  exact ne_of_lt h

noncomputable def gaussianSecantSource :
    Registration gaussianSecantArena (type_of% (@gaussian_secant)) where
  actual := gaussianSecantActual
  bridge := gaussianSecant_actual_bridge
  variation := ⟨gaussianSecant_actual_law,
    gaussianSecantRejected, gaussianSecant_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨gaussianSecantRejected, ?_, rfl, gaussianSecant_rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := gaussianSecant_actual_dependence

noncomputable def gaussianSecantRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@gaussian_secant)
      (Realization gaussianRootFunctionalSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot.gaussian_secant.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot.gaussianSecantSource
  realizationSource := none
  generated := false
  arena := .source ⟨gaussianSecantArena⟩
  objectArena := .source ⟨gaussianSecantArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source gaussianSecantArena ⟨gaussianSecantSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize gaussianRootFunctionalSignature
    (fun _ _ s => gaussian s)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def gaussianStrictMonoOnActual :
    Realization gaussianRootFunctionalSignature :=
  realize gaussianRootFunctionalSignature
    (fun _ _ s => gaussian s)
    (fun e => nomatch e)

noncomputable def gaussianStrictMonoOnRejected :
    Realization gaussianRootFunctionalSignature :=
  realize gaussianRootFunctionalSignature
    (fun _ _ _ => 0)
    (fun e => nomatch e)

abbrev gaussianStrictMonoOnArena : Arena where
  signature := gaussianRootFunctionalSignature
  Law R := StrictMonoOn (fun s : ℝ => R.readout () () s)
    (Set.Ici (2 / 3 : ℝ))

private theorem gaussianStrictMonoOn_actual_bridge :
    (type_of% gaussian_strictMonoOn) ↔
      gaussianStrictMonoOnArena.Law gaussianStrictMonoOnActual := Iff.rfl

private theorem gaussianStrictMonoOn_actual_law :
    gaussianStrictMonoOnArena.Law gaussianStrictMonoOnActual :=
  gaussianStrictMonoOn_actual_bridge.mp gaussian_strictMonoOn

private theorem gaussianStrictMonoOn_rejected_law :
    ¬ gaussianStrictMonoOnArena.Law gaussianStrictMonoOnRejected := by
  intro h
  have hh := h (by norm_num [Set.mem_Ici]) (by norm_num [Set.mem_Ici])
    (by norm_num : (2 / 3 : ℝ) < 1)
  change (0 : ℝ) < 0 at hh
  linarith

private theorem gaussianStrictMonoOn_actual_dependence :
    ObservationalDependence gaussianRootFunctionalSignature
      gaussianStrictMonoOnActual := by
  intro i
  refine ⟨(), (2 / 3 : ℝ), (1 : ℝ), ?_⟩
  change gaussian (2 / 3 : ℝ) ≠ gaussian 1
  have h : gaussian (2 / 3 : ℝ) < gaussian 1 :=
    gaussian_strictMonoOn (by norm_num [Set.mem_Ici])
      (by norm_num [Set.mem_Ici]) (by norm_num)
  exact ne_of_lt h

noncomputable def gaussianStrictMonoOnSource :
    Registration gaussianStrictMonoOnArena (type_of% gaussian_strictMonoOn) where
  actual := gaussianStrictMonoOnActual
  bridge := gaussianStrictMonoOn_actual_bridge
  variation := ⟨gaussianStrictMonoOn_actual_law,
    gaussianStrictMonoOnRejected, gaussianStrictMonoOn_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨gaussianStrictMonoOnRejected, ?_, rfl,
        gaussianStrictMonoOn_rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := gaussianStrictMonoOn_actual_dependence

noncomputable def gaussianStrictMonoOnRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@gaussian_strictMonoOn)
      (Realization gaussianRootFunctionalSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot.gaussian_strictMonoOn.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot.gaussianStrictMonoOnSource
  realizationSource := none
  generated := false
  arena := .source ⟨gaussianStrictMonoOnArena⟩
  objectArena := .source ⟨gaussianStrictMonoOnArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source gaussianStrictMonoOnArena ⟨gaussianStrictMonoOnSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize gaussianRootFunctionalSignature
    (fun _ _ s => gaussian s)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot

/-! Faithful native-family registrations for the four scalar
GaussianRoot targets. The equation observes the whole original `gaussian`
function on all real states. The three inequalities observe their original
native real predicates, with the original scalar as the Law's state.
Each predicate bridge is exactly the original statement's equivalence to
its Boolean readout being true; no extra proposition is conjoined.

All signatures have Unit parameters, real states, one Unit role, and no
anchors. The equation's rejected family is the whole zero function, whose
Law would assert 0 = 2. The predicates' rejected family is the whole false
function, whose Law would assert false = true. Actual equation dependence
uses the existing `gaussian_strictMonoOn` at 2/3 and 1. Predicate dependence
uses the actual predicate values at real states 0 and 1.

Every sourceSelection and familyRecord remains none; every continuation
is unknown. Source-occurrence binding remains unfinished under
https://github.com/the-omega-institute/trureturing/issues/25856 .
No declared_validated binding is claimed. The lawful `realize` enrollment is imported through
Reg.Support.SingleDependentReadout; no enrollment or judge is changed.
-/

namespace Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot

open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

abbrev gaussianRootEquationSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℝ) (fun _ => ℝ)

noncomputable def gaussianRootEquationActual :
    Realization gaussianRootEquationSignature :=
  realize gaussianRootEquationSignature (fun _ _ => gaussian) (fun e => nomatch e)

noncomputable def gaussianRootEquationRejected :
    Realization gaussianRootEquationSignature :=
  realize gaussianRootEquationSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev gaussianRootEquationArena : Arena where
  signature := gaussianRootEquationSignature
  Law R := R.readout () () s_star = 2

private theorem gaussianRootEquation_actual_bridge :
    (type_of% gaussian_s_star) ↔
      gaussianRootEquationArena.Law gaussianRootEquationActual := Iff.rfl

private theorem gaussianRootEquation_actual_law :
    gaussianRootEquationArena.Law gaussianRootEquationActual :=
  gaussianRootEquation_actual_bridge.mp gaussian_s_star

private theorem gaussianRootEquation_rejected_law :
    ¬ gaussianRootEquationArena.Law gaussianRootEquationRejected := by
  intro h
  change (0 : ℝ) = 2 at h
  norm_num at h

private theorem gaussianRootEquation_actual_dependence :
    ObservationalDependence gaussianRootEquationSignature gaussianRootEquationActual := by
  intro i
  refine ⟨(), (2 / 3 : ℝ), (1 : ℝ), ?_⟩
  change gaussian (2 / 3 : ℝ) ≠ gaussian 1
  have h : gaussian (2 / 3 : ℝ) < gaussian 1 :=
    gaussian_strictMonoOn (by norm_num [Set.mem_Ici])
      (by norm_num [Set.mem_Ici]) (by norm_num)
  exact ne_of_lt h

noncomputable def gaussianRootEquationSource : Registration gaussianRootEquationArena
    (type_of% gaussian_s_star) where
  actual := gaussianRootEquationActual
  bridge := gaussianRootEquation_actual_bridge
  variation := ⟨gaussianRootEquation_actual_law,
    gaussianRootEquationRejected, gaussianRootEquation_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    gaussianRootEquationArena.Law gaussianRootEquationActual gaussianRootEquationRejected
    gaussianRootEquation_rejected_law
  dependence := gaussianRootEquation_actual_dependence

noncomputable def gaussianRootEquationRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@gaussian_s_star)
      (Realization gaussianRootEquationSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot.gaussian_s_star.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot.gaussianRootEquationSource
  realizationSource := none
  generated := false
  arena := .source ⟨gaussianRootEquationArena⟩
  objectArena := .source ⟨gaussianRootEquationArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source gaussianRootEquationArena ⟨gaussianRootEquationSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize gaussianRootEquationSignature
    (fun _ _ => gaussian) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev gaussianRootScalarSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℝ) (fun _ => Bool)

noncomputable def gaussianRootScalarRejected :
    Realization gaussianRootScalarSignature :=
  realize gaussianRootScalarSignature (fun _ _ _ => false) (fun e => nomatch e)

noncomputable def gaussianRootScalarTwoThirdsActual :
    Realization gaussianRootScalarSignature :=
  realize gaussianRootScalarSignature
    (fun _ _ x => @decide ((2 / 3 : ℝ) < x) (Classical.propDecidable _))
    (fun e => nomatch e)

abbrev gaussianRootScalarTwoThirdsArena : Arena where
  signature := gaussianRootScalarSignature
  Law R := R.readout () () s_star = true

private theorem gaussianRootScalarTwoThirds_actual_bridge :
    (type_of% two_thirds_lt_s_star) ↔
      gaussianRootScalarTwoThirdsArena.Law gaussianRootScalarTwoThirdsActual := by
  simp [gaussianRootScalarTwoThirdsArena, gaussianRootScalarTwoThirdsActual, realize,
    decide_eq_true_eq]

private theorem gaussianRootScalarTwoThirds_actual_law :
    gaussianRootScalarTwoThirdsArena.Law gaussianRootScalarTwoThirdsActual :=
  gaussianRootScalarTwoThirds_actual_bridge.mp two_thirds_lt_s_star

private theorem gaussianRootScalarTwoThirds_rejected_law :
    ¬ gaussianRootScalarTwoThirdsArena.Law gaussianRootScalarRejected := by
  intro h
  change false = true at h
  exact Bool.false_ne_true h

private theorem gaussianRootScalarTwoThirds_actual_dependence :
    ObservationalDependence gaussianRootScalarSignature gaussianRootScalarTwoThirdsActual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  change @decide ((2 / 3 : ℝ) < 0) (Classical.propDecidable _) ≠
    @decide ((2 / 3 : ℝ) < 1) (Classical.propDecidable _)
  norm_num

noncomputable def gaussianRootScalarTwoThirdsSource :
    Registration gaussianRootScalarTwoThirdsArena (type_of% two_thirds_lt_s_star) where
  actual := gaussianRootScalarTwoThirdsActual
  bridge := gaussianRootScalarTwoThirds_actual_bridge
  variation := ⟨gaussianRootScalarTwoThirds_actual_law,
    gaussianRootScalarRejected, gaussianRootScalarTwoThirds_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    gaussianRootScalarTwoThirdsArena.Law gaussianRootScalarTwoThirdsActual
    gaussianRootScalarRejected gaussianRootScalarTwoThirds_rejected_law
  dependence := gaussianRootScalarTwoThirds_actual_dependence

noncomputable def gaussianRootScalarTwoThirdsRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@two_thirds_lt_s_star)
      (Realization gaussianRootScalarSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot.two_thirds_lt_s_star.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot.gaussianRootScalarTwoThirdsSource
  realizationSource := none
  generated := false
  arena := .source ⟨gaussianRootScalarTwoThirdsArena⟩
  objectArena := .source ⟨gaussianRootScalarTwoThirdsArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source gaussianRootScalarTwoThirdsArena ⟨gaussianRootScalarTwoThirdsSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize gaussianRootScalarSignature
    (fun _ _ x => @decide ((2 / 3 : ℝ) < x) (Classical.propDecidable _))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def gaussianRootScalarAlphaLowerActual :
    Realization gaussianRootScalarSignature :=
  realize gaussianRootScalarSignature
    (fun _ _ x => @decide ((24 / 25 : ℝ) < x) (Classical.propDecidable _))
    (fun e => nomatch e)

abbrev gaussianRootScalarAlphaLowerArena : Arena where
  signature := gaussianRootScalarSignature
  Law R := R.readout () () alpha = true

private theorem gaussianRootScalarAlphaLower_actual_bridge :
    (type_of% alpha_gt_twentyfour_twentyfive) ↔
      gaussianRootScalarAlphaLowerArena.Law gaussianRootScalarAlphaLowerActual := by
  simp [gaussianRootScalarAlphaLowerArena, gaussianRootScalarAlphaLowerActual, realize,
    decide_eq_true_eq]

private theorem gaussianRootScalarAlphaLower_actual_law :
    gaussianRootScalarAlphaLowerArena.Law gaussianRootScalarAlphaLowerActual :=
  gaussianRootScalarAlphaLower_actual_bridge.mp alpha_gt_twentyfour_twentyfive

private theorem gaussianRootScalarAlphaLower_rejected_law :
    ¬ gaussianRootScalarAlphaLowerArena.Law gaussianRootScalarRejected := by
  intro h
  change false = true at h
  exact Bool.false_ne_true h

private theorem gaussianRootScalarAlphaLower_actual_dependence :
    ObservationalDependence gaussianRootScalarSignature gaussianRootScalarAlphaLowerActual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  change @decide ((24 / 25 : ℝ) < 0) (Classical.propDecidable _) ≠
    @decide ((24 / 25 : ℝ) < 1) (Classical.propDecidable _)
  norm_num

noncomputable def gaussianRootScalarAlphaLowerSource :
    Registration gaussianRootScalarAlphaLowerArena
      (type_of% alpha_gt_twentyfour_twentyfive) where
  actual := gaussianRootScalarAlphaLowerActual
  bridge := gaussianRootScalarAlphaLower_actual_bridge
  variation := ⟨gaussianRootScalarAlphaLower_actual_law,
    gaussianRootScalarRejected, gaussianRootScalarAlphaLower_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    gaussianRootScalarAlphaLowerArena.Law gaussianRootScalarAlphaLowerActual
    gaussianRootScalarRejected gaussianRootScalarAlphaLower_rejected_law
  dependence := gaussianRootScalarAlphaLower_actual_dependence

noncomputable def gaussianRootScalarAlphaLowerRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@alpha_gt_twentyfour_twentyfive)
      (Realization gaussianRootScalarSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot.alpha_gt_twentyfour_twentyfive.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot.gaussianRootScalarAlphaLowerSource
  realizationSource := none
  generated := false
  arena := .source ⟨gaussianRootScalarAlphaLowerArena⟩
  objectArena := .source ⟨gaussianRootScalarAlphaLowerArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source gaussianRootScalarAlphaLowerArena ⟨gaussianRootScalarAlphaLowerSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize gaussianRootScalarSignature
    (fun _ _ x => @decide ((24 / 25 : ℝ) < x) (Classical.propDecidable _))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def gaussianRootScalarAlphaUpperActual :
    Realization gaussianRootScalarSignature :=
  realize gaussianRootScalarSignature
    (fun _ _ x => @decide (x < (1 : ℝ)) (Classical.propDecidable _))
    (fun e => nomatch e)

abbrev gaussianRootScalarAlphaUpperArena : Arena where
  signature := gaussianRootScalarSignature
  Law R := R.readout () () alpha = true

private theorem gaussianRootScalarAlphaUpper_actual_bridge :
    (type_of% alpha_lt_one) ↔
      gaussianRootScalarAlphaUpperArena.Law gaussianRootScalarAlphaUpperActual := by
  simp [gaussianRootScalarAlphaUpperArena, gaussianRootScalarAlphaUpperActual, realize,
    decide_eq_true_eq]

private theorem gaussianRootScalarAlphaUpper_actual_law :
    gaussianRootScalarAlphaUpperArena.Law gaussianRootScalarAlphaUpperActual :=
  gaussianRootScalarAlphaUpper_actual_bridge.mp alpha_lt_one

private theorem gaussianRootScalarAlphaUpper_rejected_law :
    ¬ gaussianRootScalarAlphaUpperArena.Law gaussianRootScalarRejected := by
  intro h
  change false = true at h
  exact Bool.false_ne_true h

private theorem gaussianRootScalarAlphaUpper_actual_dependence :
    ObservationalDependence gaussianRootScalarSignature gaussianRootScalarAlphaUpperActual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  change @decide ((0 : ℝ) < 1) (Classical.propDecidable _) ≠
    @decide ((1 : ℝ) < 1) (Classical.propDecidable _)
  norm_num

noncomputable def gaussianRootScalarAlphaUpperSource :
    Registration gaussianRootScalarAlphaUpperArena (type_of% alpha_lt_one) where
  actual := gaussianRootScalarAlphaUpperActual
  bridge := gaussianRootScalarAlphaUpper_actual_bridge
  variation := ⟨gaussianRootScalarAlphaUpper_actual_law,
    gaussianRootScalarRejected, gaussianRootScalarAlphaUpper_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    gaussianRootScalarAlphaUpperArena.Law gaussianRootScalarAlphaUpperActual
    gaussianRootScalarRejected gaussianRootScalarAlphaUpper_rejected_law
  dependence := gaussianRootScalarAlphaUpper_actual_dependence

noncomputable def gaussianRootScalarAlphaUpperRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@alpha_lt_one)
      (Realization gaussianRootScalarSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot.alpha_lt_one.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot.gaussianRootScalarAlphaUpperSource
  realizationSource := none
  generated := false
  arena := .source ⟨gaussianRootScalarAlphaUpperArena⟩
  objectArena := .source ⟨gaussianRootScalarAlphaUpperArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source gaussianRootScalarAlphaUpperArena ⟨gaussianRootScalarAlphaUpperSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize gaussianRootScalarSignature
    (fun _ _ x => @decide (x < (1 : ℝ)) (Classical.propDecidable _))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot
