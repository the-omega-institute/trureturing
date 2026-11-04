import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Constants.Irrationality.LogNaturalIrrationality
import Reg.Support.SingleDependentReadout

/-!
# Whole-family logarithm irrationality registration

The source theorem quantifies over every natural n at least two. The arena has
one role and the whole natural-number state space; the actual readout is log n.
The zero intervention fails at n = 2, and actual observations at 2 and 3 differ.

Source selection and continuation remain unresolved. In particular this registration
does not assert source-binding acceptance; issue25856 is the existing global
source-binding limitation. The typed family evidence below supplies no missing
source reconstruction or binding receipt.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Constants.Irrationality.LogNaturalIrrationality

open _root_.D5.S3.Constants.Irrationality.LogNaturalIrrationality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ n => Real.log (n : ℝ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ), 2 ≤ n → Irrational (R.readout () () n)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 2 (by omega)
  change Irrational (0 : ℝ) at hbad
  exact not_irrational_zero hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 2, 3, ?_⟩
  change Real.log (2 : ℝ) ≠ Real.log (3 : ℝ)
  intro h
  have heq : (2 : ℝ) = 3 :=
    Real.log_injOn_pos (by norm_num) (by norm_num) h
  norm_num at heq

def source_registration :
    Registration arena (type_of% @irrational_log_natCast) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨irrational_log_natCast, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

/-- Source registration with explicitly unresolved source selection.
The evidence correspondence is the typed family bridge, not binding acceptance. -/
def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@irrational_log_natCast) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Constants.Irrationality.LogNaturalIrrationality.unit
  realizationName :=
    `Reg.D5.S3.Constants.Irrationality.LogNaturalIrrationality.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => Real.log (n : ℝ))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Constants.Irrationality.LogNaturalIrrationality
