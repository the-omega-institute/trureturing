import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaRecurrence
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the bounded continuant endpoint formula. -/

namespace Reg.D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaRecurrence
open _root_.D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaRecurrence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the sequence at its endpoint; the entire sequence is a parameter. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (ℕ → ℝ) (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ y N => y N) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (N : ℕ) (_hN : 1 ≤ N) (t : ℝ) (y : ℕ → ℝ)
    (_hy : ∀ j, j + 2 ≤ N → y (j + 2) = t * y (j + 1) - y j),
    R.readout () y N =
      ((Polynomial.Chebyshev.S ℝ ((N : ℤ) - 1)).eval t) * y 1 -
        ((Polynomial.Chebyshev.S ℝ ((N : ℤ) - 2)).eval t) * y 0

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 1 (by omega) 0 (fun _ => 0) (by intro j hj; omega)
  norm_num [rejected, realize] at hb

theorem dependence : ObservationalDependence signature actual := by
  intro r
  refine ⟨(fun n => (n : ℝ)), 0, 1, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena (type_of% @bounded_continuant_endpoint) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨bounded_continuant_endpoint, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@bounded_continuant_endpoint) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaRecurrence.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaRecurrence.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ y N => y N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaRecurrence
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Combinatorics.SpectralGraph.TwinFreeThetaRecurrence
