import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.JainAbsCosine.Separation
import Reg.Support.SingleDependentReadout

/-! Source-bound registrations for strict Fourier mode separation. -/

namespace Reg.D5.S3.Quantum.Matrix.JainAbsCosine.Separation
open _root_.D5.S3.Quantum.Matrix.JainAbsCosine.Defs
open _root_.D5.S3.Quantum.Matrix.JainAbsCosine.Separation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

abbrev topSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, ℕ) (fun _ => ℝ) (fun _ => ℝ)

def topActual : Realization topSignature :=
  realize topSignature (fun _ p r => modeValue p.1 p.2 r) (fun e => nomatch e)

def topRejected : Realization topSignature :=
  realize topSignature (fun _ p r => modeValue p.1 0 r) (fun e => nomatch e)

private theorem topDependence : ObservationalDependence topSignature topActual := by
  intro i
  refine ⟨⟨1, 0⟩, 0, 2, ?_⟩
  norm_num [topActual, realize, modeValue, angle, Finset.sum_Icc_succ_top,
    Real.rpow_natCast, Real.cos_pi_div_three]

abbrev topArena : Arena where
  signature := topSignature
  Law R := ∀ {m j : ℕ}, 1 ≤ m → 1 ≤ j → j ≤ m → ∀ r : ℝ,
    R.readout () ⟨m, j⟩ r < modeValue m 0 r

private theorem topRejected_law : ¬ topArena.Law topRejected := by
  intro h
  have he := h (m := 1) (j := 1) (by omega) (by omega) (by omega) 0
  exact (lt_irrefl _) he

abbrev injectiveSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, Σ _ : ℕ, ℕ)
    (fun _ => ℝ) (fun _ => ℝ)

def injectiveActual : Realization injectiveSignature :=
  realize injectiveSignature (fun _ p r => modeValue p.1 p.2.1 r) (fun e => nomatch e)

def injectiveRejected : Realization injectiveSignature :=
  realize injectiveSignature (fun _ p r => modeValue p.1 p.2.2 r) (fun e => nomatch e)

private theorem injectiveDependence :
    ObservationalDependence injectiveSignature injectiveActual := by
  intro i
  refine ⟨⟨1, 0, 0⟩, 0, 2, ?_⟩
  norm_num [injectiveActual, realize, modeValue, angle, Finset.sum_Icc_succ_top,
    Real.rpow_natCast, Real.cos_pi_div_three]

abbrev injectiveArena : Arena where
  signature := injectiveSignature
  Law R := ∀ {m i j : ℕ}, 1 ≤ i → i ≤ m → 1 ≤ j → j ≤ m → ∀ r : ℝ,
    R.readout () ⟨m, i, j⟩ r = modeValue m j r →
      R.readout () ⟨m, i, j⟩ r ≠ 0 → i = j

private theorem injectiveRejected_law : ¬ injectiveArena.Law injectiveRejected := by
  intro h
  have hnonzero : modeValue 2 2 4 ≠ 0 := by
    have hs := _root_.D5.S3.Quantum.Matrix.JainAbsCosine.GapSigns.modeValue_sign
      (m := 2) (j := 2) (by omega) (by omega) 4
    norm_num [rootProduct, Finset.prod_range_succ] at hs
    exact ne_of_gt (sign_eq_one_iff.mp hs)
  have he := h (m := 2) (i := 1) (j := 2) (by omega) (by omega) (by omega)
    (by omega) 4 rfl hnonzero
  omega

def topSource : Registration topArena (type_of% @modeValue_lt_top) where
  actual := topActual
  bridge := Iff.rfl
  variation := ⟨modeValue_lt_top, topRejected, topRejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    topArena.Law topActual topRejected topRejected_law
  dependence := topDependence

def topAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@modeValue_lt_top) (Realization topSignature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.JainAbsCosine.Separation.topUnit
  realizationName := `Reg.D5.S3.Quantum.Matrix.JainAbsCosine.Separation.topSource
  realizationSource := none
  generated := false
  arena := .source ⟨topArena⟩
  objectArena := .source ⟨topArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source topArena ⟨topSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize topSignature (fun _ p r => modeValue p.1 p.2 r)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.JainAbsCosine.Separation
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def injectiveSource : Registration injectiveArena (type_of% @modeValue_injective_nonzero) where
  actual := injectiveActual
  bridge := Iff.rfl
  variation := ⟨modeValue_injective_nonzero, injectiveRejected, injectiveRejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    injectiveArena.Law injectiveActual injectiveRejected injectiveRejected_law
  dependence := injectiveDependence

def injectiveAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@modeValue_injective_nonzero) (Realization injectiveSignature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.JainAbsCosine.Separation.injectiveUnit
  realizationName := `Reg.D5.S3.Quantum.Matrix.JainAbsCosine.Separation.injectiveSource
  realizationSource := none
  generated := false
  arena := .source ⟨injectiveArena⟩
  objectArena := .source ⟨injectiveArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source injectiveArena ⟨injectiveSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize injectiveSignature (fun _ p r => modeValue p.1 p.2.1 r)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.JainAbsCosine.Separation
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "domain", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Matrix.JainAbsCosine.Separation
