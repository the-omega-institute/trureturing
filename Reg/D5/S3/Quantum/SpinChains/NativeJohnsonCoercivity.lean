import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.SpinChains.NativeJohnsonCoercivity
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.SpinChains.NativeJohnsonCoercivity
open _root_.D5.S3.Quantum.SpinChains.NativeJohnsonCoercivity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators InnerProductSpace
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (ℕ × ℕ)
    (fun p => Layer p.1 p.2) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p f => (inner ℂ f (defect p.1 p.2 f)).re)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ N r : ℕ, r ≤ N → ∀ f : Layer N r,
    (N : ℝ) * ‖f - average N r f‖ ^ 2 ≤ R.readout () (N,r) f

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 0 (by omega) 0
  norm_num [rejected, realize] at hh

theorem dependence : ObservationalDependence signature actual := by
  intro i
  let f : Layer 2 1 := WithLp.toLp 2 fun A => if (0 : Fin 2) ∈ A.val then 1 else 0
  let A : Rank 2 1 := ⟨{0}, by decide⟩
  let B : Rank 2 1 := ⟨{1}, by decide⟩
  have hres : f - average 2 1 f ≠ 0 := by
    intro hz
    have he := sub_eq_zero.mp hz
    have ha := congrArg (fun g : Layer 2 1 => g A) he
    have hb := congrArg (fun g : Layer 2 1 => g B) he
    have hab : average 2 1 f A = average 2 1 f B := rfl
    have : (1 : ℂ) = 0 := by simpa [f, A, B] using ha.trans (hab.trans hb.symm)
    exact one_ne_zero this
  have hpos : 0 < (inner ℂ f (defect 2 1 f)).re := by
    have hh := result 2 1 (by omega) f
    have hn := sq_pos_of_pos (norm_pos_iff.mpr hres)
    norm_num at hh
    linarith
  refine ⟨(2,1), 0, f, ?_⟩
  change (inner ℂ (0 : Layer 2 1) (defect 2 1 0)).re ≠
    (inner ℂ f (defect 2 1 f)).re
  simpa using (ne_of_gt hpos).symm

def source_registration : Registration arena
    (∀ N r : ℕ, r ≤ N → ∀ f : Layer N r,
      (N : ℝ) * ‖f - average N r f‖ ^ 2 ≤ (inner ℂ f (defect N r f)).re) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.SpinChains.NativeJohnsonCoercivity.result)
      (Realization signature) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.NativeJohnsonCoercivity.native_energy_unit
  realizationName := `Reg.D5.S3.Quantum.SpinChains.NativeJohnsonCoercivity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p f => (inner ℂ f (defect p.1 p.2 f)).re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.NativeJohnsonCoercivity
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end
end Reg.D5.S3.Quantum.SpinChains.NativeJohnsonCoercivity
