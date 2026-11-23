import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.Qubit.FibonacciClippedProfile

/-! Source-bound audit of the excess profile comparison. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix LeanInformationAudit
open scoped ComplexOrder MatrixOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Divergence.Qubit.SignedProfile
open _root_.D5.S3.Quantum.Divergence.Qubit.FibonacciClippedProfile

namespace Reg.D5.S3.Quantum.Divergence.Qubit.FibonacciClippedProfile

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (ψ : Fin 3 → Fin 2 → ℂ) (_ : ∀ i, star (ψ i) ⬝ᵥ ψ i = 1)
    (i : Fin 6) (t : ℝ) (_ : t ∈ Set.Icc (timeCut i.castSucc) (timeCut i.succ)),
    R.readout () ()
      ((contrast (weights t) ψ)⁺.trace.re - (contrast (weights t) benchmark)⁺.trace.re)
      (envelope i t (1 - overlap ψ 0 1) (overlap ψ 0 2) (overlap ψ 1 2))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hunit (i : Fin 3) : star (benchmark i) ⬝ᵥ benchmark i = 1 := by
    fin_cases i <;> simp [benchmark, dotProduct, Fin.sum_univ_two]
  exact h benchmark hunit 0 (4 / 3) (by
    change (4 / 3 : ℝ) ≤ 4 / 3 ∧ (4 / 3 : ℝ) ≤ 113 / 81
    norm_num)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have h' := congrFun h 0
  change ((0 : ℝ) ≤ 0) = ((1 : ℝ) ≤ 0) at h'
  exact (by norm_num : ¬ (1 : ℝ) ≤ 0) (h'.mp le_rfl)

def family : Registration arena (type_of% @excess_profile_le_envelope) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@excess_profile_le_envelope, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

set_option linter.style.longLine false in
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@excess_profile_le_envelope) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.Qubit.FibonacciClippedProfile.excess_profile_le_envelope.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.Qubit.FibonacciClippedProfile.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.Qubit.FibonacciClippedProfile
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Quantum.Divergence.Qubit.FibonacciClippedProfile
