import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.NoncommutingQubit.PetzTangentArcsine
import Reg.Support.SingleDependentReadout

/-! Source-bound readouts of the exact arcsine integral as a function of its node. -/

namespace Reg.D5.S3.Quantum.Recovery.NoncommutingQubit.PetzTangentArcsine

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Recovery.PetzTangentArcsine

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Even

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => arcIntegral (kernel x)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ x : ℝ, 0 < x → R.readout () () x = 1 / x

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h := h 1 one_pos
  norm_num [rejected, realize] at h

def source_registration : Registration arena (type_of% @arcsine_even_moment) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨arcsine_even_moment, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (1 : ℝ), (2 : ℝ), ?_⟩
    change arcIntegral (kernel 1) ≠ arcIntegral (kernel 2)
    rw [arcsine_even_moment 1 one_pos, arcsine_even_moment 2 (by norm_num)]
    norm_num

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Recovery.PetzTangentArcsine.arcsine_even_moment)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Recovery.NoncommutingQubit.PetzTangentArcsine.Even.unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.NoncommutingQubit.PetzTangentArcsine.Even.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => arcIntegral (kernel x)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.NoncommutingQubit.PetzTangentArcsine
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end Even

namespace Odd

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ x g => arcIntegral (fun z => z^2 * kernel x z * kernel g z)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ x g : ℝ, 0 < x → 0 < g → g * R.readout () x g = 1 / (x * (x + g))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h := h 1 1 one_pos one_pos
  norm_num [rejected, realize] at h

def source_registration : Registration arena (type_of% @arcsine_odd_node_moment) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨arcsine_odd_node_moment, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), ?_⟩
    change arcIntegral (fun z => z^2 * kernel 1 z * kernel 1 z) ≠
      arcIntegral (fun z => z^2 * kernel 1 z * kernel 2 z)
    have h₁ := arcsine_odd_node_moment 1 1 one_pos one_pos
    have h₂ := arcsine_odd_node_moment 1 2 one_pos (by norm_num)
    intro he
    rw [he] at h₁
    linarith only [h₁, h₂]

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Recovery.PetzTangentArcsine.arcsine_odd_node_moment)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Recovery.NoncommutingQubit.PetzTangentArcsine.Odd.unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.NoncommutingQubit.PetzTangentArcsine.Odd.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ x g => arcIntegral (fun z => z^2 * kernel x z * kernel g z)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.NoncommutingQubit.PetzTangentArcsine
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end Odd

end
end Reg.D5.S3.Quantum.Recovery.NoncommutingQubit.PetzTangentArcsine
