import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import D5.S3.StatisticalMechanics.Potts.ChangShrockToroidalHoneycomb
import D5.S3.StatisticalMechanics.Potts.ChangShrockToroidalSquare
import Reg.Support.DependentFamily
import Mathlib.Algebra.MvPolynomial.Eval

/-! Source-bound observation of the native square transfer action. -/

namespace Reg.D5.S3.StatisticalMechanics.Potts.ChangShrockToroidalSquare

open _root_.D5.S3.StatisticalMechanics.Potts.ChangShrockToroidalHoneycomb (Coeff Space v q)
open _root_.D5.S3.StatisticalMechanics.Potts.ChangShrockToroidalSquare
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev Width := {L : ℕ // 2 ≤ L}

theorem positiveWidth (p : Width) : NeZero p.val := ⟨by have := p.property; omega⟩
abbrev Fiber (p : Width) := @Space p.val (positiveWidth p)
def operator (p : Width) : Module.End Coeff (Fiber p) := @transfer p.val (positiveWidth p)

def eigenvalue (L : ℕ) : Coeff := v ^ (L - 1) * (v + q)

abbrev signature : Signature where
  Params := Width
  State := Fiber
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fiber p
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p w => operator p w) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev SourceClaim : Prop :=
  ∀ (L : ℕ) (hL : 2 ≤ L),
    letI : NeZero L := ⟨by omega⟩
    ∃ w : Space L, w ≠ 0 ∧ transfer L w = eigenvalue L • w

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (L : ℕ) (hL : 2 ≤ L),
    ∃ w : Fiber ⟨L, hL⟩, w ≠ 0 ∧
      r.readout () ⟨L, hL⟩ w = eigenvalue L • w

private theorem eigenvalue_two_ne_zero : eigenvalue 2 ≠ 0 := by
  intro h
  have hh := congrArg (MvPolynomial.eval (fun _ : Fin 2 => (1 : ℤ)) : Coeff → ℤ) h
  norm_num [eigenvalue, v, q] at hh

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨w, hw, he⟩ := h 2 (by decide)
  change (0 : Fiber ⟨2, by decide⟩) = eigenvalue 2 • w at he
  exact hw ((smul_eq_zero.mp he.symm).resolve_left eigenvalue_two_ne_zero)

theorem dependence : ObservationalDependence signature actual := by
  intro r
  have hresult := @result 2 (by decide)
  obtain ⟨w, hw, he⟩ := hresult
  refine ⟨⟨2, by decide⟩, 0, w, ?_⟩
  change @transfer 2 (positiveWidth ⟨2, by decide⟩) 0 ≠
    @transfer 2 (positiveWidth ⟨2, by decide⟩) w
  change transfer 2 0 ≠ transfer 2 w
  rw [map_zero, he]
  exact (smul_ne_zero eigenvalue_two_ne_zero hw).symm

def source_registration : Registration arena SourceClaim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro r
      exact ⟨rejected, fun s hs => (hs (Subsingleton.elim s r)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.StatisticalMechanics.Potts.ChangShrockToroidalSquare.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.StatisticalMechanics.Potts.ChangShrockToroidalSquare.unit
  realizationName :=
    `Reg.D5.S3.StatisticalMechanics.Potts.ChangShrockToroidalSquare.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p w => operator p w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.ChangShrockToroidalSquare
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.StatisticalMechanics.Potts.ChangShrockToroidalSquare
