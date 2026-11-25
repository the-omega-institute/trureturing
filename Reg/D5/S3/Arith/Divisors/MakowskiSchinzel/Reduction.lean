import D5.S3.Arith.Divisors.MakowskiSchinzel.Reduction
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! A source-bound audit of adjoining the prime two to an odd input. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.Reduction

open _root_.D5.S3.Arith.MakowskiSchinzel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => alpha n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : ℕ}, Odd m → R.readout () () (2 * m) = R.readout () () m / 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (m := 1) (by decide)
  norm_num [rejected, realize] at hh

def evidence : Registration arena (type_of% @alpha_two_mul) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@alpha_two_mul, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    norm_num [actual, realize, alpha]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@alpha_two_mul) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.MakowskiSchinzel.alpha_two_mul.__information_unit
  realizationName := `Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.Reduction.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => alpha n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.MakowskiSchinzel.Reduction
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.Reduction
