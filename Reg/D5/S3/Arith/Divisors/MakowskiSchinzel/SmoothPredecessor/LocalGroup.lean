import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.LocalGroup
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Exact source bridges for finite rank domination. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.LocalGroup

open _root_.D5.S3.Arith.MakowskiSchinzel
open _root_.D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace finite

abbrev signature : Signature where
  Params := Unit
  State _ := List ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ qs => Certificate.lowerProduct qs) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {qs : List ℕ}, qs.Pairwise (· ≤ ·) →
    ∀ F : Finset ℕ, (∀ q ∈ F, q ∈ qs) →
      R.readout () () (qs.take F.card) ≤
        Certificate.lowerProduct (F.sort (· ≤ ·))

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

private theorem rejected_law : ¬arena.Law rejected := by
  intro h
  have hh := h (qs := []) (by simp) ∅ (by simp)
  norm_num [rejected, realize, Certificate.lowerProduct] at hh

def family : Registration arena (type_of% @finite_subgroup_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_subgroup_bound, rejected, rejected_law⟩
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
    cases i
    refine ⟨(), [], [2], ?_⟩
    norm_num [actual, realize, Certificate.lowerProduct]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_subgroup_bound) (Realization signature) (List ℕ → ℚ) Unit where
  unitName :=
    `D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor.finite_subgroup_bound.__information_unit
  realizationName :=
    `Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.LocalGroup.finite.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ qs => Certificate.lowerProduct qs) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.LocalGroup
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end finite



end Reg.D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.LocalGroup
