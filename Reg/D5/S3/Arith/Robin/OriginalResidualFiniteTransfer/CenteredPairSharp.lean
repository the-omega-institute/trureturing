import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer

open _root_.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
open _root_.D5.S3.Arith.Robin.ActualOddMobiusFinitePairing (mobiusPrefix)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset

noncomputable section

namespace CenteredPairSharp

abbrev signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State _ := ℕ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p a => ∑ m ∈ Ico p.1 (2*p.1), a m*centered p.2 m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N d : ℕ}, 0 < N → ∀ (a : ℕ → ℝ), 0 < d →
    |R.readout () ⟨N,d⟩ a| ≤ (d : ℝ)/16*variation N a

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (N := 1) (d := 1) (by norm_num) (fun _ => 0) (by norm_num)
  norm_num [rejected, realize, variation] at he

def registration : Registration arena (type_of% @centered_pair_variation_sharp_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨centered_pair_variation_sharp_bound, rejected, rejected_law⟩
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
    refine ⟨⟨1,2⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    have hi : Ico 1 2 = {1} := by decide
    norm_num [actual, realize, hi, centered]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@centered_pair_variation_sharp_bound) (Realization signature) Type Unit where
  unitName := `OriginalResidualFiniteTransfer.centered_pair_variation_sharp_bound.audit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.CenteredPairSharp.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p a => ∑ m ∈ Ico p.1 (2*p.1), a m*centered p.2 m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit

end CenteredPairSharp

end
end Reg.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
