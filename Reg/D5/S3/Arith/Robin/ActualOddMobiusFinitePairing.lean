import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.ActualOddMobiusFinitePairing
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Robin.ActualOddMobiusFinitePairing

open _root_.D5.S3.Arith.Robin.ActualOddMobiusFinitePairing
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset

noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The original terminal evaluation, with no restriction on the kernel or cutoff. -/
def actual : Realization signature :=
  realize signature (fun _ N P => P (N + 1)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (P : ℕ → ℝ) (N : ℕ),
    (∑ n ∈ Ioc 0 N, mobiusPrefix n * (P n - P (n + 1))) =
      (∑ m ∈ Ioc 0 N, (ArithmeticFunction.moebius m : ℝ) * P m) -
        mobiusPrefix N * R.readout () N P

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (fun _ => 1) 1
  norm_num [rejected, realize, mobiusPrefix, sum_Ioc_succ_top] at he

def registration : Registration arena (type_of% @prefix_abel) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨prefix_abel, rejected, rejected_law⟩
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
    refine ⟨1, (fun _ => 0), (fun _ => 1), ?_⟩
    norm_num [actual, realize]

/-- Exact two-binder source telescope; only its terminal kernel evaluation varies. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@prefix_abel) (Realization signature) Type Unit where
  unitName := `ActualOddMobiusFinitePairing.prefix_abel.audit
  realizationName := `Reg.D5.S3.Arith.Robin.ActualOddMobiusFinitePairing.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ N P => P (N + 1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.ActualOddMobiusFinitePairing
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit

end
end Reg.D5.S3.Arith.Robin.ActualOddMobiusFinitePairing
