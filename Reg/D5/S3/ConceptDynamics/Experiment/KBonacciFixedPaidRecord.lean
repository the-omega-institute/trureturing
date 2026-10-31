import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Experiment.KBonacciFixedPaidRecord
import Reg.Support.DependentFamily

set_option autoImplicit false

namespace Reg.D5.S3.ConceptDynamics.Experiment.KBonacciFixedPaidRecord

open _root_.D5.S3.ConceptDynamics.Experiment.KBonacciPrefixCompletion
open _root_.D5.S3.ConceptDynamics.Experiment.KBonacciFixedPaidRecord
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

/-- The complete original arrangement telescope, including the exact paid-window budget. -/
structure Parameters where
  k : ℕ
  hk : 3 ≤ k
  arrangement : Arrangement k (by omega)
  budget : windows arrangement = k * (k - 1)

abbrev Record (p : Parameters) := Arrangement p.k (by have := p.hk; omega) × List (ℝ × List ℝ)

abbrev signature : Signature where
  Params := Parameters
  State p := World p.k
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Record p
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p w => paidRecord p.arrangement w) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ p : Parameters,
    (∃ decode : Record p → Matrix (Fin p.k) (Fin p.k) ℝ,
      ∀ w : World p.k, decode (R.readout () p w) = target w) ↔
    surviving p.arrangement = offDiagonal p.k

/-- Packing the full source telescope preserves the exact original decoder statement. -/
theorem source_bridge : (type_of% complete_source_12_2) ↔ arena.Law actual := by
  constructor
  · intro h p
    exact h p.k p.hk p.arrangement p.budget
  · intro h k hk A budget
    exact h ⟨k,hk,A,budget⟩

/-- The actual whole-family law follows from the complete original theorem. -/
theorem actual_law : arena.Law actual := source_bridge.mp complete_source_12_2

private def zeroWindow : Window 3 (by decide) :=
  ⟨[false,false,false,false], by decide⟩

private def sample : Parameters where
  k := 3
  hk := by decide
  arrangement := [List.replicate 6 zeroWindow]
  budget := by decide

/-- A lawful exact-budget parameter and two actual worlds witness observational
variation of the complete paid record; no finite-state domain is substituted. -/
theorem dependence : ObservationalDependence signature actual := by
  intro i
  let w : World 3 := {
    c := fun _ => 1, ell := fun _ => 1,
    c_pos := by intro j; norm_num,
    ell_nonneg := by intro j; norm_num,
    ell_ne_zero := by intro he; have h := congrFun he 0; norm_num at h }
  let v : World 3 := {
    c := fun _ => 2, ell := fun _ => 1,
    c_pos := by intro j; norm_num,
    ell_nonneg := by intro j; norm_num,
    ell_ne_zero := by intro he; have h := congrFun he 0; norm_num at h }
  refine ⟨sample,w,v,?_⟩
  change paidRecord sample.arrangement w ≠ paidRecord sample.arrangement v
  intro he
  have first := congrArg (fun record => record.2.head?.map Prod.fst) he
  norm_num [paidRecord, sample, initial, w, v, Fin.sum_univ_succ] at first

end Reg.D5.S3.ConceptDynamics.Experiment.KBonacciFixedPaidRecord
