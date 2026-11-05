import LeanInformationAuditInterface.Contract.Registration
import D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitOrdinaryEndpoint
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Complex Filter Set Topology
open scoped BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitOrdinaryEndpoint
open _root_.D5.S3.AnalyticClosure.Polylogarithm

abbrev signature : Signature where
  Params := ℕ+ × List ℕ+ × ℕ+
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p n ↦ PowerSeries.coeff n
    (FiniteSlitOrdinaryCoefficients.ordinary p.1 p.2.1 p.2.2)) (fun e ↦ nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ ↦ 0) (fun e ↦ nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (head : ℕ+) (tail : List ℕ+) (ell : ℕ+),
    Summable (fun n : ℕ ↦ |r.readout () ⟨head, tail, ell⟩ n|) ∧
    HasSum (fun n : ℕ ↦ r.readout () ⟨head, tail, ell⟩ n)
      (FiniteSlitOrdinaryEndpoint.endpoint head tail ell) ∧
    (∀ᶠ n : ℕ in atTop, FiniteSlitOrdinaryEndpoint.endpoint head tail ell <
      ∑ i ∈ Finset.range (n + 1), r.readout () ⟨head, tail, ell⟩ i)

theorem source_equivalence :
    (type_of% @_root_.D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitOrdinaryEndpoint.result) ↔
      arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨n, hn⟩ := (h 1 [] 1).2.2.exists
  simpa [rejected, realize, FiniteSlitOrdinaryEndpoint.endpoint] using hn

def variation : Variation arena actual :=
  ⟨_root_.D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitOrdinaryEndpoint.result,
    rejected, rejected_law⟩

def sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hj
    exact (hj (Subsingleton.elim j i)).elim
  · intro e
    exact nomatch e

end Reg.D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitOrdinaryEndpoint
