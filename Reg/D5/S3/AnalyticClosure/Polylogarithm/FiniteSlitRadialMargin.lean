import LeanInformationAuditInterface.Contract.Registration
import D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitRadialMargin
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Complex Filter Set Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitRadialMargin
open _root_.D5.S3.AnalyticClosure.Polylogarithm

abbrev signature : Signature where
  Params := ℕ+ × List ℕ+ × ℕ+
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p r ↦ (FiniteSlitCompositionMoments.reciprocal
    p.1 p.2.1 p.2.2 (r : ℂ)).re) (fun e ↦ nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p _ ↦ FiniteSlitOrdinaryEndpoint.endpoint p.1 p.2.1 p.2.2)
    (fun e ↦ nomatch e)

abbrev arena : Arena where
  signature := signature
  Law s := ∀ (head : ℕ+) (tail : List ℕ+) (ell : ℕ+), 1 < (head : ℕ) →
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ r : ℝ in 𝓝[<] 1,
      c ≤ (s.readout () ⟨head, tail, ell⟩ r -
        FiniteSlitOrdinaryEndpoint.endpoint head tail ell) / (1 - r)

theorem source_equivalence :
    (type_of% @_root_.D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitRadialMargin.result) ↔
      arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨c, hc, he⟩ := h 2 [] 1 (by norm_num)
  obtain ⟨r, hr⟩ := he.exists
  have hz : c ≤ 0 := by simpa [rejected, realize] using hr
  linarith

def variation : Variation arena actual :=
  ⟨_root_.D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitRadialMargin.result,
    rejected, rejected_law⟩

def sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hj
    exact (hj (Subsingleton.elim j i)).elim
  · intro e
    exact nomatch e
end Reg.D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitRadialMargin
