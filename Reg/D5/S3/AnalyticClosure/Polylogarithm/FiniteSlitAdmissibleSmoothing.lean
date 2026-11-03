import LeanInformationAuditInterface.Contract.Registration
import D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitAdmissibleSmoothing
import Reg.Support.DependentFamily
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Set Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitAdmissibleSmoothing
open _root_.D5.S3.AnalyticClosure.Polylogarithm
open FiniteSlitOrdinarySmoothing
abbrev signature : Signature where
  Params := ℕ+ × List ℕ+ × ℕ+
  State _ := ℕ × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p jn ↦ smooth
    (FiniteSlitOrdinaryCoefficients.ordinary p.1 p.2.1 p.2.2) jn.1 jn.2)
    (fun e ↦ nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ ↦ 0) (fun e ↦ nomatch e)
abbrev arena : Arena where
  signature := signature
  Law s := ∀ (head : ℕ+) (tail : List ℕ+) (ell : ℕ+), 1 < (head : ℕ) →
    (∀ᶠ n : ℕ in atTop,
      PowerSeries.coeff n (FiniteSlitOrdinaryCoefficients.ordinary head tail ell) < 0) ∧
    ∀ j : ℕ, 1 ≤ j → ∀ᶠ n : ℕ in atTop,
      0 < s.readout () ⟨head,tail,ell⟩ (j,n) ∧
      (CompositionBoundary.zeta head tail)⁻¹ ^ (ell : ℕ) *
        (Nat.choose (n+j-1) n : ℝ) < s.readout () ⟨head,tail,ell⟩ (j,n)
theorem source_equivalence :
    (type_of% @_root_.D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitAdmissibleSmoothing.result) ↔
      arena.Law actual := Iff.rfl
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨n, hn⟩ := ((h 2 [] 1 (by norm_num)).2 1 (by norm_num)).exists
  simpa [rejected, realize] using hn.1
def variation : Variation arena actual :=
  ⟨_root_.D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitAdmissibleSmoothing.result,
    rejected, rejected_law⟩
def sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hj
    exact (hj (Subsingleton.elim j i)).elim
  · intro e
    exact nomatch e

abbrev full_arena : Arena where
  signature := signature
  Law s := ∀ (head : ℕ+) (tail : List ℕ+) (ell : ℕ+),
    (∀ᶠ n : ℕ in atTop,
      PowerSeries.coeff n (FiniteSlitOrdinaryCoefficients.ordinary head tail ell) < 0) ∧
    (∀ j : ℕ, 1 ≤ j → ∀ᶠ n : ℕ in atTop,
      0 < s.readout () ⟨head,tail,ell⟩ (j,n)) ∧
    (1 < (head : ℕ) → ∀ j : ℕ, 1 ≤ j → ∀ᶠ n : ℕ in atTop,
      (CompositionBoundary.zeta head tail)⁻¹ ^ (ell : ℕ) *
        (Nat.choose (n+j-1) n : ℝ) < s.readout () ⟨head,tail,ell⟩ (j,n))
theorem full_source_equivalence :
    (type_of% @_root_.D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitAdmissibleSmoothing.full_result) ↔
      full_arena.Law actual := Iff.rfl
private theorem full_rejected_law : ¬ full_arena.Law rejected := by
  intro h
  obtain ⟨n, hn⟩ := ((h 1 [] 1).2.1 1 (by norm_num)).exists
  simpa [rejected, realize] using hn
def full_variation : Variation full_arena actual :=
  ⟨_root_.D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitAdmissibleSmoothing.full_result,
    rejected, full_rejected_law⟩
def full_sensitivity : Sensitivity full_arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, full_rejected_law⟩
    intro j hj
    exact (hj (Subsingleton.elim j i)).elim
  · intro e
    exact nomatch e

end Reg.D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitAdmissibleSmoothing
