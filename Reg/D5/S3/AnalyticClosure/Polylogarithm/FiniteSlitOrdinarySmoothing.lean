import LeanInformationAuditInterface.Contract.Registration
import D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitOrdinarySmoothing
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Set Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitOrdinarySmoothing
open _root_.D5.S3.AnalyticClosure.Polylogarithm
open _root_.D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitOrdinarySmoothing

abbrev signature : Signature where
  Params := PowerSeries ℝ × ℝ × (ℝ → ℝ)
  State _ := ℕ × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p jn ↦ smooth p.1 jn.1 jn.2) (fun e ↦ nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ ↦ 0) (fun e ↦ nomatch e)

abbrev arena : Arena where
  signature := signature
  Law s := ∀ (p : PowerSeries ℝ) (L : ℝ) (H : ℝ → ℝ),
    (∀ᶠ n : ℕ in atTop, 0 < smooth (p - PowerSeries.C L) 1 n) →
    (∀ r : ℝ, 0 < r → r < 1 →
      HasSum (fun n ↦ smooth (p - PowerSeries.C L) 1 n * r ^ n) (H r)) →
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ r : ℝ in 𝓝[<] 1, c ≤ H r) →
    ∀ j : ℕ, 1 ≤ j → ∀ᶠ n : ℕ in atTop,
      L * (Nat.choose (n + j - 1) n : ℝ) < s.readout () ⟨p, L, H⟩ (j,n)

theorem source_equivalence :
    (type_of% @_root_.D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitOrdinarySmoothing.result) ↔
      arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he (n : ℕ) : smooth ((1 : PowerSeries ℝ) - PowerSeries.C 0) 1 n = 1 := by
    simp [smooth, PowerSeries.invOneSubPow]
  have hp : ∀ᶠ n : ℕ in atTop,
      0 < smooth ((1 : PowerSeries ℝ) - PowerSeries.C 0) 1 n :=
    Eventually.of_forall (fun n ↦ by rw [he]; norm_num)
  have hs (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
      HasSum (fun n ↦ smooth ((1 : PowerSeries ℝ) - PowerSeries.C 0) 1 n * r ^ n)
        ((1-r)⁻¹) := by
    simpa only [he, one_mul] using
      hasSum_geometric_of_abs_lt_one (by rwa [abs_of_pos hr])
  have hm : ∃ c : ℝ, 0 < c ∧ ∀ᶠ r : ℝ in 𝓝[<] 1, c ≤ (1-r)⁻¹ := by
    refine ⟨1, by norm_num, ?_⟩
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with r hr
    rw [← one_div]
    exact (le_div_iff₀ (sub_pos.mpr hr.2)).mpr (by linarith [hr.1])
  obtain ⟨n, hn⟩ := (h 1 0 (fun r ↦ (1-r)⁻¹) hp hs hm 1 (by norm_num)).exists
  simpa [rejected, realize] using hn

def variation : Variation arena actual :=
  ⟨_root_.D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitOrdinarySmoothing.result,
    rejected, rejected_law⟩

def sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hj
    exact (hj (Subsingleton.elim j i)).elim
  · intro e
    exact nomatch e
end Reg.D5.S3.AnalyticClosure.Polylogarithm.FiniteSlitOrdinarySmoothing
