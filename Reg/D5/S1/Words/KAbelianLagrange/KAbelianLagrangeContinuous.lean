/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangeContinuous
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangeContinuous
   mirror-E: none(waiver:continuous-feedback-realization)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: The target readout registers the continuous feedback realization. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeContinuous
import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeCutoff
import Reg.Support.DependentFamily
import Mathlib.Tactic

open D5.S1.Words.KAbelianLagrange Filter
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.S1.Words.KAbelianLagrange.KAbelianLagrangeContinuous
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ENNReal
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => ENNReal.ofReal) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (seed : List ℕ) (A B : ℕ)
    (_hseed : ∀ a ∈ seed, 0 < a ∧ a ≤ A) (F : ℝ → ℝ)
    (_hF : Continuous F) (_hbound : ∀ z, 6 < F z ∧ F z ≤ (B : ℝ)),
    ∃ α : ℝ, Irrational α ∧ 0 < α ∧ α < 1 ∧
      (∀ i : ℕ, ∀ hi : i < seed.length,
        (GenContFract.of α).s.get? i = some ⟨1, (seed[i] : ℝ)⟩) ∧
      (∀ i, ∃ a : ℕ, 0 < a ∧ a ≤ max A (max 4 B) ∧
        (GenContFract.of α).s.get? i = some ⟨1, (a : ℝ)⟩) ∧
      limsup (fun q : ℕ => ENNReal.ofReal
        (1 / ((q : ℝ) * |(q : ℝ) * α - (round ((q : ℝ) * α) : ℝ)|)))
        atTop = R.readout () () (F α)

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    have hbad : ¬ arena.Law bad := by
      intro h
      obtain ⟨α, hα, _, _, _, _, hlim⟩ :=
        h [] 0 7 (by simp) (fun _ => 7) continuous_const (by intro z; norm_num)
      have hh := (perron_limsup_above_cutoff α hα).trans (lagrange_limsup_lower α hα)
      rw [hlim] at hh
      norm_num [bad, realize] at hh
    exact ⟨continuous_feedback_realization, bad, hbad⟩
  sensitivity := by
    have hbad : ¬ arena.Law bad := by
      intro h
      obtain ⟨α, hα, _, _, _, _, hlim⟩ :=
        h [] 0 7 (by simp) (fun _ => 7) continuous_const (by intro z; norm_num)
      have hh := (perron_limsup_above_cutoff α hα).trans (lagrange_limsup_lower α hα)
      rw [hlim] at hh
      norm_num [bad, realize] at hh
    constructor
    · intro i
      refine ⟨bad, ?_, rfl, hbad⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def selection : LeanInformationAudit.SourceSelection := {
  owner := `D5.S1.Words.KAbelianLagrange.KAbelianLagrangeContinuous
  coordinates := #[]
  readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body",
    "arg", "body", "arg", "arg", "arg", "arg", "arg", "arg", "fn"], functionOperand := true }] }

register_information_theorem continuous_feedback_realization in arena
  readout via (realize signature (fun _ _ => ENNReal.ofReal) (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

end
end Reg.D5.S1.Words.KAbelianLagrange.KAbelianLagrangeContinuous
