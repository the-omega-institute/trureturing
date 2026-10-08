/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangeCutoff
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangeCutoff
   mirror-E: none(waiver:perron-cutoff-escape)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: The original scalar readout registers uniform escape above the Legendre cutoff. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeCutoff
import Reg.Support.DependentFamily
import Mathlib.Tactic

open D5.S1.Words.KAbelianLagrange Filter
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped ENNReal
namespace Reg.D5.S1.Words.KAbelianLagrange.KAbelianLagrangeCutoff
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => ENNReal.ofReal) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ x : ℝ, Irrational x →
    ENNReal.ofReal ((11 : ℝ) / 5) ≤ limsup (fun n : ℕ => R.readout () ()
      (1 / (((x.convergent n).den : ℝ) ^ 2 * |x - (x.convergent n : ℝ)|))) atTop

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨perron_limsup_above_cutoff, bad, ?_⟩
    intro h
    have hh := h (Real.sqrt 2) irrational_sqrt_two
    norm_num [bad, realize, limsup_const] at hh
  sensitivity := by
    have hbad : ¬ arena.Law bad := by
      intro h
      have hh := h (Real.sqrt 2) irrational_sqrt_two
      norm_num [bad, realize, limsup_const] at hh
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
    simp [actual, realize]

def selection : LeanInformationAudit.SourceSelection := {
  owner := `D5.S1.Words.KAbelianLagrange.KAbelianLagrangeCutoff
  coordinates := #[]
  readouts := #[{ path := #["body", "body", "arg", "fn", "arg",
    "body", "fn"], functionOperand := true }] }

register_information_theorem perron_limsup_above_cutoff in arena
  readout via (realize signature (fun _ _ => ENNReal.ofReal) (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

end
end Reg.D5.S1.Words.KAbelianLagrange.KAbelianLagrangeCutoff
