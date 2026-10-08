/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangePowerSpan
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangePowerSpan
   mirror-E: none(waiver:mechanical-power-no-wrap)
   anchors: []
   utility: none
   digest: The original endpoint fractional-part readout registers mechanical power geometry. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangePowerSpan
import Reg.Support.DependentFamily

open D5.S1.Words.KAbelianLagrange KAbelianLagrangeDefs
open D5.S1.Words.Mechanical
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S1.Words.KAbelianLagrange.KAbelianLagrangePowerSpan
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => Int.fract) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {alpha : ℝ} (_h0 : 0 ≤ alpha) (_h1 : alpha < 1)
    {k m e start : ℕ} (_hk : 1 ≤ k) (_he : 0 < e)
    (_hp : IsKAbelianPower alpha k m e start),
    ∃ c : ℤ,
      (∀ i ≤ e, R.readout () () (((start + i * m : ℕ) : ℝ) * alpha) =
        Int.fract ((start : ℝ) * alpha) + (i : ℝ) * ((m : ℝ) * alpha - c)) ∧
      (e : ℝ) * |(m : ℝ) * alpha - c| < 1

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    have hbad : ¬ arena.Law bad := by
      intro h
      have hp : IsKAbelianPower 0 1 0 1 0 := by
        intro i j _ _ z _ _
        simp [lowerMechanicalFactor]
      obtain ⟨c, hc, _⟩ := @h 0 (by norm_num) (by norm_num) 1 0 1 0
        (by norm_num) (by norm_num) hp
      have hh := hc 0 (by norm_num)
      norm_num [bad, realize] at hh
    exact ⟨kabelian_power_phase_span, bad, hbad⟩
  sensitivity := by
    have hbad : ¬ arena.Law bad := by
      intro h
      have hp : IsKAbelianPower 0 1 0 1 0 := by
        intro i j _ _ z _ _
        simp [lowerMechanicalFactor]
      obtain ⟨c, hc, _⟩ := @h 0 (by norm_num) (by norm_num) 1 0 1 0
        (by norm_num) (by norm_num) hp
      have hh := hc 0 (by norm_num)
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
    refine ⟨(), 0, 1 / 2, ?_⟩
    norm_num [actual, realize]

def selection : LeanInformationAudit.SourceSelection := {
  owner := `D5.S1.Words.KAbelianLagrange.KAbelianLagrangePowerSpan
  coordinates := #[]
  readouts := #[{ path := #["body", "body", "body", "body", "body", "body",
    "body", "body", "body", "body", "arg", "body", "fn", "arg", "body", "body",
    "fn", "arg", "fn"], functionOperand := true }] }

register_information_theorem kabelian_power_phase_span in arena
  readout via (realize signature (fun _ _ => Int.fract) (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

end
end Reg.D5.S1.Words.KAbelianLagrange.KAbelianLagrangePowerSpan
