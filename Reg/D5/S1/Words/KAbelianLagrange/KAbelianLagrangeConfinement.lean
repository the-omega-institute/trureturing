/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangeConfinement
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangeConfinement
   mirror-E: none(waiver:necessary-rotation-class-span)
   anchors: []
   utility: none
   digest: The original block phase readout registers necessary cut confinement. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeConfinement
import Reg.Support.DependentFamily

open D5.S1.Words.KAbelianLagrange KAbelianLagrangeDefs
open D5.S1.Words.Mechanical
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S1.Words.KAbelianLagrange.KAbelianLagrangeConfinement
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
  Law R := ∀ {alpha : ℝ} (_h0 : 0 ≤ alpha) (_h1 : alpha < 1) {k m e start : ℕ}
    (_hk : 1 ≤ k) (_hmk : k - 1 ≤ m) (_he : 0 < e)
    (_hp : IsKAbelianPower alpha k m e start),
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
      (a = 0 ∨ ∃ r : ℕ, 0 < r ∧ r ≤ m ∧
        (r ≤ k - 1 ∨ m - (k - 1) ≤ r) ∧ a = 1 - Int.fract ((r : ℝ) * alpha)) ∧
      (b = 1 ∨ ∃ r : ℕ, 0 < r ∧ r ≤ m ∧
        (r ≤ k - 1 ∨ m - (k - 1) ≤ r) ∧ b = 1 - Int.fract ((r : ℝ) * alpha)) ∧
      (∀ r : ℕ, 0 < r → r ≤ m → (r ≤ k - 1 ∨ m - (k - 1) ≤ r) →
        1 - Int.fract ((r : ℝ) * alpha) ≤ a ∨
          b ≤ 1 - Int.fract ((r : ℝ) * alpha)) ∧
      (∀ i < e, a ≤ Int.fract (((start + i * m : ℕ) : ℝ) * alpha) ∧
        R.readout () () (((start + i * m : ℕ) : ℝ) * alpha) < b) ∧
      ((e - 1 : ℕ) : ℝ) *
        |(m : ℝ) * alpha - (round ((m : ℝ) * alpha) : ℝ)| < b - a

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    have hbad : ¬ arena.Law bad := by
      intro h
      have hp : IsKAbelianPower 0 1 0 1 0 := by
        intro i j _ _ z _ _
        simp [lowerMechanicalFactor]
      obtain ⟨a, b, _, _, hb, _, _, _, hstay, _⟩ :=
        @h 0 (by norm_num) (by norm_num) 1 0 1 0
          (by norm_num) (by norm_num) (by norm_num) hp
      have hh := (hstay 0 (by norm_num)).2
      change (2 : ℝ) < b at hh
      linarith
    exact ⟨kabelian_power_cut_confinement, bad, hbad⟩
  sensitivity := by
    have hbad : ¬ arena.Law bad := by
      intro h
      have hp : IsKAbelianPower 0 1 0 1 0 := by
        intro i j _ _ z _ _
        simp [lowerMechanicalFactor]
      obtain ⟨a, b, _, _, hb, _, _, _, hstay, _⟩ :=
        @h 0 (by norm_num) (by norm_num) 1 0 1 0
          (by norm_num) (by norm_num) (by norm_num) hp
      have hh := (hstay 0 (by norm_num)).2
      change (2 : ℝ) < b at hh
      linarith
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
  owner := `D5.S1.Words.KAbelianLagrange.KAbelianLagrangeConfinement
  coordinates := #[]
  readouts := #[{ path := #["body", "body", "body", "body", "body", "body",
    "body", "body", "body", "body", "body", "arg", "body", "arg", "body",
    "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "body", "body",
    "arg", "fn", "arg", "fn"], functionOperand := true }] }

register_information_theorem kabelian_power_cut_confinement in arena
  readout via (realize signature (fun _ _ => Int.fract) (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

end
end Reg.D5.S1.Words.KAbelianLagrange.KAbelianLagrangeConfinement
