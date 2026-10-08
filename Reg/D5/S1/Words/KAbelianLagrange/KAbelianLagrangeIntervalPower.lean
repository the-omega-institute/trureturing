/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangeIntervalPower
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangeIntervalPower
   mirror-E: none(waiver:rotation-interval-attainment)
   anchors: []
   utility: none
   digest: The original power predicate registers rotation-interval attainment. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeIntervalPower
import Reg.Support.DependentFamily

open D5.S1.Words.KAbelianLagrange KAbelianLagrangeDefs
open D5.S1.Words.Mechanical
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S1.Words.KAbelianLagrange.KAbelianLagrangeIntervalPower
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ → ℕ → ℕ → ℕ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => IsKAbelianPower) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ _ _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {alpha a b : ℝ}
    (_h0 : 0 ≤ alpha) (_h1 : alpha < 1) (_hirr : Irrational alpha)
    (_ha : 0 ≤ a) (_hab : a < b) (_hb : b ≤ 1)
    {k m e : ℕ} (_hmk : k - 1 ≤ m) (_he : 0 < e) (c : ℤ)
    (_hcuts : ∀ r : ℕ, 0 < r → r ≤ m →
      (r ≤ k - 1 ∨ m - (k - 1) ≤ r) →
      1 - Int.fract ((r : ℝ) * alpha) ≤ a ∨
        b ≤ 1 - Int.fract ((r : ℝ) * alpha))
    (_hspan : ((e - 1 : ℕ) : ℝ) * |(m : ℝ) * alpha - c| < b - a),
    ∃ start : ℕ, R.readout () () alpha k m e start

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    have hbad : ¬ arena.Law bad := by
      intro h
      have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      have hs2 : Real.sqrt 2 < 2 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      have hx : Irrational (Real.sqrt 2 / 2) :=
        irrational_sqrt_two.div_natCast (m := 2) (by norm_num)
      have hh := @h (Real.sqrt 2 / 2) 0 1 (by positivity) (by linarith) hx
        (by norm_num) (by norm_num) le_rfl 1 0 1 (by norm_num) (by norm_num) 0
        (fun r hr hrm _ => by omega) (by norm_num)
      exact hh.elim (fun _ hf => hf)
    exact ⟨kabelian_power_in_cut_interval, bad, hbad⟩
  sensitivity := by
    have hbad : ¬ arena.Law bad := by
      intro h
      have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      have hs2 : Real.sqrt 2 < 2 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      have hx : Irrational (Real.sqrt 2 / 2) :=
        irrational_sqrt_two.div_natCast (m := 2) (by norm_num)
      have hh := @h (Real.sqrt 2 / 2) 0 1 (by positivity) (by linarith) hx
        (by norm_num) (by norm_num) le_rfl 1 0 1 (by norm_num) (by norm_num) 0
        (fun r hr hrm _ => by omega) (by norm_num)
      exact hh.elim (fun _ hf => hf)
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
    intro heq
    have hzero : IsKAbelianPower 0 1 1 2 0 := by
      intro i j hi hj z hz hzk
      simp only [lowerMechanicalFactor, lowerMechanicalWord, lowerMechanicalLetter,
        mul_zero, add_zero, Int.floor_zero, sub_self]
    have hone : IsKAbelianPower (1 / 2) 1 1 2 0 :=
      (congrFun (congrFun (congrFun (congrFun heq 1) 1) 2) 0).mp hzero
    have hh := hone 0 1 (by norm_num) (by norm_num) [true] (by simp) (by simp)
    norm_num [lowerMechanicalFactor, lowerMechanicalWord, lowerMechanicalLetter,
      occurrences, List.ofFn_succ, List.range_succ] at hh

def selection : LeanInformationAudit.SourceSelection := {
  owner := `D5.S1.Words.KAbelianLagrange.KAbelianLagrangeIntervalPower
  coordinates := #[]
  readouts := #[{ path := #["body", "body", "body", "body", "body", "body",
    "body", "body", "body", "body", "body", "body", "body", "body", "body",
    "body", "body", "arg", "body", "fn", "fn", "fn", "fn", "fn"], functionOperand := true }] }

register_information_theorem kabelian_power_in_cut_interval in arena
  readout via (realize signature (fun _ _ => IsKAbelianPower) (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

end
end Reg.D5.S1.Words.KAbelianLagrange.KAbelianLagrangeIntervalPower
