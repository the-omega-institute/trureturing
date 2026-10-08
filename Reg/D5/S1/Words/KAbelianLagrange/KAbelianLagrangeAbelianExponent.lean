/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangeAbelianExponent
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangeAbelianExponent
   mirror-E: none(waiver:actual-abelian-exponent)
   anchors: []
   utility: none
   digest: The original ceiling readout registers the actual abelian exponent formula. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeAbelianExponent
import Reg.Support.DependentFamily

open D5.S1.Words.KAbelianLagrange KAbelianLagrangeDefs
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S1.Words.KAbelianLagrange.KAbelianLagrangeAbelianExponent
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ => Nat.ceil) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {alpha : ℝ} (_h0 : 0 ≤ alpha) (_h1 : alpha < 1)
    (_hirr : Irrational alpha) {m : ℕ} (_hm : 0 < m),
    ae 1 alpha m =
      R.readout () () (1 / |(m : ℝ) * alpha - (round ((m : ℝ) * alpha) : ℝ)|) - 1

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    have hbad : ¬ arena.Law bad := by
      intro h
      let alpha := Real.sqrt 2 / 2
      have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      have hs2 : Real.sqrt 2 < 2 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      have h0 : 0 ≤ alpha := by dsimp [alpha]; positivity
      have h1 : alpha < 1 := by dsimp [alpha]; linarith
      have hirr : Irrational alpha :=
        irrational_sqrt_two.div_natCast (m := 2) (by norm_num)
      have hd0 : 0 < |alpha - (round alpha : ℝ)| :=
        abs_pos.mpr (sub_ne_zero.mpr (hirr.ne_int (round alpha)))
      have hd1 : |alpha - (round alpha : ℝ)| ≤ 1 / 2 := abs_sub_round alpha
      have ht : (2 : ℝ) ≤ 1 / |alpha - (round alpha : ℝ)| :=
        (le_div_iff₀ hd0).mpr (by linarith)
      have hc : 2 ≤ ⌈1 / |alpha - (round alpha : ℝ)|⌉₊ := by
        exact_mod_cast ht.trans (Nat.le_ceil _)
      have hh := @h alpha h0 h1 hirr 1 (by norm_num)
      have hg := @abelian_exponent_exact alpha h0 h1 hirr 1 (by norm_num)
      simp only [Nat.cast_one, one_mul] at hg
      have hh' : ae 1 alpha 1 = 0 := by simpa [bad, realize] using hh
      rw [hh'] at hg
      omega
    exact ⟨abelian_exponent_exact, bad, hbad⟩
  sensitivity := by
    have hbad : ¬ arena.Law bad := by
      intro h
      let alpha := Real.sqrt 2 / 2
      have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      have hs2 : Real.sqrt 2 < 2 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      have h0 : 0 ≤ alpha := by dsimp [alpha]; positivity
      have h1 : alpha < 1 := by dsimp [alpha]; linarith
      have hirr : Irrational alpha :=
        irrational_sqrt_two.div_natCast (m := 2) (by norm_num)
      have hd0 : 0 < |alpha - (round alpha : ℝ)| :=
        abs_pos.mpr (sub_ne_zero.mpr (hirr.ne_int (round alpha)))
      have hd1 : |alpha - (round alpha : ℝ)| ≤ 1 / 2 := abs_sub_round alpha
      have ht : (2 : ℝ) ≤ 1 / |alpha - (round alpha : ℝ)| :=
        (le_div_iff₀ hd0).mpr (by linarith)
      have hc : 2 ≤ ⌈1 / |alpha - (round alpha : ℝ)|⌉₊ := by
        exact_mod_cast ht.trans (Nat.le_ceil _)
      have hh := @h alpha h0 h1 hirr 1 (by norm_num)
      have hg := @abelian_exponent_exact alpha h0 h1 hirr 1 (by norm_num)
      simp only [Nat.cast_one, one_mul] at hg
      have hh' : ae 1 alpha 1 = 0 := by simpa [bad, realize] using hh
      rw [hh'] at hg
      omega
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
  owner := `D5.S1.Words.KAbelianLagrange.KAbelianLagrangeAbelianExponent
  coordinates := #[]
  readouts := #[{ path := #["body", "body", "body", "body", "body", "body",
    "arg", "fn", "arg", "fn"], functionOperand := true }] }

register_information_theorem abelian_exponent_exact in arena
  readout via (realize signature (fun _ _ => Nat.ceil) (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

end
end Reg.D5.S1.Words.KAbelianLagrange.KAbelianLagrangeAbelianExponent
