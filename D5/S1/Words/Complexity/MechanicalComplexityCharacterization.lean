/- GID: D5/S1/Words/Complexity/MechanicalComplexityCharacterization
   generality: G
   mirror-B: D5/B/S1/Words/Complexity/MechanicalComplexityCharacterization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact factor complexity, irrationality, and aperiodicity coincide. -/

import D5.S1.Words.Mechanical.MechanicalFactorComplexity
import D5.S1.Words.Mechanical.MechanicalPeriodicity
import Mathlib.Data.Nat.Periodic
import Mathlib.NumberTheory.Real.GoldenRatio

namespace D5.S1.Words.Complexity

open D5.S1.Words.Mechanical

private theorem lowerMechanicalFactor_eq_mod_of_periodic {alpha rho : Real} {p : Nat}
    (hperiodic : Function.Periodic (lowerMechanicalWord alpha rho) p) (n i : Nat) :
    lowerMechanicalFactor alpha rho n i = lowerMechanicalFactor alpha rho n (i % p) := by
  simp only [lowerMechanicalFactor]
  apply List.ofFn_inj.mpr
  funext k
  exact (hperiodic.add_const k).map_mod_nat i |>.symm

/-- A positive period `p` bounds the number of factors of every length by `p`. -/
theorem lower_mechanical_factor_set_card_le_period {alpha rho : Real} {p : Nat}
    (hperiodic : Function.Periodic (lowerMechanicalWord alpha rho) p) (hp : 0 < p) (n : Nat) :
    (lowerMechanicalFactorSet alpha rho n).card ≤ p := by
  classical
  let representatives : Finset (List Bool) :=
    (Finset.range p).image fun i => lowerMechanicalFactor alpha rho n i
  have hsubset : lowerMechanicalFactorSet alpha rho n ⊆ representatives := by
    intro w hw
    obtain ⟨i, rfl⟩ := mem_lowerMechanicalFactorSet.mp hw
    rw [lowerMechanicalFactor_eq_mod_of_periodic hperiodic n i]
    exact Finset.mem_image.mpr ⟨i % p, Finset.mem_range.mpr (Nat.mod_lt i hp), rfl⟩
  exact (Finset.card_le_card hsubset).trans
    (Finset.card_image_le.trans_eq (Finset.card_range p))

/-- Exact `n + 1` factor complexity characterizes irrational lower mechanical slopes. -/
theorem lower_mechanical_factor_complexity_iff_irrational {alpha rho : Real}
    (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1) :
    (∀ n, (lowerMechanicalFactorSet alpha rho n).card = n + 1) ↔ Irrational alpha := by
  constructor
  · intro hcomplexity
    by_contra hnotirrational
    obtain ⟨r, rfl⟩ := exists_rat_of_not_irrational hnotirrational
    have hupper := lower_mechanical_factor_set_card_le_period
      (lower_mechanical_word_rat_periodic r rho) r.den_pos r.den
    rw [hcomplexity r.den] at hupper
    omega
  · intro halpha n
    exact lower_mechanical_factor_complexity halpha0 halpha1 halpha n

/-- Exact minimal aperiodic complexity, irrationality, and nonperiodicity coincide. -/
theorem lower_mechanical_factor_complexity_iff_irrational_iff_not_eventuallyPeriodic
    {alpha rho : Real} (halpha0 : 0 ≤ alpha) (halpha1 : alpha < 1) :
    ((∀ n, (lowerMechanicalFactorSet alpha rho n).card = n + 1) ↔ Irrational alpha) ∧
      (Irrational alpha ↔ ¬lowerMechanicalEventuallyPeriodic alpha rho) := by
  refine ⟨lower_mechanical_factor_complexity_iff_irrational halpha0 halpha1, ?_⟩
  constructor
  · intro hirrational hperiodic
    exact (lower_mechanical_eventually_periodic_iff_not_irrational halpha0 halpha1).mpr
      hperiodic hirrational
  · intro hnotperiodic
    by_contra hnotirrational
    exact hnotperiodic
      ((lower_mechanical_eventually_periodic_iff_not_irrational halpha0 halpha1).mp
        hnotirrational)

private def oneThirdPattern (n : Nat) : Bool := n % 3 = 2

private theorem one_third_pattern_length_three_factor_image_card :
    ((Finset.range 3).image fun i =>
      List.ofFn fun k : Fin 3 => oneThirdPattern (i + k)).card = 3 := by
  decide

private theorem one_third_factor_complexity_fails :
    ¬∀ n, (lowerMechanicalFactorSet (1 / 3 : Real) 0 n).card = n + 1 := by
  intro hcomplexity
  have hupper := lower_mechanical_factor_set_card_le_period
    (lower_mechanical_word_rat_periodic (1 / 3 : Rat) 0) (by norm_num) 3
  norm_num at hupper
  rw [hcomplexity 3] at hupper
  omega

private theorem golden_factor_complexity_and_aperiodicity :
    (∀ n, (lowerMechanicalFactorSet Real.goldenRatio⁻¹ 0 n).card = n + 1) ∧
      ¬lowerMechanicalEventuallyPeriodic Real.goldenRatio⁻¹ 0 := by
  have hresult := lower_mechanical_factor_complexity_iff_irrational_iff_not_eventuallyPeriodic
    (alpha := Real.goldenRatio⁻¹) (rho := 0)
    (inv_nonneg.mpr Real.goldenRatio_pos.le)
    (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio)
  exact ⟨hresult.1.mpr Real.goldenRatio_irrational.inv,
    hresult.2.mp Real.goldenRatio_irrational.inv⟩

#print axioms lower_mechanical_factor_set_card_le_period
#print axioms lower_mechanical_factor_complexity_iff_irrational
#print axioms lower_mechanical_factor_complexity_iff_irrational_iff_not_eventuallyPeriodic

end D5.S1.Words.Complexity
