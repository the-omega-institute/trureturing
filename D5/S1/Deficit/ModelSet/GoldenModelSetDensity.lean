/- GID: D5/S1/Deficit/ModelSet/GoldenModelSetDensity
   generality: I
   mirror-B: D5/B/S1/Deficit/ModelSet/GoldenModelSetDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact endpoint counts for the golden model set have asymptotic density 1 / sqrt 5. -/

import D5.S1.Deficit.Beatty.BetaBeattyClosedForms
import D5.S1.Deficit.ModelSet.GoldenModelSetSelfSimilar

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'golden_model_set_density' D5 Golden/Frozen/accepted`
     returned no matches.
   * The requested `density|ncard.*Icc|counting` search found public density theorems
     only for mechanical words; none counts `Set.range betaGolden`. It found no private
     model-set-density theorem either.
   * `GoldenModelSetSelfSimilar.goldenModelSet` is reused as the model set, and its
     digest explicitly lists density among its omitted clauses.
   * `BetaBeattyClosedForms.betaReal_eq_displacement_sub_goldenConj` and
     `ZeckendorfDisplacementReading.displacement_decode_eq_beatty_floor` give the
     required explicit Beatty expression for the expanding embedding.
   * Searches in pinned mathlib found the standard floor bounds, finite image-cardinality
     lemmas, and limit algebra, but no theorem stating this golden model-set density.
   -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Deficit.ModelSet.GoldenModelSetDensity

open D5.S0.Carrier
open D5.S1.Deficit
open D5.S1.Deficit.BetaBeattyClosedForms
open D5.S1.Deficit.GoldenModelSetSelfSimilar
open D5.S1.Deficit.ZeckendorfDisplacementReading
open D5.S1.Scale
open Filter

/-- The first `n` golden model-set points, indexed by their canonical natural parameter. -/
noncomputable def goldenPrefix (n : Nat) : Finset GoldenInt :=
  (Finset.range n).image betaGolden

private theorem beta_real_error (v : Nat) :
    |betaReal v - (v : Real) * Real.sqrt 5| < 1 := by
  let x : Real := ((v : Real) + 1) * Real.goldenRatio
  have hdecode := congrArg (fun z : Int => (z : Real))
    (displacement_decode_eq_beatty_floor v)
  push_cast at hdecode
  have hlower : x - 1 < (⌊x⌋ : Int) := Int.sub_one_lt_floor x
  have hupper : ((⌊x⌋ : Int) : Real) ≤ x := Int.floor_le x
  have herror :
      betaReal v - (v : Real) * Real.sqrt 5 =
        ((⌊x⌋ : Int) : Real) - x + Real.goldenRatio - 1 := by
    rw [betaReal_eq_displacement_sub_goldenConj, hdecode,
      ← Real.goldenRatio_sub_goldenConj]
    dsimp [x]
    ring
  rw [herror, abs_lt]
  constructor
  · linarith [Real.one_lt_goldenRatio]
  · linarith [Real.goldenRatio_lt_two]

private theorem beta_real_strictMono : StrictMono betaReal := by
  intro m n hmn
  have hm := beta_real_error m
  have hn := beta_real_error n
  rw [abs_lt] at hm hn
  have hsquare : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hsqrt : 2 < Real.sqrt 5 := by
    nlinarith [Real.sqrt_nonneg 5]
  have hgap : (m : Real) + 1 ≤ (n : Real) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hmn)
  have hscaled := mul_le_mul_of_nonneg_right hgap (Real.sqrt_nonneg 5)
  rw [add_mul] at hscaled
  linarith

private theorem beta_golden_injective : Function.Injective betaGolden := by
  intro m n equality
  have coordinates := congrArg GoldenInt.b equality
  rw [D5.S1.Deficit.DoubleFaceLength.betaGolden_b,
    D5.S1.Deficit.DoubleFaceLength.betaGolden_b] at coordinates
  exact_mod_cast coordinates

private theorem beta_real_zero : betaReal 0 = 0 := by
  have hfloor : ⌊Real.goldenRatio⌋ = (1 : Int) := by
    rw [Int.floor_eq_iff]
    constructor
    · norm_num
      exact Real.one_lt_goldenRatio.le
    · norm_num
      exact Real.goldenRatio_lt_two
  have hdecode := displacement_decode_eq_beatty_floor 0
  norm_num [hfloor] at hdecode
  rw [betaReal_eq_displacement_sub_goldenConj, hdecode]
  norm_num

private theorem golden_prefix_card (n : Nat) : (goldenPrefix n).card = n := by
  rw [goldenPrefix, Finset.card_image_of_injective _ beta_golden_injective,
    Finset.card_range]

private theorem mem_golden_prefix_iff (n : Nat) (x : GoldenInt) :
    x ∈ goldenPrefix n ↔
      x ∈ goldenModelSet ∧ 0 ≤ embedding x ∧ embedding x < betaReal n := by
  constructor
  · intro membership
    rw [goldenPrefix, Finset.mem_image] at membership
    obtain ⟨v, hv, rfl⟩ := membership
    have hvn := Finset.mem_range.mp hv
    refine ⟨⟨v, rfl⟩, ?_, ?_⟩
    · change 0 ≤ betaReal v
      rw [← beta_real_zero]
      exact beta_real_strictMono.monotone (Nat.zero_le v)
    · exact beta_real_strictMono hvn
  · rintro ⟨⟨v, rfl⟩, _, upper⟩
    rw [goldenPrefix, Finset.mem_image]
    refine ⟨v, Finset.mem_range.mpr ?_, rfl⟩
    change betaReal v < betaReal n at upper
    exact beta_real_strictMono.lt_iff_lt.mp upper

private theorem beta_real_ratio_tendsto :
    Tendsto (fun n : Nat => betaReal n / n) atTop (nhds (Real.sqrt 5)) := by
  have hzero :
      Tendsto (fun n : Nat => (1 : Real) / n) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have hlower :
      Tendsto (fun n : Nat => Real.sqrt 5 - (1 : Real) / n)
        atTop (nhds (Real.sqrt 5)) := by
    simpa using tendsto_const_nhds.sub hzero
  have hupper :
      Tendsto (fun n : Nat => Real.sqrt 5 + (1 : Real) / n)
        atTop (nhds (Real.sqrt 5)) := by
    simpa using tendsto_const_nhds.add hzero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : Nat)] with n hn
    have hn_pos : (0 : Real) < n := by
      exact_mod_cast (Nat.zero_lt_of_lt hn)
    have herror := beta_real_error n
    rw [abs_lt] at herror
    have lower : (n : Real) * Real.sqrt 5 - 1 ≤ betaReal n := by
      linarith
    calc
      Real.sqrt 5 - (1 : Real) / n =
          ((n : Real) * Real.sqrt 5 - 1) / n := by field_simp
      _ ≤ betaReal n / n := (div_le_div_iff_of_pos_right hn_pos).2 lower
  · filter_upwards [eventually_ge_atTop (1 : Nat)] with n hn
    have hn_pos : (0 : Real) < n := by
      exact_mod_cast (Nat.zero_lt_of_lt hn)
    have herror := beta_real_error n
    rw [abs_lt] at herror
    have upper : betaReal n ≤ (n : Real) * Real.sqrt 5 + 1 := by
      linarith
    calc
      betaReal n / n ≤ ((n : Real) * Real.sqrt 5 + 1) / n :=
        (div_le_div_iff_of_pos_right hn_pos).2 upper
      _ = Real.sqrt 5 + (1 : Real) / n := by field_simp

/-- The expanding golden model set has exact endpoint counts and density `1 / sqrt 5`.
The first conjunct identifies the points in `[0, betaReal n)` and counts them exactly;
the second takes the resulting count-to-length ratio along those endpoints. -/
theorem golden_model_set_density :
    (∀ n : Nat, (goldenPrefix n).card = n ∧
      ∀ x : GoldenInt, x ∈ goldenPrefix n ↔
        x ∈ goldenModelSet ∧ 0 ≤ embedding x ∧ embedding x < betaReal n) ∧
      Tendsto (fun n : Nat => ((goldenPrefix n).card : Real) / betaReal n)
        atTop (nhds (1 / Real.sqrt 5)) := by
  constructor
  · intro n
    exact ⟨golden_prefix_card n, mem_golden_prefix_iff n⟩
  · convert! beta_real_ratio_tendsto.inv₀ (by positivity) using 2
    · rw [inv_div, golden_prefix_card]
    · rw [one_div]

example : (goldenPrefix 5).card = 5 := golden_model_set_density.1 5 |>.1

#print axioms golden_model_set_density

end D5.S1.Deficit.ModelSet.GoldenModelSetDensity
