/- GID: D5/S3/Analytic/Knapsack/GridDualStructure
   generality: G
   mirror-B: D5/B/S3/Analytic/Knapsack/GridDualStructure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite grid duality, extreme fill structure, and saturation of fractional optima. -/

import D5.S3.Analytic.Knapsack.FractionalKnapsackDual
import D5.S3.Analytic.Interpolation.TwoPointGridDominance
import Mathlib.Analysis.Convex.Extreme

open Set
open scoped BigOperators

noncomputable section

namespace D5.S3.Analytic.Knapsack.GridDualStructure

open Interpolation.TwoPointGridDominance (logValue)
open private logValue_strictMono from D5.S3.Analytic.Interpolation.TwoPointGridDominance

variable {ι : Type*} [Fintype ι]

/-- The grid dual value for an arbitrary finite index type. -/
def gridDualValue (c d : ι → ℝ) (M price : ℝ) : ℝ :=
  price * M + ∑ i, max (logValue (c i) - price * c i)
    (logValue (d i) - price * d i)

/-- The infimum over nonnegative budget prices. -/
def gridDualK (c d : ι → ℝ) (M : ℝ) : ℝ :=
  ⨅ p : {p : ℝ // 0 ≤ p}, gridDualValue c d M p

/-- Fractional upper-endpoint masses with an upper expected budget. -/
def FillFeasible (c d : ι → ℝ) (M : ℝ) (a : ι → ℝ) : Prop :=
  (∀ i, a i ∈ Icc 0 1) ∧ ∑ i, (d i - c i) * a i ≤ M - ∑ i, c i

/-- The expected logarithmic return of a fill. -/
def fillValue (c d a : ι → ℝ) : ℝ :=
  ∑ i, (logValue (c i) + a i * (logValue (d i) - logValue (c i)))

/-- Attainment of the supremum over feasible fills. -/
def FillOptimal (c d : ι → ℝ) (M : ℝ) (a : ι → ℝ) : Prop :=
  FillFeasible c d M a ∧
    fillValue c d a = sSup (fillValue c d '' {b | FillFeasible c d M b})

private theorem fill_value_translate (c d a : ι → ℝ) :
    fillValue c d a = (∑ i, logValue (c i)) +
      FractionalKnapsackDual.objective (fun i => logValue (d i) - logValue (c i)) a := by
  simp [fillValue, FractionalKnapsackDual.objective, Finset.sum_add_distrib, mul_comm]

private theorem grid_dual_value_translate (c d : ι → ℝ) (M p : ℝ) :
    gridDualValue c d M p = (∑ i, logValue (c i)) +
      FractionalKnapsackDual.dualValue (fun i => d i - c i)
        (fun i => logValue (d i) - logValue (c i)) (M - ∑ i, c i) p := by
  have hm (i : ι) :
      max (logValue (c i) - p * c i) (logValue (d i) - p * d i) =
        logValue (c i) - p * c i +
          max 0 (logValue (d i) - logValue (c i) - p * (d i - c i)) := by
    rw [add_max]
    congr 1 <;> ring
  simp only [gridDualValue, hm, FractionalKnapsackDual.dualValue,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- The grid price infimum is exactly the fractional linear-program supremum. -/
theorem grid_dual_eq_fill_sup (c d : ι → ℝ) (M : ℝ)
    (hc : ∀ i, 0 < c i) (hcd : ∀ i, c i < d i) (hM : ∑ i, c i ≤ M) :
    gridDualK c d M = sSup (fillValue c d '' {a | FillFeasible c d M a}) := by
  classical
  haveI : Nonempty {p : ℝ // 0 ≤ p} := ⟨⟨0, le_rfl⟩⟩
  let w := fun i => d i - c i
  let v := fun i => logValue (d i) - logValue (c i)
  let B := M - ∑ i, c i
  have hw (i : ι) : 0 < w i := sub_pos.mpr (hcd i)
  have hv (i : ι) : 0 ≤ v i :=
    (sub_pos.mpr (logValue_strictMono (hc i) ((hc i).trans (hcd i)) (hcd i))).le
  have hB : 0 ≤ B := sub_nonneg.mpr hM
  have hb : BddBelow (range (fun p : {p : ℝ // 0 ≤ p} =>
      FractionalKnapsackDual.dualValue w v B p)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨p, rfl⟩
    exact add_nonneg (mul_nonneg p.property hB)
      (Finset.sum_nonneg (fun i _ => le_max_left _ _))
  obtain ⟨l, p, _, _, _, ha, _, _, _, _, hsup, _⟩ :=
    FractionalKnapsackDual.greedy_attains_duality w v B hw hv hB
  have hne : (FractionalKnapsackDual.objective v ''
      {a | FractionalKnapsackDual.Feasible w B a}).Nonempty := ⟨_, _, ha, rfl⟩
  have hbounded : BddAbove (FractionalKnapsackDual.objective v ''
      {a | FractionalKnapsackDual.Feasible w B a}) := by
    refine ⟨∑ i, v i, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact Finset.sum_le_sum (fun i _ => mul_le_of_le_one_right (hv i) (ha.1 i).2)
  have htranslate := (OrderIso.addLeft (∑ i, logValue (c i))).map_csSup hne hbounded
  rw [gridDualK]
  simp only [grid_dual_value_translate]
  rw [← add_ciInf hb, ← FractionalKnapsackDual.fractional_knapsack_strong_duality
    w v B hw hv hB]
  rw [htranslate]
  congr 1
  ext z
  simp only [mem_image]
  constructor
  · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, (fill_value_translate c d a).symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨_, ⟨a, ha, rfl⟩, (fill_value_translate c d a).symm⟩

private theorem fill_values_bddAbove (c d : ι → ℝ) (M : ℝ) :
    BddAbove (fillValue c d '' {a | FillFeasible c d M a}) := by
  refine ⟨∑ i, (logValue (c i) + max 0 (logValue (d i) - logValue (c i))), ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  apply Finset.sum_le_sum
  intro i _
  have hbox := ha.1 i
  have h := le_max_left 0 (logValue (d i) - logValue (c i))
  have h' := le_max_right 0 (logValue (d i) - logValue (c i))
  by_cases hv : 0 ≤ logValue (d i) - logValue (c i)
  · nlinarith [hbox.2]
  · nlinarith [hbox.1]

/-- A positive-return unfilled row permits strict improvement whenever the budget has slack. -/
theorem slack_fill_improvable (c d : ι → ℝ) (M : ℝ) (a : ι → ℝ) (j : ι)
    (ha : FillFeasible c d M a) (hj : a j < 1) (hw : 0 < d j - c j)
    (hv : 0 < logValue (d j) - logValue (c j))
    (hslack : ∑ i, (d i - c i) * a i < M - ∑ i, c i) :
    ∃ b, FillFeasible c d M b ∧ fillValue c d a < fillValue c d b := by
  classical
  let ε := min (1 - a j)
    ((M - ∑ i, c i - ∑ i, (d i - c i) * a i) / (d j - c j))
  have he : 0 < ε := lt_min (sub_pos.mpr hj) (div_pos (sub_pos.mpr hslack) hw)
  have he1 : ε ≤ 1 - a j := min_le_left _ _
  have heb : (d j - c j) * ε ≤ M - ∑ i, c i - ∑ i, (d i - c i) * a i := by
    have h := (le_div_iff₀ hw).mp (min_le_right (1 - a j)
      ((M - ∑ i, c i - ∑ i, (d i - c i) * a i) / (d j - c j)))
    simpa only [mul_comm] using h
  let b := fun i => a i + if i = j then ε else 0
  have hs (q : ι → ℝ) : (∑ i, q i * b i) = (∑ i, q i * a i) + q j * ε := by
    simp [b, mul_add, Finset.sum_add_distrib, mul_ite]
  refine ⟨b, ⟨?_, ?_⟩, ?_⟩
  · intro i
    by_cases hi : i = j
    · subst i
      simp only [b, if_pos]
      exact ⟨by linarith [(ha.1 j).1], by linarith⟩
    · simpa [b, hi] using ha.1 i
  · rw [hs]
    linarith
  · rw [fill_value_translate, fill_value_translate]
    unfold FractionalKnapsackDual.objective
    rw [hs]
    exact lt_add_of_pos_right _ (mul_pos hv he)

/-- Every optimal fill with an unfilled positive row saturates its budget. -/
theorem fractional_optimum_saturates (c d : ι → ℝ) (M : ℝ) (a : ι → ℝ) (j : ι)
    (hc : ∀ i, 0 < c i) (hcd : ∀ i, c i < d i)
    (ha : FillOptimal c d M a) (hj : a j ∈ Ioo 0 1) :
    ∑ i, (d i - c i) * a i = M - ∑ i, c i := by
  apply le_antisymm ha.1.2
  by_contra hn
  obtain ⟨b, hb, hgain⟩ := slack_fill_improvable c d M a j ha.1 hj.2
    (sub_pos.mpr (hcd j))
    (sub_pos.mpr (logValue_strictMono (hc j) ((hc j).trans (hcd j)) (hcd j)))
    (lt_of_not_ge hn)
  have hbound := le_csSup (fill_values_bddAbove c d M) (show
    fillValue c d b ∈ fillValue c d '' {b | FillFeasible c d M b} from ⟨b, hb, rfl⟩)
  rw [← ha.2] at hbound
  exact (not_lt_of_ge hbound) hgain

#print axioms grid_dual_eq_fill_sup
#print axioms slack_fill_improvable
#print axioms fractional_optimum_saturates

end D5.S3.Analytic.Knapsack.GridDualStructure
