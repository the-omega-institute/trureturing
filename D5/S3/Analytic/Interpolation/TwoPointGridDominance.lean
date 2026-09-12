/- GID: D5/S3/Analytic/Interpolation/TwoPointGridDominance
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/TwoPointGridDominance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual corners bound the distance variance and locate the lower corner of a fractional row. -/

import D5.S3.Analytic.Interpolation.HermiteEnvelopeEquality
import D5.S3.Analytic.Knapsack.FractionalKnapsackDual
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Algebra.Order.Group.CompleteLattice
import Batteries.Tactic.OpenPrivate

open Set
open scoped BigOperators

noncomputable section

namespace D5.S3.Analytic.Interpolation.TwoPointGridDominance

/-- The logarithmic objective on positive coordinates. -/
def logValue (x : ℝ) : ℝ := Real.log (1 - Real.exp (-x))

/-- The distance from a closed interval to a two-point set. -/
def gridDistance (a b c d : ℝ) : ℝ :=
  min (Metric.infDist c (Icc a b)) (Metric.infDist d (Icc a b))

/-- Actual grid corners whose coordinate sums belong to the closed budget slab. -/
def corners (c d : Fin 2 → ℝ) (M₀ M₁ : ℝ) : Set (ℝ × ℝ) :=
  {p | (p.1 = c 0 ∨ p.1 = d 0) ∧ (p.2 = c 1 ∨ p.2 = d 1) ∧
    M₀ ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ M₁}

/-- The sum, rather than the average, of the two squared set distances. -/
def varianceFloor (c d : Fin 2 → ℝ) (M₀ M₁ : ℝ) : ℝ :=
  ∑ i, (gridDistance (M₀ / 2) (M₁ / 2) (c i) (d i)) ^ 2

/-- The value at a nonnegative budget price. -/
def gridDualValue (c d : Fin 2 → ℝ) (M price : ℝ) : ℝ :=
  price * M + ∑ i, max (logValue (c i) - price * c i)
    (logValue (d i) - price * d i)

/-- The separable price infimum. -/
def gridDual (c d : Fin 2 → ℝ) (M : ℝ) : ℝ :=
  ⨅ p : {p : ℝ // 0 ≤ p}, gridDualValue c d M p

/-- The two-coordinate envelope with total squared deviation V. -/
def psiTwo (m V : ℝ) : ℝ :=
  logValue (m - Real.sqrt (V / 2)) + logValue (m + Real.sqrt (V / 2))

private theorem gridDistance_nonneg (a b c d : ℝ) : 0 ≤ gridDistance a b c d :=
  le_min Metric.infDist_nonneg Metric.infDist_nonneg

private theorem gridDistance_le {a b c d x m : ℝ}
    (hx : x = c ∨ x = d) (hm : m ∈ Icc a b) :
    gridDistance a b c d ≤ |x - m| := by
  rcases hx with rfl | rfl
  · exact (min_le_left _ _).trans (by
      simpa only [Real.dist_eq] using Metric.infDist_le_dist_of_mem hm (x := x))
  · exact (min_le_right _ _).trans (by
      simpa only [Real.dist_eq] using Metric.infDist_le_dist_of_mem hm (x := x))

/-- A single positive actual corner already places the distance variance in the envelope domain. -/
theorem two_point_grid_domain (c d : Fin 2 → ℝ) (M₀ M₁ : ℝ)
    (hc : ∀ i, 0 < c i) (hcd : ∀ i, c i < d i)
    (hne : (corners c d M₀ M₁).Nonempty) :
    0 < M₁ / 2 ∧ 0 ≤ varianceFloor c d M₀ M₁ ∧
      varianceFloor c d M₀ M₁ < 2 * (M₁ / 2) ^ 2 := by
  obtain ⟨⟨x, y⟩, hx, hy, hlo, hhi⟩ := hne
  dsimp only at hx hy hlo hhi
  have hxpos : 0 < x :=
    hx.elim (fun h => h.symm ▸ hc 0) (fun h => h.symm ▸ (hc 0).trans (hcd 0))
  have hypos : 0 < y :=
    hy.elim (fun h => h.symm ▸ hc 1) (fun h => h.symm ▸ (hc 1).trans (hcd 1))
  let m := (x + y) / 2
  have hm : m ∈ Icc (M₀ / 2) (M₁ / 2) := ⟨by dsimp [m]; linarith, by dsimp [m]; linarith⟩
  have h0 := gridDistance_le hx hm
  have h1 := gridDistance_le hy hm
  have h0sq : gridDistance (M₀ / 2) (M₁ / 2) (c 0) (d 0) ^ 2 ≤ (x - m) ^ 2 := by
    nlinarith [sq_abs (x - m), gridDistance_nonneg (M₀ / 2) (M₁ / 2) (c 0) (d 0)]
  have h1sq : gridDistance (M₀ / 2) (M₁ / 2) (c 1) (d 1) ^ 2 ≤ (y - m) ^ 2 := by
    nlinarith [sq_abs (y - m), gridDistance_nonneg (M₀ / 2) (M₁ / 2) (c 1) (d 1)]
  have hV : varianceFloor c d M₀ M₁ ≤ (x - m) ^ 2 + (y - m) ^ 2 := by
    simpa only [varianceFloor, Fin.sum_univ_two] using add_le_add h0sq h1sq
  refine ⟨by linarith, Finset.sum_nonneg (fun i _ => sq_nonneg _), ?_⟩
  have hid : (x - m) ^ 2 + (y - m) ^ 2 = 2 * m ^ 2 - 2 * x * y := by dsimp [m]; ring
  have hmpos : 0 < m := by dsimp [m]; linarith
  nlinarith [mul_pos hxpos hypos, hm.2]

/-- With two actual corners, the lower endpoint of a straddling row lies in the slab. -/
theorem two_actual_corners_lower_mem {c d t u M₀ M₁ : ℝ}
    (htwo : {p : ℝ × ℝ | (p.1 = c ∨ p.1 = d) ∧ (p.2 = t ∨ p.2 = u) ∧
      M₀ ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ M₁}.Nontrivial)
    (hlower : c + t < M₁) (hupper : M₁ < d + t) :
    M₀ ≤ c + t ∧ c + t ≤ M₁ := by
  refine ⟨?_, hlower.le⟩
  obtain ⟨⟨x₁, x₂⟩, hx, ⟨y₁, y₂⟩, hy, hxy⟩ := htwo
  by_contra hn
  have hn' : c + t < M₀ := lt_of_not_ge hn
  rcases hx with ⟨hx₁, hx₂, hxlo, hxhi⟩
  rcases hy with ⟨hy₁, hy₂, hylo, hyhi⟩
  dsimp only at hx₁ hx₂ hxlo hxhi hy₁ hy₂ hylo hyhi
  rcases hx₁ with rfl | rfl <;> rcases hx₂ with rfl | rfl <;>
    rcases hy₁ with rfl | rfl <;> rcases hy₂ with rfl | rfl <;>
    first | exact hxy rfl | linarith

private theorem logValue_strictMono : StrictMonoOn logValue (Ioi 0) := by
  intro x hx y hy hxy
  apply Real.log_lt_log
  · exact sub_pos.mpr (by simpa using Real.exp_lt_exp.mpr (neg_neg_of_pos hx))
  · exact sub_lt_sub_left (Real.exp_lt_exp.mpr (neg_lt_neg hxy)) 1

private theorem psiTwo_mono_mean {m n V : ℝ} (hmn : m ≤ n)
    (hL : Real.sqrt (V / 2) < m) : psiTwo m V ≤ psiTwo n V := by
  unfold psiTwo
  apply add_le_add
  · exact logValue_strictMono.monotoneOn (sub_pos.mpr hL)
      (sub_pos.mpr (hL.trans_le hmn)) (by linarith)
  · have hm : 0 < m + Real.sqrt (V / 2) := by linarith [Real.sqrt_nonneg (V / 2)]
    have hn : 0 < n + Real.sqrt (V / 2) := by linarith [Real.sqrt_nonneg (V / 2)]
    exact logValue_strictMono.monotoneOn hm hn (by linarith)

private theorem logValue_strictConcave : StrictConcaveOn ℝ (Ioi 0) logValue := by
  have hlog := LogOneSubExpDerivatives.log_one_sub_exp_derivatives
  apply strictConcaveOn_of_deriv2_neg (convex_Ioi 0) hlog.1.continuousOn
  intro x hx
  have hxpos : 0 < x := interior_subset hx
  have hsecond := (hlog.2 x hxpos).2.1
  have he : 0 < Real.exp x - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hxpos)
  have hneg : -Real.exp x / (Real.exp x - 1) ^ 2 < 0 :=
    div_neg_of_neg_of_pos (neg_neg_of_pos (Real.exp_pos x)) (sq_pos_of_pos he)
  simpa only [logValue, iteratedDeriv_succ, iteratedDeriv_zero,
    Function.iterate_succ_apply, Function.iterate_zero, id_eq] using hsecond.trans_lt hneg

private theorem gridDualValue_translate (c d : Fin 2 → ℝ) (M price : ℝ) :
    gridDualValue c d M price = (∑ i, logValue (c i)) +
      Knapsack.FractionalKnapsackDual.dualValue (fun i => d i - c i)
        (fun i => logValue (d i) - logValue (c i)) (M - ∑ i, c i) price := by
  have hmax (i : Fin 2) :
      max (logValue (c i) - price * c i) (logValue (d i) - price * d i) =
        logValue (c i) - price * c i +
          max 0 (logValue (d i) - logValue (c i) - price * (d i - c i)) := by
    rw [add_max]
    congr 1 <;> ring
  simp only [gridDualValue, hmax, Knapsack.FractionalKnapsackDual.dualValue,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- Pricing either endpoint bounds every actual corner satisfying the upper budget. -/
theorem corner_le_grid_dual (c d : Fin 2 → ℝ) (M : ℝ) (x : Fin 2 → ℝ)
    (hx : ∀ i, x i = c i ∨ x i = d i) (hM : ∑ i, x i ≤ M) :
    (∑ i, logValue (x i)) ≤ gridDual c d M := by
  haveI : Nonempty {p : ℝ // 0 ≤ p} := ⟨⟨0, le_rfl⟩⟩
  apply le_ciInf
  intro p
  have hi (i : Fin 2) : logValue (x i) - (p : ℝ) * x i ≤
      max (logValue (c i) - (p : ℝ) * c i)
        (logValue (d i) - (p : ℝ) * d i) := by
    rcases hx i with h | h
    · rw [h]; exact le_max_left _ _
    · rw [h]; exact le_max_right _ _
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  have hb := mul_le_mul_of_nonneg_left hM p.property
  dsimp [gridDualValue]
  linarith

/-- Subtracting the lower endpoints identifies the grid dual with fractional knapsack. -/
theorem grid_dual_eq_fractional_sup (c d : Fin 2 → ℝ) (M : ℝ)
    (hc : ∀ i, 0 < c i) (hcd : ∀ i, c i < d i) (hM : ∑ i, c i ≤ M) :
    gridDual c d M = (∑ i, logValue (c i)) +
      sSup (Knapsack.FractionalKnapsackDual.objective
        (fun i => logValue (d i) - logValue (c i)) ''
        {a | Knapsack.FractionalKnapsackDual.Feasible (fun i => d i - c i)
          (M - ∑ i, c i) a}) := by
  haveI : Nonempty {p : ℝ // 0 ≤ p} := ⟨⟨0, le_rfl⟩⟩
  have hw (i : Fin 2) : 0 < d i - c i := sub_pos.mpr (hcd i)
  have hv (i : Fin 2) : 0 ≤ logValue (d i) - logValue (c i) :=
    sub_nonneg.mpr (logValue_strictMono (hc i) ((hc i).trans (hcd i)) (hcd i)).le
  have hb : 0 ≤ M - ∑ i, c i := sub_nonneg.mpr hM
  have hbounded : BddBelow (range (fun p : {p : ℝ // 0 ≤ p} =>
      Knapsack.FractionalKnapsackDual.dualValue (fun i => d i - c i)
        (fun i => logValue (d i) - logValue (c i)) (M - ∑ i, c i) p)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨p, rfl⟩
    exact add_nonneg (mul_nonneg p.property hb)
      (Finset.sum_nonneg (fun i _ => le_max_left _ _))
  simp only [gridDual, gridDualValue_translate]
  rw [← add_ciInf hbounded]
  rw [Knapsack.FractionalKnapsackDual.fractional_knapsack_strong_duality
    (fun i => d i - c i) (fun i => logValue (d i) - logValue (c i))
    (M - ∑ i, c i) hw hv hb]

open private hermite_strict_majorant quadratic_derivatives
  from D5.S3.Analytic.Interpolation.HermiteEnvelopeEquality

#print axioms psiTwo_mono_mean
#print axioms two_point_grid_domain
#print axioms two_actual_corners_lower_mem
#print axioms corner_le_grid_dual
#print axioms grid_dual_eq_fractional_sup

end D5.S3.Analytic.Interpolation.TwoPointGridDominance
