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

#print axioms two_point_grid_domain
#print axioms two_actual_corners_lower_mem

end D5.S3.Analytic.Interpolation.TwoPointGridDominance
