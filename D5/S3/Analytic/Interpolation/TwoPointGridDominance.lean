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
private theorem corner_le_grid_dual (c d : Fin 2 → ℝ) (M : ℝ) (x : Fin 2 → ℝ)
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
private theorem grid_dual_eq_fractional_sup (c d : Fin 2 → ℝ) (M : ℝ)
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

private theorem pair_value_spread {m r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) (hRm : R < m) :
    logValue (m - R) + logValue (m + R) ≤ logValue (m - r) + logValue (m + r) := by
  rcases hrR.eq_or_lt with h | h
  · rw [h]
  have hR : 0 < R := hr.trans_lt h
  let a := (R + r) / (2 * R)
  let b := (R - r) / (2 * R)
  have ha : 0 < a := div_pos (by linarith) (by positivity)
  have hb : 0 < b := div_pos (by linarith) (by positivity)
  have hab : a + b = 1 := by dsimp [a, b]; field_simp; ring
  have hleft : a * (m - R) + b * (m + R) = m - r := by
    dsimp [a, b]; field_simp; ring
  have hright : a * (m + R) + b * (m - R) = m + r := by
    dsimp [a, b]; field_simp; ring
  have hx : m - R ∈ Ioi (0 : ℝ) := sub_pos.mpr hRm
  have hy : m + R ∈ Ioi (0 : ℝ) := by change 0 < m + R; linarith
  have hxy : m - R ≠ m + R := by linarith
  have h1 := logValue_strictConcave.2 hx hy hxy ha hb hab
  have h2 := logValue_strictConcave.2 hy hx hxy.symm ha hb hab
  simp only [smul_eq_mul, hleft, hright] at h1 h2
  have hsum := add_lt_add h1 h2
  have hid : (a * logValue (m - R) + b * logValue (m + R)) +
      (a * logValue (m + R) + b * logValue (m - R)) =
      logValue (m - R) + logValue (m + R) := by
    calc
      _ = (a + b) * (logValue (m - R) + logValue (m + R)) := by ring
      _ = _ := by rw [hab, one_mul]
  rw [hid] at hsum
  exact hsum.le

/-- The inner secant and the fixed coordinate have exactly the two-node quadratic moments. -/
private theorem inner_secant_quadratic_moments (m v s A B C : ℝ) (hv : 0 < v) (hs : |s| < v) :
    let θ := 2 * (v + s) / (3 * v + s)
    let P := fun x => A + B * (x - (m - v)) + C * (x - (m - v)) ^ 2
    (1 - θ) * P (m - 2 * v - s) + θ * P (m + v) + P (m - s) =
      P (m - v) + P (m + v) := by
  have hs' := abs_lt.mp hs
  have hden : 3 * v + s ≠ 0 := by linarith
  have hden' : v * 3 + s ≠ 0 := by linarith
  dsimp only
  ring_nf
  field_simp [hden, hden']
  <;> ring

private theorem inner_secant_bound {m v s : ℝ} (hv : 0 < v) (hs : |s| < v)
    (hc : 0 < m - 2 * v - s) :
    let θ := 2 * (v + s) / (3 * v + s)
    (1 - θ) * logValue (m - 2 * v - s) + θ * logValue (m + v) + logValue (m - s) ≤
      logValue (m - v) + logValue (m + v) := by
  have hs' := abs_lt.mp hs
  let L := m - v
  let H := m + v
  have hL : 0 < L := by dsimp [L]; linarith
  have hLH : L < H := by dsimp [L, H]; linarith
  let C := (logValue H - logValue L - deriv logValue L * (H - L)) / (H - L) ^ 2
  let P := fun x => logValue L + deriv logValue L * (x - L) + C * (x - L) ^ 2
  have hPL : P L = logValue L := by dsimp [P]; ring
  have hPH : P H = logValue H := by
    dsimp [P, C]
    rw [div_mul_cancel₀ _ (pow_ne_zero 2 (sub_ne_zero.mpr hLH.ne'))]
    ring
  have hder := quadratic_derivatives (logValue L) (deriv logValue L) C L
  have hP : ContDiff ℝ 3 P := by dsimp [P]; fun_prop
  have hlog := LogOneSubExpDerivatives.log_one_sub_exp_derivatives
  have hmajor (x : ℝ) (hx : 0 < x) (hxH : x ≤ H) : logValue x ≤ P x := by
    by_cases hxL : x = L
    · simpa [hxL, hPL]
    by_cases hxH' : x = H
    · simpa [hxH', hPH]
    exact (hermite_strict_majorant L H x logValue P hL hLH hx hxH hxL hxH'
      hlog.1 hP hder.2 hPL hder.1 hPH (fun t ht => (hlog.2 t ht).2.2.2)).le
  let θ := 2 * (v + s) / (3 * v + s)
  have hden : 0 < 3 * v + s := by linarith
  have ht0 : 0 ≤ θ := (div_pos (by linarith) hden).le
  have ht1 : θ ≤ 1 := (div_le_one hden).mpr (by linarith)
  have h1 := mul_le_mul_of_nonneg_left
    (hmajor (m - 2 * v - s) hc (by dsimp [H]; linarith)) (sub_nonneg.mpr ht1)
  have h2 := mul_le_mul_of_nonneg_left
    (hmajor (m + v) (by linarith) (by exact le_rfl)) ht0
  have h3 := hmajor (m - s) (by linarith) (by dsimp [H]; linarith)
  have hmoment := inner_secant_quadratic_moments m v s
    (logValue L) (deriv logValue L) C hv hs
  change (1 - θ) * P (m - 2 * v - s) + θ * P (m + v) + P (m - s) = P L + P H at hmoment
  rw [hPL, hPH] at hmoment
  dsimp only
  change (1 - θ) * logValue (m - 2 * v - s) + θ * logValue (m + v) + logValue (m - s) ≤ _
  linarith

private theorem pair_bound {x y V : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hV : V ≤ (x - y) ^ 2 / 2) :
    logValue x + logValue y ≤ psiTwo ((x + y) / 2) V := by
  let m := (x + y) / 2
  let R := |(x - y) / 2|
  have hR : 0 ≤ R := abs_nonneg _
  have hRm : R < m := by
    dsimp [R, m]
    rw [abs_lt]
    constructor <;> linarith
  have hs : Real.sqrt (V / 2) ≤ R := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨hR, ?_⟩
    dsimp [R]
    rw [sq_abs]
    nlinarith
  have hp := pair_value_spread (Real.sqrt_nonneg (V / 2)) hs hRm
  change _ ≤ psiTwo m V at hp
  have he : logValue (m - R) + logValue (m + R) = logValue x + logValue y := by
    dsimp [m, R]
    rcases le_total y x with h | h
    · rw [abs_of_nonneg (by linarith : 0 ≤ (x - y) / 2)]
      have h₁ : (x + y) / 2 - (x - y) / 2 = y := by ring
      have h₂ : (x + y) / 2 + (x - y) / 2 = x := by ring
      rw [h₁, h₂, add_comm]
    · rw [abs_of_nonpos (by linarith : (x - y) / 2 ≤ 0)]
      have h₁ : (x + y) / 2 - -((x - y) / 2) = x := by ring
      have h₂ : (x + y) / 2 + -((x - y) / 2) = y := by ring
      rw [h₁, h₂]
  rw [he] at hp
  exact hp

private theorem secant_contract {c d C D z θ : ℝ}
    (hc : 0 < c) (hcd : c < d) (hcC : c ≤ C) (hCD : C < D) (hDd : D ≤ d)
    (hz : z ∈ Icc C D) (hθ : θ ∈ Icc 0 1) (hmean : (1 - θ) * c + θ * d = z) :
    (1 - θ) * logValue c + θ * logValue d ≤
      (1 - (z - C) / (D - C)) * logValue C + (z - C) / (D - C) * logValue D := by
  have hdc : d - c ≠ 0 := sub_ne_zero.mpr hcd.ne'
  have hDC : D - C ≠ 0 := sub_ne_zero.mpr hCD.ne'
  let A := fun x => (1 - (x - c) / (d - c)) * logValue c +
    (x - c) / (d - c) * logValue d
  have hA (x : ℝ) (hx : x ∈ Icc c d) : A x ≤ logValue x := by
    have ht0 : 0 ≤ (x - c) / (d - c) := div_nonneg (by linarith [hx.1]) (by linarith)
    have ht1 : (x - c) / (d - c) ≤ 1 := (div_le_one (sub_pos.mpr hcd)).mpr (by linarith [hx.2])
    have he : (1 - (x - c) / (d - c)) * c + (x - c) / (d - c) * d = x := by
      field_simp [hdc, hDC]
      <;> ring
    have hh := logValue_strictConcave.concaveOn.2 hc (hc.trans hcd)
      (sub_nonneg.mpr ht1) ht0 (by ring)
    simpa only [smul_eq_mul, he] using hh
  have hden : 0 < D - C := sub_pos.mpr hCD
  have ht0 : 0 ≤ (z - C) / (D - C) := div_nonneg (by linarith [hz.1]) hden.le
  have ht1 : (z - C) / (D - C) ≤ 1 := (div_le_one hden).mpr (by linarith [hz.2])
  have h₁ := mul_le_mul_of_nonneg_left (hA C ⟨hcC, hCD.le.trans hDd⟩) (sub_nonneg.mpr ht1)
  have h₂ := mul_le_mul_of_nonneg_left (hA D ⟨hcC.trans hCD.le, hDd⟩) ht0
  have he : (1 - (z - C) / (D - C)) * A C + (z - C) / (D - C) * A D =
      (1 - θ) * logValue c + θ * logValue d := by
    dsimp [A]
    rw [← hmean]
    field_simp [hdc, hDC]
    <;> ring
  linarith

private theorem fractional_row_bound {c d t u M₀ M₁ θ : ℝ}
    (hc : 0 < c) (hcd : c < d) (ht : 0 < t)
    (hM : M₀ < M₁)
    (htwo : {p : ℝ × ℝ | (p.1 = c ∨ p.1 = d) ∧ (p.2 = t ∨ p.2 = u) ∧
      M₀ ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ M₁}.Nontrivial)
    (hθ : θ ∈ Ioo 0 1) (hbudget : (1 - θ) * c + θ * d + t = M₁) :
    (1 - θ) * logValue c + θ * logValue d + logValue t ≤
      psiTwo (M₁ / 2) (gridDistance (M₀ / 2) (M₁ / 2) c d ^ 2 +
        gridDistance (M₀ / 2) (M₁ / 2) t u ^ 2) := by
  let m := M₁ / 2
  let a := M₀ / 2
  let z := (1 - θ) * c + θ * d
  let s := z - m
  let v := gridDistance a m c d
  let e := gridDistance a m t u
  have ham : a ≤ m := by dsimp [a, m]; linarith
  have hcz : c < z := by dsimp [z]; nlinarith [hθ.1]
  have hzd : z < d := by dsimp [z]; nlinarith [hθ.2]
  have hzpos : 0 < z := hc.trans hcz
  have htform : t = m - s := by dsimp [m, s, z]; linarith [hbudget]
  have hzform : z = m + s := by dsimp [s]; ring
  have him : m ∈ Icc a m := ⟨ham, le_rfl⟩
  have he : e ≤ |s| := by
    have hh := gridDistance_le (Or.inl (show t = t from Eq.refl t)) him (d := u)
    simpa only [e, htform, sub_sub_cancel_left, abs_neg] using hh
  have hv0 : 0 ≤ v := gridDistance_nonneg _ _ _ _
  have he0 : 0 ≤ e := gridDistance_nonneg _ _ _ _
  have he2 : e ^ 2 ≤ s ^ 2 := by nlinarith [sq_abs s]
  have hsum : (z + t) / 2 = m := by dsimp [m, z]; linarith [hbudget]
  change _ ≤ psiTwo m (v ^ 2 + e ^ 2)
  by_cases hsmall : v ^ 2 + e ^ 2 ≤ 2 * s ^ 2
  · have hj := logValue_strictConcave.concaveOn.2 hc (hc.trans hcd)
      (by linarith [hθ.2] : 0 ≤ 1 - θ) hθ.1.le (by ring)
    simp only [smul_eq_mul] at hj
    have hp := pair_bound hzpos ht (V := v ^ 2 + e ^ 2) (by rw [htform, hzform]; nlinarith)
    rw [hsum] at hp
    exact (add_le_add hj (le_refl (logValue t))).trans hp
  have hsv : |s| < v := by nlinarith [sq_abs s, abs_nonneg s]
  have hv : 0 < v := (abs_nonneg s).trans_lt hsv
  have hlow := two_actual_corners_lower_mem htwo
    (by dsimp [z] at hcz; linarith [hbudget])
    (by dsimp [z] at hzd; linarith [hbudget])
  have hca : c < a := by
    by_contra hn
    have hac : a ≤ c := le_of_not_gt hn
    by_cases hcm : c ≤ m
    · have hd0 : Metric.infDist c (Icc a m) = 0 := Metric.infDist_zero_of_mem ⟨hac, hcm⟩
      have hh : v ≤ 0 := by dsimp [v, gridDistance]; rw [hd0]; exact min_le_left _ _
      linarith
    · have hh := gridDistance_le (Or.inl (Eq.refl c)) him (d := d)
      rw [abs_of_nonneg (by linarith : 0 ≤ c - m)] at hh
      have hzsm : c - m < s := by dsimp [s]; linarith
      linarith [le_abs_self s]
  have hmd : m < d := by
    by_contra hn
    have hdm : d ≤ m := le_of_not_gt hn
    by_cases had : a ≤ d
    · have hd0 : Metric.infDist d (Icc a m) = 0 := Metric.infDist_zero_of_mem ⟨had, hdm⟩
      have hh : v ≤ 0 := by dsimp [v, gridDistance]; rw [hd0]; exact min_le_right _ _
      linarith
    · have hh := gridDistance_le (Or.inr (Eq.refl d)) (show a ∈ Icc a m from ⟨le_rfl, ham⟩) (c := c)
      rw [abs_of_nonpos (by linarith : d - a ≤ 0)] at hh
      have hzsm : m - d < -s := by dsimp [s]; linarith
      linarith [neg_le_abs s]
  have hvleft : v ≤ a - c := by
    have hh := gridDistance_le (Or.inl (Eq.refl c)) (show a ∈ Icc a m from ⟨le_rfl, ham⟩) (d := d)
    simpa only [abs_of_nonpos (sub_nonpos.mpr hca.le), neg_sub] using hh
  have hvright : v ≤ d - m := by
    simpa only [abs_of_nonneg (sub_nonneg.mpr hmd.le)] using
      gridDistance_le (Or.inr (Eq.refl d)) him (c := c)
  have hcinner : c ≤ m - 2 * v - s := by
    have haa : a ≤ (c + t) / 2 := by dsimp [a]; linarith [hlow.1]
    rw [htform] at haa
    linarith
  have hs := abs_lt.mp hsv
  have hinner := secant_contract hc hcd hcinner
    (by linarith : m - 2 * v - s < m + v) (by linarith : m + v ≤ d)
    (z := z) (θ := θ) (by rw [hzform]; constructor <;> linarith) ⟨hθ.1.le, hθ.2.le⟩ (Eq.refl z)
  have hfrac : (z - (m - 2 * v - s)) / (m + v - (m - 2 * v - s)) =
      2 * (v + s) / (3 * v + s) := by rw [hzform]; congr 1 <;> ring
  rw [hfrac] at hinner
  have hh := inner_secant_bound hv hsv (hc.trans_le hcinner)
  dsimp only at hh
  rw [← htform] at hh
  have hrad : Real.sqrt ((v ^ 2 + e ^ 2) / 2) ≤ v := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hv.le, by nlinarith [sq_abs s]⟩
  have hvm : v < m := by linarith
  exact ((add_le_add hinner (le_refl (logValue t))).trans hh).trans
    (pair_value_spread (Real.sqrt_nonneg _) hrad hvm)

-- Positive grids and two different actual corners inhabit the hypotheses.
example : (∀ i : Fin 2, 0 < (![1, 1] : Fin 2 → ℝ) i) ∧
    (∀ i : Fin 2, (![1, 1] : Fin 2 → ℝ) i < (![2, 2] : Fin 2 → ℝ) i) ∧
    (2 : ℝ) < 3 ∧ (corners ![1, 1] ![2, 2] 2 3).Nontrivial := by
  refine ⟨?_, ?_, by norm_num, ?_⟩
  · intro i; fin_cases i <;> norm_num
  · intro i; fin_cases i <;> norm_num
  · refine ⟨(1, 1), ?_, (1, 2), ?_, ?_⟩ <;> norm_num [corners]

#print axioms fractional_row_bound
#print axioms psiTwo_mono_mean
#print axioms two_point_grid_domain
#print axioms two_actual_corners_lower_mem
#print axioms corner_le_grid_dual
#print axioms grid_dual_eq_fractional_sup

end D5.S3.Analytic.Interpolation.TwoPointGridDominance
