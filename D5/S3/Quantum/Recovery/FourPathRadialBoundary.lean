/- GID: D5/S3/Quantum/Recovery/FourPathRadialBoundary
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/FourPathRadialBoundary
   mirror-E: none(waiver:exact-radial-geometry)
   anchors: []
   utility: none
   digest: Exact sublevel, ambient boundary and unique positive radial coordinates for the four-path inequality domain. -/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic

/-! The literal four-coordinate inequality domain and its explicit radial functional.
No unitary realization, convexity, triangle law or producer contract is assumed.
-/

noncomputable section
open Set Filter Topology

namespace D5.S3.Quantum.Recovery.FourPathRadialBoundary

abbrev Point := Fin 4 → ℂ

def minMod (w : Point) : ℝ := min (min ‖w 0‖ ‖w 1‖) (min ‖w 2‖ ‖w 3‖)
def maxMod (w : Point) : ℝ := max (max ‖w 0‖ ‖w 1‖) (max ‖w 2‖ ‖w 3‖)
def totalMod (w : Point) : ℝ := ‖w 0‖ + ‖w 1‖ + ‖w 2‖ + ‖w 3‖

/-- Independent inequality-domain encoding, including zero and all tied extrema. -/
def W : Set Point := {w | (∀ j, ‖w j‖ ≤ 1) ∧ totalMod w - 2 * minMod w ≤ 2}

/-- Explicit functional; this definition makes no norm or convexity assertion. -/
def m (w : Point) : ℝ := max (maxMod w) ((totalMod w - 2 * minMod w) / 2)

private lemma maxMod_le_iff (w : Point) (a : ℝ) :
    maxMod w ≤ a ↔ ∀ j, ‖w j‖ ≤ a := by
  simp [maxMod, max_le_iff, Fin.forall_fin_succ, and_assoc]

private lemma norm_le_maxMod (w : Point) (j : Fin 4) : ‖w j‖ ≤ maxMod w :=
  (maxMod_le_iff w _).1 le_rfl j

private lemma m_nonneg (w : Point) : 0 ≤ m w :=
  (norm_nonneg (w 0)).trans ((norm_le_maxMod w 0).trans (le_max_left _ _))

private lemma m_eq_zero_iff (w : Point) : m w = 0 ↔ w = 0 := by
  constructor
  · intro h
    funext j
    apply norm_eq_zero.mp
    have hle : ‖w j‖ ≤ m w := (norm_le_maxMod w j).trans (le_max_left _ _)
    exact le_antisymm (by simpa [h] using hle) (norm_nonneg _)
  · rintro rfl
    simp [m, maxMod, minMod, totalMod]

private lemma continuous_m : Continuous m := by
  unfold m maxMod minMod totalMod
  fun_prop

private lemma m_smul (t : ℝ) (ht : 0 ≤ t) (w : Point) : m (t • w) = t * m w := by
  simp only [m, maxMod, minMod, totalMod, Pi.smul_apply, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg ht]
  rw [← mul_max_of_nonneg _ _ ht, ← mul_max_of_nonneg _ _ ht,
    ← mul_max_of_nonneg _ _ ht, ← mul_min_of_nonneg _ _ ht,
    ← mul_min_of_nonneg _ _ ht, ← mul_min_of_nonneg _ _ ht]
  have h : (t * ‖w 0‖ + t * ‖w 1‖ + t * ‖w 2‖ + t * ‖w 3‖ -
      2 * (t * min (min ‖w 0‖ ‖w 1‖) (min ‖w 2‖ ‖w 3‖))) / 2 =
      t * ((‖w 0‖ + ‖w 1‖ + ‖w 2‖ + ‖w 3‖ -
      2 * min (min ‖w 0‖ ‖w 1‖) (min ‖w 2‖ ‖w 3‖)) / 2) := by ring
  rw [h, ← mul_max_of_nonneg _ _ ht]

private lemma mem_W_iff (w : Point) : w ∈ W ↔ m w ≤ 1 := by
  simp only [W, mem_setOf_eq, m, max_le_iff, maxMod_le_iff]
  constructor <;> rintro ⟨h, h'⟩ <;> exact ⟨h, by linarith⟩

/-- The explicit exterior sequence is the live construction behind the hard boundary inclusion. -/
private lemma exterior_approach (z : Point) (hz : m z = 1) :
    ∃ u : ℕ → Point, Tendsto u atTop (𝓝 z) ∧ ∀ n, u n ∉ W := by
  refine ⟨fun n => (1 + 1 / ((n : ℝ) + 1)) • z, ?_, ?_⟩
  · have h := (tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using h.smul_const z
  · intro n hn
    have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have he := m_smul (1 + 1 / ((n : ℝ) + 1)) (by positivity) z
    rw [hz, mul_one] at he
    have := (mem_W_iff _).1 hn
    linarith

private lemma not_interior_of_m_one (z : Point) (hz : m z = 1) : z ∉ interior W := by
  intro hi
  obtain ⟨u, hu, hout⟩ := exterior_approach z hz
  have he : ∀ᶠ n in atTop, u n ∈ W := hu (mem_interior_iff_mem_nhds.mp hi)
  obtain ⟨n, hn⟩ := eventually_atTop.1 he
  exact hout n (hn n le_rfl)

private lemma interior_W : interior W = {w | m w < 1} := by
  apply Subset.antisymm
  · intro w hw
    have hle := (mem_W_iff w).1 (interior_subset hw)
    exact lt_of_le_of_ne hle (fun h => not_interior_of_m_one w h hw)
  · apply interior_maximal
    · intro w hw
      exact (mem_W_iff w).2 hw.le
    · exact isOpen_lt continuous_m continuous_const

private lemma frontier_W : frontier W = {w | m w = 1} := by
  have hc : IsClosed W := by
    have : W = {w | m w ≤ 1} := Set.ext mem_W_iff
    rw [this]
    exact isClosed_le continuous_m continuous_const
  rw [hc.frontier_eq, interior_W]
  ext w
  simp only [mem_diff, mem_setOf_eq, mem_W_iff, not_lt]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

private lemma saturation (z : Point) : m z = 1 ↔
    z ∈ W ∧ (maxMod z = 1 ∨ totalMod z - 2 * minMod z = 2) := by
  constructor
  · intro h
    refine ⟨(mem_W_iff z).2 h.le, ?_⟩
    rcases le_total ((totalMod z - 2 * minMod z) / 2) (maxMod z) with hh | hh
    · exact Or.inl (by simpa [m, max_eq_left hh] using h)
    · right
      have : (totalMod z - 2 * minMod z) / 2 = 1 := by
        simpa [m, max_eq_right hh] using h
      linarith
  · rintro ⟨hw, ha | hb⟩
    · apply le_antisymm ((mem_W_iff z).1 hw)
      calc
        1 = maxMod z := ha.symm
        _ ≤ m z := le_max_left _ _
    · apply le_antisymm ((mem_W_iff z).1 hw)
      have : (totalMod z - 2 * minMod z) / 2 = 1 := by linarith
      calc
        1 = (totalMod z - 2 * minMod z) / 2 := this.symm
        _ ≤ m z := le_max_right _ _

private lemma radial (w : Point) (hw : w ∈ W) (hw0 : w ≠ 0) :
    ∃ t : ℝ, ∃ z : Point, 0 < t ∧ t ≤ 1 ∧ t = m w ∧ m z = 1 ∧ w = t • z ∧
      ∀ s : ℝ, ∀ y : Point, 0 < s → m y = 1 → w = s • y → s = t ∧ y = z := by
  have hp : 0 < m w := lt_of_le_of_ne (m_nonneg w)
    (fun h => hw0 ((m_eq_zero_iff w).1 h.symm))
  refine ⟨m w, (m w)⁻¹ • w, hp, (mem_W_iff w).1 hw, rfl, ?_, ?_, ?_⟩
  · rw [m_smul _ (inv_nonneg.mpr hp.le), inv_mul_cancel₀ hp.ne']
  · rw [smul_smul, mul_inv_cancel₀ hp.ne', one_smul]
  · intro s y hs hy he
    have hm : m w = s := by rw [he, m_smul s hs.le y, hy, mul_one]
    refine ⟨hm.symm, ?_⟩
    rw [hm, he, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]

/-- Complete literal radial geometry. The inclusive disjunction retains simultaneous
saturation, and uniqueness compares every positive radial representation. -/
theorem exact_radial_boundary :
    W = {w | m w ≤ 1} ∧
    interior W = {w | m w < 1} ∧
    frontier W = {w | m w = 1} ∧
    frontier W = {z | z ∈ W ∧ (maxMod z = 1 ∨ totalMod z - 2 * minMod z = 2)} ∧
    (∀ w ∈ W, w ≠ 0 →
      ∃ t : ℝ, ∃ z : Point, 0 < t ∧ t ≤ 1 ∧ t = m w ∧ m z = 1 ∧ w = t • z ∧
        ∀ s : ℝ, ∀ y : Point, 0 < s → m y = 1 → w = s • y → s = t ∧ y = z) := by
  refine ⟨Set.ext mem_W_iff, interior_W, frontier_W, ?_, radial⟩
  rw [frontier_W]
  exact Set.ext saturation

end D5.S3.Quantum.Recovery.FourPathRadialBoundary
