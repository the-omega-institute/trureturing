/- GID: D5/S3/StatisticalMechanics/SingleEntrySecularRoot
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/SingleEntrySecularRoot
   mirror-E: none(waiver:finite-positive-rate-secular-equation)
   anchors: []
   utility: none
   digest: The single-entry secular function has one root below all free rates. -/

import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

/-! # The scalar secular root of the single-entry inhibition network -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators
open Set

namespace D5.S3.StatisticalMechanics.SingleEntrySecularRoot

/-- Free relaxation rate of a site with binding and unbinding rates `a`, `b`. -/
def siteRate {ι : Type*} (a b : ι → ℝ) (i : ι) : ℝ := a i + b i

/-- Free equilibrium occupancy. -/
def occupancy {ι : Type*} (a b : ι → ℝ) (i : ι) : ℝ := a i / siteRate a b i

/-- The free product generator's subset rate. -/
def subsetRate {ι : Type*} (a b : ι → ℝ) (S : Finset ι) : ℝ :=
  ∑ i ∈ S, siteRate a b i

/-- Product weight of the subset mode at the empty configuration. -/
def modeWeight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (S : Finset ι) : ℝ :=
  ∏ i, if i ∈ S then occupancy a b i else 1 - occupancy a b i

/-- The scalar function, with the zero subset excluded from the resolvent sum. -/
def secular {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (η θ x : ℝ) : ℝ :=
  θ + η * modeWeight a b ∅ - x -
    η * x * ∑ S ∈ (Finset.univ.erase (∅ : Finset ι)),
      modeWeight a b S / (subsetRate a b S - x)

/-- The pole-weight expression supplied for the derivative of the secular function. -/
def secularSlope {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (η x : ℝ) : ℝ :=
  -1 - η * ∑ S ∈ (Finset.univ.erase (∅ : Finset ι)),
    modeWeight a b S * subsetRate a b S / (subsetRate a b S - x) ^ 2

private def rationalSecular {α : Type*} (T : Finset α) (v w : α → ℝ)
    (C η x : ℝ) : ℝ := C - x - η * x * ∑ k ∈ T, w k / (v k - x)

private theorem rational_derivative {α : Type*} (T : Finset α) (v w : α → ℝ)
    (C η x : ℝ) (hx : ∀ k ∈ T, v k - x ≠ 0) :
    HasDerivAt (rationalSecular T v w C η)
      (-1 - η * ∑ k ∈ T, w k * v k / (v k - x) ^ 2) x := by
  have hterm (k : α) (hk : k ∈ T) :
      HasDerivAt (fun u => u * (w k / (v k - u)))
        (w k * v k / (v k - x) ^ 2) x := by
    have hd := (hasDerivAt_id x).mul
      ((hasDerivAt_const x (w k)).div
        ((hasDerivAt_const x (v k)).sub (hasDerivAt_id x)) (hx k hk))
    convert hd using 1
    · rfl
    · dsimp
      field_simp [hx k hk]
      ring
  have hsum := HasDerivAt.fun_sum hterm
  have hd := ((hasDerivAt_const x C).sub (hasDerivAt_id x)).sub (hsum.const_mul η)
  convert hd using 1
  · funext u
    simp [rationalSecular, Finset.mul_sum, mul_assoc]
  · ring

private theorem rational_strictAnti {α : Type*} (T : Finset α) (v w : α → ℝ)
    (C η m : ℝ) (hη : 0 < η) (hw : ∀ k ∈ T, 0 ≤ w k)
    (hv : ∀ k ∈ T, m ≤ v k) :
    StrictAntiOn (rationalSecular T v w C η) (Ico 0 m) := by
  intro x hx y hy hxy
  have hterm (k : α) (hk : k ∈ T) :
      x * (w k / (v k - x)) ≤ y * (w k / (v k - y)) := by
    have hdx : 0 < v k - x := by linarith [hv k hk, hx.2]
    have hdy : 0 < v k - y := by linarith [hv k hk, hy.2]
    have hv0 : 0 < v k := by linarith [hv k hk, hy.2, hy.1]
    rw [← mul_div_assoc, ← mul_div_assoc, div_le_div_iff₀ hdx hdy]
    nlinarith [mul_nonneg (mul_nonneg (hw k hk) hv0.le) (sub_nonneg.mpr hxy.le)]
  have hs := Finset.sum_le_sum hterm
  simp only [← Finset.mul_sum] at hs
  have hh := mul_le_mul_of_nonneg_left hs hη.le
  unfold rationalSecular
  linarith

/-- A single positive pole already forces a negative value strictly before the first pole. -/
private theorem rational_negative_point {α : Type*} [DecidableEq α]
    (T : Finset α) (v w : α → ℝ) (C η m : ℝ)
    (hC : 0 < C) (hη : 0 < η) (hm : 0 < m)
    (hw : ∀ k ∈ T, 0 ≤ w k) (hv : ∀ k ∈ T, m ≤ v k)
    (j : α) (hj : j ∈ T) (hvj : v j = m) (hwj : 0 < w j) :
    ∃ z ∈ Ioo 0 m, rationalSecular T v w C η z < 0 := by
  let D := C + η * w j
  let z := m * C / D
  have hD : 0 < D := by dsimp [D]; positivity
  have hz : 0 < z := by dsimp [z]; positivity
  have hzm : z < m := by
    dsimp [z]
    rw [div_lt_iff₀ hD]
    dsimp [D]
    nlinarith [mul_pos hm (mul_pos hη hwj)]
  have hpole : η * z * (w j / (v j - z)) = C := by
    rw [hvj]
    dsimp [z, D]
    field_simp
    <;> ring
  have hsum : w j / (v j - z) ≤ ∑ k ∈ T, w k / (v k - z) := by
    exact Finset.single_le_sum (f := fun k => w k / (v k - z))
      (fun k hk => div_nonneg (hw k hk) (by linarith [hv k hk])) hj
  have hcharge := mul_le_mul_of_nonneg_left hsum (mul_nonneg hη.le hz.le)
  rw [hpole] at hcharge
  refine ⟨z, ⟨hz, hzm⟩, ?_⟩
  unfold rationalSecular
  linarith

private theorem rational_unique_root {α : Type*} [DecidableEq α]
    (T : Finset α) (v w : α → ℝ) (C η m : ℝ)
    (hC : 0 < C) (hη : 0 < η) (hm : 0 < m)
    (hw : ∀ k ∈ T, 0 ≤ w k) (hv : ∀ k ∈ T, m ≤ v k)
    (j : α) (hj : j ∈ T) (hvj : v j = m) (hwj : 0 < w j) :
    ∃! x, x ∈ Ioo 0 m ∧ rationalSecular T v w C η x = 0 := by
  obtain ⟨z, hz, hneg⟩ :=
    rational_negative_point T v w C η m hC hη hm hw hv j hj hvj hwj
  have hc : ContinuousOn (rationalSecular T v w C η) (Icc 0 z) := by
    unfold rationalSecular
    apply ContinuousOn.sub
    · exact continuousOn_const.sub continuousOn_id
    · apply ContinuousOn.mul
      · exact continuousOn_const.mul continuousOn_id
      · apply continuousOn_finsetSum
        intro k hk
        apply continuousOn_const.div (continuousOn_const.sub continuousOn_id)
        intro x hx
        have : 0 < v k - x := by linarith [hv k hk, hz.2, hx.2]
        exact ne_of_gt this
  have hzero : rationalSecular T v w C η 0 = C := by simp [rationalSecular]
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc' hz.1.le hc
    (show 0 ∈ Icc (rationalSecular T v w C η z)
      (rationalSecular T v w C η 0) from ⟨hneg.le, by rw [hzero]; exact hC.le⟩)
  have hx0 : 0 < x := by
    rcases hx.1.eq_or_lt with h | h
    · exfalso
      have : C = 0 := by simpa [← h, hzero] using hfx
      linarith
    · exact h
  have hxm : x < m := lt_of_le_of_lt hx.2 hz.2
  refine ⟨x, ⟨⟨hx0, hxm⟩, hfx⟩, ?_⟩
  intro y hy
  exact (rational_strictAnti T v w C η m hη hw hv).injOn
    ⟨hy.1.1.le, hy.1.2⟩ ⟨hx0.le, hxm⟩ (hy.2.trans hfx.symm)

theorem weight_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (S : Finset ι) : 0 < modeWeight a b S := by
  unfold modeWeight
  apply Finset.prod_pos
  intro i _
  have hs : 0 < siteRate a b i := add_pos (ha i) (hb i)
  split_ifs
  · exact div_pos (ha i) hs
  · have hq : occupancy a b i < 1 := by
      unfold occupancy
      rw [div_lt_one hs]
      dsimp [siteRate]
      linarith [hb i]
    linarith

/-- For every nonempty finite family of positive binding and unbinding rates,
the specified secular function has exactly one root strictly below every free
site rate. Its derivative equals the supplied strictly negative pole-weight
expression throughout the nonnegative pre-pole interval. This statement does not identify the root with a generator eigenvalue. -/
theorem secular_unique_root {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (a b : ι → ℝ) (η θ : ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hη : 0 < η) (hθ : 0 < θ) :
    (∃! x : ℝ, 0 < x ∧ (∀ i, x < siteRate a b i) ∧ secular a b η θ x = 0) ∧
    ∀ x : ℝ, 0 ≤ x → (∀ i, x < siteRate a b i) →
      HasDerivAt (secular a b η θ) (secularSlope a b η x) x ∧
      secularSlope a b η x < 0 := by
  constructor
  · let rates := Finset.univ.image (siteRate a b)
    have hrates : rates.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
    let m := rates.min' hrates
    have hm_mem : m ∈ rates := Finset.min'_mem rates hrates
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm_mem
    have hmi (k : ι) : m ≤ siteRate a b k :=
      Finset.min'_le rates _ (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩)
    have hm : 0 < m := by rw [← hi]; exact add_pos (ha i) (hb i)
    let T : Finset (Finset ι) := Finset.univ.erase ∅
    have hT (S : Finset ι) (hS : S ∈ T) : S.Nonempty := by
      exact Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hS).1
    have hv (S : Finset ι) (hS : S ∈ T) : m ≤ subsetRate a b S := by
      obtain ⟨k, hk⟩ := hT S hS
      exact (hmi k).trans (Finset.single_le_sum
        (fun l _ => (add_pos (ha l) (hb l)).le) hk)
    have hj : ({i} : Finset ι) ∈ T := by simp [T]
    have hvj : subsetRate a b {i} = m := by simp [subsetRate, hi]
    have hC : 0 < θ + η * modeWeight a b ∅ :=
      add_pos hθ (mul_pos hη (weight_pos a b ha hb ∅))
    obtain ⟨x, hx, huniq⟩ := rational_unique_root T (subsetRate a b) (modeWeight a b)
      (θ + η * modeWeight a b ∅) η m hC hη hm
      (fun S _ => (weight_pos a b ha hb S).le) hv {i} hj hvj
      (weight_pos a b ha hb {i})
    refine ⟨x, ⟨hx.1.1, fun k => lt_of_lt_of_le hx.1.2 (hmi k), hx.2⟩, ?_⟩
    intro y hy
    apply huniq y
    exact ⟨⟨hy.1, by simpa [hi] using hy.2.1 i⟩, hy.2.2⟩
  · intro x hx hupper
    let T : Finset (Finset ι) := Finset.univ.erase ∅
    have hv (S : Finset ι) (hS : S ∈ T) : 0 < subsetRate a b S - x := by
      have hn : S.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hS).1
      obtain ⟨i, hi⟩ := hn
      have hsum : siteRate a b i ≤ subsetRate a b S :=
        Finset.single_le_sum (fun j _ => (add_pos (ha j) (hb j)).le) hi
      linarith [hupper i]
    constructor
    · have he : secular a b η θ =
          rationalSecular T (subsetRate a b) (modeWeight a b)
            (θ + η * modeWeight a b ∅) η := rfl
      rw [he]
      exact rational_derivative T (subsetRate a b) (modeWeight a b)
        (θ + η * modeWeight a b ∅) η x (fun S hS => ne_of_gt (hv S hS))
    · have hsum : 0 ≤ ∑ S ∈ T,
          modeWeight a b S * subsetRate a b S / (subsetRate a b S - x) ^ 2 := by
        apply Finset.sum_nonneg
        intro S hS
        apply div_nonneg
        · exact mul_nonneg (weight_pos a b ha hb S).le (by linarith [hv S hS])
        · exact sq_nonneg _
      dsimp [secularSlope]
      change -1 - η * (∑ S ∈ T, _) < 0
      nlinarith [mul_nonneg hη.le hsum]

#print axioms secular_unique_root
#print axioms weight_pos

end D5.S3.StatisticalMechanics.SingleEntrySecularRoot
