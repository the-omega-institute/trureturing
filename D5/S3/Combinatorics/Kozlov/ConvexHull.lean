/- GID: D5/S3/Combinatorics/Kozlov/ConvexHull
   generality: G
   mirror-B: none(waiver:probe-support)
   mirror-E: none(waiver:literal-kozlov-polytope)
   anchors: [mathlib/module/Mathlib.Combinatorics.SetFamily.LYM]
   utility: none
   digest: Normalized coordinate inequalities describe the convex hull of proper f-vectors. -/

import D5.S3.Combinatorics.Kozlov.ChainedCount
import Mathlib.Analysis.Convex.Combination
import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Fin.Basic

-- Source: https://gitlab.liu.se/jansn19/exterior-convex/-/blob/2f05ce99d059c305ffcf6142fcf9efbbca02e24f/lean/ExteriorConvex/Spine/LYM.lean
/-
Upstream pins: Lean v4.34.0-rc2, Mathlib 3a8a89422e16d67b7ae57698f6d96e389e4d4202.
Retire these declarations when the project's pinned Mathlib supplies equivalent results.

MIT License

Copyright (c) 2026 Jan Snellman

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

set_option autoImplicit false

open Finset
open scoped BigOperators FinsetFamily Pointwise

namespace D5.S3.Combinatorics.Kozlov

variable {n : ℕ}

theorem lym {D : Finset (Finset (Fin n))} (hD : IsComplex D) (j : ℕ) :
    (fEntry D (j + 1) : ℝ) / (n.choose (j + 1) : ℝ) ≤
      (fEntry D j : ℝ) / (n.choose j : ℝ) := by
  classical
  set 𝒜 : Finset (Finset (Fin n)) := D.filter (fun s => #s = j + 1) with h𝒜
  have hsized : (𝒜 : Set (Finset (Fin n))).Sized (j + 1) := fun s hs =>
    (mem_filter.mp hs).2
  have hlym := Finset.local_lubell_yamamoto_meshalkin_inequality_div
    (𝕜 := ℝ) j.succ_ne_zero hsized
  rw [Fintype.card_fin, Nat.succ_sub_one] at hlym
  have hshadow : ∂ 𝒜 ⊆ D.filter (fun s => #s = j) := by
    intro t ht
    rw [mem_shadow_iff] at ht
    obtain ⟨s, hs, a, ha, rfl⟩ := ht
    rw [mem_filter] at hs ⊢
    exact ⟨hD.down hs.1 (erase_subset a s),
      by rw [card_erase_of_mem ha, hs.2]; omega⟩
  have hle : (#(∂ 𝒜) : ℝ) ≤ (fEntry D j : ℝ) := by
    exact_mod_cast card_le_card hshadow
  calc (fEntry D (j + 1) : ℝ) / (n.choose (j + 1) : ℝ)
      = (#𝒜 : ℝ) / (n.choose (j + 1) : ℝ) := rfl
    _ ≤ (#(∂ 𝒜) : ℝ) / (n.choose j : ℝ) := hlym
    _ ≤ (fEntry D j : ℝ) / (n.choose j : ℝ) := by gcongr

/-! ## The skeleta and the LYM chain -/

/-- `eq:skeleton`, in the degree-0-inclusive space: the `f`-vector of the
complete `j`-skeleton on `[n]` — entry `0` is `1`, entries `1..j` are
`C(n,i)`, the rest `0`. -/
def skel (n j : ℕ) : Fin (n + 1) → ℝ := fun i =>
  if i.val = 0 then 1 else if i.val ≤ j then (n.choose i.val : ℝ) else 0

/-- The set of skeleta `{F̃_1, …, F̃_n}`, inclusively. -/
def skelSet (n : ℕ) : Set (Fin (n + 1) → ℝ) := skel n '' Set.Icc 1 n

/-- The right-hand side of `eq:mu` (`lem-mu`), in inclusive coordinates:
`x₀ = 1`, `μ₁ = 1` (i.e. `x₁ = n`), the LYM chain `μ_j ≥ μ_{j+1}` for
`1 ≤ j ≤ n-1`, and `μ_n ≥ 0`. -/
def lymChain (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {x | x 0 = 1 ∧ x 1 = (n : ℝ) ∧
    (∀ j, (hj : 1 ≤ j) → (hjn : j ≤ n - 1) →
      x ⟨j + 1, by omega⟩ / (n.choose (j + 1) : ℝ) ≤
        x ⟨j, by omega⟩ / (n.choose j : ℝ)) ∧
    0 ≤ x (Fin.last n)}

/-- For `n ≥ 1` the `Fin`-literal `1` really is the coordinate `1`.
(Utility; rung 3 uses it too.) -/
theorem fin_one_eq (hn : 1 ≤ n) :
    (1 : Fin (n + 1)) = ⟨1, by omega⟩ := by
  apply Fin.ext
  rw [Fin.val_one']
  exact Nat.mod_eq_of_lt (by omega)

/-- The chain set is convex: an intersection of two hyperplanes and finitely
many half-spaces, checked directly. -/
theorem convex_lymChain (n : ℕ) : Convex ℝ (lymChain n) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx0, hx1, hxc, hxn⟩ := hx
  obtain ⟨hy0, hy1, hyc, hyn⟩ := hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hx0, hy0, mul_one]
    exact hab
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hx1, hy1]
    rw [← add_mul, hab, one_mul]
  · intro j hj hjn
    have h1 := hxc j hj hjn
    have h2 := hyc j hj hjn
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_div,
      mul_div_assoc]
    exact add_le_add (mul_le_mul_of_nonneg_left h1 ha)
      (mul_le_mul_of_nonneg_left h2 hb)
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha hxn) (mul_nonneg hb hyn)


/-- The LYM ratio `μ_k(x) = x_k / C(n,k)` (`def-lym-ratios`), as a total
function of `k : ℕ`, zero beyond `n`. -/
noncomputable def muOf (n : ℕ) (x : Fin (n + 1) → ℝ) (k : ℕ) : ℝ :=
  if h : k ≤ n then x ⟨k, Nat.lt_succ_of_le h⟩ / (n.choose k : ℝ) else 0

theorem muOf_of_le {x : Fin (n + 1) → ℝ} {k : ℕ} (h : k ≤ n) :
    muOf n x k = x ⟨k, Nat.lt_succ_of_le h⟩ / (n.choose k : ℝ) :=
  dite_eq_left h

theorem muOf_of_gt {x : Fin (n + 1) → ℝ} {k : ℕ} (h : n < k) :
    muOf n x k = 0 :=
  dite_eq_right (by omega)

/-- Telescoping: `∑_{j=k}^{n} (μ_j − μ_{j+1}) = μ_k` for `k ≤ n`. -/
theorem sum_mu_telescope (x : Fin (n + 1) → ℝ) {k : ℕ} (hk : k ≤ n) :
    ∑ j ∈ Finset.Icc k n, (muOf n x j - muOf n x (j + 1)) = muOf n x k := by
  have hIcc : Finset.Icc k n = Finset.Ico k (n + 1) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  have hcongr : ∀ i ∈ Finset.range (n + 1 - k),
      muOf n x (k + i) - muOf n x (k + i + 1) =
        (fun i => muOf n x (k + i)) i - (fun i => muOf n x (k + i)) (i + 1) := by
    intro i _
    simp only []
    rw [← Nat.add_assoc]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_range_sub' (fun i => muOf n x (k + i))]
  simp only [Nat.add_zero]
  rw [show k + (n + 1 - k) = n + 1 by omega, muOf_of_gt (Nat.lt_succ_self n),
    sub_zero]

/-- The hard half of `lem-mu`: a point of the chain set is a convex
combination of the skeleta, with barycentric coordinates
`λ_j = μ_j − μ_{j+1}`, `λ_n = μ_n`. -/
theorem lymChain_subset_hull (hn : 1 ≤ n) :
    lymChain n ⊆ convexHull ℝ (skelSet n) := by
  intro x hx
  obtain ⟨hx0, hx1, hxc, hxn⟩ := hx
  set w : ℕ → ℝ := fun j => muOf n x j - muOf n x (j + 1) with hw
  -- μ₁ = 1, from x₁ = n.
  have hmu1 : muOf n x 1 = 1 := by
    rw [muOf_of_le hn, ← fin_one_eq hn, hx1, Nat.choose_one_right,
      div_self (Nat.cast_ne_zero.mpr (by omega : n ≠ 0))]
  -- The weights are non-negative.
  have hw0 : ∀ j ∈ Finset.Icc 1 n, 0 ≤ w j := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rcases eq_or_lt_of_le hj.2 with hjn | hjn
    · subst hjn
      rw [hw]
      simp only []
      rw [muOf_of_gt (Nat.lt_succ_self j), sub_zero, muOf_of_le (le_refl j),
        Nat.choose_self, Nat.cast_one, div_one]
      exact hxn
    · have h := hxc j hj.1 (by omega)
      rw [hw]
      simp only []
      rw [muOf_of_le (by omega : j ≤ n), muOf_of_le (by omega : j + 1 ≤ n),
        sub_nonneg]
      exact h
  -- The weights sum to 1.
  have hsum : ∑ j ∈ Finset.Icc 1 n, w j = 1 := by
    rw [hw]
    rw [sum_mu_telescope x hn, hmu1]
  -- Each skeleton is a generator.
  have hz : ∀ j ∈ Finset.Icc 1 n, skel n j ∈ skelSet n := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    exact Set.mem_image_of_mem _ (Set.mem_Icc.mpr hj)
  -- The convex combination reconstructs `x`.
  have hrepr : ∑ j ∈ Finset.Icc 1 n, w j • skel n j = x := by
    funext i
    rw [Finset.sum_apply]
    rcases Nat.eq_zero_or_pos i.val with hi0 | hipos
    · have hval : ∀ j ∈ Finset.Icc 1 n, (w j • skel n j) i = w j := by
        intro j hj
        rw [Pi.smul_apply, smul_eq_mul,
          show skel n j i = 1 by simp [skel, hi0], mul_one]
      rw [Finset.sum_congr rfl hval, hsum]
      have hi : i = 0 := Fin.ext hi0
      rw [hi, hx0]
    · have hkn : i.val ≤ n := by omega
      have hval : ∀ j ∈ Finset.Icc 1 n, (w j • skel n j) i =
          if i.val ≤ j then w j * (n.choose i.val : ℝ) else 0 := by
        intro j hj
        rw [Pi.smul_apply, smul_eq_mul]
        by_cases hkj : i.val ≤ j
        · rw [ite_eq_left hkj, show skel n j i = (n.choose i.val : ℝ) by
            simp only [skel]; rw [ite_eq_right (by omega), ite_eq_left hkj]]
        · rw [ite_eq_right hkj, show skel n j i = 0 by
            simp only [skel]; rw [ite_eq_right (by omega), ite_eq_right hkj], mul_zero]
      rw [Finset.sum_congr rfl hval, ← Finset.sum_filter]
      have hfilter : (Finset.Icc 1 n).filter (fun j => i.val ≤ j) =
          Finset.Icc i.val n := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_Icc]
        omega
      rw [hfilter, ← Finset.sum_mul, sum_mu_telescope x hkn,
        muOf_of_le hkn,
        div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.choose_pos hkn).ne')]
  have hcm := Finset.centerMass_mem_convexHull (Finset.Icc 1 n) hw0
    (by rw [hsum]; exact zero_lt_one) hz
  rwa [Finset.centerMass_eq_of_sum_1 _ _ hsum, hrepr] at hcm

abbrev RVector (n : ℕ) := Fin (n + 1) → ℝ

def realVector (f : FVector n) : RVector n := fun j => f j

def realVectors (n : ℕ) : Set (RVector n) := realVector '' SnF n

private theorem skel_eq_real_skeleton (k : ℕ) : skel n k = realVector (skeleton n k) := by
  funext j
  by_cases h0 : j.val = 0
  · simp [skel, realVector, skeleton, cap, h0]
  · by_cases h : j.val ≤ k <;> simp [skel, realVector, skeleton, h0, h]

theorem hull_eq_lymChain (hn : 1 ≤ n) : convexHull ℝ (realVectors n) = lymChain n := by
  apply Set.Subset.antisymm
  · apply convexHull_min _ (convex_lymChain n)
    rintro _ ⟨f, ⟨D, hD, rfl⟩, rfl⟩
    have h := SnF_fixed hn (show fVector D ∈ SnF n from ⟨D, hD, rfl⟩)
    refine ⟨?_, ?_, ?_, ?_⟩
    · change ((fVector D 0 : ℕ) : ℝ) = 1
      exact_mod_cast h.1
    · rw [fin_one_eq hn]
      change ((fVector D (firstDegree hn) : ℕ) : ℝ) = n
      exact_mod_cast h.2
    · intro j _ _
      exact lym hD j
    · exact Nat.cast_nonneg _
  · refine (lymChain_subset_hull hn).trans (convexHull_mono ?_)
    rintro _ ⟨k, hk, rfl⟩
    rw [skel_eq_real_skeleton]
    exact ⟨_, skeleton_mem_SnF hk.1, rfl⟩

theorem cap_pos_real (j : Fin (n + 1)) : (0 : ℝ) < cap j := by exact_mod_cast cap_pos j

/-- The rank specifies the two fixed coordinates. All layer ratios are weakly decreasing. -/
structure Normalized (hn : 1 ≤ n) (r : ℕ) (x : RVector n) : Prop where
  zero : x 0 = r
  one : x (firstDegree hn) = (r : ℝ) * n
  anti : Antitone (fun j => x j / (cap j : ℝ))
  nonneg : ∀ j, 0 ≤ x j

theorem Normalized.ratio_le {hn : 1 ≤ n} {r : ℕ} {x : RVector n}
    (h : Normalized hn r x) (j : Fin (n + 1)) : x j / (cap j : ℝ) ≤ (r : ℝ) := by
  have he := h.anti (Fin.zero_le j)
  simpa [h.zero, cap] using he

theorem lymChain_iff_normalized (hn : 1 ≤ n) {x : RVector n} :
    x ∈ lymChain n ↔ Normalized hn 1 x := by
  constructor
  · rintro ⟨hx0, hx1, hstep, hlast⟩
    have hone : x (firstDegree hn) = (n : ℝ) := by
      rw [fin_one_eq hn] at hx1
      exact hx1
    have hanti : Antitone (fun j => x j / (cap j : ℝ)) := by
      apply Fin.antitone_iff_succ_le.mpr
      intro i
      by_cases hi : i.val = 0
      · have hi1 : i.succ = firstDegree hn := Fin.ext (by simp [hi, firstDegree])
        have hi0 : i.castSucc = 0 := Fin.ext hi
        rw [hi1, hi0, hone, hx0]
        simp [firstDegree, cap, div_self (show (n : ℝ) ≠ 0 by exact_mod_cast (by omega : n ≠ 0))]
      · exact hstep i.val (by omega) (by have := i.isLt; omega)
    refine ⟨by simpa using hx0, by simpa using hone, hanti, ?_⟩
    intro j
    have hle := hanti (Fin.le_last j)
    have h := (le_div_iff₀ (cap_pos_real j)).mp
      ((div_nonneg hlast (cap_pos_real (Fin.last n)).le).trans hle)
    simpa only [zero_mul] using h
  · intro h
    refine ⟨by simpa using h.zero, ?_, ?_, h.nonneg _⟩
    · rw [fin_one_eq hn]
      simpa [firstDegree] using h.one
    · intro j _ hj
      exact h.anti (show (⟨j, by omega⟩ : Fin (n + 1)) ≤ ⟨j + 1, by omega⟩ by simp)

theorem mem_dilate_iff (hn : 1 ≤ n) {r : ℕ} (hr : 0 < r) {x : RVector n} :
    x ∈ (r : ℝ) • convexHull ℝ (realVectors n) ↔ Normalized hn r x := by
  rw [hull_eq_lymChain hn, Set.mem_smul_set]
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h := (lymChain_iff_normalized hn).mp hy
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [h.zero]
    · simp [h.one]
    · intro i j hij
      simpa only [Pi.smul_apply, smul_eq_mul, mul_div_assoc] using
        mul_le_mul_of_nonneg_left (h.anti hij) hr'.le
    · exact fun j => mul_nonneg hr'.le (h.nonneg j)
  · intro h
    let y : RVector n := fun j => (r : ℝ)⁻¹ * x j
    have hh : (r : ℝ) ≠ 0 := hr'.ne'
    refine ⟨y, (lymChain_iff_normalized hn).mpr ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp [y, h.zero, hh]
    · simp [y, h.one, hh]
    · intro i j hij
      simpa only [y, mul_div_assoc] using
        mul_le_mul_of_nonneg_left (h.anti hij) (inv_nonneg.mpr hr'.le)
    · exact fun j => mul_nonneg (inv_nonneg.mpr hr'.le) (h.nonneg j)
    · funext j
      simp [y, hh]

end D5.S3.Combinatorics.Kozlov
