/- GID: D5/S1/Phase/ThreeGap/Foundations
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Port the MIT three-gap orbit, sorting, and return foundations. -/

import Mathlib

/-!
# The Three-Gap (Steinhaus) theorem

Copyright (c) 2026 Dirk Kunert

MIT License

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

Ported from Dirk Kunert's formalization:
https://github.com/dkunert/three-gap-theorem-lean

A self-contained Lean 4 / Mathlib formalization of the three-gap theorem,
depending only on Mathlib.  It works in `[0,1)` through `Int.fract` (NOT
`AddCircle`), via the first-return (Slater / van Ravenstein) route.  The
companion paper is in `paper/three_gap_theorem_lean.tex`; for the related
rational cut-and-project period work see the README.

## Status

**Complete and machine-checked** — `three_gap_card_le_three` (for every `a : ℝ`
and `N : ℕ`, the `N`-point orbit `{i·a mod 1 : i < N}` partitions `[0,1)` into at
most three distinct gap lengths) is proved with no `sorry`, no warnings, and only
the standard axioms `propext / Classical.choice / Quot.sound`.  Uniform in `a`
(rational and irrational alike).

The development, in order:

* `orbit`, `gaps`, `gaps_sum_eq_one` — construction; the gaps sum to `1`;
* `sortedVal` and its order theory (`sortedVal_strictMono`, `_zero`, `_last`, …);
* the two first returns `etaPos = η⁺`, `etaNeg = η⁻`, with minimality;
* `three_gap_card_le_three_of_subset` — the reduction "gap values lie in a
  three-element set `⇒` at most three distinct gap lengths";
* the multiplier layer (`canMul`, `mPlus`, `mMinus`) with the index-shift
  identities (`fract_index_shift`) and the `noPointBetween` lemmas;
* cases A (`gap_eq_etaPos`) and B (`gap_eq_etaNeg`) of the first-return
  classification, with the index-bridge infrastructure;
* the **corner case** `η⁺ + η⁻` (`corner_gap`), via the M-circle (L1/L3) and an
  induction-free closure of L2 — see the "corner case" section below;
* the full classification `neighbour_gap_in_returns` and the bound
  `three_gap_card_le_three`.

## Design

`gaps` enumerates the sorted distinct points through `Finset.orderEmbOfFin`
(`Fin k ↪o ℝ`, `k = (orbit a N).card`), extended to a total `sortedVal : ℕ → ℝ`;
the gaps are the adjacent differences over `Finset.range (k - 1)` plus the
wrap-around `(min + 1) - max`, and `gaps_sum_eq_one` is a `Finset` telescoping sum.

Note on `noncomputable`: on `ℝ`, `DecidableEq` and the order are noncomputable, so
`orbit`, `orbitCard`, `orbitEmb`, `sortedVal`, `gaps`, `canMul`, … are all
`noncomputable`.
-/

namespace ThreeGap

/-- The (finite, distinct) orbit `{ Int.fract (i * a) | i < N }` in `[0,1)`.

    `noncomputable`, since `Finset.image` on `ℝ` uses the (noncomputable)
    `DecidableEq ℝ` instance. -/
noncomputable def orbit (a : ℝ) (N : ℕ) : Finset ℝ :=
  (Finset.range N).image (fun i : ℕ => Int.fract ((i : ℝ) * a))

/-- The orbit is nonempty as soon as there is at least one index, i.e. `0 < N`.
    Ties the hypothesis `0 < N` of `gaps_sum_eq_one` to the orbit. -/
theorem orbit_nonempty (a : ℝ) {N : ℕ} (hN : 0 < N) : (orbit a N).Nonempty := by
  simp only [orbit, Finset.image_nonempty, Finset.nonempty_range_iff]
  exact hN.ne'

/-- Every orbit point is a fractional part, hence lies in `[0,1)`. -/
theorem orbit_subset_Ico (a : ℝ) (N : ℕ) :
    ↑(orbit a N) ⊆ Set.Ico (0 : ℝ) 1 := by
  intro x hx
  simp only [Finset.mem_coe, orbit, Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨i, -, rfl⟩ := hx
  exact Set.mem_Ico.mpr ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- The number of distinct orbit points.  `noncomputable`, as it depends on the
    noncomputable `orbit`. -/
noncomputable def orbitCard (a : ℝ) (N : ℕ) : ℕ := (orbit a N).card

/-- The increasing enumeration `Fin k ↪o ℝ` of the distinct orbit points, where
    `k = orbitCard a N`.  Element `i` is the `i`-th smallest point. -/
noncomputable def orbitEmb (a : ℝ) (N : ℕ) :
    Fin (orbitCard a N) ↪o ℝ :=
  (orbit a N).orderEmbOfFin rfl

/-- The sorted distinct orbit points as a *total* index function `ℕ → ℝ`:
    `sortedVal a N i` is the `i`-th smallest point when `i < orbitCard a N`,
    and a junk value `0` otherwise.  Only indices `0, …, orbitCard a N - 1`
    matter; the telescoping below is purely formal in `sortedVal`. -/
noncomputable def sortedVal (a : ℝ) (N : ℕ) (i : ℕ) : ℝ :=
  if h : i < orbitCard a N then orbitEmb a N ⟨i, h⟩ else 0

/-- The multiset of consecutive gaps of the sorted distinct orbit points, plus
    the single wrap-around gap `(min + 1) - max`.

    With `k = orbitCard a N` and `g = sortedVal a N`:
    * the `k - 1` adjacent gaps `g (i+1) - g i`, `i = 0, …, k - 2`, by mapping
      over `Finset.range (k - 1)`;
    * the wrap-around gap `g 0 + 1 - g (k - 1)` (i.e. `min + 1 - max`), added as a
      singleton. -/
noncomputable def gaps (a : ℝ) (N : ℕ) : Multiset ℝ :=
  ((Finset.range (orbitCard a N - 1)).val.map
      (fun i => sortedVal a N (i + 1) - sortedVal a N i)) +
    {sortedVal a N 0 + 1 - sortedVal a N (orbitCard a N - 1)}

/-- **The gaps sum to one.**  Telescoping of the adjacent differences gives
    `max - min`; adding the wrap-around gap `(min + 1) - max` yields `1`.

    The proof is a pure `Finset` telescoping sum (`Finset.sum_range_sub`) followed
    by `ring`. -/
theorem gaps_sum_eq_one (a : ℝ) (N : ℕ) (hN : 0 < N) : (gaps a N).sum = 1 := by
  have _hne : (orbit a N).Nonempty := orbit_nonempty a hN
  simp only [gaps, Multiset.sum_add, Multiset.sum_singleton, Finset.sum_map_val]
  rw [Finset.sum_range_sub (sortedVal a N) (orbitCard a N - 1)]
  ring

/-! ## Phase 1 — orbit membership and the sorted enumeration -/

/-- **Membership in the orbit.**  `x` is an orbit point iff it is `Int.fract (i * a)`
    for some index `i < N`. -/
theorem mem_orbit_iff (a : ℝ) (N : ℕ) (x : ℝ) :
    x ∈ orbit a N ↔ ∃ i, i < N ∧ Int.fract ((i : ℝ) * a) = x := by
  simp only [orbit, Finset.mem_image, Finset.mem_range]

/-- **`0` lies in every nonempty orbit** (index `i = 0` gives `Int.fract 0 = 0`). -/
theorem zero_mem_orbit (a : ℝ) {N : ℕ} (hN : 0 < N) : (0 : ℝ) ∈ orbit a N := by
  rw [mem_orbit_iff]
  exact ⟨0, hN, by rw [Nat.cast_zero, zero_mul, Int.fract_zero]⟩

/-- **The sorted enumeration is strictly increasing** on the valid index range:
    for `i < j` with `j < orbitCard a N`, `sortedVal a N i < sortedVal a N j`. -/
theorem sortedVal_strictMono (a : ℝ) (N : ℕ) {i j : ℕ}
    (hij : i < j) (hj : j < orbitCard a N) :
    sortedVal a N i < sortedVal a N j := by
  have hi : i < orbitCard a N := lt_trans hij hj
  simp only [sortedVal, dif_pos hi, dif_pos hj]
  exact (orbitEmb a N).strictMono (by simpa using hij)

/-- **The first sorted value is the minimum.** -/
theorem sortedVal_zero (a : ℝ) {N : ℕ} (hN : 0 < N) :
    sortedVal a N 0 = (orbit a N).min' (orbit_nonempty a hN) := by
  have hpos : 0 < orbitCard a N := Finset.card_pos.mpr (orbit_nonempty a hN)
  simp only [sortedVal, dif_pos hpos]
  exact Finset.orderEmbOfFin_zero rfl hpos

/-- **The last sorted value is the maximum.** -/
theorem sortedVal_last (a : ℝ) {N : ℕ} (hN : 0 < N) :
    sortedVal a N (orbitCard a N - 1) = (orbit a N).max' (orbit_nonempty a hN) := by
  have hpos : 0 < orbitCard a N := Finset.card_pos.mpr (orbit_nonempty a hN)
  have hlast : orbitCard a N - 1 < orbitCard a N := Nat.sub_lt hpos Nat.one_pos
  simp only [sortedVal, dif_pos hlast]
  exact Finset.orderEmbOfFin_last rfl hpos

/-- **Every sorted value (below the count) is an orbit point.** -/
theorem sortedVal_mem (a : ℝ) {N : ℕ} {i : ℕ} (h : i < orbitCard a N) :
    sortedVal a N i ∈ orbit a N := by
  simp only [sortedVal, dif_pos h]
  exact Finset.orderEmbOfFin_mem (orbit a N) rfl ⟨i, h⟩

/-! ## Phase 2 — gap infrastructure and the distinct-gap-count reduction -/

/-- The `i`-th adjacent gap of the sorted enumeration. -/
noncomputable def gapAt (a : ℝ) (N : ℕ) (i : ℕ) : ℝ :=
  sortedVal a N (i + 1) - sortedVal a N i

/-- `gaps` written through `gapAt` (definitional). -/
theorem gaps_eq (a : ℝ) (N : ℕ) :
    gaps a N =
      ((Finset.range (orbitCard a N - 1)).val.map (gapAt a N)) +
        {sortedVal a N 0 + 1 - sortedVal a N (orbitCard a N - 1)} := rfl

/-- Internal (non-wrap-around) gaps are positive. -/
theorem gapAt_pos (a : ℝ) (N : ℕ) {i : ℕ} (h : i + 1 < orbitCard a N) :
    0 < gapAt a N i := by
  unfold gapAt
  exact sub_pos.mpr (sortedVal_strictMono a N (Nat.lt_succ_self i) h)

/-- Membership in `gaps`, unpacked into the internal gaps and the wrap-around gap. -/
theorem mem_gaps_iff (a : ℝ) (N : ℕ) (x : ℝ) :
    x ∈ gaps a N ↔
      (∃ i, i < orbitCard a N - 1 ∧ gapAt a N i = x) ∨
      x = sortedVal a N 0 + 1 - sortedVal a N (orbitCard a N - 1) := by
  rw [gaps_eq]
  simp only [Multiset.mem_add, Multiset.mem_map, Finset.range_val,
    Multiset.mem_range, Multiset.mem_singleton]

/-- A loose bound: the number of distinct gap values is at most the number of gaps. -/
theorem gaps_toFinset_card_le (a : ℝ) (N : ℕ) :
    (gaps a N).toFinset.card ≤ Multiset.card (gaps a N) :=
  Multiset.toFinset_card_le (gaps a N)

/-- **Reduction lemma for the three-gap bound.** If every distinct gap value lies in
    a fixed three-element set, then there are at most three distinct gap lengths.
    The Phase 2 core supplies the hypothesis with `{η⁺, η⁻, η⁺+η⁻}`. -/
theorem three_gap_card_le_three_of_subset (a : ℝ) (N : ℕ) {x y z : ℝ}
    (hsub : (gaps a N).toFinset ⊆ ({x, y, z} : Finset ℝ)) :
    (gaps a N).toFinset.card ≤ 3 :=
  (Finset.card_le_card hsub).trans Finset.card_le_three

/-! ## Phase 2 core — the two first returns `η⁺`, `η⁻` (self-contained infrastructure)

The *positive return* `η⁺` is the smallest **positive** orbit point; the *negative
return* `η⁻` is `1 - max(orbit)`.  We package the positive orbit points as
`posOrbit a N := (orbit a N).erase 0`.  Everything below is proved unconditionally
(no surjectivity of the sorted enumeration is needed); the genuinely combinatorial
crux and the lemmas that depend on the enumeration-onto bridge are organized in the
Phase 2 core sections below. -/

/-- The **positive orbit points** `(orbit a N) \ {0}`.  Each lies in `(0,1)`. -/
noncomputable def posOrbit (a : ℝ) (N : ℕ) : Finset ℝ := (orbit a N).erase 0

theorem mem_posOrbit_iff (a : ℝ) (N : ℕ) (x : ℝ) :
    x ∈ posOrbit a N ↔ x ≠ 0 ∧ x ∈ orbit a N := by
  simp only [posOrbit, Finset.mem_erase]

theorem posOrbit_subset_orbit (a : ℝ) (N : ℕ) : posOrbit a N ⊆ orbit a N :=
  Finset.erase_subset _ _

theorem posOrbit_pos (a : ℝ) (N : ℕ) {x : ℝ} (hx : x ∈ posOrbit a N) : 0 < x := by
  rw [mem_posOrbit_iff] at hx
  obtain ⟨hx0, hxo⟩ := hx
  have hmem : x ∈ Set.Ico (0 : ℝ) 1 := orbit_subset_Ico a N (by simpa using hxo)
  exact lt_of_le_of_ne hmem.1 (Ne.symm hx0)

theorem posOrbit_lt_one (a : ℝ) (N : ℕ) {x : ℝ} (hx : x ∈ posOrbit a N) : x < 1 := by
  rw [mem_posOrbit_iff] at hx
  have hmem : x ∈ Set.Ico (0 : ℝ) 1 := orbit_subset_Ico a N (by simpa using hx.2)
  exact hmem.2

theorem posOrbit_nonempty (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) :
    (posOrbit a N).Nonempty := by
  have hntriv : (orbit a N).Nontrivial := by
    rw [← Finset.one_lt_card_iff_nontrivial]
    exact lt_of_lt_of_le one_lt_two h2
  obtain ⟨x, hx, hx0⟩ := hntriv.exists_ne (0 : ℝ)
  exact ⟨x, by rw [mem_posOrbit_iff]; exact ⟨hx0, hx⟩⟩

/-- `orbitCard a N ≤ N` (the orbit is the image of `range N`). -/
theorem orbitCard_le (a : ℝ) (N : ℕ) : orbitCard a N ≤ N := by
  unfold orbitCard orbit
  calc ((Finset.range N).image (fun i : ℕ => Int.fract ((i : ℝ) * a))).card
      ≤ (Finset.range N).card := Finset.card_image_le
    _ = N := Finset.card_range N

/-- A nondegenerate orbit (`2 ≤ orbitCard`) forces `0 < N`. -/
theorem pos_of_two_le_orbitCard (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) : 0 < N := by
  have hle := orbitCard_le a N
  omega

/-- The **positive return** `η⁺`: the smallest positive orbit point. Junk `1` in the
    degenerate regime. -/
noncomputable def etaPos (a : ℝ) (N : ℕ) : ℝ :=
  if h : (posOrbit a N).Nonempty then (posOrbit a N).min' h else 1

/-- The **negative return** `η⁻ = 1 - (largest positive orbit point)`. Junk `1` in
    the degenerate regime. -/
noncomputable def etaNeg (a : ℝ) (N : ℕ) : ℝ :=
  if h : (posOrbit a N).Nonempty then 1 - (posOrbit a N).max' h else 1

/-- `η⁺` is achieved by an actual positive orbit point: it lies in `posOrbit`. -/
theorem etaPos_mem (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) :
    etaPos a N ∈ posOrbit a N := by
  have h := posOrbit_nonempty a h2
  simp only [etaPos, dif_pos h]
  exact (posOrbit a N).min'_mem h

/-- `η⁺ > 0`. -/
theorem etaPos_pos (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) : 0 < etaPos a N :=
  posOrbit_pos a N (etaPos_mem a h2)

/-- `η⁺` is minimal among positive orbit points. -/
theorem etaPos_le (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N)
    {x : ℝ} (hx : x ∈ posOrbit a N) : etaPos a N ≤ x := by
  have h := posOrbit_nonempty a h2
  simp only [etaPos, dif_pos h]
  exact (posOrbit a N).min'_le x hx

/-- `η⁺` is the smallest *positive* orbit point. -/
theorem no_orbit_below_etaPos (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N)
    {x : ℝ} (hx : x ∈ orbit a N) (hx0 : 0 < x) : etaPos a N ≤ x :=
  etaPos_le a h2 (by rw [mem_posOrbit_iff]; exact ⟨hx0.ne', hx⟩)

/-- `1 - η⁻` (the largest positive orbit point) is achieved. -/
theorem max_posOrbit_mem (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) :
    (1 : ℝ) - etaNeg a N ∈ posOrbit a N := by
  have h := posOrbit_nonempty a h2
  simp only [etaNeg, dif_pos h, sub_sub_self]
  exact (posOrbit a N).max'_mem h

/-- `η⁻ > 0`. -/
theorem etaNeg_pos (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) : 0 < etaNeg a N := by
  have hmem := max_posOrbit_mem a h2
  have hlt1 : (1 : ℝ) - etaNeg a N < 1 := posOrbit_lt_one a N hmem
  linarith

/-- Every positive orbit point is `≤ 1 - η⁻`. -/
theorem le_one_sub_etaNeg (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N)
    {x : ℝ} (hx : x ∈ posOrbit a N) : x ≤ 1 - etaNeg a N := by
  have h := posOrbit_nonempty a h2
  simp only [etaNeg, dif_pos h, sub_sub_self]
  exact (posOrbit a N).le_max' x hx

/-- With at least one orbit point, the smallest sorted value is `0`. -/
theorem sortedVal_zero_eq_zero (a : ℝ) {N : ℕ} (hN : 0 < N) :
    sortedVal a N 0 = 0 := by
  rw [sortedVal_zero a hN]
  refine le_antisymm ?_ ?_
  · exact (orbit a N).min'_le 0 (zero_mem_orbit a hN)
  · rw [Finset.le_min'_iff]
    intro y hy
    have : y ∈ Set.Ico (0 : ℝ) 1 := orbit_subset_Ico a N (by simpa using hy)
    exact this.1

/-- `sortedVal` is monotone (non-strict) on the valid index range. -/
theorem sortedVal_monotone (a : ℝ) (N : ℕ) {i j : ℕ}
    (hij : i ≤ j) (hj : j < orbitCard a N) :
    sortedVal a N i ≤ sortedVal a N j := by
  rcases eq_or_lt_of_le hij with h | h
  · exact le_of_eq (by rw [h])
  · exact le_of_lt (sortedVal_strictMono a N h hj)

/-- `sortedVal` reflects strict order on valid indices. -/
theorem lt_of_sortedVal_lt (a : ℝ) (N : ℕ) {i m : ℕ}
    (hi : i < orbitCard a N) (h : sortedVal a N i < sortedVal a N m) : i < m := by
  by_contra hcon
  push Not at hcon
  exact absurd (sortedVal_monotone a N hcon hi) (not_le.mpr h)

/-- In the degenerate regime `orbitCard a N ≤ 1`, `gaps a N` has a single element. -/
theorem gaps_card_eq_one_of_degenerate (a : ℝ) {N : ℕ} (h1 : orbitCard a N ≤ 1) :
    Multiset.card (gaps a N) = 1 := by
  rw [gaps_eq]
  have hz : orbitCard a N - 1 = 0 := by omega
  rw [hz]
  simp

/-! ## Phase 2 core — enumeration-onto bridge and the two returns as gap values

The bridge from the sorted enumeration back to the orbit, the no-orbit-point-between
lemma, and the identification of the first internal gap with `η⁺` and the wrap-around
gap with `η⁻`.  Together with `three_gap_card_le_three_of_subset` these reduce the
three-gap bound to the single first-return classification lemma
(`neighbour_gap_in_returns`, the genuine combinatorial core, proved below). -/

/-- **The sorted enumeration is onto the orbit.**  Every orbit point is `sortedVal j`
    for some valid index `j`. -/
theorem exists_index_of_mem_orbit (a : ℝ) (N : ℕ) {y : ℝ} (hy : y ∈ orbit a N) :
    ∃ j, j < orbitCard a N ∧ sortedVal a N j = y := by
  have hrange : Set.range (orbitEmb a N) = ↑(orbit a N) :=
    Finset.range_orderEmbOfFin (orbit a N) (k := orbitCard a N) rfl
  have hyr : y ∈ Set.range (orbitEmb a N) := by
    rw [hrange]; exact Finset.mem_coe.mpr hy
  obtain ⟨j, hj⟩ := hyr
  refine ⟨j.1, j.2, ?_⟩
  simp only [sortedVal, dif_pos j.2, Fin.eta]
  exact hj

/-- No orbit point lies strictly between two consecutive sorted points. -/
theorem no_orbit_strictly_between (a : ℝ) (N : ℕ) {i : ℕ} (hi : i + 1 < orbitCard a N)
    {z : ℝ} (hz : z ∈ orbit a N)
    (hlo : sortedVal a N i < z) (hhi : z < sortedVal a N (i + 1)) : False := by
  obtain ⟨m, hm, hmval⟩ := exists_index_of_mem_orbit a N hz
  have hi' : i < orbitCard a N := lt_trans (Nat.lt_succ_self i) hi
  have him : i < m := lt_of_sortedVal_lt a N hi' (by rwa [hmval])
  have hmi : m < i + 1 := lt_of_sortedVal_lt a N hm (by rwa [hmval])
  omega

/-- `sortedVal a N 1 = η⁺`. -/
theorem sortedVal_one_eq_etaPos (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) :
    sortedVal a N 1 = etaPos a N := by
  have hN : 0 < N := pos_of_two_le_orbitCard a h2
  have h1 : (1 : ℕ) < orbitCard a N := lt_of_lt_of_le one_lt_two h2
  have hpos : 0 < sortedVal a N 1 := by
    have := sortedVal_strictMono a N (i := 0) (j := 1) Nat.zero_lt_one h1
    rwa [sortedVal_zero_eq_zero a hN] at this
  have hmem : sortedVal a N 1 ∈ orbit a N := sortedVal_mem a (i := 1) h1
  refine le_antisymm ?_ ?_
  · have hetaMem : etaPos a N ∈ orbit a N := posOrbit_subset_orbit a N (etaPos_mem a h2)
    have hetaPos : 0 < etaPos a N := etaPos_pos a h2
    obtain ⟨j, hj, hjval⟩ := exists_index_of_mem_orbit a N hetaMem
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · rw [sortedVal_zero_eq_zero a hN] at hjval
        exact absurd hjval.symm hetaPos.ne'
      · exact hjpos
    rw [← hjval]
    rcases eq_or_lt_of_le hj1 with hje | hjlt
    · exact le_of_eq (by rw [← hje])
    · exact le_of_lt (sortedVal_strictMono a N hjlt hj)
  · exact no_orbit_below_etaPos a h2 hmem hpos

/-- The wrap-around gap equals `η⁻`. -/
theorem wraparound_eq_etaNeg (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) :
    sortedVal a N 0 + 1 - sortedVal a N (orbitCard a N - 1) = etaNeg a N := by
  have hN : 0 < N := pos_of_two_le_orbitCard a h2
  rw [sortedVal_zero_eq_zero a hN, sortedVal_last a hN]
  have hmem : (1 : ℝ) - etaNeg a N ∈ orbit a N :=
    posOrbit_subset_orbit a N (max_posOrbit_mem a h2)
  have hmax : (orbit a N).max' (orbit_nonempty a hN) = 1 - etaNeg a N := by
    refine le_antisymm ?_ ?_
    · rw [Finset.max'_le_iff]
      intro y hy
      rcases eq_or_ne y 0 with rfl | hy0
      · have hmm : (1 : ℝ) - etaNeg a N ∈ Set.Ico (0 : ℝ) 1 :=
          orbit_subset_Ico a N (by simpa using hmem)
        exact hmm.1
      · exact le_one_sub_etaNeg a h2 (by rw [mem_posOrbit_iff]; exact ⟨hy0, hy⟩)
    · exact (orbit a N).le_max' _ hmem
  rw [hmax]; ring

/-- The first internal gap is `η⁺`. -/
theorem gapAt_zero_eq_etaPos (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) :
    gapAt a N 0 = etaPos a N := by
  have hN : 0 < N := pos_of_two_le_orbitCard a h2
  unfold gapAt
  rw [sortedVal_zero_eq_zero a hN, sortedVal_one_eq_etaPos a h2, sub_zero]

/-- `η⁺` occurs as a gap value.  (API extra; not used by the main chain.) -/
theorem etaPos_is_gap (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) :
    etaPos a N ∈ gaps a N := by
  rw [mem_gaps_iff]
  left
  refine ⟨0, ?_, gapAt_zero_eq_etaPos a h2⟩
  omega

/-- `η⁻` occurs as a gap value.  (API extra; not used by the main chain.) -/
theorem etaNeg_is_gap (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) :
    etaNeg a N ∈ gaps a N := by
  rw [mem_gaps_iff]
  right
  exact (wraparound_eq_etaNeg a h2).symm

end ThreeGap

/-! ## Phase 2 core — fractional-part rotation helpers (toward the first-return lemma) -/
