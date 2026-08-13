/- GID: D5/S1/Phase/ThreeGap/Returns
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Port the MIT first-return multiplier and index-shift layer. -/

import D5.S1.Phase.ThreeGap.Foundations

/- Copyright (c) 2026 Dirk Kunert. MIT License.
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
   https://github.com/dkunert/three-gap-theorem-lean -/

namespace ThreeGap


/-- **Fractional-part index-shift identity.**  Reducing the two summands mod 1
    first does not change the fractional part of a sum:
    `Int.fract (Int.fract x + Int.fract y) = Int.fract (x + y)`.  With `x = u*a`,
    `y = m*a` this is the value form of the multiplier shift `u, m ↦ u + m`. -/
theorem fract_add_fract_eq (x y : ℝ) :
    Int.fract (Int.fract x + Int.fract y) = Int.fract (x + y) := by
  rw [Int.fract_eq_fract]
  refine ⟨-⌊x⌋ - ⌊y⌋, ?_⟩
  have hx : Int.fract x = x - ⌊x⌋ := (Int.self_sub_floor x).symm
  have hy : Int.fract y = y - ⌊y⌋ := (Int.self_sub_floor y).symm
  rw [hx, hy]; push_cast; ring

/-- **Forward rotation closure (multiplier in range).**  If `u + m < N`, the
    rotated value `Int.fract (Int.fract (u*a) + Int.fract (m*a))` is again an orbit
    point.  This is the half of the Slater closure that does not wrap past index
    `N`; the values that fall off the end (`u + m ≥ N`) are where the negative
    return appears.  (API extra; not used by the main chain.) -/
theorem fract_rotate_mem (a : ℝ) (N : ℕ) {u m : ℕ} (hum : u + m < N) :
    Int.fract (Int.fract ((u : ℝ) * a) + Int.fract ((m : ℝ) * a)) ∈ orbit a N := by
  rw [fract_add_fract_eq]
  have hcast : (u : ℝ) * a + (m : ℝ) * a = ((u + m : ℕ) : ℝ) * a := by push_cast; ring
  rw [hcast]
  exact (mem_orbit_iff a N _).mpr ⟨u + m, hum, rfl⟩

/-! ## Multiplier-indexed infrastructure (toward the first-return dichotomy)

The value-Finset `orbit` hides the index ("multiplier") behind each point.
We recover a canonical multiplier and the forward value-shift; the discriminant
of the three-gap dichotomy is the *Nat* condition `canMul + mp < N`.
-/

/-- The finset of indices `< N` whose rotation value equals `p`. -/
noncomputable def mulFiber (a : ℝ) (N : ℕ) (p : ℝ) : Finset ℕ :=
  (Finset.range N).filter (fun k => Int.fract ((k : ℝ) * a) = p)

theorem mem_mulFiber_iff (a : ℝ) (N : ℕ) (p : ℝ) (k : ℕ) :
    k ∈ mulFiber a N p ↔ k < N ∧ Int.fract ((k : ℝ) * a) = p := by
  simp only [mulFiber, Finset.mem_filter, Finset.mem_range]

theorem mulFiber_nonempty (a : ℝ) (N : ℕ) {p : ℝ} (hp : p ∈ orbit a N) :
    (mulFiber a N p).Nonempty := by
  obtain ⟨i, hi, hival⟩ := (mem_orbit_iff a N p).mp hp
  exact ⟨i, (mem_mulFiber_iff a N p i).mpr ⟨hi, hival⟩⟩

/-- **Canonical (least) multiplier** of an orbit point `p`. -/
noncomputable def canMul (a : ℝ) (N : ℕ) (p : ℝ) (hp : p ∈ orbit a N) : ℕ :=
  (mulFiber a N p).min' (mulFiber_nonempty a N hp)

theorem canMul_mem_fiber (a : ℝ) (N : ℕ) {p : ℝ} (hp : p ∈ orbit a N) :
    canMul a N p hp ∈ mulFiber a N p := by
  unfold canMul
  exact (mulFiber a N p).min'_mem (mulFiber_nonempty a N hp)

theorem canMul_lt (a : ℝ) (N : ℕ) {p : ℝ} (hp : p ∈ orbit a N) :
    canMul a N p hp < N :=
  ((mem_mulFiber_iff a N p _).mp (canMul_mem_fiber a N hp)).1

theorem fract_canMul (a : ℝ) (N : ℕ) {p : ℝ} (hp : p ∈ orbit a N) :
    Int.fract ((canMul a N p hp : ℝ) * a) = p :=
  ((mem_mulFiber_iff a N p _).mp (canMul_mem_fiber a N hp)).2

/-- **Return-multiplier existence** for `η⁺` (the smallest positive orbit point):
    some `mp < N` rotates to `η⁺`. -/
theorem exists_return_multiplier (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) :
    ∃ mp, mp < N ∧ Int.fract ((mp : ℝ) * a) = etaPos a N := by
  have hmem : etaPos a N ∈ orbit a N := posOrbit_subset_orbit a N (etaPos_mem a h2)
  obtain ⟨mp, hmp, hmpval⟩ := (mem_orbit_iff a N _).mp hmem
  exact ⟨mp, hmp, hmpval⟩

/-- **Backward return-multiplier existence** for `1 - η⁻` (the largest positive
    orbit point): some `mn < N` rotates to `1 - η⁻`. -/
theorem exists_back_return_multiplier (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) :
    ∃ mn, mn < N ∧ Int.fract ((mn : ℝ) * a) = 1 - etaNeg a N := by
  have hmem : (1 : ℝ) - etaNeg a N ∈ orbit a N :=
    posOrbit_subset_orbit a N (max_posOrbit_mem a h2)
  obtain ⟨mn, hmn, hmnval⟩ := (mem_orbit_iff a N _).mp hmem
  exact ⟨mn, hmn, hmnval⟩

/-- **Value-shift identity.**  Rotating an orbit point `p` (canonical multiplier
    `u = canMul p`) by a return multiplier `mp` for `η⁺` lands on
    `Int.fract (p + η⁺)`.  (API extra; the main chain uses `fract_index_shift`.) -/
theorem fract_shift_eq (a : ℝ) (N : ℕ) {p : ℝ} (hp : p ∈ orbit a N)
    {mp : ℕ} (hmpval : Int.fract ((mp : ℝ) * a) = etaPos a N) :
    Int.fract (((canMul a N p hp + mp : ℕ)) * a) = Int.fract (p + etaPos a N) := by
  have hcast : ((canMul a N p hp + mp : ℕ) : ℝ) * a
      = (canMul a N p hp : ℝ) * a + (mp : ℝ) * a := by push_cast; ring
  rw [hcast, ← fract_add_fract_eq, fract_canMul a N hp, hmpval]

/-- **Forward shift lands in the orbit** when the multiplier stays in range
    (`canMul p + mp < N`) and `p + η⁺ < 1` (no wrap).  (API extra; unused.) -/
theorem shift_mem_orbit (a : ℝ) (N : ℕ) {p : ℝ} (hp : p ∈ orbit a N)
    {mp : ℕ} (hmpval : Int.fract ((mp : ℝ) * a) = etaPos a N)
    (hrange : canMul a N p hp + mp < N)
    (hlt1 : p + etaPos a N < 1)
    (hp0 : 0 ≤ p) (heta0 : 0 ≤ etaPos a N) :
    p + etaPos a N ∈ orbit a N := by
  have hval : Int.fract (((canMul a N p hp + mp : ℕ)) * a) = p + etaPos a N := by
    rw [fract_shift_eq a N hp hmpval, Int.fract_eq_self.mpr ⟨by linarith, hlt1⟩]
  exact (mem_orbit_iff a N _).mpr ⟨_, hrange, hval⟩

/-! ### Forward-neighbour upper bound (API extra — superseded by Case A below) -/

/-- **Forward-neighbour upper bound.**  Under the forward hypothesis `hfwd`, the
    gap is at MOST `η⁺`: the orbit point `q := sortedVal i + η⁺` lies strictly above
    `sortedVal i` and `< 1`, so by `no_orbit_strictly_between` it cannot sit strictly
    below `sortedVal (i+1)`.  (API extra; superseded by `gap_eq_etaPos`.) -/
theorem gap_le_etaPos (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N)
    {i : ℕ} (hi : i + 1 < orbitCard a N)
    (hfwd : sortedVal a N i + etaPos a N < 1 ∧ sortedVal a N i + etaPos a N ∈ orbit a N) :
    gapAt a N i ≤ etaPos a N := by
  obtain ⟨_, hmem⟩ := hfwd
  have heta0 : 0 < etaPos a N := etaPos_pos a h2
  by_contra hcon
  push Not at hcon
  have hlo : sortedVal a N i < sortedVal a N i + etaPos a N := by linarith
  have hhi : sortedVal a N i + etaPos a N < sortedVal a N (i + 1) := by
    unfold gapAt at hcon; linarith
  exact no_orbit_strictly_between a N hi hmem hlo hhi

/-! ## Index-bridge infrastructure (multiplier indices and difference extraction)

Toward the first-return classification, recovering the index structure behind the
orbit values.  The decisive discriminant is the index condition `j + m⁺ < N`, NOT
the value condition `xⱼ + η⁺ ∈ orbit`: those differ (e.g. `α = 4/5, N = 4`, point
`2/5` has `2/5 + η⁺ = 4/5 ∈ orbit` yet gap `= η⁻`, since its index is off-end).
-/

/-- Fractional-part subtraction identity (companion of `fract_add_fract_eq`). -/
theorem fract_sub_fract_eq (x y : ℝ) :
    Int.fract (Int.fract x - Int.fract y) = Int.fract (x - y) := by
  rw [Int.fract_eq_fract]
  refine ⟨⌊y⌋ - ⌊x⌋, ?_⟩
  have hx : Int.fract x = x - ⌊x⌋ := (Int.self_sub_floor x).symm
  have hy : Int.fract y = y - ⌊y⌋ := (Int.self_sub_floor y).symm
  rw [hx, hy]; push_cast; ring

/-- Pure `Nat`/`Finset` counting seed: exactly `N - mp` indices keep their forward
    `+mp` shift in range, so exactly `mp` fall off the end.  (API extra; unused.) -/
theorem forward_inRange_card {N mp : ℕ} (h : mp ≤ N) :
    (Finset.filter (fun j => j + mp < N) (Finset.range N)).card = N - mp := by
  have hset : Finset.filter (fun j => j + mp < N) (Finset.range N)
      = Finset.range (N - mp) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hset, Finset.card_range]

/-- Forward return multiplier as an index: the canonical (least) index whose
    rotation value is `η⁺`. -/
noncomputable def mPlus (a : ℝ) (N : ℕ) (h2 : 2 ≤ orbitCard a N) : ℕ :=
  canMul a N (etaPos a N) (posOrbit_subset_orbit a N (etaPos_mem a h2))

theorem mPlus_lt (a : ℝ) (N : ℕ) (h2 : 2 ≤ orbitCard a N) : mPlus a N h2 < N := by
  unfold mPlus; exact canMul_lt a N _

theorem fract_mPlus (a : ℝ) (N : ℕ) (h2 : 2 ≤ orbitCard a N) :
    Int.fract ((mPlus a N h2 : ℝ) * a) = etaPos a N := by
  unfold mPlus; exact fract_canMul a N _

theorem mPlus_pos (a : ℝ) (N : ℕ) (h2 : 2 ≤ orbitCard a N) : 0 < mPlus a N h2 := by
  rcases Nat.eq_zero_or_pos (mPlus a N h2) with h0 | hpos
  · exfalso
    have hf := fract_mPlus a N h2
    rw [h0] at hf
    simp only [Nat.cast_zero, zero_mul, Int.fract_zero] at hf
    exact (etaPos_pos a h2).ne hf
  · exact hpos

/-- **Difference extraction, `w ≥ j`.**  If two orbit points have non-decreasing
    indices `j ≤ w < N` and increasing values, their difference is an orbit point.
    Combined with `no_orbit_below_etaPos` this rules out a between-point reachable
    from a higher index. -/
theorem sub_mem_orbit_of_index_le (a : ℝ) (N : ℕ) {j w : ℕ} (hjw : j ≤ w) (hw : w < N)
    (hlt : Int.fract ((j : ℝ) * a) < Int.fract ((w : ℝ) * a)) :
    Int.fract ((w : ℝ) * a) - Int.fract ((j : ℝ) * a) ∈ orbit a N := by
  set d : ℝ := Int.fract ((w : ℝ) * a) - Int.fract ((j : ℝ) * a) with hd
  have hpos : 0 < d := by rw [hd]; linarith
  have hlt1 : d < 1 := by
    rw [hd]
    have h1 := Int.fract_lt_one ((w : ℝ) * a)
    have h2 := Int.fract_nonneg ((j : ℝ) * a)
    linarith
  have hself : Int.fract d = d := Int.fract_eq_self.mpr ⟨le_of_lt hpos, hlt1⟩
  have hcast : ((w - j : ℕ) : ℝ) * a = (w : ℝ) * a - (j : ℝ) * a := by
    rw [Nat.cast_sub hjw]; ring
  have hkey : Int.fract (((w - j : ℕ) : ℝ) * a) = d := by
    rw [hcast, ← fract_sub_fract_eq]; exact hself
  have hwj : w - j < N := lt_of_le_of_lt (Nat.sub_le w j) hw
  rw [← hkey]
  exact (mem_orbit_iff a N _).mpr ⟨w - j, hwj, rfl⟩

/-- **Difference extraction, `w < j` (dual).**  If the larger value `{w·a}` has the
    *smaller* index `w < j`, the complement `1 - ({w·a} - {j·a})` is an orbit point
    (`{(j-w)·a}`) in the top band `(1 - η⁺, 1)`.  Via `le_one_sub_etaNeg` this gives
    `{w·a} - {j·a} ≥ η⁻`; used in the backward index-bridge toward Case B. -/
theorem compl_mem_orbit_of_index_gt (a : ℝ) (N : ℕ) {j w : ℕ} (hwj : w < j) (hj : j < N)
    (hlt : Int.fract ((j : ℝ) * a) < Int.fract ((w : ℝ) * a)) :
    1 - (Int.fract ((w : ℝ) * a) - Int.fract ((j : ℝ) * a)) ∈ orbit a N := by
  set z : ℝ := Int.fract ((w : ℝ) * a) with hz
  set v : ℝ := Int.fract ((j : ℝ) * a) with hv
  have hpos : 0 < z - v := by linarith
  have hlt1 : z - v < 1 := by
    rw [hz, hv]
    have h1 := Int.fract_lt_one ((w : ℝ) * a)
    have h2 := Int.fract_nonneg ((j : ℝ) * a)
    linarith
  have hmem01 : (0 : ℝ) ≤ 1 - (z - v) ∧ 1 - (z - v) < 1 := ⟨by linarith, by linarith⟩
  have hcast : ((j - w : ℕ) : ℝ) * a = (j : ℝ) * a - (w : ℝ) * a := by
    rw [Nat.cast_sub (le_of_lt hwj)]; ring
  have hfr : Int.fract (((j - w : ℕ) : ℝ) * a) = 1 - (z - v) := by
    rw [hcast, ← fract_sub_fract_eq, ← hz, ← hv]
    have heq : v - z = (1 - (z - v)) + ((-1 : ℤ) : ℝ) := by push_cast; ring
    rw [heq, Int.fract_add_intCast, Int.fract_eq_self.mpr hmem01]
  have hjw : j - w < N := lt_of_le_of_lt (Nat.sub_le j w) hj
  rw [← hfr]
  exact (mem_orbit_iff a N _).mpr ⟨j - w, hjw, rfl⟩

/-! ## The forward (η⁺) case -/

/-- Shifting an index by `m⁺` realises the rotation by `η⁺` at the value level:
    `{(j+m⁺)·a} = {{j·a} + η⁺}`. -/
theorem fract_index_shift (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) (j : ℕ) :
    Int.fract (((j + mPlus a N h2 : ℕ) : ℝ) * a)
      = Int.fract (Int.fract ((j : ℝ) * a) + etaPos a N) := by
  have hcast : ((j + mPlus a N h2 : ℕ) : ℝ) * a
      = (j : ℝ) * a + (mPlus a N h2 : ℝ) * a := by push_cast; ring
  rw [hcast, ← fract_add_fract_eq, fract_mPlus]

/-- No-wrap specialisation: when `{j·a} + η⁺ < 1`, the `m⁺`-shifted index lands on
    exactly `{j·a} + η⁺`. -/
theorem fract_index_shift_noWrap (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) (j : ℕ)
    (hlt1 : Int.fract ((j : ℝ) * a) + etaPos a N < 1) :
    Int.fract (((j + mPlus a N h2 : ℕ) : ℝ) * a) = Int.fract ((j : ℝ) * a) + etaPos a N := by
  rw [fract_index_shift a h2 j]
  have hnn : (0 : ℝ) ≤ Int.fract ((j : ℝ) * a) + etaPos a N := by
    have h1 := Int.fract_nonneg ((j : ℝ) * a)
    have h2' := etaPos_pos a h2
    linarith
  exact Int.fract_eq_self.mpr ⟨hnn, hlt1⟩

/-- **D1 — an in-range index is not in the top band.**  If `d + m⁺ < N` then
    `{d·a} + η⁺ ≤ 1`.  (If not, `{(d+m⁺)·a} = {d·a}+η⁺-1` is a positive orbit value
    `< η⁺`, contradicting minimality.) -/
theorem fract_add_etaPos_le_one (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) {d : ℕ}
    (hd : d + mPlus a N h2 < N) :
    Int.fract ((d : ℝ) * a) + etaPos a N ≤ 1 := by
  by_contra hcon
  push Not at hcon
  have hfr_lt1 := Int.fract_lt_one ((d : ℝ) * a)
  have heta_lt1 : etaPos a N < 1 := posOrbit_lt_one a N (etaPos_mem a h2)
  have hval : Int.fract (Int.fract ((d : ℝ) * a) + etaPos a N)
      = Int.fract ((d : ℝ) * a) + etaPos a N - 1 := by
    have h1 : (0 : ℝ) ≤ Int.fract ((d : ℝ) * a) + etaPos a N - 1 := by linarith
    have h2'' : Int.fract ((d : ℝ) * a) + etaPos a N - 1 < 1 := by linarith
    conv_lhs => rw [show Int.fract ((d : ℝ) * a) + etaPos a N
          = (Int.fract ((d : ℝ) * a) + etaPos a N - 1) + ((1 : ℤ) : ℝ) by push_cast; ring]
    rw [Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr ⟨h1, h2''⟩
  have hmem : Int.fract (((d + mPlus a N h2 : ℕ) : ℝ) * a) ∈ orbit a N :=
    (mem_orbit_iff a N _).mpr ⟨d + mPlus a N h2, hd, rfl⟩
  rw [fract_index_shift a h2 d, hval] at hmem
  have hpos : 0 < Int.fract ((d : ℝ) * a) + etaPos a N - 1 := by linarith
  have hmin := no_orbit_below_etaPos a h2 hmem hpos
  linarith

/-- **No orbit point lies in `(xⱼ, xⱼ + η⁺)` when `j + m⁺ < N`.**  `w ≥ j`: the
    difference is a positive orbit value `< η⁺` (minimality).  `w < j`: the
    complementary index `j - w` would be in the top band, contradicting D1. -/
theorem noPointBetween (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) {j : ℕ}
    (hj : j + mPlus a N h2 < N)
    {z : ℝ} (hz : z ∈ orbit a N)
    (hlo : Int.fract ((j : ℝ) * a) < z)
    (hhi : z < Int.fract ((j : ℝ) * a) + etaPos a N) : False := by
  obtain ⟨w, hwN, hwval⟩ := (mem_orbit_iff a N z).mp hz
  have hjN : j < N := lt_of_le_of_lt (Nat.le_add_right j _) hj
  have hlt' : Int.fract ((j : ℝ) * a) < Int.fract ((w : ℝ) * a) := by rw [hwval]; exact hlo
  rcases Nat.lt_or_ge w j with hwlt | hwge
  · have hdN : (j - w) + mPlus a N h2 < N := by omega
    have hD1 := fract_add_etaPos_le_one a h2 hdN
    have hcast : ((j - w : ℕ) : ℝ) * a = (j : ℝ) * a - (w : ℝ) * a := by
      rw [Nat.cast_sub (le_of_lt hwlt)]; ring
    have hzv1 : Int.fract ((w : ℝ) * a) - Int.fract ((j : ℝ) * a) < 1 := by
      have h1 := Int.fract_lt_one ((w : ℝ) * a)
      have h2' := Int.fract_nonneg ((j : ℝ) * a)
      linarith
    have hzvpos : 0 < Int.fract ((w : ℝ) * a) - Int.fract ((j : ℝ) * a) := by linarith
    have hmem01 : (0 : ℝ) ≤ 1 - (Int.fract ((w : ℝ) * a) - Int.fract ((j : ℝ) * a)) ∧
        1 - (Int.fract ((w : ℝ) * a) - Int.fract ((j : ℝ) * a)) < 1 := ⟨by linarith, by linarith⟩
    have hfr : Int.fract (((j - w : ℕ) : ℝ) * a)
        = 1 - (Int.fract ((w : ℝ) * a) - Int.fract ((j : ℝ) * a)) := by
      rw [hcast, ← fract_sub_fract_eq]
      have heq : Int.fract ((j : ℝ) * a) - Int.fract ((w : ℝ) * a)
          = (1 - (Int.fract ((w : ℝ) * a) - Int.fract ((j : ℝ) * a))) + ((-1 : ℤ) : ℝ) := by
        push_cast; ring
      rw [heq, Int.fract_add_intCast, Int.fract_eq_self.mpr hmem01]
    rw [hfr, hwval] at hD1
    linarith
  · have hd := sub_mem_orbit_of_index_le a N hwge hwN hlt'
    have hdpos : 0 < Int.fract ((w : ℝ) * a) - Int.fract ((j : ℝ) * a) := by
      rw [hwval]; linarith
    have hmin := no_orbit_below_etaPos a h2 hd hdpos
    rw [hwval] at hmin
    linarith

/-- **Case A (forward): an index `j` of `v = sortedVal i` with `j + m⁺ < N` forces
    gap `= η⁺`.** -/
theorem gap_eq_etaPos (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) {i : ℕ}
    (hi : i + 1 < orbitCard a N)
    {j : ℕ} (hjfr : Int.fract ((j : ℝ) * a) = sortedVal a N i)
    (hjN : j + mPlus a N h2 < N) :
    gapAt a N i = etaPos a N := by
  set v := sortedVal a N i with hv
  set v' := sortedVal a N (i + 1) with hv'
  have hv'mem : v' ∈ orbit a N := sortedVal_mem a hi
  have hvv' : v < v' := sortedVal_strictMono a N (Nat.lt_succ_self i) hi
  have hv'lt1 : v' < 1 := (orbit_subset_Ico a N (Finset.mem_coe.mpr hv'mem)).2
  have hetapos : 0 < etaPos a N := etaPos_pos a h2
  have hge : v + etaPos a N ≤ v' := by
    by_contra hc
    push Not at hc
    exact noPointBetween a h2 hjN hv'mem (by rw [hjfr]; exact hvv') (by rw [hjfr]; exact hc)
  have hvlt1 : v + etaPos a N < 1 := by
    by_contra hc
    push Not at hc
    exact noPointBetween a h2 hjN hv'mem (by rw [hjfr]; exact hvv') (by rw [hjfr]; linarith)
  have hmem : v + etaPos a N ∈ orbit a N := by
    have hms : Int.fract (((j + mPlus a N h2 : ℕ) : ℝ) * a) ∈ orbit a N :=
      (mem_orbit_iff a N _).mpr ⟨j + mPlus a N h2, hjN, rfl⟩
    rw [fract_index_shift_noWrap a h2 j (by rw [hjfr]; exact hvlt1), hjfr] at hms
    exact hms
  have hle : v' ≤ v + etaPos a N := by
    by_contra hc
    push Not at hc
    exact no_orbit_strictly_between a N hi hmem (by linarith) hc
  have heq : v' = v + etaPos a N := le_antisymm hle hge
  unfold gapAt
  rw [← hv, ← hv', heq]; ring

/-! ### Backward (η⁻) machinery — mirror of the forward case -/

end ThreeGap
