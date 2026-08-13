/- GID: D5/S1/Phase/ThreeGap/Classification
   generality: G
   mirror-B: D5/B/S1/Phase/ThreeGap/Classification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Port the MIT forward, backward, and corner gap classification. -/

import D5.S1.Phase.ThreeGap.Returns

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


/-- Backward return multiplier: the canonical index of the MAX orbit value `1-η⁻`. -/
noncomputable def mMinus (a : ℝ) (N : ℕ) (h2 : 2 ≤ orbitCard a N) : ℕ :=
  canMul a N (1 - etaNeg a N) (posOrbit_subset_orbit a N (max_posOrbit_mem a h2))

theorem mMinus_lt (a : ℝ) (N : ℕ) (h2 : 2 ≤ orbitCard a N) : mMinus a N h2 < N := by
  unfold mMinus; exact canMul_lt a N _

theorem fract_mMinus (a : ℝ) (N : ℕ) (h2 : 2 ≤ orbitCard a N) :
    Int.fract ((mMinus a N h2 : ℝ) * a) = 1 - etaNeg a N := by
  unfold mMinus; exact fract_canMul a N _

/-- Index shift by `m⁻` realises rotation by `1-η⁻` (i.e. by `-η⁻`) at value level. -/
theorem fract_index_shift_neg (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) (j : ℕ) :
    Int.fract (((j + mMinus a N h2 : ℕ) : ℝ) * a)
      = Int.fract (Int.fract ((j : ℝ) * a) + (1 - etaNeg a N)) := by
  have hcast : ((j + mMinus a N h2 : ℕ) : ℝ) * a
      = (j : ℝ) * a + (mMinus a N h2 : ℝ) * a := by push_cast; ring
  rw [hcast, ← fract_add_fract_eq, fract_mMinus]

/-- **D1' (mirror): an in-range index is not in the bottom band.**  If
    `d + m⁻ < N` and `{d·a} > 0` then `η⁻ ≤ {d·a}`. -/
theorem fract_sub_etaNeg_ge (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) {d : ℕ}
    (hd : d + mMinus a N h2 < N) (h0 : 0 < Int.fract ((d : ℝ) * a)) :
    etaNeg a N ≤ Int.fract ((d : ℝ) * a) := by
  by_contra hcon
  push Not at hcon
  have h1mη : 0 < 1 - etaNeg a N := posOrbit_pos a N (max_posOrbit_mem a h2)
  have hval : Int.fract (Int.fract ((d : ℝ) * a) + (1 - etaNeg a N))
      = Int.fract ((d : ℝ) * a) + (1 - etaNeg a N) :=
    Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have hmemorb : Int.fract (((d + mMinus a N h2 : ℕ) : ℝ) * a) ∈ orbit a N :=
    (mem_orbit_iff a N _).mpr ⟨_, hd, rfl⟩
  rw [fract_index_shift_neg a h2 d, hval] at hmemorb
  have hpos2 : 0 < Int.fract ((d : ℝ) * a) + (1 - etaNeg a N) := by linarith
  have hposorb : Int.fract ((d : ℝ) * a) + (1 - etaNeg a N) ∈ posOrbit a N := by
    rw [mem_posOrbit_iff]; exact ⟨ne_of_gt hpos2, hmemorb⟩
  have hle := le_one_sub_etaNeg a h2 hposorb
  linarith

/-- **No orbit point lies in `(xⱼ - η⁻, xⱼ)` when `j + m⁻ < N`** (backward mirror
    of `noPointBetween`). -/
theorem noPointBetween_neg (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) {j : ℕ}
    (hj : j + mMinus a N h2 < N)
    {z : ℝ} (hz : z ∈ orbit a N)
    (hlo : Int.fract ((j : ℝ) * a) - etaNeg a N < z)
    (hhi : z < Int.fract ((j : ℝ) * a)) : False := by
  obtain ⟨w, hwN, hwval⟩ := (mem_orbit_iff a N z).mp hz
  have hlt' : Int.fract ((w : ℝ) * a) < Int.fract ((j : ℝ) * a) := by rw [hwval]; exact hhi
  rcases Nat.lt_or_ge w j with hwlt | hwge
  · have hdN : (j - w) + mMinus a N h2 < N := by omega
    have hcast : ((j - w : ℕ) : ℝ) * a = (j : ℝ) * a - (w : ℝ) * a := by
      rw [Nat.cast_sub (le_of_lt hwlt)]; ring
    have hdpos : 0 < Int.fract ((j : ℝ) * a) - Int.fract ((w : ℝ) * a) := by linarith
    have hdlt1 : Int.fract ((j : ℝ) * a) - Int.fract ((w : ℝ) * a) < 1 := by
      have h1 := Int.fract_lt_one ((j : ℝ) * a)
      have h2' := Int.fract_nonneg ((w : ℝ) * a)
      linarith
    have hself : Int.fract (Int.fract ((j : ℝ) * a) - Int.fract ((w : ℝ) * a))
        = Int.fract ((j : ℝ) * a) - Int.fract ((w : ℝ) * a) :=
      Int.fract_eq_self.mpr ⟨le_of_lt hdpos, hdlt1⟩
    have hfrac : Int.fract (((j - w : ℕ) : ℝ) * a)
        = Int.fract ((j : ℝ) * a) - Int.fract ((w : ℝ) * a) := by
      rw [hcast, ← fract_sub_fract_eq]; exact hself
    have hval_pos : 0 < Int.fract (((j - w : ℕ) : ℝ) * a) := by rw [hfrac]; exact hdpos
    have hD1' := fract_sub_etaNeg_ge a h2 hdN hval_pos
    rw [hfrac, hwval] at hD1'
    linarith
  · have hwgt : j < w := by
      rcases eq_or_lt_of_le hwge with he | hgt
      · exfalso; rw [he, hwval] at hhi; exact lt_irrefl z hhi
      · exact hgt
    have hcm := compl_mem_orbit_of_index_gt a N hwgt hwN hlt'
    rw [hwval] at hcm
    have h1mη : 0 < 1 - etaNeg a N := posOrbit_pos a N (max_posOrbit_mem a h2)
    have hgt1mη : 1 - etaNeg a N < 1 - (Int.fract ((j : ℝ) * a) - z) := by linarith
    have hpos : 0 < 1 - (Int.fract ((j : ℝ) * a) - z) := by linarith
    have hposorb : 1 - (Int.fract ((j : ℝ) * a) - z) ∈ posOrbit a N := by
      rw [mem_posOrbit_iff]; exact ⟨ne_of_gt hpos, hcm⟩
    have hle := le_one_sub_etaNeg a h2 hposorb
    linarith

/-- **Case B (backward): an index `j'` of `v' = sortedVal (i+1)` with `j' + m⁻ < N`
    forces gap `= η⁻`.** -/
theorem gap_eq_etaNeg (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) {i : ℕ}
    (hi : i + 1 < orbitCard a N)
    {j' : ℕ} (hjfr : Int.fract ((j' : ℝ) * a) = sortedVal a N (i + 1))
    (hjN : j' + mMinus a N h2 < N) :
    gapAt a N i = etaNeg a N := by
  set v := sortedVal a N i with hv
  set v' := sortedVal a N (i + 1) with hv'
  have hvmem : v ∈ orbit a N := sortedVal_mem a (by omega : i < orbitCard a N)
  have hvv' : v < v' := sortedVal_strictMono a N (Nat.lt_succ_self i) hi
  have hetaneg : 0 < etaNeg a N := etaNeg_pos a h2
  have hvpos : 0 ≤ v := (orbit_subset_Ico a N (Finset.mem_coe.mpr hvmem)).1
  have hv'lt1 : v' < 1 := (orbit_subset_Ico a N (Finset.mem_coe.mpr (sortedVal_mem a hi))).2
  have hge : v ≤ v' - etaNeg a N := by
    by_contra hc
    push Not at hc
    exact noPointBetween_neg a h2 hjN hvmem (by rw [hjfr]; exact hc) (by rw [hjfr]; exact hvv')
  have hge0 : etaNeg a N ≤ v' := by
    by_contra hc
    push Not at hc
    exact noPointBetween_neg a h2 hjN hvmem (by rw [hjfr]; linarith) (by rw [hjfr]; exact hvv')
  have hmem : v' - etaNeg a N ∈ orbit a N := by
    have hms : Int.fract (((j' + mMinus a N h2 : ℕ) : ℝ) * a) ∈ orbit a N :=
      (mem_orbit_iff a N _).mpr ⟨_, hjN, rfl⟩
    rw [fract_index_shift_neg a h2 j', hjfr] at hms
    have hcompute : Int.fract (v' + (1 - etaNeg a N)) = v' - etaNeg a N := by
      rw [show v' + (1 - etaNeg a N) = (v' - etaNeg a N) + ((1 : ℤ) : ℝ) by push_cast; ring,
        Int.fract_add_intCast]
      exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    rw [hcompute] at hms
    exact hms
  have hle : v' - etaNeg a N ≤ v := by
    by_contra hc
    push Not at hc
    exact no_orbit_strictly_between a N hi hmem hc (by linarith)
  have heq : v = v' - etaNeg a N := le_antisymm hge hle
  unfold gapAt
  rw [← hv, ← hv', heq]; ring

/-! ## The corner case `η⁺ + η⁻` — completing the classification

The remaining case of the three-gap bound: the *corner*, where both first returns
fall off the end (`canMul v + m⁺ ≥ N` and `canMul v' + m⁻ ≥ N`).  Then the gap is
`η⁺ + η⁻` (`corner_gap`).  The argument:

* `corner_canMul_lt_mMinus` (`hP1 : canMul v < m⁻`): if `j ≥ m⁻` then `v+η⁻` would
  be the successor `v'`, forcing `canMul v' + m⁻ < N`, contradicting `hB`.
* upper bound `v' ≤ v+η⁺+η⁻`: realise `q := v+η⁺+η⁻` as `{(canMul v + m⁺ - m⁻)·a}`
  (index `< N` by `hP1`).
* lower bound: no orbit point in `(v, v+η⁺+η⁻)`, split as L1 `(v, v+η⁺)`,
  L2 `v+η⁺ ∉ orbit a N`, L3 `(v+η⁺, q)`.

L1/L3 (`corner_noPoint_lo` / `corner_noPoint_hi`) use the *M-circle* `M := m⁺ + m⁻`:
`orbit a N ⊆ orbit a M`, the returns are unchanged (`no_new_below_etaPos`,
`no_new_above_etaNeg`, `etaPos_eq_extend`, `etaNeg_eq_extend`), and `hP1` keeps the
shifted indices `< M`.

L2 is closed WITHOUT induction (uniform in `a`, rational or irrational): if
`v+η⁺ = {k·a}` with `k ≥ j` then `m⁺ ≤ k-j`, so `k ≥ j+m⁺ ≥ N`, impossible; if
`k < j` then `d := j+m⁺-k` is a period (`{d·a}=0`) with `m⁺ < d < m⁺+m⁻`,
contradicting minimality of `m⁻` (the max `1-η⁻` at index `m⁻-d`) or of `m⁺`
(`η⁺=η⁻`, then at index `d-m⁻`).  This replaces van Ravenstein / Mayero's
induction-on-`N` and avoids their irrational-only restriction. -/


/-- **Backward index shift by `m⁻`.**  For `m⁻ ≤ k`, subtracting the canonical
    `m⁻` from the index `k` rotates the value by `-(1-η⁻)` mod 1. -/
theorem fract_sub_mMinus (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) {k : ℕ}
    (hk : mMinus a N h2 ≤ k) :
    Int.fract (((k - mMinus a N h2 : ℕ) : ℝ) * a)
      = Int.fract (Int.fract ((k : ℝ) * a) - (1 - etaNeg a N)) := by
  have hcast : ((k - mMinus a N h2 : ℕ) : ℝ) * a
      = (k : ℝ) * a - (mMinus a N h2 : ℝ) * a := by
    rw [Nat.cast_sub hk]; ring
  rw [hcast, ← fract_sub_fract_eq, fract_mMinus a N h2]

/-- **Minimality of the canonical multiplier.**  Any in-range index `c < N` whose
    rotation value is `p` is at least `canMul a N p`. -/
theorem canMul_le (a : ℝ) (N : ℕ) {p : ℝ} (hp : p ∈ orbit a N) {c : ℕ}
    (hc : c < N) (hcval : Int.fract ((c : ℝ) * a) = p) : canMul a N p hp ≤ c := by
  unfold canMul
  exact Finset.min'_le _ _ ((mem_mulFiber_iff a N p c).mpr ⟨hc, hcval⟩)

/-- **Forward index shift by `m⁺`.**  For `m⁺ ≤ k`, subtracting the canonical `m⁺`
    from the index `k` rotates the value by `-η⁺` mod 1. -/
theorem fract_sub_mPlus (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) {k : ℕ}
    (hk : mPlus a N h2 ≤ k) :
    Int.fract (((k - mPlus a N h2 : ℕ) : ℝ) * a)
      = Int.fract (Int.fract ((k : ℝ) * a) - etaPos a N) := by
  have hcast : ((k - mPlus a N h2 : ℕ) : ℝ) * a
      = (k : ℝ) * a - (mPlus a N h2 : ℝ) * a := by
    rw [Nat.cast_sub hk]; ring
  rw [hcast, ← fract_sub_fract_eq, fract_mPlus a N h2]

/-- **Returns are preserved when extending the orbit to `M = m⁺ + m⁻` indices
    (positive return).**  No new index `k ∈ [N, m⁺+m⁻)` produces a positive value
    below `η⁺`.  (Key step of the M-circle route to the corner bound: a value
    `s = {k·a} ∈ (0, η⁺)` would force `{(k-m⁻)·a} = η⁺`, hence `m⁺ ≤ k-m⁻` by
    minimality, i.e. `k ≥ m⁺+m⁻`, contradiction.) -/
theorem no_new_below_etaPos (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N)
    {k : ℕ} (hkN : N ≤ k) (hkM : k < mPlus a N h2 + mMinus a N h2)
    (hpos : 0 < Int.fract ((k : ℝ) * a)) :
    etaPos a N ≤ Int.fract ((k : ℝ) * a) := by
  by_contra hcon
  push Not at hcon
  set s := Int.fract ((k : ℝ) * a) with hs
  have hep : 0 < etaPos a N := etaPos_pos a h2
  have hep1 : etaPos a N < 1 := posOrbit_lt_one a N (etaPos_mem a h2)
  have hen : 0 < etaNeg a N := etaNeg_pos a h2
  have hmPlt : mPlus a N h2 < N := mPlus_lt a N h2
  have hmMlt : mMinus a N h2 < N := mMinus_lt a N h2
  have hsum : etaPos a N + etaNeg a N ≤ 1 := by
    have := le_one_sub_etaNeg a h2 (etaPos_mem a h2); linarith
  -- s + η⁻ = {(k - m⁻)·a} ∈ orbit, hence ≥ η⁺
  have hval1 : Int.fract (((k - mMinus a N h2 : ℕ) : ℝ) * a) = s + etaNeg a N := by
    rw [fract_sub_mMinus a h2 (by omega : mMinus a N h2 ≤ k), ← hs,
      show s - (1 - etaNeg a N) = (s + etaNeg a N) + ((-1 : ℤ) : ℝ) by push_cast; ring,
      Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have hmem1 : s + etaNeg a N ∈ orbit a N :=
    hval1 ▸ (mem_orbit_iff a N _).mpr ⟨k - mMinus a N h2, by omega, rfl⟩
  have hge1 : etaPos a N ≤ s + etaNeg a N :=
    no_orbit_below_etaPos a h2 hmem1 (by linarith)
  -- 1-(η⁺-s) = {(k - m⁺)·a} ∈ orbit, hence ≤ 1-η⁻, giving s ≤ η⁺-η⁻
  have hval2 : Int.fract (((k - mPlus a N h2 : ℕ) : ℝ) * a) = 1 - (etaPos a N - s) := by
    rw [fract_sub_mPlus a h2 (by omega : mPlus a N h2 ≤ k), ← hs,
      show s - etaPos a N = (1 - (etaPos a N - s)) + ((-1 : ℤ) : ℝ) by push_cast; ring,
      Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have hmem2 : 1 - (etaPos a N - s) ∈ orbit a N :=
    hval2 ▸ (mem_orbit_iff a N _).mpr ⟨k - mPlus a N h2, by omega, rfl⟩
  have hle2 : 1 - (etaPos a N - s) ≤ 1 - etaNeg a N :=
    le_one_sub_etaNeg a h2 (by rw [mem_posOrbit_iff]; exact ⟨ne_of_gt (by linarith), hmem2⟩)
  -- combine: s + η⁻ = η⁺, so {(k-m⁻)·a} = η⁺, so m⁺ ≤ k-m⁻, i.e. k ≥ m⁺+m⁻
  have hs_eq : s + etaNeg a N = etaPos a N := by linarith
  have hmin : mPlus a N h2 ≤ k - mMinus a N h2 := by
    have h := canMul_le a N (posOrbit_subset_orbit a N (etaPos_mem a h2))
      (show k - mMinus a N h2 < N by omega) (by rw [hval1, hs_eq])
    simpa only [mPlus] using h
  omega

/-- **Returns are preserved when extending the orbit to `M = m⁺ + m⁻` indices
    (negative return).**  No new index `k ∈ [N, m⁺+m⁻)` produces a value in the top
    band `(1-η⁻, 1)`.  Mirror of `no_new_below_etaPos`. -/
theorem no_new_above_etaNeg (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N)
    {k : ℕ} (hkN : N ≤ k) (hkM : k < mPlus a N h2 + mMinus a N h2) :
    Int.fract ((k : ℝ) * a) ≤ 1 - etaNeg a N := by
  by_contra hcon
  push Not at hcon
  set s := Int.fract ((k : ℝ) * a) with hs
  have hs1 : s < 1 := Int.fract_lt_one _
  have hep : 0 < etaPos a N := etaPos_pos a h2
  have hep1 : etaPos a N < 1 := posOrbit_lt_one a N (etaPos_mem a h2)
  have hen : 0 < etaNeg a N := etaNeg_pos a h2
  have hmPlt : mPlus a N h2 < N := mPlus_lt a N h2
  have hmMlt : mMinus a N h2 < N := mMinus_lt a N h2
  have hsum : etaPos a N + etaNeg a N ≤ 1 := by
    have := le_one_sub_etaNeg a h2 (etaPos_mem a h2); linarith
  -- s - η⁺ = {(k - m⁺)·a} ∈ orbit, hence ≤ 1-η⁻
  have hval1 : Int.fract (((k - mPlus a N h2 : ℕ) : ℝ) * a) = s - etaPos a N := by
    rw [fract_sub_mPlus a h2 (by omega : mPlus a N h2 ≤ k), ← hs]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have hmem1 : s - etaPos a N ∈ orbit a N :=
    hval1 ▸ (mem_orbit_iff a N _).mpr ⟨k - mPlus a N h2, by omega, rfl⟩
  have hle1 : s - etaPos a N ≤ 1 - etaNeg a N :=
    le_one_sub_etaNeg a h2 (by rw [mem_posOrbit_iff]; exact ⟨ne_of_gt (by linarith), hmem1⟩)
  -- s - (1-η⁻) = {(k - m⁻)·a} ∈ orbit, positive, hence ≥ η⁺
  have hval2 : Int.fract (((k - mMinus a N h2 : ℕ) : ℝ) * a) = s - (1 - etaNeg a N) := by
    rw [fract_sub_mMinus a h2 (by omega : mMinus a N h2 ≤ k), ← hs]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have hmem2 : s - (1 - etaNeg a N) ∈ orbit a N :=
    hval2 ▸ (mem_orbit_iff a N _).mpr ⟨k - mMinus a N h2, by omega, rfl⟩
  have hge2 : etaPos a N ≤ s - (1 - etaNeg a N) :=
    no_orbit_below_etaPos a h2 hmem2 (by linarith)
  -- combine: s - η⁺ = 1-η⁻, so {(k-m⁺)·a} = 1-η⁻ (= max), so m⁻ ≤ k-m⁺, k ≥ m⁺+m⁻
  have hs_eq : s - etaPos a N = 1 - etaNeg a N := by linarith
  have hmin : mMinus a N h2 ≤ k - mPlus a N h2 := by
    have h := canMul_le a N (posOrbit_subset_orbit a N (max_posOrbit_mem a h2))
      (show k - mPlus a N h2 < N by omega) (by rw [hval1, hs_eq])
    simpa only [mMinus] using h
  omega

/-! ## M-circle infrastructure (orbit extension `N ↦ M = m⁺ + m⁻`)

Monotonicity of the orbit in the index count, and the fact that the two returns
`η⁺, η⁻` are *unchanged* when the orbit is extended from `N` to `M = m⁺ + m⁻`
(no new index in `[N, M)` produces a smaller positive value or a larger value).
These let the corner "no point in the big gap" arguments (`corner_noPoint_lo/hi`)
borrow the in-range first-return machinery in the larger circle. -/

/-- The orbit grows with the index count. -/
theorem orbit_mono (a : ℝ) {N M : ℕ} (h : N ≤ M) : orbit a N ⊆ orbit a M := by
  intro x hx
  rw [mem_orbit_iff] at hx ⊢
  obtain ⟨k, hk, hkval⟩ := hx
  exact ⟨k, lt_of_lt_of_le hk h, hkval⟩

theorem orbitCard_mono (a : ℝ) {N M : ℕ} (h : N ≤ M) : orbitCard a N ≤ orbitCard a M :=
  Finset.card_le_card (orbit_mono a h)

theorem posOrbit_mono (a : ℝ) {N M : ℕ} (h : N ≤ M) : posOrbit a N ⊆ posOrbit a M := by
  intro x hx
  rw [mem_posOrbit_iff] at hx ⊢
  exact ⟨hx.1, orbit_mono a h hx.2⟩

/-- **Positive return preserved under extension.**  If every new index `k ∈ [N, M)`
    avoids the band `(0, η⁺)`, then `η⁺` is unchanged from `N` to `M`. -/
theorem etaPos_eq_extend (a : ℝ) {N M : ℕ} (h2 : 2 ≤ orbitCard a N) (hNM : N ≤ M)
    (hM2 : 2 ≤ orbitCard a M)
    (hnew : ∀ k, N ≤ k → k < M → 0 < Int.fract ((k : ℝ) * a) →
      etaPos a N ≤ Int.fract ((k : ℝ) * a)) :
    etaPos a M = etaPos a N := by
  refine le_antisymm ?_ ?_
  · exact etaPos_le a hM2 (posOrbit_mono a hNM (etaPos_mem a h2))
  · have hmem := etaPos_mem a hM2
    have hpos : 0 < etaPos a M := posOrbit_pos a M hmem
    have horb : etaPos a M ∈ orbit a M := posOrbit_subset_orbit a M hmem
    obtain ⟨k, hk, hkval⟩ := (mem_orbit_iff a M _).mp horb
    rcases Nat.lt_or_ge k N with hkN | hkN
    · exact no_orbit_below_etaPos a h2 ((mem_orbit_iff a N _).mpr ⟨k, hkN, hkval⟩) hpos
    · have := hnew k hkN hk (by rw [hkval]; exact hpos); rwa [hkval] at this

/-- **Negative return preserved under extension.**  If every new index `k ∈ [N, M)`
    avoids the top band `(1 - η⁻, 1)`, then `η⁻` is unchanged from `N` to `M`. -/
theorem etaNeg_eq_extend (a : ℝ) {N M : ℕ} (h2 : 2 ≤ orbitCard a N) (hNM : N ≤ M)
    (hM2 : 2 ≤ orbitCard a M)
    (hnew : ∀ k, N ≤ k → k < M → Int.fract ((k : ℝ) * a) ≤ 1 - etaNeg a N) :
    etaNeg a M = etaNeg a N := by
  refine le_antisymm ?_ ?_
  · have : (1 : ℝ) - etaNeg a N ≤ 1 - etaNeg a M :=
      le_one_sub_etaNeg a hM2 (posOrbit_mono a hNM (max_posOrbit_mem a h2))
    linarith
  · have hmem := max_posOrbit_mem a hM2
    have hpos : 0 < 1 - etaNeg a M := posOrbit_pos a M hmem
    have horb : (1 - etaNeg a M) ∈ orbit a M := posOrbit_subset_orbit a M hmem
    obtain ⟨k, hk, hkval⟩ := (mem_orbit_iff a M _).mp horb
    have hle : (1 : ℝ) - etaNeg a M ≤ 1 - etaNeg a N := by
      rcases Nat.lt_or_ge k N with hkN | hkN
      · refine le_one_sub_etaNeg a h2 ?_
        rw [mem_posOrbit_iff]
        exact ⟨ne_of_gt hpos, (mem_orbit_iff a N _).mpr ⟨k, hkN, hkval⟩⟩
      · have := hnew k hkN hk; rwa [hkval] at this
    linarith

/-- **Corner discriminant `hP1` (independent of the lower bound).**  In the corner,
    the canonical index `j = canMul v` of the left point satisfies `j < m⁻`.

    Proof: if `j ≥ m⁻`, then `w := v + η⁻ = {(j-m⁻)·a} ∈ orbit a N` (a valid index
    `< N`).  As `w` lies in range with `canMul w + m⁻ ≤ j < N`, case B
    (`gap_eq_etaNeg`) shows the predecessor of `w` is `w - η⁻ = v`; hence `w` is the
    successor `v'` of `v`, so `v' = v + η⁻` and `canMul v' ≤ j - m⁻`, giving
    `canMul v' + m⁻ ≤ j < N` — contradicting the corner hypothesis `hB`. -/
theorem corner_canMul_lt_mMinus (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) {i : ℕ}
    (hi : i + 1 < orbitCard a N)
    (hvmem : sortedVal a N i ∈ orbit a N)
    (hv'mem : sortedVal a N (i + 1) ∈ orbit a N)
    (hB : ¬ (canMul a N (sortedVal a N (i + 1)) hv'mem + mMinus a N h2 < N)) :
    canMul a N (sortedVal a N i) hvmem < mMinus a N h2 := by
  have hN : 0 < N := pos_of_two_le_orbitCard a h2
  set v := sortedVal a N i with hv
  set j := canMul a N v hvmem with hj
  by_contra hcon
  push Not at hcon
  have hjfr : Int.fract ((j : ℝ) * a) = v := fract_canMul a N hvmem
  have hjN : j < N := canMul_lt a N hvmem
  have hen : 0 < etaNeg a N := etaNeg_pos a h2
  have hvv' : v < sortedVal a N (i + 1) := sortedVal_strictMono a N (Nat.lt_succ_self i) hi
  have hv0 : 0 ≤ v := (orbit_subset_Ico a N (Finset.mem_coe.mpr hvmem)).1
  have hv'pos : 0 < sortedVal a N (i + 1) := lt_of_le_of_lt hv0 hvv'
  have hv'le : sortedVal a N (i + 1) ≤ 1 - etaNeg a N :=
    le_one_sub_etaNeg a h2 (by rw [mem_posOrbit_iff]; exact ⟨ne_of_gt hv'pos, hv'mem⟩)
  have hvmax : v < 1 - etaNeg a N := lt_of_lt_of_le hvv' hv'le
  -- w := v + η⁻ realised at index j - m⁻
  have hwval : Int.fract (((j - mMinus a N h2 : ℕ) : ℝ) * a) = v + etaNeg a N := by
    rw [fract_sub_mMinus a h2 hcon, hjfr,
      show v - (1 - etaNeg a N) = (v + etaNeg a N) + ((-1 : ℤ) : ℝ) by push_cast; ring,
      Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have hwmem : v + etaNeg a N ∈ orbit a N :=
    hwval ▸ (mem_orbit_iff a N _).mpr ⟨j - mMinus a N h2, by omega, rfl⟩
  obtain ⟨s, hs, hsval⟩ := exists_index_of_mem_orbit a N hwmem
  -- s ≥ 1 since sortedVal 0 = 0 < v + η⁻
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with rfl | hsp
    · rw [sortedVal_zero_eq_zero a hN] at hsval; linarith
    · exact hsp
  -- canMul w is in range: canMul w + m⁻ ≤ j < N
  set jw := canMul a N (v + etaNeg a N) hwmem with hjw
  have hjwle : jw ≤ j - mMinus a N h2 := canMul_le a N hwmem (by omega) hwval
  have hjwN : jw + mMinus a N h2 < N := by omega
  -- case B at index s-1: gap to the left of w (= sortedVal s) is η⁻
  have hsval' : Int.fract ((jw : ℝ) * a) = sortedVal a N ((s - 1) + 1) := by
    rw [show (s - 1) + 1 = s by omega, hsval]; exact fract_canMul a N hwmem
  have hgap := gap_eq_etaNeg a h2 (by omega : (s - 1) + 1 < orbitCard a N) hsval' hjwN
  -- so sortedVal (s-1) = w - η⁻ = v
  have hpred : sortedVal a N (s - 1) = v := by
    unfold gapAt at hgap
    rw [show (s - 1) + 1 = s by omega, hsval] at hgap
    linarith
  -- hence s - 1 = i (sortedVal injective on valid indices)
  have hsi : s - 1 = i := by
    by_contra hne
    rcases Nat.lt_or_ge (s - 1) i with h | h
    · have := sortedVal_strictMono a N h (show i < orbitCard a N by omega)
      rw [hpred] at this; exact (lt_irrefl v) this
    · have h' : i < s - 1 := lt_of_le_of_ne h (Ne.symm hne)
      have := sortedVal_strictMono a N h' (show s - 1 < orbitCard a N by omega)
      rw [hpred] at this; exact (lt_irrefl v) this
  -- so sortedVal (i+1) = w = v + η⁻, and canMul (sortedVal (i+1)) ≤ j - m⁻,
  -- contradicting hB
  have hv'idx : Int.fract (((j - mMinus a N h2 : ℕ) : ℝ) * a) = sortedVal a N (i + 1) := by
    rw [hwval, ← (show s = i + 1 by omega)]; exact hsval.symm
  have hle : canMul a N (sortedVal a N (i + 1)) hv'mem ≤ j - mMinus a N h2 :=
    canMul_le a N hv'mem (by omega) hv'idx
  exact hB (by omega)

/-- **L1 — no orbit point in `(v, v + η⁺)` (corner).**  Direct difference
    extraction: a point `z = {w·a}` with `v < z < v + η⁺` gives, when `w ≥ j`, a
    positive value `z - v < η⁺` in `orbit a N` (contra `η⁺` minimal); and when
    `w < j`, a positive value `η⁺ - (z-v) < η⁺` in the *extended* orbit `orbit a M`
    (`M = m⁺ + m⁻`) at index `(j-w) + m⁺ < M`, contradicting minimality of
    `etaPos a M = etaPos a N`.  The discriminant `hP1 : j < m⁻` makes the shifted
    index stay in range `< M`. -/
theorem corner_noPoint_lo (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) {i : ℕ}
    (hvmem : sortedVal a N i ∈ orbit a N)
    (hP1 : canMul a N (sortedVal a N i) hvmem < mMinus a N h2)
    (hA : N ≤ canMul a N (sortedVal a N i) hvmem + mPlus a N h2)
    {z : ℝ} (hz : z ∈ orbit a N)
    (hlo : sortedVal a N i < z) (hhi : z < sortedVal a N i + etaPos a N) : False := by
  set v := sortedVal a N i with hv
  set j := canMul a N v hvmem with hj
  have hjfr : Int.fract ((j : ℝ) * a) = v := fract_canMul a N hvmem
  have hjN : j < N := canMul_lt a N hvmem
  have hep : 0 < etaPos a N := etaPos_pos a h2
  have hep1 : etaPos a N < 1 := posOrbit_lt_one a N (etaPos_mem a h2)
  have hmP : mPlus a N h2 < N := mPlus_lt a N h2
  have hmM : mMinus a N h2 < N := mMinus_lt a N h2
  set M := mPlus a N h2 + mMinus a N h2 with hMdef
  have hNM : N ≤ M := by omega
  have hM2 : 2 ≤ orbitCard a M := le_trans h2 (orbitCard_mono a hNM)
  have hetaPosM : etaPos a M = etaPos a N :=
    etaPos_eq_extend a h2 hNM hM2 (fun k hk1 hk2 hk3 => no_new_below_etaPos a h2 hk1 hk2 hk3)
  obtain ⟨w, hwN, hwval⟩ := (mem_orbit_iff a N z).mp hz
  rcases Nat.lt_or_ge w j with hwlt | hwge
  · -- w < j : η⁺ - (z-v) ∈ orbit a M, positive and < η⁺
    have hfracjw : Int.fract (((j - w : ℕ) : ℝ) * a) = 1 - (z - v) := by
      have hcast : ((j - w : ℕ) : ℝ) * a = (j : ℝ) * a - (w : ℝ) * a := by
        rw [Nat.cast_sub (le_of_lt hwlt)]; ring
      rw [hcast, ← fract_sub_fract_eq, hjfr, hwval,
        show v - z = (1 - (z - v)) + ((-1 : ℤ) : ℝ) by push_cast; ring, Int.fract_add_intCast]
      exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    have hidxval : Int.fract ((((j - w) + mPlus a N h2 : ℕ) : ℝ) * a) = etaPos a N - (z - v) := by
      rw [fract_index_shift a h2 (j - w), hfracjw,
        show (1 - (z - v)) + etaPos a N = (etaPos a N - (z - v)) + ((1 : ℤ) : ℝ) by push_cast; ring,
        Int.fract_add_intCast]
      exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    have hmemM : etaPos a N - (z - v) ∈ orbit a M := by
      rw [← hidxval]
      exact (mem_orbit_iff a M _).mpr ⟨(j - w) + mPlus a N h2, by omega, rfl⟩
    have := no_orbit_below_etaPos a hM2 hmemM (by linarith)
    rw [hetaPosM] at this; linarith
  · -- w ≥ j : z - v ∈ orbit a N, positive and < η⁺
    have hlt' : Int.fract ((j : ℝ) * a) < Int.fract ((w : ℝ) * a) := by rw [hjfr, hwval]; linarith
    have hdmem := sub_mem_orbit_of_index_le a N hwge hwN hlt'
    rw [hwval, hjfr] at hdmem
    have := no_orbit_below_etaPos a h2 hdmem (by linarith)
    linarith

/-- **L3 — no orbit point in `(v + η⁺, v + η⁺ + η⁻)` (corner).**  Mirror of `L1`:
    the point `p₁ = v + η⁺ = {(j+m⁺)·a} ∈ orbit a M`.  A point `z` with
    `p₁ < z < p₁ + η⁻` has every index `w < N ≤ j + m⁺`, so `{((j+m⁺)-w)·a} = 1 -
    (z - p₁)` lies in `(1 - η⁻, 1) ∩ orbit a M`, exceeding the maximum `1 - η⁻` of
    `orbit a M` — contradiction. -/
theorem corner_noPoint_hi (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) {i : ℕ}
    (hvmem : sortedVal a N i ∈ orbit a N)
    (hP1 : canMul a N (sortedVal a N i) hvmem < mMinus a N h2)
    (hA : N ≤ canMul a N (sortedVal a N i) hvmem + mPlus a N h2)
    {z : ℝ} (hz : z ∈ orbit a N)
    (hlo : sortedVal a N i + etaPos a N < z)
    (hhi : z < sortedVal a N i + etaPos a N + etaNeg a N) : False := by
  set v := sortedVal a N i with hv
  set j := canMul a N v hvmem with hj
  have hjfr : Int.fract ((j : ℝ) * a) = v := fract_canMul a N hvmem
  have hjN : j < N := canMul_lt a N hvmem
  have hv0 : 0 ≤ v := (orbit_subset_Ico a N (Finset.mem_coe.mpr hvmem)).1
  have hep : 0 < etaPos a N := etaPos_pos a h2
  have hen : 0 < etaNeg a N := etaNeg_pos a h2
  have hmP : mPlus a N h2 < N := mPlus_lt a N h2
  have hmM : mMinus a N h2 < N := mMinus_lt a N h2
  set M := mPlus a N h2 + mMinus a N h2 with hMdef
  have hNM : N ≤ M := by omega
  have hM2 : 2 ≤ orbitCard a M := le_trans h2 (orbitCard_mono a hNM)
  have hetaNegM : etaNeg a M = etaNeg a N :=
    etaNeg_eq_extend a h2 hNM hM2 (fun k hk1 hk2 => no_new_above_etaNeg a h2 hk1 hk2)
  obtain ⟨w, hwN, hwval⟩ := (mem_orbit_iff a N z).mp hz
  have hz1 : z < 1 := (orbit_subset_Ico a N (Finset.mem_coe.mpr hz)).2
  have hvep1 : v + etaPos a N < 1 := lt_trans hlo hz1
  have hp1val : Int.fract (((j + mPlus a N h2 : ℕ) : ℝ) * a) = v + etaPos a N := by
    rw [fract_index_shift a h2 j, hjfr]
    exact Int.fract_eq_self.mpr ⟨by linarith, hvep1⟩
  have hwlt : w < j + mPlus a N h2 := by omega
  have hfrac : Int.fract ((((j + mPlus a N h2) - w : ℕ) : ℝ) * a) = 1 - (z - (v + etaPos a N)) := by
    have hcast : (((j + mPlus a N h2) - w : ℕ) : ℝ) * a
        = ((j + mPlus a N h2 : ℕ) : ℝ) * a - (w : ℝ) * a := by
      rw [Nat.cast_sub (le_of_lt hwlt)]; ring
    rw [hcast, ← fract_sub_fract_eq, hp1val, hwval,
      show (v + etaPos a N) - z = (1 - (z - (v + etaPos a N))) + ((-1 : ℤ) : ℝ) by push_cast; ring,
      Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have hmemM : 1 - (z - (v + etaPos a N)) ∈ orbit a M := by
    rw [← hfrac]
    exact (mem_orbit_iff a M _).mpr ⟨(j + mPlus a N h2) - w, by omega, rfl⟩
  have hpos : 0 < 1 - (z - (v + etaPos a N)) := by linarith
  have hle := le_one_sub_etaNeg a hM2 (by rw [mem_posOrbit_iff]; exact ⟨ne_of_gt hpos, hmemM⟩)
  rw [hetaNegM] at hle; linarith


end ThreeGap
