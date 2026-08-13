/- GID: D5/S1/Phase/ThreeGap/Main
   generality: G
   mirror-B: D5/B/S1/Phase/ThreeGap/Main
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Port the MIT final three-gap theorem and expose its card bound. -/

import D5.S1.Phase.ThreeGap.Classification

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

/-- **The corner case.**  When both first returns fall off the end
    (`canMul v + m⁺ ≥ N` and `canMul v' + m⁻ ≥ N`), the internal gap is `η⁺ + η⁻`.
    The lower bound `hLower` (no orbit point lies strictly in `(v, v + η⁺ + η⁻)`)
    is proved inline below; the proof is self-contained, with no external input. -/
theorem corner_gap (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) {i : ℕ}
    (hi : i + 1 < orbitCard a N)
    (hvmem : sortedVal a N i ∈ orbit a N)
    (hv'mem : sortedVal a N (i + 1) ∈ orbit a N)
    (hA : ¬ (canMul a N (sortedVal a N i) hvmem + mPlus a N h2 < N))
    (hB : ¬ (canMul a N (sortedVal a N (i + 1)) hv'mem + mMinus a N h2 < N)) :
    gapAt a N i = etaPos a N + etaNeg a N := by
  have hN : 0 < N := pos_of_two_le_orbitCard a h2
  set v := sortedVal a N i with hv
  set v' := sortedVal a N (i + 1) with hv'
  set j := canMul a N v hvmem with hj
  have hjfr : Int.fract ((j : ℝ) * a) = v := by rw [hj]; exact fract_canMul a N hvmem
  have hjN : j < N := by rw [hj]; exact canMul_lt a N hvmem
  have hep : 0 < etaPos a N := etaPos_pos a h2
  have hen : 0 < etaNeg a N := etaNeg_pos a h2
  have hmMlt : mMinus a N h2 < N := mMinus_lt a N h2
  have hmPlt : mPlus a N h2 < N := mPlus_lt a N h2
  have hvv' : v < v' := sortedVal_strictMono a N (Nat.lt_succ_self i) hi
  have hv0 : 0 ≤ v := (orbit_subset_Ico a N (Finset.mem_coe.mpr hvmem)).1
  have hv'lt1 : v' < 1 := (orbit_subset_Ico a N (Finset.mem_coe.mpr hv'mem)).2
  have hv'pos : 0 < v' := lt_of_le_of_lt hv0 hvv'
  have hv'le : v' ≤ 1 - etaNeg a N :=
    le_one_sub_etaNeg a h2 (by rw [mem_posOrbit_iff]; exact ⟨ne_of_gt hv'pos, hv'mem⟩)
  have hv_lt_max : v < 1 - etaNeg a N := lt_of_lt_of_le hvv' hv'le
  -- corner index fact: canMul v + m⁺ ≥ N
  have hAge : N ≤ j + mPlus a N h2 := by omega
  -- hP1 : j < m⁻ — the corner discriminant, proved independently (no circularity).
  have hP1 : j < mMinus a N h2 := corner_canMul_lt_mMinus a h2 hi hvmem hv'mem hB
  -- THE LOWER BOUND, reduced to L2.  No orbit point lies strictly in
  -- `(v, v + η⁺ + η⁻)`: by L1 none in `(v, v+η⁺)`, by L3 none in `(v+η⁺, q)`, so the
  -- successor `v'` (which is `> v` and, if `hLower` failed, `< q`) would have to be
  -- exactly `v + η⁺` — but `v + η⁺ ∉ orbit a N` (L2).  L1/L3 (the M-circle lemmas
  -- above) and L2 (the period argument below) are all proved here, no `sorry`.
  have hLower : v + etaPos a N + etaNeg a N ≤ v' := by
    by_contra hcon
    push Not at hcon
    have hge : v + etaPos a N ≤ v' := by
      by_contra hc
      push Not at hc
      exact corner_noPoint_lo a h2 hvmem hP1 hAge hv'mem hvv' hc
    have hle : v' ≤ v + etaPos a N := by
      by_contra hc
      push Not at hc
      exact corner_noPoint_hi a h2 hvmem hP1 hAge hv'mem hc hcon
    have hv'eq : v' = v + etaPos a N := le_antisymm hle hge
    -- L2: `v + η⁺ ∉ orbit a N` in the corner.
    have hL2 : v + etaPos a N ∉ orbit a N := by
      intro hmem
      obtain ⟨k, hkN, hkval⟩ := (mem_orbit_iff a N _).mp hmem
      rcases Nat.lt_or_ge k j with hkj | hkj
      · -- k < j : `{k·a} = v+η⁺ = {(j+m⁺)·a}` with `k ≠ j+m⁺` forces `d := j+m⁺-k`
        -- to be a PERIOD (`{d·a}=0`), with `m⁺ < d < m⁺+m⁻`.  That contradicts
        -- minimality of `m⁻` (if `d < m⁻`, the max `1-η⁻` appears at index `m⁻-d`)
        -- or of `m⁺` (if `d > m⁻`, then `η⁻ ∈ orbit` and `1-η⁺ ∈ orbit` force
        -- `η⁺ = η⁻`, which then appears at index `d-m⁻ < m⁺`).  Induction-free.
        have hvep1 : v + etaPos a N < 1 := by rw [← hkval]; exact Int.fract_lt_one _
        have hep1 : etaPos a N < 1 := posOrbit_lt_one a N (etaPos_mem a h2)
        have hen1 : etaNeg a N < 1 := by
          have := posOrbit_pos a N (max_posOrbit_mem a h2); linarith
        have hmaxpos : 0 < 1 - etaNeg a N := posOrbit_pos a N (max_posOrbit_mem a h2)
        have hjmp : Int.fract (((j + mPlus a N h2 : ℕ) : ℝ) * a) = v + etaPos a N := by
          rw [fract_index_shift_noWrap a h2 j (by rw [hjfr]; exact hvep1), hjfr]
        set d : ℕ := (j + mPlus a N h2) - k with hd
        have hdpos : 0 < d := by omega
        have hdcast : ((d : ℕ) : ℝ) * a = ((j + mPlus a N h2 : ℕ) : ℝ) * a - (k : ℝ) * a := by
          rw [hd, Nat.cast_sub (by omega)]; ring
        have hd0 : Int.fract ((d : ℝ) * a) = 0 := by
          rw [hdcast, ← fract_sub_fract_eq, hjmp, hkval, sub_self, Int.fract_zero]
        have hdlo : mPlus a N h2 < d := by omega
        have hdhi : d < mPlus a N h2 + mMinus a N h2 := by omega
        -- 1 - η⁺ ∈ orbit a N (index d - m⁺ < m⁻), hence η⁻ ≤ η⁺
        have h1mp : Int.fract (((d - mPlus a N h2 : ℕ) : ℝ) * a) = 1 - etaPos a N := by
          rw [fract_sub_mPlus a h2 (by omega : mPlus a N h2 ≤ d), hd0,
            show (0 : ℝ) - etaPos a N = (1 - etaPos a N) + ((-1 : ℤ) : ℝ) by push_cast; ring,
            Int.fract_add_intCast]
          exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
        have h1mp_mem : 1 - etaPos a N ∈ orbit a N :=
          h1mp ▸ (mem_orbit_iff a N _).mpr ⟨d - mPlus a N h2, by omega, rfl⟩
        have hηle : etaNeg a N ≤ etaPos a N := by
          have := le_one_sub_etaNeg a h2 (by
            rw [mem_posOrbit_iff]; exact ⟨ne_of_gt (by linarith), h1mp_mem⟩)
          linarith
        rcases Nat.lt_trichotomy d (mMinus a N h2) with hdm | hdm | hdm
        · -- d < m⁻ : the max `1-η⁻` occurs at index m⁻-d < m⁻, contra `canMul = m⁻`
          have hmax : Int.fract (((mMinus a N h2 - d : ℕ) : ℝ) * a) = 1 - etaNeg a N := by
            have hcast : ((mMinus a N h2 - d : ℕ) : ℝ) * a
                = (mMinus a N h2 : ℝ) * a - (d : ℝ) * a := by
              rw [Nat.cast_sub (le_of_lt hdm)]; ring
            rw [hcast, ← fract_sub_fract_eq, fract_mMinus a N h2, hd0, sub_zero]
            exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
          have hmaxmem : (1 - etaNeg a N) ∈ orbit a N :=
            hmax ▸ (mem_orbit_iff a N _).mpr ⟨mMinus a N h2 - d, by omega, rfl⟩
          have hb : mMinus a N h2 ≤ mMinus a N h2 - d :=
            canMul_le a N hmaxmem (by omega) hmax
          omega
        · -- d = m⁻ : but {m⁻·a} = 1-η⁻ > 0, contradicting {d·a} = 0
          rw [hdm, fract_mMinus a N h2] at hd0; linarith
        · -- d > m⁻ : η⁻ ∈ orbit (index d-m⁻ < m⁺); with η⁻ ≤ η⁺ get η⁺ = η⁻, contra `canMul = m⁺`
          have hηm : Int.fract (((d - mMinus a N h2 : ℕ) : ℝ) * a) = etaNeg a N := by
            rw [fract_sub_mMinus a h2 (le_of_lt hdm), hd0,
              show (0 : ℝ) - (1 - etaNeg a N) = etaNeg a N + ((-1 : ℤ) : ℝ) by push_cast; ring,
              Int.fract_add_intCast]
            exact Int.fract_eq_self.mpr ⟨le_of_lt hen, by linarith⟩
          have hηmem : etaNeg a N ∈ orbit a N :=
            hηm ▸ (mem_orbit_iff a N _).mpr ⟨d - mMinus a N h2, by omega, rfl⟩
          have heq : etaPos a N = etaNeg a N :=
            le_antisymm (no_orbit_below_etaPos a h2 hηmem hen) hηle
          have hηm' : Int.fract (((d - mMinus a N h2 : ℕ) : ℝ) * a) = etaPos a N := by
            rw [hηm, heq]
          have hb : mPlus a N h2 ≤ d - mMinus a N h2 :=
            canMul_le a N (posOrbit_subset_orbit a N (etaPos_mem a h2)) (by omega) hηm'
          omega
      · -- k ≥ j : `{(k-j)·a} = η⁺`, so `m⁺ ≤ k - j`, i.e. `k ≥ j + m⁺ ≥ N` — but
        -- `k < N`.  (This is exactly where `hA` bites.)
        have hep1 : etaPos a N < 1 := posOrbit_lt_one a N (etaPos_mem a h2)
        have hfr : Int.fract (((k - j : ℕ) : ℝ) * a) = etaPos a N := by
          have hcast : ((k - j : ℕ) : ℝ) * a = (k : ℝ) * a - (j : ℝ) * a := by
            rw [Nat.cast_sub hkj]; ring
          rw [hcast, ← fract_sub_fract_eq, hkval, hjfr,
            show (v + etaPos a N) - v = etaPos a N by ring]
          exact Int.fract_eq_self.mpr ⟨le_of_lt hep, hep1⟩
        have hmem' : etaPos a N ∈ orbit a N := posOrbit_subset_orbit a N (etaPos_mem a h2)
        have hle : mPlus a N h2 ≤ k - j := by
          have := canMul_le a N hmem' (show k - j < N by omega) hfr
          simpa only [mPlus] using this
        omega
    exact hL2 (hv'eq ▸ hv'mem)
  have hP2 : v + etaPos a N + etaNeg a N < 1 := lt_of_le_of_lt hLower hv'lt1
  have hvep1 : v + etaPos a N < 1 := by linarith
  -- construct q = v + η⁺ + η⁻ ∈ orbit, via index (j + m⁺) - m⁻ < N
  have hkcN : (j + mPlus a N h2) - mMinus a N h2 < N := by omega
  have hqval : Int.fract ((((j + mPlus a N h2) - mMinus a N h2 : ℕ) : ℝ) * a)
      = v + etaPos a N + etaNeg a N := by
    rw [fract_sub_mMinus a h2 (by omega : mMinus a N h2 ≤ j + mPlus a N h2),
      fract_index_shift a h2 j, hjfr, Int.fract_eq_self.mpr ⟨by linarith, hvep1⟩,
      show v + etaPos a N - (1 - etaNeg a N)
          = (v + etaPos a N + etaNeg a N) + ((-1 : ℤ) : ℝ) by push_cast; ring,
      Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr ⟨by linarith, hP2⟩
  have hq : v + etaPos a N + etaNeg a N ∈ orbit a N := by
    rw [← hqval]
    exact (mem_orbit_iff a N _).mpr ⟨_, hkcN, rfl⟩
  -- upper bound: v' ≤ q (else q is strictly between the consecutive v, v')
  have hUpper : v' ≤ v + etaPos a N + etaNeg a N := by
    by_contra hcon
    push Not at hcon
    exact no_orbit_strictly_between a N hi hq (by linarith) hcon
  have heq : v' = v + etaPos a N + etaNeg a N := le_antisymm hUpper hLower
  unfold gapAt
  rw [← hv, ← hv', heq]; ring

/-- **The first-return classification.**  Every internal gap is `η⁺`, `η⁻`, or
    `η⁺ + η⁻`: case A (`gap_eq_etaPos`) when `canMul v + m⁺ < N`, case B
    (`gap_eq_etaNeg`) when `canMul v' + m⁻ < N`, and the corner (`corner_gap`)
    otherwise.  (No `i = 0` special case is needed: there `canMul v = 0` and
    `m⁺ < N`, so case A always fires.) -/
theorem neighbour_gap_in_returns (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N)
    {i : ℕ} (hi : i + 1 < orbitCard a N) :
    gapAt a N i ∈ ({etaPos a N, etaNeg a N, etaPos a N + etaNeg a N} : Finset ℝ) := by
  have hvmem : sortedVal a N i ∈ orbit a N := sortedVal_mem a (by omega : i < orbitCard a N)
  have hv'mem : sortedVal a N (i + 1) ∈ orbit a N := sortedVal_mem a hi
  have hjvfr : Int.fract ((canMul a N (sortedVal a N i) hvmem : ℝ) * a) = sortedVal a N i :=
    fract_canMul a N hvmem
  have hjv'fr : Int.fract ((canMul a N (sortedVal a N (i + 1)) hv'mem : ℝ) * a)
      = sortedVal a N (i + 1) := fract_canMul a N hv'mem
  by_cases hA : canMul a N (sortedVal a N i) hvmem + mPlus a N h2 < N
  · rw [gap_eq_etaPos a h2 hi hjvfr hA]
    exact Finset.mem_insert_self _ _
  · by_cases hB : canMul a N (sortedVal a N (i + 1)) hv'mem + mMinus a N h2 < N
    · rw [gap_eq_etaNeg a h2 hi hjv'fr hB]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · rw [corner_gap a h2 hi hvmem hv'mem hA hB]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

/-- All distinct gap values lie in `{η⁺, η⁻, η⁺ + η⁻}` (non-degenerate regime). -/
theorem gaps_subset_returns (a : ℝ) {N : ℕ} (h2 : 2 ≤ orbitCard a N) :
    (gaps a N).toFinset ⊆
      ({etaPos a N, etaNeg a N, etaPos a N + etaNeg a N} : Finset ℝ) := by
  intro x hx
  rw [Multiset.mem_toFinset, mem_gaps_iff] at hx
  rcases hx with ⟨i, hi, hgap⟩ | hwrap
  · rw [← hgap]
    have hi' : i + 1 < orbitCard a N := by omega
    exact neighbour_gap_in_returns a h2 hi'
  · rw [hwrap, wraparound_eq_etaNeg a h2]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

/-- **The three-gap (Steinhaus) theorem, distinct-gap-count form.**  Every gap of
    `{i·a mod 1 : i < N}` is `η⁺`, `η⁻`, or `η⁺ + η⁻`, so at most three lengths. -/
theorem three_gap_card_le_three (a : ℝ) (N : ℕ) :
    (gaps a N).toFinset.card ≤ 3 := by
  by_cases h2 : 2 ≤ orbitCard a N
  · exact three_gap_card_le_three_of_subset a N (gaps_subset_returns a h2)
  · have h1 : orbitCard a N ≤ 1 := by omega
    calc (gaps a N).toFinset.card
        ≤ Multiset.card (gaps a N) := gaps_toFinset_card_le a N
      _ = 1 := gaps_card_eq_one_of_degenerate a h1
      _ ≤ 3 := by norm_num

/-- **The sum relation.**  When the gaps take exactly three distinct lengths, those
    lengths are precisely `η⁺`, `η⁻`, and `η⁺ + η⁻`; in particular the largest,
    `η⁺ + η⁻`, is the sum of the other two (they are positive: `etaPos_pos`,
    `etaNeg_pos`).  The nondegeneracy `2 ≤ orbitCard` is derived from `h3`. -/
theorem three_gap_lengths_eq (a : ℝ) {N : ℕ}
    (h3 : (gaps a N).toFinset.card = 3) :
    (gaps a N).toFinset = ({etaPos a N, etaNeg a N, etaPos a N + etaNeg a N} : Finset ℝ) := by
  have h2 : 2 ≤ orbitCard a N := by
    by_contra h
    have hle := gaps_toFinset_card_le a N
    rw [gaps_card_eq_one_of_degenerate a (by omega)] at hle
    omega
  refine Finset.eq_of_subset_of_card_le (gaps_subset_returns a h2) ?_
  rw [h3]; exact Finset.card_le_three


end ThreeGap
