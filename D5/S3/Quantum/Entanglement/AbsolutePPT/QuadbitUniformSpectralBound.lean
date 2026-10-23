/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: none
   digest: Three-row scalar purity bound with the natural integer optimizer. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.StructuralCone

set_option autoImplicit false

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
open scoped BigOperators Matrix
open Finset Matrix
open UniformSpectralBound.SharedSpectral
noncomputable section

private def middleColumn : Fin 3 → ℝ := ![-3,-6,-1]


private theorem boundary_positions_literal (N j : ℕ) (hN : 16 ≤ N) :
    positions N j = ![1,2,3,4,5,j,N-9,N-8,N-7,N-6,N-5,N-4,N-3,N-2,N-1,N] := by
  funext q
  fin_cases q <;> simp [positions] <;> omega

private theorem boundary_positions_strict (N j : ℕ) (hN : 16 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) : StrictMono (positions N j) := by
  intro q r hqr
  have hq := q.isLt
  have hr := r.isLt
  have hqr' : q.val < r.val := hqr
  dsimp [positions]
  split_ifs <;> omega

private theorem positions_bounds (N j : ℕ) (hN : 16 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) (q : Fin 16) :
    1 ≤ positions N j q ∧ positions N j q ≤ N := by
  have hq := q.isLt
  dsimp [positions]
  split_ifs <;> omega


-- The embedding is in ORIGINAL gap indices, so its value is one below the step.
private def slot (N : ℕ) (hN : 16 ≤ N) (j : ℕ) (hj : 6 ≤ j) (hj' : j ≤ N-10) :
    Fin 16 ↪ Fin N where
  toFun q := ⟨positions N j q - 1, by
    have := positions_bounds N j hN hj hj' q
    omega⟩
  inj' := by
    intro q r h
    have he : positions N j q - 1 = positions N j r - 1 := congrArg Fin.val h
    have hq := positions_bounds N j hN hj hj' q
    have hr := positions_bounds N j hN hj hj' r
    apply (boundary_positions_strict N j hN hj hj').injective
    omega

private theorem slot_step (N j : ℕ) (hN : 16 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) (q : Fin 16) :
    (slot N hN j hj hj' q).val + 1 = positions N j q := by
  have := positions_bounds N j hN hj hj' q
  change positions N j q - 1 + 1 = positions N j q
  omega

private theorem slot_five (N j : ℕ) (hN : 16 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) :
    (slot N hN j hj hj' 5).val + 1 = j := by
  calc
    _ = positions N j 5 := slot_step N j hN hj hj' 5
    _ = j := by norm_num [positions]

def middle (N : ℕ) : Finset (Fin N) :=
  univ.filter (fun k => 5 ≤ k.val ∧ k.val < N-10)

theorem mem_middle {N : ℕ} (k : Fin N) :
    k ∈ middle N ↔ 5 ≤ k.val ∧ k.val < N-10 := by
  simp [middle]

private theorem slot_boundary (N j : ℕ) (hN : 16 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) (q : Fin 16) (hq : q ≠ 5) :
    slot N hN j hj hj' q ∉ middle N := by
  have hqv := q.isLt
  have hq5 : q.val ≠ 5 := by
    intro he
    apply hq
    exact Fin.ext he
  rw [mem_middle]
  change ¬ (5 ≤ positions N j q - 1 ∧ positions N j q - 1 < N-10)
  dsimp only [positions]
  split_ifs <;> omega

private theorem boundary_covered (N j : ℕ) (hN : 16 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) (k : Fin N) (hk : k ∉ middle N) :
    ∃ q : Fin 16, q ≠ 5 ∧ slot N hN j hj hj' q = k := by
  have hkN := k.isLt
  have hk' : ¬ (5 ≤ k.val ∧ k.val < N-10) := by
    simpa only [mem_middle] using hk
  by_cases hhead : k.val < 5
  · refine ⟨⟨k.val, by omega⟩, ?_, ?_⟩
    · intro he
      have he' : k.val = 5 := congrArg Fin.val he
      omega
    · apply Fin.ext
      change positions N j ⟨k.val, by omega⟩ - 1 = k.val
      simp [positions, hhead]
  · have htail : N-10 ≤ k.val := by omega
    refine ⟨⟨6 + (k.val - (N-10)), by omega⟩, ?_, ?_⟩
    · intro he
      have he' : 6 + (k.val - (N-10)) = 5 := congrArg Fin.val he
      omega
    · apply Fin.ext
      change positions N j ⟨6 + (k.val - (N-10)), by omega⟩ - 1 = k.val
      dsimp only [positions]
      split_ifs <;> omega

def middleMass {N : ℕ} (g : Fin N → ℝ) : ℝ := ∑ k ∈ middle N, g k

def boundaryGaps {N : ℕ} (g : Fin N → ℝ) : Fin N → ℝ :=
  fun k => if k ∈ middle N then 0 else g k

def unitGap {N : ℕ} (k : Fin N) : Fin N → ℝ := Pi.single k 1

def fixedGaps {N : ℕ} (g : Fin N → ℝ) (k : Fin N) : Fin N → ℝ :=
  boundaryGaps g + middleMass g • unitGap k

-- All 15 boundary entries are literally unchanged in EVERY fixed term.
private theorem fixedGaps_boundary {N : ℕ} (g : Fin N → ℝ)
    (k : Fin N) (hk : k ∈ middle N) (i : Fin N) (hi : i ∉ middle N) :
    fixedGaps g k i = g i := by
  have hik : i ≠ k := by intro he; exact hi (he.symm ▸ hk)
  simp [fixedGaps, boundaryGaps, unitGap, hi, hik, Ne.symm hik]

-- Fixed coordinates do not depend on the middle position j.
def boundaryPacked {N : ℕ} (hN : 16 ≤ N) (g : Fin N → ℝ) (q : Fin 16) : ℝ :=
  if hh : q.val < 5 then g ⟨q.val, by omega⟩ else
  if q.val = 5 then middleMass g else
  g ⟨N - 10 + (q.val - 6), by have := q.isLt; omega⟩

private theorem packed_boundary (N j : ℕ) (hN : 16 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) (g : Fin N → ℝ)
    (q : Fin 16) (hq : q ≠ 5) :
    boundaryPacked hN g q = g (slot N hN j hj hj' q) := by
  have hqv := q.isLt
  have hq5 : q.val ≠ 5 := by
    intro he
    apply hq
    exact Fin.ext he
  by_cases hh : q.val < 5
  · dsimp only [boundaryPacked]
    rw [dif_pos hh]
    congr 1
    apply Fin.ext
    change q.val = positions N j q - 1
    simp [positions, hh]
  · dsimp only [boundaryPacked]
    rw [dif_neg hh, if_neg hq5]
    congr 1
    apply Fin.ext
    change N - 10 + (q.val - 6) = positions N j q - 1
    simp only [positions, if_neg hh, if_neg hq5]
    omega

theorem boundary_packed_nonneg {N : ℕ} (hN : 16 ≤ N)
    (g : Fin N → ℝ) (hg : ∀ k, 0 ≤ g k) : ∀ q, 0 ≤ boundaryPacked hN g q := by
  intro q
  dsimp only [boundaryPacked]
  split_ifs
  · exact hg _
  · exact sum_nonneg (fun k _ => hg k)
  · exact hg _

-- This is only a linear zero extension; the distinct slot embedding is explicit.
def boundaryLift (N j : ℕ) (hN : 16 ≤ N) (hj : 6 ≤ j) (hj' : j ≤ N-10) :
    (Fin 16 → ℝ) →ₗ[ℝ] (Fin N → ℝ) where
  toFun x := ∑ q, x q • unitGap (slot N hN j hj hj' q)
  map_add' x y := by
    calc
      _ = ∑ q, (x q • unitGap (slot N hN j hj hj' q) +
          y q • unitGap (slot N hN j hj hj' q)) :=
        sum_congr rfl (fun q _ => add_smul _ _ _)
      _ = _ := sum_add_distrib
  map_smul' a x := by
    rw [Finset.smul_sum]
    exact sum_congr rfl (fun q _ => mul_smul _ _ _)

theorem boundary_lift_packed (N : ℕ) (hN : 16 ≤ N) (g : Fin N → ℝ)
    (k : Fin N) (hk : k ∈ middle N) :
    boundaryLift N (k.val+1) hN (by have := (mem_middle k).mp hk; omega)
      (by have := (mem_middle k).mp hk; omega) (boundaryPacked hN g) = fixedGaps g k := by
  let hj : 6 ≤ k.val+1 := by have := (mem_middle k).mp hk; omega
  let hj' : k.val+1 ≤ N-10 := by have := (mem_middle k).mp hk; omega
  let e := slot N hN (k.val+1) hj hj'
  have he5 : e 5 = k := by
    apply Fin.ext
    have := slot_five N (k.val+1) hN hj hj'
    change (e 5).val + 1 = k.val + 1 at this
    omega
  ext i
  change (∑ q : Fin 16, boundaryPacked hN g q • unitGap (e q)) i = fixedGaps g k i
  rw [Finset.sum_apply]
  by_cases hi : i ∈ middle N
  · rw [Finset.sum_eq_single (5 : Fin 16)]
    · rw [he5]
      dsimp only [boundaryPacked]
      simp [fixedGaps, boundaryGaps, unitGap, hi]
    · intro q _ hq
      have hqi : e q ≠ i := by
        intro he
        have hb := slot_boundary N (k.val+1) hN hj hj' q hq
        exact hb (he.symm ▸ hi)
      rw [Pi.smul_apply, unitGap, Pi.single_eq_of_ne (Ne.symm hqi), smul_zero]
    · exact fun h => (h (mem_univ _)).elim
  · obtain ⟨q, hq, heq⟩ := boundary_covered N (k.val+1) hN hj hj' i hi
    change e q = i at heq
    rw [Finset.sum_eq_single q]
    · rw [packed_boundary N (k.val+1) hN hj hj' g q hq]
      change g (e q) • unitGap (e q) i = fixedGaps g k i
      rw [heq, fixedGaps_boundary g k hk i hi]
      simp [unitGap]
    · intro r _ hr
      have hri : e r ≠ i := by
        intro he
        exact hr (e.injective (he.trans heq.symm))
      rw [Pi.smul_apply, unitGap, Pi.single_eq_of_ne (Ne.symm hri), smul_zero]
    · exact fun h => (h (mem_univ _)).elim

-- The old step synthesis generalized from Fin 9 to Fin m is the ONLY synthesis.
abbrev fullSynth (N : ℕ) : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) :=
  synth (fun k : Fin N => k.val+1)

theorem fullSynth_unit {N : ℕ} (k : Fin N) :
    fullSynth N (unitGap k) = step N (k.val+1) := by
  classical
  simp [fullSynth, synth, unitGap]

theorem boundary_synth_lift (N j : ℕ) (hN : 16 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) (x : Fin 16 → ℝ) :
    fullSynth N (boundaryLift N j hN hj hj' x) = synth (d := N) (positions N j) x := by
  change fullSynth N (∑ q, x q • unitGap (slot N hN j hj hj' q)) = _
  rw [map_sum]
  change (∑ q, fullSynth N (x q • unitGap (slot N hN j hj hj' q))) =
    ∑ q, x q • step N (positions N j q)
  apply sum_congr rfl
  intro q _
  rw [map_smul, fullSynth_unit, slot_step N j hN hj hj']

-- The exact original sums, oriented bottom minus top. No selected terms dropped.
def boundarySlackMap (N : ℕ) (hN : 16 ≤ N) : (Fin N → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun l := ![
    (∑ i : Fin 6, l ⟨N-6+i.val, by omega⟩) - ∑ i : Fin 3, l ⟨i.val, by omega⟩,
    (∑ i : Fin 10, l ⟨N-10+i.val, by omega⟩) - ∑ i : Fin 6, l ⟨i.val, by omega⟩,
    (∑ i : Fin 3, l ⟨N-3+i.val, by omega⟩) - l ⟨0, by omega⟩]
  map_add' x y := by
    ext r
    fin_cases r <;> simp [Finset.sum_add_distrib] <;> ring
  map_smul' a x := by
    ext r
    fin_cases r <;> simp [Finset.mul_sum, mul_sub] <;> ring

private theorem middle_step_slack (N j : ℕ) (hN : 16 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) :
    boundarySlackMap N hN (step N j) = middleColumn := by
  ext r
  fin_cases r <;>
    simp (disch := omega) [boundarySlackMap, middleColumn, step, Fin.sum_univ_succ,
      if_pos, if_neg] <;> norm_num

set_option maxHeartbeats 2000000 in
-- All sixteen slots and all three original rows are evaluated separately.
private theorem slot_step_slack (N j : ℕ) (hN : 16 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) (q : Fin 16) :
    boundarySlackMap N hN (step N (positions N j q)) = fun r => A r q := by
  rw [boundary_positions_literal N j hN]
  ext r
  fin_cases q <;> fin_cases r <;>
    simp (disch := omega) [boundarySlackMap, A, step, Fin.sum_univ_succ, if_pos, if_neg] <;>
    norm_num

private theorem slack_synth (N j : ℕ) (hN : 16 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) (x : Fin 16 → ℝ) :
    boundarySlackMap N hN (synth (d := N) (positions N j) x) = A *ᵥ x := by
  change boundarySlackMap N hN (∑ q, x q • step N (positions N j q)) = _
  rw [map_sum]
  calc
    _ = ∑ q, x q • (fun r => A r q) := by
      apply sum_congr rfl
      intro q _
      rw [map_smul, slot_step_slack N j hN hj hj']
    _ = _ := by
      ext r
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

-- The A-image of the full Fin N gap vector is the original row-slack vector.
def boundaryGapRows (N : ℕ) (hN : 16 ≤ N) : (Fin N → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
  (boundarySlackMap N hN).comp (fullSynth N)

theorem gaps_split {N : ℕ} (g : Fin N → ℝ) :
    boundaryGaps g + ∑ k ∈ middle N, g k • unitGap k = g := by
  classical
  ext i
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hi : i ∈ middle N
  · rw [Finset.sum_eq_single i]
    · simp [boundaryGaps, unitGap, hi]
    · intro k _ hki
      simp [unitGap, hki, Ne.symm hki]
    · exact fun h => (h hi).elim
  · have hz : (∑ k ∈ middle N, g k * unitGap k i) = 0 := by
      apply sum_eq_zero
      intro k hk
      have hki : k ≠ i := by intro he; exact hi (he ▸ hk)
      simp [unitGap, hki, Ne.symm hki]
    simp [boundaryGaps, hi, hz]

private theorem gapRows_fixed (N : ℕ) (hN : 16 ≤ N) (g : Fin N → ℝ)
    (k : Fin N) (hk : k ∈ middle N) :
    boundaryGapRows N hN (fixedGaps g k) = boundaryGapRows N hN g := by
  have hu (i : Fin N) (hi : i ∈ middle N) :
      boundaryGapRows N hN (unitGap i) = middleColumn := by
    change boundarySlackMap N hN (fullSynth N (unitGap i)) = _
    rw [fullSynth_unit]
    exact middle_step_slack N (i.val+1) hN
      (by have := (mem_middle i).mp hi; omega)
      (by have := (mem_middle i).mp hi; omega)
  have hsum : middleMass g • middleColumn =
      ∑ i ∈ middle N, g i • boundaryGapRows N hN (unitGap i) := by
    rw [middleMass, Finset.sum_smul]
    apply sum_congr rfl
    intro i hi
    rw [hu i hi]
  calc
    boundaryGapRows N hN (fixedGaps g k) =
        boundaryGapRows N hN (boundaryGaps g) + middleMass g • middleColumn := by
      rw [fixedGaps, map_add, map_smul, hu k hk]
    _ = boundaryGapRows N hN (boundaryGaps g + ∑ i ∈ middle N, g i • unitGap i) := by
      rw [map_add, map_sum]
      rw [hsum]
      congr 1
      apply sum_congr rfl
      intro i hi
      rw [map_smul]
    _ = boundaryGapRows N hN g := by rw [gaps_split g]

theorem boundary_packed_image (N : ℕ) (hN : 16 ≤ N) (g : Fin N → ℝ)
    (k : Fin N) (hk : k ∈ middle N) :
    A *ᵥ boundaryPacked hN g = boundaryGapRows N hN g := by
  have hj : 6 ≤ k.val+1 := by have := (mem_middle k).mp hk; omega
  have hj' : k.val+1 ≤ N-10 := by have := (mem_middle k).mp hk; omega
  rw [← slack_synth N (k.val+1) hN hj hj', ← boundary_synth_lift N (k.val+1) hN hj hj']
  rw [boundary_lift_packed N hN g k hk]
  exact gapRows_fixed N hN g k hk

-- This expression is an equality of FULL original gaps, not just row images.
private theorem middle_barycentric {N : ℕ} (g : Fin N → ℝ)
    (hM : middleMass g ≠ 0) :
    (∑ k ∈ middle N, (g k / middleMass g) • fixedGaps g k) = g := by
  simp only [fixedGaps, smul_add, smul_smul, sum_add_distrib]
  rw [← sum_smul, ← sum_div]
  change (middleMass g / middleMass g) • boundaryGaps g +
    (∑ k ∈ middle N, (g k / middleMass g * middleMass g) • unitGap k) = g
  simp only [div_self hM, one_smul, div_mul_cancel₀ _ hM]
  exact gaps_split g

-- The fixed-cone estimate follows from arbitrary ordered defects,
-- scalar interval estimates and constructive bulk subtraction.
private theorem norm_from_fixed_cones (N : ℕ) (hN : 16 ≤ N) (c : ℝ)
    (fixedGood : ∀ (j : ℕ), 6 ≤ j → j ≤ N-10 →
      ∀ x : Fin 16 → ℝ, (∀ q, 0 ≤ x q) → (∀ r, 0 ≤ (A *ᵥ x) r) →
        spectralGood c (synth (d := N) (positions N j) x))
    (l : Fin N → ℝ) (ho : Antitone l) (hn : ∀ i, 0 ≤ l i)
    (hrows : ∀ r, 0 ≤ boundarySlackMap N hN l r) : spectralGood c l := by
  let g := spectralGap l
  have hg : ∀ k, 0 ≤ g k := spectralGap_nonneg l ho hn
  have hrecon : fullSynth N g = l := gap_reconstruct l
  have hmass : 0 ≤ middleMass g := sum_nonneg (fun k _ => hg k)
  have hpacked : ∀ q, 0 ≤ boundaryPacked hN g q := boundary_packed_nonneg hN g hg
  have hfixed (k : Fin N) (hk : k ∈ middle N) :
      spectralGood c (fullSynth N (fixedGaps g k)) := by
    have hj : 6 ≤ k.val+1 := by have := (mem_middle k).mp hk; omega
    have hj' : k.val+1 ≤ N-10 := by have := (mem_middle k).mp hk; omega
    rw [← boundary_lift_packed N hN g k hk, boundary_synth_lift N (k.val+1) hN hj hj']
    apply fixedGood (k.val+1) hj hj' (boundaryPacked hN g) hpacked
    intro r
    rw [boundary_packed_image N hN g k hk]
    change 0 ≤ boundarySlackMap N hN (fullSynth N g) r
    rw [hrecon]
    exact hrows r
  by_cases hM : middleMass g = 0
  · -- Boundary-only branch, no division: every middle gap is actually zero.
    have hz : ∀ k ∈ middle N, g k = 0 :=
      (sum_eq_zero_iff_of_nonneg (fun k _ => hg k)).mp hM
    have hb : boundaryGaps g = g := by
      ext k
      by_cases hk : k ∈ middle N
      · simp [boundaryGaps, hk, hz k hk]
      · simp [boundaryGaps, hk]
    let k : Fin N := ⟨5, by omega⟩
    have hk : k ∈ middle N := by simp [middle, k]; omega
    have hf := hfixed k hk
    have he : fixedGaps g k = g := by simp [fixedGaps, hM, hb]
    rwa [he, hrecon] at hf
  · -- Positive branch: weights g_k/M ≥ 0, sum=1, boundaries unchanged.
    have hgood : spectralGood c
        (fullSynth N (∑ k ∈ middle N, (g k / middleMass g) • fixedGaps g k)) := by
      rw [map_sum]
      apply sum_mem_of_closed (spectralGood c) (spectralGood_zero N c)
        (fun x y hx hy => spectralGood_add c x y hx hy)
      intro k hk
      rw [map_smul]
      exact spectralGood_smul c _ _ (div_nonneg (hg k) hmass) (hfixed k hk)
    rwa [middle_barycentric g hM, hrecon] at hgood

private abbrev lift16 (N j : ℕ) (hN : 56 ≤ N) (hj : 6 ≤ j) (hj' : j ≤ N-10) :
    (Fin 16 → ℝ) →ₗ[ℝ] (Fin N → ℝ) :=
  boundaryLift N j (by omega) hj hj'

def packed {N : ℕ} (hN : 56 ≤ N) (g : Fin N → ℝ) (q : Fin 16) : ℝ :=
  boundaryPacked (by omega) g q

def slackMap (N : ℕ) (hN : 56 ≤ N) : (Fin N → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
  boundarySlackMap N (by omega)

def gapRows (N : ℕ) (hN : 56 ≤ N) : (Fin N → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
  boundaryGapRows N (by omega)

theorem packed_nonneg {N : ℕ} (hN : 56 ≤ N)
    (g : Fin N → ℝ) (hg : ∀ k, 0 ≤ g k) : ∀ q, 0 ≤ packed hN g q := by
  exact boundary_packed_nonneg (by omega) g hg

theorem lift_packed (N : ℕ) (hN : 56 ≤ N) (g : Fin N → ℝ)
    (k : Fin N) (hk : k ∈ middle N) :
    lift16 N (k.val+1) hN (by have := (mem_middle k).mp hk; omega)
      (by have := (mem_middle k).mp hk; omega) (packed hN g) = fixedGaps g k := by
  exact boundary_lift_packed N (by omega) g k hk

theorem synth_lift (N j : ℕ) (hN : 56 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) (x : Fin 16 → ℝ) :
    fullSynth N (lift16 N j hN hj hj' x) = synth (d := N) (positions N j) x := by
  exact boundary_synth_lift N j (by omega) hj hj' x

theorem packed_image (N : ℕ) (hN : 56 ≤ N) (g : Fin N → ℝ)
    (k : Fin N) (hk : k ∈ middle N) :
    A *ᵥ packed hN g = gapRows N hN g := by
  exact boundary_packed_image N (by omega) g k hk

-- The exact scalar target uses the natural integer optimizer.

set_option maxRecDepth 8192 in
set_option maxHeartbeats 20000000 in
theorem three_row_scalar_bound (N : ℕ) (hN : 67 ≤ N)
    (l : Fin N → ℝ) (ho : Antitone l) (hn : ∀ i, 0 ≤ l i)
    (hmass : ∑ i, l i = 1)
    (hL3 : (∑ i : Fin 3, l ⟨i.val, by omega⟩) ≤
      ∑ i : Fin 6, l ⟨N-6+i.val, by omega⟩)
    (hL4 : (∑ i : Fin 6, l ⟨i.val, by omega⟩) ≤
      ∑ i : Fin 10, l ⟨N-10+i.val, by omega⟩)
    (hC3 : l ⟨0, by omega⟩ ≤ ∑ i : Fin 3, l ⟨N-3+i.val, by omega⟩) :
    let t : ℕ := (3*N+4)/8
    ∑ i, (l i)^2 ≤ (9*(N : ℝ)+16*(t : ℝ))/(3*(N : ℝ)+2*(t : ℝ))^2 := by
  classical
  have h56 : 56 ≤ N := by omega
  -- The arbitrary-defect proof supplies fixedGood with no success premise.
  have fixedGood : ∀ (j : ℕ), 6 ≤ j → j ≤ N-10 →
      ∀ x : Fin 16 → ℝ, (∀ q, 0 ≤ x q) → (∀ r, 0 ≤ (A *ᵥ x) r) →
        spectralGood (Real.sqrt (target N))
          (synth (d := N) (positions N j) x) := by
    intro j hj hj' x hx hAx
    exact structural_fixed_good N j hN hj hj' x hx hAx

  have hrows : ∀ r, 0 ≤ slackMap N h56 l r := by
    intro r
    fin_cases r
    · exact sub_nonneg.mpr hL3
    · exact sub_nonneg.mpr hL4
    · exact sub_nonneg.mpr hC3
  have hgood := norm_from_fixed_cones N (by omega) (Real.sqrt (target N)) fixedGood l ho hn hrows
  have hb := spectralGood_square (Real.sqrt (target N)) l (Real.sqrt_nonneg _)
    (by rw [hmass]; norm_num) hgood
  rw [hmass, Real.sq_sqrt (target_nonneg N)] at hb
  simpa only [one_pow, mul_one, target] using hb

#print axioms three_row_scalar_bound

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
