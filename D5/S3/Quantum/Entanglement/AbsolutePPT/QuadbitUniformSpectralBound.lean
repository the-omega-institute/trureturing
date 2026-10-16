/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniformSpectralBound.three_row_scalar_bound; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SpectrumCompression.A
   digest: Three-row scalar purity bound with the natural integer optimizer. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.FullRowCofactor
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.SpectrumCompression
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.RaySoundness
import D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform.ScalarConeSoundness

set_option autoImplicit false

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
open scoped BigOperators Matrix
open Finset Matrix
open NonnegativeKernelCircuit NonnegativeKernelCofactor
open D5.S3.Arith.Lattices.CofactorKernel (cofactor augment kernel_cross_identity)
open UniformSpectralBound.SharedSpectral
open ScalarCertificate
noncomputable section

private def middleColumn : Fin 3 → ℝ := ![-3,-6,-1]


private theorem positions_bounds (N j : ℕ) (hN : 67 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) (q : Fin 16) :
    1 ≤ positions N j q ∧ positions N j q ≤ N := by
  have hq := q.isLt
  dsimp [positions]
  split_ifs <;> omega


-- The embedding is in ORIGINAL gap indices, so its value is one below the step.
private def slot (N : ℕ) (hN : 67 ≤ N) (j : ℕ) (hj : 6 ≤ j) (hj' : j ≤ N-10) :
    Fin 16 ↪ Fin N where
  toFun q := ⟨positions N j q - 1, by
    have := positions_bounds N j hN hj hj' q
    omega⟩
  inj' := by
    intro q r h
    have he : positions N j q - 1 = positions N j r - 1 := congrArg Fin.val h
    have hq := positions_bounds N j hN hj hj' q
    have hr := positions_bounds N j hN hj hj' r
    apply (positions_strict N j hN hj hj').injective
    omega

private theorem slot_step (N j : ℕ) (hN : 67 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) (q : Fin 16) :
    (slot N hN j hj hj' q).val + 1 = positions N j q := by
  have := positions_bounds N j hN hj hj' q
  change positions N j q - 1 + 1 = positions N j q
  omega

private theorem slot_five (N j : ℕ) (hN : 67 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) :
    (slot N hN j hj hj' 5).val + 1 = j := by
  simpa [positions] using slot_step N j hN hj hj' 5

private def middle (N : ℕ) : Finset (Fin N) :=
  univ.filter (fun k => 5 ≤ k.val ∧ k.val < N-10)

private theorem mem_middle {N : ℕ} (k : Fin N) :
    k ∈ middle N ↔ 5 ≤ k.val ∧ k.val < N-10 := by
  simp [middle]

private theorem slot_boundary (N j : ℕ) (hN : 67 ≤ N)
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

private theorem boundary_covered (N j : ℕ) (hN : 67 ≤ N)
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

private def middleMass {N : ℕ} (g : Fin N → ℝ) : ℝ := ∑ k ∈ middle N, g k

private def boundaryGaps {N : ℕ} (g : Fin N → ℝ) : Fin N → ℝ :=
  fun k => if k ∈ middle N then 0 else g k

private def unitGap {N : ℕ} (k : Fin N) : Fin N → ℝ := Pi.single k 1

private def fixedGaps {N : ℕ} (g : Fin N → ℝ) (k : Fin N) : Fin N → ℝ :=
  boundaryGaps g + middleMass g • unitGap k

-- All 15 boundary entries are literally unchanged in EVERY fixed term.
private theorem fixedGaps_boundary {N : ℕ} (g : Fin N → ℝ)
    (k : Fin N) (hk : k ∈ middle N) (i : Fin N) (hi : i ∉ middle N) :
    fixedGaps g k i = g i := by
  have hik : i ≠ k := by intro he; exact hi (he.symm ▸ hk)
  simp [fixedGaps, boundaryGaps, unitGap, hi, hik, Ne.symm hik]

-- Fixed coordinates do not depend on the middle position j.
private def packed {N : ℕ} (hN : 67 ≤ N) (g : Fin N → ℝ) (q : Fin 16) : ℝ :=
  if hh : q.val < 5 then g ⟨q.val, by omega⟩ else
  if q.val = 5 then middleMass g else
  g ⟨N - 10 + (q.val - 6), by have := q.isLt; omega⟩

private theorem packed_boundary (N j : ℕ) (hN : 67 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) (g : Fin N → ℝ)
    (q : Fin 16) (hq : q ≠ 5) :
    packed hN g q = g (slot N hN j hj hj' q) := by
  have hqv := q.isLt
  have hq5 : q.val ≠ 5 := by
    intro he
    apply hq
    exact Fin.ext he
  by_cases hh : q.val < 5
  · simp only [packed, dif_pos hh]
    congr 1
    apply Fin.ext
    change q.val = positions N j q - 1
    simp [positions, hh]
  · simp only [packed, dif_neg hh, if_neg hq5]
    congr 1
    apply Fin.ext
    change N - 10 + (q.val - 6) = positions N j q - 1
    simp only [positions, if_neg hh, if_neg hq5]
    omega

private theorem packed_nonneg {N : ℕ} (hN : 67 ≤ N)
    (g : Fin N → ℝ) (hg : ∀ k, 0 ≤ g k) : ∀ q, 0 ≤ packed hN g q := by
  intro q
  dsimp only [packed]
  split_ifs
  · exact hg _
  · exact sum_nonneg (fun k _ => hg k)
  · exact hg _

-- This is only a linear zero extension; the distinct slot embedding is explicit.
private def lift16 (N j : ℕ) (hN : 67 ≤ N) (hj : 6 ≤ j) (hj' : j ≤ N-10) :
    (Fin 16 → ℝ) →ₗ[ℝ] (Fin N → ℝ) where
  toFun x := ∑ q, x q • unitGap (slot N hN j hj hj' q)
  map_add' x y := by simp [add_smul, sum_add_distrib]
  map_smul' a x := by simp [Finset.smul_sum, smul_smul]

private theorem lift_packed (N : ℕ) (hN : 67 ≤ N) (g : Fin N → ℝ)
    (k : Fin N) (hk : k ∈ middle N) :
    lift16 N (k.val+1) hN (by have := (mem_middle k).mp hk; omega)
      (by have := (mem_middle k).mp hk; omega) (packed hN g) = fixedGaps g k := by
  let hj : 6 ≤ k.val+1 := by have := (mem_middle k).mp hk; omega
  let hj' : k.val+1 ≤ N-10 := by have := (mem_middle k).mp hk; omega
  let e := slot N hN (k.val+1) hj hj'
  have he5 : e 5 = k := by
    apply Fin.ext
    have := slot_five N (k.val+1) hN hj hj'
    change (e 5).val + 1 = k.val + 1 at this
    omega
  ext i
  change (∑ q : Fin 16, packed hN g q • unitGap (e q)) i = fixedGaps g k i
  rw [Finset.sum_apply]
  by_cases hi : i ∈ middle N
  · rw [Finset.sum_eq_single (5 : Fin 16)]
    · simp [fixedGaps, boundaryGaps, unitGap, packed, hi, he5]
    · intro q _ hq
      have hqi : e q ≠ i := by
        intro he
        have hb := slot_boundary N (k.val+1) hN hj hj' q hq
        exact hb (he.symm ▸ hi)
      simp [unitGap, hqi, Ne.symm hqi]
    · simp
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
      simp [unitGap, hri, Ne.symm hri]
    · simp

-- The old step synthesis generalized from Fin 9 to Fin m is the ONLY synthesis.
private abbrev fullSynth (N : ℕ) : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) :=
  synth (fun k : Fin N => k.val+1)

private theorem fullSynth_unit {N : ℕ} (k : Fin N) :
    fullSynth N (unitGap k) = step N (k.val+1) := by
  classical
  simp [fullSynth, synth, unitGap]

private theorem synth_lift (N j : ℕ) (hN : 67 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) (x : Fin 16 → ℝ) :
    fullSynth N (lift16 N j hN hj hj' x) = synth (d := N) (positions N j) x := by
  change fullSynth N (∑ q, x q • unitGap (slot N hN j hj hj' q)) = _
  rw [map_sum]
  simp_rw [map_smul, fullSynth_unit, slot_step N j hN hj hj']
  rfl

-- The exact original sums, oriented bottom minus top. No selected terms dropped.
private def slackMap (N : ℕ) (hN : 67 ≤ N) : (Fin N → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
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

private theorem middle_step_slack (N j : ℕ) (hN : 67 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) :
    slackMap N hN (step N j) = middleColumn := by
  ext r
  fin_cases r <;>
    simp (disch := omega) [slackMap, middleColumn, step, Fin.sum_univ_succ,
      if_pos, if_neg] <;> norm_num

set_option maxHeartbeats 2000000 in
-- All sixteen slots and all three original rows are evaluated separately.
private theorem slot_step_slack (N j : ℕ) (hN : 67 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) (q : Fin 16) :
    slackMap N hN (step N (positions N j q)) = fun r => A r q := by
  rw [positions_literal N j hN]
  ext r
  fin_cases q <;> fin_cases r <;>
    simp (disch := omega) [slackMap, A, step, Fin.sum_univ_succ, if_pos, if_neg] <;>
    norm_num

private theorem slack_synth (N j : ℕ) (hN : 67 ≤ N)
    (hj : 6 ≤ j) (hj' : j ≤ N-10) (x : Fin 16 → ℝ) :
    slackMap N hN (synth (d := N) (positions N j) x) = A *ᵥ x := by
  change slackMap N hN (∑ q, x q • step N (positions N j q)) = _
  rw [map_sum]
  simp_rw [map_smul, slot_step_slack N j hN hj hj']
  ext r
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

-- The A-image of the full Fin N gap vector is the original row-slack vector.
private def gapRows (N : ℕ) (hN : 67 ≤ N) : (Fin N → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
  (slackMap N hN).comp (fullSynth N)

private theorem gaps_split {N : ℕ} (g : Fin N → ℝ) :
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

private theorem gapRows_fixed (N : ℕ) (hN : 67 ≤ N) (g : Fin N → ℝ)
    (k : Fin N) (hk : k ∈ middle N) :
    gapRows N hN (fixedGaps g k) = gapRows N hN g := by
  have hu (i : Fin N) (hi : i ∈ middle N) :
      gapRows N hN (unitGap i) = middleColumn := by
    change slackMap N hN (fullSynth N (unitGap i)) = _
    rw [fullSynth_unit]
    exact middle_step_slack N (i.val+1) hN
      (by have := (mem_middle i).mp hi; omega)
      (by have := (mem_middle i).mp hi; omega)
  have hsum : middleMass g • middleColumn =
      ∑ i ∈ middle N, g i • gapRows N hN (unitGap i) := by
    rw [middleMass, Finset.sum_smul]
    apply sum_congr rfl
    intro i hi
    rw [hu i hi]
  calc
    gapRows N hN (fixedGaps g k) =
        gapRows N hN (boundaryGaps g) + middleMass g • middleColumn := by
      simp only [fixedGaps, map_add, map_smul, hu k hk]
    _ = gapRows N hN (boundaryGaps g + ∑ i ∈ middle N, g i • unitGap i) := by
      rw [map_add, map_sum]
      simp_rw [map_smul]
      rw [hsum]
    _ = gapRows N hN g := by rw [gaps_split g]

private theorem packed_image (N : ℕ) (hN : 67 ≤ N) (g : Fin N → ℝ)
    (k : Fin N) (hk : k ∈ middle N) :
    A *ᵥ packed hN g = gapRows N hN g := by
  have hj : 6 ≤ k.val+1 := by have := (mem_middle k).mp hk; omega
  have hj' : k.val+1 ≤ N-10 := by have := (mem_middle k).mp hk; omega
  rw [← slack_synth N (k.val+1) hN hj hj', ← synth_lift N (k.val+1) hN hj hj']
  rw [lift_packed N hN g k hk]
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

-- The fixed-cone fact is the remaining mathematical dependency, to be proved
-- by the cofactor and scalar estimates inside the substantive scalar proof.
private theorem norm_from_fixed_cones (N : ℕ) (hN : 67 ≤ N) (c : ℝ)
    (fixedGood : ∀ (j : ℕ), 6 ≤ j → j ≤ N-10 →
      ∀ x : Fin 16 → ℝ, (∀ q, 0 ≤ x q) → (∀ r, 0 ≤ (A *ᵥ x) r) →
        spectralGood c (synth (d := N) (positions N j) x))
    (l : Fin N → ℝ) (ho : Antitone l) (hn : ∀ i, 0 ≤ l i)
    (hrows : ∀ r, 0 ≤ slackMap N hN l r) : spectralGood c l := by
  let g := spectralGap l
  have hg : ∀ k, 0 ≤ g k := spectralGap_nonneg l ho hn
  have hrecon : fullSynth N g = l := gap_reconstruct l
  have hmass : 0 ≤ middleMass g := sum_nonneg (fun k _ => hg k)
  have hpacked : ∀ q, 0 ≤ packed hN g q := packed_nonneg hN g hg
  have hfixed (k : Fin N) (hk : k ∈ middle N) :
      spectralGood c (fullSynth N (fixedGaps g k)) := by
    have hj : 6 ≤ k.val+1 := by have := (mem_middle k).mp hk; omega
    have hj' : k.val+1 ≤ N-10 := by have := (mem_middle k).mp hk; omega
    rw [← lift_packed N hN g k hk, synth_lift N (k.val+1) hN hj hj']
    apply fixedGood (k.val+1) hj hj' (packed hN g) hpacked
    intro r
    rw [packed_image N hN g k hk]
    change 0 ≤ slackMap N hN (fullSynth N g) r
    simpa only [hrecon] using hrows r
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
  -- The support and ray certificates supply the finite arithmetic for this bound.
  -- fixedGood is constructed here; it is not a hypothesis of the result.
  have fixedGood : ∀ (j : ℕ), 6 ≤ j → j ≤ N-10 →
      ∀ x : Fin 16 → ℝ, (∀ q, 0 ≤ x q) → (∀ r, 0 ≤ (A *ᵥ x) r) →
        spectralGood (Real.sqrt (target N))
          (synth (d := N) (positions N j) x) := by
    intro j hj hj' x hx hAx
    have hpositions : positions N j = positions₁₆ N j := by
      rw [positions_literal N j hN]
      rfl
    have hp : ∀ q, positions N j q ≤ N := by
      rw [hpositions]
      exact positions₁₆_le N j hN hj'
    have hrays (i : Fin 187) :
        spectralGood (Real.sqrt (target N))
          (synth (d := N) (positions N j)
            (fun q => ((originalRay i).gap q : ℝ))) := by
      apply spectralGood_of_square _ _ (Real.sqrt_nonneg _)
      · rw [mass_synth (positions N j) hp, hpositions,
          ray_mass_identity (originalRay i) (originalRay_valid i).moments N j hN]
        exact (ray_mass_positive (originalRay i) (originalRay_valid i)
          (N : ℝ) (j : ℝ) (by exact_mod_cast hN) (by exact_mod_cast hj)).le
      · rw [square_synth (positions N j) hp, mass_synth (positions N j) hp,
          Real.sq_sqrt (target_nonneg N), hpositions]
        simpa only [target, bulkValue, bulkIndex] using
          original_ray_gram_bound i N j hN hj hj'

    -- Good is the actual promoted norm-to-mass property after projection and
    -- synthesis at these SAME N,j and positions, not an abstract assumed cone.
    let K : PointedCone ℝ (Fin 19 → ℝ) := {
      carrier := {z | spectralGood (Real.sqrt (target N))
        (synth (d := N) (positions N j) (project z))}
      zero_mem' := by
        change spectralGood (Real.sqrt (target N))
          (synth (d := N) (positions N j) (project 0))
        simp only [map_zero]
        exact spectralGood_zero N _
      add_mem' := by
        intro u v hu hv
        change spectralGood (Real.sqrt (target N))
          (synth (d := N) (positions N j) (project (u+v)))
        simp only [map_add]
        exact spectralGood_add _ _ _ hu hv
      smul_mem' := by
        intro a z hz
        change spectralGood (Real.sqrt (target N))
          (synth (d := N) (positions N j) (project ((a : ℝ) • z)))
        simp only [map_smul]
        exact spectralGood_smul _ (a : ℝ) _ a.property hz }

    have hull_le : PointedCone.hull ℝ (cofactorCandidates bR) ≤ K := by
      apply Submodule.span_le.mpr
      intro w hw
      have hwdata : InKernel bR w ∧ w ≠ 0 := by
        rcases hw with ⟨k, hk, ρ, σ, η, hη, hweq, hwK, hw0⟩
        exact ⟨hwK, hw0⟩
      obtain ⟨S, ε, a, hε, ha, heq⟩ :=
        cofactor_candidate_ordered_full bR bR_full_span hw
      -- FullSupport 19 3 is definitionally Support4. The local orderedCof is
      -- definitionally the private generic orderedCof bR, including the ordering.
      have hwfull : w = a • (ε • orderedCof S) := heq
      have hvn : ∀ q, 0 ≤ (ε • orderedCof S) q := by
        intro q
        have h := hwdata.1.1 q
        rw [hwfull] at h
        change 0 ≤ a * (ε • orderedCof S) q at h
        exact nonneg_of_mul_nonneg_right h ha
      have hv0 : ε • orderedCof S ≠ 0 := by
        intro hz
        apply hwdata.2
        rw [hwfull, hz, smul_zero]
      obtain ⟨t, d, hd, hcat⟩ :=
        oriented_full_cofactor_in_catalog S ε hε hvn hv0
      have hwcat : w = (a*d) • (fun q => (zZ t q : ℝ)) := by
        rw [hwfull, hcat, smul_smul]
      change spectralGood (Real.sqrt (target N))
        (synth (d := N) (positions N j) (project w))
      rw [hwcat]
      simp only [map_smul, project_catalog_owner t]
      exact spectralGood_smul _ (a*d) _ (mul_pos ha hd).le (hrays t)

    have hkernel : InKernel bR (liftGap x) := by
      apply (liftGap_kernel x).mpr
      exact ⟨hx, by simpa only [aR_eq_A] using hAx⟩
    have hmem : liftGap x ∈ PointedCone.hull ℝ (cofactorCandidates bR) :=
      (nonnegKernel_iff_mem_hull_cofactorCandidates bR (liftGap x)).mp hkernel
    have hgood := hull_le hmem
    change spectralGood (Real.sqrt (target N))
      (synth (d := N) (positions N j) (project (liftGap x))) at hgood
    have hproject : project (liftGap x) = x := by
      funext q
      change Fin.append x (aR *ᵥ x) (Fin.castAdd 3 q) = x q
      exact Fin.append_left _ _ _
    rwa [hproject] at hgood

  have hrows : ∀ r, 0 ≤ slackMap N hN l r := by
    intro r
    fin_cases r
    · exact sub_nonneg.mpr hL3
    · exact sub_nonneg.mpr hL4
    · exact sub_nonneg.mpr hC3
  have hgood := norm_from_fixed_cones N hN (Real.sqrt (target N)) fixedGood l ho hn hrows
  have hb := spectralGood_square (Real.sqrt (target N)) l (Real.sqrt_nonneg _)
    (by rw [hmass]; norm_num) hgood
  rw [hmass, Real.sq_sqrt (target_nonneg N)] at hb
  simpa only [one_pow, mul_one, target] using hb

#print axioms three_row_scalar_bound

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniformSpectralBound
