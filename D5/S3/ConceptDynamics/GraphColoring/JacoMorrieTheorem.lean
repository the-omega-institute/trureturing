/- GID: D5/S3/ConceptDynamics/GraphColoring/JacoMorrieTheorem
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/GraphColoring/JacoMorrieTheorem
   mirror-E: none(waiver:structural-proof)
   anchors: [lake/module/D5.S3.ConceptDynamics.GraphColoring.JacoMaximumSet, lake/module/D5.S3.ConceptDynamics.GraphColoring.JacoMaximumDegree, lake/module/D5.S3.ConceptDynamics.GraphColoring.JacoTripleMaximizers, lake/module/D5.S3.ConceptDynamics.GraphColoring.JacoDirectedPathCount]
   utility: none
   digest: Morrie's theorem on finite Jaco graphs holds once n = R_k is added to its indegree conditions. -/

import D5.S3.ConceptDynamics.GraphColoring.JacoMaximumSet
import D5.S3.ConceptDynamics.GraphColoring.JacoMaximumDegree
import D5.S3.ConceptDynamics.GraphColoring.JacoTripleMaximizers
import D5.S3.ConceptDynamics.GraphColoring.JacoDirectedPathCount

/-! The corrected form of Morrie's theorem for the finite linear Jaco graphs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.GraphColoring.JacoMorrieTheorem

/-
proof_shape:
  indeg: definition
  bo_step2: bind-only (consumers: next_set, corrected, result)
  no_two_flat: content (consumer: result)
  indeg_eq_iff: bind-only (consumers: corrected, result)
  prime_eq: bind-only (consumer: corrected)
  mem_jaconian_iff: bind-only (consumer: next_set)
  icc_three, icc_two: bind-only (consumer: corrected)
  next_set: content (consumer: corrected)
  corrected: bind-only (consumer: result)
  result: content
direct frozen dependencies:
  D5/S3/ConceptDynamics/GraphColoring/JacoMaximumSet.result (statement_id
    sha256:d31cfe56216a7368dfd3700d57fd0f68ca52816f38e6d48739b538a93e32a20f)
  D5/S3/ConceptDynamics/GraphColoring/JacoMaximumDegree.degree_formula (statement_id
    sha256:0e86e1b7bcb5cf4a23c8cf5390ae207b2bcf9fd946fd97d2badc1c1cb672c72d)
  D5/S3/ConceptDynamics/GraphColoring/JacoEndpointBeatty.endpoint_eq_beatty, beatty_bounds
    (statement_id sha256:15f9f8627a73d9d28232ecd5a1deb1d41054ab6114f152475628df4fd9def028)
  D5/S3/ConceptDynamics/GraphColoring/JacoTripleMaximizers.g_pos, g_quad, bo_le, bo_zero
  D5/S3/ConceptDynamics/GraphColoring/JacoDirectedPathCount.out_step
  (both made public in this delivery; their modules are re-pinned through the canonical writer)
escape_witness: by the degree formula deg(v_i) = min(i, n + 1 - b_i) at order n + 1, after a
  singleton maximum set {v_k} at n = R_k = k + b_k the label k + 2 is a maximizer of
  J_(n+1)(1) exactly when b_(k+2) = b_(k+1); with d^-(v_i) = i - b_i this turns the
  merged singleton criterion into both corrected equivalences; and no_two_flat (2/phi > 1),
  which makes d^-(v_k) = d^-(v_(k+1)) a consequence of d^-(v_(k+2)) = d^-(v_(k+1)) + 1.
admission_basis: escape-witness
-/

open D5.S0.Certificates.JacoExponentialDominationRefutation
open D5.S3.ConceptDynamics.GraphColoring.JacoDomPathDiameterRefutation
open D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty
open D5.S3.ConceptDynamics.GraphColoring.JacoAdditionLaw
open D5.S3.ConceptDynamics.GraphColoring.JacoMaximumDegree
open D5.S3.ConceptDynamics.GraphColoring.JacoMaximumSet
open D5.S3.ConceptDynamics.GraphColoring.JacoTripleMaximizers (g_pos g_quad bo_le bo_zero)
open D5.S3.ConceptDynamics.GraphColoring.JacoDirectedPathCount (out_step)

/-- The indegree `d⁻(v_i) = a_i = i - b_i` of `v_i` in the infinite Jaco graph. -/
noncomputable def indeg (i : ℕ) : ℕ := i - beattyOut i

private theorem bo_step2 (k : ℕ) :
    beattyOut (k + 2) = beattyOut (k + 1) ∨ beattyOut (k + 2) = beattyOut (k + 1) + 1 :=
  out_step (k + 1)

/-- The outdegree sequence has no two consecutive zero steps. -/
private theorem no_two_flat (k : ℕ) (h : beattyOut (k + 2) = beattyOut (k + 1)) :
    beattyOut (k + 1) = beattyOut k + 1 := by
  rcases out_step k with h0 | h0
  · exfalso
    have hl := (bo_le k).1
    have hu := (bo_le (k + 2)).2
    have hq := g_quad
    have hg := g_pos
    have heq : (beattyOut (k + 2) : ℝ) = beattyOut k := by rw [h, h0]
    push_cast at hu
    nlinarith
  · exact h0

/-- `d⁻(v_k) = d⁻(v_(k+1))` exactly when `b_(k+1) = b_k + 1`. -/
private theorem indeg_eq_iff (k : ℕ) :
    indeg k = indeg (k + 1) ↔ beattyOut (k + 1) = beattyOut k + 1 := by
  have hb : beattyOut k ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [bo_zero]
    · exact (beatty_bounds k hk).2
  unfold indeg
  rcases out_step k with h | h <;> rw [h] <;> omega

/-- For `n ≥ 2` the least maximum-degree label is `Δ_n`. -/
private theorem prime_eq (n k : ℕ) (hn : 2 ≤ n) (hk : k ∈ jaconian n)
    (hmin : ∀ i ∈ jaconian n, k ≤ i) : k = (jaco n).maxDegree := by
  obtain ⟨-, hset, -, -⟩ := JacoMaximumSet.result
  rw [(hset n hn).2.1] at hk hmin
  have hk' := Finset.mem_Icc.mp hk
  have := hmin (jaco n).maxDegree (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
  omega

private theorem mem_jaconian_iff (m i : ℕ) (hi : i ∈ Finset.Icc 1 m) :
    i ∈ jaconian m ↔ (jaco m).degree ⟨i, hi⟩ = (jaco m).maxDegree := by
  constructor
  · intro h
    obtain ⟨v, hv, hvi⟩ := Finset.mem_map.mp h
    have hd := (Finset.mem_filter.mp hv).2
    have hv' : v = ⟨i, hi⟩ := Subtype.ext hvi
    rw [hv'] at hd
    exact hd
  · intro h
    exact Finset.mem_map.mpr ⟨⟨i, hi⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩

/-- After a singleton maximum set `{v_k}` at `n`, the label `k + 2` is maximum at `n + 1`
exactly when `b_(k+2) = b_(k+1)`. -/
private theorem next_set (n k : ℕ) (hn : 2 ≤ n) (hk : (jaco n).maxDegree = k)
    (hJ : jaconian n = {k}) :
    (jaconian (n + 1) = Finset.Icc k (k + 2) ↔ beattyOut (k + 2) = beattyOut (k + 1)) ∧
      (jaconian (n + 1) = Finset.Icc k (k + 1) ↔
        beattyOut (k + 2) = beattyOut (k + 1) + 1) := by
  obtain ⟨-, hset, hsing, hnext⟩ := JacoMaximumSet.result
  have hJ' : jaconian n = {(jaco n).maxDegree} := by rw [hk]; exact hJ
  have hcrit := ((hsing n hn).2.1).mp hJ'
  have hsame := ((hsing n hn).2.2.2).mp hJ'
  have hnx := (hnext n hn hJ').2.2.2
  rw [hk] at hcrit hsame hnx
  have hRk : n = k + beattyOut k := by rw [← endpoint_eq_beatty]; exact hcrit.1
  have hb1 : beattyOut (k + 1) = beattyOut k + 1 := hcrit.2
  have hk1 : 1 ≤ k := by
    by_contra h0
    have hk0 : k = 0 := by omega
    rw [hk0, bo_zero] at hRk
    omega
  have hle : k + 2 ≤ n + 1 := by have := (beatty_bounds k hk1).1; omega
  have hv : k + 2 ∈ Finset.Icc 1 (n + 1) := Finset.mem_Icc.mpr ⟨by omega, hle⟩
  have hdeg : (jaco (n + 1)).degree ⟨k + 2, hv⟩ = min (k + 2) (n + 1 - beattyOut (k + 2)) :=
    degree_formula (n + 1) ⟨k + 2, hv⟩
  have hmem : k + 2 ∈ jaconian (n + 1) ↔ beattyOut (k + 2) = beattyOut (k + 1) := by
    rw [mem_jaconian_iff (n + 1) (k + 2) hv, hdeg, hsame]
    rcases bo_step2 k with h | h
    · rw [h]; constructor <;> intro _ <;> omega
    · rw [h]; constructor <;> intro hh <;> omega
  have h3 : k + 2 ∈ Finset.Icc k (k + 2) := Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
  have h2 : k + 2 ∉ Finset.Icc k (k + 1) := by simp
  have hne : Finset.Icc k (k + 2) ≠ Finset.Icc k (k + 1) := fun h => h2 (h ▸ h3)
  rcases bo_step2 k with hs | hs
  · have hin := hmem.mpr hs
    have hJ2 : jaconian (n + 1) = Finset.Icc k (k + 2) := by
      rcases hnx with h | h
      · rw [h] at hin; exact absurd hin h2
      · exact h
    refine ⟨⟨fun _ => hs, fun _ => hJ2⟩, ⟨fun h => absurd (hJ2.symm.trans h) hne, fun h => by omega⟩⟩
  · have hnin : k + 2 ∉ jaconian (n + 1) := fun h => by have := hmem.mp h; omega
    have hJ2 : jaconian (n + 1) = Finset.Icc k (k + 1) := by
      rcases hnx with h | h
      · exact h
      · rw [h] at hnin; exact absurd h3 hnin
    refine ⟨⟨fun h => absurd (h.symm.trans hJ2) hne, fun h => by omega⟩, ⟨fun _ => hs, fun _ => hJ2⟩⟩

private theorem icc_three (k : ℕ) : Finset.Icc k (k + 2) = {k, k + 1, k + 2} := by
  ext i; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega

private theorem icc_two (k : ℕ) : Finset.Icc k (k + 1) = {k, k + 1} := by
  ext i; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega

/-- The corrected equivalences, with `n = R_k` added on the left. -/
private theorem corrected (n k : ℕ) (hn : 2 ≤ n) (hk : k ∈ jaconian n)
    (hmin : ∀ i ∈ jaconian n, k ≤ i) :
    ((n = jacoRight k ∧ indeg k = indeg (k + 1) ∧ indeg (k + 2) = indeg (k + 1) + 1) ↔
        (jaconian n = {k} ∧ jaconian (n + 1) = {k, k + 1, k + 2})) ∧
      ((n = jacoRight k ∧ indeg k = indeg (k + 1) ∧ indeg (k + 1) = indeg (k + 2)) ↔
        (jaconian n = {k} ∧ jaconian (n + 1) = {k, k + 1})) := by
  obtain ⟨-, -, hsing, -⟩ := JacoMaximumSet.result
  have hkeq := prime_eq n k hn hk hmin
  have hi1 := indeg_eq_iff (k + 1)
  have hi0 := indeg_eq_iff k
  have hstep := bo_step2 k
  have hplus : indeg (k + 2) = indeg (k + 1) + 1 ↔ beattyOut (k + 2) = beattyOut (k + 1) := by
    unfold indeg
    have hb : beattyOut (k + 1) ≤ k + 1 := (beatty_bounds (k + 1) (by omega)).2
    rcases hstep with h | h <;> rw [h] <;> omega
  have hsingk : jaconian n = {k} ↔ n = jacoRight k ∧ beattyOut (k + 1) = beattyOut k + 1 := by
    rw [hkeq]; exact (hsing n hn).2.1
  constructor
  · constructor
    · rintro ⟨hR, h0, h2⟩
      have hJ : jaconian n = {k} := hsingk.mpr ⟨hR, hi0.mp h0⟩
      have hn3 := (next_set n k hn hkeq.symm hJ).1
      exact ⟨hJ, by rw [← icc_three]; exact hn3.mpr (hplus.mp h2)⟩
    · rintro ⟨hJ, hJ1⟩
      obtain ⟨hR, hb⟩ := hsingk.mp hJ
      have hn3 := (next_set n k hn hkeq.symm hJ).1
      rw [icc_three] at hn3
      exact ⟨hR, hi0.mpr hb, hplus.mpr (hn3.mp hJ1)⟩
  · constructor
    · rintro ⟨hR, h0, h2⟩
      have hJ : jaconian n = {k} := hsingk.mpr ⟨hR, hi0.mp h0⟩
      have hn2 := (next_set n k hn hkeq.symm hJ).2
      exact ⟨hJ, by rw [← icc_two]; exact hn2.mpr (hi1.mp h2)⟩
    · rintro ⟨hJ, hJ1⟩
      obtain ⟨hR, hb⟩ := hsingk.mp hJ
      have hn2 := (next_set n k hn hkeq.symm hJ).2
      rw [icc_two] at hn2
      exact ⟨hR, hi0.mpr hb, hi1.mpr (hn2.mp hJ1)⟩

/-- Morrie's theorem with `n = R_k` added to each left-hand condition: for `n ≥ 2` and the
prime (least) maximum-degree label `k` of `J_n(1)`, with `d⁻(v_i) = i - b_i`,
(a) `n = R_k`, `d⁻(v_k) = d⁻(v_(k+1))` and `d⁻(v_(k+2)) = d⁻(v_(k+1)) + 1` iff
`J_n = {v_k}` and `J_(n+1) = {v_k, v_(k+1), v_(k+2)}`, and already `n = R_k` with
`d⁻(v_(k+2)) = d⁻(v_(k+1)) + 1` is equivalent to the same conclusion;
(b) `n = R_k` and `d⁻(v_k) = d⁻(v_(k+1)) = d⁻(v_(k+2))` iff `J_n = {v_k}` and
`J_(n+1) = {v_k, v_(k+1)}`. -/
theorem result :
    ∀ n k, 2 ≤ n → k ∈ jaconian n → (∀ i ∈ jaconian n, k ≤ i) →
      ((n = jacoRight k ∧ indeg k = indeg (k + 1) ∧ indeg (k + 2) = indeg (k + 1) + 1) ↔
          (jaconian n = {k} ∧ jaconian (n + 1) = {k, k + 1, k + 2})) ∧
        ((n = jacoRight k ∧ indeg (k + 2) = indeg (k + 1) + 1) ↔
          (jaconian n = {k} ∧ jaconian (n + 1) = {k, k + 1, k + 2})) ∧
        ((n = jacoRight k ∧ indeg k = indeg (k + 1) ∧ indeg (k + 1) = indeg (k + 2)) ↔
          (jaconian n = {k} ∧ jaconian (n + 1) = {k, k + 1})) := by
  intro n k hn hk hmin
  obtain ⟨ha, hb⟩ := corrected n k hn hk hmin
  have hplus : indeg (k + 2) = indeg (k + 1) + 1 → indeg k = indeg (k + 1) := by
    intro h
    have hb1 : beattyOut (k + 1) ≤ k + 1 := (beatty_bounds (k + 1) (by omega)).2
    have h2 : beattyOut (k + 2) = beattyOut (k + 1) := by
      unfold indeg at h
      rcases bo_step2 k with h' | h'
      · exact h'
      · rw [h'] at h; omega
    exact (indeg_eq_iff k).mpr (no_two_flat k h2)
  refine ⟨ha, ?_, hb⟩
  rw [← ha]
  exact ⟨fun ⟨hR, h2⟩ => ⟨hR, hplus h2, h2⟩, fun ⟨hR, _, h2⟩ => ⟨hR, h2⟩⟩

#print axioms result

end D5.S3.ConceptDynamics.GraphColoring.JacoMorrieTheorem
