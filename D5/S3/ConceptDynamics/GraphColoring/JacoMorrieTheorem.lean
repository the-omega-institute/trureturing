/- GID: D5/S3/ConceptDynamics/GraphColoring/JacoMorrieTheorem
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/GraphColoring/JacoMorrieTheorem
   mirror-E: none(waiver:structural-proof)
   anchors: [lake/module/D5.S3.ConceptDynamics.GraphColoring.JacoMaximumSet, lake/module/D5.S3.ConceptDynamics.GraphColoring.JacoMaximumDegree]
   utility: none
   digest: Morrie's theorem on finite Jaco graphs holds once n = R_k is added to its indegree conditions, and fails without it at n = 6 and n = 4. -/

import D5.S3.ConceptDynamics.GraphColoring.JacoMaximumSet
import D5.S3.ConceptDynamics.GraphColoring.JacoMaximumDegree

/-! The corrected form of Morrie's theorem for the finite linear Jaco graphs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.GraphColoring.JacoMorrieTheorem

/-
proof_shape:
  indeg: definition
  g_pos: bind-only (consumers: g_fine, bo_eq_iff, bo_step)
  g_quad: bind-only (consumer: g_fine)
  g_fine: bind-only (consumers: bo_step, indeg_eq_iff, next_set, bo_val, maxDegree_val)
  bo_eq_iff, bo_step, bo_step2: bind-only (consumers: indeg_eq_iff, next_set, corrected, bo_val)
  mem_jaconian_iff: bind-only (consumer: next_set)
  icc_three, icc_two: bind-only (consumer: corrected)
  prime_eq, prime_mem: bind-only (consumers: corrected, counter_six, counter_four)
  bo_val, maxDegree_val: bind-only (consumers: counter_six, counter_four)
  indeg_eq_iff: content (consumer: corrected)
  next_set: content (consumer: corrected)
  corrected: content (consumer: result)
  counter_six, counter_four: content (consumer: result)
  result: content
direct frozen dependencies:
  D5/S3/ConceptDynamics/GraphColoring/JacoMaximumSet.result (statement_id
    sha256:d31cfe56216a7368dfd3700d57fd0f68ca52816f38e6d48739b538a93e32a20f)
  D5/S3/ConceptDynamics/GraphColoring/JacoMaximumDegree.degree_formula (statement_id
    sha256:0e86e1b7bcb5cf4a23c8cf5390ae207b2bcf9fd946fd97d2badc1c1cb672c72d)
  D5/S3/ConceptDynamics/GraphColoring/JacoEndpointBeatty.endpoint_eq_beatty, beatty_bounds
    (statement_id sha256:15f9f8627a73d9d28232ecd5a1deb1d41054ab6114f152475628df4fd9def028)
  D5/S3/ConceptDynamics/GraphColoring/JacoAdditionLaw.delta_eq_floor (statement_id
    sha256:289669fd9ce5e9c638eb5eb4c27e641b00d3b68fa3cf9720a425b277073d78ff)
escape_witness: by the degree formula deg(v_i) = min(i, n + 1 - b_i) at order n + 1, after a
  singleton maximum set {v_k} at n = R_k = k + b_k the label k + 2 is a maximizer of
  J_(n+1)(1) exactly when b_(k+2) = b_(k+1); with d^-(v_i) = i - b_i this turns the
  merged singleton criterion into both corrected equivalences.
admission_basis: escape-witness
-/

open D5.S0.Certificates.JacoExponentialDominationRefutation
open D5.S3.ConceptDynamics.GraphColoring.JacoDomPathDiameterRefutation
open D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty
open D5.S3.ConceptDynamics.GraphColoring.JacoAdditionLaw
open D5.S3.ConceptDynamics.GraphColoring.JacoMaximumDegree
open D5.S3.ConceptDynamics.GraphColoring.JacoMaximumSet

/-- The indegree `d⁻(v_i) = a_i = i - b_i` of `v_i` in the infinite Jaco graph. -/
noncomputable def indeg (i : ℕ) : ℕ := i - beattyOut i

private theorem g_pos : 0 < Real.goldenRatio⁻¹ := inv_pos.mpr Real.goldenRatio_pos

private theorem g_quad : Real.goldenRatio⁻¹ ^ 2 + Real.goldenRatio⁻¹ = 1 := by
  rw [Real.inv_goldenRatio, neg_sq, Real.goldenConj_sq]; ring

private theorem g_fine : (618 : ℝ) / 1000 < Real.goldenRatio⁻¹ ∧ Real.goldenRatio⁻¹ < 619 / 1000 := by
  have hq := g_quad
  have hg0 := g_pos
  constructor <;> nlinarith

private theorem bo_eq_iff (k N : ℕ) :
    beattyOut k = N ↔
      (N : ℝ) ≤ ((k : ℝ) + 1) * Real.goldenRatio⁻¹ ∧
        ((k : ℝ) + 1) * Real.goldenRatio⁻¹ < N + 1 := by
  have hpos : (0 : ℝ) ≤ ((k : ℝ) + 1) * Real.goldenRatio⁻¹ := by have := g_pos; positivity
  rw [beattyOut, ← div_eq_mul_inv]
  rw [← div_eq_mul_inv] at hpos
  exact Nat.floor_eq_iff hpos

/-- Consecutive outdegrees differ by zero or one. -/
private theorem bo_step (k : ℕ) :
    beattyOut (k + 1) = beattyOut k ∨ beattyOut (k + 1) = beattyOut k + 1 := by
  have hpos : (0 : ℝ) ≤ ((k : ℝ) + 1) * Real.goldenRatio⁻¹ := by have := g_pos; positivity
  have h1 : (beattyOut k : ℝ) ≤ ((k : ℝ) + 1) * Real.goldenRatio⁻¹ := by
    rw [beattyOut, ← div_eq_mul_inv]; exact Nat.floor_le (by rw [div_eq_mul_inv]; exact hpos)
  have h2 : ((k : ℝ) + 1) * Real.goldenRatio⁻¹ < beattyOut k + 1 := by
    rw [beattyOut, ← div_eq_mul_inv]; exact Nat.lt_floor_add_one _
  have hg := g_fine
  rcases lt_or_ge (((k : ℝ) + 2) * Real.goldenRatio⁻¹) (beattyOut k + 1) with h | h
  · left; rw [bo_eq_iff]; push_cast; constructor <;> nlinarith
  · right; rw [bo_eq_iff]; push_cast; constructor <;> nlinarith

private theorem bo_step2 (k : ℕ) :
    beattyOut (k + 2) = beattyOut (k + 1) ∨ beattyOut (k + 2) = beattyOut (k + 1) + 1 :=
  bo_step (k + 1)

/-- `d⁻(v_k) = d⁻(v_(k+1))` exactly when `b_(k+1) = b_k + 1`. -/
private theorem indeg_eq_iff (k : ℕ) :
    indeg k = indeg (k + 1) ↔ beattyOut (k + 1) = beattyOut k + 1 := by
  have hb : beattyOut k ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [show beattyOut 0 = 0 from (bo_eq_iff 0 0).mpr (by have := g_fine; push_cast; constructor <;> linarith)]
    · exact (beatty_bounds k hk).2
  unfold indeg
  rcases bo_step k with h | h <;> rw [h] <;> omega

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
    have hb0 : beattyOut 0 = 0 :=
      (bo_eq_iff 0 0).mpr (by have := g_fine; push_cast; constructor <;> linarith)
    rw [hk0, hb0] at hRk
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

/-- Concrete outdegrees used by the counterexamples. -/
private theorem bo_val (k N : ℕ) (hlo : (N : ℝ) ≤ ((k : ℝ) + 1) * (618 / 1000))
    (hhi : ((k : ℝ) + 1) * (619 / 1000) < N + 1) : beattyOut k = N := by
  have hg := g_fine
  rw [bo_eq_iff]
  constructor <;> nlinarith

/-- The least maximum-degree label of `J_n` is `Δ_n`, and it lies in `J_n`. -/
private theorem prime_mem (n : ℕ) (hn : 2 ≤ n) :
    (jaco n).maxDegree ∈ jaconian n ∧ ∀ i ∈ jaconian n, (jaco n).maxDegree ≤ i := by
  obtain ⟨-, hset, -, -⟩ := JacoMaximumSet.result
  have hne : (jaconian n).Nonempty := by
    rw [← Finset.card_pos]; rcases (hset n hn).2.2.2 with h | h | h <;> omega
  rw [(hset n hn).2.1] at hne ⊢
  exact ⟨Finset.mem_Icc.mpr ⟨le_rfl, Finset.nonempty_Icc.mp hne⟩,
    fun i hi => (Finset.mem_Icc.mp hi).1⟩

private theorem maxDegree_val (n p : ℕ)
    (hlo : ((p : ℝ) + 1) ≤ ((n : ℝ) + 2) * (618 / 1000))
    (hhi : ((n : ℝ) + 2) * (619 / 1000) < p + 2) : (jaco n).maxDegree = p := by
  have hd := delta_eq_floor n
  have hg := g_fine
  have hf : ⌊((n : ℝ) + 2) / Real.goldenRatio⌋ = p + 1 := by
    rw [Int.floor_eq_iff, div_eq_mul_inv]; push_cast; constructor <;> nlinarith
  rw [delta, hf] at hd
  omega

/-- The unqualified part (a) fails at `n = 6`, `k = 3`. -/
private theorem counter_six :
    ¬ ∀ n k, 2 ≤ n → k ∈ jaconian n → (∀ i ∈ jaconian n, k ≤ i) →
      ((indeg k = indeg (k + 1) ∧ indeg (k + 2) = indeg (k + 1) + 1) ↔
        (jaconian n = {k} ∧ jaconian (n + 1) = {k, k + 1, k + 2})) := by
  intro h
  have hd : (jaco 6).maxDegree = 3 := maxDegree_val 6 3 (by norm_num) (by norm_num)
  obtain ⟨hmem, hmin⟩ := prime_mem 6 (by omega)
  rw [hd] at hmem hmin
  have h3 := bo_val 3 2 (by norm_num) (by norm_num)
  have h4 := bo_val 4 3 (by norm_num) (by norm_num)
  have h5 := bo_val 5 3 (by norm_num) (by norm_num)
  obtain ⟨-, -, hsing, -⟩ := JacoMaximumSet.result
  have hs := ((hsing 6 (by omega)).2.1)
  rw [hd, endpoint_eq_beatty, h3] at hs
  have hcond : indeg 3 = indeg (3 + 1) ∧ indeg (3 + 2) = indeg (3 + 1) + 1 := by
    show indeg 3 = indeg 4 ∧ indeg 5 = indeg 4 + 1
    unfold indeg
    rw [h3, h4, h5]
    omega
  have := ((h 6 3 (by omega) hmem hmin).mp hcond).1
  have := hs.mp this
  omega

/-- The unqualified part (b) fails at `n = 4`, `k = 2`. -/
private theorem counter_four :
    ¬ ∀ n k, 2 ≤ n → k ∈ jaconian n → (∀ i ∈ jaconian n, k ≤ i) →
      ((indeg k = indeg (k + 1) ∧ indeg (k + 1) = indeg (k + 2)) ↔
        (jaconian n = {k} ∧ jaconian (n + 1) = {k, k + 1})) := by
  intro h
  have hd : (jaco 4).maxDegree = 2 := maxDegree_val 4 2 (by norm_num) (by norm_num)
  obtain ⟨hmem, hmin⟩ := prime_mem 4 (by omega)
  rw [hd] at hmem hmin
  have h2 := bo_val 2 1 (by norm_num) (by norm_num)
  have h3 := bo_val 3 2 (by norm_num) (by norm_num)
  have h4 := bo_val 4 3 (by norm_num) (by norm_num)
  obtain ⟨-, -, hsing, -⟩ := JacoMaximumSet.result
  have hs := ((hsing 4 (by omega)).2.1)
  rw [hd, endpoint_eq_beatty, h2] at hs
  have hcond : indeg 2 = indeg (2 + 1) ∧ indeg (2 + 1) = indeg (2 + 2) := by
    show indeg 2 = indeg 3 ∧ indeg 3 = indeg 4
    unfold indeg
    rw [h2, h3, h4]
    omega
  have := ((h 4 2 (by omega) hmem hmin).mp hcond).1
  have := hs.mp this
  omega

/-- Morrie's theorem with `n = R_k` added to each left-hand condition: for `n ≥ 2` and the
prime (least) maximum-degree label `k` of `J_n(1)`, with `d⁻(v_i) = i - b_i`,
(a) `n = R_k`, `d⁻(v_k) = d⁻(v_(k+1))` and `d⁻(v_(k+2)) = d⁻(v_(k+1)) + 1` iff
`J_n = {v_k}` and `J_(n+1) = {v_k, v_(k+1), v_(k+2)}`;
(b) `n = R_k` and `d⁻(v_k) = d⁻(v_(k+1)) = d⁻(v_(k+2))` iff `J_n = {v_k}` and
`J_(n+1) = {v_k, v_(k+1)}`. Without `n = R_k`, (a) fails at `n = 6` and (b) at `n = 4`. -/
theorem result :
    (∀ n k, 2 ≤ n → k ∈ jaconian n → (∀ i ∈ jaconian n, k ≤ i) →
      ((n = jacoRight k ∧ indeg k = indeg (k + 1) ∧ indeg (k + 2) = indeg (k + 1) + 1) ↔
          (jaconian n = {k} ∧ jaconian (n + 1) = {k, k + 1, k + 2})) ∧
        ((n = jacoRight k ∧ indeg k = indeg (k + 1) ∧ indeg (k + 1) = indeg (k + 2)) ↔
          (jaconian n = {k} ∧ jaconian (n + 1) = {k, k + 1}))) ∧
    (¬ ∀ n k, 2 ≤ n → k ∈ jaconian n → (∀ i ∈ jaconian n, k ≤ i) →
      ((indeg k = indeg (k + 1) ∧ indeg (k + 2) = indeg (k + 1) + 1) ↔
        (jaconian n = {k} ∧ jaconian (n + 1) = {k, k + 1, k + 2}))) ∧
    (¬ ∀ n k, 2 ≤ n → k ∈ jaconian n → (∀ i ∈ jaconian n, k ≤ i) →
      ((indeg k = indeg (k + 1) ∧ indeg (k + 1) = indeg (k + 2)) ↔
        (jaconian n = {k} ∧ jaconian (n + 1) = {k, k + 1}))) :=
  ⟨corrected, counter_six, counter_four⟩

#print axioms result

end D5.S3.ConceptDynamics.GraphColoring.JacoMorrieTheorem
