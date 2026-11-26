/- GID: D5/S3/ConceptDynamics/GraphColoring/JacoMorrieTheoremRefutation
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/GraphColoring/JacoMorrieTheoremRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [lake/module/D5.S3.ConceptDynamics.GraphColoring.JacoMorrieTheorem]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ConceptDynamics/GraphColoring/JacoMorrieTheoremRefutation.claim; result=D5/S3/ConceptDynamics/GraphColoring/JacoMorrieTheoremRefutation.result; claim=D5/S3/ConceptDynamics/GraphColoring/JacoMorrieTheoremRefutation.claim
   digest: Each part of Morrie's theorem on finite Jaco graphs fails as stated: part (a) at n = 6 and part (b) at n = 4. -/

import D5.S3.ConceptDynamics.GraphColoring.JacoMorrieTheorem

/-! Refutation of Morrie's theorem (Theorem 2.3 of arXiv:1404.0484v1) as stated. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.GraphColoring.JacoMorrieTheoremRefutation

/-
proof_shape:
  claim: definition
  g_fine: bind-only (consumers: bo_val, maxDegree_val)
  bo_val, maxDegree_val, prime_mem: bind-only (consumer: result)
  result: content (certified refutation; witnesses n = 6, k = 3 for part (a) and n = 4, k = 2
    for part (b))
direct frozen dependencies:
  D5/S3/ConceptDynamics/GraphColoring/JacoMaximumSet.result (statement_id
    sha256:d31cfe56216a7368dfd3700d57fd0f68ca52816f38e6d48739b538a93e32a20f)
  D5/S3/ConceptDynamics/GraphColoring/JacoAdditionLaw.delta_eq_floor (statement_id
    sha256:289669fd9ce5e9c638eb5eb4c27e641b00d3b68fa3cf9720a425b277073d78ff)
  D5/S3/ConceptDynamics/GraphColoring/JacoEndpointBeatty.endpoint_eq_beatty (statement_id
    sha256:15f9f8627a73d9d28232ecd5a1deb1d41054ab6114f152475628df4fd9def028)
  D5/S3/ConceptDynamics/GraphColoring/JacoTripleMaximizers.g_pos, g_quad, bo_eq_iff
    (statement_id sha256:9eb0c30e4bc66cb8afb1eb6f9c71517c9be6c29aae118e2ab59e200b54844d07)
escape_witness: the concrete outdegrees b_2..b_5 = 1, 2, 3, 3 and maximum degrees
  Delta_4 = 2, Delta_6 = 3, read from (k + 1)/phi and (n + 2)/phi with 0.618 < 1/phi < 0.619,
  against the singleton criterion J_n = {Delta_n} iff n = R_(Delta_n) and b_(Delta_n + 1) =
  b_(Delta_n) + 1 with R_3 = 5 and R_2 = 3.
admission_basis: escape-witness
-/

open D5.S0.Certificates.JacoExponentialDominationRefutation
open D5.S3.ConceptDynamics.GraphColoring.JacoDomPathDiameterRefutation
open D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty
open D5.S3.ConceptDynamics.GraphColoring.JacoAdditionLaw
open D5.S3.ConceptDynamics.GraphColoring.JacoMaximumSet
open D5.S3.ConceptDynamics.GraphColoring.JacoMorrieTheorem (indeg)

/-- Theorem 2.3 (Morrie's Theorem) of arXiv:1404.0484v1 as stated, part (a) or part (b): for
every `n ≥ 2` and prime (least) maximum-degree label `k` of `J_n(1)`, the indegree conditions
alone are equivalent to the asserted maximum sets at `n` and `n + 1`. -/
def claim : Prop :=
  (∀ n k, 2 ≤ n → k ∈ jaconian n → (∀ i ∈ jaconian n, k ≤ i) →
    ((indeg k = indeg (k + 1) ∧ indeg (k + 2) = indeg (k + 1) + 1) ↔
      (jaconian n = {k} ∧ jaconian (n + 1) = {k, k + 1, k + 2}))) ∨
  (∀ n k, 2 ≤ n → k ∈ jaconian n → (∀ i ∈ jaconian n, k ≤ i) →
    ((indeg k = indeg (k + 1) ∧ indeg (k + 1) = indeg (k + 2)) ↔
      (jaconian n = {k} ∧ jaconian (n + 1) = {k, k + 1})))

private theorem g_fine :
    (618 : ℝ) / 1000 < Real.goldenRatio⁻¹ ∧ Real.goldenRatio⁻¹ < 619 / 1000 := by
  have hq := JacoTripleMaximizers.g_quad
  have hg0 := JacoTripleMaximizers.g_pos
  constructor <;> nlinarith

private theorem bo_val (k N : ℕ) (hlo : (N : ℝ) ≤ ((k : ℝ) + 1) * (618 / 1000))
    (hhi : ((k : ℝ) + 1) * (619 / 1000) < N + 1) : beattyOut k = N := by
  have hg := g_fine
  rw [JacoTripleMaximizers.bo_eq_iff]
  constructor <;> nlinarith

private theorem maxDegree_val (n p : ℕ)
    (hlo : ((p : ℝ) + 1) ≤ ((n : ℝ) + 2) * (618 / 1000))
    (hhi : ((n : ℝ) + 2) * (619 / 1000) < p + 2) : (jaco n).maxDegree = p := by
  have hd := delta_eq_floor n
  have hg := g_fine
  have hf : ⌊((n : ℝ) + 2) / Real.goldenRatio⌋ = p + 1 := by
    rw [Int.floor_eq_iff, div_eq_mul_inv]; push_cast; constructor <;> nlinarith
  rw [delta, hf] at hd
  omega

/-- `Δ_n` lies in `J_n` and is its least element. -/
private theorem prime_mem (n : ℕ) (hn : 2 ≤ n) :
    (jaco n).maxDegree ∈ jaconian n ∧ ∀ i ∈ jaconian n, (jaco n).maxDegree ≤ i := by
  obtain ⟨-, hset, -, -⟩ := JacoMaximumSet.result
  have hne : (jaconian n).Nonempty := by
    rw [← Finset.card_pos]; rcases (hset n hn).2.2.2 with h | h | h <;> omega
  rw [(hset n hn).2.1] at hne ⊢
  exact ⟨Finset.mem_Icc.mpr ⟨le_rfl, Finset.nonempty_Icc.mp hne⟩,
    fun i hi => (Finset.mem_Icc.mp hi).1⟩

/-- Neither part holds: at `n = 6`, `k = 3` the indegrees `1, 1, 2` satisfy (a) while
`J_6 ≠ {3}` because `R_3 = 5`; at `n = 4`, `k = 2` the indegrees `1, 1, 1` satisfy (b) while
`J_4 ≠ {2}` because `R_2 = 3`. -/
theorem result : ¬ claim := by
  obtain ⟨-, -, hsing, -⟩ := JacoMaximumSet.result
  have h2 := bo_val 2 1 (by norm_num) (by norm_num)
  have h3 := bo_val 3 2 (by norm_num) (by norm_num)
  have h4 := bo_val 4 3 (by norm_num) (by norm_num)
  have h5 := bo_val 5 3 (by norm_num) (by norm_num)
  rintro (h | h)
  · have hd : (jaco 6).maxDegree = 3 := maxDegree_val 6 3 (by norm_num) (by norm_num)
    obtain ⟨hmem, hmin⟩ := prime_mem 6 (by omega)
    rw [hd] at hmem hmin
    have hs := (hsing 6 (by omega)).2.1
    rw [hd, endpoint_eq_beatty, h3] at hs
    have hcond : indeg 3 = indeg (3 + 1) ∧ indeg (3 + 2) = indeg (3 + 1) + 1 := by
      show indeg 3 = indeg 4 ∧ indeg 5 = indeg 4 + 1
      unfold indeg
      rw [h3, h4, h5]
      omega
    have := ((h 6 3 (by omega) hmem hmin).mp hcond).1
    have := hs.mp this
    omega
  · have hd : (jaco 4).maxDegree = 2 := maxDegree_val 4 2 (by norm_num) (by norm_num)
    obtain ⟨hmem, hmin⟩ := prime_mem 4 (by omega)
    rw [hd] at hmem hmin
    have hs := (hsing 4 (by omega)).2.1
    rw [hd, endpoint_eq_beatty, h2] at hs
    have hcond : indeg 2 = indeg (2 + 1) ∧ indeg (2 + 1) = indeg (2 + 2) := by
      show indeg 2 = indeg 3 ∧ indeg 3 = indeg 4
      unfold indeg
      rw [h2, h3, h4]
      omega
    have := ((h 4 2 (by omega) hmem hmin).mp hcond).1
    have := hs.mp this
    omega

#print axioms result

end D5.S3.ConceptDynamics.GraphColoring.JacoMorrieTheoremRefutation
