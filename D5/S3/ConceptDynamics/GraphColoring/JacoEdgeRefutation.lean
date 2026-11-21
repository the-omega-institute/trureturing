/- GID: D5/S3/ConceptDynamics/GraphColoring/JacoEdgeRefutation
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/GraphColoring/JacoEdgeRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [lake/module/D5.S3.ConceptDynamics.GraphColoring.JacoDegreeShift]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ConceptDynamics/GraphColoring/JacoEdgeRefutation.claim; result=D5/S3/ConceptDynamics/GraphColoring/JacoEdgeRefutation.result; claim=D5/S3/ConceptDynamics/GraphColoring/JacoEdgeRefutation.claim
   digest: The edge v_Delta v_n exists exactly when Delta_n = b_n; the edge clause of Kok's Theorem 2.15 fails at order nineteen. -/

import D5.S3.ConceptDynamics.GraphColoring.JacoDegreeShift

/-! The maximum-degree vertex and the last vertex of a finite linear Jaco graph. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.GraphColoring.JacoEdgeRefutation

/-
proof_shape:
  out_succ: bind-only (consumer: edge_iff)
  edge_iff: content
  bound: content
  claim: definition
  result: content (consumer of edge_iff)
escape_witness: R_Delta <= n from the Beatty threshold at n + 1 and b_(n+1) = Delta_n + 1, and
  the edge criterion n <= R_Delta iff b_n <= Delta_n, which with Delta_n in {b_n - 1, b_n}
  pins the edge to Delta_n = b_n; the order-nineteen value Delta_19 = 11 and R_11 = 18 then
  falsify the claim.
admission_basis: escape-witness
-/

open D5.S0.Certificates.JacoExponentialDominationRefutation
open D5.S3.ConceptDynamics.GraphColoring.JacoDomPathDiameterRefutation
open D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty
open D5.S3.ConceptDynamics.GraphColoring.JacoAdditionLaw

private theorem out_succ (n : ℕ) :
    (beattyOut (n + 1) : ℤ) = (jaco n).maxDegree + 1 := by
  have h := delta_eq_floor n
  have hpos : (0 : ℝ) ≤ (((n + 1 : ℕ) : ℝ) + 1) / Real.goldenRatio := by
    have := Real.goldenRatio_pos; positivity
  rw [beattyOut, Int.natCast_floor_eq_floor hpos, delta] at *
  have : (((n + 1 : ℕ) : ℝ) + 1) = (n : ℝ) + 2 := by push_cast; ring
  rw [this]
  omega

/-- For every positive order, the vertex `v_Δ` is joined to the last vertex `v_n`
exactly when `n = R_Δ`, exactly when `Δ_n = b_n`, and exactly when the golden fractional
part of `(n + 2) / φ` lies below `1 / φ`; moreover `R_Δ ≤ n` always. -/
theorem edge_iff (n : ℕ) (hn : 1 ≤ n) :
    jacoRight (jaco n).maxDegree ≤ n ∧
    (Adj (jaco n).maxDegree n ↔ n = jacoRight (jaco n).maxDegree) ∧
    (Adj (jaco n).maxDegree n ↔ (jaco n).maxDegree = beattyOut n) ∧
    (Adj (jaco n).maxDegree n ↔ frac n < Real.goldenRatio⁻¹) := by
  set P := (jaco n).maxDegree with hP
  have hs := out_succ n
  have hb1 : beattyOut (n + 1) < n + 1 := by
    have hlo : (8 : ℝ) / 5 < Real.goldenRatio := by
      rw [Real.goldenRatio]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
    have hpos : (0 : ℝ) ≤ (((n + 1 : ℕ) : ℝ) + 1) / Real.goldenRatio := by
      have := Real.goldenRatio_pos; positivity
    apply (Nat.floor_lt hpos).mpr
    rw [div_lt_iff₀ Real.goldenRatio_pos]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    push_cast
    nlinarith
  have hPn : P < n := by omega
  -- R_P ≤ n, since n + 1 ≤ R_P would force b_(n+1) ≤ P
  have hR : jacoRight P ≤ n := by
    by_contra h
    have := (beatty_threshold (n + 1) P).mp (by rw [← endpoint_eq_beatty]; omega)
    omega
  have hadj : Adj P n ↔ n ≤ jacoRight P := by
    unfold Adj; constructor
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact h
      · omega
    · intro h; exact Or.inl ⟨hPn, h⟩
  have hthr : n ≤ jacoRight P ↔ beattyOut n ≤ P := by
    rw [endpoint_eq_beatty]; exact beatty_threshold n P
  have hds := (JacoDegreeShift.result n).1
  have hbn := beatty_bounds n hn
  refine ⟨hR, ?_, ?_, ?_⟩
  · rw [hadj]; omega
  · rw [hadj, hthr]; omega
  · rw [hadj, hthr, ← (JacoDegreeShift.result n).2.1]; omega

/-- The bound of Theorem 2.15 holds along `n = 7 + 3k`. -/
theorem bound (k : ℕ) : (jaco (7 + 3 * k)).maxDegree ≤ 4 + 2 * k := by
  have h := delta_eq_floor (7 + 3 * k)
  rw [delta] at h
  have hlo : (8 : ℝ) / 5 < Real.goldenRatio := by
    rw [Real.goldenRatio]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
  have hf : ⌊(((7 + 3 * k : ℕ) : ℝ) + 2) / Real.goldenRatio⌋ ≤ 5 + 2 * k := by
    rw [Int.floor_le_iff, div_lt_iff₀ Real.goldenRatio_pos]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  omega

/-- The edge assertion of Theorem 2.15 of arXiv:1404.0484v1: along `n = 7 + 3k` the
vertex `v_Δ` is joined to `v_n`. -/
def claim : Prop :=
  ∀ k : ℕ, Adj (jaco (7 + 3 * k)).maxDegree (7 + 3 * k)

/-- The edge assertion fails at `k = 4`, that is at order nineteen. -/
theorem result : ¬ claim := by
  intro h
  have he := (edge_iff 19 (by norm_num)).2.1.mp (h 4)
  have hP : (jaco 19).maxDegree = 11 := by
    have hd := delta_eq_floor 19
    rw [delta] at hd
    have hlo : (1617 : ℝ) / 1000 < Real.goldenRatio := by
      rw [Real.goldenRatio]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
    have hhi : Real.goldenRatio < (13 : ℝ) / 8 := by
      rw [Real.goldenRatio]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
    have hf : ⌊(((19 : ℕ) : ℝ) + 2) / Real.goldenRatio⌋ = 12 := by
      rw [Int.floor_eq_iff, le_div_iff₀ Real.goldenRatio_pos, div_lt_iff₀ Real.goldenRatio_pos]
      push_cast; constructor <;> linarith
    omega
  have hR : jacoRight 11 = 18 := by decide +kernel
  rw [hP, hR] at he
  omega

#print axioms edge_iff
#print axioms bound
#print axioms result

end D5.S3.ConceptDynamics.GraphColoring.JacoEdgeRefutation
