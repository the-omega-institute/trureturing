/- GID: D5/S3/ConceptDynamics/GraphColoring/JacoAdditionLawRefutation
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/GraphColoring/JacoAdditionLawRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [lake/module/D5.S3.ConceptDynamics.GraphColoring.JacoMaximumDegree]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ConceptDynamics/GraphColoring/JacoAdditionLawRefutation.claim; result=D5/S3/ConceptDynamics/GraphColoring/JacoAdditionLawRefutation.result; claim=D5/S3/ConceptDynamics/GraphColoring/JacoAdditionLawRefutation.claim
   digest: The complete original Jaco addition assertion fails at the distinct orders three and eleven. -/

import D5.S3.ConceptDynamics.GraphColoring.JacoMaximumDegree

/-! The whole original two-branch addition law has an admissible counterexample. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.GraphColoring.JacoAdditionLawRefutation

open D5.S3.ConceptDynamics.GraphColoring.JacoDomPathDiameterRefutation
open D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty

/-
proof_shape:
  result: bind-only
escape_witness: none
admission_basis: open-problem-resolution (issue #25870)
The graph, degree and maximum-degree suppliers are reused directly.
-/

/-- Exactly one vertex of this graph attains its ordinary maximum degree. -/
def UniqueJaconian (n : ℕ) : Prop :=
  ∃! v : Vertex n, (jaco n).degree v = (jaco n).maxDegree

/-- The complete two-branch assertion of arXiv:1404.0484v1, Theorem 2.10. -/
def claim : Prop :=
  ∀ n m : ℕ, 3 ≤ n → 3 ≤ m → n ≠ m →
    ((UniqueJaconian n ∨ UniqueJaconian m) →
      (jaco (n + m)).maxDegree = (jaco n).maxDegree + (jaco m).maxDegree) ∧
    ((¬ UniqueJaconian n ∧ ¬ UniqueJaconian m) →
      (jaco (n + m)).maxDegree = (jaco n).maxDegree + (jaco m).maxDegree + 1)

/-- One admissible pair contradicts the complete universal assertion. -/
theorem result : ¬ claim := by
  have hp := Real.goldenRatio_pos
  have hlo : (8 : ℝ) / 5 < Real.goldenRatio := by
    rw [Real.goldenRatio]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
  have hhi : Real.goldenRatio < (13 : ℝ) / 8 := by
    rw [Real.goldenRatio]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
  have floor_at (a : ℝ) (k : ℕ)
      (hl : (k : ℝ) * Real.goldenRatio ≤ a)
      (hh : a < (k + 1 : ℝ) * Real.goldenRatio) :
      ⌊a / Real.goldenRatio⌋₊ = k := by
    have ha : 0 ≤ a := (mul_nonneg (Nat.cast_nonneg k) hp.le).trans hl
    apply (Nat.floor_eq_iff (div_nonneg ha hp.le)).mpr
    exact ⟨(le_div_iff₀ hp).mpr hl, (div_lt_iff₀ hp).mpr hh⟩
  have hb1 : beattyOut 1 = 1 := by
    norm_num only [beattyOut, Nat.cast_ofNat]
    exact floor_at 2 1
      (by norm_num only [Nat.cast_ofNat]; linarith)
      (by norm_num only [Nat.cast_ofNat]; linarith)
  have hb2 : beattyOut 2 = 1 := by
    norm_num only [beattyOut, Nat.cast_ofNat]
    exact floor_at 3 1
      (by norm_num only [Nat.cast_ofNat]; linarith)
      (by norm_num only [Nat.cast_ofNat]; linarith)
  have hb3 : beattyOut 3 = 2 := by
    norm_num only [beattyOut, Nat.cast_ofNat]
    exact floor_at 4 2
      (by norm_num only [Nat.cast_ofNat]; linarith)
      (by norm_num only [Nat.cast_ofNat]; linarith)
  have maximum_at (n k : ℕ) (hn : 2 ≤ n)
      (hf : ⌊((n : ℝ) + 2) / Real.goldenRatio⌋₊ = k) :
      (jaco n).maxDegree = k - 1 := by
    have h := (JacoMaximumDegree.result.1 n hn).1
    have he : 2 * ((n : ℝ) + 2) / (1 + Real.sqrt 5) =
        ((n : ℝ) + 2) / Real.goldenRatio := by
      simp only [Real.goldenRatio, div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring
    rwa [he, hf] at h
  have h3 : (jaco 3).maxDegree = 2 := by
    apply maximum_at 3 3 (by decide)
    norm_num only [Nat.cast_ofNat]
    exact floor_at 5 3
      (by norm_num only [Nat.cast_ofNat]; linarith)
      (by norm_num only [Nat.cast_ofNat]; linarith)
  have h11 : (jaco 11).maxDegree = 7 := by
    apply maximum_at 11 8 (by decide)
    norm_num only [Nat.cast_ofNat]
    exact floor_at 13 8
      (by norm_num only [Nat.cast_ofNat]; linarith)
      (by norm_num only [Nat.cast_ofNat]; linarith)
  have h14 : (jaco 14).maxDegree = 8 := by
    apply maximum_at 14 9 (by decide)
    norm_num only [Nat.cast_ofNat]
    exact floor_at 16 9
      (by norm_num only [Nat.cast_ofNat]; linarith)
      (by norm_num only [Nat.cast_ofNat]; linarith)
  have hdegree (v : Vertex 3) :
      (jaco 3).degree v = if v.1 = 2 then 2 else 1 := by
    rw [JacoMaximumDegree.degree_formula]
    have hv := Finset.mem_Icc.mp v.2
    have cases : v.1 = 1 ∨ v.1 = 2 ∨ v.1 = 3 := by omega
    rcases cases with h | h | h <;> simp [h, hb1, hb2, hb3]
  have hu3 : UniqueJaconian 3 := by
    refine ⟨⟨2, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩, ?_, ?_⟩
    · dsimp only
      rw [hdegree, h3]
      norm_num
    · intro v hv
      apply Subtype.ext
      have hd := hdegree v
      rw [h3] at hv
      split_ifs at hd with h
      · exact h
      · omega
  intro hclaim
  have h := (hclaim 3 11 (by decide) (by decide) (by decide)).1 (Or.inl hu3)
  norm_num only [show 3 + 11 = 14 by decide, h3, h11, h14] at h

#print axioms result

end D5.S3.ConceptDynamics.GraphColoring.JacoAdditionLawRefutation
