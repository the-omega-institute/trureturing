/- GID: D5/S3/Quantum/Divergence/MaximalHockeyStickComponents
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/MaximalHockeyStickComponents
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: Actual finite reverse tests from positive spectral components, including zero labels. -/

import D5.S3.Quantum.Divergence.MaximalHockeyStickReverseTest

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator CStarAlgebra
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Divergence.MaximalHockeyStickQuadratic
open D5.S3.Quantum.Divergence.MaximalHockeyStickReverseTest

namespace D5.S3.Quantum.Divergence.MaximalHockeyStickComponents

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem component_trace_real (G : Matrix n n ℂ) (hG : G.PosSemidef) :
    G.trace = (G.trace.re : ℂ) := Complex.eq_re_of_ofReal_le hG.trace_nonneg

private def componentState (G : Matrix n n ℂ) (hG : G.PosSemidef) (i : n) :
    DensityState n := by
  classical
  by_cases h : G.trace.re = 0
  · refine ⟨CStarMatrix.ofMatrix (single i i 1), ?_, ?_⟩
    · apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      apply Matrix.PosSemidef.nonneg
      rw [← Matrix.diagonal_single]
      apply Matrix.PosSemidef.diagonal
      intro j
      simp only [Pi.single_apply]
      split_ifs <;> norm_num
    · change (single i i (1 : ℂ)).trace = 1
      simp [Matrix.trace, Matrix.single]
  · refine ⟨CStarMatrix.ofMatrix (G.trace.re⁻¹ • G), ?_, ?_⟩
    · apply map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      exact (hG.smul (inv_nonneg.mpr (Complex.nonneg_iff.mp hG.trace_nonneg).1)).nonneg
    · change (G.trace.re⁻¹ • G).trace = 1
      rw [Matrix.trace_smul, component_trace_real G hG]
      simp [Complex.real_smul, h]

private theorem componentState_mass (G : Matrix n n ℂ) (hG : G.PosSemidef) (i : n) :
    G.trace.re • CStarMatrix.ofMatrix.symm (componentState G hG i).1 = G := by
  classical
  by_cases h : G.trace.re = 0
  · have hG0 : G = 0 := hG.trace_eq_zero_iff.mp (by rw [component_trace_real G hG, h]; rfl)
    rw [h, zero_smul, hG0]
  · simp only [componentState, dite_eq_right h]
    change G.trace.re • (G.trace.re⁻¹ • G) = G
    rw [smul_smul, mul_inv_cancel₀ h, one_smul]

private theorem perspective_component (x s : ℝ) :
    starPerspective (x * s) ((1 - x) * s) = (2 * x - 1) ^ 2 * s := by
  by_cases h : s = 0
  · simp [h, starPerspective]
  · unfold starPerspective
    have he : x * s + (1 - x) * s = s := by ring
    rw [he]
    field_simp
    ring

/-- A finite positive component decomposition gives an actual reverse test.
Zero components prepare an arbitrary coordinate density matrix with zero
classical weight; no endpoint labels are discarded. -/
theorem reverse_test_from_components_profile (G : n → Matrix n n ℂ)
    (hG : ∀ i, (G i).PosSemidef) (x : n → ℝ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    ∃ R : ReverseTest (∑ i, x i • G i) (∑ i, (1 - x i) • G i) (Fintype.card n),
      R.starCost = ∑ i, (2 * x i - 1) ^ 2 * (G i).trace.re ∧
      ∀ t : ℝ, R.hockey t =
        ∑ i, max (x i - t * (1 - x i)) 0 * (G i).trace.re := by
  classical
  let e := (Fintype.equivFin n).symm
  let s : n → ℝ := fun i => (G i).trace.re
  have hs (i : n) : 0 ≤ s i := (Complex.nonneg_iff.mp (hG i).trace_nonneg).1
  let R : ReverseTest (∑ i, x i • G i) (∑ i, (1 - x i) • G i) (Fintype.card n) :=
    { p := fun j => x (e j) * s (e j)
      q := fun j => (1 - x (e j)) * s (e j)
      p_nonneg := fun j => mul_nonneg (hx (e j)).1 (hs (e j))
      q_nonneg := fun j => mul_nonneg (sub_nonneg.mpr (hx (e j)).2) (hs (e j))
      state := fun j => componentState (G (e j)) (hG (e j)) (e j)
      prepares_left := by
        simp only [mul_smul, s, componentState_mass]
        exact e.sum_comp (fun i => x i • G i)
      prepares_right := by
        simp only [mul_smul, s, componentState_mass]
        exact e.sum_comp (fun i => (1 - x i) • G i) }
  refine ⟨R, ?_, ?_⟩
  · change (∑ j, starPerspective (x (e j) * s (e j)) ((1 - x (e j)) * s (e j))) = _
    simp_rw [perspective_component]
    exact e.sum_comp (fun i => (2 * x i - 1) ^ 2 * (G i).trace.re)
  · intro t
    change (∑ j, max (x (e j) * s (e j) - t * ((1 - x (e j)) * s (e j))) 0) = _
    have hterm (i : n) :
        max (x i * s i - t * ((1 - x i) * s i)) 0 =
          max (x i - t * (1 - x i)) 0 * s i := by
      rw [show x i * s i - t * ((1 - x i) * s i) =
        (x i - t * (1 - x i)) * s i by ring]
      simpa only [zero_mul] using
        (max_mul_of_nonneg (x i - t * (1 - x i)) 0 (hs i)).symm
    simp_rw [hterm]
    exact e.sum_comp (fun i => max (x i - t * (1 - x i)) 0 * (G i).trace.re)

/-- The cost projection of the same positive-component construction. -/
theorem reverse_test_from_components (G : n → Matrix n n ℂ)
    (hG : ∀ i, (G i).PosSemidef) (x : n → ℝ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    ∃ R : ReverseTest (∑ i, x i • G i) (∑ i, (1 - x i) • G i) (Fintype.card n),
      R.starCost = ∑ i, (2 * x i - 1) ^ 2 * (G i).trace.re := by
  obtain ⟨R, hc, -⟩ := reverse_test_from_components_profile G hG x hx
  exact ⟨R, hc⟩

/-- Independently indexed positive components with two arbitrary nonnegative
weights. A coordinate for each label supplies a state only when its component
has zero mass; in particular an empty matrix carrier may use an empty alphabet. -/
theorem reverse_test_from_weighted_components {l : Type*} [Fintype l]
    (coordinate : l → n) (G : l → Matrix n n ℂ)
    (hG : ∀ i, (G i).PosSemidef) (a b : l → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    ∃ R : ReverseTest (∑ i, a i • G i) (∑ i, b i • G i) (Fintype.card l),
      ∀ t : ℝ, R.hockey t =
        ∑ i, max (a i - t * b i) 0 * (G i).trace.re := by
  classical
  let e := (Fintype.equivFin l).symm
  let s : l → ℝ := fun i => (G i).trace.re
  have hs (i : l) : 0 ≤ s i := (Complex.nonneg_iff.mp (hG i).trace_nonneg).1
  let R : ReverseTest (∑ i, a i • G i) (∑ i, b i • G i) (Fintype.card l) :=
    { p := fun j => a (e j) * s (e j)
      q := fun j => b (e j) * s (e j)
      p_nonneg := fun j => mul_nonneg (ha (e j)) (hs (e j))
      q_nonneg := fun j => mul_nonneg (hb (e j)) (hs (e j))
      state := fun j => componentState (G (e j)) (hG (e j)) (coordinate (e j))
      prepares_left := by
        simp only [mul_smul, s, componentState_mass]
        exact e.sum_comp (fun i => a i • G i)
      prepares_right := by
        simp only [mul_smul, s, componentState_mass]
        exact e.sum_comp (fun i => b i • G i) }
  refine ⟨R, ?_⟩
  intro t
  change (∑ j, max (a (e j) * s (e j) - t * (b (e j) * s (e j))) 0) = _
  have hterm (i : l) :
      max (a i * s i - t * (b i * s i)) 0 = max (a i - t * b i) 0 * s i := by
    rw [show a i * s i - t * (b i * s i) = (a i - t * b i) * s i by ring]
    simpa only [zero_mul] using
      (max_mul_of_nonneg (a i - t * b i) 0 (hs i)).symm
  simp_rw [hterm]
  exact e.sum_comp (fun i => max (a i - t * b i) 0 * (G i).trace.re)

end D5.S3.Quantum.Divergence.MaximalHockeyStickComponents
