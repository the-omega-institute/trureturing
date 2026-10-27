/- GID: D5/S3/Quantum/QuantumChannels/QutritChannelUnitaryExtremeDecomposition
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/QutritChannelUnitaryExtremeDecomposition
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Unitary and doubly extreme decomposition of the equal-modulus HMR qutrit channel. -/

import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import Mathlib.Analysis.Convex.Extreme
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.FieldTheory.IsAlgClosed.Basic

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open MatrixMap

namespace D5.S3.Quantum.QuantumChannels.QutritChannelUnitaryExtremeDecomposition

/-- The four operators of Haagerup, Musat and Ruskai, in their source order. -/
def hmrKraus (α β : ℂ) : Fin 4 → Matrix (Fin 3) (Fin 3) ℂ :=
  ![!![α, 0, 0; 0, 0, 1; 0, 0, 0],
    !![0, 0, β; 0, 0, 0; 0, 1, 0],
    !![0, -1, 0; 0, 0, 0; -star β, 0, 0],
    !![0, 0, 0; 1, 0, 0; 0, 0, star α]]

/-- The source convention places the adjoint of each operator on the left. -/
def hmrChannel (α β : ℂ) : MatrixMap (Fin 3) (Fin 3) ℂ :=
  (1 / 2 : ℂ) • of_kraus (fun k => star (hmrKraus α β k))
    (fun k => star (hmrKraus α β k))

/-- A map is unital when it preserves the identity matrix. -/
def IsUnital (φ : MatrixMap (Fin 3) (Fin 3) ℂ) : Prop := φ 1 = 1

/-- Trace preservation is required on every complex matrix. -/
def IsTracePreserving (φ : MatrixMap (Fin 3) (Fin 3) ℂ) : Prop :=
  ∀ x, (φ x).trace = x.trace

private def krausChannel (y : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ) :
    MatrixMap (Fin 3) (Fin 3) ℂ :=
  of_kraus (fun i => star (y i)) (fun i => star (y i))

private def baseKraus : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ :=
  fun i => (1 / (2 * Real.sqrt 3) : ℂ) •
    (![!![-1, -(Real.sqrt 2 : ℂ), 1;
          (Real.sqrt 2 : ℂ), 0, -(Real.sqrt 2 : ℂ);
          -1, (Real.sqrt 2 : ℂ), 1],
       !![1, (Real.sqrt 2 : ℂ), 1;
          (Real.sqrt 2 : ℂ), 0, (Real.sqrt 2 : ℂ);
          1, (Real.sqrt 2 : ℂ), 1],
       !![1, -(Real.sqrt 2 : ℂ), 1;
          -(Real.sqrt 2 : ℂ), 0, (Real.sqrt 2 : ℂ);
          -1, (Real.sqrt 2 : ℂ), -1]] i)

private def baseUnitary : Matrix (Fin 3) (Fin 3) ℂ :=
  (1 / 2 : ℂ) • !![1, -(Real.sqrt 2 : ℂ), -1;
    (Real.sqrt 2 : ℂ), 0, (Real.sqrt 2 : ℂ);
    -1, -(Real.sqrt 2 : ℂ), 1]

private def diagonalPhase (r : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal ![r, 1, r⁻¹]

private def conjugateChannel (d e : Matrix (Fin 3) (Fin 3) ℂ)
    (φ : MatrixMap (Fin 3) (Fin 3) ℂ) : MatrixMap (Fin 3) (Fin 3) ℂ :=
  (of_kraus (fun _ : Fin 1 => star e) (fun _ : Fin 1 => star e)).comp
    (φ.comp (of_kraus (fun _ : Fin 1 => star d) (fun _ : Fin 1 => star d)))

private lemma kraus_action (y : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ)
    (ρ : Matrix (Fin 3) (Fin 3) ℂ) :
    krausChannel y ρ = ∑ i, star (y i) * ρ * y i := by
  sorry

private lemma choi_range_lift (y : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ)
    (θ : MatrixMap (Fin 3) (Fin 3) ℂ) (t : ℝ) (ht : 0 < t)
    (hθ : θ.IsCompletelyPositive)
    (hdom : (choi_matrix (krausChannel y) - t • choi_matrix θ).PosSemidef) :
    ∃ h : Matrix (Fin 3) (Fin 3) ℂ, ∀ ρ,
      θ ρ = ∑ i, ∑ j, h i j • (star (y i) * ρ * y j) := by
  sorry

private lemma extreme_ucp_of_independent
    (y : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ)
    (hu : ∑ i, star (y i) * y i = 1)
    (hli : LinearIndependent ℂ
      (fun p : Fin 3 × Fin 3 => star (y p.1) * y p.2)) :
    krausChannel y ∈ Set.extremePoints ℝ
      {θ : MatrixMap (Fin 3) (Fin 3) ℂ | θ.IsCompletelyPositive ∧ IsUnital θ} := by
  sorry

private lemma extreme_cpt_of_independent
    (y : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ)
    (htp : ∑ i, y i * star (y i) = 1)
    (hli : LinearIndependent ℂ
      (fun p : Fin 3 × Fin 3 => y p.1 * star (y p.2))) :
    krausChannel y ∈ Set.extremePoints ℝ
      {θ : MatrixMap (Fin 3) (Fin 3) ℂ |
        θ.IsCompletelyPositive ∧ IsTracePreserving θ} := by
  sorry

private lemma choi_rank_of_independent
    (y : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ)
    (hli : LinearIndependent ℂ
      (fun p : Fin 3 × Fin 3 => star (y p.1) * y p.2)) :
    (choi_matrix (krausChannel y)).rank = 3 := by
  sorry

private lemma base_unital : ∑ i, star (baseKraus i) * baseKraus i = 1 := by
  sorry

private lemma base_trace : ∑ i, baseKraus i * star (baseKraus i) = 1 := by
  sorry

private lemma base_left_independent : LinearIndependent ℂ
    (fun p : Fin 3 × Fin 3 => star (baseKraus p.1) * baseKraus p.2) := by
  sorry

private lemma base_right_independent : LinearIndependent ℂ
    (fun p : Fin 3 × Fin 3 => baseKraus p.1 * star (baseKraus p.2)) := by
  sorry

private lemma base_decomposition :
    baseUnitary ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧
    ∀ ρ, hmrChannel (1 / Real.sqrt 2) (1 / Real.sqrt 2) ρ =
      (1 / 4 : ℂ) • (star baseUnitary * ρ * baseUnitary) +
      (3 / 4 : ℂ) • krausChannel baseKraus ρ := by
  sorry

private lemma phase_reduction (α β : ℂ)
    (hα : ‖α‖ = 1 / Real.sqrt 2) (hβ : ‖β‖ = 1 / Real.sqrt 2) :
    ∃ r s : ℂ, diagonalPhase r ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧
      diagonalPhase s ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧
      hmrChannel α β = conjugateChannel (diagonalPhase r) (diagonalPhase s)
        (hmrChannel (1 / Real.sqrt 2) (1 / Real.sqrt 2)) := by
  sorry

private lemma transport (d e u : Matrix (Fin 3) (Fin 3) ℂ)
    (φ ψ : MatrixMap (Fin 3) (Fin 3) ℂ)
    (hd : d ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (he : e ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (hu : u ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (hcp : ψ.IsCompletelyPositive) (hunit : IsUnital ψ) (htp : IsTracePreserving ψ)
    (hrank : (choi_matrix ψ).rank = 3)
    (hucp : ψ ∈ Set.extremePoints ℝ
      {θ : MatrixMap (Fin 3) (Fin 3) ℂ | θ.IsCompletelyPositive ∧ IsUnital θ})
    (hcpt : ψ ∈ Set.extremePoints ℝ
      {θ : MatrixMap (Fin 3) (Fin 3) ℂ |
        θ.IsCompletelyPositive ∧ IsTracePreserving θ})
    (hdec : ∀ ρ, φ ρ = (1 / 4 : ℂ) • (star u * ρ * u) + (3 / 4 : ℂ) • ψ ρ) :
    ∃ (v : Matrix (Fin 3) (Fin 3) ℂ) (η : MatrixMap (Fin 3) (Fin 3) ℂ),
      v ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧ η.IsCompletelyPositive ∧ IsUnital η ∧
      IsTracePreserving η ∧ (choi_matrix η).rank = 3 ∧
      η ∈ Set.extremePoints ℝ
        {θ : MatrixMap (Fin 3) (Fin 3) ℂ | θ.IsCompletelyPositive ∧ IsUnital θ} ∧
      η ∈ Set.extremePoints ℝ
        {θ : MatrixMap (Fin 3) (Fin 3) ℂ |
          θ.IsCompletelyPositive ∧ IsTracePreserving θ} ∧
      ∀ ρ, conjugateChannel d e φ ρ =
        (1 / 4 : ℂ) • (star v * ρ * v) + (3 / 4 : ℂ) • η ρ := by
  sorry

/-- Every equal-modulus HMR channel has a unitary and doubly extreme decomposition. -/
theorem result : ∀ α β : ℂ, ‖α‖ = 1 / Real.sqrt 2 → ‖β‖ = 1 / Real.sqrt 2 →
    ∃ (u : Matrix (Fin 3) (Fin 3) ℂ) (lam : ℝ)
      (ψ : MatrixMap (Fin 3) (Fin 3) ℂ),
      u ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧ 0 ≤ lam ∧ lam ≤ 1 ∧
      ψ.IsCompletelyPositive ∧ IsUnital ψ ∧ IsTracePreserving ψ ∧
      (choi_matrix ψ).rank = 3 ∧
      ψ ∈ Set.extremePoints ℝ
        {θ : MatrixMap (Fin 3) (Fin 3) ℂ | θ.IsCompletelyPositive ∧ IsUnital θ} ∧
      ψ ∈ Set.extremePoints ℝ
        {θ : MatrixMap (Fin 3) (Fin 3) ℂ |
          θ.IsCompletelyPositive ∧ IsTracePreserving θ} ∧
      ∀ ρ, hmrChannel α β ρ = (lam : ℂ) • (star u * ρ * u) +
        ((1 - lam : ℝ) : ℂ) • ψ ρ := by
  intro α β hα hβ
  obtain ⟨r, s, hr, hs, hphase⟩ := phase_reduction α β hα hβ
  have hucp := extreme_ucp_of_independent baseKraus base_unital base_left_independent
  have hcpt := extreme_cpt_of_independent baseKraus base_trace base_right_independent
  have hprops := Set.extremePoints_subset hcpt
  have hu := (Set.extremePoints_subset hucp).2
  obtain ⟨u, ψ, hun, hcp, hunit, htp, hrank, hue, hte, hdec⟩ :=
    transport (diagonalPhase r) (diagonalPhase s) baseUnitary
      (hmrChannel (1 / Real.sqrt 2) (1 / Real.sqrt 2)) (krausChannel baseKraus)
      hr hs base_decomposition.1 hprops.1 hu hprops.2
      (choi_rank_of_independent baseKraus base_left_independent)
      hucp hcpt base_decomposition.2
  refine ⟨u, 1 / 4, ψ, hun, by norm_num, by norm_num,
    hcp, hunit, htp, hrank, hue, hte, ?_⟩
  intro ρ
  rw [hphase, hdec]
  norm_num

end D5.S3.Quantum.QuantumChannels.QutritChannelUnitaryExtremeDecomposition
