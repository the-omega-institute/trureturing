/- GID: D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixNetBounds
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixNetBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite net bounds for Schmidt and operator tails of Hermitian sign matrices. -/

import D5.S3.Quantum.Entanglement.EntanglementBreaking.NetInterpolation
import D5.S3.Quantum.Entanglement.EntanglementBreaking.FiniteSignTails

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace D5.S3.Quantum.Entanglement.EntanglementBreaking

open _root_.Matrix MeasureTheory
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)

private abbrev Sample (d : ℕ) := HermitianSignIndex (Fin d × Fin d) → Bool

/-- The rank-restricted net tests suffice at half the required Schmidt threshold. -/
theorem signCubeSample_schmidt_failure_le {d k : ℕ} (hkd : k ≤ d) :
    (signCubeMeasure (HermitianSignIndex (Fin d × Fin d))).real
      {ω | ¬ SchmidtQuadraticBound k (signCubeSample ω)} ≤
      (17 : ℝ) ^ (8 * d * k) *
        (4 * Real.exp (-((d : ℝ) / (64 * (k : ℝ))) ^ 2 / (4 * (18 / 25 : ℝ)))) := by
  classical
  obtain ⟨N, hcard, hN, hinterp⟩ := exists_schmidt_bilinear_net d k hkd
  let μ := signCubeMeasure (HermitianSignIndex (Fin d × Fin d))
  let t := (d : ℝ) / (64 * (k : ℝ))
  have ht : 0 ≤ t := by positivity
  let E : Set (Sample d) :=
    {ω | ∃ p ∈ N ×ˢ N, t ≤ ‖star p.1 ⬝ᵥ (signCubeSample ω *ᵥ p.2)‖}
  have hsub : {ω | ¬ SchmidtQuadraticBound k (signCubeSample ω)} ⊆ E := by
    intro ω hω
    by_contra h
    apply hω
    intro x hx hxr
    have hnet (u) (hu : u ∈ N) (v) (hv : v ∈ N) :
        ‖star u ⬝ᵥ (signCubeSample ω *ᵥ v)‖ ≤ t := by
      apply le_of_lt
      exact lt_of_not_ge (fun hbad => h ⟨(u, v), Finset.mem_product.mpr ⟨hu, hv⟩, hbad⟩)
    have hbound := hinterp (signCubeSample ω) t ht hnet x x hx hx hxr hxr
    convert hbound using 1
    simp only [t]
    ring
  have htail := signCubeSample_bilinear_finset_tail (N ×ˢ N)
    (fun p => p.1) (fun p => p.2)
    (fun p hp => ((hN _ (Finset.mem_product.mp hp).1).1).le)
    (fun p hp => ((hN _ (Finset.mem_product.mp hp).2).1).le) ht
  have hbound : ((N ×ˢ N).card : ℝ) ≤ (17 : ℝ) ^ (8 * d * k) := by
    have hn : (N.card : ℝ) ≤ (17 : ℝ) ^ (4 * d * k) := by exact_mod_cast hcard
    rw [Finset.card_product, Nat.cast_mul, show 8 * d * k = (4 * d * k) + (4 * d * k) by ring,
      pow_add]
    gcongr
  exact (measureReal_mono (μ := μ) hsub).trans
    (htail.trans (mul_le_mul_of_nonneg_right hbound (by positivity)))

/-- The full-sphere net lifts any uniform fixed-vector quadratic tail for Hermitian samples
to an operator norm tail. -/
theorem operator_tail_of_quadratic_tail {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (H : Ω → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hH : ∀ ω, (H ω).IsHermitian) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 ≤ b)
    (hquad : ∀ x : Fin d × Fin d → ℂ, ‖WithLp.toLp 2 x‖ = 1 →
      μ.real {ω | t ≤ ‖star x ⬝ᵥ (H ω *ᵥ x)‖} ≤ b) :
    μ.real {ω | (4 / 3 : ℝ) * t < ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (H ω)‖} ≤
      (17 : ℝ) ^ (2 * d ^ 2) * b := by
  classical
  obtain ⟨N, hcard, hN, -, hinterp⟩ := exists_full_sphere_quadratic_net d
  let E (x : Fin d × Fin d → ℂ) : Set Ω := {ω | t ≤ ‖star x ⬝ᵥ (H ω *ᵥ x)‖}
  have hsub : {ω | (4 / 3 : ℝ) * t < ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (H ω)‖}
      ⊆ ⋃ x ∈ N, E x := by
    intro ω hω
    by_contra h
    apply (not_lt_of_ge (hinterp _ (hH ω) t ht ?_)) hω
    intro x hx
    apply le_of_lt
    exact lt_of_not_ge (fun hbad => h (Set.mem_iUnion₂.mpr ⟨x, hx, hbad⟩))
  calc
    _ ≤ μ.real (⋃ x ∈ N, E x) := measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ ∑ x ∈ N, μ.real (E x) := measureReal_biUnion_finset_le N E
    _ ≤ ∑ _x ∈ N, b := Finset.sum_le_sum fun x hx => hquad x (hN x hx)
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hb

/-- Apply the operator norm bound to the finite sign sample and its known quadratic tail. -/
theorem signCubeSample_operator_tail {d : ℕ} {t : ℝ} (ht : 0 ≤ t) :
    (signCubeMeasure (HermitianSignIndex (Fin d × Fin d))).real
      {ω | (4 / 3 : ℝ) * t <
          ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (signCubeSample ω)‖} ≤
      (17 : ℝ) ^ (2 * d ^ 2) *
        (2 * Real.exp (-(t ^ 2) / (2 * (18 / 25 : ℝ)))) :=
  operator_tail_of_quadratic_tail (signCubeMeasure _) signCubeSample
    (fun _ => finiteSignSample_isHermitian _ _) ht (by positivity)
    (fun x hx => signCubeSample_quadratic_tail x hx.le ht)

/-- The same full-sphere net applies to the partial transpose when supplied its
fixed-vector quadratic tail. -/
theorem signCubeSample_partialTranspose_operator_tail_of_quadratic {d : ℕ} {t : ℝ}
    (ht : 0 ≤ t)
    (hquad : ∀ x : Fin d × Fin d → ℂ, ‖WithLp.toLp 2 x‖ = 1 →
      (signCubeMeasure (HermitianSignIndex (Fin d × Fin d))).real
        {ω | t ≤ ‖star x ⬝ᵥ (partialTranspose (signCubeSample ω) *ᵥ x)‖} ≤
        2 * Real.exp (-(t ^ 2) / (2 * (18 / 25 : ℝ)))) :
    (signCubeMeasure (HermitianSignIndex (Fin d × Fin d))).real
      {ω | (4 / 3 : ℝ) * t <
          ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (partialTranspose (signCubeSample ω))‖} ≤
      (17 : ℝ) ^ (2 * d ^ 2) *
        (2 * Real.exp (-(t ^ 2) / (2 * (18 / 25 : ℝ)))) := by
  apply operator_tail_of_quadratic_tail _ _ ?_ ht (by positivity) hquad
  intro ω
  have hH : (signCubeSample ω).IsHermitian := finiteSignSample_isHermitian _ _
  ext ⟨i, j⟩ ⟨k, l⟩
  exact hH.apply (i, l) (k, j)

end D5.S3.Quantum.Entanglement.EntanglementBreaking
