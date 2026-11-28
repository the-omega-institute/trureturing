/- GID: D5/S3/Quantum/Analysis/TraceClass/ModularTransferReadout
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/TraceClass/ModularTransferReadout
   mirror-E: none(waiver:analytic-hilbert-space-proof)
   anchors: []
   utility: none
   digest: Finite tensor readouts characterize Hilbert–Schmidt modular transfer. -/

import D5.S3.Quantum.Analysis.TraceClass.ModularTransferTensor

/-! The sharp norm of a reflected correlation on finite sums of tensor probes. -/

set_option autoImplicit false

open scoped BigOperators InnerProductSpace TensorProduct

namespace ModularTransferReadout

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A common norm bound for the correlation on arbitrary finite sums of elementary tensors. -/
def Bound (T : H →L[ℂ] H) (reflect : H → H) (B : ℝ) : Prop :=
  ∀ (ι : Type u) (s : Finset ι) (x y : ι → H),
    ‖∑ i ∈ s, inner ℂ (reflect (x i)) (T (y i))‖ ≤ B *
      ‖∑ i ∈ s, x i ⊗ₜ[ℂ] y i‖

private theorem partial_sum_le [CompleteSpace H] (T : H →L[ℂ] H) (reflect : H → H)
    (hiso : ∀ x, ‖reflect x‖ = ‖x‖)
    (hsymm : ∀ x y, inner ℂ (reflect x) y = inner ℂ (reflect y) x)
    {B : ℝ} (hB : Bound T reflect B) {w : Set H} (b : HilbertBasis w ℂ H) (s : Finset w) :
    (∑ i ∈ s, ‖T (b i)‖ ^ 2) ≤ B ^ 2 := by
  classical
  let x (i : w) := reflect (T (b i))
  let v : H ⊗[ℂ] H := ∑ i ∈ s, x i ⊗ₜ[ℂ] b i
  let E := ∑ i ∈ s, ‖T (b i)‖ ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hv : ‖v‖ ^ 2 = E := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
    simp only [v, sum_inner, inner_sum, TensorProduct.inner_tmul,
      orthonormal_iff_ite.mp b.orthonormal, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq']
    change (∑ i ∈ s, if i ∈ s then inner ℂ (x i) (x i) else 0).re = E
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [ite_eq_left hi]
    calc
      (inner ℂ (x i) (x i)).re = ‖x i‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
      _ = ‖T (b i)‖ ^ 2 := congrArg (fun r : ℝ => r ^ 2) (hiso _)
  have hnum : (∑ i ∈ s, inner ℂ (reflect (x i)) (T (b i))) = (E : ℂ) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hsymm (x i) (T (b i))]
    change inner ℂ (x i) (x i) = _
    rw [inner_self_eq_norm_sq_to_K, show ‖x i‖ = ‖T (b i)‖ from hiso _]
    norm_cast
  have h := hB w s x b
  change ‖∑ i ∈ s, inner ℂ (reflect (x i)) (T (b i))‖ ≤ B * ‖v‖ at h
  rw [hnum, Complex.norm_real, Real.norm_of_nonneg hE, ← hv] at h
  change E ≤ B ^ 2
  by_cases hz : ‖v‖ = 0
  · rw [← hv, hz]
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using sq_nonneg B
  · have hp : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hb : ‖v‖ ≤ B := le_of_mul_le_mul_right (by simpa only [pow_two] using h) hp
    rw [← hv]
    exact (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans hb)).mpr hb

private theorem bound_of_representative [CompleteSpace H] (T : H →L[ℂ] H) (reflect : H → H)
    (v : UniformSpace.Completion (H ⊗[ℂ] H))
    (hpair : ∀ x y : H, inner ℂ v
      ((x ⊗ₜ[ℂ] y : H ⊗[ℂ] H) : UniformSpace.Completion (H ⊗[ℂ] H)) =
      inner ℂ (reflect x) (T y)) : Bound T reflect ‖v‖ := by
  intro ι s x y
  let z : H ⊗[ℂ] H := ∑ i ∈ s, x i ⊗ₜ[ℂ] y i
  have hz : inner ℂ v (z : UniformSpace.Completion (H ⊗[ℂ] H)) =
      ∑ i ∈ s, inner ℂ (reflect (x i)) (T (y i)) := by
    change inner ℂ v ((UniformSpace.Completion.toComplL :
      (H ⊗[ℂ] H) →L[ℂ] UniformSpace.Completion (H ⊗[ℂ] H)) z) = _
    rw [show z = ∑ i ∈ s, x i ⊗ₜ[ℂ] y i from rfl, map_sum, inner_sum]
    exact Finset.sum_congr rfl (fun i _ => hpair (x i) (y i))
  rw [← hz]
  simpa [z] using norm_inner_le_norm v (z : UniformSpace.Completion (H ⊗[ℂ] H))

/-- A uniform bound over finite product readouts exists precisely for Hilbert–Schmidt transfer. -/
theorem finite_readout_bound_iff [CompleteSpace H] (T : H →L[ℂ] H) (reflect : H → H)
    (hiso : ∀ x, ‖reflect x‖ = ‖x‖)
    (hsymm : ∀ x y, inner ℂ (reflect x) y = inner ℂ (reflect y) x) :
    (∃ B : ℝ, Bound T reflect B) ↔ HilbertSchmidt.IsHilbertSchmidt T := by
  constructor
  · rintro ⟨B, hB⟩
    obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
    exact ⟨w, b, summable_of_sum_le (fun i => sq_nonneg ‖T (b i)‖)
      (partial_sum_le T reflect hiso hsymm hB b)⟩
  · rintro hT
    obtain ⟨v, _, hpair⟩ := ModularTransferTensor.transfer_tensor T hT reflect hiso hsymm
    exact ⟨‖v‖, bound_of_representative T reflect v hpair⟩

/-- Every bound on the finite readouts controls the full Hilbert–Schmidt trace square. -/
theorem trace_le_bound_sq [CompleteSpace H] (T : H →L[ℂ] H)
    (hT : HilbertSchmidt.IsHilbertSchmidt T) (reflect : H → H)
    (hiso : ∀ x, ‖reflect x‖ = ‖x‖)
    (hsymm : ∀ x y, inner ℂ (reflect x) y = inner ℂ (reflect y) x)
    {B : ℝ} (hB : Bound T reflect B) :
    (trace (star T * T)
      (HilbertSchmidt.isTraceClass_star_mul_self_of_isHilbertSchmidt hT)).re ≤ B ^ 2 := by
  obtain ⟨w, b, _⟩ := hT
  rw [trace_eq_of_hilbertBasis_of_nonneg (star_mul_self_nonneg T) _ b]
  have hentry (i : w) : inner ℂ (b i) ((star T * T) (b i)) = ((‖T (b i)‖ ^ 2 : ℝ) : ℂ) := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
      inner_self_eq_norm_sq_to_K]
    norm_cast
  simp only [hentry, ← Complex.ofReal_tsum, Complex.ofReal_re]
  exact Real.tsum_le_of_sum_le (fun i => sq_nonneg ‖T (b i)‖)
    (partial_sum_le T reflect hiso hsymm hB b)

/-- The least nonnegative bound equals the square root of the transfer trace. -/
theorem least_finite_readout_bound [CompleteSpace H] (T : H →L[ℂ] H)
    (hT : HilbertSchmidt.IsHilbertSchmidt T) (reflect : H → H)
    (hiso : ∀ x, ‖reflect x‖ = ‖x‖)
    (hsymm : ∀ x y, inner ℂ (reflect x) y = inner ℂ (reflect y) x) :
    IsLeast {B : ℝ | 0 ≤ B ∧ Bound T reflect B}
      (Real.sqrt (trace (star T * T)
        (HilbertSchmidt.isTraceClass_star_mul_self_of_isHilbertSchmidt hT)).re) := by
  obtain ⟨v, hv, hpair⟩ := ModularTransferTensor.transfer_tensor T hT reflect hiso hsymm
  rw [← hv, Real.sqrt_sq (norm_nonneg v)]
  refine ⟨⟨norm_nonneg v, bound_of_representative T reflect v hpair⟩, ?_⟩
  rintro B ⟨hB, hbound⟩
  apply (sq_le_sq₀ (norm_nonneg v) hB).mp
  rw [hv]
  exact trace_le_bound_sq T hT reflect hiso hsymm hbound

#print axioms finite_readout_bound_iff
#print axioms least_finite_readout_bound

end ModularTransferReadout
