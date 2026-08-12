/- GID: D5/S3/Quantum/PureState/PureStateHandshake
   generality: G
   mirror-B: D5/B/S3/Quantum/PureState/PureStateHandshake
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The pure-state handshake. For a normalized amplitude vector v the rank-one density matrix ρ = |v⟩⟨v| is idempotent, and for any matrix X the sandwich ρ X ρ collapses to the scalar multiple ⟨v, X v⟩ · ρ, where that scalar equals the trace Tr(X ρ). The middle identity is the handshake mechanism; the outer two are its supporting idempotency and expectation-equals-trace facts. -/

import Mathlib

open Matrix BigOperators

namespace D5.S3.Quantum.PureState.PureStateHandshake

variable {n : Type*} [Fintype n]

/-- The **rank-one (pure) density matrix** `ρ = |v⟩⟨v|` built from an amplitude vector `v`, as the
outer product `vecMulVec v (star v)` with entries `ρ i j = v i * conj (v j)`. -/
noncomputable def rankOneDensity (v : n → ℂ) : Matrix n n ℂ := vecMulVec v (star v)

/-- **Pure-state handshake.** For a normalized amplitude `v` (`⟨v, v⟩ = 1`) and *any* matrix `X`, the
rank-one density matrix `ρ = |v⟩⟨v|` satisfies three facts at once:

* `ρ * ρ = ρ` — `ρ` is idempotent (a pure state is its own square root);
* `ρ * X * ρ = ⟨v, X v⟩ • ρ` — the **handshake**: the sandwich of any `X` between two copies of `ρ`
  collapses to the scalar `⟨v, X v⟩` times `ρ`;
* `⟨v, X v⟩ = Tr (X * ρ)` — that scalar is exactly the density-matrix expectation `Tr(X ρ)`.

Specializing `X` to an inverse state `σ⁻¹` gives the mechanism behind the pure-state divergence
handshake. The load-bearing new content is the middle sandwich-collapse identity; the idempotency and
the expectation-equals-trace fact are its supporting glue. Only `⟨v, v⟩ = 1` is used, and only for
idempotency — the handshake and the trace identity hold for every `v` and every `X`, with no
positivity or invertibility hypothesis.

This records the algebraic handshake mechanism only; the downstream conclusion that the
Belavkin–Staszewski and max divergences of a pure state against `σ` both equal `ln ⟨v, σ⁻¹ v⟩` is
not covered by this statement. -/
theorem pure_state_handshake (v : n → ℂ) (hv : star v ⬝ᵥ v = 1) (X : Matrix n n ℂ) :
    rankOneDensity v * rankOneDensity v = rankOneDensity v
      ∧ rankOneDensity v * X * rankOneDensity v = (star v ⬝ᵥ X *ᵥ v) • rankOneDensity v
      ∧ star v ⬝ᵥ X *ᵥ v = trace (X * rankOneDensity v) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    simp only [rankOneDensity, Matrix.mul_apply, Matrix.vecMulVec_apply, Pi.star_apply]
    have hsum : ∑ k, star (v k) * v k = 1 := by
      have := hv; simp only [dotProduct, Pi.star_apply] at this; exact this
    calc ∑ k, v i * star (v k) * (v k * star (v j))
        = (v i * star (v j)) * ∑ k, star (v k) * v k := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
      _ = v i * star (v j) := by rw [hsum, mul_one]
  · ext i j
    simp only [rankOneDensity, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply,
      smul_eq_mul, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
  · simp only [rankOneDensity, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply,
      dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

end D5.S3.Quantum.PureState.PureStateHandshake
