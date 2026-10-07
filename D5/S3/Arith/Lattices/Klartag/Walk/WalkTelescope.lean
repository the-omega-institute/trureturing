/- GID: D5/S3/Arith/Lattices/Klartag/Walk/WalkTelescope
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Walk/WalkTelescope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian matrix walk, filtration and stopped increments. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Walk.ChainWalk
import D5.S3.Arith.Lattices.Klartag.State.Padding

open D5.S3.Arith.Lattices.Klartag.Completion
open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Contact
open D5.S3.Arith.Lattices.Klartag.Gaussian
open D5.S3.Arith.Lattices.Klartag.State
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag

open MeasureTheory
open ProbabilityTheory
open Set
open Real
open scoped ENNReal NNReal

theorem sum_fin_ite_lt {N k : ℕ} (hk : k ≤ N) (g : ℕ → ℝ) :
    ∑ i : Fin N, (if (i : ℕ) < k then g (i : ℕ) else 0) = ∑ i ∈ Finset.range k, g i := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < k then g i else 0) N,
    ← Finset.sum_subset (s₁ := Finset.range k) (s₂ := Finset.range N)
      (fun x hx => Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hx) hk))
      (fun x _ hx => if_neg (by simpa using hx))]
  exact Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.1 hi))

/-- **The padding construction's increment vector.**  The `i`-th coordinate is the negated padded
increment: the martingale difference `ΔM_i` plus the padding `c_i·η_i`. -/
noncomputable def padIncVec {Ω₁ : Type*} (M c : ℕ → Ω₁ → ℝ) (N : ℕ)
    (ω : Ω₁ × (Fin N → ℝ)) : Fin N → ℝ :=
  fun i => -((M ((i : ℕ) + 1) ω.1 - M (i : ℕ) ω.1) + c (i : ℕ) ω.1 * ω.2 i)

theorem measurable_padIncVec {Ω₁ : Type*} [MeasurableSpace Ω₁] {M c : ℕ → Ω₁ → ℝ}
    (hM : ∀ j, Measurable (M j)) (hc : ∀ i, Measurable (c i)) (N : ℕ) :
    Measurable (padIncVec M c N) := by
  refine measurable_pi_iff.mpr fun i => ?_
  exact ((((hM ((i : ℕ) + 1)).comp measurable_fst).sub ((hM (i : ℕ)).comp measurable_fst)).add
    (((hc (i : ℕ)).comp measurable_fst).mul
      ((measurable_pi_apply i).comp measurable_snd))).neg

/-- **`walkSum_padded_eq`** — `Padding.padded_tail_of_increments`' `hincw`, proved.  The only
proviso is that `M 0` is the deterministic constant `M₀`, which is exactly Klartag's initial gap
read at time zero. -/
theorem walkSum_padded_eq {Ω₁ : Type*} (M c : ℕ → Ω₁ → ℝ) {M₀ : ℝ} {N : ℕ}
    (hzero : ∀ ω₁, M 0 ω₁ = M₀) (k : ℕ) (hk : k ≤ N) (ω : Ω₁ × (Fin N → ℝ)) :
    walkSum k (padIncVec M c N ω) = -(paddedProc M M₀ c k ω) := by
  have hpt : ∀ i : Fin N,
      (if (i : ℕ) < k then padIncVec M c N ω i else 0)
        = -(if (i : ℕ) < k then M ((i : ℕ) + 1) ω.1 - M (i : ℕ) ω.1 else 0)
          - (if (i : ℕ) < k then c (i : ℕ) ω.1 * ω.2 i else 0) := by
    intro i
    unfold padIncVec
    split_ifs <;> ring
  have hdrift : ∑ i : Fin N, (if (i : ℕ) < k then M ((i : ℕ) + 1) ω.1 - M (i : ℕ) ω.1 else 0)
      = M k ω.1 - M₀ := by
    rw [sum_fin_ite_lt hk (fun i => M (i + 1) ω.1 - M i ω.1),
      Finset.sum_range_sub (fun i => M i ω.1) k, hzero ω.1]
  show ∑ i : Fin N, (if (i : ℕ) < k then padIncVec M c N ω i else 0) = _
  rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, hdrift]
  show -(M k ω.1 - M₀) - padSum c k ω = -((M k ω.1 - M₀) + padSum c k ω)
  ring

/-- **The transported Proposition 4.1, with `hincw` discharged.**  `ChainWalk.tail_of_transport''`
and `ChainWalk.chainRaw2_of_walk` take `hprop`; this is `hprop` with everything proved except the
padded increment vector's law. -/
theorem hprop_of_hincl {Ω₁ : Type*} [MeasurableSpace Ω₁] {P₁ : Measure Ω₁}
    [IsProbabilityMeasure P₁] {k : ℕ} {δ : ℝ≥0} {M c : ℕ → Ω₁ → ℝ}
    (hM : ∀ j, Measurable (M j)) (hc : ∀ i, Measurable (c i))
    {a₀ u t : ℝ} (ht : 0 < t) (hM₀ : 0 < a₀ - (u ^ 2)⁻¹)
    (hzero : ∀ ω₁, M 0 ω₁ = a₀ - (u ^ 2)⁻¹)
    (hv : (((k • δ : ℝ≥0)) : ℝ) = t * 1 ^ 2)
    (hincl : (P₁.prod (Measure.pi fun _ : Fin k => gaussianReal 0 δ)).map (padIncVec M c k)
      = Measure.pi fun _ : Fin k => gaussianReal 0 δ) :
    P₁ {ω₁ | ∃ j ≤ k, M j ω₁ ≤ 0} ≤ ENNReal.ofReal (4 * Phi (yOf a₀ t u)) :=
  hit_tail_yOf hM hc ht hM₀ hv (measurable_padIncVec hM hc k)
    (fun j hj ω => walkSum_padded_eq M c hzero j hj ω) hincl

/-- **The hitting event is scale-invariant.**  The chain's walk `⟪A_k, q y⟫ − 1` and its
normalisation by `‖q y‖ = ‖x‖²` — the form `yOf`'s argument is written in — have the same hitting
event, so `hprop_of_hincl` may be read at either. -/
theorem hitSet_smul {Ω₁ : Type*} {M : ℕ → Ω₁ → ℝ} {s : ℝ} (hs : 0 < s) (k : ℕ) :
    {ω₁ : Ω₁ | ∃ j ≤ k, s * M j ω₁ ≤ 0} = {ω₁ : Ω₁ | ∃ j ≤ k, M j ω₁ ≤ 0} := by
  ext ω₁
  constructor
  · rintro ⟨j, hj, hle⟩
    exact ⟨j, hj, nonpos_of_mul_nonpos_left (by linarith) hs⟩
  · rintro ⟨j, hj, hle⟩
    exact ⟨j, hj, mul_nonpos_of_nonneg_of_nonpos hs.le hle⟩

end D5.S3.Arith.Lattices.Klartag
