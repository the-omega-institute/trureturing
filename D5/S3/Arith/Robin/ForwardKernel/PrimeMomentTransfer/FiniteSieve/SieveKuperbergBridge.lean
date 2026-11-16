/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveKuperbergBridge
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveKuperbergBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kuperberg exponential sum bounds imply the smoothed finite sieve moment bounds. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.SieveSmoothMomentBridge
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.SieveFourierAdmissibility

/-! Smooth interval admissibility and the moment identity transfer the raw bounds. -/

open scoped BigOperators

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

private theorem weighted_wick_defect_eq_raw (Q : ℕ+) (hQ : Squarefree (Q : ℕ))
    (h : ℕ) (hh : 0 < h) (f : Fin 4 → ℝ → ℝ) (hf : ∀ i, SmoothPositiveWeight (f i)) :
    (sieveWickDefect Q (fun i => sieveWeightedSum Q h (f i)) : ℂ) = kuperbergRawWickDefect Q h f := by
  have hp (i j : Fin 4) :
      (sieveProductMoment Q ![sieveWeightedSum Q h (f i), sieveWeightedSum Q h (f j)] : ℂ) =
        kuperbergRawMoment Q h ![f i, f j] := by
    have hm := sieve_weighted_moment_eq_raw 2 Q hQ h hh ![f i, f j]
      (by intro t; fin_cases t <;> exact hf _)
    have he : (fun t => sieveWeightedSum Q h (![f i, f j] t)) =
        ![sieveWeightedSum Q h (f i), sieveWeightedSum Q h (f j)] := by
      funext t
      fin_cases t <;> rfl
    rw [he] at hm
    exact hm
  unfold sieveWickDefect sieveWickPairing kuperbergRawWickDefect
  push_cast
  rw [sieve_weighted_moment_eq_raw 4 Q hQ h hh f hf, hp, hp, hp, hp, hp, hp]

/-- The exponential-sum hypothesis supplies the smoothed finite-sieve bounds. -/
theorem kuperberg_raw_implies_smoothed (hK : KuperbergRaw) : KuperbergSmoothed := by
  constructor
  · intro δ hδ a b hab
    let f : Fin 3 → ℝ → ℝ := fun i => smoothedInterval δ hδ (a i) (b i)
    have hf (i : Fin 3) := smooth_interval_admissible δ hδ (a i) (b i) (hab i).1 (hab i).2
    obtain ⟨C, hC, hbound⟩ := hK.third f (fun i => (hf i).1) (fun i => (hf i).2)
    refine ⟨C, hC, ?_⟩
    intro Q hQ h hh
    have hm := sieve_weighted_moment_eq_raw 3 Q hQ h (by omega) f (fun i => (hf i).1)
    have hb := hbound Q hQ h hh
    rw [← hm] at hb
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hb
  · intro δ hδ a b hab
    let f : Fin 4 → ℝ → ℝ := fun i => smoothedInterval δ hδ (a i) (b i)
    have hf (i : Fin 4) := smooth_interval_admissible δ hδ (a i) (b i) (hab i).1 (hab i).2
    obtain ⟨C, hC, hbound⟩ := hK.fourth f (fun i => (hf i).1) (fun i => (hf i).2)
    refine ⟨C, hC, ?_⟩
    intro Q hQ h hh
    have hm := weighted_wick_defect_eq_raw Q hQ h (by omega) f (fun i => (hf i).1)
    have hb := hbound Q hQ h hh
    rw [← hm] at hb
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hb

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
