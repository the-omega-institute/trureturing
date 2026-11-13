/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveRealRecovery
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveRealRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integer-scale estimates recover real-scale sieve moments at the original modulus. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.SieveIntegerRecovery
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.SingularSeriesTail
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.RealLengthRescaling

/-! Real-scale recovery retains the modulus and dilates the interval endpoints. -/

open scoped BigOperators Topology
open Set Filter

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

private theorem sieve_real_rescale (Q : ℕ+) (H h a b : ℝ) (hh : 0 < h)
    (x : ZMod (Q : ℕ)) :
    sieveIntervalSum Q H a b x = sieveIntervalSum Q h (a * H / h) (b * H / h) x := by
  simp only [sieveIntervalSum, points, div_mul_cancel₀ _ hh.ne']

private theorem sieve_floor_scale_bounds :
    ∀ᶠ H : ℝ in atTop,
      let h : ℕ := ⌊H⌋₊
      3 ≤ h ∧ H ≤ 2 * (h : ℝ) ∧ Real.log H ≤ 2 * Real.log h ∧
      ∀ k : ℕ, k ≤ 4 → momentScale k h ≤ momentScale k H := by
  filter_upwards [eventually_ge_atTop (6 : ℝ)] with H hH
  have hH0 : 0 ≤ H := by linarith
  have hh : 3 ≤ ⌊H⌋₊ := (Nat.le_floor_iff hH0).2 (by norm_num; linarith)
  have hh3 : (3 : ℝ) ≤ (⌊H⌋₊ : ℝ) := by exact_mod_cast hh
  have hh0 : (0 : ℝ) < (⌊H⌋₊ : ℝ) := by linarith
  have hfloor : (⌊H⌋₊ : ℝ) ≤ H := Nat.floor_le hH0
  have hlt : H < (⌊H⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one H
  have hdouble : H ≤ 2 * (⌊H⌋₊ : ℝ) := by linarith
  have hlog : Real.log H ≤ 2 * Real.log (⌊H⌋₊ : ℝ) := by
    calc
      _ ≤ Real.log ((⌊H⌋₊ : ℝ) ^ 2) :=
        Real.log_le_log (by linarith) (by nlinarith)
      _ = _ := by rw [Real.log_pow]; norm_num
  refine ⟨hh, hdouble, hlog, ?_⟩
  intro k _hk
  have hlog0 : 0 ≤ Real.log (⌊H⌋₊ : ℝ) := Real.log_nonneg (by linarith)
  have hlogmono : Real.log (⌊H⌋₊ : ℝ) ≤ Real.log H := Real.log_le_log hh0 hfloor
  exact Real.rpow_le_rpow (mul_nonneg hh0.le hlog0)
    (mul_le_mul hfloor hlogmono hlog0 hH0) (by positivity)

private theorem sieve_real_uniform_transfer (k : ℕ) (hk : k = 3 ∨ k = 4)
    (F : ℕ+ → ℝ → (Fin k → ℝ) → (Fin k → ℝ) → ℝ)
    (hscale : ∀ Q H h a b, 0 < h →
      F Q H a b = F Q h (fun i => a i * H / h) (fun i => b i * H / h))
    (hsmall : UniformIntegerSmall k F) (M B : ℝ) (hM : 1 ≤ M) (hB : 1 ≤ B)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ H : ℝ in atTop, ∀ Q : ℕ+, Squarefree (Q : ℕ) → sieveDensity Q ≤ B * Real.log H →
      ∀ a b : Fin k → ℝ, admissible M a b → |F Q H a b| ≤ ε * momentScale k H := by
  have hk4 : k ≤ 4 := by rcases hk with rfl | rfl <;> norm_num
  have hint := hsmall (2 * M) (2 * B) (by linarith) (by linarith) ε hε
  have hfloor := (tendsto_nat_floor_atTop (α := ℝ)).eventually hint
  filter_upwards [hfloor, sieve_floor_scale_bounds, eventually_ge_atTop (6 : ℝ)]
    with H hi hb hH Q hQ hP a b hab
  obtain ⟨hh3, hdouble, hlog, hmono⟩ := hb
  have hh : (0 : ℝ) < (⌊H⌋₊ : ℝ) := by exact_mod_cast (by omega : 0 < ⌊H⌋₊)
  have hH0 : 0 ≤ H := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hP' : sieveDensity Q ≤ (2 * B) * Real.log (⌊H⌋₊ : ℝ) := by
    calc
      _ ≤ B * Real.log H := hP
      _ ≤ B * (2 * Real.log (⌊H⌋₊ : ℝ)) := mul_le_mul_of_nonneg_left hlog hB0
      _ = _ := by ring
  have hr0 : 0 ≤ H / (⌊H⌋₊ : ℝ) := div_nonneg hH0 hh.le
  have hr2 : H / (⌊H⌋₊ : ℝ) ≤ 2 := (div_le_iff₀ hh).2 hdouble
  have had : admissible (2 * M)
      (fun i => a i * H / (⌊H⌋₊ : ℝ)) (fun i => b i * H / (⌊H⌋₊ : ℝ)) := by
    convert rescaled_admissible M (H / (⌊H⌋₊ : ℝ)) k a b hr0 hr2 hab using 1 <;>
      (funext i; ring)
  rw [hscale Q H (⌊H⌋₊ : ℝ) a b hh]
  exact (hi Q hQ hP' _ _ had).trans (mul_le_mul_of_nonneg_left (hmono k hk4) hε.le)

private theorem sieve_moment_real_rescale (k : ℕ) (Q : ℕ+) (H h : ℝ)
    (a b : Fin k → ℝ) (hh : 0 < h) :
    sieveIntervalMoment Q H a b =
      sieveIntervalMoment Q h (fun i => a i * H / h) (fun i => b i * H / h) := by
  rw [sieve_interval_moment_eq_product_moment, sieve_interval_moment_eq_product_moment]
  congr 1
  funext i x
  exact sieve_real_rescale Q H h (a i) (b i) hh x

private theorem sieve_wick_defect_real_rescale (Q : ℕ+) (H h : ℝ)
    (a b : Fin 4 → ℝ) (hh : 0 < h) :
    sieveIntervalWickDefect Q H a b =
      sieveIntervalWickDefect Q h (fun i => a i * H / h) (fun i => b i * H / h) := by
  have he : (fun i => sieveIntervalSum Q H (a i) (b i)) =
      (fun i => sieveIntervalSum Q h (a i * H / h) (b i * H / h)) := by
    funext i x
    exact sieve_real_rescale Q H h (a i) (b i) hh x
  rw [sieve_interval_defect_eq_wick_defect, sieve_interval_defect_eq_wick_defect]
  rw [he]

private theorem sieve_primorial_interval_recovery (k : ℕ) (hk : k = 3 ∨ k = 4)
    (F : ℕ+ → ℝ → (Fin k → ℝ) → (Fin k → ℝ) → ℝ)
    (hscale : ∀ Q H h a b, 0 < h →
      F Q H a b = F Q h (fun i => a i * H / h) (fun i => b i * H / h))
    (hsmall : UniformIntegerSmall k F) :
    ∀ M : ℝ, 1 ≤ M → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ H : ℝ in atTop, ∀ a b : Fin k → ℝ, admissible M a b →
        |F (primorialSieveModulus M H) H a b| ≤ ε * momentScale k H := by
  intro M hM ε hε
  obtain ⟨B, _hB, hden⟩ := density_log_bound M hM
  have hreal := sieve_real_uniform_transfer k hk F hscale hsmall M (max B 1)
    hM (le_max_right _ _) ε hε
  filter_upwards [hreal, eventually_ge_atTop (2 : ℝ)] with H hbound hH a b hab
  have hQ : Squarefree (primorialSieveModulus M H : ℕ) :=
    squarefree_primorial (sieveCutoff M H)
  have hlog : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
  have hP : sieveDensity (primorialSieveModulus M H) ≤ max B 1 * Real.log H :=
    (hden H hH).trans (mul_le_mul_of_nonneg_right (le_max_left B 1) hlog)
  exact hbound (primorialSieveModulus M H) hQ hP a b hab

/-- Finite scalar moments and smoothed pairing estimates recover sharp real interval moments. -/
theorem finite_sieve_intervals (hMS : MSFinite) (hK : KuperbergSmoothed) :
    FiniteSieveIntervals := by
  constructor
  · exact sieve_primorial_interval_recovery 3 (Or.inl rfl) sieveIntervalMoment
      (fun Q H h a b hh => sieve_moment_real_rescale 3 Q H h a b hh)
      (sieve_integer_third hMS hK)
  · exact sieve_primorial_interval_recovery 4 (Or.inr rfl) sieveIntervalWickDefect
      (fun Q H h a b hh => sieve_wick_defect_real_rescale Q H h a b hh)
      (sieve_integer_fourth hMS hK)

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
