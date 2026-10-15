/- GID: D5/S3/Quantum/Analysis/FourierWindowFiniteRank
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/FourierWindowFiniteRank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite-measure Fourier windows admit ordered-monomial finite-rank approximations with explicit factorial operator-norm error, including zero-dimensional and zero-volume cases. -/
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Tactic

/-! Explicit finite-rank approximations of finite-measure Fourier windows. -/

noncomputable section

open MeasureTheory Filter FourierTransform
open scoped ENNReal NNReal Topology BigOperators ComplexConjugate
open scoped SchwartzMap ContDiff

namespace D5.S3.Quantum.Analysis.FourierWindowFiniteRank

set_option maxHeartbeats 8000000

theorem fourier_window_finite_rank_approximation :
    ∀ (n : ℕ)
      (A B : Set (EuclideanSpace ℝ (Fin n)))
      (a b : ℝ),
      ∀ (_ha : 0 ≤ a) (_hb : 0 ≤ b)
      (hA : MeasurableSet A) (hB : MeasurableSet B)
      (hμA : (volume : Measure (EuclideanSpace ℝ (Fin n))) A ≠ (∞ : ℝ≥0∞))
      (hμB : (volume : Measure (EuclideanSpace ℝ (Fin n))) B ≠ (∞ : ℝ≥0∞))
      (_hxa : ∀ x ∈ A, ‖x‖ ≤ a)
      (_hξb : ∀ ξ ∈ B, ‖ξ‖ ≤ b),
      let E := EuclideanSpace ℝ (Fin n)
      let μ : Measure E := volume
      let H := Lp ℂ 2 μ
      letI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
      let M
          (S : Set E)
          (hS : MeasurableSet S)
          (hμS : μ S ≠ (∞ : ℝ≥0∞)) : H →L[ℂ] H :=
        (ContinuousLinearMap.lsmul ℂ ℂ).holderL μ
          (∞ : ℝ≥0∞) 2 2
          (indicatorConstLp ∞ hS hμS (1 : ℂ))
      let MA : H →L[ℂ] H := M A hA hμA
      let MB : H →L[ℂ] H := M B hB hμB
      let F : H →L[ℂ] H :=
        (MeasureTheory.Lp.fourierTransformₗᵢ E ℂ : H →L[ℂ] H)
      let T : H →L[ℂ] H := MB ∘L F ∘L MA
      let q : ℂ := ((-2 * Real.pi : ℝ) : ℂ) * Complex.I
      let phase (x ξ : E) : ℂ :=
        q * ((inner ℝ x ξ : ℝ) : ℂ)
      let P (N : ℕ) (x ξ : E) : ℂ :=
        ∑ k ∈ Finset.range N,
          phase x ξ ^ k / (k.factorial : ℂ)
      let R : ℝ := 2 * Real.pi * a * b
      let mon (k : ℕ) (s : Fin k → Fin n) (x : E) : ℂ :=
        ((∏ j : Fin k, x (s j) : ℝ) : ℂ)
      let coeff (k : ℕ) : ℂ :=
        q ^ k / (k.factorial : ℂ)
      ∃ vin : (k : ℕ) → (Fin k → Fin n) → H,
      ∃ vout : (k : ℕ) → (Fin k → Fin n) → H,
        (∀ (k : ℕ) (s : Fin k → Fin n),
          ⇑(vin k s) =ᵐ[μ] A.indicator (mon k s)) ∧
        (∀ (k : ℕ) (s : Fin k → Fin n),
          ⇑(vout k s) =ᵐ[μ]
            (fun ξ => coeff k * B.indicator (mon k s) ξ)) ∧
        (∀ (k : ℕ) (s : Fin k → Fin n) (f : H),
          inner ℂ (vin k s) f =
            ∫ x in A, mon k s x * f x ∂μ) ∧
        let I (N : ℕ) := Σ k : Fin N, Fin (k : ℕ) → Fin n
        let TN (N : ℕ) : H →L[ℂ] H :=
          ∑ i : I N,
            InnerProductSpace.rankOne ℂ
              (vout (i.1 : ℕ) i.2)
              (vin (i.1 : ℕ) i.2)
        (∀ f : H,
          ⇑(T f) =ᵐ[μ]
            B.indicator
              (fun ξ : E =>
                ∫ x in A, Complex.exp (phase x ξ) * f x ∂μ)) ∧
        (∀ (N : ℕ) (f : H),
          ⇑(TN N f) =ᵐ[μ]
            B.indicator
              (fun ξ : E =>
                ∫ x in A, P N x ξ * f x ∂μ)) ∧
        (∀ N : ℕ,
          FiniteDimensional ℂ
            (Submodule.span ℂ
              (Set.range
                (fun i : I N => vin (i.1 : ℕ) i.2)))) ∧
        (∀ N : ℕ,
          FiniteDimensional ℂ
            (Submodule.span ℂ
              (Set.range
                (fun i : I N => vout (i.1 : ℕ) i.2)))) ∧
        (∀ N : ℕ,
          FiniteDimensional ℂ (TN N).toLinearMap.range) ∧
        (∀ N : ℕ, IsCompactOperator (TN N)) ∧
        TN 0 = 0 ∧
        (∀ N : ℕ,
          R / ((N + 1 : ℕ) : ℝ) ≤ (1 / 2 : ℝ) →
          ‖T - TN N‖ ≤
            Real.sqrt (μ.real A * μ.real B) *
              (2 * R ^ N / (N.factorial : ℝ))) ∧
        (∀ᶠ N : ℕ in atTop,
          R / ((N + 1 : ℕ) : ℝ) ≤ (1 / 2 : ℝ)) ∧
        Tendsto TN atTop (𝓝 T) ∧
        IsCompactOperator T ∧
        ((μ A = 0 ∨ μ B = 0) →
          T = 0 ∧ ∀ N : ℕ, TN N = 0) ∧
        (∀ N : ℕ,
          N ≠ 0 →
          n = 0 ∨ a = 0 ∨ b = 0 →
          T = TN N) := by
  intro n A B a b ha hb hA hB hμA hμB hxa hξb
  classical
  have hFourier :
      ∀ n : ℕ,
      let E := EuclideanSpace ℝ (Fin n)
      let μ : Measure E := volume
      let H := Lp ℂ 2 μ
      letI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
      let F := MeasureTheory.Lp.fourierTransformₗᵢ E ℂ
      (∀ (g : E → ℂ) (hg2 : MemLp g 2 μ) (_hg1 : Integrable g μ),
        (F (hg2.toLp g) : E → ℂ) =ᵐ[μ] (fun ξ => ∫ x, Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I) * g x ∂μ)) ∧
      (∀ (A : Set E) (hA : MeasurableSet A) (hAvol : μ A ≠ (∞ : ℝ≥0∞)) (f : H),
        let X : H →L[ℂ] H := (ContinuousLinearMap.lsmul ℂ ℂ).holderL μ (∞ : ℝ≥0∞) 2 2 (indicatorConstLp ∞ hA hAvol (1 : ℂ))
        (F (X f) : E → ℂ) =ᵐ[μ] (fun ξ => ∫ x in A, Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) *
              Complex.I) * f x ∂μ)) := by
    intro n
    classical
    let E := EuclideanSpace ℝ (Fin n)
    let μ : Measure E := volume
    let H := Lp ℂ 2 μ
    letI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
    let F : H ≃ₗᵢ[ℂ] H :=
      MeasureTheory.Lp.fourierTransformₗᵢ E ℂ
    have hIntegralBridge (g : E → ℂ) (hg2 : MemLp g 2 μ) (hg1 : Integrable g μ) : (F (hg2.toLp g) : E → ℂ) =ᵐ[μ] (fun ξ => ∫ x, Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I) *
                g x ∂μ) := by
      have hContinuous : Continuous (𝓕 g : E → ℂ) :=
        VectorFourier.fourierIntegral_continuous
          Real.continuous_fourierChar
          (innerSL ℝ (E := E)).continuous₂
          hg1
      have hLloc :
          LocallyIntegrable
            ((𝓕 (hg2.toLp g) : H) : E → ℂ) μ :=
        (Lp.memLp (𝓕 (hg2.toLp g) : H)).locallyIntegrable
          (by norm_num)
      have hGloc : LocallyIntegrable (𝓕 g : E → ℂ) μ :=
        hContinuous.locallyIntegrable
      have hClassical : ((𝓕 (hg2.toLp g) : H) : E → ℂ) =ᵐ[μ] (𝓕 g : E → ℂ) := by
        apply ae_eq_of_integral_contDiff_smul_eq hLloc hGloc
        intro φ hφ hφs
        have hφC :
            ContDiff ℝ ∞ (fun x : E => (φ x : ℂ)) :=
          Complex.ofRealCLM.contDiff.comp hφ
        have hφCs :
            HasCompactSupport (fun x : E => (φ x : ℂ)) :=
          hφs.comp_left (g := Complex.ofReal) (by simp)
        let ψ : 𝓢(E, ℂ) := hφCs.toSchwartzMap hφC
        have hψ (x : E) : ψ x = (φ x : ℂ) := rfl
        have hDistribution :=
          congrArg
            (fun t : TemperedDistribution E ℂ => t ψ)
            (Lp.fourier_toTemperedDistribution_eq (hg2.toLp g))
        have hTest : (∫ x, ψ x * (𝓕 (hg2.toLp g) : H) x ∂μ) =
              ∫ x, ψ x * (𝓕 g) x ∂μ := by
          calc
            (∫ x, ψ x * (𝓕 (hg2.toLp g) : H) x ∂μ)
                = ∫ x, (𝓕 ψ) x * (hg2.toLp g) x ∂μ := by
                    simpa only
                      [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply, smul_eq_mul]
                      using hDistribution.symm
            _ = ∫ x, (𝓕 ψ) x * g x ∂μ := by
                  apply integral_congr_ae
                  filter_upwards [hg2.coeFn_toLp] with x hx
                  rw [hx]
            _ = ∫ x, ψ x * (𝓕 g) x ∂μ := by
                  simpa only
                    [flip_innerₗ, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
                    using!
                      (VectorFourier.integral_bilin_fourierIntegral_eq_flip (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] ℂ →L[ℂ] ℂ)
                        (L := innerₗ E) (μ := μ) (ν := μ) Real.continuous_fourierChar continuous_inner ψ.integrable hg1)
          all_goals rfl
        simpa only [hψ, Complex.real_smul] using hTest
      have hKernel (ξ : E) : (𝓕 g) ξ =
            ∫ x,
              Complex.exp
                  (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I) *
                g x ∂μ := by
        simpa only [smul_eq_mul] using (Real.fourier_eq' g ξ)
      change
        ((𝓕 (hg2.toLp g) : H) : E → ℂ) =ᵐ[μ]
          (fun ξ => ∫ x, Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I) *
                g x ∂μ)
      exact hClassical.trans (Filter.Eventually.of_forall hKernel)
    refine ⟨hIntegralBridge, ?_⟩
    intro A hA hAvol f
    let mul : Lp ℂ ∞ μ →L[ℂ] H →L[ℂ] H :=
      (ContinuousLinearMap.lsmul ℂ ℂ).holderL μ
        (∞ : ℝ≥0∞) 2 2
    let window (A : Set E) (hA : MeasurableSet A) (hAvol : μ A ≠ (∞ : ℝ≥0∞)) : H →L[ℂ] H :=
      mul (indicatorConstLp ∞ hA hAvol (1 : ℂ))
    let X : H →L[ℂ] H := window A hA hAvol
    have hWindowIntegral (f : H) : (F (X f) : E → ℂ) =ᵐ[μ] (fun ξ => ∫ x in A, Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I) *
                f x ∂μ) := by
      let g : E → ℂ := A.indicator (fun x => f x)
      have hg2 : MemLp g 2 μ :=
        MemLp.indicator hA (Lp.memLp f)
      have hgsupport : ∀ x : E, x ∉ A → g x = 0 := by
        intro x hx
        simp only [g, Set.indicator_of_notMem hx]
      have hgMem1 : MemLp g 1 μ :=
        hg2.mono_exponent_of_measure_support_ne_top
          hgsupport hAvol (by norm_num)
      have hg1 : Integrable g μ :=
        memLp_one_iff_integrable.mp hgMem1
      let χA : Lp ℂ ∞ μ :=
        indicatorConstLp ∞ hA hAvol (1 : ℂ)
      have hχA : (χA : E → ℂ) =ᵐ[μ]
            A.indicator (fun _ => (1 : ℂ)) :=
        indicatorConstLp_coeFn
      have hXg : (X f : E → ℂ) =ᵐ[μ] g := by
        have hmul : (X f : E → ℂ) =ᵐ[μ] (fun x => χA x • f x) := by
          change
            ((ContinuousLinearMap.lsmul ℂ ℂ).holder 2 χA f : E → ℂ) =ᵐ[μ]
                (fun x => χA x • f x)
          exact
            (ContinuousLinearMap.lsmul ℂ ℂ).coeFn_holder χA f
        filter_upwards [hmul, hχA] with x hx hχx
        rw [hx, hχx]
        by_cases hxA : x ∈ A
        · simp [g, hxA]
        · simp [g, hxA]
      have hgX : hg2.toLp g = X f := by
        apply Lp.ext
        exact hg2.coeFn_toLp.trans hXg.symm
      have hFg := hIntegralBridge g hg2 hg1
      rw [hgX] at hFg
      filter_upwards [hFg] with ξ hξ
      calc
        (F (X f) : E → ℂ) ξ
            = ∫ x,
                Complex.exp
                    (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I) *
                  g x ∂μ := hξ
        _ = ∫ x,
              A.indicator
                (fun x => Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I) *
                    f x) x ∂μ := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall (fun x => by
                by_cases hxA : x ∈ A
                · simp only [g, Set.indicator_of_mem hxA]
                · simp only
                    [g, Set.indicator_of_notMem hxA, mul_zero])
        _ = ∫ x in A,
              Complex.exp
                  (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I) *
                f x ∂μ :=
              integral_indicator hA
    exact hWindowIntegral f
  let E := EuclideanSpace ℝ (Fin n)
  let μ : Measure E := volume
  let H := Lp ℂ 2 μ
  letI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  let M (S : Set E) (hS : MeasurableSet S) (hμS : μ S ≠ (∞ : ℝ≥0∞)) : H →L[ℂ] H :=
    (ContinuousLinearMap.lsmul ℂ ℂ).holderL μ
      (∞ : ℝ≥0∞) 2 2
      (indicatorConstLp ∞ hS hμS (1 : ℂ))
  let MA : H →L[ℂ] H := M A hA hμA
  let MB : H →L[ℂ] H := M B hB hμB
  let F : H →L[ℂ] H :=
    (MeasureTheory.Lp.fourierTransformₗᵢ E ℂ : H →L[ℂ] H)
  let T : H →L[ℂ] H := MB ∘L F ∘L MA
  let q : ℂ := ((-2 * Real.pi : ℝ) : ℂ) * Complex.I
  let phase (x ξ : E) : ℂ :=
    q * ((inner ℝ x ξ : ℝ) : ℂ)
  let P (N : ℕ) (x ξ : E) : ℂ :=
    ∑ k ∈ Finset.range N,
      phase x ξ ^ k / (k.factorial : ℂ)
  let R : ℝ := 2 * Real.pi * a * b
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  have hM_rep (S : Set E) (hS : MeasurableSet S) (hμS : μ S ≠ (∞ : ℝ≥0∞)) (f : H) :
      ⇑(M S hS hμS f) =ᵐ[μ] S.indicator (⇑f) := by
    let χS : Lp ℂ ∞ μ :=
      indicatorConstLp ∞ hS hμS (1 : ℂ)
    have hχS :
        ⇑χS =ᵐ[μ] S.indicator (fun _ => (1 : ℂ)) :=
      indicatorConstLp_coeFn
    have hmul :
        ⇑(M S hS hμS f) =ᵐ[μ]
          (fun x => χS x • f x) := by
      change
        ((ContinuousLinearMap.lsmul ℂ ℂ).holder 2 χS f : E → ℂ) =ᵐ[μ] (fun x => χS x • f x)
      exact (ContinuousLinearMap.lsmul ℂ ℂ).coeFn_holder χS f
    filter_upwards [hmul, hχS] with x hmulx hχx
    rw [hmulx, hχx]
    by_cases hxS : x ∈ S
    · simp [hxS]
    · simp [hxS]
  have hphase_native (x ξ : E) :
      phase x ξ =
        (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) *
          Complex.I) := by
    dsimp [phase, q]
    push_cast
    ring
  have hTrep (f : H) :
      ⇑(T f) =ᵐ[μ]
        B.indicator
          (fun ξ : E =>
            ∫ x in A, Complex.exp (phase x ξ) * f x ∂μ) := by
    have hFMA :
        ⇑(F (MA f)) =ᵐ[μ]
          (fun ξ : E => ∫ x in A, Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I) *
                f x ∂μ) := by
      exact (hFourier n).2 A hA hμA f
    have hMB := hM_rep B hB hμB (F (MA f))
    change
      ⇑(MB (F (MA f))) =ᵐ[μ]
        B.indicator
          (fun ξ : E => ∫ x in A, Complex.exp (phase x ξ) * f x ∂μ)
    filter_upwards [hMB, hFMA] with ξ hMBξ hFξ
    rw [hMBξ]
    by_cases hξ : ξ ∈ B
    · simp only [Set.indicator_of_mem hξ]
      rw [hFξ]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hphase_native]
    · simp [hξ]
  let mon (k : ℕ) (s : Fin k → Fin n) (x : E) : ℂ :=
    ((∏ j : Fin k, x (s j) : ℝ) : ℂ)
  let coeff (k : ℕ) : ℂ :=
    q ^ k / (k.factorial : ℂ)
  have hmon_cont (k : ℕ) (s : Fin k → Fin n) :
      Continuous (mon k s) := by
    dsimp [mon, E]
    fun_prop
  have hmon_conj (k : ℕ) (s : Fin k → Fin n) (x : E) :
      conj (mon k s x) = mon k s x := by
    simp [mon]
  have hmon_bound (k : ℕ) (s : Fin k → Fin n) (r : ℝ) (hr : 0 ≤ r) (x : E) (hx : ‖x‖ ≤ r) :
      ‖mon k s x‖ ≤ r ^ k := by
    calc
      ‖mon k s x‖ = ∏ j : Fin k, ‖x (s j)‖ := by
        simp [mon, norm_prod]
      _ ≤ ∏ _j : Fin k, r := by
        apply Finset.prod_le_prod₀
        · intro j hj
          exact norm_nonneg _
        · intro j hj
          exact (PiLp.norm_apply_le x (s j)).trans hx
      _ = r ^ k := by
        simp
  have hmon_mem (S : Set E) (hS : MeasurableSet S) (hμS : μ S ≠ (∞ : ℝ≥0∞)) (r : ℝ) (hr : 0 ≤ r) (hSr : ∀ x ∈ S, ‖x‖ ≤ r) (k : ℕ) (s : Fin k → Fin n) :
      MemLp (S.indicator (mon k s)) 2 μ := by
    apply
      (memLp_indicator_const 2 hS ((r ^ k : ℝ) : ℂ) (Or.inr hμS)).of_le
    · exact (hmon_cont k s).aestronglyMeasurable.indicator hS
    · filter_upwards [] with x
      by_cases hxs : x ∈ S
      · simpa [hxs, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hr k), abs_of_nonneg hr] using
          hmon_bound k s r hr x (hSr x hxs)
      · simp [hxs]
  let vwin (S : Set E) (hS : MeasurableSet S) (hμS : μ S ≠ (∞ : ℝ≥0∞)) (r : ℝ) (hr : 0 ≤ r) (hSr : ∀ x ∈ S, ‖x‖ ≤ r) (k : ℕ) (s : Fin k → Fin n) : H :=
    (hmon_mem S hS hμS r hr hSr k s).toLp
      (S.indicator (mon k s))
  let vin (k : ℕ) (s : Fin k → Fin n) : H :=
    vwin A hA hμA a ha hxa k s
  let vout (k : ℕ) (s : Fin k → Fin n) : H :=
    coeff k • vwin B hB hμB b hb hξb k s
  have hvin_rep (k : ℕ) (s : Fin k → Fin n) :
      ⇑(vin k s) =ᵐ[μ] A.indicator (mon k s) := by
    exact MemLp.coeFn_toLp
      (hmon_mem A hA hμA a ha hxa k s)
  have hvout_rep (k : ℕ) (s : Fin k → Fin n) :
      ⇑(vout k s) =ᵐ[μ]
        (fun ξ => coeff k * B.indicator (mon k s) ξ) := by
    filter_upwards
      [Lp.coeFn_smul (coeff k) (vwin B hB hμB b hb hξb k s),
       MemLp.coeFn_toLp (hmon_mem B hB hμB b hb hξb k s)]
      with ξ hsmul hrep
    change (vwin B hB hμB b hb hξb k s : E → ℂ) ξ =
      B.indicator (mon k s) ξ at hrep
    simpa only [vout, Pi.smul_apply, smul_eq_mul, hrep] using hsmul
  have hmon_integrable (S : Set E) (hS : MeasurableSet S) (hμS : μ S ≠ (∞ : ℝ≥0∞)) (r : ℝ) (hr : 0 ≤ r) (hSr : ∀ x ∈ S, ‖x‖ ≤ r) (k : ℕ) (s : Fin k → Fin n) (f : H) :
      Integrable (fun x => mon k s x * f x)
        (μ.restrict S) := by
    apply
      (integrableOn_Lp_of_measure_ne_top f
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) hμS).bdd_mul
    · exact (hmon_cont k s).aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem hS] with x hx
      exact hmon_bound k s r hr x (hSr x hx)
  have hinner (k : ℕ) (s : Fin k → Fin n) (f : H) :
      inner ℂ (vin k s) f =
        ∫ x in A, mon k s x * f x ∂μ := by
    rw [L2.inner_def, ← integral_indicator hA]
    apply integral_congr_ae
    filter_upwards [hvin_rep k s] with x hx
    by_cases hxs : x ∈ A
    · simp [hx, hxs, RCLike.inner_apply', hmon_conj, mul_comm]
    · simp [hx, hxs, RCLike.inner_apply']
  let I (N : ℕ) := Σ k : Fin N, Fin (k : ℕ) → Fin n
  let TN (N : ℕ) : H →L[ℂ] H :=
    ∑ i : I N,
      InnerProductSpace.rankOne ℂ
        (vout (i.1 : ℕ) i.2)
        (vin (i.1 : ℕ) i.2)
  have hTN_apply (N : ℕ) (f : H) :
      TN N f =
        ∑ i : I N,
          inner ℂ (vin (i.1 : ℕ) i.2) f •
            vout (i.1 : ℕ) i.2 := by
    simp [TN, InnerProductSpace.rankOne_apply]
  have hTN_zero : TN 0 = 0 := by
    simp [TN, I]
  have hdot (x ξ : E) : ((inner ℝ x ξ : ℝ) : ℂ) =
        ∑ j : Fin n, (ξ j : ℂ) * (x j : ℂ) := by
    change ((∑ j : Fin n, ξ j * x j : ℝ) : ℂ) = _
    simp [Complex.ofReal_sum, Complex.ofReal_mul]
  have hdot_pow (k : ℕ) (x ξ : E) : (((inner ℝ x ξ : ℝ) : ℂ) ^ k) =
        ∑ s : Fin k → Fin n, mon k s ξ * mon k s x := by
    rw [hdot]
    simpa [mon, Fintype.piFinset_univ, Finset.prod_mul_distrib] using
      (Finset.sum_pow' (Finset.univ : Finset (Fin n)) (fun j => (ξ j : ℂ) * (x j : ℂ)) k)
  have hP_expand (N : ℕ) (x ξ : E) :
      P N x ξ =
        ∑ i : I N,
          coeff (i.1 : ℕ) *
            mon (i.1 : ℕ) i.2 ξ *
            mon (i.1 : ℕ) i.2 x := by
    calc
      P N x ξ =
          ∑ k : Fin N,
            phase x ξ ^ (k : ℕ) / ((k : ℕ).factorial : ℂ) := by
        dsimp [P]
        exact
          (Fin.sum_univ_eq_sum_range (fun k => phase x ξ ^ k / (k.factorial : ℂ)) N).symm
      _ =
          ∑ k : Fin N, ∑ s : Fin (k : ℕ) → Fin n,
            coeff (k : ℕ) *
              mon (k : ℕ) s ξ *
              mon (k : ℕ) s x := by
        apply Finset.sum_congr rfl
        intro k hk
        dsimp [phase, coeff]
        rw [mul_pow, hdot_pow]
        simp only [Finset.mul_sum, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro s hs
        ring
      _ =
          ∑ i : I N,
            coeff (i.1 : ℕ) *
              mon (i.1 : ℕ) i.2 ξ *
              mon (i.1 : ℕ) i.2 x := by
        simp only [I, Fintype.sum_sigma]
  have hP_integrable (N : ℕ) (ξ : E) (f : H) :
      Integrable (fun x => P N x ξ * f x)
        (μ.restrict A) := by
    have hsum :
        Integrable
          (fun x => ∑ i : I N, (coeff (i.1 : ℕ) * mon (i.1 : ℕ) i.2 ξ) * (mon (i.1 : ℕ) i.2 x * f x))
          (μ.restrict A) := by
      apply integrable_finsetSum
      intro i hi
      exact
        (hmon_integrable A hA hμA a ha hxa (i.1 : ℕ) i.2 f).const_mul
            (coeff (i.1 : ℕ) * mon (i.1 : ℕ) i.2 ξ)
    apply hsum.congr
    filter_upwards [] with x
    rw [hP_expand, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hP_integral (N : ℕ) (ξ : E) (f : H) : (∫ x in A, P N x ξ * f x ∂μ) =
        ∑ i : I N,
          coeff (i.1 : ℕ) * mon (i.1 : ℕ) i.2 ξ *
            (∫ x in A, mon (i.1 : ℕ) i.2 x * f x ∂μ) := by
    calc
      (∫ x in A, P N x ξ * f x ∂μ) =
          ∫ x in A,
            ∑ i : I N,
              (coeff (i.1 : ℕ) * mon (i.1 : ℕ) i.2 ξ) *
                (mon (i.1 : ℕ) i.2 x * f x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [hP_expand, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ =
          ∑ i : I N,
            ∫ x in A,
              (coeff (i.1 : ℕ) * mon (i.1 : ℕ) i.2 ξ) *
                (mon (i.1 : ℕ) i.2 x * f x) ∂μ := by
        apply integral_finsetSum
        intro i hi
        exact
          (hmon_integrable A hA hμA a ha hxa (i.1 : ℕ) i.2 f).const_mul
              (coeff (i.1 : ℕ) * mon (i.1 : ℕ) i.2 ξ)
      _ =
          ∑ i : I N,
            coeff (i.1 : ℕ) * mon (i.1 : ℕ) i.2 ξ *
              (∫ x in A,
                mon (i.1 : ℕ) i.2 x * f x ∂μ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact integral_const_mul
          (coeff (i.1 : ℕ) * mon (i.1 : ℕ) i.2 ξ)
          (fun x => mon (i.1 : ℕ) i.2 x * f x)
  have hTN_rep (N : ℕ) (f : H) :
      ⇑(TN N f) =ᵐ[μ]
        B.indicator
          (fun ξ : E =>
            ∫ x in A, P N x ξ * f x ∂μ) := by
    rw [hTN_apply]
    have heach :
        ∀ᵐ ξ ∂μ, ∀ i : I N,
          (inner ℂ (vin (i.1 : ℕ) i.2) f • vout (i.1 : ℕ) i.2) ξ =
          inner ℂ (vin (i.1 : ℕ) i.2) f *
            (coeff (i.1 : ℕ) *
              B.indicator (mon (i.1 : ℕ) i.2) ξ) := by
      rw [ae_all_iff]
      intro i
      filter_upwards
        [Lp.coeFn_smul (inner ℂ (vin (i.1 : ℕ) i.2) f) (vout (i.1 : ℕ) i.2),
         hvout_rep (i.1 : ℕ) i.2]
        with ξ hsmul hout
      simpa [Pi.smul_apply, smul_eq_mul, hout] using hsmul
    filter_upwards
      [Lp.coeFn_finsetSum Finset.univ (fun i : I N => inner ℂ (vin (i.1 : ℕ) i.2) f • vout (i.1 : ℕ) i.2),
       heach]
      with ξ hsum heachξ
    simp only [Finset.sum_apply] at hsum
    rw [hsum]
    by_cases hξ : ξ ∈ B
    · simp only [Set.indicator_of_mem hξ]
      rw [hP_integral]
      apply Finset.sum_congr rfl
      intro i hi
      rw [heachξ i, hinner]
      simp only [Set.indicator_of_mem hξ]
      ring
    · simp only [Set.indicator_of_notMem hξ]
      apply Finset.sum_eq_zero
      intro i hi
      rw [heachξ i]
      simp [hξ]
  let InputSpan (N : ℕ) : Submodule ℂ H :=
    Submodule.span ℂ
      (Set.range (fun i : I N => vin (i.1 : ℕ) i.2))
  let OutputSpan (N : ℕ) : Submodule ℂ H :=
    Submodule.span ℂ
      (Set.range (fun i : I N => vout (i.1 : ℕ) i.2))
  have hInputSpanFinite (N : ℕ) :
      FiniteDimensional ℂ (InputSpan N) := by
    exact FiniteDimensional.span_of_finite ℂ
      (Set.finite_range (fun i : I N => vin (i.1 : ℕ) i.2))
  have hOutputSpanFinite (N : ℕ) :
      FiniteDimensional ℂ (OutputSpan N) := by
    exact FiniteDimensional.span_of_finite ℂ
      (Set.finite_range (fun i : I N => vout (i.1 : ℕ) i.2))
  have hRange (N : ℕ) : (TN N).toLinearMap.range ≤ OutputSpan N := by
    rintro y ⟨f, rfl⟩
    change TN N f ∈ OutputSpan N
    rw [hTN_apply]
    apply (OutputSpan N).sum_mem
    intro i hi
    apply (OutputSpan N).smul_mem
    exact Submodule.subset_span ⟨i, rfl⟩
  have hFiniteRank (N : ℕ) :
      FiniteDimensional ℂ (TN N).toLinearMap.range := by
    letI : FiniteDimensional ℂ (OutputSpan N) :=
      hOutputSpanFinite N
    exact FiniteDimensional.of_injective
      (Submodule.inclusion (hRange N))
      (Submodule.inclusion_injective (hRange N))
  have hTN_compact (N : ℕ) : IsCompactOperator (TN N) := by
    letI : FiniteDimensional ℂ (OutputSpan N) :=
      hOutputSpanFinite N
    let V : H →L[ℂ] OutputSpan N :=
      (TN N).codRestrict (OutputSpan N)
        (fun f => hRange N ⟨f, rfl⟩)
    have hV : IsCompactOperator V :=
      isCompactOperator_of_locallyCompactSpace_dom V
    have hcomp :
        IsCompactOperator ((OutputSpan N).subtypeL ∘L V) := by
      exact hV.clm_comp (OutputSpan N).subtypeL
    simpa [V] using hcomp
  have hphase_bound (x ξ : E) (hx : x ∈ A) (hξ : ξ ∈ B) :
      ‖phase x ξ‖ ≤ R := by
    have hab :
        |inner ℝ x ξ| ≤ a * b :=
      (abs_real_inner_le_norm x ξ).trans
        (mul_le_mul (hxa x hx) (hξb ξ hξ) (norm_nonneg ξ) ha)
    calc
      ‖phase x ξ‖ =
          (2 * Real.pi) * |inner ℝ x ξ| := by
        simp [phase, q, norm_mul, abs_mul, abs_of_nonneg Real.pi_pos.le]
      _ ≤ (2 * Real.pi) * (a * b) :=
        mul_le_mul_of_nonneg_left hab (by positivity)
      _ = R := by
        dsimp [R]
        ring
  have hKernelError (N : ℕ) (hN : R / ((N + 1 : ℕ) : ℝ) ≤ (1 / 2 : ℝ)) (x ξ : E) (hx : x ∈ A) (hξ : ξ ∈ B) :
      ‖Complex.exp (phase x ξ) - P N x ξ‖ ≤
        2 * R ^ N / (N.factorial : ℝ) := by
    have hp := hphase_bound x ξ hx hξ
    have hratio :
        ‖phase x ξ‖ / (N.succ : ℝ) ≤ (1 / 2 : ℝ) := by
      calc
        ‖phase x ξ‖ / (N.succ : ℝ) ≤ R / (N.succ : ℝ) := by
          gcongr
        _ ≤ (1 / 2 : ℝ) := by
          simpa [Nat.succ_eq_add_one] using hN
    calc
      ‖Complex.exp (phase x ξ) - P N x ξ‖ ≤
          ‖phase x ξ‖ ^ N / (N.factorial : ℝ) * 2 := by
        simpa [P] using
          (Complex.exp_bound' (x := phase x ξ) (n := N) hratio)
      _ ≤ R ^ N / (N.factorial : ℝ) * 2 := by
        gcongr
      _ = 2 * R ^ N / (N.factorial : ℝ) := by
        ring
  have hphase_degenerate (hdeg : n = 0 ∨ a = 0 ∨ b = 0) (x ξ : E) (hx : x ∈ A) (hξ : ξ ∈ B) :
      phase x ξ = 0 := by
    rcases hdeg with hn | hz
    · subst n
      simp [phase, E, PiLp.inner_apply]
    · have hRzero : R = 0 := by
        rcases hz with hza | hzb
        · simp [R, hza]
        · simp [R, hzb]
      apply norm_eq_zero.mp
      apply le_antisymm
      · simpa [hRzero] using hphase_bound x ξ hx hξ
      · exact norm_nonneg _
  have hKernelExactDegenerate (hdeg : n = 0 ∨ a = 0 ∨ b = 0) (N : ℕ) (hN : N ≠ 0) (x ξ : E) (hx : x ∈ A) (hξ : ξ ∈ B) :
      Complex.exp (phase x ξ) - P N x ξ = 0 := by
    have hz := hphase_degenerate hdeg x ξ hx hξ
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hN
    subst N
    simp [P, hz, Finset.sum_range_succ', pow_succ]
  have hExpUnit (x ξ : E) :
      ‖Complex.exp (phase x ξ)‖ = 1 := by
    simp [phase, q, Complex.norm_exp]
  have hExpIntegrable (ξ : E) (f : H) :
      Integrable
        (fun x => Complex.exp (phase x ξ) * f x)
        (μ.restrict A) := by
    apply
      (integrableOn_Lp_of_measure_ne_top f
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) hμA).bdd_mul
    · have hc : Continuous
          (fun x : E => Complex.exp (phase x ξ)) := by
        dsimp [phase]
        fun_prop
      exact hc.aestronglyMeasurable.restrict
    · filter_upwards [] with x
      exact le_of_eq (hExpUnit x ξ)
  have hResidualRep (N : ℕ) (f : H) :
      ⇑((T - TN N) f) =ᵐ[μ]
        B.indicator
          (fun ξ : E => ∫ x in A, (Complex.exp (phase x ξ) - P N x ξ) *
                f x ∂μ) := by
    change ⇑(T f - TN N f) =ᵐ[μ] _
    filter_upwards
      [Lp.coeFn_sub (T f) (TN N f), hTrep f, hTN_rep N f]
      with ξ hsub hTξ hTNξ
    simp only [Pi.sub_apply] at hsub
    rw [hsub, hTξ, hTNξ]
    by_cases hξ : ξ ∈ B
    · simp only [Set.indicator_of_mem hξ]
      rw [← integral_sub (hExpIntegrable ξ f) (hP_integrable N ξ f)]
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    · simp [hξ]
  let WindowKernelNormBound : Prop :=
    ∀ (S : H →L[ℂ] H) (κ : E → E → ℂ) (c : ℝ),
      0 ≤ c →
      (∀ ξ : E, Continuous (κ ξ)) →
      (∀ ξ ∈ B, ∀ x ∈ A, ‖κ ξ x‖ ≤ c) →
      (∀ f : H, ⇑(S f) =ᵐ[μ] B.indicator (fun ξ : E => ∫ x in A, κ ξ x * f x ∂μ)) →
      ‖S‖ ≤ Real.sqrt (μ.real A * μ.real B) * c
  have hWindowKernelNorm : WindowKernelNormBound := by
    dsimp only [WindowKernelNormBound]
    intro S κ c hc hκcont hκbound hSrep
    have hOneNorm (C : Set E) (hC : MeasurableSet C) (hμC : μ C ≠ (∞ : ℝ≥0∞)) :
        ‖indicatorConstLp (μ := μ) 2 hC hμC (1 : ℝ)‖ =
          Real.sqrt (μ.real C) := by
      simpa [Real.sqrt_eq_rpow] using
        (norm_indicatorConstLp (p := (2 : ℝ≥0∞)) (μ := μ) (hs := hC) (hμs := hμC) (c := (1 : ℝ))
          (by norm_num)
          (by norm_num))
    apply S.opNorm_le_bound
      (mul_nonneg (Real.sqrt_nonneg _) hc)
    intro f
    have hfA : Integrable (⇑f) (μ.restrict A) := by
      exact integrableOn_Lp_of_measure_ne_top f
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) hμA
    let g : Lp ℝ 2 μ :=
      MemLp.toLp
        (fun x : E => ‖f x‖)
        ((Lp.memLp f).norm)
    have hg_rep :
        ⇑g =ᵐ[μ] (fun x : E => ‖f x‖) := by
      exact MemLp.coeFn_toLp ((Lp.memLp f).norm)
    have hg_norm : ‖g‖ = ‖f‖ := by
      apply le_antisymm
      · apply Lp.norm_le_norm_of_ae_le
        filter_upwards [hg_rep] with x hx
        simpa only [hx, norm_norm] using
          (le_rfl : ‖f x‖ ≤ ‖f x‖)
      · apply Lp.norm_le_norm_of_ae_le
        filter_upwards [hg_rep] with x hx
        simpa only [hx, norm_norm] using
          (le_rfl : ‖f x‖ ≤ ‖f x‖)
    have hIntegralNorm_eq_inner : (∫ x in A, ‖f x‖ ∂μ) =
          inner ℝ
            (indicatorConstLp (μ := μ) 2 hA hμA (1 : ℝ))
            g := by
      calc
        (∫ x in A, ‖f x‖ ∂μ) =
            ∫ x in A, g x ∂μ := by
          exact integral_congr_ae
            (ae_restrict_of_ae hg_rep.symm)
        _ =
            inner ℝ
              (indicatorConstLp (μ := μ) 2 hA hμA (1 : ℝ))
              g :=
          (L2.inner_indicatorConstLp_one (𝕜 := ℝ) hA hμA g).symm
    have hL1Bound : (∫ x in A, ‖f x‖ ∂μ) ≤
          Real.sqrt (μ.real A) * ‖f‖ := by
      rw [hIntegralNorm_eq_inner]
      calc
        inner ℝ
            (indicatorConstLp (μ := μ) 2 hA hμA (1 : ℝ))
            g ≤
            |inner ℝ
              (indicatorConstLp (μ := μ) 2 hA hμA (1 : ℝ))
              g| :=
          le_abs_self _
        _ ≤
            ‖indicatorConstLp (μ := μ) 2 hA hμA (1 : ℝ)‖ *
              ‖g‖ :=
          abs_real_inner_le_norm _ _
        _ = Real.sqrt (μ.real A) * ‖f‖ := by
          rw [hOneNorm A hA hμA, hg_norm]
    have hKernelIntegrable (ξ : E) (hξ : ξ ∈ B) :
        Integrable
          (fun x : E => κ ξ x * f x)
          (μ.restrict A) := by
      apply hfA.bdd_mul
      · exact (hκcont ξ).aestronglyMeasurable.restrict
      · filter_upwards [ae_restrict_mem hA] with x hx
        exact hκbound ξ hξ x hx
    have hPointwise (ξ : E) (hξ : ξ ∈ B) :
        ‖∫ x in A, κ ξ x * f x ∂μ‖ ≤
          c * (Real.sqrt (μ.real A) * ‖f‖) := by
      calc
        ‖∫ x in A, κ ξ x * f x ∂μ‖ ≤
            ∫ x in A, ‖κ ξ x * f x‖ ∂μ :=
          norm_integral_le_integral_norm
            (μ := μ.restrict A)
            (fun x : E => κ ξ x * f x)
        _ ≤ ∫ x in A, c * ‖f x‖ ∂μ := by
          apply integral_mono_ae
            (hKernelIntegrable ξ hξ).norm
            (hfA.norm.const_mul c)
          filter_upwards [ae_restrict_mem hA] with x hx
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right
            (hκbound ξ hξ x hx)
            (norm_nonneg (f x))
        _ = c * (∫ x in A, ‖f x‖ ∂μ) :=
          integral_const_mul c (fun x : E => ‖f x‖)
        _ ≤ c * (Real.sqrt (μ.real A) * ‖f‖) :=
          mul_le_mul_of_nonneg_left hL1Bound hc
    let uB : Lp ℝ 2 μ :=
      indicatorConstLp (μ := μ) 2 hB hμB (1 : ℝ)
    have huB_rep :
        ⇑uB =ᵐ[μ] B.indicator (fun _ : E => (1 : ℝ)) := by
      exact indicatorConstLp_coeFn
    have huB_norm : ‖uB‖ = Real.sqrt (μ.real B) := by
      exact hOneNorm B hB hμB
    have hDomination :
        ∀ᵐ ξ ∂μ,
          ‖(S f) ξ‖ ≤
            (c * (Real.sqrt (μ.real A) * ‖f‖)) * ‖uB ξ‖ := by
      filter_upwards [hSrep f, huB_rep] with ξ hSfξ huBξ
      rw [hSfξ, huBξ]
      by_cases hξ : ξ ∈ B
      · simpa only
          [Set.indicator_of_mem hξ, norm_one, mul_one]
          using hPointwise ξ hξ
      · simp only
          [Set.indicator_of_notMem hξ, norm_zero, mul_zero, le_refl]
    calc
      ‖S f‖ ≤
          (c * (Real.sqrt (μ.real A) * ‖f‖)) * ‖uB‖ :=
        Lp.norm_le_mul_norm_of_ae_le_mul hDomination
      _ =
          (Real.sqrt (μ.real A * μ.real B) * c) * ‖f‖ := by
        rw [huB_norm, Real.sqrt_mul (show 0 ≤ μ.real A from measureReal_nonneg) (μ.real B)]
        ring
  have hError (N : ℕ) (hN : R / ((N + 1 : ℕ) : ℝ) ≤ (1 / 2 : ℝ)) :
      ‖T - TN N‖ ≤
        Real.sqrt (μ.real A * μ.real B) *
          (2 * R ^ N / (N.factorial : ℝ)) := by
    apply hWindowKernelNorm
      (T - TN N)
      (fun ξ x => Complex.exp (phase x ξ) - P N x ξ)
      (2 * R ^ N / (N.factorial : ℝ))
    · positivity
    · intro ξ
      dsimp [phase, P]
      fun_prop
    · intro ξ hξ x hx
      exact hKernelError N hN x ξ hx hξ
    · intro f
      exact hResidualRep N f
  have hRatioEventually :
      ∀ᶠ N : ℕ in atTop,
        R / ((N + 1 : ℕ) : ℝ) ≤ (1 / 2 : ℝ) := by
    obtain ⟨K, hK⟩ := exists_nat_gt (2 * R)
    filter_upwards [eventually_ge_atTop K] with N hKN
    have hcast : (K : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hKN
    apply (div_le_iff₀
      (by positivity : 0 < ((N + 1 : ℕ) : ℝ))).2
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have hDecay :
      Tendsto
        (fun N : ℕ => Real.sqrt (μ.real A * μ.real B) * (2 * R ^ N / (N.factorial : ℝ)))
        atTop (𝓝 0) := by
    simpa [mul_div_assoc] using
      ((FloorSemiring.tendsto_pow_div_factorial_atTop R).const_mul 2).const_mul
        (Real.sqrt (μ.real A * μ.real B))
  have hTendsto : Tendsto TN atTop (𝓝 T) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall
        (fun N => norm_nonneg (TN N - T))
    · filter_upwards [hRatioEventually] with N hN
      simpa only [norm_sub_rev] using hError N hN
    · exact hDecay
  have hCompact : IsCompactOperator T := by
    exact isCompactOperator_of_tendsto hTendsto
      (Filter.Eventually.of_forall hTN_compact)
  have hPBound (N : ℕ) (x ξ : E) (hx : x ∈ A) (hξ : ξ ∈ B) :
      ‖P N x ξ‖ ≤
        ∑ k ∈ Finset.range N,
          R ^ k / (k.factorial : ℝ) := by
    calc
      ‖P N x ξ‖ ≤
          ∑ k ∈ Finset.range N,
            ‖phase x ξ ^ k / (k.factorial : ℂ)‖ := by
        exact norm_sum_le _ _
      _ =
          ∑ k ∈ Finset.range N,
            ‖phase x ξ‖ ^ k / (k.factorial : ℝ) := by
        simp only [norm_div, norm_pow, Complex.norm_natCast]
      _ ≤
          ∑ k ∈ Finset.range N,
            R ^ k / (k.factorial : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        gcongr
        exact hphase_bound x ξ hx hξ
  have hZeroVolume (hz : μ A = 0 ∨ μ B = 0) :
      T = 0 ∧ ∀ N : ℕ, TN N = 0 := by
    have hVolumeFactor :
        Real.sqrt (μ.real A * μ.real B) = 0 := by
      rcases hz with hzA | hzB
      · simp [measureReal_def, hzA]
      · simp [measureReal_def, hzB]
    have hTbound :
        ‖T‖ ≤ Real.sqrt (μ.real A * μ.real B) * (1 : ℝ) := by
      apply hWindowKernelNorm
        T
        (fun ξ x => Complex.exp (phase x ξ))
        1
      · norm_num
      · intro ξ
        dsimp [phase]
        fun_prop
      · intro ξ hξ x hx
        exact le_of_eq (hExpUnit x ξ)
      · exact hTrep
    have hTzero : T = 0 := by
      apply norm_eq_zero.mp
      apply le_antisymm
      · simpa only [hVolumeFactor, zero_mul, norm_zero] using hTbound
      · exact norm_nonneg _
    refine ⟨hTzero, ?_⟩
    intro N
    have hTNbound :
        ‖TN N‖ ≤
          Real.sqrt (μ.real A * μ.real B) *
            (∑ k ∈ Finset.range N,
              R ^ k / (k.factorial : ℝ)) := by
      apply hWindowKernelNorm
        (TN N)
        (fun ξ x => P N x ξ)
        (∑ k ∈ Finset.range N, R ^ k / (k.factorial : ℝ))
      · positivity
      · intro ξ
        dsimp [P, phase]
        fun_prop
      · intro ξ hξ x hx
        exact hPBound N x ξ hx hξ
      · exact hTN_rep N
    apply norm_eq_zero.mp
    apply le_antisymm
    · simpa only [hVolumeFactor, zero_mul, norm_zero] using hTNbound
    · exact norm_nonneg _
  have hDegenerateExact (N : ℕ) (hN : N ≠ 0) (hdeg : n = 0 ∨ a = 0 ∨ b = 0) :
      T = TN N := by
    have hnorm : ‖T - TN N‖ ≤ 0 := by
      have hbound :
          ‖T - TN N‖ ≤
            Real.sqrt (μ.real A * μ.real B) * (0 : ℝ) := by
        apply hWindowKernelNorm
          (T - TN N)
          (fun ξ x => Complex.exp (phase x ξ) - P N x ξ)
          0
        · exact le_rfl
        · intro ξ
          dsimp [phase, P]
          fun_prop
        · intro ξ hξ x hx
          simp only
            [hKernelExactDegenerate hdeg N hN x ξ hx hξ, norm_zero]
          exact le_rfl
        · intro f
          exact hResidualRep N f
      simpa using hbound
    have hz : ‖T - TN N‖ = 0 :=
      le_antisymm hnorm (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  exact
    ⟨vin, vout, hvin_rep, hvout_rep, hinner, hTrep, hTN_rep, hInputSpanFinite, hOutputSpanFinite, hFiniteRank, hTN_compact, hTN_zero, hError, hRatioEventually, hTendsto, hCompact, hZeroVolume, hDegenerateExact⟩
end D5.S3.Quantum.Analysis.FourierWindowFiniteRank
