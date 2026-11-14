/- GID: D5/S3/Analytic/Probability/CompactStrassen
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/CompactStrassen
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: CompactStrassen for compact scalar martingale transport. -/
/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0, retained in docs/reports/licenses/econlib-strassen/LICENSE.txt.
Authors: Daniel Lyng
Ported from danlyng/Econlib revision d7bd9477476cade1c6695c8891746048ceddc52f.
Modified for the host probability-measure API, native conditional expectation,
existing library suppliers, and a construction-oriented module organization.
-/
import D5.S3.Analytic.Probability.ConditionalMeanApproximation
import D5.S3.Analytic.Probability.NoncompactQuantile
import D5.S3.Analytic.Probability.FiniteMartingaleCoupling
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov


open MeasureTheory Set Filter Topology

section
open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Econlib.Probability

/-- **Tightness on a compact support.** A sequence of probability measures on `ℝ × ℝ` all
concentrated on the compact set `Icc a b ×ˢ Icc a b` is a tight family. -/
private lemma isTight_of_supportsOn_Icc_prod (a b : ℝ) (π : ℕ → ProbabilityMeasure (ℝ × ℝ))
    (hπ : ∀ n, (π n).toMeasure (Icc a b ×ˢ Icc a b) = 1) :
    IsTightMeasureSet { ρ : Measure (ℝ × ℝ) | ∃ n, (π n : Measure (ℝ × ℝ)) = ρ } := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  refine ⟨Icc a b ×ˢ Icc a b, isCompact_Icc.prod isCompact_Icc, ?_⟩
  rintro ρ ⟨n, rfl⟩
  have hmeas : MeasurableSet (Icc a b ×ˢ Icc a b : Set (ℝ × ℝ)) :=
    measurableSet_Icc.prod measurableSet_Icc
  have h0 : (π n : Measure (ℝ × ℝ)) (Icc a b ×ˢ Icc a b)ᶜ = 0 :=
    (MeasureTheory.prob_compl_eq_zero_iff hmeas).mpr (hπ n)
  rw [h0]
  exact le_of_lt hε

/-- **Weak-limit extraction.** A sequence of probability measures on `ℝ × ℝ` all concentrated on a
compact square admits a weakly convergent subsequence. -/
private lemma exists_weak_limit_of_supportsOn_Icc_prod (a b : ℝ)
    (π : ℕ → ProbabilityMeasure (ℝ × ℝ))
    (hπ : ∀ n, (π n).toMeasure (Icc a b ×ˢ Icc a b) = 1) :
    ∃ (φ : ℕ → ℕ) (_ : StrictMono φ) (πInf : ProbabilityMeasure (ℝ × ℝ)),
      Tendsto (fun n => π (φ n)) atTop (𝓝 πInf) ∧
      πInf.toMeasure (Icc a b ×ˢ Icc a b) = 1 := by
  -- Step 1: tightness of the range.
  have htight : IsTightMeasureSet
      {x : Measure (ℝ × ℝ) | ∃ μ ∈ Set.range π, (μ : Measure (ℝ × ℝ)) = x} := by
    have h := isTight_of_supportsOn_Icc_prod a b π hπ
    refine h.subset ?_
    rintro x ⟨μ, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, rfl⟩
  -- Step 2: Prokhorov gives compactness of closure.
  have hcomp : IsCompact (closure (Set.range π)) :=
    isCompact_closure_of_isTightMeasureSet htight
  -- Step 3: Extract convergent subsequence via sequential compactness (metrizable).
  have hmem : ∀ n, π n ∈ closure (Set.range π) := fun n =>
    subset_closure ⟨n, rfl⟩
  obtain ⟨πInf, _hmemInf, φ, hmono, htend⟩ := hcomp.tendsto_subseq (x := π) hmem
  refine ⟨φ, hmono, πInf, htend, ?_⟩
  -- Step 4: the limit still has mass 1 on the compact square (portmanteau closed).
  have hclosed : IsClosed (Icc a b ×ˢ Icc a b : Set (ℝ × ℝ)) :=
    isClosed_Icc.prod isClosed_Icc
  have hmeas : MeasurableSet (Icc a b ×ˢ Icc a b : Set (ℝ × ℝ)) :=
    measurableSet_Icc.prod measurableSet_Icc
  -- By portmanteau: `limsup ((π (φ n)) F) ≤ πInf F` (in ENNReal via toMeasure).
  have hlimsup :=
    MeasureTheory.ProbabilityMeasure.limsup_measure_closed_le_of_tendsto htend hclosed
  -- Each `(π (φ n)).toMeasure F = 1` (from `hπ`), so the limsup of the constant-1 sequence is 1.
  have hlimsup_eq : Filter.limsup
      (fun i => (((π ∘ φ) i : ProbabilityMeasure (ℝ × ℝ)) : Measure (ℝ × ℝ))
        (Icc a b ×ˢ Icc a b)) Filter.atTop = 1 := by
    have hfun : (fun i => (((π ∘ φ) i : ProbabilityMeasure (ℝ × ℝ)) :
        Measure (ℝ × ℝ)) (Icc a b ×ˢ Icc a b))
        = fun _ => (1 : ENNReal) := funext fun i => hπ (φ i)
    rw [hfun, Filter.limsup_const]
  rw [hlimsup_eq] at hlimsup
  -- We have `1 ≤ πInf F`. Combined with `πInf F ≤ 1` we get equality.
  have hge : (1 : ENNReal) ≤ (πInf : Measure (ℝ × ℝ)) (Icc a b ×ˢ Icc a b) := hlimsup
  exact le_antisymm MeasureTheory.prob_le_one hge

/-- Marginal pushforward is continuous in the weak-* topology on probability measures. -/
private lemma ProbabilityMeasure.continuous_map_fst :
    Continuous (fun π : ProbabilityMeasure (ℝ × ℝ) =>
      ProbabilityMeasure.map π (Prod.fst : ℝ × ℝ → ℝ)) :=
  MeasureTheory.ProbabilityMeasure.continuous_map (f := (Prod.fst : ℝ × ℝ → ℝ))
    continuous_fst

/-- Marginal pushforward is continuous in the weak-* topology on probability measures. -/
private lemma ProbabilityMeasure.continuous_map_snd :
    Continuous (fun π : ProbabilityMeasure (ℝ × ℝ) =>
      ProbabilityMeasure.map π (Prod.snd : ℝ × ℝ → ℝ)) :=
  MeasureTheory.ProbabilityMeasure.continuous_map (f := (Prod.snd : ℝ × ℝ → ℝ))
    continuous_snd

/-- **Weak-limit marginals.** If `πₙ → πInf` weakly and each `πₙ` has marginals `(μₙ, νₙ)` with
`μₙ → μ`, `νₙ → ν`, then `πInf` has marginals `(μ, ν)`. -/
lemma IsCoupling.coupling_of_weak_limit {μ ν : ProbDist ℝ} {μ_seq ν_seq : ℕ → ProbDist ℝ}
    {π_seq : ℕ → ProbDist (ℝ × ℝ)} {πInf : ProbDist (ℝ × ℝ)}
    (hπcoup : ∀ n, IsCoupling (μ_seq n) (ν_seq n) (π_seq n))
    (hπlim : Tendsto (fun n => (π_seq n : ProbabilityMeasure (ℝ × ℝ))) atTop (𝓝 πInf))
    (hμlim : Tendsto (fun n => (μ_seq n : ProbabilityMeasure ℝ)) atTop (𝓝 μ))
    (hνlim : Tendsto (fun n => (ν_seq n : ProbabilityMeasure ℝ)) atTop (𝓝 ν)) :
    IsCoupling μ ν πInf := by
  -- Use continuity of the marginal pushforward composed with convergence of `πₙ → πInf`.
  have hfst_lim : Tendsto
      (fun n => ProbabilityMeasure.map (π_seq n : ProbabilityMeasure (ℝ × ℝ))
        (Prod.fst : ℝ × ℝ → ℝ)) atTop
      (𝓝 (ProbabilityMeasure.map (πInf : ProbabilityMeasure (ℝ × ℝ))
        (Prod.fst : ℝ × ℝ → ℝ))) :=
    (ProbabilityMeasure.continuous_map_fst.tendsto _).comp hπlim
  have hsnd_lim : Tendsto
      (fun n => ProbabilityMeasure.map (π_seq n : ProbabilityMeasure (ℝ × ℝ))
        (Prod.snd : ℝ × ℝ → ℝ)) atTop
      (𝓝 (ProbabilityMeasure.map (πInf : ProbabilityMeasure (ℝ × ℝ))
        (Prod.snd : ℝ × ℝ → ℝ))) :=
    (ProbabilityMeasure.continuous_map_snd.tendsto _).comp hπlim
  -- Each `ProbabilityMeasure.map (π_seq n) ... = μ_seq n` by the coupling hypothesis.
  -- `ProbDist.map (π_seq n) Prod.fst/.snd = μ_seq n / ν_seq n`, and `ProbDist.map` is
  -- definitionally `ProbabilityMeasure.map ... aemeasurable`.
  have hfst_eq : ∀ n, ProbabilityMeasure.map (π_seq n : ProbabilityMeasure (ℝ × ℝ))
      (Prod.fst : ℝ × ℝ → ℝ) = (μ_seq n : ProbabilityMeasure ℝ) :=
    fun n => (hπcoup n).fst_probability_marginal
  have hsnd_eq : ∀ n, ProbabilityMeasure.map (π_seq n : ProbabilityMeasure (ℝ × ℝ))
      (Prod.snd : ℝ × ℝ → ℝ) = (ν_seq n : ProbabilityMeasure ℝ) :=
    fun n => (hπcoup n).snd_probability_marginal
  -- Substitute into the convergence.
  rw [funext hfst_eq] at hfst_lim
  rw [funext hsnd_eq] at hsnd_lim
  -- Now both limits: `μ_seq n → map πInf fst` and `μ_seq n → μ`. Unique limit.
  refine ⟨?_, ?_⟩
  · exact congrArg (fun d : ProbabilityMeasure ℝ => (d : Measure ℝ))
      (tendsto_nhds_unique hμlim hfst_lim |>.symm)
  · exact congrArg (fun d : ProbabilityMeasure ℝ => (d : Measure ℝ))
      (tendsto_nhds_unique hνlim hsnd_lim |>.symm)

end Econlib.Probability
end

section
open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Econlib.Probability

/-- **Tested martingale identity passes to the weak limit (continuous φ).** If each `πₙ` is a
martingale coupling concentrated on `Icc a b × Icc a b`, then any weak limit has the tested
identity for every bounded continuous `φ`. -/
lemma tested_martingale_of_weak_limit {a b : ℝ}
    {π_seq : ℕ → ProbDist (ℝ × ℝ)} {πInf : ProbDist (ℝ × ℝ)}
    (hπsupp : ∀ n, (π_seq n).toMeasure (Icc a b ×ˢ Icc a b) = 1)
    (hInfSupp : πInf.toMeasure (Icc a b ×ˢ Icc a b) = 1)
    (hπmart : ∀ n, ∀ φ : ℝ → ℝ, Measurable φ → (∃ M, ∀ x, |φ x| ≤ M) →
      ∫ p, (p.2 - p.1) * φ p.1 ∂(π_seq n).toMeasure = 0)
    (hπlim : Tendsto (fun n => (π_seq n : ProbabilityMeasure (ℝ × ℝ))) atTop (𝓝 πInf))
    (φ : ℝ → ℝ) (hφ_cont : Continuous φ) (hφ_bdd : ∃ M, ∀ x, |φ x| ≤ M) :
    ∫ p, (p.2 - p.1) * φ p.1 ∂πInf.toMeasure = 0 := by
  -- Extract `a ≤ b` from the support hypothesis; otherwise `Icc a b = ∅` but
  -- `πInf (Icc a b × Icc a b) = 1 ≠ 0`.
  have hab : a ≤ b := by
    by_contra hab'
    rw [Set.Icc_eq_empty hab'] at hInfSupp
    simp at hInfSupp
  -- Build a bounded continuous ψ : ℝ × ℝ → ℝ that equals (y - x) * φ(x) on Icc × Icc.
  -- Let `c : ℝ → ℝ` be the clamp `x ↦ max a (min b x)` (Set.projIcc applied).
  set c : ℝ → ℝ := fun x => max a (min b x) with hc_def
  have hc_cont : Continuous c :=
    (continuous_const.max (continuous_const.min continuous_id))
  have hc_mem : ∀ x, c x ∈ Icc a b := fun x =>
    ⟨le_max_left a _, max_le hab (min_le_left b x)⟩
  have hc_id_on_Icc : ∀ x ∈ Icc a b, c x = x := by
    rintro x ⟨hxa, hxb⟩
    simp only [hc_def]
    have hmin : min b x = x := min_eq_right hxb
    rw [hmin, max_eq_right hxa]
  -- Define ψ := (c ∘ snd - c ∘ fst) * (φ ∘ c ∘ fst).
  set ψ : ℝ × ℝ → ℝ := fun p => (c p.2 - c p.1) * φ (c p.1) with hψ_def
  have hψ_cont : Continuous ψ := by
    refine Continuous.mul ?_ ?_
    · exact (hc_cont.comp continuous_snd).sub (hc_cont.comp continuous_fst)
    · exact hφ_cont.comp (hc_cont.comp continuous_fst)
  -- ψ is bounded: |c(y) - c(x)| ≤ b - a ≥ 0, and |φ(c(x))| ≤ M.
  obtain ⟨M, hM⟩ := hφ_bdd
  have hψ_bdd : ∀ p, |ψ p| ≤ (b - a) * M := by
    intro p
    have h1 : |c p.2 - c p.1| ≤ b - a := by
      have hcx := hc_mem p.1
      have hcy := hc_mem p.2
      rcases le_or_gt (c p.2) (c p.1) with h | h
      · rw [abs_of_nonpos (sub_nonpos.mpr h)]
        have : c p.1 - c p.2 ≤ b - a := sub_le_sub hcx.2 hcy.1
        linarith
      · rw [abs_of_pos (sub_pos.mpr h)]
        exact sub_le_sub hcy.2 hcx.1
    have h2 : |φ (c p.1)| ≤ M := hM (c p.1)
    calc |ψ p| = |c p.2 - c p.1| * |φ (c p.1)| := by rw [hψ_def]; exact abs_mul _ _
      _ ≤ (b - a) * M := by
          have hM0 : 0 ≤ M := le_trans (abs_nonneg _) h2
          have hba0 : 0 ≤ b - a := by linarith
          exact mul_le_mul h1 h2 (abs_nonneg _) hba0
  -- Bounded continuous version as `BoundedContinuousFunction`.
  let ψBC : BoundedContinuousFunction (ℝ × ℝ) ℝ :=
    BoundedContinuousFunction.mkOfBound
      ⟨ψ, hψ_cont⟩ (2 * ((b - a) * M)) (by
        intro p q
        have hp := hψ_bdd p
        have hq := hψ_bdd q
        calc dist (ψ p) (ψ q) = |ψ p - ψ q| := by rw [Real.dist_eq]
          _ ≤ |ψ p| + |ψ q| := abs_sub _ _
          _ ≤ (b - a) * M + (b - a) * M := add_le_add hp hq
          _ = 2 * ((b - a) * M) := by ring)
  -- On the compact square, ψ equals (y - x) * φ(x).
  have hψ_eq : ∀ p ∈ Icc a b ×ˢ Icc a b, ψ p = (p.2 - p.1) * φ p.1 := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    simp only [hψ_def, hc_id_on_Icc x hx, hc_id_on_Icc y hy]
  -- Convert: `∫ ψ dπ = ∫ (y - x) * φ x dπ` whenever π is concentrated on the square.
  have hint_eq : ∀ (ρ : Measure (ℝ × ℝ)) (_hρ : ρ (Icc a b ×ˢ Icc a b) = 1)
      [_hρprob : IsProbabilityMeasure ρ],
      ∫ p, ψ p ∂ρ = ∫ p, (p.2 - p.1) * φ p.1 ∂ρ := by
    intro ρ hρ _
    refine MeasureTheory.integral_congr_ae ?_
    have hmeas : MeasurableSet (Icc a b ×ˢ Icc a b : Set (ℝ × ℝ)) :=
      measurableSet_Icc.prod measurableSet_Icc
    have : ∀ᵐ p ∂ρ, p ∈ Icc a b ×ˢ Icc a b := by
      rw [ae_iff]
      have hcompl : ρ (Icc a b ×ˢ Icc a b)ᶜ = 0 :=
        (MeasureTheory.prob_compl_eq_zero_iff hmeas).mpr hρ
      exact hcompl
    filter_upwards [this] with p hp
    exact hψ_eq p hp
  -- Apply the weak convergence on bounded continuous ψBC.
  have hconv :=
    (MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hπlim) ψBC
  -- Each LHS is 0 via the martingale identity and support-based equality.
  have hzero : ∀ n, ∫ p, ψBC p ∂((π_seq n : ProbabilityMeasure (ℝ × ℝ)) :
      Measure (ℝ × ℝ)) = 0 := by
    intro n
    rw [show (fun p => ψBC p) = ψ from rfl,
      hint_eq ((π_seq n : ProbabilityMeasure (ℝ × ℝ)) : Measure (ℝ × ℝ)) (hπsupp n)]
    exact hπmart n (fun x => φ x) hφ_cont.measurable ⟨M, hM⟩
  have hconv0 : Tendsto
      (fun n => ∫ p, ψBC p ∂((π_seq n : ProbabilityMeasure (ℝ × ℝ)) :
        Measure (ℝ × ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.congr fun n => (hzero n).symm
  -- Unique limit: `∫ ψ dπInf = 0`.
  have heq := tendsto_nhds_unique hconv hconv0
  -- Convert back to `∫ (y - x) * φ x dπInf = 0`.
  have hψBC_eq : (fun p => ψBC p) = ψ := rfl
  rw [hψBC_eq] at heq
  rw [← hint_eq πInf.toMeasure hInfSupp]
  exact heq

/-- **Tested martingale identity lifts to measurable φ.** If the tested identity holds for every
bounded continuous `φ` against a coupling concentrated on a compact square, then it holds for every
bounded measurable `φ`. -/
lemma tested_martingale_measurable_of_continuous {a b : ℝ} {π : ProbDist (ℝ × ℝ)}
    (_hsupp : π.toMeasure (Icc a b ×ˢ Icc a b) = 1)
    (hint_fst : Integrable (fun p : ℝ × ℝ => p.1) π.toMeasure)
    (hint_snd : Integrable (fun p : ℝ × ℝ => p.2) π.toMeasure)
    (hcts : ∀ φ : ℝ → ℝ, Continuous φ → (∃ M, ∀ x, |φ x| ≤ M) →
      ∫ p, (p.2 - p.1) * φ p.1 ∂π.toMeasure = 0) :
    ∀ φ : ℝ → ℝ, Measurable φ → (∃ M, ∀ x, |φ x| ≤ M) →
      ∫ p, (p.2 - p.1) * φ p.1 ∂π.toMeasure = 0 := by
  exact NoncompactQuantile.tested_measurable_of_continuous hint_fst hint_snd hcts

/-- **Main weak-limit theorem for martingale couplings.** Given a sequence
`πₙ : IsMartingaleCoupling μₙ νₙ πₙ` with all `πₙ` concentrated on `Icc a b × Icc a b` and
marginals converging weakly to `μ, ν`, every weak limit point of `πₙ` is a martingale coupling of
`(μ, ν)`. -/
theorem IsMartingaleCoupling.martingaleCoupling_of_weak_limit {a b : ℝ}
    {μ ν : ProbDist ℝ} {μ_seq ν_seq : ℕ → ProbDist ℝ}
    {π_seq : ℕ → ProbDist (ℝ × ℝ)} {πInf : ProbDist (ℝ × ℝ)}
    (_hμ_supp : μ.supportsOn (Icc a b)) (_hν_supp : ν.supportsOn (Icc a b))
    (hπcoup : ∀ n, IsMartingaleCoupling (μ_seq n) (ν_seq n) (π_seq n))
    (hπsupp : ∀ n, (π_seq n).toMeasure (Icc a b ×ˢ Icc a b) = 1)
    (hInfSupp : πInf.toMeasure (Icc a b ×ˢ Icc a b) = 1)
    (hπlim : Tendsto (fun n => (π_seq n : ProbabilityMeasure (ℝ × ℝ))) atTop (𝓝 πInf))
    (hμlim : Tendsto (fun n => (μ_seq n : ProbabilityMeasure ℝ)) atTop (𝓝 μ))
    (hνlim : Tendsto (fun n => (ν_seq n : ProbabilityMeasure ℝ)) atTop (𝓝 ν)) :
    IsMartingaleCoupling μ ν πInf := by
  -- Step 1: marginals via `IsCoupling.coupling_of_weak_limit`.
  have hπcoup' : ∀ n, IsCoupling (μ_seq n) (ν_seq n) (π_seq n) := fun n =>
    ⟨(hπcoup n).fst_measure, (hπcoup n).snd_measure⟩
  have hcoup : IsCoupling μ ν πInf :=
    IsCoupling.coupling_of_weak_limit hπcoup' hπlim hμlim hνlim
  -- Step 2: integrability of coordinate projections against πInf.
  have hmeas_sq : MeasurableSet (Icc a b ×ˢ Icc a b : Set (ℝ × ℝ)) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hae_mem : ∀ᵐ p ∂πInf.toMeasure, p ∈ Icc a b ×ˢ Icc a b := by
    rw [ae_iff]
    exact (MeasureTheory.prob_compl_eq_zero_iff hmeas_sq).mpr hInfSupp
  -- Helper: `|x| ≤ max |a| |b|` when `x ∈ Icc a b`.
  have habs_bound : ∀ x ∈ Icc a b, |x| ≤ max |a| |b| :=
    fun _ ⟨hxa, hxb⟩ => abs_le_max_abs_abs hxa hxb
  have hint_fst : Integrable (fun p : ℝ × ℝ => p.1) πInf.toMeasure :=
    Integrable.mono' (integrable_const (max |a| |b|))
      measurable_fst.aestronglyMeasurable
      (by filter_upwards [hae_mem] with p hp
          rw [Real.norm_eq_abs]; exact habs_bound p.1 hp.1)
  have hint_snd : Integrable (fun p : ℝ × ℝ => p.2) πInf.toMeasure :=
    Integrable.mono' (integrable_const (max |a| |b|))
      measurable_snd.aestronglyMeasurable
      (by filter_upwards [hae_mem] with p hp
          rw [Real.norm_eq_abs]; exact habs_bound p.2 hp.2)
  -- Step 3: tested martingale property for continuous φ, via weak limit.
  have hπmart : ∀ n, ∀ φ : ℝ → ℝ, Measurable φ → (∃ M, ∀ x, |φ x| ≤ M) →
      ∫ p, (p.2 - p.1) * φ p.1 ∂(π_seq n).toMeasure = 0 := fun n φ hφm hφb =>
    (hπcoup n).martingale φ hφm hφb
  have hcts : ∀ φ : ℝ → ℝ, Continuous φ → (∃ M, ∀ x, |φ x| ≤ M) →
      ∫ p, (p.2 - p.1) * φ p.1 ∂πInf.toMeasure = 0 := fun φ hφ_cont hφ_bdd =>
    tested_martingale_of_weak_limit hπsupp hInfSupp hπmart hπlim φ hφ_cont hφ_bdd
  -- Step 4: lift from continuous to measurable.
  have hmart : ∀ φ : ℝ → ℝ, Measurable φ → (∃ M, ∀ x, |φ x| ≤ M) →
      ∫ p, (p.2 - p.1) * φ p.1 ∂πInf.toMeasure = 0 :=
    tested_martingale_measurable_of_continuous hInfSupp hint_fst hint_snd hcts
  -- Assemble.
  exact {
    fst_marginal := hcoup.fst_probability_marginal
    snd_marginal := hcoup.snd_probability_marginal
    integrable_fst := hint_fst
    integrable_snd := hint_snd
    martingale := hmart
  }

end Econlib.Probability
end

section
open MeasureTheory Set Filter Topology

namespace Econlib.Probability

/-- **Strassen's theorem (hard direction)** (Strassen 1965). On compact support `[a, b]`, the
convex order `μ ≼cx[a,b] ν` implies the existence of a martingale coupling `π : ProbDist (ℝ × ℝ)`
with `Prod.fst`-marginal `μ`, `Prod.snd`-marginal `ν`, and `𝔼π[Y ∣ X] = X` almost surely. -/
private theorem exists_martingaleCoupling_of_convexOrderOnIcc (a b : ℝ) {μ ν : ProbDist ℝ}
    (h : ConvexOrderOnIcc a b μ ν) :
    ∃ π : ProbDist (ℝ × ℝ), IsMartingaleCoupling μ ν π := by
  have hμ_supp : μ.supportsOn (Icc a b) := h.support_left
  have hν_supp : ν.supportsOn (Icc a b) := h.support_right
  obtain ⟨p, q, happ⟩ := exists_discrete_approximation h
  rcases happ with ⟨hcx, hn_pos, hsameN, hp_uniform, hq_uniform, hpIcc, hqIcc, hp_lim, hq_lim⟩
  have h_exists : ∀ n, ∃ π : ProbDist (ℝ × ℝ),
      IsMartingaleCoupling (p n).toProbDist (q n).toProbDist π := fun n =>
    DiscreteLaw.exists_martingaleCoupling_uniform (p n) (q n) (hn_pos n) (hsameN n)
      (hp_uniform n) (hq_uniform n) (hcx n)
  classical
  let π : ℕ → ProbDist (ℝ × ℝ) := fun n => (h_exists n).choose
  have hπmart : ∀ n, IsMartingaleCoupling (p n).toProbDist (q n).toProbDist (π n) := fun n =>
    (h_exists n).choose_spec
  have hp_supp : ∀ n, (p n).toProbDist.supportsOn (Icc a b) := fun n =>
    (p n).toProbDist_supportsOn_of_atoms_mem measurableSet_Icc (hpIcc n)
  have hq_supp : ∀ n, (q n).toProbDist.supportsOn (Icc a b) := fun n =>
    (q n).toProbDist_supportsOn_of_atoms_mem measurableSet_Icc (hqIcc n)
  have hπcoup : ∀ n, IsCoupling (p n).toProbDist (q n).toProbDist (π n) := fun n =>
    ⟨(hπmart n).fst_measure, (hπmart n).snd_measure⟩
  have hπ_supp : ∀ n, (π n).toMeasure (Icc a b ×ˢ Icc a b) = 1 := fun n =>
    (hπcoup n).supportsOn_Icc_prod (hp_supp n) (hq_supp n)
  obtain ⟨φ, hmono, πInf, hπlim, hInfSupp⟩ :=
    exists_weak_limit_of_supportsOn_Icc_prod a b π hπ_supp
  have hp_lim_sub : Tendsto
      (fun n => ((p (φ n)).toProbDist : ProbabilityMeasure ℝ)) atTop (𝓝 μ) :=
    hp_lim.comp hmono.tendsto_atTop
  have hq_lim_sub : Tendsto
      (fun n => ((q (φ n)).toProbDist : ProbabilityMeasure ℝ)) atTop (𝓝 ν) :=
    hq_lim.comp hmono.tendsto_atTop
  refine ⟨πInf, ?_⟩
  exact IsMartingaleCoupling.martingaleCoupling_of_weak_limit
    (μ_seq := fun n => (p (φ n)).toProbDist) (ν_seq := fun n => (q (φ n)).toProbDist)
    (π_seq := fun n => π (φ n))
    hμ_supp hν_supp (fun n => hπmart (φ n)) (fun n => hπ_supp (φ n)) hInfSupp
    hπlim hp_lim_sub hq_lim_sub

end Econlib.Probability

namespace Econlib.Probability

lemma IsMartingaleCoupling.condExp_snd_eq_fst {μ ν : ProbDist ℝ}
    {π : ProbDist (ℝ × ℝ)} (h : IsMartingaleCoupling μ ν π) :
    π.toMeasure[Prod.snd | (borel ℝ).comap Prod.fst] =ᵐ[π.toMeasure] Prod.fst := by
  have hm : ((borel ℝ).comap (Prod.fst : ℝ × ℝ → ℝ)) ≤ (inferInstance : MeasurableSpace (ℝ × ℝ)) :=
    (measurable_fst : Measurable (Prod.fst : ℝ × ℝ → ℝ)).comap_le
  have hxm : StronglyMeasurable[((borel ℝ).comap (Prod.fst : ℝ × ℝ → ℝ))] (Prod.fst : ℝ × ℝ → ℝ) :=
    (comap_measurable _).stronglyMeasurable
  apply Filter.EventuallyEq.symm
  refine ae_eq_condExp_of_forall_setIntegral_eq hm h.integrable_snd
    (fun _ _ _ => h.integrable_fst.integrableOn) ?_ hxm.aestronglyMeasurable
  intro s hs _
  obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
  let ψ : ℝ → ℝ := t.indicator (fun _ => 1)
  have hψ : Measurable ψ := measurable_const.indicator ht
  have hbψ : ∃ M, ∀ x, |ψ x| ≤ M := by
    refine ⟨1, ?_⟩
    intro x
    by_cases hx : x ∈ t <;> simp [ψ, hx]
  have heq := h.martingale ψ hψ hbψ
  have htest : (fun p : ℝ × ℝ => (p.2 - p.1) * ψ p.1) =
      (Prod.fst ⁻¹' t).indicator (fun p : ℝ × ℝ => p.2 - p.1) := by
    funext p
    by_cases hp : p.1 ∈ t <;> simp [ψ, hp]
  rw [htest, integral_indicator (ht.preimage measurable_fst),
    integral_sub h.integrable_snd.integrableOn h.integrable_fst.integrableOn] at heq
  linarith

private lemma isMartingaleCoupling_of_condExp {a b : ℝ} {μ ν : ProbDist ℝ}
    (hμ : μ.toMeasure (Icc a b) = 1) (hν : ν.toMeasure (Icc a b) = 1)
    {π : ProbDist (ℝ × ℝ)}
    (hfst : π.toMeasure.map Prod.fst = μ.toMeasure)
    (hsnd : π.toMeasure.map Prod.snd = ν.toMeasure)
    (hce : π.toMeasure[Prod.snd | (borel ℝ).comap Prod.fst] =ᵐ[π.toMeasure] Prod.fst) :
    IsMartingaleCoupling μ ν π := by
  have hxi : Integrable (Prod.fst : ℝ × ℝ → ℝ) π.toMeasure := by
    have hμi := ProbDist.integrable_id_of_supportsOn_Icc hμ
    rw [← hfst] at hμi
    exact (integrable_map_measure measurable_id.aestronglyMeasurable
      measurable_fst.aemeasurable).mp hμi
  have hyi : Integrable (Prod.snd : ℝ × ℝ → ℝ) π.toMeasure := by
    have hνi := ProbDist.integrable_id_of_supportsOn_Icc hν
    rw [← hsnd] at hνi
    exact (integrable_map_measure measurable_id.aestronglyMeasurable
      measurable_snd.aemeasurable).mp hνi
  refine ⟨ProbabilityMeasure.toMeasure_injective hfst,
    ProbabilityMeasure.toMeasure_injective hsnd, hxi, hyi, ?_⟩
  intro ψ hψ hbψ
  obtain ⟨M, hM⟩ := hbψ
  have hm : ((borel ℝ).comap (Prod.fst : ℝ × ℝ → ℝ)) ≤ (inferInstance : MeasurableSpace (ℝ × ℝ)) :=
    (measurable_fst : Measurable (Prod.fst : ℝ × ℝ → ℝ)).comap_le
  have hψm : StronglyMeasurable[((borel ℝ).comap (Prod.fst : ℝ × ℝ → ℝ))] (fun p : ℝ × ℝ => ψ p.1) :=
    (hψ.comp (comap_measurable _)).stronglyMeasurable
  have hψae : AEStronglyMeasurable (fun p : ℝ × ℝ => ψ p.1) π.toMeasure :=
    (hψ.comp measurable_fst).aestronglyMeasurable
  have hbound : ∀ᵐ p ∂π.toMeasure, ‖ψ p.1‖ ≤ M :=
    Filter.Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hM p.1
  have hprod_y := hyi.mul_bdd hψae hbound
  have hprod_x := hxi.mul_bdd hψae hbound
  have hpull := condExp_mul_of_stronglyMeasurable_right hψm hprod_y hyi
  have hi : (∫ p, p.2 * ψ p.1 ∂π.toMeasure) = ∫ p, p.1 * ψ p.1 ∂π.toMeasure := by
    calc
      _ = ∫ p, (π.toMeasure[(fun q : ℝ × ℝ => q.2 * ψ q.1) | ((borel ℝ).comap (Prod.fst : ℝ × ℝ → ℝ))]) p ∂π.toMeasure :=
        (integral_condExp hm).symm
      _ = ∫ p, p.1 * ψ p.1 ∂π.toMeasure := by
        apply integral_congr_ae
        filter_upwards [hpull, hce] with p hp hc
        exact hp.trans (by change (π.toMeasure[Prod.snd | ((borel ℝ).comap (Prod.fst : ℝ × ℝ → ℝ))]) p * ψ p.1 = _; rw [hc])
  simp_rw [sub_mul]
  rw [integral_sub hprod_y hprod_x, hi, sub_self]

/-- Compact scalar convex order is equivalent to a genuine joint martingale law. -/
theorem compact_convex_order_iff_martingale (a b : ℝ) (μ ν : ProbabilityMeasure ℝ)
    (hμ : μ.toMeasure (Icc a b) = 1) (hν : ν.toMeasure (Icc a b) = 1) :
    ((∫ x, x ∂μ.toMeasure) = ∫ x, x ∂ν.toMeasure) ∧
      (∀ φ : ℝ → ℝ, ConvexOn ℝ (Icc a b) φ → ContinuousOn φ (Icc a b) →
        (∫ x, φ x ∂μ.toMeasure) ≤ ∫ x, φ x ∂ν.toMeasure) ↔
    ∃ π : ProbabilityMeasure (ℝ × ℝ),
      π.toMeasure.map Prod.fst = μ.toMeasure ∧
      π.toMeasure.map Prod.snd = ν.toMeasure ∧
      π.toMeasure[Prod.snd | (borel ℝ).comap Prod.fst] =ᵐ[π.toMeasure] Prod.fst := by
  constructor
  · rintro ⟨hm, hc⟩
    obtain ⟨π, hπ⟩ := exists_martingaleCoupling_of_convexOrderOnIcc a b
      (μ := μ) (ν := ν) ⟨hμ, hν, hm, hc⟩
    exact ⟨π, hπ.fst_measure, hπ.snd_measure, hπ.condExp_snd_eq_fst⟩
  · rintro ⟨π, hfst, hsnd, hce⟩
    have hπ := isMartingaleCoupling_of_condExp hμ hν hfst hsnd hce
    exact ⟨hπ.marginal_mean_eq, fun φ hc ht => hπ.convex_expect_le hμ hν φ hc ht⟩

end Econlib.Probability
end
