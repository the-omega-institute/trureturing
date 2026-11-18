/- GID: D5/S3/Analytic/NativePeriod/OriginalGaussianSourceCharacter
   generality: I
   mirror-B: D5/B/S3/Analytic/NativePeriod/OriginalGaussianSourceCharacter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Complex]
   utility: none
   digest: The literal negative source zero amplitude and its normalized square-root covering branch. -/

import D5.S3.Analytic.NativePeriod.OriginalHalfBinomialComplementMonodromy
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGenerators

/-! The source phase is fixed by the public generator of the literal amplitudes. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter unitInterval
open scoped Topology

namespace D5.S3.Analytic.NativePeriod.OriginalGaussianSourceCharacter
open OriginalHalfBinomialDiskCorrection
open OriginalHalfBinomialLocalCharts
open OriginalHalfBinomialContinuation
open OriginalHalfBinomialMonodromy
open OriginalHalfBinomialComplementMonodromy
open D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceEvaluation
open D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGenerators

/-- This is the literal negative source amplitude, not an independently normalized root. -/
def C (r : ℂ) : ℂ := sourceAmplitude false 0 r

def sourceCover (z : ℂ) : ℂ := Complex.exp (-z / 2)

def sourceChart (z r : ℂ) : ℂ := sourceCover (localLog z (1 - r))

private lemma disk_slit {r : ℂ} (hr : r ∈ disk) : 1 - r ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  left
  have h := (Complex.re_le_norm r).trans_lt (show ‖r‖ < 1 by simpa [disk] using hr)
  simpa only [Complex.sub_re, Complex.one_re] using sub_pos.mpr h

private lemma source_closed {r : ℂ} (hr : r ∈ disk) :
    C r = Complex.exp (-Complex.log (1 - r) / 2) := by
  have h := (sourceAmplitude_generators (u := 0) (x := r)
    (by simpa [disk] using hr)).2
  have hf : (fun p : ℕ => sourceAmplitude false p r * (0 : ℂ) ^ p) =
      Pi.single 0 (sourceAmplitude false 0 r) := by
    funext p
    by_cases hp : p = 0 <;> simp [hp]
  rw [hf] at h
  have hc : C r = (1 - r) ^ (-1 / 2 : ℂ) := by simpa [C] using h.tsum_eq
  rw [hc, Complex.cpow_def_of_ne_zero (Complex.slitPlane_ne_zero (disk_slit hr))]
  congr 1
  ring

/-- The public generator at u=0 identifies the actual source, including its
phase, and gives holomorphy on the entire original disk. -/
theorem actual_source_branch :
    (∀ r ∈ disk, C r = Complex.exp (-Complex.log (1 - r) / 2)) ∧
    DifferentiableOn ℂ C disk ∧
    (∀ r ∈ disk, sourceMode false 0 r = C r) := by
  refine ⟨fun r hr => source_closed hr, ?_, ?_⟩
  · intro r hr
    have hd : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (-Complex.log (1 - w) / 2)) r :=
      (((Complex.hasDerivAt_log (disk_slit hr)).comp r
        ((hasDerivAt_id r).const_sub 1)).neg.div_const 2).cexp.differentiableAt
    apply (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [Metric.isOpen_ball.mem_nhds hr] with w hw
    exact source_closed hw
  · intro r hr
    have h := (sourceAmplitude_generators (u := 0) (x := r)
      (by simpa [disk] using hr)).2.tsum_eq
    change (∑' p : ℕ, sourceAmplitude false p r * (0 : ℂ) ^ p) = C r
    rw [h, source_closed hr]
    simp only [sub_zero, div_one, one_div_one, one_mul]
    rw [Complex.cpow_def_of_ne_zero (Complex.slitPlane_ne_zero (disk_slit hr))]
    congr 1
    ring

/-- The fixed source phase has the integer character (-1)^k on the
complementary exponential cover. -/
theorem source_deck :
    Differentiable ℂ sourceCover ∧
    (∀ z : ℂ, ∀ k : ℤ,
      sourceCover (z + k * (2 * (Real.pi : ℂ) * Complex.I)) =
        (-1 : ℂ) ^ k * sourceCover z) := by
  refine ⟨by unfold sourceCover; fun_prop, ?_⟩
  intro z k
  have ha : -(z + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) / 2 =
      (-k : ℂ) * ((Real.pi : ℂ) * Complex.I) + -z / 2 := by ring
  rw [sourceCover, ha, Complex.exp_add,
    show (-k : ℂ) = ((-k : ℤ) : ℂ) by simp, Complex.exp_int_mul,
    Complex.exp_pi_mul_I]
  rw [zpow_neg, ← inv_zpow]
  norm_num [sourceCover]

private lemma source_initial : sourceChart baseLog =ᶠ[𝓝 b] C := by
  have hb : b ∈ lens := by norm_num [b, lens, Metric.mem_ball, dist_eq_norm]
  have hs : b ∈ Complex.slitPlane := by norm_num [b, Complex.mem_slitPlane_iff]
  have he := (native_chart baseLog (native_initial_germ b hb).1).2.2.2.2.comp_tendsto
    (Complex.hasDerivAt_log hs).continuousAt.tendsto
  have hl : localLog baseLog =ᶠ[𝓝 b] Complex.log := by
    filter_upwards [he, Complex.isOpen_slitPlane.mem_nhds hs] with r hr hsr
    simpa only [Function.comp_def, Complex.exp_log (Complex.slitPlane_ne_zero hsr)] using hr
  have hc := hl.comp_tendsto
    (show Tendsto (fun r : ℂ => 1 - r) (𝓝 b) (𝓝 b) by
      convert ((by fun_prop : Continuous (fun r : ℂ => 1 - r)).continuousAt (x := b)).tendsto using 1 <;>
        norm_num [b])
  filter_upwards [hc, Metric.isOpen_ball.mem_nhds (show b ∈ disk by norm_num [disk, b])] with r hr hrD
  dsimp only [Function.comp_def] at hr
  rw [sourceChart, hr, sourceCover, actual_source_branch.1 r hrD]

/-- Only the explicit source charts associated to this native path are needed. -/
structure SourceCharts (γ L : C(I, ℂ)) : Prop where
  holomorphic : ∀ t, DifferentiableOn ℂ (sourceChart (L t)) (complementDomain (L t))
  germAlong : ∀ t, ∀ᶠ s in 𝓝 t,
    sourceChart (L t) =ᶠ[𝓝 (γ s)] sourceChart (L s)
  initial : sourceChart (L 0) =ᶠ[𝓝 b] C
  liftValue : ∀ t, sourceChart (L t) (γ t) = sourceCover (L t)

private lemma source_certificate (γ L : C(I, ℂ))
    (hn : NativeCharts (complementPath γ) L) (h0 : L 0 = baseLog) : SourceCharts γ L := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t r hr
    have hd := ((native_chart (L t) (hn.halfPlane t)).2.2.2.1 (1 - r) hr).2.2.1
    exact (source_deck.1.differentiableAt.comp r
      (hd.differentiableAt.comp r ((hasDerivAt_id r).const_sub 1).differentiableAt)).differentiableWithinAt
  · intro t
    have hm : ∀ᶠ s in 𝓝 t, (L s - L t).im ∈ Ioo (-Real.pi) Real.pi := by
      apply (isOpen_Ioo.preimage (by fun_prop : Continuous (fun s : I => (L s - L t).im))).mem_nhds
      simp [Real.pi_pos]
    filter_upwards [hm] with s hs
    have he := (chart_transition (L t) (L s) (hn.halfPlane s) hs).1
    rw [hn.projection s] at he
    have he' := he.comp_tendsto
      (show Tendsto (fun r : ℂ => 1 - r) (𝓝 (γ s)) (𝓝 (complementPath γ s)) from
        (continuous_const.sub continuous_id).continuousAt.tendsto)
    exact he'.mono (fun r hr => by
      dsimp only [Function.comp_def] at hr
      simp only [sourceChart, hr])
  · rw [h0]
    exact source_initial
  · intro t
    have hp : 1 - γ t = Complex.exp (L t) := (hn.projection t).symm
    simp only [sourceChart, hp, (native_chart (L t) (hn.halfPlane t)).2.2.1]

private lemma source_chart_shift (z : ℂ) (k : ℤ) :
    sourceChart (z + deck k) = (fun r => (-1 : ℂ) ^ k * sourceChart z r) := by
  funext r
  have he : Complex.exp (z + deck k) = Complex.exp z :=
    Complex.exp_eq_exp_iff_exists_int.mpr ⟨k, rfl⟩
  have hl : localLog (z + deck k) (1 - r) = localLog z (1 - r) + deck k := by
    simp only [localLog, he]
    ring
  rw [sourceChart, hl]
  exact source_deck.2 _ k

/-- All continuous complementary paths carry the actual source germ, with
local holomorphic charts and genuine neighborhood transition equalities. -/
theorem actual_source_path (γ : C(I, ℂ))
    (hD : ∀ t, ‖1 - γ t‖ < 1) (hn : ∀ t, γ t ≠ 1) (hb : γ 0 = b) :
    ∃ L : C(I, ℂ), L 0 = baseLog ∧ NativeCharts (complementPath γ) L ∧ SourceCharts γ L := by
  obtain ⟨L, h0, hc, _, _⟩ := complementary_path_continuation γ hD hn hb
  exact ⟨L, h0, hc, source_certificate γ L hc h0⟩

/-- The entire original disk supplies the single-valued source charts around
zero. Around one, every based loop has the exact endpoint character (-1)^k. -/
theorem actual_source_loop_character :
    DifferentiableOn ℂ C disk ∧
    (∀ γ : C(I, ℂ), (∀ t, ‖γ t‖ < 1) →
      (∀ t, disk ∈ 𝓝 (γ t)) ∧
      (∀ t, ∀ᶠ s in 𝓝 t, C =ᶠ[𝓝 (γ s)] C) ∧
      C =ᶠ[𝓝 (γ 0)] C ∧ C =ᶠ[𝓝 (γ 1)] C) ∧
    (∀ γ : C(I, ℂ), (∀ t, ‖1 - γ t‖ < 1) → (∀ t, γ t ≠ 1) →
      γ 0 = b → γ 1 = b →
      ∃ L : C(I, ℂ), ∃ k : ℤ, L 0 = baseLog ∧ NativeCharts (complementPath γ) L ∧
        SourceCharts γ L ∧ L 1 = baseLog + deck k ∧
        sourceChart (L 1) =ᶠ[𝓝 b] (fun r => (-1 : ℂ) ^ k * C r)) := by
  refine ⟨actual_source_branch.2.1, ?_, ?_⟩
  · intro γ hD
    exact ⟨fun t => Metric.isOpen_ball.mem_nhds (by simpa [disk] using hD t),
      fun _ => Filter.Eventually.of_forall (fun _ => Filter.EventuallyEq.rfl),
      Filter.EventuallyEq.rfl, Filter.EventuallyEq.rfl⟩
  · intro γ hD hn hb hb1
    obtain ⟨L, k, h0, hc, h1, _, _⟩ := complementary_loop_monodromy γ hD hn hb hb1
    refine ⟨L, k, h0, hc, source_certificate γ L hc h0, h1, ?_⟩
    rw [h1, source_chart_shift]
    exact source_initial.mono (fun r hr => by dsimp; rw [hr])

/-- The native positive loop around one reverses the actual source sign;
the initial germ remains the literal negative source amplitude. -/
theorem positive_source_monodromy :
    SourceCharts gamma1 positiveLift ∧
    sourceChart (positiveLift 1) =ᶠ[𝓝 b] (fun r => -C r) := by
  refine ⟨source_certificate gamma1 positiveLift positive_one_monodromy.1
    (by simp [positiveLift]), ?_⟩
  rw [positive_zero_monodromy.2.1, source_chart_shift]
  filter_upwards [source_initial] with r hr
  rw [hr]
  norm_num

end D5.S3.Analytic.NativePeriod.OriginalGaussianSourceCharacter
