/- GID: D5/S3/Weil/Scattering/ScatteringRatioCompletion
   generality: G
   mirror-B: D5/B/S3/Weil/Scattering/ScatteringRatioCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Scattering data and right normalization recover nonzero meromorphic functions. -/

import D5.S3.Analytic.Isolation.MeromorphicContinuationUniqueness
import Mathlib.Analysis.Meromorphic.IsolatedZeros
import Mathlib.Analysis.Meromorphic.RCLike
import Mathlib.Algebra.Field.Periodic

-- Library-search audit trail (2026-08-28): no repository declaration covers equal
-- scattering ratios plus right-shift normalization. The completed-zeta scattering
-- modules are strict special cases. Pinned mathlib supplies normal-form conversion,
-- codiscrete isolated-zero machinery, periodic iteration, and uniqueness of limits,
-- but no exact theorem. Loogle, LeanSearch, and GitHub code search found no exact hit.

open Filter Topology

namespace D5.S3.Weil.Scattering.ScatteringRatioCompletion

open D5.S3.Analytic.Isolation.MeromorphicContinuationUniqueness

-- A globally defined normal-form representative of a nonzero meromorphic function.
def NonzeroMeromorphic (f : ℂ → ℂ) : Prop :=
  MeromorphicNFOn f Set.univ ∧ ∃ z, f z ≠ 0

-- The normal-form meromorphic quotient of two complex functions.
noncomputable def normalizedQuotient (f g : ℂ → ℂ) : ℂ → ℂ :=
  toMeromorphicNFOn (f / g) Set.univ

private def pullLeft (f : ℂ → ℂ) : ℂ → ℂ :=
  fun s => f (2 * s - 1)

private def pullRight (f : ℂ → ℂ) : ℂ → ℂ :=
  fun s => f (2 * s)

-- The scattering reading `s ↦ F(2s-1) / F(2s)`, in meromorphic normal form.
noncomputable def scatteringRatio (f : ℂ → ℂ) : ℂ → ℂ :=
  normalizedQuotient (pullLeft f) (pullRight f)

-- The multiplicative gauge `F/G`, in meromorphic normal form.
noncomputable def gaugeRatio (f g : ℂ → ℂ) : ℂ → ℂ :=
  normalizedQuotient f g

-- The gauge tends to one along every sequence of positive integral right shifts.
def RightNormalized (f g : ℂ → ℂ) : Prop :=
  ∀ z, Tendsto (fun n : ℕ => gaugeRatio f g (z + n)) atTop (𝓝 1)

-- Candidates with the same local scattering reading and the prescribed gauge normalization.
def RecoveryFiber (f candidate : ℂ → ℂ) : Prop :=
  NonzeroMeromorphic candidate ∧
    scatteringRatio f = scatteringRatio candidate ∧
    RightNormalized f candidate

private lemma normalizedQuotient_meromorphicNFOn (f g : ℂ → ℂ) :
    MeromorphicNFOn (normalizedQuotient f g) Set.univ := by
  exact meromorphicNFOn_toMeromorphicNFOn _ _

private lemma pullLeft_meromorphicNFOn {f : ℂ → ℂ}
    (hf : MeromorphicNFOn f Set.univ) :
    MeromorphicNFOn (pullLeft f) Set.univ := by
  intro s _
  change MeromorphicNFAt (f ∘ fun w : ℂ => 2 * w - 1) s
  exact (hf (Set.mem_univ _)).comp_analyticAt (by fun_prop)

private lemma pullRight_meromorphicNFOn {f : ℂ → ℂ}
    (hf : MeromorphicNFOn f Set.univ) :
    MeromorphicNFOn (pullRight f) Set.univ := by
  intro s _
  change MeromorphicNFAt (f ∘ fun w : ℂ => 2 * w) s
  exact (hf (Set.mem_univ _)).comp_analyticAt (by fun_prop)

private lemma pullLeft_nonzeroMeromorphic {f : ℂ → ℂ}
    (hf : NonzeroMeromorphic f) :
    NonzeroMeromorphic (pullLeft f) := by
  refine ⟨pullLeft_meromorphicNFOn hf.1, ?_⟩
  obtain ⟨z, hz⟩ := hf.2
  refine ⟨(z + 1) / 2, ?_⟩
  convert hz using 1 <;> simp [pullLeft] <;> ring

private lemma pullRight_nonzeroMeromorphic {f : ℂ → ℂ}
    (hf : NonzeroMeromorphic f) :
    NonzeroMeromorphic (pullRight f) := by
  refine ⟨pullRight_meromorphicNFOn hf.1, ?_⟩
  obtain ⟨z, hz⟩ := hf.2
  refine ⟨z / 2, ?_⟩
  convert hz using 1 <;> simp [pullRight] <;> ring

private lemma eventually_ne_zero_of_nonzeroMeromorphic {f : ℂ → ℂ}
    (hf : NonzeroMeromorphic f) :
    ∀ᶠ z in Filter.codiscrete ℂ, f z ≠ 0 := by
  have hmeromorphic : Meromorphic f := meromorphicOn_univ.mp hf.1.meromorphicOn
  have hfinite : ∀ z, meromorphicOrderAt f z ≠ ⊤ :=
    hmeromorphic.exists_meromorphicOrderAt_ne_top_iff_forall.mp (by
      obtain ⟨z, hz⟩ := hf.2
      refine ⟨z, ?_⟩
      intro htop
      have hpunc : f =ᶠ[𝓝[≠] z] (0 : ℂ → ℂ) := by
        change ∀ᶠ y in 𝓝[≠] z, f y = 0
        exact meromorphicOrderAt_eq_top_iff.mp htop
      have hzeroNF : MeromorphicNFAt (0 : ℂ → ℂ) z :=
        analyticAt_const.meromorphicNFAt
      have hnhds :=
        ((hf.1 (Set.mem_univ z)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hzeroNF).mp hpunc
      exact hz hnhds.eq_of_nhds)
  simpa [Filter.codiscrete] using
    MeromorphicAt.MeromorphicOn.codiscreteWithin_setOf_ne_zero hf.1.meromorphicOn
      (fun z _ => hfinite z)

private lemma quotient_eventually_eq_normalized {f g : ℂ → ℂ}
    (hf : MeromorphicNFOn f Set.univ) (hg : MeromorphicNFOn g Set.univ) :
    (f / g) =ᶠ[Filter.codiscrete ℂ] normalizedQuotient f g := by
  simpa [Filter.codiscrete, normalizedQuotient] using
    toMeromorphicNFOn_eqOn_codiscrete (hf.meromorphicOn.div hg.meromorphicOn)

private lemma normalForms_eq_of_eventuallyEq_codiscrete {f g : ℂ → ℂ}
    (hf : MeromorphicNFOn f Set.univ) (hg : MeromorphicNFOn g Set.univ)
    (hfg : f =ᶠ[Filter.codiscrete ℂ] g) :
    f = g := by
  let D : Set ℂ := {z | f z = g z}
  have hDmem : D ∈ Filter.codiscrete ℂ := hfg
  have hDopen : IsOpen D := (mem_codiscrete'.mp hDmem).1
  have hDnonempty : D.Nonempty := by
    by_contra hempty
    have hDempty : D = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
    rw [hDempty] at hDmem
    have hnoAcc := (mem_codiscrete_accPt.mp hDmem) 0
    exact hnoAcc (by
      simpa using PerfectSpace.univ_preperfect (0 : ℂ) (Set.mem_univ _))
  funext z
  exact meromorphic_continuation_unique isOpen_univ isPreconnected_univ
    hDopen hDnonempty (Set.subset_univ D) hf hg (fun _ hz => hz) (Set.mem_univ z)

private noncomputable def leftGauge (f g : ℂ → ℂ) : ℂ → ℂ :=
  normalizedQuotient (pullLeft f) (pullLeft g)

private noncomputable def rightGauge (f g : ℂ → ℂ) : ℂ → ℂ :=
  normalizedQuotient (pullRight f) (pullRight g)

private noncomputable def leftAffineHomeomorph : ℂ ≃ₜ ℂ :=
  (Homeomorph.mulLeft₀ (2 : ℂ) (by norm_num)).trans (Homeomorph.addRight (-1))

private noncomputable def rightAffineHomeomorph : ℂ ≃ₜ ℂ :=
  Homeomorph.mulLeft₀ (2 : ℂ) (by norm_num)

private lemma homeomorph_tendsto_codiscrete (e : ℂ ≃ₜ ℂ) :
    Tendsto e (Filter.codiscrete ℂ) (Filter.codiscrete ℂ) := by
  rw [tendsto_def]
  intro s hs
  apply (e.isEmbedding.image_mem_codiscreteWithin_range (s := e ⁻¹' s)).mp
  simpa [e.surjective.image_preimage, e.surjective.range_eq, Filter.codiscrete] using hs

private lemma leftGauge_eq_comp_gaugeRatio {f g : ℂ → ℂ}
    (hf : NonzeroMeromorphic f) (hg : NonzeroMeromorphic g) :
    leftGauge f g = fun s => gaugeRatio f g (2 * s - 1) := by
  apply normalForms_eq_of_eventuallyEq_codiscrete
  · exact normalizedQuotient_meromorphicNFOn _ _
  · intro s _
    change MeromorphicNFAt (gaugeRatio f g ∘ fun w : ℂ => 2 * w - 1) s
    exact (normalizedQuotient_meromorphicNFOn f g (Set.mem_univ _)).comp_analyticAt (by fun_prop)
  · have hpull := quotient_eventually_eq_normalized
      (pullLeft_meromorphicNFOn hf.1) (pullLeft_meromorphicNFOn hg.1)
    have hglobal := quotient_eventually_eq_normalized hf.1 hg.1
    have hcomp := homeomorph_tendsto_codiscrete leftAffineHomeomorph hglobal
    filter_upwards [hpull, hcomp] with s hsPull hsGlobal
    have hAffine : leftAffineHomeomorph s = 2 * s - 1 := by
      simp [leftAffineHomeomorph, sub_eq_add_neg]
    calc
      leftGauge f g s = (pullLeft f / pullLeft g) s := hsPull.symm
      _ = (f / g) (leftAffineHomeomorph s) := by
        simp [pullLeft, hAffine]
      _ = gaugeRatio f g (leftAffineHomeomorph s) := hsGlobal
      _ = gaugeRatio f g (2 * s - 1) := by rw [hAffine]

private lemma rightGauge_eq_comp_gaugeRatio {f g : ℂ → ℂ}
    (hf : NonzeroMeromorphic f) (hg : NonzeroMeromorphic g) :
    rightGauge f g = fun s => gaugeRatio f g (2 * s) := by
  apply normalForms_eq_of_eventuallyEq_codiscrete
  · exact normalizedQuotient_meromorphicNFOn _ _
  · intro s _
    change MeromorphicNFAt (gaugeRatio f g ∘ fun w : ℂ => 2 * w) s
    exact (normalizedQuotient_meromorphicNFOn f g (Set.mem_univ _)).comp_analyticAt (by fun_prop)
  · have hpull := quotient_eventually_eq_normalized
      (pullRight_meromorphicNFOn hf.1) (pullRight_meromorphicNFOn hg.1)
    have hglobal := quotient_eventually_eq_normalized hf.1 hg.1
    have hcomp := homeomorph_tendsto_codiscrete rightAffineHomeomorph hglobal
    filter_upwards [hpull, hcomp] with s hsPull hsGlobal
    calc
      rightGauge f g s = (pullRight f / pullRight g) s := hsPull.symm
      _ = (f / g) (rightAffineHomeomorph s) := by
        simp [pullRight, rightAffineHomeomorph]
      _ = gaugeRatio f g (rightAffineHomeomorph s) := hsGlobal
      _ = gaugeRatio f g (2 * s) := by simp [rightAffineHomeomorph]

private lemma gaugeRatio_periodic {f g : ℂ → ℂ}
    (hf : NonzeroMeromorphic f) (hg : NonzeroMeromorphic g)
    (hreading : scatteringRatio f = scatteringRatio g) :
    Function.Periodic (gaugeRatio f g) 1 := by
  have hrawReading :
      (pullLeft f / pullRight f) =ᶠ[Filter.codiscrete ℂ]
        (pullLeft g / pullRight g) := by
    have hfRaw := quotient_eventually_eq_normalized
      (pullLeft_meromorphicNFOn hf.1) (pullRight_meromorphicNFOn hf.1)
    have hgRaw := quotient_eventually_eq_normalized
      (pullLeft_meromorphicNFOn hg.1) (pullRight_meromorphicNFOn hg.1)
    filter_upwards [hfRaw, hgRaw] with s hsF hsG
    calc
      (pullLeft f / pullRight f) s = scatteringRatio f s := by
        simpa [scatteringRatio] using hsF
      _ = scatteringRatio g s := congrFun hreading s
      _ = (pullLeft g / pullRight g) s := by
        simpa [scatteringRatio] using hsG.symm
  have hleftRaw := quotient_eventually_eq_normalized
    (pullLeft_meromorphicNFOn hf.1) (pullLeft_meromorphicNFOn hg.1)
  have hrightRaw := quotient_eventually_eq_normalized
    (pullRight_meromorphicNFOn hf.1) (pullRight_meromorphicNFOn hg.1)
  have hfRight := eventually_ne_zero_of_nonzeroMeromorphic (pullRight_nonzeroMeromorphic hf)
  have hgLeft := eventually_ne_zero_of_nonzeroMeromorphic (pullLeft_nonzeroMeromorphic hg)
  have hgRight := eventually_ne_zero_of_nonzeroMeromorphic (pullRight_nonzeroMeromorphic hg)
  have hgauges : leftGauge f g = rightGauge f g := by
    apply normalForms_eq_of_eventuallyEq_codiscrete
    · exact normalizedQuotient_meromorphicNFOn _ _
    · exact normalizedQuotient_meromorphicNFOn _ _
    · filter_upwards [hrawReading, hleftRaw, hrightRaw, hfRight, hgLeft, hgRight]
        with s hsReading hsLeft hsRight hFRight hGLeft hGRight
      simp only [Pi.div_apply] at hsReading hsLeft hsRight
      have hcross := (div_eq_div_iff hFRight hGRight).mp hsReading
      have hratio : pullLeft f s / pullLeft g s = pullRight f s / pullRight g s :=
        (div_eq_div_iff hGLeft hGRight).2 (by simpa [mul_comm] using hcross)
      exact hsLeft.symm.trans (hratio.trans hsRight)
  have hleft := leftGauge_eq_comp_gaugeRatio hf hg
  have hright := rightGauge_eq_comp_gaugeRatio hf hg
  intro z
  let s : ℂ := (z + 1) / 2
  have hs : gaugeRatio f g (2 * s - 1) = gaugeRatio f g (2 * s) := by
    calc
      gaugeRatio f g (2 * s - 1) = leftGauge f g s := (congrFun hleft s).symm
      _ = rightGauge f g s := congrFun hgauges s
      _ = gaugeRatio f g (2 * s) := congrFun hright s
  convert hs.symm using 1 <;> simp [s] <;> ring

private lemma gaugeRatio_eq_one_of_periodic_rightNormalized {f g : ℂ → ℂ}
    (hperiodic : Function.Periodic (gaugeRatio f g) 1)
    (hright : RightNormalized f g) :
    gaugeRatio f g = 1 := by
  funext z
  have hconstant : (fun n : ℕ => gaugeRatio f g (z + n)) = fun _ => gaugeRatio f g z := by
    funext n
    simpa using hperiodic.nsmul n z
  have htoGauge : Tendsto (fun _ : ℕ => gaugeRatio f g z) atTop (𝓝 (gaugeRatio f g z)) :=
    tendsto_const_nhds
  have htoOne : Tendsto (fun _ : ℕ => gaugeRatio f g z) atTop (𝓝 1) := by
    simpa [hconstant] using hright z
  exact tendsto_nhds_unique htoGauge htoOne

private lemma gaugeRatio_self_eq_one {f : ℂ → ℂ} (hf : NonzeroMeromorphic f) :
    gaugeRatio f f = 1 := by
  apply normalForms_eq_of_eventuallyEq_codiscrete
  · exact normalizedQuotient_meromorphicNFOn _ _
  · intro z _
    exact analyticAt_const.meromorphicNFAt
  · have hraw := quotient_eventually_eq_normalized hf.1 hf.1
    have hne := eventually_ne_zero_of_nonzeroMeromorphic hf
    filter_upwards [hraw, hne] with z hz hzne
    have hzRaw : (f / f) z = 1 := by simp [Pi.div_apply, hzne]
    exact hz.symm.trans hzRaw

private lemma scattering_ratio_unique {f g : ℂ → ℂ}
    (hf : NonzeroMeromorphic f) (hg : NonzeroMeromorphic g)
    (hreading : scatteringRatio f = scatteringRatio g)
    (hright : RightNormalized f g) :
    f = g := by
  have hperiodic := gaugeRatio_periodic hf hg hreading
  have hgauge : gaugeRatio f g = 1 :=
    gaugeRatio_eq_one_of_periodic_rightNormalized hperiodic hright
  have hraw := quotient_eventually_eq_normalized hf.1 hg.1
  have hgne := eventually_ne_zero_of_nonzeroMeromorphic hg
  apply normalForms_eq_of_eventuallyEq_codiscrete hf.1 hg.1
  filter_upwards [hraw, hgne] with z hz hGz
  have hquotient : f z / g z = 1 := by
    calc
      f z / g z = gaugeRatio f g z := by
        simpa only [Pi.div_apply, gaugeRatio] using hz
      _ = 1 := congrFun hgauge z
  exact (div_eq_one_iff_eq hGz).mp hquotient

private lemma recovery_exists (f : ℂ → ℂ) (hf : NonzeroMeromorphic f) :
    ∃ candidate, RecoveryFiber f candidate := by
  refine ⟨f, hf, rfl, ?_⟩
  intro z
  rw [gaugeRatio_self_eq_one hf]
  exact tendsto_const_nhds

-- The global object selected from the completed scattering-data fiber.
noncomputable def gaugeCompletion (f : ℂ → ℂ) (hf : NonzeroMeromorphic f) : ℂ → ℂ :=
  Classical.choose (recovery_exists f hf)

private lemma gaugeCompletion_spec (f : ℂ → ℂ) (hf : NonzeroMeromorphic f) :
    RecoveryFiber f (gaugeCompletion f hf) :=
  Classical.choose_spec (recovery_exists f hf)

-- Equal scattering readings and right-half-plane normalization recover the original
-- nonzero meromorphic function, its unique recovery fiber, and its gauge completion.
theorem scattering_ratio_completion (f g : ℂ → ℂ)
    (hf : NonzeroMeromorphic f) (hg : NonzeroMeromorphic g)
    (hreading : scatteringRatio f = scatteringRatio g)
    (hright : RightNormalized f g) :
    f = g ∧
      (∃ candidate, RecoveryFiber f candidate) ∧
      (∀ candidate, RecoveryFiber f candidate → candidate = f) ∧
      gaugeCompletion f hf = f := by
  have heq : f = g := scattering_ratio_unique hf hg hreading hright
  have hexists : ∃ candidate, RecoveryFiber f candidate := recovery_exists f hf
  have hunique : ∀ candidate, RecoveryFiber f candidate → candidate = f := by
    intro candidate hcandidate
    exact (scattering_ratio_unique hf hcandidate.1 hcandidate.2.1 hcandidate.2.2).symm
  exact ⟨heq, hexists, hunique, hunique _ (gaugeCompletion_spec f hf)⟩

-- Reverse probe (CAS-A1): the public first leaf recovers equality at every complex point.
example (f g : ℂ → ℂ)
    (hf : NonzeroMeromorphic f) (hg : NonzeroMeromorphic g)
    (hreading : scatteringRatio f = scatteringRatio g)
    (hright : RightNormalized f g) (z : ℂ) :
    f z = g z := by
  exact congrFun (scattering_ratio_completion f g hf hg hreading hright).1 z

-- Projection probes (CAS-A2/A3/A4): each post-proof conclusion is independently available.
example (f g : ℂ → ℂ)
    (hf : NonzeroMeromorphic f) (hg : NonzeroMeromorphic g)
    (hreading : scatteringRatio f = scatteringRatio g)
    (hright : RightNormalized f g) :
    (∃ candidate, RecoveryFiber f candidate) ∧
      (∀ candidate, RecoveryFiber f candidate → candidate = f) ∧
      gaugeCompletion f hf = f := by
  exact (scattering_ratio_completion f g hf hg hreading hright).2

-- Trivialization probe (CAS-A2): the zero function is outside the stated nonzero carrier.
example : ¬NonzeroMeromorphic (0 : ℂ → ℂ) := by
  intro hzero
  obtain ⟨z, hz⟩ := hzero.2
  exact hz rfl

end D5.S3.Weil.Scattering.ScatteringRatioCompletion
