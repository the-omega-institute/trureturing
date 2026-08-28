/- GID: D5/S3/Analytic/Asymptotics/SpectralZetaContinuation
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/SpectralZetaContinuation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Linear spectral density yields zeta continuation and its residue. -/

import D5.S3.Analytic.Asymptotics.FiniteCountertermMellinContinuation
import D5.S3.Analytic.Asymptotics.LinearDensityHeatTrace
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.Order.Interval.Set.Nat

open Asymptotics Filter MeasureTheory Set
open Complex
open scoped Topology

namespace D5.S3.Analytic.Asymptotics.SpectralZetaContinuation

noncomputable section

open D5.S3.Analytic.Asymptotics.LinearDensityHeatTrace
open D5.S3.Analytic.Asymptotics.FiniteCountertermMellinContinuation

/-- The spectral Dirichlet series from Corollary 13.2. -/
def spectralZeta (lambda : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, (lambda n : ℂ) ^ (-s)

/-- The complex-valued heat trace used by the Mellin transform. -/
def complexHeatTrace (lambda : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑' n : ℕ, (Real.exp (-t * lambda n) : ℂ)

/-- The leading heat mode `c / t`, expressed in the complex power notation used by Mellin theory. -/
def principalHeatTerm (c t : ℝ) : ℂ :=
  (c : ℂ) * (t : ℂ) ^ (-(1 : ℂ))

/-- The one-counterterm heat trace used in the continuation construction. -/
def regularizedHeatTrace (lambda : ℕ → ℝ) (c : ℝ) (t : ℝ) : ℂ :=
  if t ≤ 1 then complexHeatTrace lambda t - principalHeatTerm c t
  else complexHeatTrace lambda t

/-- The finite-part Mellin transform with its single pole term restored. -/
def spectralMellinCompletion (lambda : ℕ → ℝ) (c : ℝ) (s : ℂ) : ℂ :=
  (∫ t in Set.Ioc (0 : ℝ) 1,
      (t : ℂ) ^ (s - 1) * (complexHeatTrace lambda t - principalHeatTerm c t)) +
    (∫ t in Set.Ioi (1 : ℝ),
      (t : ℂ) ^ (s - 1) * complexHeatTrace lambda t) +
    (c : ℂ) / (s - 1)

/-- The named meromorphic continuation of the spectral Dirichlet series. -/
def continuedSpectralZeta (lambda : ℕ → ℝ) (c : ℝ) (s : ℂ) : ℂ :=
  spectralMellinCompletion lambda c s / Gamma s

/-- Meromorphic continuation means both meromorphicity on the larger half-plane and agreement
with the original Dirichlet series on its initial half-plane. -/
def IsSpectralZetaContinuation (lambda : ℕ → ℝ) (Z : ℂ → ℂ) : Prop :=
  MeromorphicOn Z {s | 0 < s.re} ∧
    ∀ s : ℂ, 1 < s.re → Z s = spectralZeta lambda s

private def oneZeroExponent (i : Fin 2) : ℝ :=
  1 - (i.val : ℝ)

private lemma oneZeroExponent_strictAnti : StrictAnti oneZeroExponent := by
  intro i j hij
  have hij' : (i.val : ℝ) < j.val := by exact_mod_cast hij
  dsimp only [oneZeroExponent]
  linarith

@[simp] private lemma oneZeroExponent_zero : oneZeroExponent 0 = 1 := by
  norm_num [oneZeroExponent]

@[simp] private lemma oneZeroExponent_last : oneZeroExponent (Fin.last 1) = 0 := by
  norm_num [oneZeroExponent, Fin.last]

@[simp] private lemma oneZeroExponent_castSucc (i : Fin 1) :
    oneZeroExponent i.castSucc = 1 := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  norm_num [oneZeroExponent]

private lemma counting_at_spectrum (lambda : ℕ → ℝ) (hstrict : StrictMono lambda)
    (n : ℕ) : spectralCounting lambda (lambda n) = n + 1 := by
  have hset : {k | lambda k ≤ lambda n} = Set.Iic n := by
    ext k
    exact hstrict.le_iff_le
  unfold spectralCounting
  rw [hset, Set.ncard_Iic_nat]
  norm_num

private lemma eventually_linear_lower (lambda : ℕ → ℝ) (c : ℝ)
    (hpos : ∀ n, 0 < lambda n) (hstrict : StrictMono lambda)
    (hfinite : ∀ u, Set.Finite {n | lambda n ≤ u})
    (hdensity : (fun u => spectralCounting lambda u - c * u) =O[atTop]
      (fun _ => (1 : ℝ))) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) / (2 * (|c| + 1)) ≤ lambda n := by
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hdensity
  simp only [norm_one, mul_one] at hC
  obtain ⟨U, hU⟩ := eventually_atTop.1 hC
  have houtside : ∀ᶠ n : ℕ in atTop, n ∉ {n | lambda n ≤ U} := by
    rw [← Nat.cofinite_eq_atTop]
    exact (hfinite U).eventually_cofinite_notMem
  have hnlarge : ∀ᶠ n : ℕ in atTop, 2 * C ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (2 * C))
  filter_upwards [houtside, hnlarge] with n hnU hnC
  have hUn : U ≤ lambda n := le_of_not_ge hnU
  have hbound := hU (lambda n) hUn
  have hcount : spectralCounting lambda (lambda n) = (n : ℝ) + 1 := by
    rw [counting_at_spectrum lambda hstrict n]
  have hupper : (n : ℝ) + 1 ≤ |c| * lambda n + C := by
    calc
      (n : ℝ) + 1 = spectralCounting lambda (lambda n) := hcount.symm
      _ ≤ c * lambda n + C := by
        have hresidual : spectralCounting lambda (lambda n) - c * lambda n ≤ C :=
          (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hbound)
        linarith
      _ ≤ |c| * lambda n + C := by
        simpa only [add_comm] using add_le_add_right
          (mul_le_mul_of_nonneg_right (le_abs_self c) (hpos n).le) C
  have hdenom : 0 < |c| + 1 := by positivity
  have hlinear : (n : ℝ) / 2 ≤ (|c| + 1) * lambda n := by
    have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hlambda := (hpos n).le
    nlinarith [abs_nonneg c]
  rw [div_le_iff₀ (by positivity : 0 < 2 * (|c| + 1))]
  nlinarith

private lemma summable_heat (lambda : ℕ → ℝ) (c t : ℝ)
    (hpos : ∀ n, 0 < lambda n) (hstrict : StrictMono lambda)
    (hfinite : ∀ u, Set.Finite {n | lambda n ≤ u})
    (hdensity : (fun u => spectralCounting lambda u - c * u) =O[atTop]
      (fun _ => (1 : ℝ))) (ht : 0 < t) :
    Summable (fun n : ℕ => Real.exp (-t * lambda n)) := by
  let q : ℝ := Real.exp (-t / (2 * (|c| + 1)))
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    rw [Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos ht) (by positivity)
  refine Summable.of_norm_bounded_eventually_nat
    (g := fun n : ℕ => q ^ n) (summable_geometric_of_lt_one hq0 hq1) ?_
  filter_upwards [eventually_linear_lower lambda c hpos hstrict hfinite hdensity] with n hn
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hexp : Real.exp (-t * lambda n) ≤
      Real.exp (-t * ((n : ℝ) / (2 * (|c| + 1)))) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hn (by linarith)
  calc
    Real.exp (-t * lambda n) ≤
        Real.exp (-t * ((n : ℝ) / (2 * (|c| + 1)))) := hexp
    _ = q ^ n := by
      change Real.exp (-t * ((n : ℝ) / (2 * (|c| + 1)))) =
        Real.exp (-t / (2 * (|c| + 1))) ^ n
      rw [← Real.exp_nat_mul]
      congr 1
      ring

private lemma summable_spectral_rpow (lambda : ℕ → ℝ) (c r : ℝ)
    (hpos : ∀ n, 0 < lambda n) (hstrict : StrictMono lambda)
    (hfinite : ∀ u, Set.Finite {n | lambda n ≤ u})
    (hdensity : (fun u => spectralCounting lambda u - c * u) =O[atTop]
      (fun _ => (1 : ℝ))) (hr : 1 < r) :
    Summable (fun n : ℕ => 1 / lambda n ^ r) := by
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-r)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  refine Summable.of_norm_bounded_eventually_nat
    (g := fun n : ℕ => (2 * (|c| + 1)) ^ r * (n : ℝ) ^ (-r))
    (hbase.mul_left _) ?_
  filter_upwards [eventually_linear_lower lambda c hpos hstrict hfinite hdensity,
    eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn hnpos
  rw [Real.norm_eq_abs, abs_of_pos
    (div_pos one_pos (Real.rpow_pos_of_pos (hpos n) r))]
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hdenom : 0 < 2 * (|c| + 1) := by positivity
  calc
    1 / lambda n ^ r = lambda n ^ (-r) := by
      simpa only [one_div] using (Real.rpow_neg (hpos n).le r).symm
    _ ≤ ((n : ℝ) / (2 * (|c| + 1))) ^ (-r) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hn (by linarith)
    _ = (2 * (|c| + 1)) ^ r * (n : ℝ) ^ (-r) := by
      rw [Real.div_rpow hnreal.le hdenom.le, Real.rpow_neg hnreal.le,
        Real.rpow_neg hdenom.le]
      field_simp

private lemma complexHeatTrace_eq_ofReal (lambda : ℕ → ℝ) (t : ℝ) :
    complexHeatTrace lambda t = (spectralHeatTrace lambda t : ℂ) := by
  rw [complexHeatTrace, spectralHeatTrace, Complex.ofReal_tsum]

private lemma principalHeatTerm_eq_div (c : ℝ) {t : ℝ} :
    principalHeatTerm c t = ((c / t : ℝ) : ℂ) := by
  rw [principalHeatTerm, Complex.cpow_neg_one]
  simp only [div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv]

private lemma complexHeatTrace_continuousOn (lambda : ℕ → ℝ) (c : ℝ)
    (hpos : ∀ n, 0 < lambda n) (hstrict : StrictMono lambda)
    (hfinite : ∀ u, Set.Finite {n | lambda n ≤ u})
    (hdensity : (fun u => spectralCounting lambda u - c * u) =O[atTop]
      (fun _ => (1 : ℝ))) :
    ContinuousOn (complexHeatTrace lambda) (Set.Ioi 0) := by
  intro t ht
  have htpos : 0 < t := Set.mem_Ioi.mp ht
  let a : ℝ := t / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hsum : Summable (fun n : ℕ => Real.exp (-a * lambda n)) :=
    summable_heat lambda c a hpos hstrict hfinite hdensity ha
  have hcontinuous : ContinuousOn (complexHeatTrace lambda) (Set.Ici a) := by
    apply continuousOn_tsum (u := fun n : ℕ => Real.exp (-a * lambda n))
    · intro n
      fun_prop
    · exact hsum
    · intro n x hx
      have hax : a ≤ x := Set.mem_Ici.mp hx
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (neg_le_neg hax) (hpos n).le
  exact (hcontinuous.continuousAt (Ici_mem_nhds (by dsimp [a]; linarith))).continuousWithinAt

private lemma regularizedHeatTrace_locallyIntegrableOn (lambda : ℕ → ℝ) (c : ℝ)
    (hpos : ∀ n, 0 < lambda n) (hstrict : StrictMono lambda)
    (hfinite : ∀ u, Set.Finite {n | lambda n ≤ u})
    (hdensity : (fun u => spectralCounting lambda u - c * u) =O[atTop]
      (fun _ => (1 : ℝ))) :
    LocallyIntegrableOn (regularizedHeatTrace lambda c) (Set.Ioi 0) := by
  have hthetaContinuous :=
    complexHeatTrace_continuousOn lambda c hpos hstrict hfinite hdensity
  have htheta : LocallyIntegrableOn (complexHeatTrace lambda) (Set.Ioi 0) :=
    ContinuousOn.locallyIntegrableOn hthetaContinuous measurableSet_Ioi
  have hprincipalContinuous : ContinuousOn (principalHeatTerm c) (Set.Ioi 0) := by
    have hrealDiv : ContinuousOn (fun t : ℝ => c / t) (Set.Ioi 0) :=
      continuousOn_const.div continuousOn_id (fun t ht => ne_of_gt (Set.mem_Ioi.mp ht))
    have hdiv : ContinuousOn (fun t : ℝ => ((c / t : ℝ) : ℂ)) (Set.Ioi 0) :=
      Complex.continuous_ofReal.comp_continuousOn hrealDiv
    apply hdiv.congr
    intro t ht
    exact principalHeatTerm_eq_div c
  have hprincipal : LocallyIntegrableOn (principalHeatTerm c) (Set.Ioi 0) :=
    ContinuousOn.locallyIntegrableOn hprincipalContinuous measurableSet_Ioi
  have hindicator : LocallyIntegrableOn
      ((Set.Iic (1 : ℝ)).indicator (principalHeatTerm c)) (Set.Ioi 0) := by
    intro x hx
    obtain ⟨u, hu, hu'⟩ := hprincipal x hx
    exact ⟨u, hu, hu'.indicator measurableSet_Iic⟩
  apply (htheta.sub hindicator).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  by_cases ht1 : t ≤ 1
  · simp [regularizedHeatTrace, ht1]
  · simp [regularizedHeatTrace, ht1]

private lemma heat_residual_isBigO (lambda : ℕ → ℝ) (c : ℝ)
    (hpos : ∀ n, 0 < lambda n) (hstrict : StrictMono lambda)
    (hfinite : ∀ u, Set.Finite {n | lambda n ≤ u})
    (hdensity : (fun u => spectralCounting lambda u - c * u) =O[atTop]
      (fun _ => (1 : ℝ))) :
    (fun t => complexHeatTrace lambda t - principalHeatTerm c t) =O[𝓝[>] 0]
      (fun _ => (1 : ℝ)) := by
  have hreal := linear_density_heat_trace lambda c hpos hstrict hfinite hdensity
  have hcomplex : (fun t => ((spectralHeatTrace lambda t - c / t : ℝ) : ℂ)) =O[𝓝[>] 0]
      (fun _ => (1 : ℝ)) := by
    obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hreal
    refine Asymptotics.isBigO_iff.mpr ⟨C, ?_⟩
    simpa only [Complex.norm_real, Real.norm_eq_abs, norm_one] using hC
  apply hcomplex.congr'
  · filter_upwards [self_mem_nhdsWithin] with t ht
    rw [complexHeatTrace_eq_ofReal, principalHeatTerm_eq_div c]
    push_cast
    rfl
  · exact Eventually.of_forall fun _ => rfl

private lemma complexHeatTrace_isBigO_atTop (lambda : ℕ → ℝ) (c : ℝ)
    (hpos : ∀ n, 0 < lambda n) (hstrict : StrictMono lambda)
    (hfinite : ∀ u, Set.Finite {n | lambda n ≤ u})
    (hdensity : (fun u => spectralCounting lambda u - c * u) =O[atTop]
      (fun _ => (1 : ℝ))) :
    complexHeatTrace lambda =O[atTop]
      (fun t : ℝ => Real.exp (-(lambda 0) * t)) := by
  have hsumOne : Summable (fun n : ℕ => Real.exp (-1 * lambda n)) :=
    summable_heat lambda c 1 hpos hstrict hfinite hdensity one_pos
  let C : ℝ := Real.exp (lambda 0) * ∑' n : ℕ, Real.exp (-1 * lambda n)
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hsumT : Summable (fun n : ℕ => Real.exp (-t * lambda n)) :=
    summable_heat lambda c t hpos hstrict hfinite hdensity htpos
  have hnormSummable : Summable
      (fun n : ℕ => ‖(Real.exp (-t * lambda n) : ℂ)‖) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hsumT
  have hfactorNonneg : 0 ≤ Real.exp (-(t - 1) * lambda 0) := (Real.exp_pos _).le
  have hmajor : Summable (fun n : ℕ =>
      Real.exp (-(t - 1) * lambda 0) * Real.exp (-1 * lambda n)) :=
    hsumOne.mul_left _
  have hpoint (n : ℕ) : Real.exp (-t * lambda n) ≤
      Real.exp (-(t - 1) * lambda 0) * Real.exp (-1 * lambda n) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hlambda : lambda 0 ≤ lambda n := hstrict.monotone (Nat.zero_le n)
    nlinarith
  calc
    ‖complexHeatTrace lambda t‖ ≤
        ∑' n : ℕ, ‖(Real.exp (-t * lambda n) : ℂ)‖ := by
      exact norm_tsum_le_tsum_norm hnormSummable
    _ = ∑' n : ℕ, Real.exp (-t * lambda n) := by
      apply tsum_congr
      intro n
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    _ ≤ ∑' n : ℕ,
        Real.exp (-(t - 1) * lambda 0) * Real.exp (-1 * lambda n) :=
      hsumT.tsum_le_tsum hpoint hmajor
    _ = Real.exp (-(t - 1) * lambda 0) *
        ∑' n : ℕ, Real.exp (-1 * lambda n) := by rw [tsum_mul_left]
    _ = C * ‖Real.exp (-(lambda 0) * t)‖ := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      dsimp only [C]
      have hexp : Real.exp (-(t - 1) * lambda 0) =
          Real.exp (lambda 0) * Real.exp (-lambda 0 * t) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp]
      ring

/-- **Corollary 13.2 (spectral zeta continuation).** A positive strictly increasing real
spectrum with finite sublevel sets and linear counting density has a spectral Dirichlet series
which continues meromorphically to `re s > 0`; the continuation has residue `c` at `s = 1`. -/
theorem linear_density_spectral_zeta_continuation (lambda : ℕ → ℝ) (c : ℝ)
    (hpos : ∀ n, 0 < lambda n) (hstrict : StrictMono lambda)
    (hfinite : ∀ u, Set.Finite {n | lambda n ≤ u})
    (hdensity : (fun u => spectralCounting lambda u - c * u) =O[atTop]
      (fun _ => (1 : ℝ))) :
    IsSpectralZetaContinuation lambda (continuedSpectralZeta lambda c) ∧
      Tendsto (fun s : ℂ => (s - 1) * continuedSpectralZeta lambda c s)
        (𝓝[≠] 1) (𝓝 (c : ℂ)) := by
  let U : Set ℂ := {s | 0 < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hlocal := regularizedHeatTrace_locallyIntegrableOn
    lambda c hpos hstrict hfinite hdensity
  have hresidual := heat_residual_isBigO lambda c hpos hstrict hfinite hdensity
  have hthetaTop := complexHeatTrace_isBigO_atTop lambda c hpos hstrict hfinite hdensity
  have hregularizedTop : regularizedHeatTrace lambda c =O[atTop]
      (fun t : ℝ => Real.exp (-(lambda 0) * t)) := by
    apply hthetaTop.congr'
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
      simp [regularizedHeatTrace, not_le.mpr ht]
    · exact Eventually.of_forall fun _ => rfl
  have hregularizedBot : regularizedHeatTrace lambda c =O[𝓝[>] 0]
      (fun _ : ℝ => (1 : ℝ)) := by
    apply hresidual.congr'
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with t ht ht1
      simp [regularizedHeatTrace, ht1.le]
    · exact Eventually.of_forall fun _ => rfl
  have hfiniteCore :
      MeromorphicOn (spectralMellinCompletion lambda c) U ∧
        ∀ s : ℂ, 1 < s.re →
          MellinConvergent (complexHeatTrace lambda) s ∧
            spectralMellinCompletion lambda c s = mellin (complexHeatTrace lambda) s := by
    have hcore := finite_counterterm_mellin_continuation
      (m := 1) (complexHeatTrace lambda) (fun _ : Fin 1 => (c : ℂ))
      oneZeroExponent (lambda 0) oneZeroExponent_strictAnti (hpos 0)
      (by
        have hlocal' := hlocal
        unfold regularizedHeatTrace principalHeatTerm at hlocal'
        simpa [oneZeroExponent] using hlocal')
      (by
        have hresidual' := hresidual
        unfold principalHeatTerm at hresidual'
        simpa [oneZeroExponent] using hresidual')
      hthetaTop
    have hdomain : {s : ℂ | oneZeroExponent (Fin.last 1) < s.re} = U := by
      ext s
      simp [oneZeroExponent, U, Fin.last]
    rw [hdomain] at hcore
    constructor
    · refine hcore.1.congr ?_ hU
      intro s _
      simp [spectralMellinCompletion, principalHeatTerm]
    · intro s hs
      have hs' : oneZeroExponent 0 < s.re := by simpa using hs
      simpa [spectralMellinCompletion, principalHeatTerm] using hcore.2 s hs'
  have hregularizedConvergent (s : ℂ) (hs : s ∈ U) :
      MellinConvergent (regularizedHeatTrace lambda c) s :=
    mellinConvergent_of_isBigO_rpow_exp (a := lambda 0) (b := 0)
      (hpos 0) hlocal hregularizedTop
      (by simpa only [neg_zero, Real.rpow_zero] using hregularizedBot)
      (by simpa [U] using hs)
  have hregularizedDifferentiable :
      DifferentiableOn ℂ (mellin (regularizedHeatTrace lambda c)) U := by
    intro s hs
    exact (mellin_differentiableAt_of_isBigO_rpow_exp (a := lambda 0) (b := 0)
      (hpos 0) hlocal
      hregularizedTop (by simpa only [neg_zero, Real.rpow_zero] using hregularizedBot)
      (by simpa [U] using hs)).differentiableWithinAt
  have hsplit (s : ℂ) (hs : s ∈ U) :
      spectralMellinCompletion lambda c s =
        mellin (regularizedHeatTrace lambda c) s + (c : ℂ) / (s - 1) := by
    have hconv := hregularizedConvergent s hs
    have hleft : IntegrableOn
        (fun t : ℝ => (t : ℂ) ^ (s - 1) * regularizedHeatTrace lambda c t)
        (Set.Ioc 0 1) := hconv.mono_set Ioc_subset_Ioi_self
    have hright : IntegrableOn
        (fun t : ℝ => (t : ℂ) ^ (s - 1) * regularizedHeatTrace lambda c t)
        (Set.Ioi 1) := hconv.mono_set (Ioi_subset_Ioi zero_le_one)
    rw [spectralMellinCompletion, mellin]
    simp only [smul_eq_mul]
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hleft hright]
    have hleftEq :
        (∫ t in Set.Ioc (0 : ℝ) 1,
          (t : ℂ) ^ (s - 1) * (complexHeatTrace lambda t - principalHeatTerm c t)) =
        ∫ t in Set.Ioc (0 : ℝ) 1,
          (t : ℂ) ^ (s - 1) * regularizedHeatTrace lambda c t := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      simp [regularizedHeatTrace, ht.2]
    have hrightEq :
        (∫ t in Set.Ioi (1 : ℝ),
          (t : ℂ) ^ (s - 1) * complexHeatTrace lambda t) =
        ∫ t in Set.Ioi (1 : ℝ),
          (t : ℂ) ^ (s - 1) * regularizedHeatTrace lambda c t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      simp [regularizedHeatTrace, not_le.mpr (Set.mem_Ioi.mp ht)]
    rw [hleftEq, hrightEq]
  have hcontinuationMeromorphic :
      MeromorphicOn (continuedSpectralZeta lambda c) U := by
    have hinvGamma : MeromorphicOn (fun s : ℂ => (Gamma s)⁻¹) U :=
      (Complex.differentiable_one_div_Gamma.differentiableOn.analyticOnNhd hU).meromorphicOn
    refine (hfiniteCore.1.mul hinvGamma).congr ?_ hU
    intro s _
    simp only [continuedSpectralZeta, Pi.mul_apply, div_eq_mul_inv]
  have hagreement : ∀ s : ℂ, 1 < s.re →
      continuedSpectralZeta lambda c s = spectralZeta lambda s := by
    intro s hs
    have hsumComplex (t : ℝ) (ht : 0 < t) :
        Summable (fun n : ℕ => (Real.exp (-t * lambda n) : ℂ)) := by
      apply Summable.of_norm
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
        summable_heat lambda c t hpos hstrict hfinite hdensity ht
    have hMellin := hasSum_mellin
      (a := fun _ : ℕ => (1 : ℂ)) (p := lambda)
      (F := complexHeatTrace lambda) (s := s)
      (fun n => Or.inr (hpos n)) (lt_trans zero_lt_one hs)
      (fun t ht => by
        refine ((hsumComplex t (Set.mem_Ioi.mp ht)).hasSum).congr_fun ?_
        intro n
        simp only [one_mul]
        congr 2
        ring)
      (by
        simpa only [norm_one, one_div] using
          summable_spectral_rpow lambda c s.re hpos hstrict hfinite hdensity hs)
    have hmellinEq : mellin (complexHeatTrace lambda) s =
        Gamma s * spectralZeta lambda s := by
      calc
        mellin (complexHeatTrace lambda) s =
            ∑' n : ℕ, Gamma s * 1 / (lambda n : ℂ) ^ s := hMellin.tsum_eq.symm
        _ = ∑' n : ℕ, Gamma s * (lambda n : ℂ) ^ (-s) := by
          apply tsum_congr
          intro n
          rw [Complex.cpow_neg]
          simp only [mul_one, div_eq_mul_inv]
        _ = Gamma s * spectralZeta lambda s := by
          rw [spectralZeta, tsum_mul_left]
    rw [continuedSpectralZeta, hfiniteCore.2 s hs |>.2, hmellinEq]
    exact mul_div_cancel_left₀ _ (Gamma_ne_zero_of_re_pos (lt_trans zero_lt_one hs))
  refine ⟨⟨hcontinuationMeromorphic, hagreement⟩, ?_⟩
  have hHcontinuous : ContinuousAt (mellin (regularizedHeatTrace lambda c)) 1 := by
    exact (mellin_differentiableAt_of_isBigO_rpow_exp
      (a := lambda 0) (b := 0) (s := (1 : ℂ)) (hpos 0) hlocal
      hregularizedTop (by simpa only [neg_zero, Real.rpow_zero] using hregularizedBot)
      (by norm_num)).continuousAt
  have hzero : Tendsto
      (fun s : ℂ => (s - 1) * mellin (regularizedHeatTrace lambda c) s)
      (𝓝[≠] 1) (𝓝 0) := by
    have hsub : Tendsto (fun s : ℂ => s - 1) (nhds 1) (nhds 0) :=
      by
        have hone : Tendsto (fun _ : ℂ => (1 : ℂ)) (nhds 1) (nhds 1) :=
          tendsto_const_nhds
        simpa using tendsto_id.sub hone
    have h := hsub.mul hHcontinuous.tendsto
    simpa using h.mono_left nhdsWithin_le_nhds
  have hinvGamma : Tendsto (fun s : ℂ => (Gamma s)⁻¹) (𝓝[≠] 1) (𝓝 1) := by
    have h := Complex.differentiable_one_div_Gamma.continuous.tendsto 1
    simpa using h.mono_left nhdsWithin_le_nhds
  have hcInv : Tendsto (fun s : ℂ => (c : ℂ) * (Gamma s)⁻¹)
      (𝓝[≠] 1) (𝓝 (c : ℂ)) := by
    simpa using (tendsto_const_nhds.mul hinvGamma)
  have hlimit : Tendsto
      (fun s : ℂ =>
        ((s - 1) * mellin (regularizedHeatTrace lambda c) s) * (Gamma s)⁻¹ +
          (c : ℂ) * (Gamma s)⁻¹)
      (𝓝[≠] 1) (𝓝 (c : ℂ)) := by
    simpa only [zero_mul, zero_add] using (hzero.mul hinvGamma).add hcInv
  apply hlimit.congr'
  have hU_one : U ∈ 𝓝 (1 : ℂ) := hU.mem_nhds (by norm_num [U])
  have hU_one' : ∀ᶠ s in 𝓝[≠] (1 : ℂ), s ∈ U :=
    nhdsWithin_le_nhds hU_one
  filter_upwards [self_mem_nhdsWithin, hU_one'] with s hsne hsU
  have hs_ne : s - 1 ≠ 0 := sub_ne_zero.mpr hsne
  rw [continuedSpectralZeta, hsplit s hsU]
  field_simp

/-- Reverse probe for A1: the public continuation conjunct exposes meromorphicity at every point
of the positive real half-plane. -/
example (lambda : ℕ → ℝ) (Z : ℂ → ℂ)
    (h : IsSpectralZetaContinuation lambda Z) {s : ℂ} (hs : 0 < s.re) :
    MeromorphicAt Z s := h.1 s hs

/-- Reverse probe for A2: the public residue conjunct is the exact punctured-neighborhood limit. -/
example (lambda : ℕ → ℝ) (c : ℝ)
    (hpos : ∀ n, 0 < lambda n) (hstrict : StrictMono lambda)
    (hfinite : ∀ u, Set.Finite {n | lambda n ≤ u})
    (hdensity : (fun u => spectralCounting lambda u - c * u) =O[atTop]
      (fun _ => (1 : ℝ))) :
    Tendsto (fun s : ℂ => (s - 1) * continuedSpectralZeta lambda c s)
      (𝓝[≠] 1) (𝓝 (c : ℂ)) :=
  (linear_density_spectral_zeta_continuation lambda c hpos hstrict hfinite hdensity).2

/-- Trivialization probe: a constant spectrum cannot satisfy the strict-increase premise. -/
example (a : ℝ) : ¬ StrictMono (fun _ : ℕ => a) := by
  intro h
  exact (h Nat.zero_lt_one).ne rfl

#print axioms linear_density_spectral_zeta_continuation

end

end D5.S3.Analytic.Asymptotics.SpectralZetaContinuation
