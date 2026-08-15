/- GID: D5/S3/Analytic/CompletedZetaMellinReconstruction
   generality: I
   mirror-B: D5/B/S3/Analytic/CompletedZetaMellinReconstruction
   mirror-E: none(waiver:source-window-certificate-is-non-load-bearing)
   anchors: []
   digest: Reconstruct completed zeta from its symmetric theta-tail Mellin integral. -/

import D5.S3.Zeros.CompletedZeta
import D5.S3.Weil.Convention
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.MellinTransform

namespace D5.S3.Analytic.CompletedZetaMellinReconstruction

open D5.S3.Weil.Convention
open D5.S3.Zeros.CompletedZeta
open HurwitzZeta
open MeasureTheory Set Filter Topology Complex

/-- The symmetric theta tail `A t = 1_{t>1}·(θ(t) - 1)`, whose Mellin transform generates the
entire (pole-free) part of the completed zeta reading. -/
private noncomputable def tail : ℝ → ℂ :=
  (Set.Ioi (1 : ℝ)).indicator (fun t => ((evenKernel 0 t : ℝ) : ℂ) - 1)

private theorem tail_locInt : LocallyIntegrableOn tail (Ioi 0) := by
  have hg : LocallyIntegrableOn (fun t : ℝ => ((evenKernel 0 t : ℝ) : ℂ) - 1) (Ioi 0) :=
    ((continuous_ofReal.comp_continuousOn (continuousOn_evenKernel 0)).locallyIntegrableOn
      measurableSet_Ioi).sub (locallyIntegrableOn_const _)
  intro x hx
  obtain ⟨u, hu, hu'⟩ := hg x hx
  exact ⟨u, hu, hu'.indicator measurableSet_Ioi⟩

/-- The theta tail decays exponentially at `+∞`. -/
private theorem tail_isBigO_atTop : ∃ p : ℝ, 0 < p ∧ tail =O[atTop] fun t => Real.exp (-p * t) := by
  obtain ⟨p, hp, hp'⟩ := isBigO_atTop_evenKernel_sub 0
  refine ⟨p, hp, ?_⟩
  have hp'' : (fun t : ℝ => evenKernel 0 t - 1) =O[atTop] fun t => Real.exp (-p * t) := by
    simpa using hp'
  have hcoe : (fun t : ℝ => ((evenKernel 0 t : ℝ) : ℂ) - 1)
      =O[atTop] fun t => Real.exp (-p * t) := by
    rw [show (fun t : ℝ => ((evenKernel 0 t : ℝ) : ℂ) - 1)
        = (fun t : ℝ => ((evenKernel 0 t - 1 : ℝ) : ℂ)) by ext t; push_cast; ring]
    exact Complex.isBigO_ofReal_left.mpr hp''
  refine (Filter.EventuallyEq.isBigO ?_).trans hcoe
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  simp [tail, Set.indicator_of_mem (Set.mem_Ioi.mpr ht)]

/-- The theta tail vanishes near `0`, so it is dominated by any negative power there. -/
private theorem tail_isBigO_zero (b : ℝ) : tail =O[𝓝[>] (0 : ℝ)] fun t => t ^ (-b) := by
  have hz : tail =ᶠ[𝓝[>] (0 : ℝ)] 0 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
      with t _ ht1
    simp [tail, Set.indicator_of_notMem (by simp [Set.mem_Ioi]; linarith : t ∉ Set.Ioi (1 : ℝ))]
  exact hz.trans_isBigO (Asymptotics.isBigO_zero _ _)

/-- The Mellin transform of the theta tail is entire. -/
private theorem tail_mellin_differentiable : Differentiable ℂ (mellin tail) := by
  obtain ⟨p, hp, htop⟩ := tail_isBigO_atTop
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow_exp hp tail_locInt htop
    (tail_isBigO_zero (s.re - 1)) (by linarith)

/-- The theta tail Mellin integral converges at every complex point. -/
private theorem tail_mellinConvergent (w : ℂ) : MellinConvergent tail w := by
  obtain ⟨p, hp, htop⟩ := tail_isBigO_atTop
  exact mellinConvergent_of_isBigO_rpow_exp hp tail_locInt htop
    (tail_isBigO_zero (w.re - 1)) (by linarith)

/-- The reflected tail: `1_{0<t<1}·(θ(t) - t^{-1/2})`, the second summand of the modified kernel. -/
private noncomputable def shifted : ℝ → ℂ :=
  (Set.Ioo (0 : ℝ) 1).indicator
    (fun t => ((evenKernel 0 t : ℝ) : ℂ) - ((t ^ (-(1 / 2) : ℝ) : ℝ) : ℂ))

/-- The mathlib modified kernel splits into the theta tail and the reflected tail. -/
private theorem hfmodif_eq :
    (hurwitzEvenFEPair 0).f_modif = fun t => tail t + shifted t := by
  have hf0 : (hurwitzEvenFEPair 0).f₀ = 1 := if_pos rfl
  have hff : ∀ x, (hurwitzEvenFEPair 0).f x = ((evenKernel 0 x : ℝ) : ℂ) := fun _ => rfl
  have hε : (hurwitzEvenFEPair 0).ε = 1 := rfl
  have hk : (hurwitzEvenFEPair 0).k = 1 / 2 := rfl
  have hg0 : (hurwitzEvenFEPair 0).g₀ = 1 := rfl
  funext t
  simp only [WeakFEPair.f_modif, Pi.add_apply, tail, shifted, hf0, hff, hε, hk, hg0,
    one_mul, smul_eq_mul, mul_one]

/-- On the positive axis, the reflected tail is a `t^{-1/2}` rescaling of the theta tail at `t⁻¹`,
via the theta functional equation. -/
private theorem shifted_pointwise :
    ∀ t ∈ Set.Ioi (0 : ℝ), shifted t = (t : ℂ) ^ (-(1 / 2) : ℂ) • tail t⁻¹ := by
  intro t ht
  rw [Set.mem_Ioi] at ht
  have hcpow : ((t ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) = (t : ℂ) ^ (-(1 / 2) : ℂ) := by
    rw [Complex.ofReal_cpow ht.le]; push_cast; ring_nf
  rcases lt_or_ge t 1 with h1 | h1
  · -- inside (0,1): both indicators fire
    have htinv : (1 : ℝ) < t⁻¹ := by rw [one_lt_inv_iff₀]; exact ⟨ht, h1⟩
    have hFE : (evenKernel 0 t : ℂ) = (t : ℂ) ^ (-(1 / 2) : ℂ) * (evenKernel 0 t⁻¹ : ℂ) := by
      have h := evenKernel_functional_equation (0 : UnitAddCircle) t
      rw [← evenKernel_eq_cosKernel_of_zero] at h
      have e1 : (1 : ℝ) / t ^ (1 / 2 : ℝ) = t ^ (-(1 / 2) : ℝ) := by
        rw [Real.rpow_neg ht.le, one_div]
      rw [e1, one_div t] at h
      have h2 := congrArg (Complex.ofReal) h
      rw [Complex.ofReal_mul, hcpow] at h2
      exact h2
    rw [shifted, Set.indicator_of_mem (Set.mem_Ioo.mpr ⟨ht, h1⟩),
      tail, Set.indicator_of_mem (Set.mem_Ioi.mpr htinv), hcpow, hFE, smul_eq_mul, mul_sub,
      mul_one]
  · -- at or beyond 1: both indicators vanish
    have htout : t ∉ Set.Ioo (0 : ℝ) 1 := fun h => absurd h.2 (not_lt.mpr h1)
    have htinvout : t⁻¹ ∉ Set.Ioi (1 : ℝ) := by
      rw [Set.mem_Ioi, not_lt]
      exact inv_le_one_of_one_le₀ h1
    rw [shifted, Set.indicator_of_notMem htout, tail, Set.indicator_of_notMem htinvout, smul_zero]

/-- The reflected tail's Mellin transform is the theta tail's reflected across `w ↦ 1/2 - w`. -/
private theorem shifted_mellin_eq (w : ℂ) : mellin shifted w = mellin tail (1 / 2 - w) := by
  have hstep : mellin shifted w = mellin (fun t => (t : ℂ) ^ (-(1 / 2) : ℂ) • tail t⁻¹) w := by
    simp only [mellin]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [shifted_pointwise t ht]
  rw [hstep, mellin_cpow_smul (fun t => tail t⁻¹) w (-(1 / 2)), mellin_comp_inv tail (w + -(1 / 2))]
  congr 1
  ring

/-- Core: the Mellin transform of the mathlib modified kernel splits as a symmetric sum of two
tail Mellin values, reflected across `w ↦ 1/2 - w`. -/
private theorem fmodif_mellin_split (w : ℂ) :
    mellin ((hurwitzEvenFEPair 0).f_modif) w = mellin tail w + mellin tail (1 / 2 - w) := by
  have hconvT : MellinConvergent tail w := tail_mellinConvergent w
  have hconvS : MellinConvergent shifted w := by
    have hinv : MellinConvergent (fun t => tail (t ^ (-1 : ℝ))) (w + -(1 / 2)) :=
      (MellinConvergent.comp_rpow (f := tail) (s := w + -(1 / 2)) (a := -1)
        (by norm_num)).2 (by
          convert tail_mellinConvergent (1 / 2 - w) using 1 <;> norm_num <;> ring)
    have hscaled : MellinConvergent
        (fun t => (t : ℂ) ^ (-(1 / 2) : ℂ) • tail (t ^ (-1 : ℝ))) w :=
      MellinConvergent.cpow_smul.mpr hinv
    have hscaledInv : MellinConvergent
        (fun t => (t : ℂ) ^ (-(1 / 2) : ℂ) • tail t⁻¹) w := by
      simpa only [Real.rpow_neg_one] using hscaled
    rw [MellinConvergent] at hscaledInv ⊢
    rw [integrableOn_congr_fun (fun t ht => by
      rw [shifted_pointwise t ht]) measurableSet_Ioi]
    exact hscaledInv
  have hconvF : MellinConvergent ((hurwitzEvenFEPair 0).f_modif) w := by
    rw [hfmodif_eq]
    exact (hasMellin_add hconvT hconvS).1
  rw [hfmodif_eq, (hasMellin_add hconvT hconvS).2, shifted_mellin_eq]

/-- Master identity: the symmetric theta-tail Mellin integral equals the entire completed zeta. -/
private theorem symmetric_mellin_eq_completed (s : ℂ) :
    (∫ t in Set.Ioi (1 : ℝ), (((evenKernel 0 t : ℝ) : ℂ) - 1) / 2 *
        ((t : ℂ) ^ (s / 2) + (t : ℂ) ^ ((1 - s) / 2)) / (t : ℂ))
      = completedRiemannZeta₀ s := by
  -- `mellin tail` written as a genuine integral over `Ioi 1`
  have hmt : ∀ z : ℂ, mellin tail z
      = ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (z - 1) * (((evenKernel 0 t : ℝ) : ℂ) - 1) := by
    intro z
    rw [mellin,
      show (fun t : ℝ => (t : ℂ) ^ (z - 1) • tail t)
          = (Set.Ioi (1 : ℝ)).indicator
              (fun t => (t : ℂ) ^ (z - 1) * (((evenKernel 0 t : ℝ) : ℂ) - 1)) by
        funext t
        by_cases h : t ∈ Set.Ioi (1 : ℝ)
        · simp only [tail, Set.indicator_of_mem h, smul_eq_mul]
        · simp only [tail, Set.indicator_of_notMem h, smul_zero],
      setIntegral_indicator measurableSet_Ioi,
      Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))]
  -- each summand is integrable on `Ioi 1`
  have hsub : Set.Ioi (1 : ℝ) ⊆ Set.Ioi 0 := Set.Ioi_subset_Ioi (by norm_num)
  have hint : ∀ z : ℂ,
      IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 1) * (((evenKernel 0 t : ℝ) : ℂ) - 1))
        (Set.Ioi 1) := by
    intro z
    refine ((tail_mellinConvergent z).mono_set hsub).congr_fun ?_ measurableSet_Ioi
    intro t ht
    simp only [tail, Set.indicator_of_mem ht, smul_eq_mul]
  -- unfold completed zeta through the modified-kernel Mellin split
  have hcompleted : completedRiemannZeta₀ s
      = mellin ((hurwitzEvenFEPair 0).f_modif) (s / 2) / 2 := rfl
  have hRHS : completedRiemannZeta₀ s
      = (∫ t in Set.Ioi (1 : ℝ), ((t : ℂ) ^ (s / 2 - 1) * (((evenKernel 0 t : ℝ) : ℂ) - 1)
          + (t : ℂ) ^ ((1 - s) / 2 - 1) * (((evenKernel 0 t : ℝ) : ℂ) - 1))) / 2 := by
    rw [hcompleted, fmodif_mellin_split (s / 2),
      show (1 : ℂ) / 2 - s / 2 = (1 - s) / 2 from by ring, hmt (s / 2), hmt ((1 - s) / 2),
      ← integral_add (hint (s / 2)) (hint ((1 - s) / 2))]
  rw [hRHS, ← integral_div]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  rw [Set.mem_Ioi] at ht
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (lt_trans one_pos ht).ne'
  dsimp only
  rw [Complex.cpow_sub _ _ ht0, Complex.cpow_sub _ _ ht0, Complex.cpow_one]
  ring

theorem completed_zeta_mellin_reconstruction :
    let theta : ℝ → ℂ := fun t => ((evenKernel 0 t : ℝ) : ℂ)
    let omega : ℝ → ℂ := fun t => (theta t - 1) / 2
    let M : ℂ → ℂ := fun s => ∫ t in Set.Ioi (1 : ℝ),
        omega t * ((t : ℂ) ^ (s / 2) + (t : ℂ) ^ ((1 - s) / 2)) / (t : ℂ)
    (∀ s : ℂ, 1 < s.re →
        completedZetaReading s
          = (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * classicalZeta s) ∧
    (∀ s : ℂ, completedZetaReading s = M s - 1 / s - 1 / (1 - s)) ∧
    Differentiable ℂ M ∧
    (∀ s : ℂ, M (1 - s) = M s) ∧
    (∀ s : ℂ, s ≠ 0 → s ≠ 1 → DifferentiableAt ℂ completedZetaReading s) ∧
    (Tendsto (fun s : ℂ => s * completedZetaReading s) (𝓝[≠] (0 : ℂ)) (𝓝 (-1)) ∧
      Tendsto (fun s : ℂ => (s - 1) * completedZetaReading s) (𝓝[≠] (1 : ℂ)) (𝓝 1)) ∧
    (∀ s : ℂ, xiReading (1 - s) = xiReading s) := by
  intro theta omega M
  have hM : ∀ s : ℂ, M s = completedRiemannZeta₀ s := fun s => symmetric_mellin_eq_completed s
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · -- clause 1: Euler-product completion form on the convergence half-plane
    intro s hs
    have hs0 : s ≠ 0 := by rintro rfl; simp only [Complex.zero_re] at hs; linarith
    have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
    change completedRiemannZeta s
        = (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * riemannZeta s
    rw [← Gammaℝ_def, riemannZeta_def_of_ne_zero hs0]
    field_simp
  · -- clause 2: the Mellin reconstruction with explicit pole terms
    intro s
    change completedRiemannZeta s = M s - 1 / s - 1 / (1 - s)
    rw [completedRiemannZeta_eq, hM s]
  · -- clause 3: `M` is entire
    exact (funext hM : M = completedRiemannZeta₀) ▸ differentiable_completedZeta₀
  · -- clause 4: `M` is reflection-symmetric
    intro s
    rw [hM (1 - s), hM s, completedRiemannZeta₀_one_sub]
  · -- clause 5: the completed reading is differentiable off the two poles
    intro s hs0 hs1
    change DifferentiableAt ℂ completedRiemannZeta s
    exact differentiableAt_completedZeta hs0 hs1
  · -- clause 6a: residue `-1` at `s = 0`
    have hif : (if (0 : UnitAddCircle) = 0 then (-1 : ℂ) else 0) = -1 := if_pos rfl
    have h := completedHurwitzZetaEven_residue_zero (0 : UnitAddCircle)
    rw [hif] at h
    exact Tendsto.congr
      (fun s => by simp only [completedZetaReading, HurwitzZeta.completedHurwitzZetaEven_zero]) h
  · -- clause 6b: residue `1` at `s = 1`
    exact completedRiemannZeta_residue_one
  · -- clause 7: reflection symmetry of the xi reading
    intro s
    exact xi_reading_reflection s

end D5.S3.Analytic.CompletedZetaMellinReconstruction
