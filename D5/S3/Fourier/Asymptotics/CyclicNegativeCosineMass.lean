/- GID: D5/S3/Fourier/Asymptotics/CyclicNegativeCosineMass
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/CyclicNegativeCosineMass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Negative-cosine mass limit for joint cyclic minimizers. -/

import D5.S3.Fourier.Asymptotics.CyclicToLatticeComparison
import D5.S3.Fourier.Concentration.ActiveCosineConstraints
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! The scaled second cosine deficit outside the fixed lattice support tends to zero.
It bounds the errors in recovering the negative-cosine mass from the first deficit. -/

open Filter Finset
open scoped Topology
open D5.S3.Fourier.Asymptotics.LatticeSquareMomentActivation
open D5.S3.Fourier.Asymptotics.CyclicToLatticeComparison
open D5.S3.Fourier.Concentration.ActiveCosineConstraints

noncomputable section

namespace D5.S3.Fourier.Asymptotics.CyclicNegativeCosineMass

set_option autoImplicit false

private theorem mode_residue {q : ℕ} (r : ℕ) (i : ZMod q) :
    D5.S3.Fourier.Concentration.AggregateCosineBalance.mode i (r : ℤ) =
      Real.cos ((r : ℝ) * (2 * Real.pi * (i.val : ℝ) / q)) := by
  unfold D5.S3.Fourier.Concentration.AggregateCosineBalance.mode
  rw [Int.cast_natCast]
  congr 1
  ring

private theorem cos_residue_eq {q : ℕ} [NeZero q] (r : ℕ) (i : ZMod q) :
    Real.cos ((r : ℝ) * (2 * Real.pi * (i.val : ℝ) / q)) =
      Real.cos ((r : ℝ) * centeredAngle i) := by
  classical
  have h := cosineMoment_eq_centered r (Pi.single i (1 : ℝ))
  dsimp [cosineMoment] at h
  simpa [mode_residue, Pi.single_apply, ite_mul, Finset.sum_ite_eq'] using h

private theorem eventually_centered (j : ℤ) :
    ∀ᶠ k : ℕ in atTop, (j : ZMod k.succ).valMinAbs = j := by
  filter_upwards [eventually_ge_atTop (2 * j.natAbs)] with k hk
  have h : (2 * j.natAbs : ℤ) ≤ k := by exact_mod_cast hk
  have hj : |j| = (j.natAbs : ℤ) := (Int.natCast_natAbs j).symm
  have ⟨hl, hu⟩ := abs_le.mp hj.le
  exact (ZMod.valMinAbs_spec _ _).mpr ⟨rfl, by constructor <;> omega⟩

private theorem inv_modulus_tendsto :
    Tendsto (fun k : ℕ => (k.succ : ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))

private theorem lattice_site_tendsto {lam t Z : ℝ} {n : ℕ} {w : ℤ → ℝ}
    (hn : 0 < n) (hmlo : ((n : ℝ) ^ 2 - 1) / 5 ≤ lam / (8 * Real.pi ^ 2))
    (hmhi : lam / (8 * Real.pi ^ 2) ≤ (n : ℝ) * (n + 2) / 5)
    (A : Activation (lam / (8 * Real.pi ^ 2)) n t Z w)
    {v : (k : ℕ) → ZMod k.succ → ℝ}
    (hv : ∀ᶠ k in atTop,
      v k ∈ feasible k.succ (1 - lam / (k.succ : ℝ) ^ 2) ∧
        IsMinOn energy (feasible k.succ (1 - lam / (k.succ : ℝ) ^ 2)) (v k))
    (j : ℤ) : Tendsto (fun k => v k (j : ZMod k.succ)) atTop (𝓝 (w j)) := by
  have hdist : ∀ᶠ k : ℕ in atTop, (v k (j : ZMod k.succ) - w j) ^ 2 ≤
      (2 * t / Z) * (lam / (k.succ : ℝ) ^ 2) := by
    filter_upwards [hv, eventually_centered j, eventually_ge_atTop (2 * n)] with k hmin hj hk
    have hq : 2 * latticeSupportRadius n (lam / (8 * Real.pi ^ 2)) < k.succ := by
      unfold latticeSupportRadius
      split <;> omega
    obtain ⟨t', Z', w', A', hcompare, u, hu, _, hgap, _, _⟩ :=
      cyclic_to_lattice_comparison k.succ n hn lam hq hmlo hmhi
    obtain ⟨a, ha, huniq⟩ :=
      (exists_lattice_square_moment_minimizer_on_interval n hn _).mp ⟨hmlo, hmhi⟩
    have heq : (t', Z', w') = (t, Z, w) :=
      (huniq (t', Z', w') A').trans (huniq (t, Z, w) A).symm
    obtain ⟨htEq, hZEq, hwEq⟩ := Prod.mk.inj heq |>.imp_right Prod.mk.inj
    subst t' Z' w'
    have h := hcompare (v k) hmin.1.1 hmin.1.2.1
    have ht : 0 ≤ t := (sq_nonneg _).trans A.radius_lower
    have hs₁ := mul_nonneg
      (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ht) A.normalizer_pos.le)
      (sub_nonneg.mpr hmin.1.2.2.1)
    have hs₂ := mul_nonneg
      (div_nonneg (sq_nonneg ((k.succ : ℝ) / (2 * Real.pi))) A.normalizer_pos.le)
      (sub_nonneg.mpr hmin.1.2.2.2)
    have hvu : energy (v k) ≤ energy u := hmin.2 hu
    have hpoint := single_le_sum (f := fun i : ZMod k.succ => (v k i - w i.valMinAbs) ^ 2)
      (fun i _ => sq_nonneg _) (mem_univ (j : ZMod k.succ))
    rw [hj] at hpoint
    linarith only [hpoint, h, hgap, hvu, hs₁, hs₂]
  have hbound : Tendsto (fun k : ℕ => (2 * t / Z) * (lam / (k.succ : ℝ) ^ 2)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, inv_pow] using
      (tendsto_const_nhds (x := 2 * t / Z)).mul
        ((tendsto_const_nhds (x := lam)).mul (inv_modulus_tendsto.pow 2))
  have hsquare := tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hbound (Eventually.of_forall fun k => sq_nonneg _) hdist
  have habs : Tendsto (fun k => |v k (j : ZMod k.succ) - w j|) atTop (𝓝 0) := by
    simpa [Function.comp_def, Real.sqrt_sq_eq_abs] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
  exact tendsto_iff_dist_tendsto_zero.mpr (by simpa [Real.dist_eq] using habs)

private theorem scaled_cos_tendsto (b : ℝ) :
    Tendsto (fun k : ℕ => (k.succ : ℝ) ^ 2 * (1 - Real.cos (2 * (b / k.succ))))
      atTop (𝓝 (2 * b ^ 2)) := by
  have hsmall : Tendsto (fun k : ℕ => b / (k.succ : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using inv_modulus_tendsto.const_mul b
  have hsinc : Tendsto (fun k : ℕ => Real.sinc (b / k.succ)) atTop (𝓝 1) := by
    simpa [Function.comp_def] using Real.continuous_sinc.continuousAt.tendsto.comp hsmall
  have hlim : Tendsto (fun k : ℕ => 2 * b ^ 2 * Real.sinc (b / k.succ) ^ 2)
      atTop (𝓝 (2 * b ^ 2)) := by
    simpa using (hsinc.pow 2).const_mul (2 * b ^ 2)
  apply hlim.congr
  intro k
  rw [Real.cos_two_mul_eq_one_sub]
  have hk : (k.succ : ℝ) ≠ 0 := by positivity
  by_cases hb : b = 0
  · simp [hb]
  · rw [Real.sinc_of_ne_zero (div_ne_zero hb hk)]
    field_simp
    ring

private def deficit {q : ℕ} (r : ℕ) (v : ZMod q → ℝ) (i : ZMod q) : ℝ :=
  (q : ℝ) ^ 2 * (1 - Real.cos ((r : ℝ) * centeredAngle i)) * v i

private theorem total_deficits {q : ℕ} [NeZero q] (hq : 4 ≤ q) {lam : ℝ}
    (hpos : 0 < 1 - lam / (q : ℝ) ^ 2) (hlam : 0 ≤ lam)
    {v : ZMod q → ℝ} (hv : v ∈ feasible q (1 - lam / (q : ℝ) ^ 2))
    (hmin : IsMinOn energy (feasible q (1 - lam / (q : ℝ) ^ 2)) v) :
    (∑ i, deficit 1 v i) = lam ∧ (∑ i, deficit 2 v i) = lam := by
  have hfirst (i : ZMod q) :
      D5.S3.Fourier.Concentration.AggregateCosineBalance.mode i ((1 : ℕ) : ℤ) =
        Real.cos (2 * Real.pi * (i.val : ℝ) / q) := by
    simpa only [Nat.cast_one, one_mul] using mode_residue 1 i
  have hsecond (i : ZMod q) :
      D5.S3.Fourier.Concentration.AggregateCosineBalance.mode i ((2 : ℕ) : ℤ) =
        Real.cos (4 * Real.pi * (i.val : ℝ) / q) := by
    rw [mode_residue]
    congr 1
    push_cast
    ring
  have heq : cosineMoment 1 v = 1 - lam / (q : ℝ) ^ 2 ∧
      cosineMoment 2 v = 1 - lam / (q : ℝ) ^ 2 := by
    rcases hlam.eq_or_lt with hzero | hpositive
    · subst lam
      have hm (r : ℕ) : cosineMoment r v ≤ 1 := by
        unfold cosineMoment
        calc
          _ ≤ ∑ i, v i := by
            apply sum_le_sum
            intro i _
            exact mul_le_of_le_one_right (hv.1 i) (Real.cos_le_one _)
          _ = _ := hv.2.1
      simpa using And.intro (le_antisymm (hm 1) (by simpa using hv.2.2.1))
        (le_antisymm (hm 2) (by simpa using hv.2.2.2))
    have hlt : 1 - lam / (q : ℝ) ^ 2 < 1 := by
      have h := div_pos hpositive (show 0 < (q : ℝ) ^ 2 by positivity)
      linarith
    simp only [cosineMoment, hfirst, hsecond]
    apply (active_cosine_constraints hq hpos hlt).2.2
    refine ⟨⟨⟨hv.1, hv.2.1⟩, ?_⟩, ?_⟩
    · simpa only [cosineMoment, hfirst, hsecond] using hv.2.2
    · intro u hu
      apply hmin
      refine ⟨hu.1.1, hu.1.2, ?_⟩
      simpa only [cosineMoment, hfirst, hsecond] using hu.2
  have htotal (r : ℕ) (hr : cosineMoment r v = 1 - lam / (q : ℝ) ^ 2) :
      ∑ i, deficit r v i = lam := by
    calc
      _ = (q : ℝ) ^ 2 * ((∑ i, v i) - cosineMoment r v) := by
        rw [cosineMoment_eq_centered]
        rw [← sum_sub_distrib, mul_sum]
        apply sum_congr rfl
        intro i _
        unfold deficit
        ring
      _ = lam := by
        have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
        rw [hv.2.1, hr]
        field_simp
        ring
  exact ⟨htotal 1 heq.1, htotal 2 heq.2⟩

/-- The rescaled mass where the first cosine is negative converges to three eighths
of the deficit parameter for every eventual choice of full cyclic minimizers.
The moduli run through all positive integers. -/
theorem cyclic_negative_cosine_mass_limit (lam : ℝ) (hlam : 0 ≤ lam)
    (v : (k : ℕ) → ZMod k.succ → ℝ)
    (hv : ∀ᶠ k in atTop,
      v k ∈ feasible k.succ (1 - lam / (k.succ : ℝ) ^ 2) ∧
        IsMinOn energy (feasible k.succ (1 - lam / (k.succ : ℝ) ^ 2)) (v k)) :
    let limitValue := fun x : ℝ => 3 * x / 8
    let readout (k : ℕ) (i : ZMod k.succ) := Real.cos (2 * Real.pi * (i.val : ℝ) / k.succ)
    let negative (k : ℕ) := (univ : Finset (ZMod k.succ)).filter (fun i => readout k i < 0)
    Tendsto (fun k : ℕ => (k.succ : ℝ) ^ 2 * ∑ i ∈ negative k, v k i)
      atTop (𝓝 (limitValue lam)) ∧
    Tendsto (fun k : ℕ => ∑ i ∈ negative k,
      (k.succ : ℝ) ^ 2 * (1 + readout k i) * v k i) atTop (𝓝 0) := by
  let m := lam / (8 * Real.pi ^ 2)
  obtain ⟨⟨n, t, Z, w⟩, ⟨hn, ⟨hmlo, hmhi⟩, A⟩, _⟩ :=
    (exists_lattice_square_moment_minimizer m).mp (by positivity)
  let S := A.finite_support.toFinset
  let sites (k : ℕ) := S.image (fun j : ℤ => (j : ZMod k.succ))
  let front (k : ℕ) := (univ : Finset (ZMod k.succ)).filter (fun i => 0 ≤ Real.cos (centeredAngle i))
  let back (k : ℕ) := (univ : Finset (ZMod k.succ)).filter (fun i => Real.cos (centeredAngle i) < 0)
  let core (r k : ℕ) := ∑ i ∈ sites k, deficit r (v k) i
  let tail (k : ℕ) := ∑ i ∈ univ \ sites k, deficit 2 (v k) i
  let frontDeficit (k : ℕ) := ∑ i ∈ front k, deficit 1 (v k) i
  let frontTail (k : ℕ) := ∑ i ∈ front k \ sites k, deficit 1 (v k) i
  let backError (k : ℕ) := ∑ i ∈ back k,
    (k.succ : ℝ) ^ 2 * (1 + Real.cos (centeredAngle i)) * v k i
  let backMass (k : ℕ) := (k.succ : ℝ) ^ 2 * ∑ i ∈ back k, v k i
  have hsite := lattice_site_tendsto hn hmlo hmhi.le A hv
  have hcent : ∀ᶠ k : ℕ in atTop, ∀ j ∈ S, (j : ZMod k.succ).valMinAbs = j :=
    (eventually_all_finset S).mpr (fun j _ => eventually_centered j)
  have hfront : ∀ᶠ k in atTop, sites k ⊆ front k := by
    have hsmall (j : ℤ) : Tendsto (fun k : ℕ => 2 * Real.pi * (j : ℝ) / k.succ)
        atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using inv_modulus_tendsto.const_mul (2 * Real.pi * (j : ℝ))
    have hpos : ∀ᶠ k : ℕ in atTop, ∀ j ∈ S, 0 ≤ Real.cos (2 * Real.pi * (j : ℝ) / k.succ) :=
      (eventually_all_finset S).mpr fun j _ =>
        (Real.continuous_cos.continuousAt.tendsto.comp (hsmall j)).eventually
          (Ici_mem_nhds (by simp : (0 : ℝ) < Real.cos 0))
    filter_upwards [hcent, hpos] with k hc hp i hi
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    simpa only [centeredAngle, hc j hj] using hp j hj
  have hmoment : ∑ j ∈ S, (j : ℝ) ^ 2 * w j = m := by
    refine (hasSum_sum_of_ne_finset_zero (s := S) ?_).unique A.second_moment
    intro j hj
    have hw : w j = 0 := by
      by_contra h
      exact hj (A.finite_support.mem_toFinset.mpr h)
    simp [hw]
  have hcore (r : ℕ) :
      Tendsto (core r) atTop (𝓝 (2 * Real.pi ^ 2 * (r : ℝ) ^ 2 * m)) := by
    have hterm (j : ℤ) :
        Tendsto (fun k : ℕ => ((k.succ : ℝ) ^ 2 *
          (1 - Real.cos (2 * (Real.pi * (r : ℝ) * (j : ℝ) / k.succ)))) *
          v k (j : ZMod k.succ)) atTop
          (𝓝 (2 * Real.pi ^ 2 * (r : ℝ) ^ 2 * ((j : ℝ) ^ 2 * w j))) := by
      convert (scaled_cos_tendsto (Real.pi * (r : ℝ) * (j : ℝ))).mul (hsite j) using 2
      ring
    have hs := tendsto_finsetSum S (fun j _ => hterm j)
    rw [← mul_sum, hmoment] at hs
    apply hs.congr'
    filter_upwards [hcent] with k hc
    unfold core sites
    rw [sum_image (fun a ha b hb hab => by
      simpa only [hc a ha, hc b hb] using congrArg ZMod.valMinAbs hab)]
    apply sum_congr rfl
    intro j hj
    rw [deficit, centeredAngle, hc j hj]
    rw [show (r : ℝ) * (2 * Real.pi * (j : ℝ) / k.succ) =
      2 * (Real.pi * (r : ℝ) * (j : ℝ) / k.succ) by ring]
  have hcore₁ : Tendsto (core 1) atTop (𝓝 (lam / 4)) := by
    convert hcore 1 using 2
    norm_num [m]
    field_simp [Real.pi_ne_zero] <;> ring
  have hcore₂ : Tendsto (core 2) atTop (𝓝 lam) := by
    convert hcore 2 using 2
    norm_num [m]
    field_simp [Real.pi_ne_zero] <;> ring
  have htotal : ∀ᶠ k in atTop,
      (∑ i, deficit 1 (v k) i) = lam ∧ (∑ i, deficit 2 (v k) i) = lam := by
    have hsmall : Tendsto (fun k : ℕ => lam / (k.succ : ℝ) ^ 2) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv, inv_pow] using (inv_modulus_tendsto.pow 2).const_mul lam
    filter_upwards [hv, eventually_ge_atTop 3, hsmall.eventually (Iio_mem_nhds zero_lt_one)]
      with k hmin hk hsmall'
    exact total_deficits (by omega) (sub_pos.mpr hsmall') hlam hmin.1 hmin.2
  -- The fixed lattice sites exhaust the limiting second deficit.
  have htail : Tendsto tail atTop (𝓝 0) := by
    apply (show Tendsto (fun k => lam - core 2 k) atTop (𝓝 0) by
      simpa using (tendsto_const_nhds (x := lam)).sub hcore₂).congr'
    filter_upwards [htotal] with k h
    have hsplit := sum_sdiff (subset_univ (sites k)) (f := deficit 2 (v k))
    change tail k + core 2 k = _ at hsplit
    linarith only [hsplit, h.2]
  have hsqueeze {region : (k : ℕ) → Finset (ZMod k.succ)}
      {f : (k : ℕ) → ZMod k.succ → ℝ}
      (hsubset : ∀ᶠ k in atTop, region k ⊆ univ \ sites k)
      (hbound : ∀ᶠ k in atTop, ∀ i ∈ region k, 0 ≤ f k i ∧ f k i ≤ deficit 2 (v k) i / 2) :
      Tendsto (fun k => ∑ i ∈ region k, f k i) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (show Tendsto (fun k => tail k / 2) atTop (𝓝 0) by simpa using htail.div_const 2)
    · filter_upwards [hbound] with k hk
      exact sum_nonneg (fun i hi => (hk i hi).1)
    · filter_upwards [hv, hsubset, hbound] with k hk hsub hb
      rw [show tail k / 2 = ∑ i ∈ univ \ sites k, deficit 2 (v k) i / 2 by
        simp only [tail, sum_div]]
      exact (sum_le_sum fun i hi => (hb i hi).2).trans
        (sum_le_sum_of_subset_of_nonneg hsub fun i _ _ =>
          div_nonneg
            (mul_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (Real.cos_le_one _)))
              (hk.1.1 i)) (by norm_num))
  have hhalf {k : ℕ} (i : ZMod k.succ) :
      deficit 2 (v k) i / 2 =
        (k.succ : ℝ) ^ 2 * (1 - Real.cos (centeredAngle i) ^ 2) * v k i := by
    simp only [deficit, Nat.cast_ofNat, Real.cos_two_mul]
    ring
  have hfrontTail : Tendsto frontTail atTop (𝓝 0) := by
    apply hsqueeze (Eventually.of_forall fun k =>
      Finset.sdiff_subset_sdiff_left (sites k) (subset_univ (front k)))
    filter_upwards [hv] with k hk i hi
    have hf : i ∈ front k := (mem_sdiff.mp hi).1
    have hc := (mem_filter.mp hf).2
    have hle := Real.cos_le_one (centeredAngle i)
    have hweight := mul_nonneg (sq_nonneg (k.succ : ℝ)) (hk.1.1 i)
    rw [hhalf]
    simp only [deficit, Nat.cast_one, one_mul]
    constructor
    · exact mul_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hle)) (hk.1.1 i)
    · calc
        _ = (1 - Real.cos (centeredAngle i)) * ((k.succ : ℝ) ^ 2 * v k i) := by ring
        _ ≤ (1 - Real.cos (centeredAngle i) ^ 2) * ((k.succ : ℝ) ^ 2 * v k i) :=
          mul_le_mul_of_nonneg_right (by nlinarith only [mul_nonneg hc (sub_nonneg.mpr hle)]) hweight
        _ = _ := by ring
  have hfrontDeficit : Tendsto frontDeficit atTop (𝓝 (lam / 4)) := by
    apply (show Tendsto (fun k => frontTail k + core 1 k) atTop (𝓝 (lam / 4)) by
      simpa using hfrontTail.add hcore₁).congr'
    filter_upwards [hfront] with k hk
    exact sum_sdiff hk
  have hbackError : Tendsto backError atTop (𝓝 0) := by
    apply hsqueeze
    · filter_upwards [hfront] with k hsf i hi
      refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
      intro hs
      have hf := (mem_filter.mp (hsf hs)).2
      have hb := (mem_filter.mp hi).2
      exact (not_lt_of_ge hf) hb
    · filter_upwards [hv] with k hk i hi
      have hc := (mem_filter.mp hi).2
      have hplus : 0 ≤ 1 + Real.cos (centeredAngle i) := by linarith [Real.neg_one_le_cos (centeredAngle i)]
      have hweight := mul_nonneg (sq_nonneg (k.succ : ℝ)) (hk.1.1 i)
      rw [hhalf]
      constructor
      · exact mul_nonneg (mul_nonneg (sq_nonneg _) hplus) (hk.1.1 i)
      · calc
          _ = (1 + Real.cos (centeredAngle i)) * ((k.succ : ℝ) ^ 2 * v k i) := by ring
          _ ≤ (1 - Real.cos (centeredAngle i) ^ 2) * ((k.succ : ℝ) ^ 2 * v k i) :=
            mul_le_mul_of_nonneg_right
              (by nlinarith only [mul_nonneg (neg_nonneg.mpr hc.le) hplus]) hweight
          _ = _ := by ring
  have hmass : Tendsto backMass atTop (𝓝 (3 * lam / 8)) := by
    have hlim := (((tendsto_const_nhds (x := lam)).sub hfrontDeficit).add hbackError).div_const 2
    rw [show (lam - lam / 4 + 0) / 2 = 3 * lam / 8 by ring] at hlim
    apply hlim.congr'
    filter_upwards [htotal] with k hk
    have hsplit : frontDeficit k + ∑ i ∈ back k, deficit 1 (v k) i =
        ∑ i, deficit 1 (v k) i := by
      simpa only [frontDeficit, front, back, not_le] using
        sum_filter_add_sum_filter_not univ (fun i => 0 ≤ Real.cos (centeredAngle i)) (deficit 1 (v k))
    have hback : (∑ i ∈ back k, deficit 1 (v k) i) + backError k = 2 * backMass k := by
      unfold backError backMass
      rw [← sum_add_distrib, ← mul_assoc, mul_sum]
      apply sum_congr rfl
      intro i _
      simp only [deficit, Nat.cast_one, one_mul]
      ring
    linarith only [hsplit, hk.1, hback]
  have hcos (k : ℕ) (i : ZMod k.succ) :
      Real.cos (2 * Real.pi * (i.val : ℝ) / k.succ) = Real.cos (centeredAngle i) := by
    simpa only [Nat.cast_one, one_mul] using cos_residue_eq 1 i
  simpa only [backMass, backError, back, hcos] using And.intro hmass hbackError

end D5.S3.Fourier.Asymptotics.CyclicNegativeCosineMass
