/- GID: D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicCommonSequence
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicCommonSequence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One sequence of matched faithful pairs works for every positive geodesic parameter. -/

import D5.S3.Quantum.Information.GeodesicCMI.CapelCostaRicoForwardGeodesicCMI

/-! For #32416 we regularize uniformly over compact subintervals of the open
interpolation interval, and also enforce the error bound at the separate endpoint
`t = 1`. The chosen sequence then works for both deficits at every `0 < t ≤ 1`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.GeodesicCMI.CapelCostaRicoForwardGeodesicCMI

open Matrix Filter Set
open scoped BigOperators ComplexOrder Kronecker Matrix MatrixOrder Matrix.Norms.L2Operator Topology
open CapelCostaRicoForwardGeodesicDensity (Triple RMatrix SMatrix)
open CapelCostaRicoForwardGeodesicBoundary (geodesicRelativeEntropy_RMatrix_zero)
open CapelCostaRicoReverseGeodesicCMI
  (geodesicRelativeEntropy geodesicModular geodesicModular_eq_kronecker
    geodesicModular_posSemidef weightedVector)

noncomputable section

private theorem continuousOn_rpow_uniformOn {K : Set ℝ} (hK : IsCompact K) :
    ContinuousOn (fun p : ℝ => UniformOnFun.ofFun {K} (fun x : ℝ => x ^ p)) (Ioi 0) := by
  intro p hp
  rw [ContinuousWithinAt, UniformOnFun.tendsto_iff_tendstoUniformlyOn]
  intro s hs
  have hsK : s = K := mem_singleton_iff.mp hs
  subst s
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  let g : ℝ × ℝ → ℝ := fun z => dist (z.1 ^ p) (z.1 ^ z.2)
  have hpow : ContinuousOn (fun z : ℝ × ℝ => z.1 ^ z.2) (univ ×ˢ Ioi 0) :=
    fun z hz => (Real.continuousAt_rpow_of_pos z hz.2).continuousWithinAt
  have hconst : ContinuousOn (fun z : ℝ × ℝ => z.1 ^ p) (univ ×ˢ Ioi 0) :=
    ((Real.continuous_rpow_const (mem_Ioi.mp hp).le).comp continuous_fst).continuousOn
  have hg : ContinuousOn g (univ ×ˢ Ioi 0) :=
    (continuous_dist.continuousOn (s := (univ : Set (ℝ × ℝ)))).comp'
      (hconst.prodMk hpow) (fun _ _ => mem_univ _)
  have hopen : IsOpen ((univ ×ˢ Ioi (0 : ℝ)) ∩ g ⁻¹' Iio ε) :=
    hg.isOpen_inter_preimage (isOpen_univ.prod isOpen_Ioi) isOpen_Iio
  have hsubset : K ×ˢ {p} ⊆ (univ ×ˢ Ioi (0 : ℝ)) ∩ g ⁻¹' Iio ε := by
    rintro ⟨x, q⟩ ⟨_, hq⟩
    have hqp : q = p := mem_singleton_iff.mp hq
    subst q
    exact ⟨⟨mem_univ _, hp⟩, by simpa [g] using hε⟩
  obtain ⟨U, V, _, hV, hKU, hpV, hUV⟩ :=
    generalized_tube_lemma hK isCompact_singleton hopen hsubset
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hV.mem_nhds (hpV (mem_singleton p)))]
    with q hq
  intro x hx
  exact (hUV (show (x, q) ∈ U ×ˢ V from ⟨hKU hx, hq⟩)).2

private theorem continuousOn_geodesicRelativeEntropy_regularization {u : ℝ}
    (hu : 0 < u) (hhalf : u < 1 / 2) :
    ContinuousOn (fun x : ℝ × ℝ => geodesicRelativeEntropy x.1 (RMatrix u x.2) (SMatrix u))
      (Ioo (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := by
  let domain : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).bddAbove_image
    (continuous_norm.comp (continuous_RMatrix u)).continuousOn
  let K : Set ℝ := Icc 0 M
  have hspectrum (η : ℝ) (hη : η ∈ Icc (0 : ℝ) 1) : spectrum ℝ (RMatrix u η) ⊆ K := by
    have hnorm : ‖RMatrix u η‖ ≤ M := hM (mem_image_of_mem _ hη)
    intro z hz
    refine ⟨spectrum_nonneg_of_nonneg (RMatrix_posSemidef_of_mem_Icc hu hhalf hη).nonneg hz, ?_⟩
    exact (le_abs_self z).trans (by
      simpa only [Real.norm_eq_abs] using (spectrum.norm_le_norm_of_mem hz).trans hnorm)
  have hpow (p : ℝ × ℝ → ℝ) (hp : Continuous p)
      (hpp : ∀ x ∈ domain, 0 < p x) :
      ContinuousOn (fun x => cfc (fun z : ℝ => z ^ p x) (RMatrix u x.2)) domain := by
    have hscalar : ContinuousOn (fun x => UniformOnFun.ofFun {K} (fun z : ℝ => z ^ p x)) domain :=
      (continuousOn_rpow_uniformOn (K := K) isCompact_Icc).comp' hp.continuousOn hpp
    have hmat : ContinuousOn (fun x : ℝ × ℝ => RMatrix u x.2) domain :=
      ((continuous_RMatrix u).comp continuous_snd).continuousOn
    refine (continuousOn_cfc_setProd (A := Matrix Triple Triple ℂ) (p := IsSelfAdjoint)
      (s := K) isCompact_Icc).comp' (hscalar.prodMk hmat) ?_
    intro x hx
    exact ⟨(Real.continuous_rpow_const (hpp x hx).le).continuousOn,
      (RMatrix_posSemidef_of_mem_Icc hu hhalf hx.2).isHermitian.isSelfAdjoint,
      hspectrum x.2 hx.2⟩
  have hleft :=
    hpow (fun x => 1 - x.1) (continuous_const.sub continuous_fst)
      (fun x hx => sub_pos.mpr hx.1.2)
  let q : Matrix Triple Triple ℂ := cfc (fun z : ℝ => (Real.sqrt z)⁻¹) (SMatrix u)
  have hright : ContinuousOn (fun x : ℝ × ℝ => q * cfc (fun z : ℝ => z ^ x.1) (RMatrix u x.2) * q)
      domain :=
    ((continuousOn_const (c := q)).mul
      (hpow Prod.fst continuous_fst (fun x hx => hx.1.1))).mul (continuousOn_const (c := q))
  have hmod : ContinuousOn (fun x : ℝ × ℝ => geodesicModular x.1 (RMatrix u x.2) (SMatrix u))
      domain := by
    rw [continuousOn_iff_continuous_domRestrict] at hleft hright ⊢
    refine continuous_matrix fun ⟨i₁, i₂⟩ ⟨j₁, j₂⟩ => ?_
    simp only [domRestrict_apply, geodesicModular_eq_kronecker, Matrix.kronecker_apply,
      Matrix.transpose_apply]
    exact (hleft.matrix_elem i₁ j₁).mul (hright.matrix_elem j₂ i₂)
  have hlog : ContinuousOn (fun x : ℝ × ℝ => cfc (fun z : ℝ => z * Real.log z)
      (geodesicModular x.1 (RMatrix u x.2) (SMatrix u))) domain :=
    hmod.cfc_of_mem_nhdsSet (s := (univ : Set ℝ)) (fun z : ℝ => z * Real.log z) Filter.univ_mem
      (fun x hx => (geodesicModular_posSemidef x.1
        (RMatrix_posSemidef_of_mem_Icc hu hhalf hx.2) (SMatrix u)).isHermitian.isSelfAdjoint)
      Real.continuous_mul_log.continuousOn
  change ContinuousOn _ domain
  unfold geodesicRelativeEntropy
  rw [continuousOn_iff_continuous_domRestrict] at hlog ⊢
  exact Complex.continuous_re.comp <|
    (continuous_const (y := star (weightedVector (SMatrix u)))).dotProduct
      (hlog.matrix_mulVec (continuous_const (y := weightedVector (SMatrix u))))

/-- At fixed `u`, every compact subset of the open geodesic parameter interval
has one regularization neighborhood that works for every `t` in that subset. -/
theorem eventually_uniform_regularization {u ε : ℝ}
    (hu : 0 < u) (hhalf : u < 1 / 2) (hε : 0 < ε)
    {K : Set ℝ} (hK : IsCompact K) (hKinside : K ⊆ Ioo (0 : ℝ) 1) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ t ∈ K,
      dist (geodesicRelativeEntropy t (RMatrix u η) (SMatrix u)) (Real.log 2) < ε := by
  let domain : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  let f : ℝ × ℝ → ℝ := fun x =>
    dist (geodesicRelativeEntropy x.1 (RMatrix u x.2) (SMatrix u)) (Real.log 2)
  have hf : ContinuousOn f domain :=
    (continuous_dist.continuousOn (s := (univ : Set (ℝ × ℝ)))).comp'
      ((continuousOn_geodesicRelativeEntropy_regularization hu hhalf).prodMk
        (continuousOn_const (c := Real.log 2))) (fun _ _ => mem_univ _)
  obtain ⟨W, hW, heq⟩ :=
    continuousOn_iff'.mp hf (Iio ε) isOpen_Iio
  have hKW : K ×ˢ {(0 : ℝ)} ⊆ W := by
    rintro ⟨t, η⟩ ⟨ht, hη⟩
    have hη₀ : η = 0 := mem_singleton_iff.mp hη
    subst η
    have ht' := hKinside ht
    have hd : (t, (0 : ℝ)) ∈ domain := ⟨ht', by norm_num⟩
    have hf₀ : (t, (0 : ℝ)) ∈ f ⁻¹' Iio ε := by
      change dist (geodesicRelativeEntropy t (RMatrix u 0) (SMatrix u)) (Real.log 2) < ε
      rwa [geodesicRelativeEntropy_RMatrix_zero hu hhalf ht'.1 ht'.2.le, dist_self]
    have hw : (t, (0 : ℝ)) ∈ W ∩ domain := by
      rw [← heq]
      exact ⟨hf₀, hd⟩
    exact hw.1
  obtain ⟨U, V, _, hV, hKU, h0V, hUV⟩ :=
    generalized_tube_lemma hK isCompact_singleton hW hKW
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hV.mem_nhds (h0V (mem_singleton 0))),
    eventually_regularization_valid] with η hηV hη
  intro t ht
  have htd : (t, η) ∈ domain := ⟨hKinside ht, ⟨hη.1.le, hη.2.le⟩⟩
  have hw : (t, η) ∈ W ∩ domain :=
    ⟨hUV (show (t, η) ∈ U ×ˢ V from ⟨hKU ht, hηV⟩), htd⟩
  rw [← heq] at hw
  exact hw.1

private def parameterInterval (n : ℕ) : Set ℝ :=
  Icc (sequenceParameter n) (1 - sequenceParameter n)

private theorem parameterInterval_subset (n : ℕ) : parameterInterval n ⊆ Ioo (0 : ℝ) 1 := by
  intro t ht
  exact ⟨(sequenceParameter_pos n).trans_le ht.1,
    ht.2.trans_lt (sub_lt_self _ (sequenceParameter_pos n))⟩

private theorem eventually_mem_parameterInterval {t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1) :
    ∀ᶠ n in atTop, t ∈ parameterInterval n := by
  have hmin : 0 < min t (1 - t) := lt_min ht₀ (sub_pos.mpr ht₁)
  filter_upwards [tendsto_sequenceParameter.eventually (Iio_mem_nhds hmin)] with n hn
  change sequenceParameter n < min t (1 - t) at hn
  exact ⟨(hn.trans_le (min_le_left _ _)).le, by linarith [hn.trans_le (min_le_right t (1 - t))]⟩

/-- One sequence of faithful pairs meets all the marginal and distance conditions
and has both forward CMI gaps converge to `log 2` for every `0 < t ≤ 1`. -/
theorem result :
    ∃ p : MatchedFaithfulPairs, ∀ t : ℝ, 0 < t → t ≤ 1 → ForwardGap p t := by
  have h (n : ℕ) : ∃ η : ℝ, 0 < η ∧ η < 1 ∧
      (∀ t ∈ parameterInterval n, dist
        (geodesicRelativeEntropy t (RMatrix (sequenceParameter n) η) (SMatrix (sequenceParameter n)))
        (Real.log 2) < sequenceParameter n) ∧
      dist (geodesicRelativeEntropy 1 (RMatrix (sequenceParameter n) η)
        (SMatrix (sequenceParameter n))) (Real.log 2) < sequenceParameter n := by
    have hcompact := eventually_uniform_regularization
      (sequenceParameter_pos n) (sequenceParameter_lt_half n) (sequenceParameter_pos n)
      (K := parameterInterval n) (show IsCompact (parameterInterval n) from isCompact_Icc)
      (parameterInterval_subset n)
    have hend := (Metric.tendsto_nhds.mp
      (regularization_tendsto 1 (sequenceParameter n) (by norm_num) le_rfl
        (sequenceParameter_pos n) (sequenceParameter_lt_half n)))
      (sequenceParameter n) (sequenceParameter_pos n)
    obtain ⟨η, hvalid, hclose, hendpoint⟩ :=
      (eventually_regularization_valid.and (hcompact.and hend)).exists
    exact ⟨η, hvalid.1, hvalid.2, hclose, hendpoint⟩
  choose η hη₀ hη₁ hcompact hend using h
  refine ⟨witnessPairs η hη₀ hη₁, ?_⟩
  intro t ht₀ ht₁
  apply witnessPairs_forwardGap
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsmall : ∀ᶠ n in atTop, sequenceParameter n < ε :=
    tendsto_sequenceParameter.eventually (Iio_mem_nhds hε)
  rcases lt_or_eq_of_le ht₁ with ht | rfl
  · filter_upwards [hsmall, eventually_mem_parameterInterval ht₀ ht] with n hn htn
    exact (hcompact n t htn).trans hn
  · exact hsmall.mono fun n hn => (hend n).trans hn

end

end D5.S3.Quantum.Information.GeodesicCMI.CapelCostaRicoForwardGeodesicCMI
