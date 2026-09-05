/- GID: D5/S3/PrimeGaps/FragmentLaw
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:analytic-source-port)
   anchors: []
   digest: Realize the weighted Poisson fragment law, its finite mass, and its first-moment tail bound without analytic input axioms. -/

/-
Ported from openai/PrimeGaps186 at 61340d0b74163003b32756bb16e91d9209a5e330.
Source: PrimeGaps186.lean, definitions 168-232, proofs 3255-3440 and 3798-3826.
SPDX-License-Identifier: Apache-2.0
The upstream attribution notices remain applicable; see the provenance section
in RH_RESEARCH_LANE_THEORY.md. Modified on 2026-09-05: dependency-isolated port
onto the repository's pinned Mathlib, with original public names preserved.
No main-module or Challenge import and no project axiom is used.
-/

import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Tactic

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory Filter

namespace PrimeGap186

/-- Finite empirical measure with each sample weighted by its nonnegative location. -/
noncomputable def weightedEmpirical (n : ℕ) (x : Fin n → ℝ) : FiniteMeasure ℝ :=
  ∑ i : Fin n,
    let atom : FiniteMeasure ℝ := ⟨Measure.dirac (x i), inferInstance⟩
    (x i).toNNReal • atom

/-- Poisson count followed by independent normalized locations and weighted atoms. -/
noncomputable def finitePoissonLaw (μ : FiniteMeasure ℝ) : Measure (FiniteMeasure ℝ) :=
  Measure.map
    (fun p : ℕ × (ℕ → ℝ) =>
      weightedEmpirical p.1 (fun i : Fin p.1 => p.2 i.val))
    ((ProbabilityTheory.poissonMeasure μ.mass).prod
      (Measure.infinitePi (fun _ : ℕ => (μ.normalize : Measure ℝ))))

/-- The finite intensity with density 1/u in one capped dyadic band. -/
noncomputable def cappedDyadicIntensity (ζ : ℝ) (k : ℤ) : FiniteMeasure ℝ :=
  ⟨((volume.restrict (Set.Ioc (0 : ℝ) ζ)).withDensity
      (fun u : ℝ => ENNReal.ofReal (1 / u))).restrict
      (Set.Ioc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))), by
    rw [restrict_withDensity measurableSet_Ioc]
    apply isFiniteMeasure_withDensity
    apply ne_of_lt
    calc
      (∫⁻ u, ENNReal.ofReal (1 / u)
          ∂((volume.restrict (Set.Ioc (0 : ℝ) ζ)).restrict
            (Set.Ioc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))))
        ≤ ∫⁻ _u, ENNReal.ofReal (1 / (2 : ℝ) ^ k)
            ∂((volume.restrict (Set.Ioc (0 : ℝ) ζ)).restrict
              (Set.Ioc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
          exact ENNReal.ofReal_le_ofReal
            (one_div_le_one_div_of_le (zpow_pos (by norm_num) k) hu.1.le)
      _ < ∞ := by
        rw [lintegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩

/-- Sum the bands when their total mass is finite, with the upstream zero fallback. -/
noncomputable def finiteFragments (ω : ℤ → FiniteMeasure ℝ) : FiniteMeasure ℝ := by
  classical
  exact if h : IsFiniteMeasure (Measure.sum (fun k : ℤ => (ω k : Measure ℝ))) then
      ⟨Measure.sum (fun k : ℤ => (ω k : Measure ℝ)), h⟩
    else 0

/-- Probability law of the finite weighted fragment measure. -/
noncomputable def fragmentLaw (ζ : ℝ) : Measure (FiniteMeasure ℝ) :=
  Measure.map finiteFragments
    (Measure.infinitePi (fun k : ℤ => finitePoissonLaw (cappedDyadicIntensity ζ k)))

theorem coe_weightedEmpirical (n : ℕ) (x : Fin n → ℝ) :
    (weightedEmpirical n x : Measure ℝ) =
      ∑ i : Fin n, ENNReal.ofReal (x i) • Measure.dirac (x i) := by
  unfold weightedEmpirical
  rw [FiniteMeasure.toMeasure_sum]
  rfl

theorem measurable_weightedEmpirical (n : ℕ) : Measurable (weightedEmpirical n) := by
  have hm : Measurable (fun x : Fin n → ℝ => (weightedEmpirical n x : Measure ℝ)) := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [coe_weightedEmpirical, Measure.finsetSum_apply, Measure.smul_apply,
      smul_eq_mul, Measure.dirac_apply' _ hs]
    fun_prop
  exact hm.subtype_mk

theorem measurable_weightedEmpirical_sample :
    Measurable (fun p : ℕ × (ℕ → ℝ) =>
      weightedEmpirical p.1 (fun i : Fin p.1 => p.2 i.val)) := by
  refine measurable_from_prod_countable_right fun n => ?_
  exact (measurable_weightedEmpirical n).comp (by fun_prop)

theorem coe_eq_mass_smul_normalize (μ : FiniteMeasure ℝ) :
    (μ : Measure ℝ) = (μ.mass : ℝ≥0∞) • (μ.normalize : Measure ℝ) :=
  congrArg (fun ν : FiniteMeasure ℝ => (ν : Measure ℝ)) μ.self_eq_mass_smul_normalize

theorem lintegral_finitePoissonLaw_normalized
    (μ : FiniteMeasure ℝ) (F : FiniteMeasure ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ c, F c ∂(finitePoissonLaw μ) =
      ∫⁻ n, ∫⁻ x : Fin n → ℝ, F (weightedEmpirical n x)
        ∂(Measure.pi (fun _ : Fin n => (μ.normalize : Measure ℝ)))
        ∂(ProbabilityTheory.poissonMeasure μ.mass) := by
  unfold finitePoissonLaw
  rw [lintegral_map hF measurable_weightedEmpirical_sample,
    lintegral_prod (fun p : ℕ × (ℕ → ℝ) =>
      F (weightedEmpirical p.1 (fun i => p.2 i)))
      (hF.comp measurable_weightedEmpirical_sample).aemeasurable]
  apply lintegral_congr
  intro n
  rw [← Measure.infinitePi_eq_pi,
    ← Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : ℕ => (μ.normalize : Measure ℝ)) (f := fun i : Fin n => i.val)
      Fin.val_injective,
    lintegral_map (f := fun x => F (weightedEmpirical n x))
      (hF.comp (measurable_weightedEmpirical n)) (by fun_prop)]

theorem lintegral_weightedEmpirical_pi (μ : FiniteMeasure ℝ) (n : ℕ)
    (h : ℝ → ℝ≥0∞) (hh : Measurable h) :
    (∫⁻ x : Fin n → ℝ, ∫⁻ u, h u ∂(weightedEmpirical n x : Measure ℝ)
      ∂(Measure.pi (fun _ : Fin n => (μ.normalize : Measure ℝ)))) =
      (n : ℝ≥0∞) * ∫⁻ u, ENNReal.ofReal u * h u ∂(μ.normalize : Measure ℝ) := by
  simp_rw [coe_weightedEmpirical, lintegral_finsetSum_measure, lintegral_smul_measure,
    lintegral_dirac, smul_eq_mul]
  rw [lintegral_finsetSum Finset.univ (by fun_prop)]
  simpa using Finset.sum_eq_card_nsmul (s := Finset.univ) (fun i _ =>
    (measurePreserving_eval (fun _ : Fin n => (μ.normalize : Measure ℝ)) i).lintegral_comp
      (measurable_id.ennreal_ofReal.mul hh))

theorem poisson_singleton_succ (r : ℝ≥0) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ≥0∞) * ProbabilityTheory.poissonMeasure r {n + 1} =
      (r : ℝ≥0∞) * ProbabilityTheory.poissonMeasure r {n} := by
  have hreal : ((n + 1 : ℕ) : ℝ) *
      (Real.exp (-(r : ℝ)) * (r : ℝ) ^ (n + 1) / (n + 1).factorial) =
      (r : ℝ) * (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial) := by
    rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
    field_simp
  simpa only [ENNReal.ofReal_mul (by positivity : 0 ≤ ((n + 1 : ℕ) : ℝ)),
    ENNReal.ofReal_mul r.coe_nonneg, ENNReal.ofReal_natCast, ENNReal.ofReal_coe_nnreal,
    ProbabilityTheory.poissonMeasure_singleton] using congrArg ENNReal.ofReal hreal

theorem lintegral_poisson_id (r : ℝ≥0) :
    ∫⁻ n : ℕ, (n : ℝ≥0∞) ∂(ProbabilityTheory.poissonMeasure r) = (r : ℝ≥0∞) := by
  have hsum : ∑' n : ℕ, ProbabilityTheory.poissonMeasure r {n} = 1 := by
    simpa using (lintegral_countable' (μ := ProbabilityTheory.poissonMeasure r)
      (fun _ : ℕ => (1 : ℝ≥0∞))).symm
  rw [lintegral_countable', tsum_eq_zero_add' ENNReal.summable]
  simp only [Nat.cast_zero, zero_mul, zero_add, poisson_singleton_succ]
  rw [ENNReal.tsum_mul_left, hsum, mul_one]

theorem lintegral_weighted_finitePoissonLaw
    (μ : FiniteMeasure ℝ) (h : ℝ → ℝ≥0∞) (hh : Measurable h) :
    (∫⁻ c, ∫⁻ u, h u ∂(c : Measure ℝ) ∂(finitePoissonLaw μ)) =
      ∫⁻ u, ENNReal.ofReal u * h u ∂(μ : Measure ℝ) := by
  rw [lintegral_finitePoissonLaw_normalized μ
    (fun c => ∫⁻ u, h u ∂(c : Measure ℝ))
    ((Measure.measurable_lintegral hh).comp measurable_subtype_coe)]
  simp_rw [lintegral_weightedEmpirical_pi μ _ h hh]
  rw [lintegral_mul_const _ (by fun_prop), lintegral_poisson_id,
    coe_eq_mass_smul_normalize μ, lintegral_smul_measure, smul_eq_mul]

theorem finitePoissonLaw_isProbabilityMeasure (μ : FiniteMeasure ℝ) :
    IsProbabilityMeasure (finitePoissonLaw μ) := by
  unfold finitePoissonLaw
  infer_instance

theorem measurable_fragment_sum :
    Measurable (fun ω : ℤ → FiniteMeasure ℝ =>
      Measure.sum (fun k : ℤ => (ω k : Measure ℝ))) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [Measure.sum_apply _ hs]
  exact Measurable.tsum fun k => (Measure.measurable_coe hs).comp
    (measurable_subtype_coe.comp (measurable_pi_apply k))

theorem measurable_finiteFragments : Measurable finiteFragments := by
  classical
  have hg : Measurable (fun ω : {ω : ℤ → FiniteMeasure ℝ |
      IsFiniteMeasure (Measure.sum (fun k : ℤ => (ω k : Measure ℝ)))} =>
      (⟨Measure.sum (fun k : ℤ => (ω.val k : Measure ℝ)), ω.property⟩ : FiniteMeasure ℝ)) :=
    (measurable_fragment_sum.comp measurable_subtype_coe).subtype_mk
  unfold finiteFragments
  exact hg.dite (g := fun _ => (0 : FiniteMeasure ℝ)) measurable_const
    (FiniteMeasure.measurableSet_isFiniteMeasure.preimage measurable_fragment_sum)

theorem dyadic_bands_disjoint :
    Pairwise (fun i j : ℤ => Disjoint
      (Set.Ioc ((2 : ℝ) ^ i) ((2 : ℝ) ^ (i + 1)))
      (Set.Ioc ((2 : ℝ) ^ j) ((2 : ℝ) ^ (j + 1)))) :=
  (zpow_right_mono₀ (by norm_num : (1 : ℝ) ≤ 2)).pairwise_disjoint_on_Ioc_succ

theorem iUnion_dyadic_bands :
    (⋃ k : ℤ, Set.Ioc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1))) = Set.Ioi 0 := by
  ext u
  simp only [Set.mem_iUnion, Set.mem_Ioi]
  constructor
  · rintro ⟨k, hk⟩
    exact (zpow_pos (by norm_num) k).trans hk.1
  · exact fun hu => exists_mem_Ioc_zpow hu (by norm_num : (1 : ℝ) < 2)

theorem sum_cappedDyadicIntensity (ζ : ℝ) :
    Measure.sum (fun k : ℤ => (cappedDyadicIntensity ζ k : Measure ℝ)) =
      (volume.restrict (Set.Ioc (0 : ℝ) ζ)).withDensity
        (fun u : ℝ => ENNReal.ofReal (1 / u)) := by
  change Measure.sum (fun k : ℤ =>
    ((volume.restrict (Set.Ioc (0 : ℝ) ζ)).withDensity
      (fun u : ℝ => ENNReal.ofReal (1 / u))).restrict
      (Set.Ioc ((2 : ℝ) ^ k) ((2 : ℝ) ^ (k + 1)))) = _
  rw [← Measure.restrict_iUnion dyadic_bands_disjoint (fun _ => measurableSet_Ioc),
    iUnion_dyadic_bands, restrict_withDensity measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi,
    Set.inter_eq_right.mpr (fun _ hu => hu.1)]

theorem lintegral_fragment_sum (ζ : ℝ) (h : ℝ → ℝ≥0∞) (hh : Measurable h) :
    (∫⁻ ω, ∫⁻ u, h u ∂(Measure.sum (fun k : ℤ => (ω k : Measure ℝ)))
      ∂(Measure.infinitePi (fun k : ℤ =>
        finitePoissonLaw (cappedDyadicIntensity ζ k)))) =
      ∫⁻ u in Set.Ioc (0 : ℝ) ζ, h u ∂volume := by
  let : ∀ k : ℤ, IsProbabilityMeasure (finitePoissonLaw (cappedDyadicIntensity ζ k)) :=
    fun k => finitePoissonLaw_isProbabilityMeasure _
  have hm : Measurable (fun c : FiniteMeasure ℝ => ∫⁻ u, h u ∂(c : Measure ℝ)) :=
    (Measure.measurable_lintegral hh).comp measurable_subtype_coe
  simp_rw [lintegral_sum_measure]
  rw [lintegral_tsum (f := fun k : ℤ => fun ω : ℤ → FiniteMeasure ℝ =>
    ∫⁻ u, h u ∂(ω k : Measure ℝ))
    (fun k => (hm.comp (measurable_pi_apply k)).aemeasurable)]
  have he (k : ℤ) := (measurePreserving_eval_infinitePi
      (fun j : ℤ => finitePoissonLaw (cappedDyadicIntensity ζ j)) k).lintegral_comp hm
  simp_rw [he, lintegral_weighted_finitePoissonLaw _ h hh]
  rw [← lintegral_sum_measure, sum_cappedDyadicIntensity,
    lintegral_withDensity_eq_lintegral_mul _
      (f := fun u : ℝ => ENNReal.ofReal (1 / u))
      (g := fun u : ℝ => ENNReal.ofReal u * h u) (by fun_prop) (by fun_prop)]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  have hu0 : 0 < u := hu.1
  change ENNReal.ofReal (1 / u) * (ENNReal.ofReal u * h u) = h u
  rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt (one_div_pos.mpr hu0)),
    one_div_mul_cancel hu0.ne', ENNReal.ofReal_one, one_mul]

theorem ae_isFiniteMeasure_fragment_sum (ζ : ℝ) :
    ∀ᵐ ω ∂(Measure.infinitePi (fun k : ℤ =>
      finitePoissonLaw (cappedDyadicIntensity ζ k))),
      IsFiniteMeasure (Measure.sum (fun k : ℤ => (ω k : Measure ℝ))) := by
  have hm : Measurable (fun ω : ℤ → FiniteMeasure ℝ =>
      (Measure.sum (fun k : ℤ => (ω k : Measure ℝ))) Set.univ) :=
    (Measure.measurable_coe MeasurableSet.univ).comp measurable_fragment_sum
  have he := lintegral_fragment_sum ζ (fun _ => 1) measurable_const
  simp only [lintegral_one, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero] at he
  filter_upwards [ae_lt_top hm (by rw [he]; exact ENNReal.ofReal_ne_top)] with ω hω
  exact ⟨hω⟩

theorem fragmentLaw_isProbabilityMeasure (ζ : ℝ) : IsProbabilityMeasure (fragmentLaw ζ) := by
  let : ∀ k : ℤ, IsProbabilityMeasure (finitePoissonLaw (cappedDyadicIntensity ζ k)) :=
    fun k => finitePoissonLaw_isProbabilityMeasure _
  unfold fragmentLaw
  infer_instance

theorem lintegral_fragmentLaw (ζ : ℝ) (h : ℝ → ℝ≥0∞) (hh : Measurable h) :
    (∫⁻ c, ∫⁻ u, h u ∂(c : Measure ℝ) ∂(fragmentLaw ζ)) =
      ∫⁻ u in Set.Ioc (0 : ℝ) ζ, h u ∂volume := by
  have hm : Measurable (fun c : FiniteMeasure ℝ => ∫⁻ u, h u ∂(c : Measure ℝ)) :=
    (Measure.measurable_lintegral hh).comp measurable_subtype_coe
  rw [fragmentLaw, lintegral_map hm measurable_finiteFragments, ← lintegral_fragment_sum ζ h hh]
  apply lintegral_congr_ae
  filter_upwards [ae_isFiniteMeasure_fragment_sum ζ] with ω hω
  simp [finiteFragments, hω]

theorem fragmentLaw_small_seed_tail
    (ζ ε δ : ℝ) (hζ : 0 < ζ) (hε : 0 ≤ ε) (hδ : 0 < δ) :
    fragmentLaw ζ {c : FiniteMeasure ℝ |
      ENNReal.ofReal δ ≤ (c : Measure ℝ) (Set.Ioc (0 : ℝ) ε)} ≤
      ENNReal.ofReal (min ε ζ) / ENNReal.ofReal δ := by
  have hmin : 0 ≤ min ε ζ := le_min hε hζ.le
  have hm : Measurable (fun c : FiniteMeasure ℝ => (c : Measure ℝ) (Set.Ioc (0 : ℝ) ε)) :=
    (Measure.measurable_coe measurableSet_Ioc).comp measurable_subtype_coe
  have he : (∫⁻ c, (c : Measure ℝ) (Set.Ioc (0 : ℝ) ε) ∂(fragmentLaw ζ)) =
      (NNReal.mk (min ε ζ) hmin : ℝ≥0∞) := by
    have hi := lintegral_fragmentLaw ζ ((Set.Ioc (0 : ℝ) ε).indicator (fun _ => 1))
      (measurable_const.indicator measurableSet_Ioc)
    simpa only [lintegral_indicator_fun_one measurableSet_Ioc,
      Measure.restrict_apply measurableSet_Ioc, Set.Ioc_inter_Ioc, max_self,
      Real.volume_Ioc, sub_zero, ENNReal.ofReal_eq_coe_nnreal hmin] using hi
  simpa only [he, ENNReal.ofReal_eq_coe_nnreal hmin] using
    (meas_ge_le_lintegral_div (μ := fragmentLaw ζ) hm.aemeasurable
      (ne_of_gt (ENNReal.ofReal_pos.mpr hδ)) ENNReal.ofReal_ne_top)

#print axioms ae_isFiniteMeasure_fragment_sum
#print axioms measurable_finiteFragments
#print axioms fragmentLaw_isProbabilityMeasure
#print axioms lintegral_fragmentLaw
#print axioms fragmentLaw_small_seed_tail

end PrimeGap186
