/- GID: D5/S3/PrimeGaps/FragmentOriginalMesh
   generality: G
   mirror-B: D5/B/S3/PrimeGaps/FragmentOriginalMesh
   mirror-E: none(waiver:probability-error-bound)
   anchors: []
   utility: none
   digest: Localize actual fragment mesh crossings to finitely many original-mass intervals and expose the remaining perpetuity identity. -/

import D5.S3.PrimeGaps.FragmentMeshTruncation
import D5.S3.PrimeGaps.FragmentUniformSmoothing

/-!
# Original-side fragment mesh bounds

The deterministic witness places the ORIGINAL total mass in a short interval
above a positive mesh boundary. The retained mass may have an atom at zero;
no density assertion is made about it.

The event reduction and total-mass Markov bound use the actual `fragmentLaw`
unconditionally. The final two numerical bounds additionally require the
explicit scalar perpetuity equality. This source does not prove that equality,
and does not treat it as an axiom or silently remove it from the conclusions.

All definitions of the fragment law, deletion and retained measure are imported
from their existing owners. No replacement probability model is introduced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace PrimeGap186

private theorem measurable_fragment_mass_real :
    Measurable (fun c : FiniteMeasure ℝ => (c.mass : ℝ)) := by
  have hm : Measurable (fun c : FiniteMeasure ℝ =>
      (c : Measure ℝ) Set.univ) :=
    (Measure.measurable_coe MeasurableSet.univ).comp measurable_subtype_coe
  simpa only [← FiniteMeasure.ennreal_mass, ENNReal.coe_toReal] using
    hm.ennreal_toReal

/-- A small nonnegative deletion changing a floor index puts the original
mass just above a positive boundary. The witness is bounded by the window. -/
theorem original_mesh_boundary_witness
    (x d h delta R : ℝ) (hx : 0 ≤ x) (hd : 0 ≤ d) (hh : 0 < h)
    (hsmall : d < delta) (hwindow : x + d ≤ R)
    (hcross : ⌊(x + d) / h⌋₊ ≠ ⌊x / h⌋₊) :
    ∃ k : ℕ, k ∈ Finset.Icc 1 ⌊R / h⌋₊ ∧
      x + d ∈ Set.Ico ((k : ℝ) * h) ((k : ℝ) * h + delta) := by
  let k : ℕ := ⌊x / h⌋₊ + 1
  have hmono : ⌊x / h⌋₊ ≤ ⌊(x + d) / h⌋₊ :=
    Nat.floor_mono (div_le_div_of_nonneg_right (by linarith) hh.le)
  have hk : k ≤ ⌊(x + d) / h⌋₊ := by
    dsimp [k]
    omega
  have hkR : k ≤ ⌊R / h⌋₊ := hk.trans
    (Nat.floor_mono (div_le_div_of_nonneg_right hwindow hh.le))
  have hcast : (k : ℝ) ≤ (⌊(x + d) / h⌋₊ : ℝ) := by exact_mod_cast hk
  have hlower : (k : ℝ) * h ≤ x + d :=
    (le_div_iff₀ hh).mp
      (hcast.trans (Nat.floor_le (div_nonneg (add_nonneg hx hd) hh.le)))
  have hxlt : x < (k : ℝ) * h := by
    apply (div_lt_iff₀ hh).mp
    simpa [k] using (Nat.lt_floor_add_one (x / h))
  refine ⟨k, Finset.mem_Icc.mpr ⟨?_, hkR⟩, hlower, ?_⟩
  · dsimp [k]
    omega
  · linarith

/-- An unconditional reduction for the actual fragment law. Unlike the older
retained-side bound, the boundary events here concern the original mass and
there are exactly `floor(R/h)` possible positive boundaries. -/
theorem fragment_mesh_original_boundary_probability
    (zeta epsilon delta h R : ℝ)
    (hzeta : 0 < zeta) (hepsilon : 0 ≤ epsilon)
    (hdelta : 0 < delta) (hh : 0 < h) :
    fragmentLaw zeta {c : FiniteMeasure ℝ |
      ⌊(c.mass : ℝ) / h⌋₊ ≠
        ⌊((retainedFragments epsilon c).mass : ℝ) / h⌋₊ ∧ (c.mass : ℝ) ≤ R} ≤
      ENNReal.ofReal (min epsilon zeta) / ENNReal.ofReal delta +
        ∑ k ∈ Finset.Icc 1 ⌊R / h⌋₊,
          fragmentLaw zeta {c : FiniteMeasure ℝ |
            (c.mass : ℝ) ∈ Set.Ico ((k : ℝ) * h) ((k : ℝ) * h + delta)} := by
  let strip : ℕ → Set (FiniteMeasure ℝ) := fun k =>
    {c | (c.mass : ℝ) ∈ Set.Ico ((k : ℝ) * h) ((k : ℝ) * h + delta)}
  have hsub : {c : FiniteMeasure ℝ |
      ⌊(c.mass : ℝ) / h⌋₊ ≠
        ⌊((retainedFragments epsilon c).mass : ℝ) / h⌋₊ ∧ (c.mass : ℝ) ≤ R} ⊆
      {c : FiniteMeasure ℝ | delta ≤ deletedFragmentMass epsilon c} ∪
        ⋃ k ∈ Finset.Icc 1 ⌊R / h⌋₊, strip k := by
    intro c hc
    by_cases hlarge : delta ≤ deletedFragmentMass epsilon c
    · exact Or.inl hlarge
    · right
      have hw : ((retainedFragments epsilon c).mass : ℝ) +
          deletedFragmentMass epsilon c ≤ R := by
        rw [retained_deleted_mass]
        exact hc.2
      have hx :
          ⌊(((retainedFragments epsilon c).mass : ℝ) +
            deletedFragmentMass epsilon c) / h⌋₊ ≠
          ⌊((retainedFragments epsilon c).mass : ℝ) / h⌋₊ := by
        rw [retained_deleted_mass]
        exact hc.1
      obtain ⟨k, hk, hs⟩ := original_mesh_boundary_witness
        ((retainedFragments epsilon c).mass : ℝ) (deletedFragmentMass epsilon c)
        h delta R (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) hh
        (lt_of_not_ge hlarge) hw hx
      rw [retained_deleted_mass] at hs
      exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hk, hs⟩⟩
  calc
    _ ≤ fragmentLaw zeta
        ({c : FiniteMeasure ℝ | delta ≤ deletedFragmentMass epsilon c} ∪
          ⋃ k ∈ Finset.Icc 1 ⌊R / h⌋₊, strip k) := measure_mono hsub
    _ ≤ fragmentLaw zeta {c | delta ≤ deletedFragmentMass epsilon c} +
        fragmentLaw zeta (⋃ k ∈ Finset.Icc 1 ⌊R / h⌋₊, strip k) := measure_union_le _ _
    _ ≤ _ := add_le_add
      (deletedFragmentMass_tail zeta epsilon delta hzeta hepsilon hdelta)
      (measure_biUnion_finset_le (Finset.Icc 1 ⌊R / h⌋₊) strip)

/-- The uniform-smoothing theorem applies to the actual scalar mass
pushforward once its perpetuity identity has been independently proved. -/
theorem fragment_mass_interval_of_perpetuity
    (zeta x delta : ℝ) (hzeta : 0 < zeta)
    (hperpetuity :
      Measure.map (fun c : FiniteMeasure ℝ => (c.mass : ℝ)) (fragmentLaw zeta) =
        uniformScaleMixture zeta
          (Measure.map (fun c : FiniteMeasure ℝ => (c.mass : ℝ)) (fragmentLaw zeta))) :
    fragmentLaw zeta {c : FiniteMeasure ℝ |
      (c.mass : ℝ) ∈ Set.Ico x (x + delta)} ≤ ENNReal.ofReal (delta / zeta) := by
  let nu := Measure.map (fun c : FiniteMeasure ℝ => (c.mass : ℝ)) (fragmentLaw zeta)
  letI : IsProbabilityMeasure (fragmentLaw zeta) := fragmentLaw_isProbabilityMeasure zeta
  letI : IsProbabilityMeasure nu :=
    Measure.isProbabilityMeasure_map measurable_fragment_mass_real.aemeasurable
  have hnonnegative : ∀ᵐ s ∂nu, 0 ≤ s := by
    rw [ae_iff]
    change nu {s : ℝ | ¬ 0 ≤ s} = 0
    rw [show nu = Measure.map (fun c : FiniteMeasure ℝ => (c.mass : ℝ))
      (fragmentLaw zeta) from rfl,
      Measure.map_apply measurable_fragment_mass_real
        (show MeasurableSet {s : ℝ | ¬ 0 ≤ s} from
          (measurableSet_le measurable_const measurable_id).compl)]
    have hempty : (fun c : FiniteMeasure ℝ => (c.mass : ℝ)) ⁻¹'
        {s : ℝ | ¬ 0 ≤ s} = ∅ := by
      ext c
      simp [NNReal.coe_nonneg]
    rw [hempty, measure_empty]
  have hb := uniform_scale_fixedPoint_Ico_le zeta nu hzeta hnonnegative hperpetuity x delta
  change (Measure.map (fun c : FiniteMeasure ℝ => (c.mass : ℝ)) (fragmentLaw zeta))
    (Set.Ico x (x + delta)) ≤ _ at hb
  rw [Measure.map_apply measurable_fragment_mass_real measurableSet_Ico] at hb
  exact hb

/-- Explicit finite-window bound. The sole additional distributional premise
is the displayed perpetuity equality for the existing scalar mass law. -/
theorem fragment_mesh_window_of_perpetuity
    (zeta epsilon delta h R : ℝ)
    (hzeta : 0 < zeta) (hepsilon : 0 ≤ epsilon)
    (hdelta : 0 < delta) (hh : 0 < h)
    (hperpetuity :
      Measure.map (fun c : FiniteMeasure ℝ => (c.mass : ℝ)) (fragmentLaw zeta) =
        uniformScaleMixture zeta
          (Measure.map (fun c : FiniteMeasure ℝ => (c.mass : ℝ)) (fragmentLaw zeta))) :
    fragmentLaw zeta {c : FiniteMeasure ℝ |
      ⌊(c.mass : ℝ) / h⌋₊ ≠
        ⌊((retainedFragments epsilon c).mass : ℝ) / h⌋₊ ∧ (c.mass : ℝ) ≤ R} ≤
      ENNReal.ofReal (min epsilon zeta) / ENNReal.ofReal delta +
        (⌊R / h⌋₊ : ℝ≥0∞) * ENNReal.ofReal (delta / zeta) := by
  refine (fragment_mesh_original_boundary_probability zeta epsilon delta h R
    hzeta hepsilon hdelta hh).trans ?_
  apply add_le_add_right
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 ⌊R / h⌋₊, ENNReal.ofReal (delta / zeta) := by
      apply Finset.sum_le_sum
      intro k hk
      exact fragment_mass_interval_of_perpetuity zeta ((k : ℝ) * h) delta
        hzeta hperpetuity
    _ = _ := by simp [nsmul_eq_mul]

/-- The original mass has the already established first moment zeta. This
Markov bound requires no perpetuity or anti-concentration premise. -/
theorem fragment_total_mass_tail
    (zeta R : ℝ) (hzeta : 0 < zeta) (hR : 0 < R) :
    fragmentLaw zeta {c : FiniteMeasure ℝ | R ≤ (c.mass : ℝ)} ≤
      ENNReal.ofReal zeta / ENNReal.ofReal R := by
  have hm : Measurable (fun c : FiniteMeasure ℝ => (c : Measure ℝ) Set.univ) :=
    (Measure.measurable_coe MeasurableSet.univ).comp measurable_subtype_coe
  have hmean : (∫⁻ c, (c : Measure ℝ) Set.univ ∂fragmentLaw zeta) =
      ENNReal.ofReal zeta := by
    simpa only [lintegral_const, one_mul, Measure.restrict_apply_univ,
      Real.volume_Ioc, sub_zero] using
      lintegral_fragmentLaw zeta (fun _ => (1 : ℝ≥0∞)) measurable_const
  have hsets : {c : FiniteMeasure ℝ | R ≤ (c.mass : ℝ)} =
      {c : FiniteMeasure ℝ | ENNReal.ofReal R ≤ (c : Measure ℝ) Set.univ} := by
    ext c
    change R ≤ (c.mass : ℝ) ↔ ENNReal.ofReal R ≤ (c : Measure ℝ) Set.univ
    rw [← FiniteMeasure.ennreal_mass]
    exact ENNReal.ofReal_le_coe.symm
  rw [hsets]
  simpa only [hmean] using
    (meas_ge_le_lintegral_div (μ := fragmentLaw zeta) hm.aemeasurable
      (ne_of_gt (ENNReal.ofReal_pos.mpr hR)) ENNReal.ofReal_ne_top)

/-- A full-probability error estimate adds the unconditional total-mass tail
to the finite-window estimate. The distributional premise remains explicit. -/
theorem fragment_mesh_global_of_perpetuity
    (zeta epsilon delta h R : ℝ)
    (hzeta : 0 < zeta) (hepsilon : 0 ≤ epsilon)
    (hdelta : 0 < delta) (hh : 0 < h) (hR : 0 < R)
    (hperpetuity :
      Measure.map (fun c : FiniteMeasure ℝ => (c.mass : ℝ)) (fragmentLaw zeta) =
        uniformScaleMixture zeta
          (Measure.map (fun c : FiniteMeasure ℝ => (c.mass : ℝ)) (fragmentLaw zeta))) :
    fragmentLaw zeta {c : FiniteMeasure ℝ |
      ⌊(c.mass : ℝ) / h⌋₊ ≠
        ⌊((retainedFragments epsilon c).mass : ℝ) / h⌋₊} ≤
      ENNReal.ofReal zeta / ENNReal.ofReal R +
        (ENNReal.ofReal (min epsilon zeta) / ENNReal.ofReal delta +
          (⌊R / h⌋₊ : ℝ≥0∞) * ENNReal.ofReal (delta / zeta)) := by
  have hsub : {c : FiniteMeasure ℝ |
      ⌊(c.mass : ℝ) / h⌋₊ ≠
        ⌊((retainedFragments epsilon c).mass : ℝ) / h⌋₊} ⊆
      {c : FiniteMeasure ℝ | R ≤ (c.mass : ℝ)} ∪
      {c : FiniteMeasure ℝ |
        ⌊(c.mass : ℝ) / h⌋₊ ≠
          ⌊((retainedFragments epsilon c).mass : ℝ) / h⌋₊ ∧ (c.mass : ℝ) ≤ R} := by
    intro c hc
    by_cases hmass : R ≤ (c.mass : ℝ)
    · exact Or.inl hmass
    · exact Or.inr ⟨hc, (lt_of_not_ge hmass).le⟩
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans
    (add_le_add (fragment_total_mass_tail zeta R hzeta hR)
      (fragment_mesh_window_of_perpetuity zeta epsilon delta h R
        hzeta hepsilon hdelta hh hperpetuity)))

#print axioms original_mesh_boundary_witness
#print axioms fragment_mesh_original_boundary_probability
#print axioms fragment_mass_interval_of_perpetuity
#print axioms fragment_mesh_window_of_perpetuity
#print axioms fragment_total_mass_tail
#print axioms fragment_mesh_global_of_perpetuity

end PrimeGap186
