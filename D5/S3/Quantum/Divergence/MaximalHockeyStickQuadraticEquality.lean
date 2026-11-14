/- GID: D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticEquality
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/MaximalHockeyStickQuadraticEquality
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: Integrated quadratic equality and approximate-test transfer for singular matrix pairs. -/

import D5.S3.Quantum.Divergence.MaximalHockeyStickQuadraticIntegral

/-! The compact reference detects the original common-interior commutator. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Filter Matrix MeasureTheory Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology
open D5.S3.Quantum.Divergence.MaximalHockeyStickOverlap
open D5.S3.Quantum.Divergence.MaximalHockeyStickSupport
open D5.S3.Quantum.Divergence.MaximalHockeyStickSpectral
open D5.S3.Quantum.Divergence.MaximalHockeyStickThreshold
open D5.S3.Quantum.Divergence.MaximalHockeyStickSingularCriterion
open D5.S3.Quantum.Divergence.MaximalHockeyStickOriginalPair
open D5.S3.Quantum.Divergence.MaximalHockeyStickQuadratic
open D5.S3.Quantum.Divergence.MaximalHockeyStickQuadraticBound
open D5.S3.Quantum.Divergence.MaximalHockeyStickQuadraticCanonical
open D5.S3.Quantum.Divergence.MaximalHockeyStickQuadraticIntegral
open D5.S3.Quantum.Divergence.MaximalHockeyStickApproximate
open D5.S3.Quantum.Divergence.MaximalHockeyStickReverseTest

namespace D5.S3.Quantum.Divergence.MaximalHockeyStickQuadraticEquality

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The compactly rescaled actual maximal hockey profile. Values at the two
endpoints do not affect its Lebesgue integral. -/
def compactMaximal (A B : Matrix n n ℂ) (u : ℝ) : ℝ :=
  (1 - u) * maximalHockey A B (u / (1 - u))

/-- The integrated maximal hockey quantity for the standard quadratic
generator, using its exact finite-interval perspective representation. -/
def quadraticHockeyValue (A B : Matrix n n ℂ) : ℝ :=
  B.trace.re - 3 * A.trace.re + 8 * ∫ u in Ioo (0 : ℝ) 1, compactMaximal A B u

private def compactGap {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (u : ℝ) : ℝ := compactHockey R u - compactMaximal A B u

private theorem compact_gap_eq_scaled {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
    compactGap R u = (1 - u) * gap R ⟨u / (1 - u), div_pos hu.1 (sub_pos.mpr hu.2)⟩ := by
  rw [compactGap, compact_hockey_eq_scaled R u hu.2]
  unfold compactMaximal gap
  ring

private theorem compact_gap_continuous {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ContinuousOn (compactGap R) (Ioo (0 : ℝ) 1) := by
  let T : Ioo (0 : ℝ) 1 → PositiveThreshold := fun u =>
    ⟨u.1 / (1 - u.1), div_pos u.2.1 (sub_pos.mpr u.2.2)⟩
  have hT : Continuous T := by
    exact (continuous_subtype_val.div (continuous_const.sub continuous_subtype_val)
      (fun u => ne_of_gt (sub_pos.mpr u.2.2))).subtype_mk
        (fun u => div_pos u.2.1 (sub_pos.mpr u.2.2))
  rw [continuousOn_iff_continuous_restrict]
  convert (continuous_const.sub continuous_subtype_val).mul
    ((actual_gap_profile_data R hA hB).2.continuous.comp hT) using 1
  funext u
  exact compact_gap_eq_scaled R u u.2

private theorem compact_gap_bounds {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
    0 ≤ compactGap R u ∧ compactGap R u ≤ A.trace.re := by
  rw [compact_gap_eq_scaled R u hu]
  have hd := (actual_gap_profile_data R hA hB).1
    ⟨u / (1 - u), div_pos hu.1 (sub_pos.mpr hu.2)⟩
  refine ⟨mul_nonneg (sub_nonneg.mpr hu.2.le) hd.1, ?_⟩
  calc
    _ ≤ 1 * gap R ⟨u / (1 - u), div_pos hu.1 (sub_pos.mpr hu.2)⟩ :=
      mul_le_mul_of_nonneg_right (by linarith [hu.1]) hd.1
    _ ≤ A.trace.re := by simpa only [one_mul] using hd.2

private theorem compact_gap_integrable {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    IntegrableOn (compactGap R) (Ioo (0 : ℝ) 1) := by
  apply (integrableOn_const (C := A.trace.re) (s := Ioo (0 : ℝ) 1)
    (by simp [Real.volume_Ioo])).mono'
    ((compact_gap_continuous R hA hB).aestronglyMeasurable measurableSet_Ioo)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
  simpa only [Real.norm_eq_abs, abs_of_nonneg (compact_gap_bounds R hA hB u hu).1] using
    (compact_gap_bounds R hA hB u hu).2

private theorem compact_maximal_integrable (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    IntegrableOn (compactMaximal A B) (Ioo (0 : ℝ) 1) := by
  obtain ⟨R, -, -⟩ := quadratic_reverse_test_attained_profile A B hA hB
  have hi : IntegrableOn (compactHockey R) (Ioo (0 : ℝ) 1) :=
    ((compact_hockey_continuous R).continuousOn.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  convert hi.sub (compact_gap_integrable R hA hB) using 1
  funext u
  change compactMaximal A B u = compactHockey R u - (compactHockey R u - compactMaximal A B u)
  ring

private theorem star_cost_gap_integral {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    R.starCost - quadraticHockeyValue A B =
      8 * ∫ u in Ioo (0 : ℝ) 1, compactGap R u := by
  have hi : IntegrableOn (compactHockey R) (Ioo (0 : ℝ) 1) :=
    ((compact_hockey_continuous R).continuousOn.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  rw [star_cost_hockey_integral R, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]
  unfold quadraticHockeyValue compactGap
  rw [integral_sub hi (compact_maximal_integrable A B hA hB)]
  ring

private theorem quadratic_hockey_le_cost {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    quadraticHockeyValue A B ≤ R.starCost := by
  have hn : 0 ≤ ∫ u in Ioo (0 : ℝ) 1, compactGap R u := by
    apply integral_nonneg_of_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
    exact (compact_gap_bounds R hA hB u hu).1
  have he := star_cost_gap_integral R hA hB
  linarith

private theorem zero_compact_gap_all_thresholds {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (he : R.starCost = quadraticHockeyValue A B) :
    ∀ t : ℝ, 0 < t → R.hockey t = maximalHockey A B t := by
  have hz : (∫ u in Ioo (0 : ℝ) 1, compactGap R u) = 0 := by
    have hi := star_cost_gap_integral R hA hB
    rw [he] at hi
    linarith
  have hn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] compactGap R := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
    exact (compact_gap_bounds R hA hB u hu).1
  have hae := (integral_eq_zero_iff_of_nonneg_ae hn (compact_gap_integrable R hA hB)).1 hz
  have heq := MeasureTheory.Measure.eqOn_open_of_ae_eq hae isOpen_Ioo
    (compact_gap_continuous R hA hB) continuousOn_const
  intro t ht
  let u := t / (1 + t)
  have hden : 0 < 1 + t := by linarith
  have hu : u ∈ Ioo (0 : ℝ) 1 := ⟨div_pos ht hden,
    (div_lt_one hden).2 (by linarith)⟩
  have hratio : u / (1 - u) = t := by dsimp [u]; field_simp; ring
  have hz' := heq hu
  rw [compact_gap_eq_scaled R u hu] at hz'
  have hgap : gap R ⟨u / (1 - u), div_pos hu.1 (sub_pos.mpr hu.2)⟩ = 0 :=
    (mul_eq_zero.mp hz').resolve_left (ne_of_gt (sub_pos.mpr hu.2))
  simpa only [gap, hratio, sub_eq_zero] using hgap

/-- Exact integrated equality classification for the actual quadratic
reverse-test infimum, for every finite PSD pair and its common interior
corner, including singular, zero and empty matrix spaces. -/
theorem quadratic_integrated_eq_iff_commute (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    let S := A + B
    let C := MaximalHockeyStickSupport.normalize S A
    let P := interiorProjection C
    (maximalQuadratic A B = (quadraticHockeyValue A B : EReal)) ↔
      (P * S * P) * (P * C * P) = (P * C * P) * (P * S * P) := by
  dsimp only
  obtain ⟨R, hcost, hprofile⟩ := quadratic_reverse_test_attained_profile A B hA hB
  rw [maximal_quadratic_eq_value A B hA hB, EReal.coe_eq_coe_iff]
  constructor
  · intro he
    apply (original_all_thresholds_iff_commute A B hA hB).1
    intro t ht
    rw [← hprofile t]
    exact (zero_compact_gap_all_thresholds R hA hB (hcost.trans he) t ht).symm
  · intro hc
    have he := (original_all_thresholds_iff_commute A B hA hB).2 hc
    have hz : (∫ u in Ioo (0 : ℝ) 1, compactGap R u) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
      rw [compact_gap_eq_scaled R u hu]
      have hp : R.hockey (u / (1 - u)) = maximalHockey A B (u / (1 - u)) :=
        (hprofile _).trans (he _ (div_pos hu.1 (sub_pos.mpr hu.2))).symm
      simp only [gap, hp, sub_self, mul_zero, Pi.zero_apply]
    have hi := star_cost_gap_integral R hA hB
    rw [hz, mul_zero, hcost] at hi
    linarith

/-- The same original-pair commutator follows from any sequence of actual
finite tests whose integrable gaps vanish against a full-support locally
finite measure. The scalar convex representation and finite-cost
approximation are explicit obligations of a general-generator consumer. -/
theorem vanishing_curvature_gaps_imply_commute
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (μ : Measure PositiveThreshold) [μ.IsOpenPosMeasure] [IsLocallyFiniteMeasure μ]
    (tests : ∀ j : ℕ, Σ k : ℕ, ReverseTest A B k)
    (hint : ∀ j, Integrable (gap (tests j).2) μ)
    (hlim : Tendsto (fun j => ∫ t, gap (tests j).2 t ∂μ) atTop (𝓝 0)) :
    let S := A + B
    let C := MaximalHockeyStickSupport.normalize S A
    let P := interiorProjection C
    (P * S * P) * (P * C * P) = (P * C * P) * (P * S * P) := by
  have hp := (actual_tests_full_support_transfer hA hB μ 0 tests
    (fun j => gap (tests j).2) (fun _ _ => rfl) hint hlim (by simp)).1
  have hDCT := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (F := fun j => compactGap (tests j).2) (f := fun _ : ℝ => 0)
    (fun _ : ℝ => A.trace.re)
    (fun j => (compact_gap_continuous (tests j).2 hA hB).aestronglyMeasurable measurableSet_Ioo)
    (integrableOn_const (C := A.trace.re) (by simp [Real.volume_Ioo]))
    (fun j => by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
      simpa only [Real.norm_eq_abs, abs_of_nonneg (compact_gap_bounds (tests j).2 hA hB u hu).1]
        using (compact_gap_bounds (tests j).2 hA hB u hu).2)
    (by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
      have hh := (hp ⟨u / (1 - u), div_pos hu.1 (sub_pos.mpr hu.2)⟩).const_mul (1 - u)
      simpa only [compact_gap_eq_scaled _ u hu, mul_zero] using hh)
  have hcostlim : Tendsto (fun j => (tests j).2.starCost) atTop (𝓝 (quadraticHockeyValue A B)) := by
    have hh := (hDCT.const_mul 8).add_const (quadraticHockeyValue A B)
    simp only [integral_zero, mul_zero, zero_add] at hh
    convert hh using 1
    funext j
    have he := star_cost_gap_integral (tests j).2 hA hB
    linarith
  have hle : quadraticValue A B ≤ quadraticHockeyValue A B := by
    apply ge_of_tendsto hcostlim
    exact Eventually.of_forall (fun j => quadratic_value_le_test A B hA hB (tests j).2)
  obtain ⟨R, hcost, -⟩ := quadratic_reverse_test_attained_profile A B hA hB
  have hge : quadraticHockeyValue A B ≤ quadraticValue A B := by
    rw [← hcost]
    exact quadratic_hockey_le_cost R hA hB
  apply (quadratic_integrated_eq_iff_commute A B hA hB).1
  rw [maximal_quadratic_eq_value A B hA hB, le_antisymm hle hge]

end D5.S3.Quantum.Divergence.MaximalHockeyStickQuadraticEquality
