/- GID: D5/S3/Observer/GoldenPrimeCircle/CayleyCauchyLimit
   generality: I
   mirror-B: D5/B/S3/Observer/GoldenPrimeCircle/CayleyCauchyLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Cyclic Haar phases converge under Cayley to the standard Cauchy law. -/

import Mathlib

/-!
The finite cyclic Haar phase with modulus `K` is the uniform law on the
nontrivial grid points `j / K`, `1 <= j < K`.  This file realizes that grid as
the intersection of `(0,1)` with the scaled integral lattice in one real
dimension, then pushes it through the Cayley chart
`u |-> tan (pi * (u - 1/2)) = -cot (pi * u)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.GoldenPrimeCircle.CayleyCauchyLimit

open Filter MeasureTheory ProbabilityTheory Set Submodule
open scoped BoundedContinuousFunction ENNReal NNReal Pointwise Real Topology

/-- One real coordinate is used so that the finite phases are literally a
scaled integral lattice, as in Mathlib's lattice-point limit theorem. -/
abbrev PhaseLine := Fin 1 -> Real

/-- The open phase interval with the same bounds in the unique coordinate. -/
def phaseBox (a b : Real) : Set PhaseLine :=
  Set.pi Set.univ (fun _ => Set.Ioo a b)

/-- The standard integral lattice in the one-dimensional phase line. -/
def phaseLattice : Set PhaseLine :=
  (Submodule.span Int (Set.range (Pi.basisFun Real (Fin 1))) :
    Submodule Int PhaseLine)

/-- The nontrivial `K`-torsion phases `j / K`, with `0 < j < K`. -/
def phaseGrid (K : Nat) : Set PhaseLine :=
  phaseBox 0 1 ∩ (K : Real)⁻¹ • phaseLattice

theorem phaseBox_isBounded (a b : Real) : Bornology.IsBounded (phaseBox a b) := by
  rw [phaseBox]
  exact Bornology.IsBounded.pi (fun _ => Metric.isBounded_Ioo a b)

theorem phaseBox_measurable (a b : Real) : MeasurableSet (phaseBox a b) := by
  unfold phaseBox
  exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo)

theorem phaseBox_volume_real {a b : Real} (hab : a <= b) :
    volume.real (phaseBox a b) = b - a := by
  rw [phaseBox, measureReal_def, Real.volume_pi_Ioo_toReal]
  · simp
  · exact fun _ => hab

theorem phaseBox_frontier_volume_zero {a b : Real} (hab : a < b) :
    volume (frontier (phaseBox a b)) = 0 := by
  let e : PhaseLine ≃ₜ Real := Homeomorph.funUnique (Fin 1) Real
  have hpreimage : e ⁻¹' Set.Ioo a b = phaseBox a b := by
    ext x
    simp [e, phaseBox, Unique.forall_iff]
  have hfrontier : frontier (phaseBox a b) = e ⁻¹' ({a, b} : Set Real) := by
    rw [← hpreimage, ← e.preimage_frontier, frontier_Ioo hab]
  rw [hfrontier]
  have hp := volume_preserving_funUnique (Fin 1) Real
  have hmap :
      volume ((MeasurableEquiv.funUnique (Fin 1) Real) ⁻¹' ({a, b} : Set Real)) =
        volume ({a, b} : Set Real) := by
    rw [← hp.map_eq]
    exact (Measure.map_apply (μ := (volume : Measure PhaseLine)) hp.measurable
      (by measurability)).symm
  calc
    volume (e ⁻¹' ({a, b} : Set Real)) =
        volume ((MeasurableEquiv.funUnique (Fin 1) Real) ⁻¹'
          ({a, b} : Set Real)) := by rfl
    _ = volume ({a, b} : Set Real) := hmap
    _ = 0 := by
      apply le_antisymm
      · calc
          volume ({a, b} : Set Real) <= volume ({a} : Set Real) + volume ({b} : Set Real) := by
            simpa only [singleton_union] using
              (measure_union_le ({a} : Set Real) ({b} : Set Real) (μ := volume))
          _ = 0 := by rw [Real.volume_singleton, Real.volume_singleton, add_zero]
      · exact bot_le

theorem phaseBox_lattice_card_tendsto {a b : Real} (hab : a < b) :
    Tendsto
      (fun K : Nat =>
        (Nat.card ↥(phaseBox a b ∩ (K : Real)⁻¹ • phaseLattice) : Real) / K)
      atTop (nhds (b - a)) := by
  simpa [phaseLattice, Fintype.card_fin, phaseBox_volume_real hab.le] using
    (tendsto_card_div_pow_atTop_volume (ι := Fin 1) (s := phaseBox a b)
      (phaseBox_isBounded a b) (phaseBox_measurable a b)
      (phaseBox_frontier_volume_zero hab))

theorem phaseGrid_finite (K : Nat) : (phaseGrid K).Finite := by
  by_cases hK : K = 0
  · subst K
    refine (Set.finite_singleton (0 : PhaseLine)).subset ?_
    intro x hx
    simpa [phaseGrid, phaseLattice] using hx.2
  · unfold phaseGrid phaseLattice
    rw [← coe_pointwise_smul,
      ZSpan.smul _ (inv_ne_zero (Nat.cast_ne_zero.mpr hK))]
    exact ZSpan.setFinite_inter _ (phaseBox_isBounded 0 1)

theorem phaseGrid_nonempty (n : Nat) : (phaseGrid (n + 2)).Nonempty := by
  let K : Nat := n + 2
  let x : PhaseLine := fun _ => (K : Real)⁻¹
  have hK : (0 : Real) < K := by positivity
  have hxBox : x ∈ phaseBox 0 1 := by
    intro i hi
    simp only [x, Set.mem_Ioo]
    refine ⟨inv_pos.mpr hK, inv_lt_one_of_one_lt₀ ?_⟩
    exact_mod_cast Nat.succ_lt_succ (Nat.zero_lt_succ n)
  have hxLattice : (fun _ : Fin 1 => (1 : Real)) ∈ phaseLattice := by
    change (fun _ : Fin 1 => (1 : Real)) ∈
      Submodule.span Int (Set.range (Pi.basisFun Real (Fin 1)))
    rw [(Pi.basisFun Real (Fin 1)).mem_span_iff_repr_mem Int]
    intro i
    exact ⟨1, by simp⟩
  refine ⟨x, hxBox, ?_⟩
  change x ∈ (K : Real)⁻¹ • phaseLattice
  have hsmul : (K : Real)⁻¹ • (fun _ : Fin 1 => (1 : Real)) ∈
      (K : Real)⁻¹ • phaseLattice := Set.smul_mem_smul_set hxLattice
  convert hsmul using 1
  ext i
  simp [x, Pi.smul_apply]

theorem uniformOn_measureReal {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] {s t : Set α} (hs : s.Finite) (hs0 : s.Nonempty) :
    (ProbabilityTheory.uniformOn s).real t =
      ((s ∩ t).ncard : Real) / s.ncard := by
  rw [measureReal_def, ProbabilityTheory.uniformOn,
    cond_apply hs.measurableSet,
    Measure.count_apply_finite s hs,
    Measure.count_apply_finite (s ∩ t) (hs.inter_of_left t),
    ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    Set.ncard_eq_toFinset_card (s ∩ t) (hs.inter_of_left t),
    Set.ncard_eq_toFinset_card s hs]
  have hcard : hs.toFinset.card ≠ 0 := by
    rw [Finset.card_ne_zero, hs.toFinset_nonempty]
    exact hs0
  field_simp

/-- Uniform probability measure on the `n+2` cyclic phase grid. -/
def cyclicHaarPhase (n : Nat) : ProbabilityMeasure PhaseLine :=
  ⟨ProbabilityTheory.uniformOn (phaseGrid (n + 2)),
    ProbabilityTheory.isProbabilityMeasure_uniformOn
      (phaseGrid_finite (n + 2)) (phaseGrid_nonempty n)⟩

/-- The real Cayley chart on the open phase interval. -/
def cayleyPhase (u : Real) : Real :=
  Real.tan (Real.pi * (u - 1 / 2))

theorem cayleyPhase_measurable :
    Measurable (fun x : PhaseLine => cayleyPhase (x 0)) := by
  unfold cayleyPhase Real.tan
  fun_prop

/-- This is the source's Cayley formula, not a replacement chart. -/
theorem cayleyPhase_eq_neg_cot (u : Real) :
    cayleyPhase u = -Real.cot (Real.pi * u) := by
  rw [cayleyPhase, show Real.pi * (u - 1 / 2) =
      -(Real.pi / 2 - Real.pi * u) by ring,
    Real.tan_neg, Real.tan_pi_div_two_sub, Real.tan_inv_eq_cot]

/-- The finite cyclic Haar phase after the Cayley map. -/
def cayleyCauchyEmpirical (n : Nat) : ProbabilityMeasure Real :=
  (cyclicHaarPhase n).map
    cayleyPhase_measurable.aemeasurable

/-- The canonical standard Cauchy probability measure from Mathlib. -/
def standardCauchyProbabilityMeasure : ProbabilityMeasure Real :=
  ⟨ProbabilityTheory.cauchyMeasure 0 1, inferInstance⟩

/-- The Cayley coordinate has inverse phase `arctan(h)/pi + 1/2`. -/
def inverseCayleyPhase (h : Real) : Real :=
  Real.arctan h / Real.pi + 1 / 2

theorem inverseCayleyPhase_mem (h : Real) : inverseCayleyPhase h ∈ Set.Ioo 0 1 := by
  have hp := Real.pi_pos
  have ha := Real.arctan_mem_Ioo h
  have hhalf : Real.pi / 2 / Real.pi = (1 : Real) / 2 := by
    field_simp [Real.pi_ne_zero]
  constructor <;> unfold inverseCayleyPhase
  · have := (div_lt_div_iff_of_pos_right hp).mpr ha.1
    rw [neg_div, hhalf] at this
    linarith
  · have := (div_lt_div_iff_of_pos_right hp).mpr ha.2
    rw [hhalf] at this
    linarith

theorem cayleyPhase_inverse (h : Real) : cayleyPhase (inverseCayleyPhase h) = h := by
  rw [cayleyPhase, inverseCayleyPhase]
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  convert Real.tan_arctan h using 1
  field_simp [hp] <;> ring

theorem inverse_cayleyPhase {u : Real} (hu : u ∈ Set.Ioo 0 1) :
    inverseCayleyPhase (cayleyPhase u) = u := by
  unfold inverseCayleyPhase cayleyPhase
  rw [Real.arctan_tan]
  · field_simp [Real.pi_ne_zero]
    ring
  · nlinarith [Real.pi_pos, hu.1]
  · nlinarith [Real.pi_pos, hu.2]

theorem cayleyPhase_strictMonoOn : StrictMonoOn cayleyPhase (Set.Ioo 0 1) := by
  intro u hu v hv huv
  apply Real.strictMonoOn_tan
  · constructor <;> nlinarith [Real.pi_pos, hu.1, hu.2]
  · constructor <;> nlinarith [Real.pi_pos, hv.1, hv.2]
  · exact mul_lt_mul_of_pos_left (sub_lt_sub_right huv _) Real.pi_pos

theorem cayleyPhase_preimage_Ioo_inter_phaseGrid (K : Nat) (a b : Real) :
    phaseGrid K ∩ (fun x : PhaseLine => cayleyPhase (x 0)) ⁻¹' Set.Ioo a b =
      phaseBox (inverseCayleyPhase a) (inverseCayleyPhase b) ∩
        (K : Real)⁻¹ • phaseLattice := by
  ext x
  constructor
  · rintro ⟨⟨hxBox, hxLattice⟩, haxb⟩
    refine ⟨?_, hxLattice⟩
    intro i hi
    fin_cases i
    exact ⟨(cayleyPhase_strictMonoOn.lt_iff_lt
        (inverseCayleyPhase_mem a) (hxBox 0 trivial)).mp
          (by simpa [cayleyPhase_inverse] using haxb.1),
      (cayleyPhase_strictMonoOn.lt_iff_lt
        (hxBox 0 trivial) (inverseCayleyPhase_mem b)).mp
          (by simpa [cayleyPhase_inverse] using haxb.2)⟩
  · rintro ⟨hxInverse, hxLattice⟩
    have hx0 : x 0 ∈ Set.Ioo 0 1 :=
      ⟨(inverseCayleyPhase_mem a).1.trans (hxInverse 0 trivial).1,
        (hxInverse 0 trivial).2.trans (inverseCayleyPhase_mem b).2⟩
    refine ⟨⟨?_, hxLattice⟩, ?_⟩
    · intro i hi
      fin_cases i
      exact hx0
    · have hleft := (cayleyPhase_strictMonoOn.lt_iff_lt
        (inverseCayleyPhase_mem a) hx0).mpr (hxInverse 0 trivial).1
      have hright := (cayleyPhase_strictMonoOn.lt_iff_lt
        hx0 (inverseCayleyPhase_mem b)).mpr (hxInverse 0 trivial).2
      exact ⟨by simpa [cayleyPhase_inverse] using hleft,
        by simpa [cayleyPhase_inverse] using hright⟩

theorem cayleyCauchyEmpirical_measureReal_Ioo (n : Nat) (a b : Real) :
    (cayleyCauchyEmpirical n : Measure Real).real (Set.Ioo a b) =
      ((phaseBox (inverseCayleyPhase a) (inverseCayleyPhase b) ∩
          ((n + 2 : Nat) : Real)⁻¹ • phaseLattice).ncard : Real) /
        (phaseGrid (n + 2)).ncard := by
  rw [cayleyCauchyEmpirical, measureReal_def,
    ProbabilityMeasure.toMeasure_map,
    Measure.map_apply_of_aemeasurable cayleyPhase_measurable.aemeasurable
      (measurableSet_Ioo : MeasurableSet (Set.Ioo a b)),
    ← measureReal_def,
    show (cyclicHaarPhase n : Measure PhaseLine) =
        ProbabilityTheory.uniformOn (phaseGrid (n + 2)) by rfl,
    uniformOn_measureReal (phaseGrid_finite (n + 2)) (phaseGrid_nonempty n),
    cayleyPhase_preimage_Ioo_inter_phaseGrid]

theorem standardCauchy_cdf (x : Real) :
    ProbabilityTheory.cdf (ProbabilityTheory.cauchyMeasure 0 1) x =
      inverseCayleyPhase x := by
  rw [ProbabilityTheory.cdf_eq_real,
    ProbabilityTheory.cauchyMeasure_of_scale_ne_zero (x₀ := 0) (by norm_num),
    measureReal_def, withDensity_apply _ measurableSet_Iic]
  simp only [ProbabilityTheory.cauchyPDF]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (ProbabilityTheory.integrable_cauchyPDFReal 0).integrableOn
    (ae_restrict_of_forall_mem measurableSet_Iic fun y _ =>
      (ProbabilityTheory.cauchyPDF_pos 0 (by norm_num) y).le),
    ENNReal.toReal_ofReal]
  · simp only [ProbabilityTheory.cauchyPDFReal_def, NNReal.coe_one, sub_zero,
      one_pow, mul_one, inv_mul_eq_div]
    simp_rw [div_eq_inv_mul]
    rw [MeasureTheory.integral_const_mul]
    have hintegral :
        (∫ y : Real in Set.Iic x, (y ^ 2 + 1)⁻¹) =
          Real.arctan x + Real.pi / 2 := by
      simpa [add_comm] using (integral_Iic_inv_one_add_sq (i := x))
    rw [hintegral]
    unfold inverseCayleyPhase
    field_simp [Real.pi_ne_zero]
  · exact integral_nonneg_of_ae
      (ae_restrict_of_forall_mem measurableSet_Iic fun y _ =>
        (ProbabilityTheory.cauchyPDF_pos 0 (by norm_num) y).le)

theorem continuous_inverseCayleyPhase : Continuous inverseCayleyPhase := by
  unfold inverseCayleyPhase
  fun_prop

theorem standardCauchy_measureReal_Ioo {a b : Real} (hab : a < b) :
    (ProbabilityTheory.cauchyMeasure 0 1).real (Set.Ioo a b) =
      inverseCayleyPhase b - inverseCayleyPhase a := by
  have hcdf : ProbabilityTheory.cdf (ProbabilityTheory.cauchyMeasure 0 1) =
      inverseCayleyPhase := funext standardCauchy_cdf
  have hcontinuousCDF : Continuous
      (ProbabilityTheory.cdf (ProbabilityTheory.cauchyMeasure 0 1) : Real -> Real) := by
    rw [hcdf]
    exact continuous_inverseCayleyPhase
  rw [measureReal_def,
    ← ProbabilityTheory.measure_cdf (ProbabilityTheory.cauchyMeasure 0 1),
    StieltjesFunction.measure_Ioo,
    (hcontinuousCDF.continuousAt.continuousWithinAt.leftLim_eq),
    standardCauchy_cdf, standardCauchy_cdf,
    ENNReal.toReal_ofReal]
  apply sub_nonneg.mpr
  unfold inverseCayleyPhase
  gcongr

theorem standardCauchy_singleton_zero (x : Real) :
    ProbabilityTheory.cauchyMeasure 0 1 ({x} : Set Real) = 0 := by
  rw [ProbabilityTheory.cauchyMeasure_of_scale_ne_zero (x₀ := 0) (by norm_num)]
  exact measure_singleton x

theorem standardCauchyProbabilityMeasure_singleton_zero (x : Real) :
    (standardCauchyProbabilityMeasure : Measure Real) ({x} : Set Real) = 0 := by
  change ProbabilityTheory.cauchyMeasure 0 1 ({x} : Set Real) = 0
  exact standardCauchy_singleton_zero x

/-- Finite cyclic Haar phases converge strictly, after the Cayley chart, to
Mathlib's standard Cauchy probability measure. -/
theorem cayley_cauchy_limit :
    Tendsto cayleyCauchyEmpirical atTop (nhds standardCauchyProbabilityMeasure) := by
  let intervalSystem : Set (Set Real) :=
    {s | ∃ a b : Real, a < b ∧ Set.Ioo a b = s}
  have hPi : IsPiSystem intervalSystem := by
    simpa [intervalSystem] using
      (isPiSystem_Ioo (fun x : Real => x) (fun x : Real => x))
  apply hPi.tendsto_probabilityMeasure_of_tendsto_of_mem
  · intro s hs
    rcases hs with ⟨a, b, _, rfl⟩
    exact measurableSet_Ioo
  · intro u hu x hx
    rcases mem_nhds_iff_exists_Ioo_subset.mp (hu.mem_nhds hx) with
      ⟨a, b, hxab, hab⟩
    exact ⟨Set.Ioo a b, ⟨a, b, hxab.1.trans hxab.2, rfl⟩,
      Ioo_mem_nhds hxab.1 hxab.2, hab⟩
  · intro s hs
    rcases hs with ⟨a, b, hab, rfl⟩
    have hinverse : inverseCayleyPhase a < inverseCayleyPhase b := by
      unfold inverseCayleyPhase
      gcongr
    have hnum := (phaseBox_lattice_card_tendsto hinverse).comp
      (tendsto_add_atTop_nat 2)
    have hden := (phaseBox_lattice_card_tendsto (show (0 : Real) < 1 by norm_num)).comp
      (tendsto_add_atTop_nat 2)
    have hratio := hnum.div hden (by norm_num)
    have hratio' :
        Tendsto
          (fun n : Nat =>
            ((phaseBox (inverseCayleyPhase a) (inverseCayleyPhase b) ∩
                ((n + 2 : Nat) : Real)⁻¹ • phaseLattice).ncard : Real) /
              (phaseGrid (n + 2)).ncard)
          atTop (nhds (inverseCayleyPhase b - inverseCayleyPhase a)) := by
      convert hratio.congr' (Eventually.of_forall fun n => ?_) using 1
      · norm_num
      · simp only [Nat.card_coe_set_eq, phaseGrid]
        apply div_div_div_cancel_right₀
        positivity
    rw [← NNReal.tendsto_coe]
    convert hratio' using 1
    · funext n
      rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn,
        cayleyCauchyEmpirical_measureReal_Ioo]
    · rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn]
      change 𝓝 ((ProbabilityTheory.cauchyMeasure 0 1).real (Set.Ioo a b)) = _
      rw [standardCauchy_measureReal_Ioo hab]

/-- Reverse probe for the single CAS assertion: weak convergence gives exactly
the bounded-continuous test-function limit stated immediately before the atom. -/
theorem cayley_cauchy_limit_integral_probe (f : Real →ᵇ Real) :
    Tendsto
      (fun n => ∫ x, f x ∂(cayleyCauchyEmpirical n : Measure Real))
      atTop
      (nhds (∫ x, f x ∂(standardCauchyProbabilityMeasure : Measure Real))) :=
  ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    cayley_cauchy_limit f

/-- The point mass at zero, used only to test that the public limit cannot
collapse to a constant sequence. -/
def zeroPointMass : ProbabilityMeasure Real :=
  ⟨Measure.dirac (0 : Real), inferInstance⟩

theorem zeroPointMass_singleton :
    (zeroPointMass : Measure Real) ({0} : Set Real) = 1 := by
  change Measure.dirac (0 : Real) ({0} : Set Real) = 1
  exact Measure.dirac_apply_of_mem (Set.mem_singleton 0)

/-- Trivialization probe: a constant point mass cannot satisfy the public
weak-limit assertion. -/
theorem constant_point_mass_not_cauchy :
    ¬Tendsto (fun _ : Nat => zeroPointMass)
      atTop (nhds standardCauchyProbabilityMeasure) := by
  intro h
  have hconst : Tendsto (fun _ : Nat => zeroPointMass) atTop (nhds zeroPointMass) :=
    tendsto_const_nhds
  have heq := tendsto_nhds_unique hconst h
  have hsingleton := congr_arg
    (fun μ : ProbabilityMeasure Real => (μ : Measure Real) ({0} : Set Real)) heq
  rw [zeroPointMass_singleton,
    standardCauchyProbabilityMeasure_singleton_zero] at hsingleton
  exact one_ne_zero hsingleton

#print axioms cayley_cauchy_limit
#print axioms cayley_cauchy_limit_integral_probe
#print axioms constant_point_mass_not_cauchy

end D5.S3.Observer.GoldenPrimeCircle.CayleyCauchyLimit
