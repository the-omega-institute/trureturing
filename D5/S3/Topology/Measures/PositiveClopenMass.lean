/- GID: D5/S3/Topology/Measures/PositiveClopenMass
   generality: G
   mirror-B: D5/B/S3/Topology/Measures/PositiveClopenMass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Regular Jordan positive mass is approximated by signed clopen mass -/

import Mathlib.Basic.ENNReal.Real
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.Topology.Clopen
import Mathlib.Topology.InductiveDimension.Classes
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.Linarith

/-!
# Positive Jordan mass through signed clopen sets

For a compact Hausdorff zero-dimensional Borel space, explicit regularity of
the two finite Jordan parts lets an open set retain any strict lower threshold
of its positive mass on a clopen subset, after controlling the negative mass
by an open enlargement of a positive compact core.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set MeasureTheory

namespace D5.S3.Topology.Measures.PositiveClopenMass

/-- A regular signed measure realizes every strict lower threshold of the
positive Jordan mass of an open set on a clopen subset of that open set. -/
theorem exists_isClopen_subset_lt_apply_of_lt_posPart
    {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [ZeroDimensionalSpace K] [MeasurableSpace K] [BorelSpace K]
    (s : SignedMeasure K)
    (hp : Measure.Regular s.toJordanDecomposition.posPart)
    (hn : Measure.Regular s.toJordanDecomposition.negPart)
    {V : Set K} (hV : IsOpen V) {r : ℝ}
    (hr : r < s.toJordanDecomposition.posPart.real V) :
    ∃ W : Set K, IsClopen W ∧ W ⊆ V ∧ r < s W := by
  by_cases hrneg : r < 0
  · refine ⟨∅, isClopen_empty, empty_subset V, ?_⟩
    simpa only [VectorMeasure.empty] using hrneg
  have hrnonneg : 0 ≤ r := le_of_not_gt hrneg
  let p : Measure K := s.toJordanDecomposition.posPart
  let n : Measure K := s.toJordanDecomposition.negPart
  letI : IsFiniteMeasure p := s.toJordanDecomposition.posPart_finite
  letI : IsFiniteMeasure n := s.toJordanDecomposition.negPart_finite
  letI : Measure.Regular p := hp
  letI : Measure.Regular n := hn
  change r < p.real V at hr
  obtain ⟨b, hrb, hbV⟩ := exists_between hr
  have hbnonneg : 0 ≤ b := hrnonneg.trans hrb.le
  obtain ⟨N, hN, hpN, hnNc⟩ := s.toJordanDecomposition.mutuallySingular
  change p N = 0 at hpN
  change n Nᶜ = 0 at hnNc
  have hpA : p (V ∩ Nᶜ) = p V := by
    apply measure_inter_conull
    simpa only [compl_compl] using hpN
  have hbA : ENNReal.ofReal b < p (V ∩ Nᶜ) := by
    apply (ENNReal.ofReal_lt_iff_lt_toReal hbnonneg
      (measure_ne_top p (V ∩ Nᶜ))).2
    simpa only [Measure.real, hpA] using hbV
  obtain ⟨C, hCA, hC, hbC⟩ :=
    (hV.measurableSet.inter hN.compl).exists_lt_isCompact_of_ne_top
      (μ := p) (measure_ne_top p (V ∩ Nᶜ)) hbA
  have hbCreal : b < p.real C :=
    (ENNReal.ofReal_lt_iff_lt_toReal hbnonneg (measure_ne_top p C)).1 hbC
  have hnC : n C = 0 :=
    measure_mono_null (fun x hx => (hCA hx).2) hnNc
  have hdelta : 0 < b - r := sub_pos.mpr hrb
  have hnCdelta : n C < ENNReal.ofReal (b - r) := by
    rw [hnC]
    exact ENNReal.ofReal_pos.mpr hdelta
  obtain ⟨O, hCO, hO, hnO⟩ :=
    Set.exists_isOpen_lt_of_lt (μ := n) C (ENNReal.ofReal (b - r)) hnCdelta
  have hnOreal : n.real O < b - r := by
    have h := (ENNReal.toReal_lt_toReal (measure_ne_top n O)
      ENNReal.ofReal_ne_top).2 hnO
    simpa only [Measure.real, ENNReal.toReal_ofReal hdelta.le] using h
  obtain ⟨W, hW, hCW, hWOV⟩ :=
    exists_clopen_of_closed_subset_open hC.isClosed (hO.inter hV)
      (fun x hx => ⟨hCO hx, (hCA hx).1⟩)
  refine ⟨W, hW, (fun x hx => (hWOV hx).2), ?_⟩
  have hpCW : p.real C ≤ p.real W :=
    measureReal_mono hCW (measure_ne_top p W)
  have hnWO : n.real W ≤ n.real O :=
    measureReal_mono (fun x hx => (hWOV hx).1) (measure_ne_top n O)
  rw [s.apply_eq_posPart_real_sub_negPart_real (hW.isOpen.measurableSet)]
  change r < p.real W - n.real W
  linarith only [hbCreal, hnOreal, hpCW, hnWO]

end D5.S3.Topology.Measures.PositiveClopenMass
