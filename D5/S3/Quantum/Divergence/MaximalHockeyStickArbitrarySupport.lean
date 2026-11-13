/- GID: D5/S3/Quantum/Divergence/MaximalHockeyStickArbitrarySupport
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/MaximalHockeyStickArbitrarySupport
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: Arbitrary curvature support equality for the original whole-L1 maximal divergence. -/

import D5.S3.Quantum.Divergence.MaximalHockeyStickAllL1Convex
import D5.S3.Quantum.Divergence.MaximalHockeyStickComponents
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Sequences
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Tactic



universe u

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Filter Matrix MeasureTheory Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology ENNReal
open D5.S3.Analytic.Convexity.CurvatureHingeRepresentation
open D5.S3.Quantum.Divergence.MaximalHockeyStickOverlap
open D5.S3.Quantum.Divergence.MaximalHockeyStickProfile
open D5.S3.Quantum.Divergence.MaximalHockeyStickQuadratic
open D5.S3.Quantum.Divergence.MaximalHockeyStickReverseTest
open D5.S3.Quantum.Divergence.MaximalHockeyStickApproximate
open D5.S3.Quantum.Divergence.MaximalHockeyStickConvex
open D5.S3.Quantum.Divergence.MaximalHockeyStickAllL1Convex

namespace D5.S3.Quantum.Divergence.MaximalHockeyStickArbitrarySupport

/-! Only the positive-neighborhood step changes from FullSupportProfileTransfer.
The pointwise statement needs neither a global bound nor a second measure. -/

theorem tendsto_zero_at_support_of_integral
    {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] (μ : Measure α) [IsLocallyFiniteMeasure μ]
    (K : ℝ) (hK : 0 ≤ K) (g : ℕ → α → ℝ)
    (hnonneg : ∀ j x, 0 ≤ g j x)
    (hlip : ∀ j, LipschitzWith (Real.toNNReal K) (g j))
    (hint : ∀ j, Integrable (g j) μ)
    (hlim : Tendsto (fun j => ∫ x, g j x ∂μ) atTop (𝓝 0))
    (x : α) (hx : x ∈ μ.support) :
    Tendsto (fun j => g j x) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  by_contra hbad
  have hfreq : ∃ᶠ j in atTop, ¬dist (g j x) 0 < ε := by
    rw [frequently_atTop]
    intro N
    by_contra hN
    push_neg at hN
    exact hbad ⟨N, hN⟩
  obtain ⟨U, hxU, hUopen, hUfin⟩ := μ.exists_isOpen_measure_lt_top x
  let δ : ℝ := ε / (2 * (K + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let V : Set α := U ∩ Metric.ball x δ
  have hVopen : IsOpen V := hUopen.inter Metric.isOpen_ball
  have hxV : x ∈ V := ⟨hxU, Metric.mem_ball_self hδ⟩
  have hVpos : 0 < μ V :=
    (Measure.mem_support_iff_forall x).1 hx V (hVopen.mem_nhds hxV)
  have hVfin : μ V < ⊤ :=
    lt_of_le_of_lt (measure_mono inter_subset_left) hUfin
  have hμreal : 0 < μ.real V := ENNReal.toReal_pos hVpos.ne' hVfin.ne
  let c : ℝ := (ε / 2) * μ.real V
  have hc : 0 < c := by dsimp [c]; exact mul_pos (by linarith) hμreal
  have hsmall : ∀ᶠ j in atTop, (∫ x, g j x ∂μ) < c := by
    have ht := (Metric.tendsto_atTop.1 hlim) c hc
    filter_upwards [Filter.eventually_atTop.2 ht] with j hj
    have hj' : |(∫ x, g j x ∂μ)| < c := by
      simpa only [Real.dist_eq, sub_zero] using hj
    exact lt_of_le_of_lt (le_abs_self _) hj'
  have hfreq' : ∃ᶠ j in atTop, ε ≤ g j x := by
    exact hfreq.mono (fun j hj => by
      have hj' : ε ≤ |g j x| := by
        simpa only [Real.dist_eq, sub_zero, not_lt] using hj
      simpa only [abs_of_nonneg (hnonneg j x)] using hj')
  obtain ⟨j, hjgap, hjsmall⟩ := (hfreq'.and_eventually hsmall).exists
  have hlower : c ≤ ∫ x, g j x ∂μ := by
    have hconst : ∀ y ∈ V, ε / 2 ≤ g j y := by
      intro y hy
      have hyd : dist y x < δ := Metric.mem_ball.mp hy.2
      have hKdist : K * dist y x ≤ ε / 2 := by
        have hmul : K * dist y x ≤ K * δ :=
          mul_le_mul_of_nonneg_left hyd.le hK
        have hδ' : K * δ ≤ ε / 2 := by
          have hden : 0 < 2 * (K + 1) := by positivity
          calc
            K * δ = (K * ε) / (2 * (K + 1)) := by dsimp [δ]; ring
            _ ≤ ε / 2 := (div_le_iff₀ hden).2 (by nlinarith)
        exact hmul.trans hδ'
      have hdist : |g j y - g j x| ≤ K * dist y x := by
        simpa only [Real.dist_eq, Real.coe_toNNReal', max_eq_left hK] using
          (hlip j).dist_le_mul y x
      have hsub : g j x - g j y ≤ |g j y - g j x| := by
        simpa only [abs_sub_comm] using le_abs_self (g j x - g j y)
      nlinarith
    calc
      c = (ε / 2) * μ.real V := rfl
      _ ≤ ∫ y in V, g j y ∂μ :=
        setIntegral_ge_of_const_le_real hVopen.measurableSet hVfin.ne
          hconst (hint j).integrableOn
      _ ≤ ∫ y, g j y ∂μ :=
        setIntegral_le_integral (hint j) (ae_of_all _ (hnonneg j))
  exact (not_lt_of_ge hlower) hjsmall

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem continuous_trace_re :
    Continuous (fun X : Matrix n n ℂ => X.trace.re) := by
  unfold Matrix.trace
  fun_prop

/-! A two-effect use of the existing subunital quadratic Jensen theorem.
No range decomposition or Douglas factorization, and no nonempty carrier. -/

private theorem square_le_scalar_residual
    (R D : Matrix n n ℂ) (hR : 0 ≤ R)
    (hlo : -R ≤ D) (hhi : D ≤ R)
    (c : ℝ) (hc : 0 < c) (hRc : ‖R‖ ≤ c) :
    D * D ≤ c • R := by
  classical
  let E : Bool → Matrix n n ℂ := fun b =>
    if b then (2 * c)⁻¹ • (R + D) else (2 * c)⁻¹ • (R - D)
  let r : Bool → ℝ := fun b => if b then c else -c
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hE : ∀ b, (E b).PosSemidef := by
    intro b
    cases b
    · exact (sub_nonneg.mpr hhi).posSemidef.smul (by positivity)
    · have hRD : 0 ≤ R + D := by
        have h := sub_nonneg.mpr hlo
        simpa only [sub_neg_eq_add, add_comm] using h
      exact hRD.posSemidef.smul (by positivity)
  have hsum : ∑ b, E b = c⁻¹ • R := by
    simp only [Fintype.sum_bool, E, Bool.false_eq_true, ↓reduceIte]
    rw [← smul_add, show (R + D) + (R - D) = (2 : ℝ) • R by module,
      smul_smul]
    congr 1
    field_simp <;> ring
  have hfirst : ∑ b, r b • E b = D := by
    have hm : -c * (2 * c)⁻¹ = -(1 / 2 : ℝ) := by field_simp; ring
    have hp : c * (2 * c)⁻¹ = (1 / 2 : ℝ) := by field_simp
    simp only [Fintype.sum_bool, r, E, Bool.false_eq_true, ↓reduceIte, smul_smul]
    rw [hm, hp]
    module
  have hsecond : ∑ b, (r b) ^ 2 • E b = c • R := by
    have hp : c ^ 2 * (2 * c)⁻¹ = c / 2 := by field_simp; ring
    simp only [Fintype.sum_bool, r, E, Bool.false_eq_true, ↓reduceIte,
      neg_sq, smul_smul]
    simp_rw [hp]
    rw [← smul_add,
      show (R + D) + (R - D) = (2 : ℝ) • R by module, smul_smul]
    congr 1
    ring
  have hRle : R ≤ c • (1 : Matrix n n ℂ) := by
    have h := (CStarAlgebra.norm_le_iff_le_algebraMap R hc.le hR).1 hRc
    simpa only [Algebra.algebraMap_eq_smul_one] using h
  have hsumle : ∑ b, E b ≤ 1 := by
    rw [hsum]
    have h := smul_le_smul_of_nonneg_left hRle (inv_nonneg.mpr hc.le)
    simpa only [smul_smul, inv_mul_cancel₀ hc0, one_smul] using h
  simpa only [hfirst, hsecond] using square_jensen_subunital E r hE hsumle

/-- PSD trace-maximizing overlaps are unique. This is the constrained PSD
problem, independent of `hermitian_overlap_unique`. -/
private theorem positive_overlap_unique (A B U V : Matrix n n ℂ)
    (hU : U ∈ positiveOverlaps A B) (hV : V ∈ positiveOverlaps A B)
    (hUt : U.trace.re = overlapValue A B)
    (hVt : V.trace.re = overlapValue A B) : U = V := by
  let X : Matrix n n ℂ := (1 / 2 : ℝ) • (U + V)
  let D : Matrix n n ℂ := (1 / 2 : ℝ) • (U - V)
  have hX0 : 0 ≤ X := smul_nonneg (by norm_num) (add_nonneg hU.1 hV.1)
  have hXA : X ≤ A := by
    have h := smul_le_smul_of_nonneg_left (add_le_add hU.2.1 hV.2.1)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    convert h using 1 <;> dsimp [X] <;> module
  have hXB : X ≤ B := by
    have h := smul_le_smul_of_nonneg_left (add_le_add hU.2.2 hV.2.2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    convert h using 1 <;> dsimp [X] <;> module
  have hXt : X.trace.re = overlapValue A B := by
    dsimp [X]
    simp only [Matrix.trace_smul, Matrix.trace_add, Complex.real_smul,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, hUt, hVt]
    ring
  have hD : D.IsHermitian :=
    (hU.1.posSemidef.isHermitian.sub hV.1.posSemidef.isHermitian).smul
      (IsSelfAdjoint.all (1 / 2 : ℝ))
  have hDD : (D * D).PosSemidef := by
    simpa only [hD.eq] using Matrix.posSemidef_conjTranspose_mul_self D
  have hbds (T : Matrix n n ℂ) (hUT : U ≤ T) (hVT : V ≤ T) :
      -(T - X) ≤ D ∧ D ≤ T - X := by
    constructor
    · apply sub_nonneg.mp
      convert sub_nonneg.mpr hVT using 1 <;> dsimp [X, D] <;> module
    · apply sub_nonneg.mp
      convert sub_nonneg.mpr hUT using 1 <;> dsimp [X, D] <;> module
  let c : ℝ := max ‖A - X‖ ‖B - X‖ + 1
  have hc : 0 < c := by
    dsimp [c]
    have := norm_nonneg (A - X)
    have := le_max_left ‖A - X‖ ‖B - X‖
    linarith
  have hAc : ‖A - X‖ ≤ c := by dsimp [c]; have := le_max_left ‖A - X‖ ‖B - X‖; linarith
  have hBc : ‖B - X‖ ≤ c := by dsimp [c]; have := le_max_right ‖A - X‖ ‖B - X‖; linarith
  have hsquare (T : Matrix n n ℂ) (hXT : X ≤ T)
      (hUT : U ≤ T) (hVT : V ≤ T) (hTc : ‖T - X‖ ≤ c) :
      c⁻¹ • (D * D) ≤ T - X := by
    have hh := hbds T hUT hVT
    have h := square_le_scalar_residual (T - X) D (sub_nonneg.mpr hXT)
      hh.1 hh.2 c hc hTc
    have hs := smul_le_smul_of_nonneg_left h (inv_nonneg.mpr hc.le)
    simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul] using hs
  have hnew : X + c⁻¹ • (D * D) ∈ positiveOverlaps A B := by
    refine ⟨add_nonneg hX0 (smul_nonneg (inv_nonneg.mpr hc.le) hDD.nonneg), ?_, ?_⟩
    · simpa only [add_comm] using
        le_sub_iff_add_le.mp (hsquare A hXA hU.2.1 hV.2.1 hAc)
    · simpa only [add_comm] using
        le_sub_iff_add_le.mp (hsquare B hXB hU.2.2 hV.2.2 hBc)
  have htrace := feasible_le_value hnew
  have htr0 : 0 ≤ (D * D).trace.re :=
    (Complex.nonneg_iff.mp hDD.trace_nonneg).1
  have htr : (D * D).trace.re = 0 := by
    simp only [Matrix.trace_add, Matrix.trace_smul, Complex.add_re,
      Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, hXt] at htrace
    have hcinv : 0 < c⁻¹ := inv_pos.mpr hc
    nlinarith
  have htrC : (D * D).trace = 0 := by
    rw [Complex.eq_re_of_ofReal_le hDD.trace_nonneg, htr, Complex.ofReal_zero]
  have hDz : D = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
    (by simpa only [hD.eq] using htrC)
  have hdiff : U - V = 0 := by
    have h := congrArg (fun Z : Matrix n n ℂ => (2 : ℝ) • Z) hDz
    simpa only [D, smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
      one_smul, smul_zero] using h
  exact sub_eq_zero.mp hdiff

/-- Chosen actual PSD optimum. Values at negative parameters are irrelevant;
the explicitly included zero parameter is forced to have zero overlap. -/
def optimalOverlap (A B : Matrix n n ℂ) (hA : A.PosSemidef)
    (hB : B.PosSemidef) (t : ℝ) : Matrix n n ℂ :=
  if ht : 0 ≤ t then Classical.choose (overlap_attained A (t • B) hA (hB.smul ht))
  else 0

theorem optimalOverlap_spec (A B : Matrix n n ℂ) (hA : A.PosSemidef)
    (hB : B.PosSemidef) (t : ℝ) (ht : 0 ≤ t) :
    optimalOverlap A B hA hB t ∈ positiveOverlaps A (t • B) ∧
      (optimalOverlap A B hA hB t).trace.re = overlapValue A (t • B) := by
  simp only [optimalOverlap, dif_pos ht]
  exact Classical.choose_spec (overlap_attained A (t • B) hA (hB.smul ht))

@[simp] theorem optimalOverlap_zero (A B : Matrix n n ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) : optimalOverlap A B hA hB 0 = 0 := by
  have h := (optimalOverlap_spec A B hA hB 0 le_rfl).1
  exact le_antisymm (by simpa only [zero_smul] using h.2.2) h.1

/-- Actual Loewner secant; zero is added only as an initial interpolation knot. -/
def secant (X : ℝ → Matrix n n ℂ) (s t : ℝ) : Matrix n n ℂ :=
  (t - s)⁻¹ • (X t - X s)

/-- The manuscript's finite ordered slope criterion, including the empty
threshold set (`m = 0`). K is a set of strictly positive thresholds: neither
zero nor infinity is part of curvature support. The first knot is zero.
All inequalities are matrix/Loewner inequalities, not scalar trace tests. -/
def FiniteLoewnerSlopes (A B : Matrix n n ℂ) (hA : A.PosSemidef)
    (hB : B.PosSemidef) (K : Set PositiveThreshold) : Prop :=
  ∀ (m : ℕ) (t : Fin (m + 1) → ℝ), t 0 = 0 → StrictMono t →
    (∀ i (hi : 0 < t i), (⟨t i, hi⟩ : PositiveThreshold) ∈ K) →
    let D : Fin m → Matrix n n ℂ := fun i =>
      secant (optimalOverlap A B hA hB) (t i.castSucc) (t i.succ)
    (∀ i, 0 ≤ D i ∧ D i ≤ B) ∧ Antitone D

/-- For a nonempty tuple of slopes the bounds used in the definition are
exactly the displayed manuscript chain B >= first >= ... >= last >= 0.
The empty tuple has no conditions in either formulation. -/
theorem finite_slope_bounds_iff_chain {m : ℕ} (B : Matrix n n ℂ)
    (D : Fin (m + 1) → Matrix n n ℂ) :
    ((∀ i, 0 ≤ D i ∧ D i ≤ B) ∧ Antitone D) ↔
      D 0 ≤ B ∧ Antitone D ∧ 0 ≤ D (Fin.last m) := by
  constructor
  · rintro ⟨hb, ha⟩
    exact ⟨(hb 0).2, ha, (hb (Fin.last m)).1⟩
  · rintro ⟨hfirst, ha, hlast⟩
    exact ⟨fun i => ⟨hlast.trans (ha (Fin.le_last i)),
      (ha (Fin.zero_le i)).trans hfirst⟩, ha⟩

private theorem state_nonneg {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (i : Fin k) : 0 ≤ R.stateMatrix i :=
  map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (R.state i).2.1

private theorem state_trace {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (i : Fin k) : (R.stateMatrix i).trace = 1 :=
  (R.state i).2.2

private theorem trace_prepared {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (t : ℝ) :
    (R.preparedOverlap t).trace.re = ∑ i, min (R.p i) (t * R.q i) := by
  simp only [ReverseTest.preparedOverlap, Matrix.trace_sum, Matrix.trace_smul,
    state_trace, Complex.real_smul, mul_one, Complex.re_sum, Complex.ofReal_re]

private theorem gap_eq_overlap_trace {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (t : PositiveThreshold) :
    gap R t = overlapValue A ((t : ℝ) • B) - (R.preparedOverlap t).trace.re := by
  have hscalar (p q : ℝ) : max (p - q) 0 = p - min p q := by
    rcases le_total p q with h | h
    · simp only [min_eq_left h, max_eq_right (sub_nonpos.mpr h), sub_self]
    · simp only [min_eq_right h, max_eq_left (sub_nonneg.mpr h)]
  unfold gap maximalHockey ReverseTest.hockey
  simp_rw [hscalar]
  rw [Finset.sum_sub_distrib, ← left_mass R, ← trace_prepared R t]
  ring

private theorem prepared_zero {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) : R.preparedOverlap 0 = 0 := by
  simp only [ReverseTest.preparedOverlap, zero_mul,
    min_eq_right (R.p_nonneg _), zero_smul, Finset.sum_const_zero]

/-! Scalar secants of min(p,tq) and their prepared matrix counterparts. -/

private theorem min_secant_bounds (p q s t : ℝ) (hq : 0 ≤ q) (hst : s < t) :
    0 ≤ (min p (t * q) - min p (s * q)) / (t - s) ∧
      (min p (t * q) - min p (s * q)) / (t - s) ≤ q := by
  have hmul : s * q ≤ t * q := mul_le_mul_of_nonneg_right hst.le hq
  have hmono : min p (s * q) ≤ min p (t * q) := min_le_min_left p hmul
  refine ⟨div_nonneg (sub_nonneg.mpr hmono) (sub_pos.mpr hst).le, ?_⟩
  apply (div_le_iff₀ (sub_pos.mpr hst)).2
  rcases le_total p (s * q) with hps | hsp
  · rw [min_eq_left hps, min_eq_left (hps.trans hmul)]
    nlinarith
  · rw [min_eq_right hsp]
    have h := min_le_right p (t * q)
    nlinarith

private theorem min_secant_adjacent (p q r s t : ℝ) (hq : 0 ≤ q)
    (hrs : r < s) (hst : s < t) :
    (min p (t * q) - min p (s * q)) / (t - s) ≤
      (min p (s * q) - min p (r * q)) / (s - r) := by
  have hrsq : r * q ≤ s * q := mul_le_mul_of_nonneg_right hrs.le hq
  have hstq : s * q ≤ t * q := mul_le_mul_of_nonneg_right hst.le hq
  rcases le_total p (s * q) with hps | hsp
  · have hafter : (min p (t * q) - min p (s * q)) / (t - s) = 0 := by
      rw [min_eq_left hps, min_eq_left (hps.trans hstq), sub_self, zero_div]
    rw [hafter]
    exact (min_secant_bounds p q r s hq hrs).1
  · have hbefore : (min p (s * q) - min p (r * q)) / (s - r) = q := by
      rw [min_eq_right hsp, min_eq_right (hrsq.trans hsp)]
      apply (div_eq_iff (ne_of_gt (sub_pos.mpr hrs))).2
      ring
    rw [hbefore]
    exact (min_secant_bounds p q s t hq hst).2

private theorem min_secant_separated (p q r s t v : ℝ) (hq : 0 ≤ q)
    (hrs : r < s) (hst : s ≤ t) (htv : t < v) :
    (min p (v * q) - min p (t * q)) / (v - t) ≤
      (min p (s * q) - min p (r * q)) / (s - r) := by
  rcases hst.eq_or_lt with he | hlt
  · subst t
    exact min_secant_adjacent p q r s v hq hrs htv
  · exact (min_secant_adjacent p q s t v hq hlt htv).trans
      (min_secant_adjacent p q r s t hq hrs hlt)

private theorem prepared_secant_eq {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (s t : ℝ) :
    secant R.preparedOverlap s t =
      ∑ i, ((min (R.p i) (t * R.q i) - min (R.p i) (s * R.q i)) / (t - s)) •
        R.stateMatrix i := by
  unfold secant ReverseTest.preparedOverlap
  rw [← Finset.sum_sub_distrib, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← sub_smul, smul_smul, div_eq_mul_inv, mul_comm]

theorem prepared_secant_bounds {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (s t : ℝ) (hst : s < t) :
    0 ≤ secant R.preparedOverlap s t ∧ secant R.preparedOverlap s t ≤ B := by
  rw [prepared_secant_eq]
  refine ⟨Finset.sum_nonneg (fun i _ =>
    smul_nonneg (min_secant_bounds (R.p i) (R.q i) s t (R.q_nonneg i) hst).1
      (state_nonneg R i)), ?_⟩
  conv_rhs => rw [← R.prepares_right]
  change (∑ i, _ • R.stateMatrix i) ≤ ∑ i, R.q i • R.stateMatrix i
  exact Finset.sum_le_sum (fun i _ => smul_le_smul_of_nonneg_right
    (min_secant_bounds (R.p i) (R.q i) s t (R.q_nonneg i) hst).2 (state_nonneg R i))

theorem prepared_secant_antitone {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (r s t v : ℝ)
    (hrs : r < s) (hst : s ≤ t) (htv : t < v) :
    secant R.preparedOverlap t v ≤ secant R.preparedOverlap r s := by
  rw [prepared_secant_eq, prepared_secant_eq]
  exact Finset.sum_le_sum (fun i _ => smul_le_smul_of_nonneg_right
    (min_secant_separated (R.p i) (R.q i) r s t v (R.q_nonneg i) hrs hst htv)
    (state_nonneg R i))

private theorem positiveOverlaps_isCompact (A B : Matrix n n ℂ) :
    IsCompact (positiveOverlaps A B) := by
  have hc : IsClosed (positiveOverlaps A B) :=
    (isClosed_le continuous_const continuous_id).inter
      ((isClosed_le continuous_id continuous_const).inter
        (isClosed_le continuous_id continuous_const))
  apply (isCompact_closedBall (0 : Matrix n n ℂ) ‖A‖).of_isClosed_subset hc
  intro X hX
  rw [Metric.mem_closedBall, dist_zero_right]
  exact CStarAlgebra.norm_le_norm_of_le_of_nonneg hX.2.1 hX.1

/-! This compactness argument is finite-dimensional matrix compactness only.
It allows varying source cardinalities and takes no limit of source maps. -/

private theorem tendsto_optimizer_of_trace
    (A B X : Matrix n n ℂ) (hX : X ∈ positiveOverlaps A B)
    (hXt : X.trace.re = overlapValue A B) (Y : ℕ → Matrix n n ℂ)
    (hY : ∀ j, Y j ∈ positiveOverlaps A B)
    (htrace : Tendsto (fun j => (Y j).trace.re) atTop (𝓝 (overlapValue A B))) :
    Tendsto Y atTop (𝓝 X) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  by_contra hbad
  have hfar : ∀ N, ∃ j, N ≤ j ∧ ε ≤ dist (Y j) X := by
    intro N
    by_contra hN
    push_neg at hN
    exact hbad ⟨N, hN⟩
  choose j hjlarge hjfar using hfar
  have hjtop : Tendsto j atTop atTop := by
    apply tendsto_atTop.2
    intro N
    exact eventually_atTop.2 ⟨N, fun k hk => hk.trans (hjlarge k)⟩
  obtain ⟨Z, hZ, φ, hφ, hconv⟩ := (positiveOverlaps_isCompact A B).tendsto_subseq
    (fun k => hY (j k))
  have hZtr : Z.trace.re = overlapValue A B :=
    tendsto_nhds_unique (continuous_trace_re.tendsto Z |>.comp hconv)
      (htrace.comp (hjtop.comp hφ.tendsto_atTop))
  have hZX : Z = X := positive_overlap_unique A B Z X hZ hX hZtr hXt
  rw [hZX] at hconv
  have hnear : ∀ᶠ k in atTop, dist (Y (j (φ k))) X < ε :=
    (Metric.tendsto_atTop.1 hconv) ε hε |> eventually_atTop.2
  obtain ⟨k, hk⟩ := hnear.exists
  exact (not_lt_of_ge (hjfar (φ k))) hk

theorem prepared_overlap_tendsto_of_gap
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (tests : ∀ j : ℕ, Σ k : ℕ, ReverseTest A B k)
    (t : PositiveThreshold)
    (hgap : Tendsto (fun j => gap (tests j).2 t) atTop (𝓝 0)) :
    Tendsto (fun j => (tests j).2.preparedOverlap t) atTop
      (𝓝 (optimalOverlap A B hA hB t)) := by
  have hs := optimalOverlap_spec A B hA hB t t.2.le
  apply tendsto_optimizer_of_trace A ((t : ℝ) • B) _ hs.1 hs.2
    (fun j => (tests j).2.preparedOverlap t)
    (fun j => (tests j).2.overlap_feasible t t.2.le)
  have h : Tendsto (fun j => overlapValue A ((t : ℝ) • B) - gap (tests j).2 t)
      atTop (𝓝 (overlapValue A ((t : ℝ) • B) - 0)) := tendsto_const_nhds.sub hgap
  simp_rw [gap_eq_overlap_trace] at h
  simpa only [sub_sub_cancel, sub_zero] using h

/-- Necessity for the ACTUAL original sigma-finite whole-complex-L1
infimum and ACTUAL operational hockey curvature integral. Real finiteness
is used to obtain finite-cost near-minimizers, never an assumed optimizer.
No full-support curvature, trace normalization, invertibility or Nonempty n. -/
theorem original_eq_implies_finiteLoewnerSlopes
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (c : ℝ) (hc : originalL1Value.{u} hf A B = (c : EReal))
    (he : originalL1Value.{u} hf A B = originalHockeyValue.{u} hf A B) :
    FiniteLoewnerSlopes A B hA hB (curvature hf).support := by
  have hbridge : originalL1Value.{u} hf A B = maximalValue hf A B :=
    (originalL1Value_eq_allL1Value hf A B).trans (allL1Value_eq_maximalValue hf A B)
  have hm : maximalValue hf A B = (c : EReal) := hbridge.symm.trans hc
  have he' : maximalValue hf A B = hockeyValue hf A B :=
    hbridge.symm.trans (he.trans (hockeyValue_eq_original_operational hf A B hA hB).1.symm)
  have hH : hockeyValue hf A B = (c : EReal) := he'.symm.trans hm
  obtain ⟨tests, htests⟩ := approximate_finite_tests hf A B c hm
  have hcost (j : ℕ) : finiteCost hf (tests j).2 ≠ ⊤ := ne_top_of_lt (htests j)
  have hg (j : ℕ) := finite_cost_gap hf (tests j).2 hA hB (hcost j)
  have hgaplim : Tendsto (fun j => ∫ t, gap (tests j).2 t ∂curvature hf)
      atTop (𝓝 0) := by
    apply squeeze_zero (g := fun j : ℕ => 1 / ((j : ℝ) + 1))
    · intro j
      exact integral_nonneg (fun t => ((actual_gap_profile_data (tests j).2 hA hB).1 t).1)
    · intro j
      have h := htests j
      rw [(hg j).2, hH, ← EReal.coe_add, EReal.coe_lt_coe_iff] at h
      change c + (∫ t, gap (tests j).2 t ∂curvature hf) <
        c + 1 / ((j : ℝ) + 1) at h
      linarith
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
  letI : IsLocallyFiniteMeasure (curvature hf : Measure PositiveThreshold) :=
    curvature_locallyFinite hf
  have hpoint (t : PositiveThreshold) (ht : t ∈ (curvature hf).support) :
      Tendsto (fun j => gap (tests j).2 t) atTop (𝓝 0) := by
    apply tendsto_zero_at_support_of_integral (curvature hf) (2 * B.trace.re)
      (by have := (Complex.nonneg_iff.mp hB.trace_nonneg).1; linarith)
      (fun j => gap (tests j).2)
      (fun j t => ((actual_gap_profile_data (tests j).2 hA hB).1 t).1)
      (fun j => (actual_gap_profile_data (tests j).2 hA hB).2)
      (fun j => (hg j).1) hgaplim t ht
  intro m t ht0 htmono htsupport
  dsimp only
  have hYlim (i : Fin (m + 1)) :
      Tendsto (fun j => (tests j).2.preparedOverlap (t i)) atTop
        (𝓝 (optimalOverlap A B hA hB (t i))) := by
    by_cases hi : i = 0
    · subst i
      simp only [ht0, prepared_zero, optimalOverlap_zero]
      exact tendsto_const_nhds
    · have hpos : 0 < t i := by
        have hii : (0 : Fin (m + 1)) < i := by omega
        simpa only [ht0] using htmono hii
      exact prepared_overlap_tendsto_of_gap A B hA hB tests ⟨t i, hpos⟩
        (hpoint ⟨t i, hpos⟩ (htsupport i hpos))
  have hDlim (i : Fin m) :
      Tendsto (fun j => secant (tests j).2.preparedOverlap (t i.castSucc) (t i.succ))
        atTop (𝓝 (secant (optimalOverlap A B hA hB) (t i.castSucc) (t i.succ))) :=
    ((hYlim i.succ).sub (hYlim i.castSucc)).const_smul _
  constructor
  · intro i
    have hst : t i.castSucc < t i.succ := htmono i.castSucc_lt_succ
    exact ⟨le_of_tendsto_of_tendsto tendsto_const_nhds (hDlim i)
        (Eventually.of_forall (fun j => (prepared_secant_bounds (tests j).2 _ _ hst).1)),
      le_of_tendsto_of_tendsto (hDlim i) tendsto_const_nhds
        (Eventually.of_forall (fun j => (prepared_secant_bounds (tests j).2 _ _ hst).2))⟩
  · intro i j hij
    rcases eq_or_lt_of_le hij with heq | hlt
    · subst j
      exact le_rfl
    · have hmid : t i.succ ≤ t j.castSucc := htmono.monotone (by
        change i.val + 1 ≤ j.val
        exact hlt)
      exact le_of_tendsto_of_tendsto (hDlim j) (hDlim i)
        (Eventually.of_forall (fun k => prepared_secant_antitone (tests k).2
          _ _ _ _ (htmono i.castSucc_lt_succ) hmid (htmono j.castSucc_lt_succ)))

/-! Finite interpolation: summation by parts and the existing actual weighted
component preparation. There is no presumed general-f reverse optimizer. -/

private theorem sum_successor_sub {V : Type*} [AddCommGroup V]
    {m : ℕ} (F : Fin (m + 1) → V) :
    (∑ i : Fin m, (F i.succ - F i.castSucc)) = F (Fin.last m) - F 0 := by
  have hfront : (∑ i : Fin m, F i.castSucc) = (∑ i, F i) - F (Fin.last m) :=
    eq_sub_iff_add_eq.mpr (Fin.sum_univ_castSucc F).symm
  have htail : (∑ i : Fin m, F i.succ) = (∑ i, F i) - F 0 := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using (Fin.sum_univ_succ F).symm
  rw [Finset.sum_sub_distrib, hfront, htail]
  abel

private theorem finite_summation_by_parts {m : ℕ}
    (w : Fin (m + 1) → ℝ) (d : Fin (m + 1) → Matrix n n ℂ) :
    (∑ i : Fin m, w i.succ • (d i.castSucc - d i.succ)) =
      (∑ i : Fin m, (w i.succ - w i.castSucc) • d i.castSucc) -
        (w (Fin.last m) • d (Fin.last m) - w 0 • d 0) := by
  have hterm (i : Fin m) :
      w i.succ • (d i.castSucc - d i.succ) =
        (w i.succ - w i.castSucc) • d i.castSucc -
          (w i.succ • d i.succ - w i.castSucc • d i.castSucc) := by module
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, sum_successor_sub]

private theorem sum_clipped_differences {m : ℕ}
    (X : Fin (m + 1) → Matrix n n ℂ) (j : Fin (m + 1)) :
    (∑ i : Fin m, if i.castSucc < j then X i.succ - X i.castSucc else 0) =
      X j - X 0 := by
  have hterm (i : Fin m) :
      X (min i.succ j) - X (min i.castSucc j) =
        if i.castSucc < j then X i.succ - X i.castSucc else 0 := by
    by_cases hi : i.castSucc < j
    · have hs : i.succ ≤ j := by change i.val + 1 ≤ j.val; exact hi
      simp only [hi, ↓reduceIte, min_eq_left hi.le, min_eq_left hs]
    · have hp : j ≤ i.castSucc := le_of_not_gt hi
      have hs : j ≤ i.succ := hp.trans i.castSucc_le_succ
      simp only [hi, ↓reduceIte, min_eq_right hp, min_eq_right hs, sub_self]
  have h := sum_successor_sub (fun i => X (min i j))
  simp_rw [hterm] at h
  simpa only [min_eq_right (Fin.le_last j), min_eq_left (Fin.zero_le j)] using h

private theorem hockey_eq_trace_sub {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (s : ℝ) :
    R.hockey s = A.trace.re - (R.preparedOverlap s).trace.re := by
  unfold ReverseTest.hockey
  rw [trace_prepared, left_mass R, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases le_total (R.p i) (s * R.q i) with h | h
  · simp only [min_eq_left h, max_eq_right (sub_nonpos.mpr h), sub_self]
  · simp only [min_eq_right h, max_eq_left (sub_nonneg.mpr h)]

/-- The explicit manuscript blocks realize ANY finite compatible tuple of
actual PSD optima. All assumptions concern finite matrix secants, not existence
of a desired reverse test. The alphabet is empty when the matrix carrier is
empty. Zero components otherwise use the existing coordinate-state convention. -/
theorem finite_test_interpolating_slopes
    (A B : Matrix n n ℂ) {m : ℕ} (t : Fin (m + 1) → ℝ)
    (ht0 : t 0 = 0) (htmono : StrictMono t)
    (X d : Fin (m + 1) → Matrix n n ℂ) (hX0 : X 0 = 0)
    (hX : ∀ j, X j ∈ positiveOverlaps A (t j • B) ∧
      (X j).trace.re = overlapValue A (t j • B))
    (hdlast : d (Fin.last m) = 0) (hdanti : Antitone d) (hdB : d 0 ≤ B)
    (hstep : ∀ i : Fin m,
      (t i.succ - t i.castSucc) • d i.castSucc = X i.succ - X i.castSucc) :
    ∃ k : ℕ, ∃ R : ReverseTest A B k, ∀ j, R.preparedOverlap (t j) = X j := by
  classical
  let G : Fin m → Matrix n n ℂ := fun i => d i.castSucc - d i.succ
  have hG (i : Fin m) : (G i).PosSemidef :=
    (sub_nonneg.mpr (hdanti i.castSucc_le_succ)).posSemidef
  have hGsum : ∑ i, G i = d 0 := by
    calc
      _ = -(∑ i : Fin m, (d i.succ - d i.castSucc)) := by
        rw [← Finset.sum_neg_distrib]
        simp only [G, neg_sub]
      _ = d 0 := by rw [sum_successor_sub, hdlast, zero_sub, neg_neg]
  have hGmoment : ∑ i, t i.succ • G i = X (Fin.last m) := by
    rw [show (∑ i, t i.succ • G i) =
      (∑ i, (t i.succ - t i.castSucc) • d i.castSucc) -
        (t (Fin.last m) • d (Fin.last m) - t 0 • d 0) from
      finite_summation_by_parts t d]
    simp_rw [hstep]
    rw [hdlast, ht0, smul_zero, zero_smul, sub_self, sub_zero,
      sum_successor_sub, hX0, sub_zero]
  have hprofile (j : Fin (m + 1)) :
      (∑ i : Fin m, min (t j) (t i.succ) • G i) = X j := by
    have hnonneg : 0 ≤ t j := by
      simpa only [ht0] using htmono.monotone (Fin.zero_le j)
    have hsum := finite_summation_by_parts (fun i => min (t j) (t i)) d
    have hw0 : min (t j) (t 0) = 0 := by rw [ht0, min_eq_right hnonneg]
    have hterm (i : Fin m) :
        (min (t j) (t i.succ) - min (t j) (t i.castSucc)) • d i.castSucc =
          if i.castSucc < j then X i.succ - X i.castSucc else 0 := by
      by_cases hi : i.castSucc < j
      · have hs : i.succ ≤ j := by change i.val + 1 ≤ j.val; exact hi
        rw [min_eq_right (htmono.monotone hs), min_eq_right (htmono hi).le,
          hstep, if_pos hi]
      · have hp : j ≤ i.castSucc := le_of_not_gt hi
        have hs : j ≤ i.succ := hp.trans i.castSucc_le_succ
        rw [min_eq_left (htmono.monotone hs), min_eq_left (htmono.monotone hp),
          sub_self, zero_smul, if_neg hi]
    change (∑ i, min (t j) (t i.succ) • (d i.castSucc - d i.succ)) = X j
    rw [hsum, hdlast, hw0, smul_zero, zero_smul, sub_self, sub_zero]
    simp_rw [hterm]
    rw [sum_clipped_differences, hX0, sub_zero]
  by_cases hn : Nonempty n
  · letI : Nonempty n := hn
    let l := Bool ⊕ Fin m
    let W : l → Matrix n n ℂ := fun z => match z with
      | .inl false => B - d 0
      | .inl true => A - X (Fin.last m)
      | .inr i => G i
    let a : l → ℝ := fun z => match z with
      | .inl false => 0
      | .inl true => 1
      | .inr i => t i.succ
    let b : l → ℝ := fun z => match z with
      | .inl false => 1
      | .inl true => 0
      | .inr _ => 1
    have hW (z : l) : (W z).PosSemidef := by
      rcases z with z | i
      · cases z
        · exact (sub_nonneg.mpr hdB).posSemidef
        · exact (sub_nonneg.mpr (hX (Fin.last m)).1.2.1).posSemidef
      · exact hG i
    have ha (z : l) : 0 ≤ a z := by
      rcases z with z | i
      · cases z <;> norm_num [a]
      · have h := htmono.monotone (Fin.zero_le i.succ)
        simpa only [a, ht0] using h
    have hb (z : l) : 0 ≤ b z := by
      rcases z with z | i
      · cases z <;> norm_num [b]
      · norm_num [b]
    have hleft : (∑ z, a z • W z) = A := by
      simp only [Fintype.sum_sum_type, Fintype.sum_bool, a, W, zero_smul,
        one_smul, add_zero]
      rw [hGmoment]
      abel
    have hright : (∑ z, b z • W z) = B := by
      simp only [Fintype.sum_sum_type, Fintype.sum_bool, b, W, zero_smul,
        one_smul, zero_add]
      rw [hGsum]
      abel
    obtain ⟨R, hR⟩ :=
      D5.S3.Quantum.Divergence.MaximalHockeyStickComponents.reverse_test_from_weighted_components
        (fun _ : l => Classical.choice hn) W hW a b ha hb
    rw [hleft, hright] at R hR
    have htrA : A.trace.re = ∑ z, a z * (W z).trace.re := by
      rw [← hleft]
      simp only [Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum,
        Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
    have htr (s : ℝ) : (R.preparedOverlap s).trace.re =
        ∑ z, min (a z) (s * b z) * (W z).trace.re := by
      have hh := hockey_eq_trace_sub R s
      rw [hR s, htrA] at hh
      calc
        _ = (∑ z, a z * (W z).trace.re) -
            ∑ z, max (a z - s * b z) 0 * (W z).trace.re := by linarith
        _ = _ := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro z _
          rcases le_total (a z) (s * b z) with h | h
          · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h), zero_mul, sub_zero]
          · rw [min_eq_right h, max_eq_left (sub_nonneg.mpr h)]
            ring
    refine ⟨_, R, ?_⟩
    intro j
    have htj : 0 ≤ t j := by
      simpa only [ht0] using htmono.monotone (Fin.zero_le j)
    have heq : (R.preparedOverlap (t j)).trace.re = (X j).trace.re := by
      rw [htr]
      have hs : (∑ z : l, min (a z) (t j * b z) * (W z).trace.re) =
          (∑ i : Fin m, min (t j) (t i.succ) • G i).trace.re := by
        simp only [Fintype.sum_sum_type, Fintype.sum_bool, a, b, W,
          mul_zero, mul_one, min_eq_left htj, min_eq_right zero_le_one,
          zero_mul, zero_add, Matrix.trace_sum, Matrix.trace_smul,
          Complex.re_sum, Complex.real_smul, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, sub_zero, min_comm]
      rw [hs, hprofile]
    exact positive_overlap_unique A (t j • B) _ _
      (R.overlap_feasible (t j) htj) (hX j).1
      (heq.trans (hX j).2) (hX j).2
  · letI : IsEmpty n := ⟨fun x => hn ⟨x⟩⟩
    let R : ReverseTest A B 0 :=
      { p := fun i => Fin.elim0 i
        q := fun i => Fin.elim0 i
        p_nonneg := fun i => Fin.elim0 i
        q_nonneg := fun i => Fin.elim0 i
        state := fun i => Fin.elim0 i
        prepares_left := by simp only [Finset.univ_eq_empty, Finset.sum_empty]; exact Subsingleton.elim _ _
        prepares_right := by simp only [Finset.univ_eq_empty, Finset.sum_empty]; exact Subsingleton.elim _ _ }
    exact ⟨0, R, fun _ => Subsingleton.elim _ _⟩

/-- Consume the actual finite Loewner criterion to obtain an actual finite
whole-preparation test at every chosen tuple. This discharges the finite
interpolation obligation without assuming common attainment on infinite K. -/
theorem finiteLoewnerSlopes_realizes_knots
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (K : Set PositiveThreshold) (hC : FiniteLoewnerSlopes A B hA hB K)
    (m : ℕ) (t : Fin (m + 1) → ℝ) (ht0 : t 0 = 0) (htmono : StrictMono t)
    (htK : ∀ i (hi : 0 < t i), (⟨t i, hi⟩ : PositiveThreshold) ∈ K) :
    ∃ k : ℕ, ∃ R : ReverseTest A B k,
      ∀ j, R.preparedOverlap (t j) = optimalOverlap A B hA hB (t j) := by
  classical
  let X : Fin (m + 1) → Matrix n n ℂ := fun j => optimalOverlap A B hA hB (t j)
  let D : Fin m → Matrix n n ℂ := fun i =>
    secant (optimalOverlap A B hA hB) (t i.castSucc) (t i.succ)
  obtain ⟨hDbounds, hDanti⟩ := hC m t ht0 htmono htK
  let d : Fin (m + 1) → Matrix n n ℂ := fun j =>
    if hj : j.val < m then D ⟨j.val, hj⟩ else 0
  have hdcast (i : Fin m) : d i.castSucc = D i := by
    simp only [d, Fin.val_castSucc, dif_pos i.isLt]
  have hdlast : d (Fin.last m) = 0 := by simp [d]
  have hdanti : Antitone d := by
    intro i j hij
    by_cases hj : j.val < m
    · have hi : i.val < m := lt_of_le_of_lt hij hj
      simp only [d, dif_pos hi, dif_pos hj]
      exact hDanti (show (⟨i.val, hi⟩ : Fin m) ≤ ⟨j.val, hj⟩ from hij)
    · rw [show d j = 0 by simp only [d, dif_neg hj]]
      by_cases hi : i.val < m
      · simpa only [d, dif_pos hi] using (hDbounds ⟨i.val, hi⟩).1
      · simp only [d, dif_neg hi, le_refl]
  have hdB : d 0 ≤ B := by
    by_cases hm : 0 < m
    · simpa only [d, Fin.val_zero, dif_pos hm] using (hDbounds ⟨0, hm⟩).2
    · simpa only [d, Fin.val_zero, dif_neg hm] using hB.nonneg
  have hstep (i : Fin m) :
      (t i.succ - t i.castSucc) • d i.castSucc = X i.succ - X i.castSucc := by
    rw [hdcast]
    dsimp only [D, secant, X]
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (sub_pos.mpr (htmono i.castSucc_lt_succ))),
      one_smul]
  apply finite_test_interpolating_slopes A B t ht0 htmono X d
    (by dsimp only [X]; rw [ht0, optimalOverlap_zero])
    (fun j => optimalOverlap_spec A B hA hB (t j) (by
      simpa only [ht0] using htmono.monotone (Fin.zero_le j)))
    hdlast hdanti hdB hstep

/-- Eventual exact interpolation on a dense family gives vanishing profiles
on its closure. This is the analytic step needed after exhausting the actual
support by finite knot sets; it requires no measure representation. -/
theorem tendsto_zero_on_closure_of_eventual_interpolation
    {α : Type*} [PseudoMetricSpace α] (K : ℝ) (hK : 0 ≤ K)
    (g : ℕ → α → ℝ) (hg : ∀ j, LipschitzWith (Real.toNNReal K) (g j))
    (q : ℕ → α) (hzero : ∀ k, ∀ᶠ j in atTop, g j (q k) = 0)
    (x : α) (hx : x ∈ closure (Set.range q)) :
    Tendsto (fun j => g j x) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  let δ : ℝ := ε / (2 * (K + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨y, ⟨k, rfl⟩, hy⟩ := Metric.mem_closure_iff.1 hx δ hδ
  have hKδ : K * δ ≤ ε / 2 := by
    have hden : 0 < 2 * (K + 1) := by positivity
    calc
      K * δ = (K * ε) / (2 * (K + 1)) := by dsimp [δ]; ring
      _ ≤ ε / 2 := (div_le_iff₀ hden).2 (by nlinarith)
  have hevent : ∀ᶠ j in atTop, dist (g j x) 0 < ε := by
    filter_upwards [hzero k] with j hj
    have hdist : dist (g j x) (g j (q k)) ≤ K * dist x (q k) := by
      simpa only [Real.coe_toNNReal', max_eq_left hK] using (hg j).dist_le_mul x (q k)
    rw [hj] at hdist
    have hmul : K * dist x (q k) ≤ K * δ :=
      mul_le_mul_of_nonneg_left hy.le hK
    linarith
  exact eventually_atTop.1 hevent

/-! Pointwise tail control for the sufficiency route. The witness may have
zero p or zero q labels: its finite cost is used later only for integrability,
not to exclude those labels. Thus this avoids prematurely assuming finite
endpoint values or a general-f optimizer. -/

private theorem prepared_trace_mono {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (s t : ℝ) (hst : s ≤ t) :
    (R.preparedOverlap s).trace.re ≤ (R.preparedOverlap t).trace.re := by
  rw [trace_prepared, trace_prepared]
  exact Finset.sum_le_sum (fun i _ => min_le_min_left (R.p i)
    (mul_le_mul_of_nonneg_right hst (R.q_nonneg i)))

private theorem prepared_trace_scaled_lower {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (r t : ℝ) (hr : 0 < r) (ht : 0 ≤ t) (htr : t ≤ r) :
    (t / r) * (R.preparedOverlap r).trace.re ≤ (R.preparedOverlap t).trace.re := by
  rw [trace_prepared, trace_prepared, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hα : 0 ≤ t / r := div_nonneg ht hr.le
  have hα1 : t / r ≤ 1 := (div_le_one hr).2 htr
  apply le_min
  · calc
      _ ≤ 1 * min (R.p i) (r * R.q i) :=
        mul_le_mul_of_nonneg_right hα1
          (le_min (R.p_nonneg i) (mul_nonneg hr.le (R.q_nonneg i)))
      _ ≤ R.p i := by rw [one_mul]; exact min_le_left _ _
  · calc
      _ ≤ (t / r) * (r * R.q i) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hα
      _ = t * R.q i := by field_simp; ring

/-- A finite witness is linear below an anchor below all its positive p/q
ratios. Labels p=0 are retained. -/
theorem prepared_trace_lower_tail_linear {A B : Matrix n n ℂ} {k : ℕ}
    (W : ReverseTest A B k) (r t : ℝ) (hr : 0 < r) (ht : 0 ≤ t) (htr : t ≤ r)
    (hratio : ∀ i, W.p i = 0 ∨ r * W.q i ≤ W.p i) :
    (W.preparedOverlap t).trace.re = (t / r) * (W.preparedOverlap r).trace.re := by
  rw [trace_prepared, trace_prepared, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rcases hratio i with hp | hp
  · rw [hp, min_eq_left (mul_nonneg ht (W.q_nonneg i)),
      min_eq_left (mul_nonneg hr.le (W.q_nonneg i)), mul_zero]
  · have htp : t * W.q i ≤ W.p i :=
      (mul_le_mul_of_nonneg_right htr (W.q_nonneg i)).trans hp
    rw [min_eq_right htp, min_eq_right hp]
    field_simp

/-- A finite witness is constant above an anchor above all its finite p/q
ratios. Labels q=0 are retained. -/
theorem prepared_trace_upper_tail_constant {A B : Matrix n n ℂ} {k : ℕ}
    (W : ReverseTest A B k) (r t : ℝ) (hrt : r ≤ t)
    (hratio : ∀ i, W.q i = 0 ∨ W.p i ≤ r * W.q i) :
    (W.preparedOverlap t).trace.re = (W.preparedOverlap r).trace.re := by
  rw [trace_prepared, trace_prepared]
  apply Finset.sum_congr rfl
  intro i _
  rcases hratio i with hq | hp
  · simp only [hq, mul_zero]
  · rw [min_eq_left hp,
      min_eq_left (hp.trans (mul_le_mul_of_nonneg_right hrt (W.q_nonneg i)))]

/-- Matching a lower-tail optimal trace makes the entire negative hinge
tail no larger than that of a fixed witness. This is pointwise, so it also
covers infinite endpoint values before any integration is performed. -/
theorem lower_hinge_tail_dominated {A B : Matrix n n ℂ} {k l : ℕ}
    (W : ReverseTest A B k) (R : ReverseTest A B l)
    (r t : ℝ) (hr : 0 < r) (ht : 0 ≤ t) (htr : t ≤ r)
    (hratio : ∀ i, W.p i = 0 ∨ r * W.q i ≤ W.p i)
    (hanchor : (W.preparedOverlap r).trace.re ≤ (R.preparedOverlap r).trace.re) :
    t * B.trace.re - (R.preparedOverlap t).trace.re ≤
      t * B.trace.re - (W.preparedOverlap t).trace.re := by
  apply sub_le_sub_left
  calc
    _ = (t / r) * (W.preparedOverlap r).trace.re :=
      prepared_trace_lower_tail_linear W r t hr ht htr hratio
    _ ≤ (t / r) * (R.preparedOverlap r).trace.re :=
      mul_le_mul_of_nonneg_left hanchor (div_nonneg ht hr.le)
    _ ≤ (R.preparedOverlap t).trace.re := prepared_trace_scaled_lower R r t hr ht htr

/-- The analogous control of the positive hinge tail, keeping q=0 labels. -/
theorem upper_hinge_tail_dominated {A B : Matrix n n ℂ} {k l : ℕ}
    (W : ReverseTest A B k) (R : ReverseTest A B l)
    (r t : ℝ) (hrt : r ≤ t)
    (hratio : ∀ i, W.q i = 0 ∨ W.p i ≤ r * W.q i)
    (hanchor : (W.preparedOverlap r).trace.re ≤ (R.preparedOverlap r).trace.re) :
    A.trace.re - (R.preparedOverlap t).trace.re ≤
      A.trace.re - (W.preparedOverlap t).trace.re := by
  apply sub_le_sub_left
  calc
    _ = (W.preparedOverlap r).trace.re := prepared_trace_upper_tail_constant W r t hrt hratio
    _ ≤ (R.preparedOverlap r).trace.re := hanchor
    _ ≤ (R.preparedOverlap t).trace.re := prepared_trace_mono R r t hrt

/-! Sufficiency. The next scalar facts unfold the *existing* test kernel;
the cost representation itself is reused, not redefined. In particular all
measurability statements use the negative branch at t = 1. -/

private theorem actual_test_kernel_nonneg {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (t : PositiveThreshold) : 0 ≤ testKernel R t := by
  apply Finset.sum_nonneg
  intro i _
  unfold hinge
  split_ifs <;> exact le_max_right _ _

private theorem actual_test_kernel_measurable {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) : Measurable (testKernel R) := by
  change Measurable (fun t : PositiveThreshold => ∑ i,
    if (t : ℝ) ≤ 1 then max ((t : ℝ) * R.q i - R.p i) 0
      else max (R.p i - (t : ℝ) * R.q i) 0)
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (measurableSet_le measurable_subtype_coe measurable_const)
    (((measurable_subtype_coe.mul_const (R.q i)).sub_const (R.p i)).max measurable_const)
    ((measurable_const.sub (measurable_subtype_coe.mul_const (R.q i))).max measurable_const)

private theorem actual_test_kernel_trace {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (t : PositiveThreshold) :
    testKernel R t = if (t : ℝ) ≤ 1 then
      (t : ℝ) * B.trace.re - (R.preparedOverlap t).trace.re
      else A.trace.re - (R.preparedOverlap t).trace.re := by
  change (∑ i, if (t : ℝ) ≤ 1 then max ((t : ℝ) * R.q i - R.p i) 0
      else max (R.p i - (t : ℝ) * R.q i) 0) = _
  split_ifs with ht
  · simp only [if_pos ht]
    rw [trace_prepared, right_mass R, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rcases le_total (R.p i) ((t : ℝ) * R.q i) with h | h
    · rw [min_eq_left h, max_eq_left (sub_nonneg.mpr h)]
    · rw [min_eq_right h, sub_self, max_eq_right (sub_nonpos.mpr h)]
  · simp only [if_neg ht]
    exact hockey_eq_trace_sub R t

private theorem actual_kernel_gap {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (t : PositiveThreshold) :
    testKernel R t = maximalKernel A B t + gap R t := by
  rw [actual_test_kernel_trace, gap_eq_overlap_trace]
  change (if (t : ℝ) ≤ 1 then
      (t : ℝ) * B.trace.re - (R.preparedOverlap t).trace.re
      else A.trace.re - (R.preparedOverlap t).trace.re) =
    (if (t : ℝ) ≤ 1 then
      (t : ℝ) * B.trace.re - overlapValue A ((t : ℝ) • B)
      else A.trace.re - overlapValue A ((t : ℝ) • B)) +
    (overlapValue A ((t : ℝ) • B) - (R.preparedOverlap t).trace.re)
  split_ifs <;> ring

private theorem actual_maximal_kernel_nonneg
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (t : PositiveThreshold) : 0 ≤ maximalKernel A B t := by
  have hX := optimalOverlap_spec A B hA hB t t.2.le
  have htr := (Complex.nonneg_iff.mp
    (sub_nonneg.mpr hX.1.2.2).posSemidef.trace_nonneg).1
  rw [Matrix.trace_sub, Complex.sub_re, Matrix.trace_smul,
    Complex.real_smul] at htr
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, hX.2] at htr
  unfold maximalKernel
  split_ifs
  · exact htr
  · exact maximal_hockey_nonneg hA hB t.2.le

private theorem actual_hockey_le_maximal
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    hockeyValue hf A B ≤ maximalValue hf A B := by
  apply le_sInf
  rintro _ ⟨k, R, rfl⟩
  rw [finite_cost_decomposition, hockeyValue]
  apply add_le_add le_rfl
  apply EReal.coe_ennreal_le_coe_ennreal_iff.mpr
  apply lintegral_mono
  intro t
  apply ENNReal.ofReal_le_ofReal
  rw [actual_kernel_gap R t]
  exact le_add_of_nonneg_right ((actual_gap_profile_data R hA hB).1 t).1

/-- The actual hockey value is finite because its nonnegative curvature
part lies between a real affine base and the real finite actual infimum. -/
private theorem actual_hockey_real
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (c : ℝ) (hc : maximalValue hf A B = (c : EReal)) :
    ∃ H : ℝ, hockeyValue hf A B = (H : EReal) := by
  have hupper : hockeyValue hf A B ≤ (c : EReal) :=
    (actual_hockey_le_maximal hf A B hA hB).trans_eq hc
  have hlower : (affineMass f A B : EReal) ≤ hockeyValue hf A B := by
    unfold hockeyValue
    apply le_add_of_nonneg_right
    positivity
  have htop : hockeyValue hf A B ≠ ⊤ :=
    ne_top_of_le_ne_top EReal.coe_ne_top hupper
  have hbot : hockeyValue hf A B ≠ ⊥ :=
    ne_bot_of_le_ne_bot EReal.coe_ne_bot hlower
  exact ⟨(hockeyValue hf A B).toReal, (EReal.coe_toReal htop hbot).symm⟩

/-- The original finite closed-perspective representation gives both
directions of this finiteness bridge. The reverse implication is used
BEFORE any invocation of finite_cost_gap on the interpolants. -/
private theorem integrable_test_kernel_iff_finite_cost
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    {A B : Matrix n n ℂ} {k : ℕ} (R : ReverseTest A B k) :
    Integrable (testKernel R) (curvature hf) ↔ finiteCost hf R ≠ ⊤ := by
  have hn : 0 ≤ᵐ[curvature hf] testKernel R :=
    ae_of_all _ (actual_test_kernel_nonneg R)
  constructor
  · intro hi
    have he : finiteCost hf R =
        ((affineMass f A B + ∫ t, testKernel R t ∂curvature hf : ℝ) : EReal) := by
      rw [finite_cost_decomposition,
        ← ofReal_integral_eq_lintegral_ofReal hi hn, EReal.coe_ennreal_ofReal,
        max_eq_left (integral_nonneg_of_ae hn), ← EReal.coe_add]
    rw [he]
    exact EReal.coe_ne_top
  · intro hfin
    have hlin : (∫⁻ t, ENNReal.ofReal (testKernel R t) ∂curvature hf) ≠ ⊤ := by
      intro h
      apply hfin
      rw [finite_cost_decomposition, h, EReal.coe_ennreal_top, EReal.coe_add_top]
    exact ⟨(actual_test_kernel_measurable R).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hn).2 (lt_top_iff_ne_top.mpr hlin)⟩

/-- Finite ratios, with both axes retained. Empty alphabets make the sums
zero, hence give the same positive lower and finite upper cutoffs. -/
private theorem witness_ratio_cutoffs {A B : Matrix n n ℂ} {k : ℕ}
    (W : ReverseTest A B k) :
    ∃ l u : ℝ, 0 < l ∧ l < 1 ∧ 1 < u ∧
      (∀ i, W.p i = 0 ∨ l * W.q i ≤ W.p i) ∧
      (∀ i, W.q i = 0 ∨ W.p i ≤ u * W.q i) := by
  classical
  let S : ℝ := ∑ i, W.q i / W.p i
  let T : ℝ := ∑ i, W.p i / W.q i
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => div_nonneg (W.q_nonneg i) (W.p_nonneg i))
  have hT : 0 ≤ T := Finset.sum_nonneg (fun i _ => div_nonneg (W.p_nonneg i) (W.q_nonneg i))
  let l : ℝ := (S + 2)⁻¹
  let u : ℝ := T + 2
  have hl : 0 < l := inv_pos.mpr (by linarith)
  have hlmul : l * (S + 2) = 1 := inv_mul_cancel₀ (by linarith)
  have hlS : 0 ≤ l * S := mul_nonneg hl.le hS
  have hl1 : l < 1 := by nlinarith
  refine ⟨l, u, hl, hl1, by dsimp [u]; linarith, ?_, ?_⟩
  · intro i
    by_cases hp : W.p i = 0
    · exact Or.inl hp
    · right
      have hp0 : 0 < W.p i := lt_of_le_of_ne (W.p_nonneg i) (Ne.symm hp)
      have hterm : W.q i / W.p i ≤ S :=
        Finset.single_le_sum (fun j _ => div_nonneg (W.q_nonneg j) (W.p_nonneg j))
          (Finset.mem_univ i)
      have hprod : l * (W.q i / W.p i) ≤ 1 := by
        have := mul_le_mul_of_nonneg_left hterm hl.le
        nlinarith
      apply (div_le_one hp0).1
      convert hprod using 1 <;> ring
  · intro i
    by_cases hq : W.q i = 0
    · exact Or.inl hq
    · right
      have hq0 : 0 < W.q i := lt_of_le_of_ne (W.q_nonneg i) (Ne.symm hq)
      have hterm : W.p i / W.q i ≤ T :=
        Finset.single_le_sum (fun j _ => div_nonneg (W.p_nonneg j) (W.q_nonneg j))
          (Finset.mem_univ i)
      apply (div_le_iff₀ hq0).1
      exact hterm.trans (by dsimp [u]; linarith)

/-- Each effective endpoint is either an actual support anchor or the
corresponding open tail contains no support. No positive anchor is invented
when that part of the support is empty. -/
private theorem witness_support_endpoints {A B : Matrix n n ℂ} {k : ℕ}
    (W : ReverseTest A B k) (K : Set PositiveThreshold) :
    ∃ a b : PositiveThreshold, (a : ℝ) < 1 ∧ 1 < (b : ℝ) ∧
      (∀ i, W.p i = 0 ∨ (a : ℝ) * W.q i ≤ W.p i) ∧
      (∀ i, W.q i = 0 ∨ W.p i ≤ (b : ℝ) * W.q i) ∧
      (a ∈ K ∨ ∀ t ∈ K, a ≤ t) ∧ (b ∈ K ∨ ∀ t ∈ K, t ≤ b) := by
  classical
  obtain ⟨l, u, hl0, hl1, hu1, hlratio, huratio⟩ := witness_ratio_cutoffs W
  have hleft : ∃ a : PositiveThreshold, (a : ℝ) < 1 ∧
      (∀ i, W.p i = 0 ∨ (a : ℝ) * W.q i ≤ W.p i) ∧
      (a ∈ K ∨ ∀ t ∈ K, a ≤ t) := by
    by_cases h : ∃ t : PositiveThreshold, t ∈ K ∧ (t : ℝ) < l
    · obtain ⟨a, haK, hal⟩ := h
      refine ⟨a, hal.trans hl1, ?_, Or.inl haK⟩
      intro i
      exact (hlratio i).imp_right (fun hi =>
        (mul_le_mul_of_nonneg_right hal.le (W.q_nonneg i)).trans hi)
    · refine ⟨⟨l, hl0⟩, hl1, hlratio, Or.inr ?_⟩
      intro t ht
      exact le_of_not_gt (fun htl => h ⟨t, ht, htl⟩)
  have hright : ∃ b : PositiveThreshold, 1 < (b : ℝ) ∧
      (∀ i, W.q i = 0 ∨ W.p i ≤ (b : ℝ) * W.q i) ∧
      (b ∈ K ∨ ∀ t ∈ K, t ≤ b) := by
    by_cases h : ∃ t : PositiveThreshold, t ∈ K ∧ u < (t : ℝ)
    · obtain ⟨b, hbK, hub⟩ := h
      refine ⟨b, hu1.trans hub, ?_, Or.inl hbK⟩
      intro i
      exact (huratio i).imp_right (fun hi =>
        hi.trans (mul_le_mul_of_nonneg_right hub.le (W.q_nonneg i)))
    · refine ⟨⟨u, lt_trans (by norm_num) hu1⟩, hu1, huratio, Or.inr ?_⟩
      intro t ht
      exact le_of_not_gt (fun hut => h ⟨t, ht, hut⟩)
  obtain ⟨a, ha1, haratio, haK⟩ := hleft
  obtain ⟨b, hb1, hbratio, hbK⟩ := hright
  exact ⟨a, b, ha1, hb1, haratio, hbratio, haK, hbK⟩

/-- Sort the distinct real knots after inserting virtual zero. This also
works for S = empty: the tuple then has length one and no secants. -/
private theorem realizes_finite_set
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (K : Set PositiveThreshold) (hC : FiniteLoewnerSlopes A B hA hB K)
    (S : Finset PositiveThreshold) (hSK : ∀ t ∈ S, t ∈ K) :
    ∃ k : ℕ, ∃ R : ReverseTest A B k,
      ∀ t ∈ S, R.preparedOverlap t = optimalOverlap A B hA hB t := by
  classical
  let P : Finset ℝ := S.image (fun t => (t : ℝ))
  let T : Finset ℝ := insert 0 P
  have hzero : (0 : ℝ) ∉ P := by
    rintro hz
    obtain ⟨x, hx, hx0⟩ := Finset.mem_image.1 hz
    exact (ne_of_gt x.2) hx0
  have hcard : T.card = P.card + 1 := Finset.card_insert_of_notMem hzero
  let t : Fin (P.card + 1) ↪o ℝ := T.orderEmbOfFin hcard
  have htmem (i : Fin (P.card + 1)) : t i ∈ T := T.orderEmbOfFin_mem hcard i
  have htrange : Set.range t = (T : Set ℝ) := T.range_orderEmbOfFin hcard
  have hnonneg (i : Fin (P.card + 1)) : 0 ≤ t i := by
    rcases Finset.mem_insert.1 (htmem i) with hi | hi
    · rw [hi]
    · obtain ⟨s, hs, hsi⟩ := Finset.mem_image.1 hi
      exact hsi ▸ s.2.le
  have ht0 : t 0 = 0 := by
    have hz : (0 : ℝ) ∈ Set.range t := by rw [htrange]; exact Finset.mem_insert_self _ _
    obtain ⟨i, hi⟩ := hz
    exact le_antisymm (by simpa only [hi] using t.monotone (Fin.zero_le i)) (hnonneg 0)
  have htK (i : Fin (P.card + 1)) (hi : 0 < t i) :
      (⟨t i, hi⟩ : PositiveThreshold) ∈ K := by
    rcases Finset.mem_insert.1 (htmem i) with hz | hp
    · exact False.elim ((ne_of_gt hi) hz)
    · obtain ⟨s, hs, hsi⟩ := Finset.mem_image.1 hp
      have he : (⟨t i, hi⟩ : PositiveThreshold) = s := Subtype.ext hsi.symm
      rw [he]
      exact hSK s hs
  obtain ⟨k, R, hR⟩ := finiteLoewnerSlopes_realizes_knots A B hA hB K hC
    P.card t ht0 t.strictMono htK
  refine ⟨k, R, ?_⟩
  intro s hs
  have hsrange : (s : ℝ) ∈ Set.range t := by
    rw [htrange]
    exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨s, hs, rfl⟩)
  obtain ⟨i, hi⟩ := hsrange
  simpa only [hi] using hR i

/-- Every fixed support anchor occurs at every stage, and every dense knot
occurs permanently from its own index onwards. Alphabets may vary with j. -/
private theorem finite_knot_exhaustion
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (K : Set PositiveThreshold) (hC : FiniteLoewnerSlopes A B hA hB K)
    (F : Finset PositiveThreshold) (hFK : ∀ t ∈ F, t ∈ K)
    (q : ℕ → PositiveThreshold) (hqK : ∀ i, q i ∈ K) :
    ∃ tests : ∀ j : ℕ, Σ k : ℕ, ReverseTest A B k,
      (∀ j t, t ∈ F → (tests j).2.preparedOverlap t = optimalOverlap A B hA hB t) ∧
      (∀ i j, i ≤ j → (tests j).2.preparedOverlap (q i) =
        optimalOverlap A B hA hB (q i)) := by
  classical
  let S (j : ℕ) : Finset PositiveThreshold := F ∪ (Finset.range (j + 1)).image q
  have hSK (j : ℕ) : ∀ t ∈ S j, t ∈ K := by
    intro t ht
    rcases Finset.mem_union.1 ht with ht | ht
    · exact hFK t ht
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ht
      exact hqK i
  have hex (j : ℕ) := realizes_finite_set A B hA hB K hC (S j) (hSK j)
  choose k R hR using hex
  refine ⟨fun j => ⟨k j, R j⟩, ?_, ?_⟩
  · intro j t ht
    exact hR j t (Finset.mem_union_left _ ht)
  · intro i j hij
    apply hR j (q i)
    exact Finset.mem_union_right _
      (Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), rfl⟩)

private theorem prepared_trace_nonneg {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (t : PositiveThreshold) :
    0 ≤ (R.preparedOverlap t).trace.re := by
  rw [trace_prepared]
  exact Finset.sum_nonneg (fun i _ =>
    le_min (R.p_nonneg i) (mul_nonneg t.2.le (R.q_nonneg i)))

private theorem test_kernel_middle_bound {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (b t : PositiveThreshold) (htb : t ≤ b) :
    testKernel R t ≤ A.trace.re + (b : ℝ) * B.trace.re := by
  have hAtr := (Complex.nonneg_iff.mp hA.trace_nonneg).1
  have hBtr := (Complex.nonneg_iff.mp hB.trace_nonneg).1
  have htr := prepared_trace_nonneg R t
  rw [actual_test_kernel_trace]
  split_ifs
  · have htb' : (t : ℝ) ≤ (b : ℝ) := htb
    have hmul := mul_le_mul_of_nonneg_right htb' hBtr
    linarith
  · have hmul := mul_nonneg b.2.le hBtr
    linarith

private theorem anchor_trace_dominates {A B : Matrix n n ℂ} {k l : ℕ}
    (W : ReverseTest A B k) (R : ReverseTest A B l)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (t : PositiveThreshold)
    (hRt : R.preparedOverlap t = optimalOverlap A B hA hB t) :
    (W.preparedOverlap t).trace.re ≤ (R.preparedOverlap t).trace.re := by
  rw [hRt, (optimalOverlap_spec A B hA hB t t.2.le).2]
  exact feasible_le_value (W.overlap_feasible t t.2.le)

/-- Compactness is inside the positive threshold space. In particular the
lower endpoint remains strictly positive even when K accumulates at zero. -/
private theorem compact_threshold_interval (a b : PositiveThreshold) :
    IsCompact (Icc a b : Set PositiveThreshold) := by
  rw [Subtype.isCompact_iff]
  have he : (Subtype.val '' (Icc a b : Set PositiveThreshold) : Set ℝ) =
      Icc (a : ℝ) (b : ℝ) := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht
    · intro hx
      exact ⟨⟨x, lt_of_lt_of_le a.2 hx.1⟩, hx, rfl⟩
  rw [he]
  exact isCompact_Icc

/-- One explicit integrable envelope for the *test kernels*, not just the
gaps. Thus it also proves the finite actual costs needed by the gap formula.
Outside [a,b] the witness dominates at every point of the actual support;
absent-anchor tails are discarded only via conull support. -/
private theorem witness_dominated_kernels
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    {k : ℕ} (W : ReverseTest A B k) (hW : Integrable (testKernel W) (curvature hf))
    (a b : PositiveThreshold) (ha1 : (a : ℝ) < 1) (hb1 : 1 < (b : ℝ))
    (haratio : ∀ i, W.p i = 0 ∨ (a : ℝ) * W.q i ≤ W.p i)
    (hbratio : ∀ i, W.q i = 0 ∨ W.p i ≤ (b : ℝ) * W.q i)
    (haleft : a ∈ (curvature hf).support ∨ ∀ t ∈ (curvature hf).support, a ≤ t)
    (hbright : b ∈ (curvature hf).support ∨ ∀ t ∈ (curvature hf).support, t ≤ b)
    (tests : ∀ j : ℕ, Σ l : ℕ, ReverseTest A B l)
    (hRa : a ∈ (curvature hf).support → ∀ j,
      (tests j).2.preparedOverlap a = optimalOverlap A B hA hB a)
    (hRb : b ∈ (curvature hf).support → ∀ j,
      (tests j).2.preparedOverlap b = optimalOverlap A B hA hB b) :
    ∃ E : PositiveThreshold → ℝ, Integrable E (curvature hf) ∧
      (∀ t, 0 ≤ E t) ∧
      (∀ j, ∀ᵐ t ∂curvature hf, ‖testKernel (tests j).2 t‖ ≤ E t) ∧
      (∀ j, ∀ᵐ t ∂curvature hf, ‖gap (tests j).2 t‖ ≤ E t) := by
  classical
  letI : IsLocallyFiniteMeasure (curvature hf : Measure PositiveThreshold) :=
    curvature_locallyFinite hf
  let C : ℝ := A.trace.re + (b : ℝ) * B.trace.re
  have hC : 0 ≤ C := add_nonneg
    (Complex.nonneg_iff.mp hA.trace_nonneg).1
    (mul_nonneg b.2.le (Complex.nonneg_iff.mp hB.trace_nonneg).1)
  let middle : PositiveThreshold → ℝ := (Icc a b).indicator (fun _ => C)
  let E : PositiveThreshold → ℝ := fun t => testKernel W t + middle t
  have hmiddle : Integrable middle (curvature hf) := by
    apply (integrable_indicator_iff measurableSet_Icc).2
    exact integrableOn_const (compact_threshold_interval a b).measure_ne_top
  have hE : Integrable E (curvature hf) := hW.add hmiddle
  have hmiddle0 (t : PositiveThreshold) : 0 ≤ middle t := by
    dsimp [middle]
    exact Set.indicator_nonneg (fun _ _ => hC) t
  have hE0 (t : PositiveThreshold) : 0 ≤ E t :=
    add_nonneg (actual_test_kernel_nonneg W t) (hmiddle0 t)
  have hbound (j : ℕ) : ∀ᵐ t ∂curvature hf, testKernel (tests j).2 t ≤ E t := by
    filter_upwards [Measure.support_mem_ae (μ := curvature hf)] with t htK
    by_cases hta : t < a
    · have haK : a ∈ (curvature hf).support := by
        rcases haleft with h | h
        · exact h
        · exact False.elim (not_lt_of_ge (h t htK) hta)
      have ht1 : (t : ℝ) ≤ 1 := (show (t : ℝ) < (a : ℝ) from hta).le.trans ha1.le
      have htail := lower_hinge_tail_dominated W (tests j).2 a t a.2 t.2.le hta.le
        haratio (anchor_trace_dominates W (tests j).2 hA hB a (hRa haK j))
      have hk : testKernel (tests j).2 t ≤ testKernel W t := by
        simpa only [actual_test_kernel_trace, if_pos ht1] using htail
      exact hk.trans (le_add_of_nonneg_right (hmiddle0 t))
    · by_cases hbt : b < t
      · have hbK : b ∈ (curvature hf).support := by
          rcases hbright with h | h
          · exact h
          · exact False.elim (not_lt_of_ge (h t htK) hbt)
        have ht1 : ¬(t : ℝ) ≤ 1 := not_le.mpr
          (hb1.trans (show (b : ℝ) < (t : ℝ) from hbt))
        have htail := upper_hinge_tail_dominated W (tests j).2 b t hbt.le hbratio
          (anchor_trace_dominates W (tests j).2 hA hB b (hRb hbK j))
        have hk : testKernel (tests j).2 t ≤ testKernel W t := by
          simpa only [actual_test_kernel_trace, if_neg ht1] using htail
        exact hk.trans (le_add_of_nonneg_right (hmiddle0 t))
      · have htm : t ∈ Icc a b := ⟨le_of_not_gt hta, le_of_not_gt hbt⟩
        have hm : middle t = C := Set.indicator_of_mem htm _
        dsimp only [E]
        rw [hm]
        exact (test_kernel_middle_bound (tests j).2 hA hB b t htm.2).trans
          (le_add_of_nonneg_left (actual_test_kernel_nonneg W t))
  refine ⟨E, hE, hE0, ?_, ?_⟩
  · intro j
    filter_upwards [hbound j] with t ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg (actual_test_kernel_nonneg (tests j).2 t)]
      using ht
  · intro j
    filter_upwards [hbound j] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg ((actual_gap_profile_data (tests j).2 hA hB).1 t).1]
    apply le_trans _ ht
    rw [actual_kernel_gap]
    exact le_add_of_nonneg_left (actual_maximal_kernel_nonneg A B hA hB t)

/-- C -> E for the actual finite infimum. This is approximation by finite
knots, not an assertion that one finite test realizes the whole support. -/
private theorem finiteLoewnerSlopes_implies_integrated_eq
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (c : ℝ) (hc : maximalValue hf A B = (c : EReal))
    (hC : FiniteLoewnerSlopes A B hA hB (curvature hf).support) :
    maximalValue hf A B = hockeyValue hf A B := by
  classical
  have hHM := actual_hockey_le_maximal hf A B hA hB
  obtain ⟨H, hH⟩ := actual_hockey_real hf A B hA hB c hc
  obtain ⟨near, hnear⟩ := approximate_finite_tests hf A B c hc
  let W : ReverseTest A B (near 0).1 := (near 0).2
  have hWfin : finiteCost hf W ≠ ⊤ := ne_top_of_lt (hnear 0)
  have hW : Integrable (testKernel W) (curvature hf) :=
    (integrable_test_kernel_iff_finite_cost hf W).2 hWfin
  by_cases hKempty : (curvature hf).support = ∅
  · have hμ : curvature hf = 0 := Measure.support_eq_empty_iff.1 hKempty
    have hg := finite_cost_gap hf W hA hB hWfin
    have hcost : finiteCost hf W = hockeyValue hf A B := by
      simpa only [hμ, integral_zero_measure, EReal.coe_zero, add_zero] using hg.2
    have hMW : maximalValue hf A B ≤ finiteCost hf W := sInf_le ⟨(near 0).1, W, rfl⟩
    exact le_antisymm (hMW.trans_eq hcost) hHM
  · have hKne : (curvature hf).support.Nonempty := Set.nonempty_iff_ne_empty.2 hKempty
    letI : Nonempty (curvature hf).support := hKne.to_subtype
    obtain ⟨qK, hqK⟩ := TopologicalSpace.exists_dense_seq (curvature hf).support
    let q : ℕ → PositiveThreshold := fun i => (qK i).1
    have hqmem (i : ℕ) : q i ∈ (curvature hf).support := (qK i).2
    have hqclosure (t : PositiveThreshold) (ht : t ∈ (curvature hf).support) :
        t ∈ closure (Set.range q) := by
      have hd : (⟨t, ht⟩ : (curvature hf).support) ∈ closure (Set.range qK) := hqK _
      have hd' := closure_subtype.1 hd
      have himage : (Subtype.val '' Set.range qK : Set PositiveThreshold) = Set.range q := by
        ext x
        constructor
        · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
          exact ⟨i, rfl⟩
        · rintro ⟨i, rfl⟩
          exact ⟨qK i, ⟨i, rfl⟩, rfl⟩
      rwa [himage] at hd'
    obtain ⟨a, b, ha1, hb1, haratio, hbratio, haleft, hbright⟩ :=
      witness_support_endpoints W (curvature hf).support
    let F : Finset PositiveThreshold := {a, b}.filter (fun t => t ∈ (curvature hf).support)
    have hFK : ∀ t ∈ F, t ∈ (curvature hf).support := by
      intro t ht
      exact (Finset.mem_filter.1 ht).2
    obtain ⟨tests, hRF, hRq⟩ := finite_knot_exhaustion A B hA hB
      (curvature hf).support hC F hFK q hqmem
    have hRa (haK : a ∈ (curvature hf).support) (j : ℕ) :
        (tests j).2.preparedOverlap a = optimalOverlap A B hA hB a := by
      apply hRF j a
      exact Finset.mem_filter.2 ⟨by simp, haK⟩
    have hRb (hbK : b ∈ (curvature hf).support) (j : ℕ) :
        (tests j).2.preparedOverlap b = optimalOverlap A B hA hB b := by
      apply hRF j b
      exact Finset.mem_filter.2 ⟨by simp, hbK⟩
    obtain ⟨E, hE, hE0, hEkernel, hEgap⟩ := witness_dominated_kernels hf A B hA hB
      W hW a b ha1 hb1 haratio hbratio haleft hbright tests hRa hRb
    have hcostfin (j : ℕ) : finiteCost hf (tests j).2 ≠ ⊤ := by
      apply (integrable_test_kernel_iff_finite_cost hf (tests j).2).1
      exact hE.mono' (actual_test_kernel_measurable (tests j).2).aestronglyMeasurable (hEkernel j)
    have hg (j : ℕ) := finite_cost_gap hf (tests j).2 hA hB (hcostfin j)
    have hzero (i : ℕ) : ∀ᶠ j in atTop, gap (tests j).2 (q i) = 0 := by
      filter_upwards [eventually_ge_atTop i] with j hij
      rw [gap_eq_overlap_trace, hRq i j hij,
        (optimalOverlap_spec A B hA hB (q i) (q i).2.le).2, sub_self]
    have hpoint (t : PositiveThreshold) (ht : t ∈ (curvature hf).support) :
        Tendsto (fun j => gap (tests j).2 t) atTop (𝓝 0) := by
      exact tendsto_zero_on_closure_of_eventual_interpolation (2 * B.trace.re)
        (by have := (Complex.nonneg_iff.mp hB.trace_nonneg).1; linarith)
        (fun j => gap (tests j).2)
        (fun j => (actual_gap_profile_data (tests j).2 hA hB).2)
        q hzero t (hqclosure t ht)
    have hgaplim : Tendsto (fun j => ∫ t, gap (tests j).2 t ∂curvature hf)
        atTop (𝓝 0) := by
      have hae : ∀ᵐ t ∂curvature hf,
          Tendsto (fun j => gap (tests j).2 t) atTop (𝓝 ((fun _ => (0 : ℝ)) t)) := by
        filter_upwards [Measure.support_mem_ae (μ := curvature hf)] with t ht
        exact hpoint t ht
      simpa only [integral_zero] using tendsto_integral_of_dominated_convergence E
        (fun j => (hg j).1.aestronglyMeasurable) hE hEgap hae
    have hineq (j : ℕ) : c ≤ H + ∫ t, gap (tests j).2 t ∂curvature hf := by
      have hMtest : maximalValue hf A B ≤ finiteCost hf (tests j).2 :=
        sInf_le ⟨(tests j).1, (tests j).2, rfl⟩
      rw [hc, (hg j).2, hH, ← EReal.coe_add, EReal.coe_le_coe_iff] at hMtest
      exact hMtest
    have hlimit : Tendsto (fun j => H + ∫ t, gap (tests j).2 t ∂curvature hf)
        atTop (𝓝 H) := by
      simpa only [add_zero] using (tendsto_const_nhds.add hgaplim)
    have hcH : c ≤ H := le_of_tendsto_of_tendsto tendsto_const_nhds hlimit
      (Eventually.of_forall hineq)
    apply le_antisymm _ hHM
    rw [hc, hH, EReal.coe_le_coe_iff]
    exact hcH

/-- Sufficiency for the entire original complex-L1 sigma-finite source
class in the independent universe u. Both values are the existing actual
ones, identified by the proved source-class and operational equalities. -/
theorem finiteLoewnerSlopes_implies_original_eq
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (c : ℝ) (hc : originalL1Value.{u} hf A B = (c : EReal))
    (hC : FiniteLoewnerSlopes A B hA hB (curvature hf).support) :
    originalL1Value.{u} hf A B = originalHockeyValue.{u} hf A B := by
  have hbridge : originalL1Value.{u} hf A B = maximalValue hf A B :=
    (originalL1Value_eq_allL1Value hf A B).trans (allL1Value_eq_maximalValue hf A B)
  have hM : maximalValue hf A B = (c : EReal) := hbridge.symm.trans hc
  exact hbridge.trans ((finiteLoewnerSlopes_implies_integrated_eq hf A B hA hB c hM hC).trans
    (hockeyValue_eq_original_operational hf A B hA hB).1)

/-- Arbitrary-support criterion for equality of the ACTUAL original-L1
infimum and ACTUAL hockey curvature value, at every finite matrix size.
The tuple condition includes virtual zero and all positive nodes lie in
the actual Stieltjes support. No endpoint finiteness or f-optimizer premise. -/
theorem original_eq_iff_finiteLoewnerSlopes
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (c : ℝ) (hc : originalL1Value.{u} hf A B = (c : EReal)) :
    (originalL1Value.{u} hf A B = originalHockeyValue.{u} hf A B) ↔
      FiniteLoewnerSlopes A B hA hB (curvature hf).support := by
  exact ⟨original_eq_implies_finiteLoewnerSlopes hf A B hA hB c hc,
    finiteLoewnerSlopes_implies_original_eq hf A B hA hB c hc⟩

end D5.S3.Quantum.Divergence.MaximalHockeyStickArbitrarySupport
