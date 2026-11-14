/- GID: D5/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/MaximalHockeyStickLoewnerSlopes
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: Actual optimal-overlap Loewner slopes, finite interpolation and original-L1 equality necessity. -/

import D5.S3.Quantum.Divergence.MaximalHockeyStickAllL1Convex
import D5.S3.Quantum.Divergence.MaximalHockeyStickComponents
import D5.S3.Analytic.Measure.FullSupportProfileTransfer
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

open D5.S3.Analytic.Measure.FullSupportProfileTransfer

namespace D5.S3.Quantum.Divergence.MaximalHockeyStickLoewnerSlopes

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
    have hm : -c * (2 * c)⁻¹ = -(1 / 2 : ℝ) := by field_simp
    have hp : c * (2 * c)⁻¹ = (1 / 2 : ℝ) := by field_simp
    simp only [Fintype.sum_bool, r, E, Bool.false_eq_true, ↓reduceIte, smul_smul]
    rw [hm, hp]
    module
  have hsecond : ∑ b, (r b) ^ 2 • E b = c • R := by
    have hp : c ^ 2 * (2 * c)⁻¹ = c / 2 := by field_simp
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
    convert h using 1 <;> module
  have hXB : X ≤ B := by
    have h := smul_le_smul_of_nonneg_left (add_le_add hU.2.2 hV.2.2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    convert h using 1 <;> module
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

private theorem state_nonneg {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (i : Fin k) : 0 ≤ R.stateMatrix i :=
  map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm (R.state i).2.1

private theorem state_trace {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (i : Fin k) : (R.stateMatrix i).trace = 1 :=
  (R.state i).2.2

theorem trace_prepared {A B : Matrix n n ℂ} {k : ℕ}
    (R : ReverseTest A B k) (t : ℝ) :
    (R.preparedOverlap t).trace.re = ∑ i, min (R.p i) (t * R.q i) := by
  simp only [ReverseTest.preparedOverlap, Matrix.trace_sum, Matrix.trace_smul,
    state_trace, Complex.real_smul, mul_one, Complex.re_sum, Complex.ofReal_re]

theorem gap_eq_overlap_trace {A B : Matrix n n ℂ} {k : ℕ}
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
        have hii : (0 : Fin (m + 1)) < i := Fin.pos_iff_ne_zero.mpr hi
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
  rw [Finset.sum_sub_distrib]
  rw [sum_successor_sub (F := fun i => w i • d i)]

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

theorem hockey_eq_trace_sub {A B : Matrix n n ℂ} {k : ℕ}
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
      (∑ i : Fin m, (t i.succ - t i.castSucc) • d i.castSucc) -
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
    change (∑ i : Fin m, min (t j) (t i.succ) • (d i.castSucc - d i.succ)) = X j
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
      simp [l, Fintype.sum_sum_type, Fintype.sum_bool, a, W]
      rw [hGmoment]
      abel
    have hright : (∑ z, b z • W z) = B := by
      simp [l, Fintype.sum_sum_type, Fintype.sum_bool, b, W]
      rw [hGsum]
      abel
    obtain ⟨R, hR⟩ :=
      D5.S3.Quantum.Divergence.MaximalHockeyStickComponents.reverse_test_from_weighted_components
        (fun _ : l => Classical.choice hn) W hW a b ha hb
    have hR' : ∃ R : ReverseTest A B (Fintype.card l),
        ∀ t : ℝ, R.hockey t =
          ∑ i, max (a i - t * b i) 0 * (W i).trace.re := by
      rw [← hleft, ← hright]
      exact ⟨R, hR⟩
    obtain ⟨R, hR⟩ := hR'
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
        simp only [l, Fintype.sum_sum_type, Fintype.sum_bool, a, b, W,
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

end D5.S3.Quantum.Divergence.MaximalHockeyStickLoewnerSlopes
