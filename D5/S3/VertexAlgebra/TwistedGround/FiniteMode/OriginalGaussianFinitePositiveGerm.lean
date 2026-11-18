/- GID: D5/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFinitePositiveGerm
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FiniteMode/OriginalGaussianFinitePositiveGerm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal finite positive source equations and unconditional positive T germ equality. -/

import D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteEulerStencil
import D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianExternalGermCoefficientBridge
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGeneratedSource

/-! The finite positive candidate satisfies both original source equations with
its genuine signed negative-zero predecessors. Each pair has a complex germ of
equality with the literal original T mode; no uniform mode radius is asserted. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators Topology

namespace D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes

open OriginalGaussianMatrix OriginalGaussianAllIndexResolvent
open OriginalGaussianSourceEvaluation
open D5.S3.Analytic.OriginalHalfBinomialPeriod

private lemma L_symmetric (H : ℕ → ℕ → ℂ → ℂ)
    (hH : ∀ p q r, H p q r = H q p r) (p q : ℕ) (r : ℂ) :
    L H p q r = L H q p r := by
  unfold L
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  rw [hH]
  ring

private lemma P_symmetric (p q : ℕ) (r : ℂ) : P p q r = P q p r := by
  have hh : ∀ p q r, h p q r = h q p r := by
    intro p q r
    simp only [h, min_comm]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hh2 : ∀ p q r, h2 p q r = h2 q p r := by
    intro p q r
    simp only [h2, min_comm]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hg := L_symmetric h hh
  have hj := L_symmetric h2 hh2
  cases p <;> cases q <;> simp [P, shift11, L_h, L_h2, hg, hj]

private lemma t_symmetric (p q : ℕ) (r : ℂ) : t p q r = t q p r := by
  unfold t
  rw [P_symmetric]
  ring

private lemma tPrime_symmetric (p q : ℕ) {r : ℂ} (hr : ‖r‖ < 1) :
    tPrime p q r = tPrime q p r := by
  have hd := hasDerivAt_t p q hr
  have he : t p q = t q p := funext (t_symmetric p q)
  rw [he] at hd
  exact hd.unique (hasDerivAt_t q p hr)

private def actualPositiveU (p : ℕ) (r : ℝ) :=
  OriginalGaussianExternalDisplacement.modeFrequency true p
    (fun e k => sourceAmplitude e k (r : ℂ))

private def actualPositiveV (p : ℕ) (r : ℝ) :=
  2*(r : ℂ)*aPrime p r-actualPositiveU p r-2*(r : ℂ)*a p r*ell r

private lemma actualPositiveU_eq (p : ℕ) (r : ℝ) :
    actualPositiveU p r = (p+1/2 : ℂ)*
      (a p r-(if p=0 then sourceAmplitude false 0 r else a (p-1) r)) := by
  by_cases hp : p=0 <;>
    simp [actualPositiveU, OriginalGaussianExternalDisplacement.modeFrequency,
      OriginalGaussianExternalFrequency.externalParameter,
      OriginalGaussianExternalFrequency.predecessor, hp, sourceAmplitude_true_finite]

private lemma negativeZeroT_eq (q : ℕ) (r : ℝ) :
    negativeZeroT q r = (Real.sqrt (1-r) : ℂ)*
      ((r : ℂ)*aPrime q r-(r : ℂ)*ell r*a q r) := by
  cases q with
  | zero => simp [negativeZeroT, aPrime, a, centralWeight]; ring
  | succ q =>
    dsimp only [negativeZeroT]
    rw [a_euler_mode_step]

private lemma positive_t_left_equation (p q : ℕ) {r : ℝ}
    (hr : 0<r) (hr1 : r<1) :
    (r : ℂ)*tPrime p q r - (p+1/2 : ℂ)*
      (t p q r-(if p=0 then negativeZeroT q r else t (p-1) q r)) =
    (1-(r : ℂ))*((r : ℂ)*aPrime p r-(r : ℂ)*ell r*a p r-actualPositiveU p r)*
      ((r : ℂ)*aPrime q r-(r : ℂ)*ell r*a q r) := by
  have hp := P_euler_stencil p q (r : ℂ)
  rw [actualPositiveU_eq]
  cases p with
  | zero =>
    have hn := OriginalGaussianExternalGeneratedSource.boundary_normalization hr hr1
    have hs : (Real.sqrt (1-r) : ℂ)^2 = 1-(r : ℂ) := by
      exact_mod_cast Real.sq_sqrt (by linarith : 0 ≤ 1-r)
    have hb : (1-(r : ℂ))*sourceAmplitude false 0 r = (Real.sqrt (1-r) : ℂ) := by
      rw [← hs]
      linear_combination (Real.sqrt (1-r) : ℂ)*hn
    simp only [shiftX, ite_true, sub_zero, Nat.cast_zero] at hp
    simp only [tPrime, t, k, ite_true, Nat.cast_zero, negativeZeroT_eq]
    have ha0 : a 0 (r : ℂ) = 1 := by simp [a, centralWeight]
    have hap0 : aPrime 0 (r : ℂ) = 0 := by simp [aPrime]
    simp only [ha0, hap0, zero_mul, mul_zero, mul_one] at hp ⊢
    linear_combination hp -
      ((r : ℂ)*aPrime q r-(r : ℂ)*ell r*a q r)/2 * hb
  | succ p =>
    simp only [shiftX, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel,
      Nat.cast_add, Nat.cast_one] at hp ⊢
    dsimp only [tPrime, t, k]
    linear_combination hp -
      (1-(r : ℂ))*((r : ℂ)*aPrime q r)*
        a_euler_mode_step p (r : ℂ)

/-- The concrete finite candidate satisfies the original positive source equations
with the genuine signed negative-zero predecessor on each boundary. -/
theorem positive_t_mode_equations (p q : ℕ) {r : ℝ}
    (hr : 0<r) (hr1 : r<1) :
    let U := fun e k => OriginalGaussianExternalDisplacement.modeFrequency e k
      (fun f l => sourceAmplitude f l (r : ℂ))
    let V := fun e k =>
      2*(r : ℂ)*deriv (fun u : ℝ => sourceAmplitude e k (u : ℂ)) r-U e k-
        2*(r : ℂ)*sourceAmplitude e k r*shiftedCentralDerivative r 0/period r
    let L := (p+1/2 : ℂ)*(t p q r-
      (if p=0 then negativeZeroT q r else t (p-1) q r))
    let R := (q+1/2 : ℂ)*(t p q r-
      (if q=0 then negativeZeroT p r else t p (q-1) r))
    (L-R = (1-(r : ℂ))*(U true p*V true q-V true p*U true q)/2) ∧
    (2*(r : ℂ)*tPrime p q r-L-R =
      (1-(r : ℂ))/2*(V true p*V true q-U true p*U true q)) := by
  have hx : ‖(r : ℂ)‖<1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using hr1
  have hl := positive_t_left_equation p q hr hr1
  have hrr := positive_t_left_equation q p hr hr1
  rw [tPrime_symmetric q p hx, t_symmetric q p] at hrr
  simp only [t_symmetric (q-1) p] at hrr
  have hv (i : ℕ) :
      2*(r : ℂ)*deriv (fun u : ℝ => sourceAmplitude true i (u : ℂ)) r-
        actualPositiveU i r-2*(r : ℂ)*sourceAmplitude true i r*
          shiftedCentralDerivative r 0/period r = actualPositiveV i r := by
    rw [deriv_sourceAmplitude_true_real, sourceAmplitude_true_finite]
    unfold actualPositiveV
    rw [ell_eq_shifted hx]
    ring
  dsimp only
  change (_ = (1-(r : ℂ))*(actualPositiveU p r *
      (2*(r : ℂ)*deriv (fun u : ℝ => sourceAmplitude true q (u : ℂ)) r-
        actualPositiveU q r-2*(r : ℂ)*sourceAmplitude true q r*
          shiftedCentralDerivative r 0/period r) -
      (2*(r : ℂ)*deriv (fun u : ℝ => sourceAmplitude true p (u : ℂ)) r-
        actualPositiveU p r-2*(r : ℂ)*sourceAmplitude true p r*
          shiftedCentralDerivative r 0/period r)*actualPositiveU q r)/2) ∧ _
  simp only [show (OriginalGaussianExternalDisplacement.modeFrequency true p
      (fun f l => sourceAmplitude f l (r : ℂ))) = actualPositiveU p r from rfl,
    show (OriginalGaussianExternalDisplacement.modeFrequency true q
      (fun f l => sourceAmplitude f l (r : ℂ))) = actualPositiveU q r from rfl,
    hv p, hv q]
  change (_ = (1-(r : ℂ))*(actualPositiveU p r*actualPositiveV q r-
      actualPositiveV p r*actualPositiveU q r)/2) ∧
    (_ = (1-(r : ℂ))/2*(actualPositiveV p r*actualPositiveV q r-
      actualPositiveU p r*actualPositiveU q r))
  dsimp only [actualPositiveV]
  constructor
  · linear_combination hrr-hl
  · linear_combination hl+hrr

open Filter OriginalGaussianExternalResolvent OriginalGaussianExternalFrequency
open OriginalGaussianExternalDisplacement OriginalGaussianExternalGermCoefficientBridge

private lemma literal_analyticAt_zero (out out' : Bool) (p q : ℕ) :
    AnalyticAt ℂ (externalT out p out' q) 0 := by
  have hd : DifferentiableOn ℂ (externalT out p out' q)
      (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    exact (OriginalGaussianExternalRadialSums.literal_differentiable
      out out' p q (by simpa using hz)).differentiableWithinAt
  exact hd.analyticAt (Metric.isOpen_ball.mem_nhds (by simp))

private lemma difference_hasFPowerSeriesAt (p q : ℕ) :
    ∃ c : ℕ → ℂ, HasFPowerSeriesAt
      (fun z => externalT true p true q z - candidateT p q z)
      (FormalMultilinearSeries.ofScalars ℂ c) 0 := by
  have han : AnalyticAt ℂ
      (fun z => externalT true p true q z - candidateT p q z) 0 :=
    (literal_analyticAt_zero true true p q).sub
      (candidateT_analyticOnNhd p q 0 (by simp))
  obtain ⟨s, hs⟩ := han
  refine ⟨s.coeff, ?_⟩
  have he : FormalMultilinearSeries.ofScalars ℂ s.coeff = s := by
    funext n
    calc
      (FormalMultilinearSeries.ofScalars ℂ s.coeff) n =
          ContinuousMultilinearMap.mkPiRing ℂ (Fin n)
            ((FormalMultilinearSeries.ofScalars ℂ s.coeff).coeff n) :=
        (FormalMultilinearSeries.mkPiRing_coeff_eq _ n).symm
      _ = ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (s.coeff n) := by
        rw [FormalMultilinearSeries.coeff_ofScalars]
      _ = s n := FormalMultilinearSeries.mkPiRing_coeff_eq s n
  rw [he]
  exact hs

private def F (p q : ℕ) (z : ℂ) : ℂ :=
  externalT true p true q z - candidateT p q z

private def U (p : ℕ) (r : ℝ) : ℂ :=
  modeFrequency true p (fun e k => sourceAmplitude e k (r : ℂ))

private def V (p : ℕ) (r : ℝ) : ℂ :=
  2 * (r : ℂ) * deriv (fun u : ℝ => sourceAmplitude true p (u : ℂ)) r - U p r -
    2 * (r : ℂ) * sourceAmplitude true p r * shiftedCentralDerivative r 0 / period r

private def sourceDiff (p q : ℕ) (r : ℝ) : ℂ :=
  (1 - (r : ℂ)) * (U p r * V q r - V p r * U q r) / 2

private def sourceRad (p q : ℕ) (r : ℝ) : ℂ :=
  (1 - (r : ℂ)) / 2 * (V p r * V q r - U p r * U q r)

private def literalLeft (p q : ℕ) (r : ℝ) : ℂ :=
  modeFrequency true p (fun e k => externalT e k true q (Real.sqrt r : ℂ))

private def literalRight (p q : ℕ) (r : ℝ) : ℂ :=
  modeFrequency true q (fun e k => externalT true p e k (Real.sqrt r : ℂ))

private def finiteLeft (p q : ℕ) (r : ℝ) : ℂ :=
  ((p : ℂ) + 1 / 2) *
    (t p q r - (if p = 0 then negativeZeroT q r else t (p - 1) q r))

private def finiteRight (p q : ℕ) (r : ℝ) : ℂ :=
  ((q : ℂ) + 1 / 2) *
    (t p q r - (if q = 0 then negativeZeroT p r else t p (q - 1) r))

private lemma negative_column_finite (p : ℕ) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) :
    externalT true p false 0 (Real.sqrt r : ℂ) = negativeZeroT p r := by
  calc
    externalT true p false 0 (Real.sqrt r : ℂ) =
        externalT false 0 true p (Real.sqrt r : ℂ) := by
      simpa only [ite_true] using
        (OriginalGaussianExternalEquations.literal_symmetry true true false p 0
          (OriginalGaussianResolvent.radial_norm_lt_one hr1))
    _ = negativeZeroT p r := externalT_negative_zero_positive_finite p hr hr1

private lemma positive_difference_equations (p q : ℕ) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) :
    (((p : ℂ) - q) * F p q (Real.sqrt r : ℂ) -
      (p + 1 / 2) * (if p = 0 then 0 else F (p - 1) q (Real.sqrt r : ℂ)) +
      (q + 1 / 2) * (if q = 0 then 0 else F p (q - 1) (Real.sqrt r : ℂ)) = 0) ∧
    (2 * (r : ℂ) * deriv (fun s : ℝ => F p q (Real.sqrt s : ℂ)) r -
      ((p : ℂ) + q + 1) * F p q (Real.sqrt r : ℂ) +
      (p + 1 / 2) * (if p = 0 then 0 else F (p - 1) q (Real.sqrt r : ℂ)) +
      (q + 1 / 2) * (if q = 0 then 0 else F p (q - 1) (Real.sqrt r : ℂ)) = 0) := by
  have hx : ‖(r : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using hr1
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hs : (Real.sqrt r : ℂ) ^ 2 = (r : ℂ) := by
    exact_mod_cast Real.sq_sqrt hr.le
  have ha := OriginalGaussianExternalSourceJet.external_source_equations
    true p true q hr hr1
  have had : literalLeft p q r - literalRight p q r = sourceDiff p q r := ha.2.1
  have har : HasDerivAt
      (fun s : ℝ => externalT true p true q (Real.sqrt s : ℂ))
      ((literalLeft p q r + literalRight p q r + sourceRad p q r) /
        (2 * (r : ℂ))) r := ha.2.2

  have hc := positive_t_mode_equations p q hr hr1
  change (finiteLeft p q r - finiteRight p q r = sourceDiff p q r) ∧
    (2 * (r : ℂ) * tPrime p q r - finiteLeft p q r - finiteRight p q r =
      sourceRad p q r) at hc

  have hleft : literalLeft p q r - finiteLeft p q r =
      (p + 1 / 2) * (F p q (Real.sqrt r : ℂ) -
        (if p = 0 then 0 else F (p - 1) q (Real.sqrt r : ℂ))) := by
    unfold literalLeft finiteLeft modeFrequency externalParameter
    by_cases hp : p = 0
    · subst p
      simp only [predecessor, ite_true, if_pos rfl, Prod.fst, Prod.snd]
      rw [externalT_negative_zero_positive_finite q hr hr1]
      simp only [F, candidateT, hs]
      ring
    · simp only [predecessor, ite_true, if_neg hp, Prod.fst, Prod.snd]
      simp only [F, candidateT, hs]
      ring
  have hright : literalRight p q r - finiteRight p q r =
      (q + 1 / 2) * (F p q (Real.sqrt r : ℂ) -
        (if q = 0 then 0 else F p (q - 1) (Real.sqrt r : ℂ))) := by
    unfold literalRight finiteRight modeFrequency externalParameter
    by_cases hq : q = 0
    · subst q
      simp only [predecessor, ite_true, if_pos rfl, Prod.fst, Prod.snd]
      rw [negative_column_finite p hr hr1]
      simp only [F, candidateT, hs]
      ring
    · simp only [predecessor, ite_true, if_neg hq, Prod.fst, Prod.snd]
      simp only [F, candidateT, hs]
      ring

  have hcanfun : (fun s : ℝ => candidateT p q (Real.sqrt s : ℂ)) =ᶠ[𝓝 r]
      (fun s : ℝ => t p q (s : ℂ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hr] with s hspos
    dsimp only [candidateT]
    rw [show (Real.sqrt s : ℂ) ^ 2 = (s : ℂ) from by
      exact_mod_cast Real.sq_sqrt hspos.le]
  have hcan : HasDerivAt
      (fun s : ℝ => candidateT p q (Real.sqrt s : ℂ)) (tPrime p q r) r :=
    (hasDerivAt_t_real p q hx).congr_of_eventuallyEq hcanfun
  have harScaled :
      2 * (r : ℂ) * deriv (fun s : ℝ => externalT true p true q (Real.sqrt s : ℂ)) r -
        literalLeft p q r - literalRight p q r = sourceRad p q r := by
    rw [har.deriv]
    field_simp [hr0] <;> ring
  constructor
  · have he : (literalLeft p q r - finiteLeft p q r) -
        (literalRight p q r - finiteRight p q r) = 0 := by
      linear_combination had - hc.1
    rw [hleft, hright] at he
    linear_combination he
  · have he : 2 * (r : ℂ) * deriv (fun s : ℝ => F p q (Real.sqrt s : ℂ)) r -
        (literalLeft p q r - finiteLeft p q r) -
        (literalRight p q r - finiteRight p q r) = 0 := by
      change 2 * (r : ℂ) * deriv (fun s : ℝ =>
        externalT true p true q (Real.sqrt s : ℂ) - candidateT p q (Real.sqrt s : ℂ)) r -
          (literalLeft p q r - finiteLeft p q r) -
          (literalRight p q r - finiteRight p q r) = 0
      rw [deriv_fun_sub har.differentiableAt hcan.differentiableAt, hcan.deriv]
      linear_combination harScaled - hc.2
    rw [hleft, hright] at he
    linear_combination he

theorem externalT_positive_finite_germ :
    ∀ p q, ∀ᶠ z in 𝓝 (0 : ℂ), externalT true p true q z = candidateT p q z := by
  have hexp : ∀ p q, ∃ c : ℕ → ℂ, HasFPowerSeriesAt
      (fun z => externalT true p true q z - candidateT p q z)
      (FormalMultilinearSeries.ofScalars ℂ c) 0 := difference_hasFPowerSeriesAt
  choose c hc using hexp
  refine externalT_positive_germ_unique_of_pos_real_differential
    candidateT candidateT_even c hc ?_ ?_
  · dsimp only
    intro p q
    refine ⟨1, zero_lt_one, ?_⟩
    intro v hv hv1
    have hv2 : v ^ 2 < 1 := pow_lt_one₀ hv.le hv1 (by norm_num)
    have he := (positive_difference_equations p q (sq_pos_of_pos hv) hv2).1
    simpa only [F, Real.sqrt_sq hv.le] using he
  · dsimp only
    intro p q
    refine ⟨1, zero_lt_one, ?_⟩
    intro r hr hr1
    simpa only [F] using (positive_difference_equations p q hr hr1).2

end D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes
