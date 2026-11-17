/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGermCoefficientBridge
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGermCoefficientBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive-real differential identities determine exact complex germ coefficients. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalParityUniqueness
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
Scalar analytic inference for the conditional positive-sector germ coefficient bridge.

Project source: commit 2fd4380ac552c5cc9d30968cdebb0e5ece3a3496,
`OriginalGaussianExternalParityUniqueness.externalT_positive_germ_unique` and
the scalar chain calculation in `OriginalGaussianExternalRadialSums`.
Mathlib source: revision 56a005855ea17e0b0958f73ec801ae140b0a1679,
`HasFPowerSeriesOnBall.fderiv`, `HasFPowerSeriesOnBall.unshift`,
`FormalMultilinearSeries.derivSeries_coeff_one`, and isolated zeros.

The top theorem assumes boundary-eliminated DIFFERENCE equations on positive
real intervals. In particular, its zero predecessor at p = 0 or q = 0 is an
explicit normalized boundary assumption, not the raw signed `modeFrequency`.
On the raw fixed-mode route one must first prove the candidate's negative-zero
row and column equal the original nonzero boundary, with identical evaluated
sources, and subtract them. The full `externalT`, including its direct identity
pairing, occurs throughout. Analyticity, evenness and the value at zero alone
do not justify eliminating those boundaries.

Only the difference power-series expansions are assumed here; no recurrence
coefficient, candidate equality or all-sector identification is assumed.
The conclusion is a separate complex germ for each positive pair of modes.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped Topology
open Filter

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGermCoefficientBridge

open OriginalGaussianExternalResolvent OriginalGaussianExternalParityUniqueness

/-- The Euler operator on a scalar complex power series multiplies its nth
coefficient by n, including the zero coefficient. -/
theorem hasFPowerSeriesAt_euler_ofScalars {f : ℂ → ℂ} {a : ℕ → ℂ}
    (hf : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ a) 0) :
    HasFPowerSeriesAt (fun z => z * deriv f z)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => (n : ℂ) * a n)) 0 := by
  have hc : ∀ n,
      ((FormalMultilinearSeries.ofScalars ℂ a).derivSeries.unshift (0 : ℂ)).coeff n =
        (n : ℂ) * a n := by
    intro n
    cases n with
    | zero =>
        simp [FormalMultilinearSeries.coeff, FormalMultilinearSeries.unshift]
    | succ n =>
        change (FormalMultilinearSeries.ofScalars ℂ a).derivSeries.coeff n 1 =
          ((n + 1 : ℕ) : ℂ) * a (n + 1)
        rw [FormalMultilinearSeries.derivSeries_coeff_one,
          FormalMultilinearSeries.coeff_ofScalars]
        simp only [nsmul_eq_mul]
  have hs : (FormalMultilinearSeries.ofScalars ℂ a).derivSeries.unshift (0 : ℂ) =
      FormalMultilinearSeries.ofScalars ℂ (fun n => (n : ℂ) * a n) := by
    funext n
    rw [← FormalMultilinearSeries.mkPiRing_coeff_eq
      ((FormalMultilinearSeries.ofScalars ℂ a).derivSeries.unshift (0 : ℂ)) n, hc n]
    simpa only [FormalMultilinearSeries.coeff_ofScalars] using
      (FormalMultilinearSeries.mkPiRing_coeff_eq
        (FormalMultilinearSeries.ofScalars ℂ (fun n => (n : ℂ) * a n)) n)
  obtain ⟨r, hfr⟩ := hf
  have he := (hfr.fderiv.unshift (z := (0 : ℂ))).hasFPowerSeriesAt
  rw [hs] at he
  simpa only [zero_add, sub_zero, fderiv_eq_smul_deriv, smul_eq_mul] using he

/-- Zeros on a positive real interval force a complex analytic germ at zero
to vanish. The interval need not contain its endpoint zero. -/
theorem analyticAt_eventually_zero_of_pos_real {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) {ε : ℝ} (hε : 0 < ε)
    (hz : ∀ t : ℝ, 0 < t → t < ε → f (t : ℂ) = 0) :
    ∀ᶠ z in nhds (0 : ℂ), f z = 0 := by
  rcases hf.eventually_eq_zero_or_eventually_ne_zero with hzero | hnonzero
  · exact hzero
  · exfalso
    rw [eventually_nhdsWithin_iff] at hnonzero
    obtain ⟨δ, hδ, hd⟩ := Metric.eventually_nhds_iff.mp hnonzero
    let t : ℝ := min ε δ / 2
    have ht : 0 < t := half_pos (lt_min hε hδ)
    have hte : t < ε := by
      have hm := min_le_left ε δ
      dsimp [t]
      linarith [lt_min hε hδ]
    have htd : t < δ := by
      have hm := min_le_right ε δ
      dsimp [t]
      linarith [lt_min hε hδ]
    have hb : dist (t : ℂ) 0 < δ := by
      simpa only [dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht] using htd
    have hne : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    exact (hd hb (by simpa using hne)) (hz t ht hte)

/-- A positive-real differential identity determines its exact scalar Taylor
coefficients. The three expansions may have different radii: `add` intersects
the finitely many germ radii, and no uniform mode radius is used. -/
theorem linear_euler_germ_coefficients {f g h : ℂ → ℂ} {a b c : ℕ → ℂ}
    (hf : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ a) 0)
    (hg : HasFPowerSeriesAt g (FormalMultilinearSeries.ofScalars ℂ b) 0)
    (hh : HasFPowerSeriesAt h (FormalMultilinearSeries.ofScalars ℂ c) 0)
    (A B C D : ℂ) {ε : ℝ} (hε : 0 < ε)
    (hz : ∀ t : ℝ, 0 < t → t < ε →
      A * (t : ℂ) * deriv f (t : ℂ) + B * f (t : ℂ) +
        C * g (t : ℂ) + D * h (t : ℂ) = 0) :
    ∀ k : ℕ, (A * (k : ℂ) + B) * a k + C * b k + D * c k = 0 := by
  have hs := ((((hasFPowerSeriesAt_euler_ofScalars hf).const_smul (c := A)).add
    (hf.const_smul (c := B))).add (hg.const_smul (c := C))).add
      (hh.const_smul (c := D))
  change HasFPowerSeriesAt (fun z =>
    A * (z * deriv f z) + B * f z + C * g z + D * h z) _ 0 at hs
  have han : AnalyticAt ℂ (fun z =>
      A * z * deriv f z + B * f z + C * g z + D * h z) 0 := by
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_assoc] using hs.analyticAt
  have hzlocal := analyticAt_eventually_zero_of_pos_real han hε hz
  have hs0 := hs.eq_zero_of_eventually (by
    filter_upwards [hzlocal] with z hz
    simpa only [Pi.zero_apply, mul_assoc] using hz)
  intro k
  have he := congrArg (fun s : FormalMultilinearSeries ℂ ℂ ℂ =>
    s k (fun _ => 1)) hs0
  have he' : A * ((k : ℂ) * a k) + B * a k + C * b k + D * c k = 0 := by
    simpa [FormalMultilinearSeries.ofScalars] using he
  linear_combination he'

/-- Exact scalar conversion from the real radial derivative at r > 0 to the
complex Euler derivative at sqrt r. No derivative of sqrt at zero is used. -/
theorem two_mul_radial_deriv_eq_euler {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableAt ℂ f (Real.sqrt r : ℂ)) :
    2 * (r : ℂ) * deriv (fun t : ℝ => f (Real.sqrt t : ℂ)) r =
      (Real.sqrt r : ℂ) * deriv f (Real.sqrt r : ℂ) := by
  have hc := hf.hasDerivAt.scomp r (Real.hasDerivAt_sqrt hr.ne').ofReal_comp
  have hd : deriv (fun t : ℝ => f (Real.sqrt t : ℂ)) r =
      (((1 / (2 * Real.sqrt r) : ℝ) : ℂ)) * deriv f (Real.sqrt r : ℂ) := by
    simpa only [Function.comp_def, smul_eq_mul] using hc.deriv
  have hs : (Real.sqrt r : ℂ) ^ 2 = (r : ℂ) := by
    exact_mod_cast Real.sq_sqrt hr.le
  have hs0 : (Real.sqrt r : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hr).ne'
  rw [hd]
  push_cast
  rw [← hs]
  field_simp [hs0]

/-- Radial equations yield coefficients in z, hence the multiplier k, not 2k.
The radius is shrunk to the intersection of the equation interval, the unit
interval, and the neighborhood where the given series makes f differentiable. -/
theorem linear_radial_germ_coefficients {f g h : ℂ → ℂ} {a b c : ℕ → ℂ}
    (hf : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ a) 0)
    (hg : HasFPowerSeriesAt g (FormalMultilinearSeries.ofScalars ℂ b) 0)
    (hh : HasFPowerSeriesAt h (FormalMultilinearSeries.ofScalars ℂ c) 0)
    (A B C D : ℂ) {ε : ℝ} (hε : 0 < ε)
    (hz : ∀ r : ℝ, 0 < r → r < ε →
      A * (2 * (r : ℂ) * deriv (fun s : ℝ => f (Real.sqrt s : ℂ)) r) +
        B * f (Real.sqrt r : ℂ) + C * g (Real.sqrt r : ℂ) +
          D * h (Real.sqrt r : ℂ) = 0) :
    ∀ k : ℕ, (A * (k : ℂ) + B) * a k + C * b k + D * c k = 0 := by
  obtain ⟨δ, hδ, hd⟩ := Metric.eventually_nhds_iff.mp hf.eventually_differentiableAt
  apply linear_euler_germ_coefficients hf hg hh A B C D
    (ε := min (min 1 ε) δ) (lt_min (lt_min zero_lt_one hε) hδ)
  intro t ht hsmall
  have ht1 : t < 1 := (hsmall.trans_le (min_le_left _ _)).trans_le (min_le_left _ _)
  have hte : t < ε := (hsmall.trans_le (min_le_left _ _)).trans_le (min_le_right _ _)
  have htd : t < δ := hsmall.trans_le (min_le_right _ _)
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  have ht2e : t ^ 2 < ε := by nlinarith [mul_pos ht (sub_pos.mpr ht1)]
  have hsqrt : Real.sqrt (t ^ 2) = t := Real.sqrt_sq ht.le
  have hdf : DifferentiableAt ℂ f (Real.sqrt (t ^ 2) : ℂ) := by
    rw [hsqrt]
    apply hd
    simpa only [dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht] using htd
  have he := two_mul_radial_deriv_eq_euler ht2 hdf
  rw [hsqrt] at he
  have hz' := hz (t ^ 2) ht2 ht2e
  rw [hsqrt, he] at hz'
  simpa only [mul_assoc] using hz'

/-- Positive-sector local identification of the FULL original T from actual
boundary-eliminated differential equations on positive real neighborhoods.
Both Taylor recurrences are derived in the proof, then the existing parity
and coefficient induction are reused.

The let-bound F is the actual original-minus-candidate difference. Its absent
positive predecessor is explicitly zero. Establishing these hypotheses from
raw signed equations still requires the candidate negative-zero row/column
identities and exact common sources. This theorem neither supplies those
candidate boundary identities nor a global or all-sector extension. -/
theorem externalT_positive_germ_unique_of_pos_real_differential
    (candidate : ℕ → ℕ → ℂ → ℂ)
    (heven : ∀ p q z, candidate p q (-z) = candidate p q z)
    (c : ℕ → ℕ → ℕ → ℂ)
    (hexp : ∀ p q, HasFPowerSeriesAt
      (fun z => externalT true p true q z - candidate p q z)
      (FormalMultilinearSeries.ofScalars ℂ (c p q)) 0)
    (hdiff :
      let F : ℕ → ℕ → ℂ → ℂ := fun p q z =>
        externalT true p true q z - candidate p q z
      ∀ p q : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε →
        ((p : ℂ) - q) * F p q (t : ℂ) -
          (p + 1 / 2) * (if p = 0 then 0 else F (p - 1) q (t : ℂ)) +
          (q + 1 / 2) * (if q = 0 then 0 else F p (q - 1) (t : ℂ)) = 0)
    (hrad :
      let F : ℕ → ℕ → ℂ → ℂ := fun p q z =>
        externalT true p true q z - candidate p q z
      ∀ p q : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
        2 * (r : ℂ) * deriv (fun s : ℝ => F p q (Real.sqrt s : ℂ)) r -
          ((p : ℂ) + q + 1) * F p q (Real.sqrt r : ℂ) +
          (p + 1 / 2) * (if p = 0 then 0 else F (p - 1) q (Real.sqrt r : ℂ)) +
          (q + 1 / 2) * (if q = 0 then 0 else F p (q - 1) (Real.sqrt r : ℂ)) = 0) :
    ∀ p q, ∀ᶠ z in nhds (0 : ℂ), externalT true p true q z = candidate p q z := by
  let F : ℕ → ℕ → ℂ → ℂ := fun p q z =>
    externalT true p true q z - candidate p q z
  have hF : ∀ p q, HasFPowerSeriesAt (F p q)
      (FormalMultilinearSeries.ofScalars ℂ (c p q)) 0 := hexp
  have hzero : HasFPowerSeriesAt (fun _ : ℂ => (0 : ℂ))
      (FormalMultilinearSeries.ofScalars ℂ (0 : ℕ → ℂ)) 0 := by
    simpa using (hasFPowerSeriesAt_const (𝕜 := ℂ) (c := (0 : ℂ)) (e := (0 : ℂ)))
  have hP (p q : ℕ) : HasFPowerSeriesAt
      (fun z => if p = 0 then 0 else F (p - 1) q z)
      (FormalMultilinearSeries.ofScalars ℂ
        (fun k => if p = 0 then 0 else c (p - 1) q k)) 0 := by
    by_cases hp : p = 0
    · simpa [hp, FormalMultilinearSeries.ofScalars, Pi.zero_def] using hzero
    · simpa [hp] using hF (p - 1) q
  have hQ (p q : ℕ) : HasFPowerSeriesAt
      (fun z => if q = 0 then 0 else F p (q - 1) z)
      (FormalMultilinearSeries.ofScalars ℂ
        (fun k => if q = 0 then 0 else c p (q - 1) k)) 0 := by
    by_cases hq : q = 0
    · simpa [hq, FormalMultilinearSeries.ofScalars, Pi.zero_def] using hzero
    · simpa [hq] using hF p (q - 1)
  refine externalT_positive_germ_unique candidate heven c hexp ?_ ?_
  · intro p q k
    obtain ⟨ε, hε, heq⟩ := hdiff p q
    have hd : ∀ t : ℝ, 0 < t → t < ε →
        ((p : ℂ) - q) * F p q (t : ℂ) -
          (p + 1 / 2) * (if p = 0 then 0 else F (p - 1) q (t : ℂ)) +
          (q + 1 / 2) * (if q = 0 then 0 else F p (q - 1) (t : ℂ)) = 0 := heq
    have hc := linear_euler_germ_coefficients (hF p q) (hP p q) (hQ p q)
      0 ((p : ℂ) - q) (-(p + 1 / 2)) (q + 1 / 2) hε (by
        intro t ht hte
        convert hd t ht hte using 1 <;> ring)
    convert hc k using 1 <;> ring
  · intro p q k
    obtain ⟨ε, hε, heq⟩ := hrad p q
    have hr : ∀ r : ℝ, 0 < r → r < ε →
        2 * (r : ℂ) * deriv (fun s : ℝ => F p q (Real.sqrt s : ℂ)) r -
          ((p : ℂ) + q + 1) * F p q (Real.sqrt r : ℂ) +
          (p + 1 / 2) * (if p = 0 then 0 else F (p - 1) q (Real.sqrt r : ℂ)) +
          (q + 1 / 2) * (if q = 0 then 0 else F p (q - 1) (Real.sqrt r : ℂ)) = 0 := heq
    have hc := linear_radial_germ_coefficients (hF p q) (hP p q) (hQ p q)
      1 (-((p : ℂ) + q + 1)) (p + 1 / 2) (q + 1 / 2) hε (by
        intro r hr0 hre
        convert hr r hr0 hre using 1 <;> ring)
    convert hc k using 1 <;> ring

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGermCoefficientBridge
