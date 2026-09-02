/- GID: D5/S3/Analytic/Dilation/ScaleShapeSeparation
   generality: G
   mirror-B: D5/B/S3/Analytic/Dilation/ScaleShapeSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive scaling preserves spectral-zeta zeros; only shape can change them. -/

import D5.S3.Analytic.Asymptotics.SpectralZetaContinuation

open Set

namespace D5.S3.Analytic.Dilation.ScaleShapeSeparation

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Analytic.Asymptotics.SpectralZetaContinuation

noncomputable section

/-- The spectrum obtained by applying an overall real scale to a dimensionless shape. -/
def scaleSpectrum (a : ℝ) (lambda : ℕ → ℝ) : ℕ → ℝ :=
  fun n => a * lambda n

/-- The domain where the raw spectral Dirichlet series is genuinely summable. -/
def spectralZetaSummableAt (lambda : ℕ → ℝ) (s : ℂ) : Prop :=
  Summable (fun n : ℕ => (lambda n : ℂ) ^ (-s))

/-- The zero set of the raw spectral zeta on its summability domain. -/
def spectralZeroSet (lambda : ℕ → ℝ) : Set ℂ :=
  {s | spectralZetaSummableAt lambda s ∧ spectralZeta lambda s = 0}

/-- Scaling a positive spectrum factors its spectral zeta by `a ^ (-s)`. -/
lemma spectralZeta_scale (a : ℝ) (ha : 0 < a) (lambda : ℕ → ℝ)
    (hpos : ∀ n, 0 < lambda n) (s : ℂ) :
    spectralZeta (scaleSpectrum a lambda) s =
      (a : ℂ) ^ (-s) * spectralZeta lambda s := by
  unfold spectralZeta scaleSpectrum
  calc
    (∑' n : ℕ, ((a * lambda n : ℝ) : ℂ) ^ (-s)) =
        ∑' n : ℕ, (a : ℂ) ^ (-s) * (lambda n : ℂ) ^ (-s) := by
      apply tsum_congr
      intro n
      rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg ha.le (hpos n).le]
    _ = (a : ℂ) ^ (-s) * ∑' n : ℕ, (lambda n : ℂ) ^ (-s) := tsum_mul_left

/-- Positive scaling preserves and reflects the summability domain of the raw Dirichlet series. -/
lemma spectralZetaSummableAt_scale (a : ℝ) (ha : 0 < a) (lambda : ℕ → ℝ)
    (hpos : ∀ n, 0 < lambda n) (s : ℂ) :
    spectralZetaSummableAt (scaleSpectrum a lambda) s ↔
      spectralZetaSummableAt lambda s := by
  unfold spectralZetaSummableAt scaleSpectrum
  simp_rw [Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg ha.le (hpos _).le]
  exact summable_mul_left_iff
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr ha.ne')))

/-- A positive overall scale leaves every spectral-zeta zero unchanged. -/
lemma spectralZeroSet_scale (a : ℝ) (ha : 0 < a) (lambda : ℕ → ℝ)
    (hpos : ∀ n, 0 < lambda n) :
    spectralZeroSet (scaleSpectrum a lambda) = spectralZeroSet lambda := by
  ext s
  rw [spectralZeroSet, spectralZeroSet, Set.mem_ofPred_eq,
    spectralZetaSummableAt_scale a ha lambda hpos s,
    spectralZeta_scale a ha lambda hpos s]
  exact and_congr_right fun _ => mul_eq_zero_iff_left
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr ha.ne')))

/-- Scale-shape separation for positive spectra: overall scale preserves the spectral-zeta
zero set, and differing zero sets therefore require differing dimensionless shapes. -/
theorem scale_shape_separation (a : ℝ) (ha : 0 < a) (lambda : ℕ → ℝ)
    (hpos : ∀ n, 0 < lambda n) :
    spectralZeroSet (scaleSpectrum a lambda) = spectralZeroSet lambda ∧
      ∀ (b : ℝ), 0 < b → ∀ (mu : ℕ → ℝ), (∀ n, 0 < mu n) →
        spectralZeroSet (scaleSpectrum a lambda) ≠
            spectralZeroSet (scaleSpectrum b mu) →
          lambda ≠ mu := by
  refine ⟨spectralZeroSet_scale a ha lambda hpos, ?_⟩
  intro b hb mu hmupos hzeros hshape
  subst mu
  apply hzeros
  exact (spectralZeroSet_scale a ha lambda hpos).trans
    (spectralZeroSet_scale b hb lambda hmupos).symm

/-- Reverse probe for the second source assertion: changed zero sets force changed shape. -/
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (lambda mu : ℕ → ℝ)
    (hpos : ∀ n, 0 < lambda n) (hmupos : ∀ n, 0 < mu n)
    (hzeros : spectralZeroSet (scaleSpectrum a lambda) ≠
      spectralZeroSet (scaleSpectrum b mu)) :
    lambda ≠ mu := by
  exact (scale_shape_separation a ha lambda hpos).2 b hb mu hmupos hzeros

/-- Reverse probe for the first source assertion: membership in the zero set is scale invariant. -/
example (a : ℝ) (ha : 0 < a) (lambda : ℕ → ℝ)
    (hpos : ∀ n, 0 < lambda n) (s : ℂ) :
    s ∈ spectralZeroSet (scaleSpectrum a lambda) ↔ s ∈ spectralZeroSet lambda := by
  rw [scale_shape_separation a ha lambda hpos |>.1]

/-- Expected-red carrier probe for source assertions A1/A2: the divergent series with
`lambda n = n + 1` at `s = 0` must not acquire a zero from totalized `tsum`. -/
example : (0 : ℂ) ∉ spectralZeroSet (fun n : ℕ => (n + 1 : ℝ)) := by
  rintro ⟨hsum, _⟩
  have hnot : ¬Summable (fun _ : ℕ => (1 : ℂ)) := by
    simpa only [summable_const_iff] using (one_ne_zero : (1 : ℂ) ≠ 0)
  apply hnot
  simpa [spectralZetaSummableAt] using hsum

/-- Trivialization probe: zero cannot be supplied as the overall positive scale. -/
example : ¬(0 : ℝ) > 0 := by norm_num

/-- Trivialization probe: the identically zero sequence is not a positive spectral shape. -/
example : ¬∀ n : ℕ, 0 < (fun _ : ℕ => (0 : ℝ)) n := by simp

end

end D5.S3.Analytic.Dilation.ScaleShapeSeparation
