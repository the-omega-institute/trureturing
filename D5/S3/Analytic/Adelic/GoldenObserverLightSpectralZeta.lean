/- GID: D5/S3/Analytic/Adelic/GoldenObserverLightSpectralZeta
   generality: I
   mirror-B: D5/B/S3/Analytic/Adelic/GoldenObserverLightSpectralZeta
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden massless observer tower has the scaled Riemann zeta shape spectrum. -/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Real.GoldenRatio

/- Library-search audit trail (2026-08-30):
   * Current D5 and origin/dev searches for the golden observer energy scale,
     chiral spectral sums, two-branch sums, and dimensionless shape spectra
     found no whole-statement owner or canonical source-object definitions.
   * `ObserverScaleDivisorNonidentifiability` defines a different exponential
     zeta multiplier and proves divisor non-reconstruction, not these tower
     identities. `ZetaIdentities.riemann_zeta_dirichlet_sum` uses the
     repository's classical-zeta wrapper but does not construct this tower.
   * Pinned Mathlib's exact half-plane identity
     `zeta_eq_tsum_one_div_nat_add_one_cpow` is applied directly below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Adelic.GoldenObserverLightSpectralZeta

noncomputable section

/-- The nonzero level spacing of the massless tangent operator on the golden
regulator circle. -/
noncomputable def goldenLightScale : Real :=
  Real.pi ^ 2 / (2 * Real.log Real.goldenRatio)

private theorem golden_light_scale_pos : 0 < goldenLightScale := by
  exact div_pos (sq_pos_of_pos Real.pi_pos)
    (mul_pos (by norm_num) (Real.log_pos Real.one_lt_goldenRatio))

/-- The positive-chirality energy at the positive Fourier mode `n + 1`. -/
noncomputable def chiralEnergy (n : Nat) : Real :=
  goldenLightScale * ((n : Real) + 1)

/-- The spectral zeta series of one positive chirality branch. -/
noncomputable def chiralSpectralZeta (s : Complex) : Complex :=
  ∑' n : Nat, (chiralEnergy n : Complex) ^ (-s)

/-- The full spectral zeta series, summed over both chiralities and positive
mode magnitudes. -/
noncomputable def fullSpectralZeta (s : Complex) : Complex :=
  ∑' _branch : Fin 2, ∑' n : Nat, (chiralEnergy n : Complex) ^ (-s)

private theorem positive_mode_zeta_eq (s : Complex) (hs : 1 < s.re) :
    (∑' n : Nat, ((((n : Real) + 1 : Real) : Complex) ^ (-s))) =
      riemannZeta s := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  apply tsum_congr
  intro n
  simp only [Complex.cpow_neg, one_div, Complex.ofReal_add,
    Complex.ofReal_natCast, Complex.ofReal_one]

private theorem chiral_spectral_zeta_eq (s : Complex) (hs : 1 < s.re) :
    chiralSpectralZeta s =
      (goldenLightScale : Complex) ^ (-s) * riemannZeta s := by
  rw [chiralSpectralZeta]
  calc
    (∑' n : Nat, (chiralEnergy n : Complex) ^ (-s)) =
        ∑' n : Nat, (goldenLightScale : Complex) ^ (-s) *
          ((((n : Real) + 1 : Real) : Complex) ^ (-s)) := by
      apply tsum_congr
      intro n
      rw [chiralEnergy]
      simpa only [Complex.ofReal_mul] using
        Complex.mul_cpow_ofReal_nonneg golden_light_scale_pos.le (by positivity)
          (-s)
    _ = (goldenLightScale : Complex) ^ (-s) *
        ∑' n : Nat, ((((n : Real) + 1 : Real) : Complex) ^ (-s)) := by
      rw [tsum_mul_left]
    _ = (goldenLightScale : Complex) ^ (-s) * riemannZeta s := by
      rw [positive_mode_zeta_eq s hs]

/-- The positive-chirality tower is a scaled Riemann zeta series, the full
two-chirality tower doubles it, and division by the physical level spacing
recovers the exact dimensionless Riemann zeta shape spectrum. -/
theorem golden_observer_light_spectral_zeta (s : Complex) (hs : 1 < s.re) :
    chiralSpectralZeta s =
        (goldenLightScale : Complex) ^ (-s) * riemannZeta s ∧
    fullSpectralZeta s =
        2 * (goldenLightScale : Complex) ^ (-s) * riemannZeta s ∧
    ((∀ n : Nat, chiralEnergy n / goldenLightScale = (n : Real) + 1) ∧
      (∑' n : Nat,
          ((chiralEnergy n / goldenLightScale : Real) : Complex) ^ (-s)) =
        riemannZeta s) := by
  have chiralIdentity := chiral_spectral_zeta_eq s hs
  have normalizedEnergy : ∀ n : Nat,
      chiralEnergy n / goldenLightScale = (n : Real) + 1 := by
    intro n
    exact mul_div_cancel_left₀ _ golden_light_scale_pos.ne'
  have normalizedZeta :
      (∑' n : Nat,
          ((chiralEnergy n / goldenLightScale : Real) : Complex) ^ (-s)) =
        riemannZeta s := by
    simp_rw [normalizedEnergy]
    exact positive_mode_zeta_eq s hs
  refine ⟨chiralIdentity, ?_, normalizedEnergy, normalizedZeta⟩
  rw [fullSpectralZeta, tsum_fintype, Fin.sum_univ_two]
  change chiralSpectralZeta s + chiralSpectralZeta s =
    2 * (goldenLightScale : Complex) ^ (-s) * riemannZeta s
  rw [chiralIdentity]
  ring

#print axioms golden_observer_light_spectral_zeta

end


end D5.S3.Analytic.Adelic.GoldenObserverLightSpectralZeta
