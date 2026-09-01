/- GID: D5/S3/Divergence/CauchyClosedForm
   generality: G
   mirror-B: D5/B/S3/Divergence/CauchyClosedForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove properties of the Cauchy KL closed form and a free-energy identity. -/

/- Library-search audit trail (2026-09-01):
   * Repository searches covered `klDivergence`, `KullbackLeibler`, `relativeEntropy`,
     `Cauchy`, `divergence`, and the `D5/S3/{Divergence,Entropy,Estimation}` trees. The finite
     divergence in `Divergence.ClassicalDPI` and its Gibbs equality theorem do not evaluate the
     continuous Cauchy family; no Cauchy closed form was found in D5.
   * Pinned mathlib provides both `ProbabilityTheory.cauchyMeasure` and the measure-valued
     `InformationTheory.klDiv`. It provides normalization of the Cauchy density and the general
     Radon--Nikodym KL API, but no theorem evaluating KL between two Cauchy measures and no
     integral of the required shifted logarithmic quadratic. The non-identical-measure integral
     bridge is therefore not claimed here.
   * The other pinned Lake packages were searched for the same Cauchy/KL names and had no hit.
     This module formalizes the atom's displayed closed form as a real-valued definition, then
     proves its algebraic consequences. The upstream measure KL is reused for the self-KL witness.
-/

import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.Distributions.Cauchy

namespace D5.S3.Divergence.CauchyClosedForm

/-- The displayed closed form for KL divergence between one-dimensional Cauchy laws, in nats. -/
noncomputable def cauchyKL (gamma1 delta1 gamma2 delta2 : Real) : Real :=
  Real.log (((delta1 + delta2) ^ 2 + (gamma1 - gamma2) ^ 2) /
    (4 * delta1 * delta2))

/-- The scalar horizon free-energy expression as a function of its singular-value ratio. -/
noncomputable def horizonFreeEnergy (sigma : Real) : Real :=
  -Real.log (1 - sigma ^ 2)

/-- The Cauchy KL closed form is symmetric. This algebraic fact does not require scale
positivity, although positivity is needed for its divergence properties. -/
theorem cauchy_kl_divergence_symm (gamma1 delta1 gamma2 delta2 : Real) :
    cauchyKL gamma1 delta1 gamma2 delta2 =
      cauchyKL gamma2 delta2 gamma1 delta1 := by
  unfold cauchyKL
  congr 1
  ring

/-- Positive scales make the argument of the logarithm at least one. -/
theorem one_le_cauchy_kl_argument (gamma1 delta1 gamma2 delta2 : Real)
    (hdelta1 : 0 < delta1) (hdelta2 : 0 < delta2) :
    1 <= ((delta1 + delta2) ^ 2 + (gamma1 - gamma2) ^ 2) /
      (4 * delta1 * delta2) := by
  have hden : 0 < 4 * delta1 * delta2 := by positivity
  apply (le_div_iff₀ hden).2
  nlinarith [sq_nonneg (delta1 - delta2), sq_nonneg (gamma1 - gamma2)]

/-- The Cauchy KL closed form is nonnegative for positive scales. -/
theorem cauchy_kl_divergence_nonneg (gamma1 delta1 gamma2 delta2 : Real)
    (hdelta1 : 0 < delta1) (hdelta2 : 0 < delta2) :
    0 <= cauchyKL gamma1 delta1 gamma2 delta2 := by
  unfold cauchyKL
  exact Real.log_nonneg (one_le_cauchy_kl_argument gamma1 delta1 gamma2 delta2
    hdelta1 hdelta2)

/-- For positive scales, the Cauchy KL closed form vanishes exactly when both parameters agree. -/
theorem cauchy_kl_divergence_eq_zero_iff (gamma1 delta1 gamma2 delta2 : Real)
    (hdelta1 : 0 < delta1) (hdelta2 : 0 < delta2) :
    cauchyKL gamma1 delta1 gamma2 delta2 = 0 <->
      gamma1 = gamma2 /\ delta1 = delta2 := by
  have hden : 0 < 4 * delta1 * delta2 := by positivity
  have harg :
      1 <= ((delta1 + delta2) ^ 2 + (gamma1 - gamma2) ^ 2) /
        (4 * delta1 * delta2) :=
    one_le_cauchy_kl_argument gamma1 delta1 gamma2 delta2 hdelta1 hdelta2
  constructor
  · intro hzero
    have hlog :
        Real.log (((delta1 + delta2) ^ 2 + (gamma1 - gamma2) ^ 2) /
          (4 * delta1 * delta2)) = 0 := by
      simpa only [cauchyKL] using hzero
    rcases Real.log_eq_zero.mp hlog with hargzero | hargone | hargneg
    · exfalso
      nlinarith
    · have hnum :
          (delta1 + delta2) ^ 2 + (gamma1 - gamma2) ^ 2 =
            4 * delta1 * delta2 :=
        (div_eq_one_iff_eq hden.ne').mp hargone
      have hsquares :
          (delta1 - delta2) ^ 2 + (gamma1 - gamma2) ^ 2 = 0 := by
        nlinarith
      have hparts := (add_eq_zero_iff_of_nonneg
        (sq_nonneg (delta1 - delta2)) (sq_nonneg (gamma1 - gamma2))).mp hsquares
      exact
        ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp hparts.2),
          sub_eq_zero.mp (sq_eq_zero_iff.mp hparts.1)⟩
    · exfalso
      nlinarith
  · rintro ⟨hgamma, hdelta⟩
    subst gamma2
    subst delta2
    unfold cauchyKL
    have hratio :
        ((delta1 + delta1) ^ 2 + (gamma1 - gamma1) ^ 2) /
          (4 * delta1 * delta1) = 1 := by
      field_simp [hdelta1.ne']
      ring
    rw [hratio, Real.log_one]

/-- For two equally centered scales `delta - omega` and `delta + omega`, the Cauchy KL closed
form is exactly the scalar horizon free energy at singular-value ratio `omega / delta`. -/
theorem shifted_cauchy_kl_eq_horizon_free_energy (gamma delta omega : Real)
    (homega : 0 < omega) (homega_delta : omega < delta) :
    cauchyKL gamma (delta - omega) gamma (delta + omega) =
      horizonFreeEnergy (omega / delta) := by
  have hdelta : 0 < delta := homega.trans homega_delta
  have hminus : 0 < delta - omega := sub_pos.mpr homega_delta
  have hplus : 0 < delta + omega := add_pos hdelta homega
  have hquot_nonneg : 0 <= omega / delta := div_nonneg homega.le hdelta.le
  have hquot_lt_one : omega / delta < 1 := (div_lt_one hdelta).2 homega_delta
  have hquot_sq_lt_one : (omega / delta) ^ 2 < (1 : Real) ^ 2 :=
    (sq_lt_sq₀ hquot_nonneg (by norm_num)).2 hquot_lt_one
  have hbase : 0 < 1 - (omega / delta) ^ 2 := by nlinarith
  have hgap : delta ^ 2 - omega ^ 2 ≠ 0 := by
    have hsquare : omega ^ 2 < delta ^ 2 :=
      (sq_lt_sq₀ homega.le hdelta.le).2 homega_delta
    nlinarith
  unfold cauchyKL horizonFreeEnergy
  have hratio :
      (((delta - omega) + (delta + omega)) ^ 2 + (gamma - gamma) ^ 2) /
          (4 * (delta - omega) * (delta + omega)) =
        (1 - (omega / delta) ^ 2)⁻¹ := by
    field_simp [hdelta.ne', hminus.ne', hplus.ne', hbase.ne', hgap]
    ring
  rw [hratio, Real.log_inv]

/- Equal unit-scale centered laws give the zero case. -/
example : cauchyKL 0 1 0 1 = 0 := by
  norm_num [cauchyKL]

/- Swapping scales one and two preserves the value `log (9/8)`, which is strictly positive. -/
example :
    cauchyKL 0 1 0 2 = Real.log (9 / 8) /\
      cauchyKL 0 2 0 1 = Real.log (9 / 8) /\
        0 < cauchyKL 0 1 0 2 := by
  constructor
  · norm_num [cauchyKL]
  constructor
  · norm_num [cauchyKL]
  · rw [show cauchyKL 0 1 0 2 = Real.log (9 / 8) by norm_num [cauchyKL]]
    exact Real.log_pos (by norm_num)

/- A location displacement of three at common unit scale gives `log (13/4) > 0`. -/
example :
    cauchyKL 0 1 3 1 = Real.log (13 / 4) /\ 0 < cauchyKL 0 1 3 1 := by
  constructor
  · norm_num [cauchyKL]
  · rw [show cauchyKL 0 1 3 1 = Real.log (13 / 4) by norm_num [cauchyKL]]
    exact Real.log_pos (by norm_num)

/- The upstream measure-valued KL agrees with the closed form at the self-divergence witness. -/
example :
    InformationTheory.klDiv
      (ProbabilityTheory.cauchyMeasure 0 1)
      (ProbabilityTheory.cauchyMeasure 0 1) = 0 := by
  exact InformationTheory.klDiv_self _

end D5.S3.Divergence.CauchyClosedForm
