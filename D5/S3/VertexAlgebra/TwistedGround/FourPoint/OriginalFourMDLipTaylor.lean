import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMDLipCovariance
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlitTaylor

/-! The literal original Taylor selectors on the continued D lip. -/

open Filter
open scoped Topology

noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDLipMean

open LatticeGeneratingFieldLocality LatticeHalfFock
open OriginalGaussianExternalBlocks OriginalCurrentMetric
open D5.S3.Analytic.OriginalHalfBinomialSlitPeriod (slitPeriod)
open OriginalFourMPeriodSource (dLip dPeriod dPeriod_eq_slit)
open OriginalFourMSignedOverlap (legSign)
open OriginalGaussianSewnAnalytic (coefficient)
open OriginalFourMSlitMean (slitMeanEntry slitCovarianceEntry slitCovariance)
open private dPeriod_analyticAt dPeriod_ne_zero from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPeriodSource
open private analytic_coefficient_slice coefficient_congr from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMSlitTaylor

def dLipMeanEntry (upperA l e : Bool) (p : ℕ) (r : ℂ) : ℂ :=
  coefficient p (fun u => -legSign l * dLipMean upperA e u r / dPeriod upperA r)

theorem dLipMeanEntry_analyticAt (upperA l e : Bool) (p : ℕ) {t : ℝ} (ht : 1 < t) :
    AnalyticAt ℂ (dLipMeanEntry upperA l e p) (t : ℂ) := by
  have hf : AnalyticAt ℂ (fun z : ℂ × ℂ =>
      -legSign l * dLipMean upperA e z.1 z.2 / dPeriod upperA z.2) (0, (t : ℂ)) :=
    (analyticAt_const.mul (dLipMean_joint_analytic upperA e ht)).div
      ((dPeriod_analyticAt upperA ht).comp_of_eq
        (f := fun z : ℂ × ℂ => z.2) analyticAt_snd rfl) (dPeriod_ne_zero upperA ht)
  exact analytic_coefficient_slice hf p

theorem dLipMeanEntry_eq_slit (upperA l e : Bool) (p : ℕ) {r : ℂ} (hr : r ∈ dLip upperA) :
    dLipMeanEntry upperA l e p r = slitMeanEntry l e p r := by
  unfold dLipMeanEntry slitMeanEntry
  apply coefficient_congr
  filter_upwards [dLipMean_eventuallyEq upperA e hr] with u hu
  rw [hu, dPeriod_eq_slit hr]

def dLipCovarianceEntry (D : LatticeData) (upperA l k : Bool)
    (x y : External D) (r : ℂ) : ℂ :=
  coefficient y.2.2 (fun v => coefficient x.2.2 (fun u =>
    gramComplex D x.2.1 y.2.1 * dLipCovariance upperA l k x.1 y.1 u v r))

theorem dLipCovarianceEntry_analyticAt (D : LatticeData) (upperA l k : Bool)
    (x y : External D) {t : ℝ} (ht : 1 < t) :
    AnalyticAt ℂ (dLipCovarianceEntry D upperA l k x y) (t : ℂ) := by
  have hf : AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ =>
      gramComplex D x.2.1 y.2.1 * dLipCovariance upperA l k x.1 y.1 p.1 p.2.1 p.2.2)
      (0, 0, (t : ℂ)) :=
    analyticAt_const.mul (dLipCovariance_joint_analytic upperA l k x.1 y.1 ht)
  exact analytic_coefficient_slice (analytic_coefficient_slice hf x.2.2) y.2.2

theorem dLipCovarianceEntry_eq_slit (D : LatticeData) (upperA l k : Bool)
    (x y : External D) {r : ℂ} (hr : r ∈ dLip upperA) :
    dLipCovarianceEntry D upperA l k x y r = slitCovarianceEntry D l k x y r := by
  have hU := dLipMean_eventuallyEq upperA x.1 hr
  have hV := dLipMean_eventuallyEq upperA y.1 hr
  let g := gramComplex D x.2.1 y.2.1
  let F (u v : ℂ) := dLipCovariance upperA l k x.1 y.1 u v r
  let G (u v : ℂ) := slitCovariance l k x.1 y.1 u v r
  unfold dLipCovarianceEntry slitCovarianceEntry
  change coefficient y.2.2 (fun v => coefficient x.2.2 (fun u => g * F u v)) =
    coefficient y.2.2 (fun v => coefficient x.2.2 (fun u => g * G u v))
  refine coefficient_congr ?_ y.2.2
  filter_upwards [hV] with v hv
  refine coefficient_congr ?_ x.2.2
  filter_upwards [hU] with u hu
  exact congrArg (g * ·) (dLipCovariance_eq_of_means upperA l k x.1 y.1 hr hu hv)

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMDLipMean
