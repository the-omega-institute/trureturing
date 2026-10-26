/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/CompactMatrixPhysical
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:finite-gaussian-helper)
   anchors: []
   utility: none
   digest: Actual compact quadratic matrix form in the central Mellin coordinates. -/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.CompactMatrixCore
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfJacobi

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace FiniteGaussianCap475
open FiniteGaussianCap4.LaguerreSevenHalf
open FiniteGaussianCap4.LaguerreSevenHalf.RationalModel

/-- The actual central mode in charge coordinates; no fitted normalization. -/
def centralScaledMode (i : Fin 16) (x : ℝ) : ℝ :=
  (normalizedCentralMellin (2 * i.val) / normalizedCentralMellin 0) *
    centralPsi x (2 * i.val)

/-- The physical sixteen-mode head, in the charge coordinates u=d/z. -/
def centralHead (u : Fin 16 → ℝ) (x : ℝ) : ℝ :=
  ∑ i, u i * centralScaledMode i x

private theorem centralScaledMode_eq (i : Fin 16) (x : ℝ) :
    centralScaledMode i x = centralNormalization 0 *
      (congruenceScaleQ i.val : ℝ) * phi x (2 * i.val) := by
  have h := centralCharge_normalization_transport
    (fun k => (congruenceScaleQ k : ℝ)) (by norm_num [congruenceScaleQ])
    (by intro k; simp only [congruenceScaleQ]; push_cast; ring) i.val
  dsimp only [centralScaledMode, centralPsi]
  rw [← mul_assoc, h]

private theorem centralScaledMode_density (i j : Fin 16) (x : ℝ) :
    x ^ (7 / 2 : ℝ) * FiniteGaussianCap4.compactDebit x *
      centralScaledMode i x * centralScaledMode j x =
    (normalizationSquared * (congruenceScaleQ i.val : ℝ) *
      (congruenceScaleQ j.val : ℝ)) *
      (x ^ (7 / 2 : ℝ) * FiniteGaussianCap4.compactDebit x * Real.exp (-2 * x) *
        (laguerre (2 * i.val)).eval (2 * x) *
        (laguerre (2 * j.val)).eval (2 * x)) := by
  rw [centralScaledMode_eq, centralScaledMode_eq]
  have he : Real.exp (-2 * x) = Real.exp (-x) * Real.exp (-x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold normalizationSquared
  rw [he, ← centralNormalization_zero_sq_exact]
  unfold phi
  ring

/-- Integrability of the actual signed compact product is derived. -/
theorem centralScaledMode_product_integrable (i j : Fin 16) :
    IntervalIntegrable (fun x : ℝ =>
      x ^ (7 / 2 : ℝ) * FiniteGaussianCap4.compactDebit x *
        centralScaledMode i x * centralScaledMode j x) volume 0 6 := by
  simpa only [centralScaledMode_density] using
    ((compact_laguerre_product_integral i.val j.val).1.const_mul
      (normalizationSquared * (congruenceScaleQ i.val : ℝ) *
        (congruenceScaleQ j.val : ℝ)))

/-- The already enclosed matrix is the actual central-mode product integral. -/
theorem compactMomentMatrix_centralScaledMode (i j : Fin 16) :
    compactMomentMatrix i j = ∫ x : ℝ in 0..6,
      x ^ (7 / 2 : ℝ) * FiniteGaussianCap4.compactDebit x *
        centralScaledMode i x * centralScaledMode j x := by
  simp_rw [centralScaledMode_density]
  rw [intervalIntegral.integral_const_mul, compactMomentMatrix_integral]

/-- The complete head square is a real integral, exactly the same matrix form.
All signed pair integrability is proved above, without an assumed matrix bridge. -/
theorem centralHead_compact_quadratic (u : Fin 16 → ℝ) :
    IntervalIntegrable (fun x : ℝ =>
      x ^ (7 / 2 : ℝ) * FiniteGaussianCap4.compactDebit x * centralHead u x ^ 2)
      volume 0 6 ∧
    (∫ x : ℝ in 0..6,
      x ^ (7 / 2 : ℝ) * FiniteGaussianCap4.compactDebit x * centralHead u x ^ 2) =
      ∑ i, ∑ j, u i * u j * compactMomentMatrix i j := by
  let f (i j : Fin 16) (x : ℝ) : ℝ :=
    u i * u j * (x ^ (7 / 2 : ℝ) * FiniteGaussianCap4.compactDebit x *
      centralScaledMode i x * centralScaledMode j x)
  have hf (i j : Fin 16) : IntervalIntegrable (f i j) volume 0 6 :=
    (centralScaledMode_product_integrable i j).const_mul (u i * u j)
  have heq : (fun x : ℝ => x ^ (7 / 2 : ℝ) * FiniteGaussianCap4.compactDebit x *
      centralHead u x ^ 2) = (fun x : ℝ => ∑ i, ∑ j, f i j x) := by
    funext x
    simp only [centralHead, pow_two, Finset.sum_mul, Finset.mul_sum, f]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hinner (i : Fin 16) : IntervalIntegrable (fun x => ∑ j, f i j x) volume 0 6 := by
    convert IntervalIntegrable.sum Finset.univ (fun j _ => hf i j) using 1
    ext x
    simp only [Finset.sum_apply]
  constructor
  · rw [heq]
    convert IntervalIntegrable.sum Finset.univ (fun i _ => hinner i) using 1
    ext x
    simp only [Finset.sum_apply]
  · rw [heq, intervalIntegral.integral_finsetSum (fun i _ => hinner i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_finsetSum (fun j _ => hf i j)]
    apply Finset.sum_congr rfl
    intro j _
    simp only [f, intervalIntegral.integral_const_mul, ← compactMomentMatrix_centralScaledMode]

end FiniteGaussianCap475
