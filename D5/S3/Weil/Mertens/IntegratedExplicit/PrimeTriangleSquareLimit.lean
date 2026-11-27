/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimeTriangleSquareLimit
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimeTriangleSquareLimit
   mirror-E: none(waiver:prime-triangle-correction)
   anchors: []
   utility: none
   digest: The complete prime-power correction to the prime triangle has normalized limit six times the square root of two minus eight. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeTrianglePowerTail
import D5.S3.Arith.Robin.PriceRecord.UniformThetaShellError
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Tactic

/-! # The prime-square contribution to the prime triangle -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimeTriangleSquareLimit

open Filter MeasureTheory Set
open D5.S3.Arith.Robin.PriceRecord
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimeQuarterTriangle (mangoldtHingeSum primeTriangleSum triangleWeight)
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimeTrianglePowerTail
open scoped BigOperators Topology

private theorem sqrt_two_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
  Real.sq_sqrt (by norm_num)

private theorem one_le_sqrt_two : (1 : ℝ) ≤ Real.sqrt 2 := by
  simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 2 by norm_num)

private theorem sqrt_two_le_two : Real.sqrt 2 ≤ (2 : ℝ) := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp
  rw [sqrt_two_sq]
  norm_num

private theorem split_bounds {y : ℝ} (hy : 0 ≤ y) :
    y ≤ Real.sqrt 2 * y ∧ Real.sqrt 2 * y ≤ 2 * y :=
  ⟨by simpa only [one_mul] using mul_le_mul_of_nonneg_right one_le_sqrt_two hy,
    mul_le_mul_of_nonneg_right sqrt_two_le_two hy⟩

/-- The primes whose squares lie in the triangle's half-open window. -/
private def primeSquareSupport (x : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊Real.sqrt x⌋₊ ⌊2 * Real.sqrt x⌋₊).filter Nat.Prime

private theorem mem_primeSquareSupport {x : ℝ} (hx : 0 ≤ x) (p : ℕ) :
    p ∈ primeSquareSupport x ↔ p.Prime ∧ x < (p : ℝ)^2 ∧ (p : ℝ)^2 ≤ 4 * x := by
  have hy : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  have htop : (2 * Real.sqrt x)^2 = 4 * x := by
    rw [mul_pow, Real.sq_sqrt hx]
    norm_num
  rw [primeSquareSupport, Finset.mem_filter, Finset.mem_Ioc,
    Nat.floor_lt hy, Nat.le_floor_iff (by positivity : 0 ≤ 2 * Real.sqrt x),
    ← sq_lt_sq₀ hy (Nat.cast_nonneg p), ← sq_le_sq₀ (Nat.cast_nonneg p) (by positivity :
      0 ≤ 2 * Real.sqrt x), Real.sq_sqrt hx, htop]
  tauto

private theorem squareTriangleSum_eq_rootWindow {x : ℝ} (hx : 0 ≤ x) :
    squareTriangleSum x =
      ∑ p ∈ primeSquareSupport x, Real.log p * triangleWeight x ((p : ℝ)^2) := by
  unfold squareTriangleSum
  congr 1
  ext p
  rw [Finset.mem_filter, Nat.mem_primesLE, mem_primeSquareSupport hx]
  constructor
  · rintro ⟨⟨_, hp⟩, hlo, hhi⟩
    exact ⟨hp, hlo, hhi⟩
  · rintro ⟨hp, hlo, hhi⟩
    have hp₁ : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
    have hle : (p : ℝ) ≤ (p : ℝ)^2 := le_self_pow₀ hp₁ (by decide)
    exact ⟨⟨(Nat.le_floor_iff (by positivity : 0 ≤ 4*x)).mpr (hle.trans hhi), hp⟩, hlo, hhi⟩

private def branch (y A B t : ℝ) : ℝ := A + (B * y^2) / t^2

private theorem weight_left {y t : ℝ} (hy : 0 < y)
    (ht : t ∈ Icc y (Real.sqrt 2 * y)) :
    triangleWeight (y^2) (t^2) = branch y 2 (-2) t := by
  have ht0 := hy.trans_le ht.1
  have ht2 : 0 < t^2 := by positivity
  have hlow := (sq_le_sq₀ hy.le ht0.le).mpr ht.1
  have hhigh := (sq_le_sq₀ ht0.le (by positivity : 0 ≤ Real.sqrt 2 * y)).mpr ht.2
  rw [mul_pow, sqrt_two_sq] at hhigh
  have h1 : y^2 / t^2 ≤ 1 := (div_le_iff₀ ht2).mpr (by simpa using hlow)
  have h2 : 1 / 2 ≤ y^2 / t^2 := (le_div_iff₀ ht2).mpr (by linarith only [hhigh])
  simp only [triangleWeight, branch, mul_div_assoc,
    max_eq_left (by linarith only [h2] : 0 ≤ 4 * (y^2 / t^2) - 1),
    max_eq_left (by linarith only [h2] : 0 ≤ 2 * (y^2 / t^2) - 1),
    max_eq_right (sub_nonpos.mpr h1)]
  ring

private theorem weight_right {y t : ℝ} (hy : 0 < y)
    (ht : t ∈ Icc (Real.sqrt 2 * y) (2 * y)) :
    triangleWeight (y^2) (t^2) = branch y (-1) 4 t := by
  have ht0 := hy.trans_le ((split_bounds hy.le).1.trans ht.1)
  have ht2 : 0 < t^2 := by positivity
  have hlow := (sq_le_sq₀ (by positivity : 0 ≤ Real.sqrt 2 * y) ht0.le).mpr ht.1
  rw [mul_pow, sqrt_two_sq] at hlow
  have hhigh := (sq_le_sq₀ ht0.le (by positivity : 0 ≤ 2 * y)).mpr ht.2
  rw [mul_pow] at hhigh
  norm_num at hhigh
  have h2 : y^2 / t^2 ≤ 1 / 2 := (div_le_iff₀ ht2).mpr (by linarith only [hlow])
  have h4 : 1 / 4 ≤ y^2 / t^2 := (le_div_iff₀ ht2).mpr (by linarith only [hhigh])
  simp only [triangleWeight, branch, mul_div_assoc,
    max_eq_left (by linarith only [h4] : 0 ≤ 4 * (y^2 / t^2) - 1),
    max_eq_right (by linarith only [h2] : 2 * (y^2 / t^2) - 1 ≤ 0),
    max_eq_right (by linarith only [h2] : y^2 / t^2 - 1 ≤ 0)]
  ring

/-- The square profile in the prime variable divided by `sqrt x`. -/
def squareProfile (u : ℝ) : ℝ :=
  if 0 < u then triangleWeight 1 (u^2) else 0

theorem squareProfile_rescale {x t : ℝ} (hx : 1 ≤ x) (ht : 0 < t) :
    triangleWeight x (t^2) = squareProfile (t / Real.sqrt x) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hy : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hscale : x / t^2 = 1 / (t / Real.sqrt x)^2 := by
    rw [div_pow, div_div_eq_mul_div, one_mul, Real.sq_sqrt hx0.le]
  rw [squareProfile, if_pos (div_pos ht hy)]
  simp only [triangleWeight, mul_div_assoc, hscale]

theorem squareProfile_left {u : ℝ} (hu : u ∈ Icc 1 (Real.sqrt 2)) :
    squareProfile u = 2 - 2 / u^2 := by
  have hu0 : 0 < u := zero_lt_one.trans_le hu.1
  rw [squareProfile, if_pos hu0]
  simpa [branch, sub_eq_add_neg, neg_div] using
    weight_left (y := 1) (t := u) zero_lt_one (by simpa using hu)

theorem squareProfile_right {u : ℝ} (hu : u ∈ Icc (Real.sqrt 2) 2) :
    squareProfile u = 4 / u^2 - 1 := by
  have hu0 : 0 < u := (zero_lt_one.trans_le one_le_sqrt_two).trans_le hu.1
  rw [squareProfile, if_pos hu0]
  simpa [branch, sub_eq_add_neg, add_comm] using
    weight_right (y := 1) (t := u) zero_lt_one (by simpa using hu)

theorem squareProfile_eq_zero_of_le {u : ℝ} (hu : u ≤ 1) :
    squareProfile u = 0 := by
  by_cases hu0 : 0 < u
  · have hsq := (sq_le_sq₀ hu0.le zero_le_one).mpr hu
    have hq : 1 ≤ 1 / u^2 := (le_div_iff₀ (by positivity : 0 < u^2)).mpr
      (by simpa using hsq)
    simp only [squareProfile, if_pos hu0, triangleWeight, mul_div_assoc,
      max_eq_left (by linarith only [hq] : 0 ≤ 4 * (1 / u^2) - 1),
      max_eq_left (by linarith only [hq] : 0 ≤ 2 * (1 / u^2) - 1),
      max_eq_left (by linarith only [hq] : 0 ≤ 1 / u^2 - 1)]
    ring
  · simp only [squareProfile, if_neg hu0]

theorem squareProfile_eq_zero_of_two_le {u : ℝ} (hu : 2 ≤ u) :
    squareProfile u = 0 := by
  have hu0 : 0 < u := (by norm_num : (0 : ℝ) < 2).trans_le hu
  have hsq : 4 ≤ u^2 := by
    norm_num at * <;> nlinarith only [(sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 2) hu0.le).mpr hu]
  have hq : 1 / u^2 ≤ 1 / 4 := (div_le_iff₀ (by positivity : 0 < u^2)).mpr
    (by linarith only [hsq])
  simp only [squareProfile, if_pos hu0, triangleWeight, mul_div_assoc,
    max_eq_right (by linarith only [hq] : 4 * (1 / u^2) - 1 ≤ 0),
    max_eq_right (by linarith only [hq] : 2 * (1 / u^2) - 1 ≤ 0),
    max_eq_right (by linarith only [hq] : 1 / u^2 - 1 ≤ 0)]
  ring

/-- The compact square profile rises from zero to one and then returns to zero. -/
theorem squareProfile_totalVariation : eVariationOn squareProfile (univ : Set ℝ) = 2 := by
  have hPeak : squareProfile (Real.sqrt 2) = 1 := by
    rw [squareProfile_left ⟨one_le_sqrt_two, le_rfl⟩, sqrt_two_sq]
    norm_num
  have hStart : squareProfile 1 = 0 := squareProfile_eq_zero_of_le le_rfl
  have hEnd : squareProfile 2 = 0 := squareProfile_eq_zero_of_two_le le_rfl
  have hmono : MonotoneOn squareProfile (Icc 1 (Real.sqrt 2)) := by
    intro u hu v hv huv
    have hu0 : 0 < u := zero_lt_one.trans_le hu.1
    have hv0 : 0 < v := hu0.trans_le huv
    rw [squareProfile_left hu, squareProfile_left hv]
    exact sub_le_sub_left (div_le_div_of_nonneg_left (by norm_num)
      (by positivity : 0 < u^2) ((sq_le_sq₀ hu0.le hv0.le).mpr huv)) _
  have hmonoNeg : MonotoneOn (fun u => -squareProfile u) (Icc (Real.sqrt 2) 2) := by
    intro u hu v hv huv
    have hu0 : 0 < u := (zero_lt_one.trans_le (one_le_sqrt_two.trans hu.1))
    have hv0 : 0 < v := hu0.trans_le huv
    simp only [squareProfile_right hu, squareProfile_right hv]
    have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 4)
      (by positivity : 0 < u^2) ((sq_le_sq₀ hu0.le hv0.le).mpr huv)
    linarith only [h]
  have hleft : eVariationOn squareProfile (Icc 1 (Real.sqrt 2)) = 1 := by
    simpa [hPeak, hStart] using
      hmono.eVariationOn_eq ⟨le_rfl, one_le_sqrt_two⟩ ⟨one_le_sqrt_two, le_rfl⟩
  have hright : eVariationOn squareProfile (Icc (Real.sqrt 2) 2) = 1 := by
    have hNeg : eVariationOn (fun u => -squareProfile u) (Icc (Real.sqrt 2) 2) =
        eVariationOn squareProfile (Icc (Real.sqrt 2) 2) := by
      simp only [eVariationOn, edist_neg_neg]
    have h := hmonoNeg.eVariationOn_eq
      ⟨le_rfl, sqrt_two_le_two⟩ ⟨sqrt_two_le_two, le_rfl⟩
    simp only [Set.inter_self] at h
    rw [hNeg] at h
    simpa [hPeak, hEnd] using h
  have hbelow : eVariationOn squareProfile (Iic 1) = 0 := by
    apply (eVariationOn.eq_zero_iff squareProfile).mpr
    intro u hu v hv
    rw [squareProfile_eq_zero_of_le hu, squareProfile_eq_zero_of_le hv, edist_self]
  have habove : eVariationOn squareProfile (Ici 2) = 0 := by
    apply (eVariationOn.eq_zero_iff squareProfile).mpr
    intro u hu v hv
    rw [squareProfile_eq_zero_of_two_le hu, squareProfile_eq_zero_of_two_le hv, edist_self]
  rw [← Set.Iic_union_Ici (a := Real.sqrt 2),
    eVariationOn.union squareProfile isGreatest_Iic isLeast_Ici]
  have hL := eVariationOn.union squareProfile isGreatest_Iic (isLeast_Icc one_le_sqrt_two)
  have hR := eVariationOn.union squareProfile (isGreatest_Icc sqrt_two_le_two) isLeast_Ici
  rw [Set.Iic_union_Icc_eq_Iic one_le_sqrt_two, hbelow, hleft, zero_add] at hL
  rw [Set.Icc_union_Ici_eq_Ici sqrt_two_le_two, hright, habove, add_zero] at hR
  rw [hL, hR] <;> norm_num

/-- The common unsigned factor in the two Abel integrals at root scale. -/
def squareAbelKernel (y t : ℝ) : ℝ := y^2 / t^3

private theorem kernel_continuousOn (y : ℝ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (squareAbelKernel y) (Icc a b) :=
  continuousOn_const.div (continuousOn_id.pow 3)
    (fun t ht => pow_ne_zero _ (ha.trans_le ht.1).ne')

private theorem hasDerivAt_branch (y A B : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (branch y A B) ((-2 * B) * squareAbelKernel y t) t := by
  have hdiv := (hasDerivAt_const t (B * y^2)).fun_div
    ((hasDerivAt_id t).pow 2) (pow_ne_zero 2 ht.ne')
  convert (hasDerivAt_const t A).add hdiv using 1
  · funext z
    simp [branch, Pi.add_apply, div_eq_mul_inv, inv_pow]
  · dsimp [squareAbelKernel]
    field_simp [ht.ne'] <;> ring

private def primeLog (p : ℕ) : ℝ := if p.Prime then Real.log p else 0

private theorem primeLog_prefix (t : ℝ) :
    (∑ p ∈ Finset.Icc 0 ⌊t⌋₊, primeLog p) = Chebyshev.theta t := by
  simp only [primeLog, ← Finset.sum_filter, Chebyshev.theta_eq_sum_Icc]

private theorem abel_branch (y A B : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, Real.log p * branch y A B p) =
      branch y A B b * Chebyshev.theta b - branch y A B a * Chebyshev.theta a -
        (-2 * B) * (∫ t in a..b, squareAbelKernel y t * Chebyshev.theta t) := by
  have hd (t : ℝ) (ht : t ∈ Icc a b) :=
    hasDerivAt_branch y A B (ha.trans_le ht.1)
  have hcont : ContinuousOn (fun t => (-2 * B) * squareAbelKernel y t) (Icc a b) :=
    continuousOn_const.mul (kernel_continuousOn y ha)
  have hi : IntegrableOn (deriv (branch y A B)) (Icc a b) :=
    hcont.integrableOn_Icc.congr_fun (fun t ht => (hd t ht).deriv.symm) measurableSet_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul primeLog ha.le hab
    (fun t ht => (hd t ht).differentiableAt) hi
  simp only [primeLog_prefix] at habel
  rw [← intervalIntegral.integral_of_le hab] at habel
  have hint :
      (∫ t in a..b, deriv (branch y A B) t * Chebyshev.theta t) =
        ∫ t in a..b, (-2 * B) * (squareAbelKernel y t * Chebyshev.theta t) := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hab]
    intro t ht
    change deriv (branch y A B) t * Chebyshev.theta t = _
    rw [(hd t ht).deriv, mul_assoc]
  rw [hint, intervalIntegral.integral_const_mul] at habel
  rw [← habel, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : p.Prime <;> simp [primeLog, h, mul_comm]

private theorem ratio_start {y : ℝ} (hy : 0 < y) : y^2 / y^2 = 1 :=
  div_self (pow_ne_zero _ hy.ne')

private theorem ratio_middle {y : ℝ} (hy : 0 < y) :
    y^2 / (Real.sqrt 2 * y)^2 = 1 / 2 := by
  rw [mul_pow, sqrt_two_sq]
  field_simp [hy.ne'] <;> ring

private theorem ratio_end {y : ℝ} (hy : 0 < y) :
    y^2 / (2 * y)^2 = 1 / 4 := by
  rw [mul_pow]
  norm_num
  <;> field_simp [hy.ne'] <;> ring

/-- Exact Abel summation for every real scale `x ≥ 1`. The middle boundary cancels. -/
theorem primeSquareTriangleSum_abel {x : ℝ} (hx : 1 ≤ x) :
    squareTriangleSum x =
      -(4 * (∫ t in Real.sqrt x..Real.sqrt 2 * Real.sqrt x,
        squareAbelKernel (Real.sqrt x) t * Chebyshev.theta t)) +
      8 * (∫ t in Real.sqrt 2 * Real.sqrt x..2 * Real.sqrt x,
        squareAbelKernel (Real.sqrt x) t * Chebyshev.theta t) := by
  let y := Real.sqrt x
  let m := Real.sqrt 2 * y
  have hy : 0 < y := Real.sqrt_pos.2 (zero_lt_one.trans_le hx)
  have hy₂ : y^2 = x := Real.sq_sqrt (zero_le_one.trans hx)
  obtain ⟨hym, hm₂⟩ := split_bounds hy.le
  change squareTriangleSum x =
    -(4 * (∫ t in y..m, squareAbelKernel y t * Chebyshev.theta t)) +
      8 * (∫ t in m..2 * y, squareAbelKernel y t * Chebyshev.theta t)
  have hsplit :
      squareTriangleSum x =
        (∑ p ∈ (Finset.Ioc ⌊y⌋₊ ⌊m⌋₊).filter Nat.Prime,
          Real.log p * triangleWeight x ((p : ℝ)^2)) +
        (∑ p ∈ (Finset.Ioc ⌊m⌋₊ ⌊2 * y⌋₊).filter Nat.Prime,
          Real.log p * triangleWeight x ((p : ℝ)^2)) := by
    rw [squareTriangleSum_eq_rootWindow (by linarith)]
    simpa only [primeSquareSupport, Finset.sum_filter] using
      (Finset.sum_Ioc_consecutive
        (fun p : ℕ => if p.Prime then Real.log p * triangleWeight x ((p : ℝ)^2) else 0)
        (Nat.floor_le_floor hym) (Nat.floor_le_floor hm₂)).symm
  have hleft :
      (∑ p ∈ (Finset.Ioc ⌊y⌋₊ ⌊m⌋₊).filter Nat.Prime,
        Real.log p * triangleWeight x ((p : ℝ)^2)) =
      ∑ p ∈ (Finset.Ioc ⌊y⌋₊ ⌊m⌋₊).filter Nat.Prime, Real.log p * branch y 2 (-2) p := by
    apply Finset.sum_congr rfl
    intro p hp
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
    rw [← hy₂, weight_left hy
      ⟨((Nat.floor_lt hy.le).mp hlo).le, (Nat.le_floor_iff (hy.le.trans hym)).mp hhi⟩]
  have hright :
      (∑ p ∈ (Finset.Ioc ⌊m⌋₊ ⌊2 * y⌋₊).filter Nat.Prime,
        Real.log p * triangleWeight x ((p : ℝ)^2)) =
      ∑ p ∈ (Finset.Ioc ⌊m⌋₊ ⌊2 * y⌋₊).filter Nat.Prime, Real.log p * branch y (-1) 4 p := by
    apply Finset.sum_congr rfl
    intro p hp
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
    rw [← hy₂, weight_right hy
      ⟨((Nat.floor_lt (hy.le.trans hym)).mp hlo).le,
        (Nat.le_floor_iff (by positivity : 0 ≤ 2 * y)).mp hhi⟩]
  have hmid₁ : branch y 2 (-2) m = 1 := by
    simp only [branch, mul_div_assoc, m, ratio_middle hy]
    norm_num
  have hmid₂ : branch y (-1) 4 m = 1 := by
    simp only [branch, mul_div_assoc, m, ratio_middle hy]
    norm_num
  have hstart : branch y 2 (-2) y = 0 := by
    simp only [branch, mul_div_assoc, ratio_start hy]
    norm_num
  have hend : branch y (-1) 4 (2 * y) = 0 := by
    simp only [branch, mul_div_assoc, ratio_end hy]
    norm_num
  rw [hsplit, hleft, hright, abel_branch y 2 (-2) hy hym,
    abel_branch y (-1) 4 (hy.trans_le hym) hm₂, hmid₁, hmid₂, hstart, hend]
  ring

private theorem integral_kernel (y : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, squareAbelKernel y t) = (y^2 / a^2 - y^2 / b^2) / 2 := by
  have hp : (∫ t in a..b, squareAbelKernel y t) =
      branch y 0 (-(1 / 2)) b - branch y 0 (-(1 / 2)) a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := branch y 0 (-(1 / 2))) _
      ((kernel_continuousOn y ha).intervalIntegrable_of_Icc hab)
    rw [Set.uIcc_of_le hab]
    intro t ht
    convert hasDerivAt_branch y 0 (-(1 / 2)) (ha.trans_le ht.1) using 1 <;> ring
  rw [hp]
  simp only [branch, mul_div_assoc]
  ring

private theorem contOn_const_div_sq (B : ℝ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t : ℝ => B / t^2) (Icc a b) :=
  continuousOn_const.div (continuousOn_id.pow 2)
    (fun t ht => pow_ne_zero _ (ha.trans_le ht.1).ne')

private theorem integral_const_div_sq (B : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, B / t^2) = B / a - B / b := by
  calc
    (∫ t in a..b, B / t^2) = (-B) / b - (-B) / a := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => (-B) / t) _
        ((contOn_const_div_sq B ha).intervalIntegrable_of_Icc hab)
      rw [Set.uIcc_of_le hab]
      intro t ht
      simpa only [id_eq, zero_mul, zero_sub, mul_one, neg_neg] using
        (hasDerivAt_const t (-B)).fun_div (hasDerivAt_id t) (ha.trans_le ht.1).ne'
    _ = _ := by ring

private theorem integral_branch (y A B : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, branch y A B t) =
      (b - a) * A + (B * y^2 / a - B * y^2 / b) := by
  simp only [branch]
  rw [intervalIntegral.integral_add intervalIntegrable_const
    ((contOn_const_div_sq (B * y^2) ha).intervalIntegrable_of_Icc hab),
    intervalIntegral.integral_const, smul_eq_mul, integral_const_div_sq _ ha hab]

private theorem squareProfile_intervalIntegrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable squareProfile volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
  have hcont : ContinuousOn (fun t : ℝ => triangleWeight 1 (t^2)) (Icc a b) := by
    have hdiv (c : ℝ) : ContinuousOn (fun t : ℝ => c / t^2 - 1) (Icc a b) :=
      (contOn_const_div_sq c ha).sub continuousOn_const
    unfold triangleWeight
    exact (((hdiv (4 * 1)).sup continuousOn_const).sub
      (continuousOn_const.mul ((hdiv (2 * 1)).sup continuousOn_const))).add
      (continuousOn_const.mul ((hdiv 1).sup continuousOn_const))
  exact hcont.integrableOn_Icc.congr_fun
    (fun t ht => (if_pos (ha.trans_le ht.1) :
      squareProfile t = triangleWeight 1 (t^2)).symm) measurableSet_Icc

private theorem sqrt_two_inv : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
  have hs : 0 < Real.sqrt 2 := zero_lt_one.trans_le one_le_sqrt_two
  apply (div_eq_iff hs.ne').mpr
  calc
    (1 : ℝ) = (Real.sqrt 2)^2 / 2 := by rw [sqrt_two_sq]; norm_num
    _ = Real.sqrt 2 / 2 * Real.sqrt 2 := by ring

/-- The exact elementary mass of the rescaled triangle. -/
theorem squareProfile_integral :
    (∫ u in (1 : ℝ)..2, squareProfile u) = 6 * Real.sqrt 2 - 8 := by
  have hr : 0 < Real.sqrt 2 := zero_lt_one.trans_le one_le_sqrt_two
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (squareProfile_intervalIntegrable zero_lt_one one_le_sqrt_two)
    (squareProfile_intervalIntegrable hr sqrt_two_le_two)]
  have hl : (∫ u in (1 : ℝ)..Real.sqrt 2, squareProfile u) =
      ∫ u in (1 : ℝ)..Real.sqrt 2, branch 1 2 (-2) u := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le one_le_sqrt_two]
    intro u hu
    simpa [branch, sub_eq_add_neg, neg_div] using squareProfile_left hu
  have hh : (∫ u in Real.sqrt 2..2, squareProfile u) =
      ∫ u in Real.sqrt 2..2, branch 1 (-1) 4 u := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le sqrt_two_le_two]
    intro u hu
    simpa [branch, sub_eq_add_neg, add_comm] using squareProfile_right hu
  rw [hl, hh, integral_branch 1 2 (-2) zero_lt_one one_le_sqrt_two,
    integral_branch 1 (-1) 4 hr sqrt_two_le_two]
  simp only [one_pow, mul_one, mul_div_assoc, ← mul_one_div (-(2 : ℝ)) (Real.sqrt 2),
    ← mul_one_div (4 : ℝ) (Real.sqrt 2), sqrt_two_inv]
  ring

private theorem integral_kernel_mul_id (y : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, squareAbelKernel y t * t) = y^2 / a - y^2 / b := by
  rw [← integral_const_div_sq (y^2) ha hab]
  apply intervalIntegral.integral_congr
  rw [Set.uIcc_of_le hab]
  intro t ht
  unfold squareAbelKernel
  field_simp [(ha.trans_le ht.1).ne'] <;> ring

private theorem kernel_mass_left {y : ℝ} (hy : 0 < y) :
    (∫ t in y..Real.sqrt 2 * y, squareAbelKernel y t) = 1 / 4 := by
  rw [integral_kernel y hy (split_bounds hy.le).1, ratio_start hy, ratio_middle hy]
  norm_num

private theorem kernel_mass_right {y : ℝ} (hy : 0 < y) :
    (∫ t in Real.sqrt 2 * y..2 * y, squareAbelKernel y t) = 1 / 8 := by
  obtain ⟨hl, hr⟩ := split_bounds hy.le
  rw [integral_kernel y (hy.trans_le hl) hr, ratio_middle hy, ratio_end hy]
  norm_num

private theorem abel_main_term {y : ℝ} (hy : 0 < y) :
    -(4 * (∫ t in y..Real.sqrt 2 * y, squareAbelKernel y t * t)) +
      8 * (∫ t in Real.sqrt 2 * y..2 * y, squareAbelKernel y t * t) =
        (6 * Real.sqrt 2 - 8) * y := by
  obtain ⟨hl, hr⟩ := split_bounds hy.le
  have h₁ : y^2 / y = y := by field_simp [hy.ne'] <;> ring
  have hm : y^2 / (Real.sqrt 2 * y) = Real.sqrt 2 / 2 * y := by
    rw [div_mul_eq_div_div_swap, h₁]
    calc
      y / Real.sqrt 2 = y * (1 / Real.sqrt 2) := by ring
      _ = Real.sqrt 2 / 2 * y := by rw [sqrt_two_inv, mul_comm y]
  have h₂ : y^2 / (2 * y) = y / 2 := by
    rw [div_mul_eq_div_div_swap, h₁]
  rw [integral_kernel_mul_id y hy hl, integral_kernel_mul_id y (hy.trans_le hl) hr, h₁, hm, h₂]
  ring

private theorem integral_theta_error_bound (y : ℝ) {a b E : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hE : ∀ t ∈ Icc a b, |Chebyshev.theta t - t| ≤ E) :
    |(∫ t in a..b, squareAbelKernel y t * Chebyshev.theta t) -
      (∫ t in a..b, squareAbelKernel y t * t)| ≤
        E * (∫ t in a..b, squareAbelKernel y t) := by
  have hK := kernel_continuousOn y (b := b) ha
  have hθ : IntervalIntegrable (fun t => squareAbelKernel y t * Chebyshev.theta t) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (by simpa only [primeLog_prefix] using
        integrableOn_mul_sum_Icc primeLog ha.le hK.integrableOn_Icc (m := 0))
  have hId : IntervalIntegrable (fun t => squareAbelKernel y t * t) volume a b :=
    (hK.mul continuousOn_id).intervalIntegrable_of_Icc hab
  have hdiff : (fun t => squareAbelKernel y t * Chebyshev.theta t - squareAbelKernel y t * t) =
      fun t => squareAbelKernel y t * (Chebyshev.theta t - t) := by
    funext t
    rw [mul_sub]
  rw [← intervalIntegral.integral_sub hθ hId, hdiff]
  refine (intervalIntegral.abs_integral_le_integral_abs hab).trans ?_
  have hInt := hθ.sub hId
  rw [hdiff] at hInt
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hab hInt.abs
    ((continuousOn_const.mul hK).intervalIntegrable_of_Icc hab) ?_
  intro t ht
  have hK0 : 0 ≤ squareAbelKernel y t := by
    have ht0 := ha.trans_le ht.1
    unfold squareAbelKernel
    positivity
  rw [abs_mul, abs_of_nonneg hK0, mul_comm E]
  exact mul_le_mul_of_nonneg_left (hE t ht) hK0

/-- Multiplying the two absolute derivative masses by the same uniform error gives
the sharp variation factor (1 + 1 = 2). -/
theorem primeSquareTriangleSum_error {x E : ℝ} (hx : 1 ≤ x)
    (hE : ∀ t ∈ Icc (Real.sqrt x) (2 * Real.sqrt x), |Chebyshev.theta t - t| ≤ E) :
    |squareTriangleSum x - (6 * Real.sqrt 2 - 8) * Real.sqrt x| ≤ 2 * E := by
  let y := Real.sqrt x
  let m := Real.sqrt 2 * y
  have hy : 0 < y := Real.sqrt_pos.2 (zero_lt_one.trans_le hx)
  obtain ⟨hym, hm₂⟩ := split_bounds hy.le
  let L := ∫ t in y..m, squareAbelKernel y t * Chebyshev.theta t
  let R := ∫ t in m..2 * y, squareAbelKernel y t * Chebyshev.theta t
  let L₀ := ∫ t in y..m, squareAbelKernel y t * t
  let R₀ := ∫ t in m..2 * y, squareAbelKernel y t * t
  have hleft : |L - L₀| ≤ E * (1 / 4) := by
    have h := integral_theta_error_bound y hy hym (E := E)
      (fun t ht => hE t ⟨ht.1, ht.2.trans hm₂⟩)
    rw [kernel_mass_left hy] at h
    exact h
  have hright : |R - R₀| ≤ E * (1 / 8) := by
    have h := integral_theta_error_bound y (hy.trans_le hym) hm₂ (E := E)
      (fun t ht => hE t ⟨hym.trans ht.1, ht.2⟩)
    rw [kernel_mass_right hy] at h
    exact h
  have hAbel : squareTriangleSum x = -(4 * L) + 8 * R :=
    primeSquareTriangleSum_abel hx
  have hMass : -(4 * L₀) + 8 * R₀ = (6 * Real.sqrt 2 - 8) * Real.sqrt x :=
    abel_main_term hy
  rw [hAbel, ← hMass]
  calc
    |-(4 * L) + 8 * R - (-(4 * L₀) + 8 * R₀)| =
        |-(4 * (L - L₀)) + 8 * (R - R₀)| := by
          congr 1
          ring
    _ ≤ |-(4 * (L - L₀))| + |8 * (R - R₀)| := abs_add_le _ _
    _ = 4 * |L - L₀| + 8 * |R - R₀| := by
      rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8)]
    _ ≤ 2 * E := by linarith only [hleft, hright]

/-- The supremum of the unnormalized Chebyshev error over the actual root window. -/
def squareThetaError (y : ℝ) : ℝ :=
  sSup ((fun t : ℝ => |Chebyshev.theta t - t|) '' Icc y (2 * y))

theorem primeSquareTriangleSum_sup_error {x : ℝ} (hx : 1 ≤ x) :
    |squareTriangleSum x - (6 * Real.sqrt 2 - 8) * Real.sqrt x| ≤
      2 * squareThetaError (Real.sqrt x) := by
  apply primeSquareTriangleSum_error hx
  intro t ht
  have hy : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  unfold squareThetaError
  refine le_csSup ?_ (Set.mem_image_of_mem _ ht)
  exact BddAbove.mono
    (Set.image_mono (Set.Icc_subset_Icc_left (by linarith only [hy] :
      Real.sqrt x / 2 ≤ Real.sqrt x))) (UniformThetaShellError.errorValues_bddAbove hy)

/-- The unconditional full-real asymptotic for the square correction. -/
theorem primeSquareTriangleSum_tendsto :
    Tendsto (fun x : ℝ => squareTriangleSum x / Real.sqrt x)
      atTop (𝓝 (6 * Real.sqrt 2 - 8)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  -- The shell estimate applies the theta part of EulerLayerRootCorrection.prime_number_limits.
  have hε₄ : 0 < ε / 4 := by positivity
  have hθ := Real.tendsto_sqrt_atTop.eventually
    (UniformThetaShellError.shellError_eventually_le_mul hε₄)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hθ] with x hx hShell
  have hy : 0 < Real.sqrt x := hShell.1
  have hE (t : ℝ) (ht : t ∈ Icc (Real.sqrt x) (2 * Real.sqrt x)) :
      |Chebyshev.theta t - t| ≤ ε / 4 * Real.sqrt x :=
    (UniformThetaShellError.pointwise_le_shellError hy.le
      ⟨by linarith only [ht.1, hy], ht.2⟩).trans hShell.2
  have hbound := primeSquareTriangleSum_error hx hE
  have hquot :
      squareTriangleSum x / Real.sqrt x - (6 * Real.sqrt 2 - 8) =
        (squareTriangleSum x - (6 * Real.sqrt 2 - 8) * Real.sqrt x) / Real.sqrt x := by
    field_simp [hy.ne'] <;> ring
  rw [Real.dist_eq, hquot, abs_div, abs_of_pos hy]
  apply (div_lt_iff₀ hy).mpr
  exact hbound.trans_lt (by nlinarith only [mul_pos hε hy])

/-- Prime powers of exponent at least three have vanishing normalized mass. -/
theorem primeTrianglePowerTail_div_sqrt_tendsto_zero :
    Tendsto (fun x : ℝ => primeTrianglePowerTail x / Real.sqrt x) atTop (𝓝 0) := by
  let bound (y : ℝ) := Real.log 4 *
    (2 * y ^ (-(1 / 6 : ℝ)) + (2 / Real.log 2) * (Real.log y / y ^ (1 / 4 : ℝ)))
  have hcube := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).tendsto_div_nhds_zero
  have hbound : Tendsto bound atTop (𝓝 0) := by
    simpa only [bound, mul_zero, add_zero] using
      (((hcube.const_mul 2).add (hlog.const_mul (2 / Real.log 2))).const_mul (Real.log 4))
  have hscaled : Tendsto (fun x : ℝ => bound (4 * x)) atTop (𝓝 0) :=
    hbound.comp ((tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 4)).mpr tendsto_id)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hscaled
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact div_nonneg (primeTrianglePowerTail_bounds hx).1 (Real.sqrt_nonneg x)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    let y := 4 * x
    let K := ⌊Real.log y / Real.log 2⌋₊
    have hy : 0 < y := by dsimp only [y]; linarith
    have hys : 1 ≤ y := by dsimp only [y]; linarith
    have hxroot : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
    have hK : ((K - 3 : ℕ) : ℝ) ≤ Real.log y / Real.log 2 :=
      (Nat.cast_le.mpr (Nat.sub_le K 3)).trans
        (Nat.floor_le (div_nonneg (Real.log_nonneg hys) (Real.log_nonneg (by norm_num))))
    have htop := (primeTrianglePowerTail_bounds hx).2.1.trans
      (primeTrianglePowerTail_bounds hx).2.2
    have hroot : Real.sqrt y = 2 * Real.sqrt x := by
      dsimp only [y]
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    have hratio (r : ℝ) : y ^ r / Real.sqrt x = 2 * y ^ (r - 1 / 2) := by
      rw [Real.rpow_sub hy, ← Real.sqrt_eq_rpow, hroot]
      field_simp [hxroot.ne'] <;> ring
    calc
      _ ≤ (Real.log 4 * (y ^ (1 / 3 : ℝ) + ((K - 3 : ℕ) : ℝ) * y ^ (1 / 4 : ℝ))) /
          Real.sqrt x := div_le_div_of_nonneg_right htop hxroot.le
      _ ≤ (Real.log 4 * (y ^ (1 / 3 : ℝ) +
          (Real.log y / Real.log 2) * y ^ (1 / 4 : ℝ))) / Real.sqrt x := by
        apply div_le_div_of_nonneg_right _ hxroot.le
        exact mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hy.le _)))
          (Real.log_nonneg (by norm_num))
      _ = bound (4 * x) := by
        change _ = bound y
        rw [mul_div_assoc, add_div, mul_div_assoc, hratio, hratio,
          show (1 / 3 : ℝ) - 1 / 2 = -(1 / 6) by norm_num,
          show (1 / 4 : ℝ) - 1 / 2 = -(1 / 4) by norm_num]
        unfold bound
        simp only [Real.rpow_neg hy.le]
        ring

/-- The complete prime-power correction in the actual triangle has the
explicit square-root coefficient unconditionally. -/
theorem normalized_mangoldtHinge_sub_primeTriangle_tendsto :
    Tendsto (fun x : ℝ => (mangoldtHingeSum x - primeTriangleSum x) / Real.sqrt x)
      atTop (𝓝 (6 * Real.sqrt 2 - 8)) := by
  have hsum := primeSquareTriangleSum_tendsto.add primeTrianglePowerTail_div_sqrt_tendsto_zero
  rw [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  rw [mangoldtHingeSum_sub_primeTriangleSum hx, add_div]

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimeTriangleSquareLimit
