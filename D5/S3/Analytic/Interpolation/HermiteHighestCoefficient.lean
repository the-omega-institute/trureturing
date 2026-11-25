/- GID: D5/S3/Analytic/Interpolation/HermiteHighestCoefficient
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/HermiteHighestCoefficient
   mirror-E: none(waiver:analytic-observation-bound-without-executable-mirror)
   anchors: []
   utility: none
   digest: Sharp recovery of the quartic coefficient from two Hermite prefix differences. -/

module

public import D5.S3.Analytic.Interpolation.ConfluentPositiveSampling
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Order.Bounds.Defs
public import D5.S3.Analytic.Interpolation.ConfluentHermiteObservation
public import Mathlib.LinearAlgebra.Matrix.Rank
import all D5.S3.Analytic.Interpolation.ConfluentPositiveSampling
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import all D5.S3.Analytic.Interpolation.ConfluentHermiteObservation
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.Abel

/-!
# Sharp quartic coefficient recovery from Hermite data

The first two positive-order Newton observations determine the cubic and quartic
coefficients on any three positive nodes, with repetitions allowed.
For matrix-valued Hermite data the signed inverse row acts in the Euclidean
operator norm, and the within-derivative bounds enter with their factorials.
-/

public section

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Interpolation.HermiteHighestCoefficient

open Polynomial ConfluentPositiveSampling

/-- Entries of the first and second positive-order Newton observations
on the cubic and quartic monomials. -/
private def cubicFirst (a : Fin 3 → ℝ) : ℝ :=
  a 0 ^ 2 + a 0 * a 1 + a 1 ^ 2

private def quarticFirst (a : Fin 3 → ℝ) : ℝ :=
  a 0 ^ 3 + a 0 ^ 2 * a 1 + a 0 * a 1 ^ 2 + a 1 ^ 3

private def cubicSecond (a : Fin 3 → ℝ) : ℝ :=
  a 0 + a 1 + a 2

private def quarticSecond (a : Fin 3 → ℝ) : ℝ :=
  a 0 ^ 2 + a 0 * a 1 + a 1 ^ 2 + (a 0 + a 1) * a 2 + a 2 ^ 2

/-- Determinant of the actual two-coordinate weighted sampling matrix. -/
private def samplingDet (a : Fin 3 → ℝ) : ℝ :=
  cubicFirst a * quarticSecond a - quarticFirst a * cubicSecond a

private theorem divByMonic_eq_of_const (p q : ℝ[X]) (b c : ℝ)
    (h : C c + (X - C b) * q = p) : p /ₘ (X - C b) = q := by
  refine (div_modByMonic_unique q (C c) (monic_X_sub_C b) ⟨h, ?_⟩).1
  rw [degree_X_sub_C]
  exact degree_C_le.trans_lt (WithBot.coe_lt_coe.mpr Nat.zero_lt_one)

/-- Direct computation from the successive monic divisions in
`weightedNewtonTail`. No separation of nodes is required. -/
private theorem weightedNewtonTail_two_entries (a : Fin 3 → ℝ) (v : Fin 2 → ℝ) :
    weightedNewtonTail 3 a v 0 = cubicFirst a * v 0 + quarticFirst a * v 1 ∧
    weightedNewtonTail 3 a v 1 = cubicSecond a * v 0 + quarticSecond a * v 1 := by
  let x := a 0
  let y := a 1
  let p : ℝ[X] := X ^ 3 * Polynomial.ofFn 2 v
  let q₁ : ℝ[X] :=
    C (v 0) * (X ^ 2 + C x * X + C (x ^ 2)) +
    C (v 1) * (X ^ 3 + C x * X ^ 2 + C (x ^ 2) * X + C (x ^ 3))
  let q₂ : ℝ[X] :=
    C (v 0) * (X + C (x + y)) +
    C (v 1) * (X ^ 2 + C (x + y) * X + C (x ^ 2 + x * y + y ^ 2))
  have hp : Polynomial.ofFn 2 v = C (v 0) + C (v 1) * X := by
    rw [Polynomial.ofFn_eq_sum_monomial, Fin.sum_univ_two]
    simp [← C_mul_X_pow_eq_monomial]
  have hq₁ : p /ₘ (X - C x) = q₁ := by
    apply divByMonic_eq_of_const p q₁ x (v 0 * x ^ 3 + v 1 * x ^ 4)
    simp only [p, hp, q₁, map_add, map_mul, map_pow]
    ring
  have hq₂ : q₁ /ₘ (X - C y) = q₂ := by
    apply divByMonic_eq_of_const q₁ q₂ y
      (v 0 * (x ^ 2 + x * y + y ^ 2) +
        v 1 * (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3))
    simp only [q₁, q₂, map_add, map_mul, map_pow]
    ring
  constructor
  · change polynomialNewtonData (fun i : Fin 2 => a i.succ)
      (p /ₘ (X - C x)) 0 = _
    rw [polynomialNewtonData_zero, hq₁]
    change q₁.eval y = _
    simp only [q₁, x, y, cubicFirst, quarticFirst, eval_add, eval_mul, eval_pow, eval_C, eval_X]
    ring
  · change polynomialNewtonData (fun i : Fin 2 => a i.succ)
      (p /ₘ (X - C x)) (0 : Fin 1).succ = _
    rw [polynomialNewtonData_succ, polynomialNewtonData_zero, hq₁]
    change (q₁ /ₘ (X - C y)).eval (a 2) = _
    rw [hq₂]
    simp only [q₂, x, y, cubicSecond, quarticSecond, eval_add, eval_mul, eval_pow, eval_C, eval_X]
    ring

/-- A positive determinant identity that also holds at full coalescence. -/
private theorem samplingDet_expansion (a : Fin 3 → ℝ) :
    samplingDet a =
      a 0 ^ 2 * a 1 ^ 2 + a 0 * a 1 * a 2 * (a 0 + a 1) +
        a 2 ^ 2 * cubicFirst a := by
  unfold samplingDet cubicFirst quarticFirst cubicSecond quarticSecond
  ring

private theorem samplingDet_pos (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i) :
    0 < samplingDet a := by
  rw [samplingDet_expansion]
  unfold cubicFirst
  have h0 := ha 0
  have h1 := ha 1
  have h2 := ha 2
  positivity

/-- Explicit inverse on both coefficient coordinates for arbitrary positive nodes. -/
def inverseTwo (a : Fin 3 → ℝ) (d : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![(quarticSecond a * d 0 - quarticFirst a * d 1) / samplingDet a,
    (cubicFirst a * d 1 - cubicSecond a * d 0) / samplingDet a]

private theorem inverseTwo_left (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i) :
    Function.LeftInverse (inverseTwo a) (weightedNewtonTail 3 a) := by
  intro v
  have hd := (samplingDet_pos a ha).ne'
  have h := weightedNewtonTail_two_entries a v
  funext i
  fin_cases i
  · change (quarticSecond a * weightedNewtonTail 3 a v 0 -
      quarticFirst a * weightedNewtonTail 3 a v 1) / samplingDet a = v 0
    rw [h.1, h.2, div_eq_iff hd]
    unfold samplingDet
    ring
  · change (cubicFirst a * weightedNewtonTail 3 a v 1 -
      cubicSecond a * weightedNewtonTail 3 a v 0) / samplingDet a = v 1
    rw [h.1, h.2, div_eq_iff hd]
    unfold samplingDet
    ring

private theorem inverseTwo_right (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i) :
    Function.RightInverse (inverseTwo a) (weightedNewtonTail 3 a) := by
  intro d
  have hd := (samplingDet_pos a ha).ne'
  have h := weightedNewtonTail_two_entries a (inverseTwo a d)
  funext i
  fin_cases i
  · change weightedNewtonTail 3 a (inverseTwo a d) 0 = d 0
    rw [h.1]
    simp only [inverseTwo, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp [hd]
    unfold samplingDet
    ring
  · change weightedNewtonTail 3 a (inverseTwo a d) 1 = d 1
    rw [h.2]
    simp only [inverseTwo, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp [hd]
    unfold samplingDet
    ring

/-- The explicit inverse works in both directions on the actual Newton data. -/
theorem weightedNewtonTail_two_inverse (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i) :
    let sample := fun v => weightedNewtonTail 3 a v
    Function.LeftInverse (inverseTwo a) sample ∧ Function.RightInverse (inverseTwo a) sample :=
  ⟨inverseTwo_left a ha, inverseTwo_right a ha⟩

/-- Signed weights for the highest coefficient, with the first weight
negative and the second positive on positive nodes. -/
def highestWeight0 (a : Fin 3 → ℝ) : ℝ :=
  -(cubicSecond a / samplingDet a)

def highestWeight1 (a : Fin 3 → ℝ) : ℝ :=
  cubicFirst a / samplingDet a

private theorem highestCoefficient_inverse (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i)
    (v : Fin 2 → ℝ) :
    v 1 = highestWeight0 a * weightedNewtonTail 3 a v 0 +
      highestWeight1 a * weightedNewtonTail 3 a v 1 := by
  have h := congrArg (fun w : Fin 2 → ℝ => w 1) ((weightedNewtonTail_two_inverse a ha).1 v)
  change (cubicFirst a * weightedNewtonTail 3 a v 1 -
    cubicSecond a * weightedNewtonTail 3 a v 0) / samplingDet a = v 1 at h
  rw [← h, highestWeight0, highestWeight1]
  ring

private theorem highestWeight_signs (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i) :
    highestWeight0 a < 0 ∧ 0 < highestWeight1 a := by
  have hd := samplingDet_pos a ha
  have h0 := ha 0
  have h1 := ha 1
  have h2 := ha 2
  unfold highestWeight0 highestWeight1 cubicFirst cubicSecond
  constructor
  · exact neg_lt_zero.mpr (by positivity)
  · positivity

/-- The l1 row norm governing the highest coefficient in the sup-norm data model. -/
def highestRowSum (a : Fin 3 → ℝ) : ℝ :=
  |highestWeight0 a| + |highestWeight1 a|

private theorem highestRowSum_formula (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i) :
    highestRowSum a = (cubicSecond a + cubicFirst a) / samplingDet a := by
  have hs := highestWeight_signs a ha
  rw [highestRowSum, abs_of_neg hs.1, abs_of_pos hs.2, highestWeight0, highestWeight1,
    neg_neg, add_div]

/-- Algebraic version of the design bound. Each magnitude is at least 1/2.
Equality in the bound for the second magnitude forces all three nodes to be 1. -/
private theorem samplingDet_bounds (a : Fin 3 → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, a i ≤ 1) :
    samplingDet a ≤ 2 * cubicFirst a ∧ samplingDet a ≤ 2 * cubicSecond a ∧
      (samplingDet a = 2 * cubicFirst a → ∀ i, a i = 1) := by
  let x := a 0
  let y := a 1
  let z := a 2
  have hx : 0 < x := ha 0
  have hy : 0 < y := ha 1
  have hz : 0 < z := ha 2
  have hx1 : x ≤ 1 := hb 0
  have hy1 : y ≤ 1 := hb 1
  have hz1 : z ≤ 1 := hb 2
  have mul_le_one {u w : ℝ} (hu : u ≤ 1) (hw₀ : 0 ≤ w) (hw : w ≤ 1) : u * w ≤ 1 :=
    (mul_le_of_le_one_left hw₀ hu).trans hw
  have hxy := mul_le_one hx1 hy.le hy1
  have hxz := mul_le_one hx1 hz.le hz1
  have hyz := mul_le_one hy1 hz.le hz1
  have hzz := mul_le_one hz1 hz.le hz1
  have hxx := mul_le_one hx1 hx.le hx1
  have hxyz := mul_le_one hxy hz.le hz1
  have hApos : 0 < x ^ 2 + x * y + y ^ 2 := by positivity
  have hgap₁ : 0 ≤ (x ^ 2 + x * y + y ^ 2) * (1 - z ^ 2) :=
    mul_nonneg hApos.le (sub_nonneg.mpr (by simpa only [pow_two] using hzz))
  have hgap₂ := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hyz)
  have hgap₃ := mul_nonneg (sq_nonneg y) (sub_nonneg.mpr hxz)
  have hgap₄ := mul_nonneg (mul_nonneg hx.le hy.le) (sub_nonneg.mpr hxy)
  have hgapC₁ := mul_nonneg hx.le (sub_nonneg.mpr (mul_le_one hxy hy.le hy1))
  have hgapC₂ := mul_nonneg hx.le (sub_nonneg.mpr hxyz)
  have hgapC₃ := mul_nonneg hy.le (sub_nonneg.mpr hxyz)
  have hgapC₄ := mul_nonneg hy.le (sub_nonneg.mpr (mul_le_one hyz hz.le hz1))
  have hgapC₅ := mul_nonneg hz.le (sub_nonneg.mpr (mul_le_one hxx hz.le hz1))
  have hgapC₆ := mul_nonneg hz.le (sub_nonneg.mpr hxyz)
  have hd : samplingDet a = x ^ 2 * y ^ 2 + x * y * z * (x + y) +
      z ^ 2 * (x ^ 2 + x * y + y ^ 2) := samplingDet_expansion a
  rw [hd]
  change _ ≤ 2 * (x ^ 2 + x * y + y ^ 2) ∧ _ ≤ 2 * (x + y + z) ∧
    (_ = 2 * (x ^ 2 + x * y + y ^ 2) → ∀ i, a i = 1)
  refine ⟨?_, ?_, ?_⟩
  · nlinarith only [hgap₁, hgap₂, hgap₃, hgap₄]
  · nlinarith only [hgapC₁, hgapC₂, hgapC₃, hgapC₄, hgapC₅, hgapC₆]
  · intro he
    have he₁ : (x ^ 2 + x * y + y ^ 2) * (1 - z ^ 2) = 0 := by
      nlinarith only [he, hgap₁, hgap₂, hgap₃, hgap₄]
    have he₄ : x * y * (1 - x * y) = 0 := by
      nlinarith only [he, hgap₁, hgap₂, hgap₃, hgap₄]
    have hzsq : 1 - z ^ 2 = 0 :=
      (mul_eq_zero.mp he₁).resolve_left hApos.ne'
    have hxyEq : 1 - x * y = 0 :=
      (mul_eq_zero.mp he₄).resolve_left (mul_pos hx hy).ne'
    have hxEq : x = 1 := by
      have h := mul_le_mul_of_nonneg_left hy1 hx.le
      nlinarith only [h, hxyEq, hx1]
    have hyEq : y = 1 := by
      have h := mul_le_mul_of_nonneg_right hx1 hy.le
      nlinarith only [h, hxyEq, hy1]
    have hzEq : z = 1 := by
      have h : z ^ 2 ≤ z := by
        simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left hz1 hz.le
      nlinarith only [h, hzsq, hz1]
    intro i
    fin_cases i
    · exact hxEq
    · exact hyEq
    · exact hzEq

/-- The optimal row sum on the positive unit cube is 1, with unique
minimizer given by complete coalescence at 1. -/
theorem highestRowSum_optimal (a : Fin 3 → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, a i ≤ 1) :
    let row := highestRowSum a
    1 ≤ row ∧ (row = 1 ↔ ∀ i, a i = 1) := by
  dsimp only
  obtain ⟨hA, hC, heq⟩ := samplingDet_bounds a ha hb
  have hd := samplingDet_pos a ha
  constructor
  · rw [highestRowSum_formula a ha, le_div_iff₀ hd, one_mul]
    linarith only [hA, hC]
  · constructor
    · intro h
      rw [highestRowSum_formula a ha, div_eq_iff hd.ne', one_mul] at h
      exact heq (by linarith only [h, hA, hC])
    · intro h
      have hh : a = (fun _ => 1) := funext h
      subst a
      norm_num [highestRowSum, highestWeight0, highestWeight1, samplingDet,
        cubicFirst, quarticFirst, cubicSecond, quarticSecond]

/-- Scalar upper bound for the actual observations, with coordinatewise
error at most ε. -/
private theorem highestCoefficient_bound (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i)
    (v : Fin 2 → ℝ) (ε : ℝ) (hdata : ∀ i, |weightedNewtonTail 3 a v i| ≤ ε) :
    |v 1| ≤ ε * highestRowSum a := by
  rw [highestCoefficient_inverse a ha v]
  calc
    _ ≤ |highestWeight0 a * weightedNewtonTail 3 a v 0| +
        |highestWeight1 a * weightedNewtonTail 3 a v 1| := abs_add_le _ _
    _ ≤ |highestWeight0 a| * ε + |highestWeight1 a| * ε := by
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left (hdata 0) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (hdata 1) (abs_nonneg _))
    _ = ε * highestRowSum a := by unfold highestRowSum; ring

/-- Sign-saturated data attain the scalar worst case for each positive cloud
and every nonnegative noise radius. Both coordinates of the inverse are explicit. -/
private theorem highestCoefficient_attained (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i)
    (ε : ℝ) (hε : 0 ≤ ε) :
    let d : Fin 2 → ℝ := ![-ε, ε]
    let v := inverseTwo a d
    weightedNewtonTail 3 a v = d ∧ (∀ i, |d i| = ε) ∧
      v 1 = ε * highestRowSum a ∧ |v 1| = ε * highestRowSum a := by
  dsimp only
  have hhigh : inverseTwo a ![-ε, ε] 1 = ε * highestRowSum a := by
    rw [highestRowSum_formula a ha]
    change (cubicFirst a * ε - cubicSecond a * (-ε)) / samplingDet a = _
    ring
  refine ⟨(weightedNewtonTail_two_inverse a ha).2 _, ?_, hhigh, ?_⟩
  · intro i
    fin_cases i
    · change |-ε| = ε
      rw [abs_neg, abs_of_nonneg hε]
    · change |ε| = ε
      exact abs_of_nonneg hε
  · have hrow : 0 ≤ highestRowSum a := add_nonneg (abs_nonneg _) (abs_nonneg _)
    rw [hhigh, abs_of_nonneg (mul_nonneg hε hrow)]

/-- The exact scalar maximum over the sup-norm ball of actual Newton data. -/
theorem highestCoefficient_worst_case (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i)
    (ε : ℝ) (hε : 0 ≤ ε) :
    IsGreatest {r : ℝ | ∃ v : Fin 2 → ℝ,
      ‖weightedNewtonTail 3 a v‖ ≤ ε ∧ r = |v 1|} (ε * highestRowSum a) := by
  obtain ⟨hd, hs, _, hv⟩ := highestCoefficient_attained a ha ε hε
  constructor
  · refine ⟨inverseTwo a ![-ε, ε], ?_, hv.symm⟩
    rw [hd]
    apply (pi_norm_le_iff_of_nonneg hε).mpr
    intro i
    simpa only [Real.norm_eq_abs, hs i] using (le_refl ε)
  · rintro r ⟨v, hv, rfl⟩
    apply highestCoefficient_bound a ha v ε
    intro i
    simpa only [Real.norm_eq_abs] using (pi_norm_le_iff_of_nonneg hε).mp hv i

open Set
open scoped BigOperators ContDiff Matrix.Norms.L2Operator RealInnerProductSpace

open ConfluentHermiteObservation ConfluentPositiveSampling

local notation "Mat₂" => Matrix (Fin 2) (Fin 2) ℝ

/-- The highest inverse row acting on the two positive-order matrix observations. -/
@[expose] def recoverHighest (a : Fin 3 → ℝ) (d : Fin 2 → Mat₂) : Mat₂ :=
  highestWeight0 a • d 0 + highestWeight1 a • d 1

private theorem matrixHermiteTail_decompose {lo hi : ℝ} (hinterval : lo < hi)
    {a : Fin 3 → ℝ} (ha : ∀ i, a i ∈ Icc lo hi)
    (v : Fin 2 → Mat₂) (K : Mat₂) (F E : ℝ → Mat₂)
    (hF : EqOn F (fun x => K + x ^ 3 • v 0 + x ^ 4 • v 1 + E x) (Icc lo hi))
    (hE : ∀ i j, ContDiffOn ℝ 2 (fun x => E x i j) (Icc lo hi)) :
    matrixHermiteTail lo hi a F =
      (fun k => Matrix.of (fun i j => weightedNewtonTail 3 a (fun t => v t i j) k)) +
        matrixHermiteTail lo hi a E := by
  funext k
  apply Matrix.ext
  intro i j
  let u : Fin 2 → ℝ := fun t => v t i j
  let P : ℝ[X] := X ^ 3 * Polynomial.ofFn 2 u
  have hp (x : ℝ) : P.eval x = x ^ 3 * u 0 + x ^ 4 * u 1 := by
    dsimp only [P]
    rw [ofFn_eq_sum_monomial, Fin.sum_univ_two]
    simp [eval_monomial]
    ring
  have hP : ContDiffOn ℝ 2 (fun x => P.eval x) (Icc lo hi) := by
    simpa only [coe_aeval_eq_eval] using (P.contDiff_aeval (𝕜 := ℝ) 2).contDiffOn
  have hK : ContDiffOn ℝ 2 (fun _ : ℝ => K i j) (Icc lo hi) := contDiffOn_const
  have hentry : EqOn (fun x => F x i j)
      (fun x => K i j + P.eval x + E x i j) (Icc lo hi) := by
    intro x hx
    simpa only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hp, u, add_assoc] using
      congrArg (fun A : Mat₂ => A i j) (hF hx)
  change hermiteTail lo hi a (fun x => F x i j) k =
    weightedNewtonTail 3 a u k + hermiteTail lo hi a (fun x => E x i j) k
  rw [hermiteTail_congr ha hentry, hermiteTail_add hinterval ha (hK.add hP) (hE i j),
    hermiteTail_add hinterval ha hK hP, hermiteTail_const hinterval ha, zero_add,
    hermiteTail_weighted hinterval ha 3 u]
  rfl

/-- On the actual within-jet observations, subtracting the observed remainder gives the
quartic coefficient exactly. The constant is arbitrary and nodes may repeat. -/
private theorem matrixHermiteTail_recoverHighest {lo hi : ℝ} (hinterval : lo < hi)
    {a : Fin 3 → ℝ} (ha : ∀ i, a i ∈ Icc lo hi) (hpos : ∀ i, 0 < a i)
    (v : Fin 2 → Mat₂) (K : Mat₂) (F E : ℝ → Mat₂)
    (hF : EqOn F (fun x => K + x ^ 3 • v 0 + x ^ 4 • v 1 + E x) (Icc lo hi))
    (hE : ∀ i j, ContDiffOn ℝ 2 (fun x => E x i j) (Icc lo hi)) :
    recoverHighest a (matrixHermiteTail lo hi a F - matrixHermiteTail lo hi a E) = v 1 := by
  rw [matrixHermiteTail_decompose hinterval ha v K F E hF hE, add_sub_cancel_right]
  apply Matrix.ext
  intro i j
  exact (highestCoefficient_inverse a hpos
    (fun t => v t i j)).symm

/-- Linearity against finite scalar weights, used to test a matrix observation against
vectors. A single application of interpolant uniqueness handles every node multiplicity. -/
private theorem hermiteTail_sum_mul {ι : Type*} [Fintype ι]
    {lo hi : ℝ} (hinterval : lo < hi) {a : Fin 3 → ℝ} (ha : ∀ i, a i ∈ Icc lo hi)
    (c : ι → ℝ) (f : ι → ℝ → ℝ)
    (hf : ∀ i, ContDiffOn ℝ 2 (fun x => c i * f i x) (Icc lo hi))
    (k : Fin 2) :
    hermiteTail lo hi a (fun x => ∑ i, c i * f i x) k =
      ∑ i, c i * hermiteTail lo hi a (f i) k := by
  let s := prefixNodes a k.succ
  let P (i : ι) := interpolant s (fun x j => iteratedDerivWithin j (f i) (Icc lo hi) x)
  let Q : ℝ[X] := ∑ i, C (c i) * P i
  let J (x : ℝ) (j : ℕ) :=
    iteratedDerivWithin j (fun t => ∑ i, c i * f i t) (Icc lo hi) x
  have hspec (i : ι) := interpolant_spec s (fun x j => iteratedDerivWithin j (f i) (Icc lo hi) x)
  have hQ : IsInterpolant s J Q := by
    refine ⟨?_, ?_⟩
    · change (∑ i, C (c i) * P i).degree < (s.card : WithBot ℕ)
      refine (degree_sum_le _ _).trans_lt
        ((Finset.sup_lt_iff (WithBot.bot_lt_coe s.card)).mpr ?_)
      intro i _
      calc
        (C (c i) * P i).degree ≤ 0 + (P i).degree :=
          degree_mul_le_of_le degree_C_le le_rfl
        _ = (P i).degree := zero_add _
        _ < (s.card : WithBot ℕ) := (hspec i).1
    · intro x j hj
      have hx : x ∈ Icc lo hi := prefixNodes_mem ha k.succ x
        (Multiset.count_pos.mp ((Nat.zero_le j).trans_lt hj))
      have hj₂ : j ≤ 2 := by
        have hc := (Multiset.count_le_card x s).trans_eq (card_prefixNodes a k.succ)
        have hk := k.isLt
        change j < s.count x at hj
        rw [Fin.val_succ] at hc
        omega
      change iteratedDerivWithin j (fun t => ∑ i, c i * f i t) (Icc lo hi) x =
        (Polynomial.derivative^[j] Q).eval x
      dsimp only [Q]
      rw [iterate_derivative_sum, eval_finsetSum,
        iteratedDerivWithin_fun_sum hx (uniqueDiffOn_Icc hinterval)
          (fun i _ => (hf i x hx).of_le (Nat.cast_le.mpr hj₂))]
      apply Finset.sum_congr rfl
      intro i _
      rw [iteratedDerivWithin_const_mul_field, iterate_derivative_C_mul, eval_mul, eval_C]
      exact congrArg (fun t : ℝ => c i * t) ((hspec i).2 x j hj)
  change (interpolant s J).coeff (k.val + 1) = ∑ i, c i * (P i).coeff (k.val + 1)
  rw [(interpolant_spec s J).unique hQ]
  simp only [Q, finsetSum_coeff, coeff_C_mul]

/-- Blockwise operator-norm derivative budget, including the Hermite factorial. -/
private theorem norm_matrixHermiteTail_remainder {lo hi : ℝ} (hinterval : lo < hi)
    {a : Fin 3 → ℝ} (ha : ∀ i, a i ∈ Icc lo hi) (E : ℝ → Mat₂)
    (hE : ∀ i j, ContDiffOn ℝ 2 (fun x => E x i j) (Icc lo hi)) (B : Fin 2 → ℝ)
    (hB : ∀ k x, x ∈ Icc lo hi →
      let D : Mat₂ := fun i j =>
        iteratedDerivWithin (k.val + 1) (fun t => E t i j) (Icc lo hi) x
      ‖D‖ ≤ B k) (k : Fin 2) :
    ‖matrixHermiteTail lo hi a E k‖ ≤ B k / ((k.val + 1).factorial : ℝ) := by
  let n := k.val + 1
  let N := matrixHermiteTail lo hi a E k
  let D (x : ℝ) : Mat₂ := fun i j => iteratedDerivWithin n (fun t => E t i j) (Icc lo hi) x
  have hfac : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hBk : 0 ≤ B k := (norm_nonneg (D lo)).trans (hB k lo ⟨le_rfl, hinterval.le⟩)
  change ‖N‖ ≤ B k / (n.factorial : ℝ)
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hBk hfac.le) fun z => ?_
  let u := Matrix.toEuclideanCLM (𝕜 := ℝ) N z
  change ‖u‖ ≤ (B k / (n.factorial : ℝ)) * ‖z‖
  by_cases hu : u = 0
  · rw [hu, norm_zero]
    exact mul_nonneg (div_nonneg hBk hfac.le) (norm_nonneg z)
  let c (p : Fin 2 × Fin 2) := u.ofLp p.1 * z.ofLp p.2
  let f (p : Fin 2 × Fin 2) (x : ℝ) := E x p.1 p.2
  let g (x : ℝ) := ∑ p, c p * f p x
  have hf (p : Fin 2 × Fin 2) : ContDiffOn ℝ 2 (fun x => c p * f p x) (Icc lo hi) :=
    contDiffOn_const.mul (hE p.1 p.2)
  have hg : ContDiffOn ℝ 2 g (Icc lo hi) := ContDiffOn.sum fun p _ => hf p
  have hpair (A : Mat₂) :
      ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) A z⟫ = ∑ p, c p * A p.1 p.2 := by
    rw [Matrix.inner_toEuclideanCLM, Fintype.sum_prod_type]
    simp only [dotProduct, Matrix.mulVec_apply_eq_sum, Finset.mul_sum, c]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hcoeff : hermiteTail lo hi a g k = ⟪u, u⟫ := by
    change hermiteTail lo hi a g k = ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) N z⟫
    rw [hpair, hermiteTail_sum_mul hinterval ha c f hf k] <;> rfl
  have hjet (x : ℝ) (hx : x ∈ Icc lo hi) :
      iteratedDerivWithin n g (Icc lo hi) x = ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (D x) z⟫ := by
    dsimp only [g]
    rw [iteratedDerivWithin_fun_sum hx (uniqueDiffOn_Icc hinterval)
      (fun p _ => (hf p x hx).of_le (Nat.cast_le.mpr k.isLt)), hpair]
    simp only [iteratedDerivWithin_const_mul_field, f, D, n, Nat.succ_eq_add_one]
  have hcard : (prefixNodes a k.succ).card = n + 1 := by
    simpa only [n, Fin.val_succ] using card_prefixNodes a k.succ
  obtain ⟨x, hx, hmean⟩ := prefix_mean hcard hinterval (prefixNodes_mem ha k.succ)
    (hg.of_le (Nat.cast_le.mpr k.isLt))
  change (n.factorial : ℝ) * hermiteTail lo hi a g k = iteratedDerivWithin n g (Icc lo hi) x at hmean
  rw [hcoeff, real_inner_self_eq_norm_sq, hjet x hx] at hmean
  have hmul : (n.factorial : ℝ) * ‖u‖ ^ 2 ≤ ‖u‖ * (B k * ‖z‖) := by
    calc
      _ = ‖⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) (D x) z⟫‖ := by
        rw [← hmean, Real.norm_of_nonneg (mul_nonneg hfac.le (sq_nonneg ‖u‖))]
      _ ≤ ‖u‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (D x) z‖ := norm_inner_le_norm _ _
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg u)
        have hDx : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (D x)‖ ≤ B k := by
          rw [Matrix.l2_opNorm_toEuclideanCLM]
          exact hB k x hx
        exact ((Matrix.toEuclideanCLM (𝕜 := ℝ) (D x)).le_opNorm z).trans
          (mul_le_mul_of_nonneg_right hDx (norm_nonneg z))
  have hc : (n.factorial : ℝ) * ‖u‖ ≤ B k * ‖z‖ := by
    apply le_of_mul_le_mul_left _ (norm_pos_iff.mpr hu)
    calc
      ‖u‖ * ((n.factorial : ℝ) * ‖u‖) = (n.factorial : ℝ) * ‖u‖ ^ 2 := by ring
      _ ≤ _ := hmul
  calc
    ‖u‖ ≤ B k * ‖z‖ / (n.factorial : ℝ) :=
      (le_div_iff₀ hfac).mpr (by simpa only [mul_comm] using hc)
    _ = _ := by ring

/-- The quartic coefficient error from direct Hermite data error and a smooth interval
remainder. Both budgets propagate through the same signed highest inverse row. -/
theorem matrixHermiteTail_highest_error {lo hi : ℝ} (hinterval : lo < hi)
    {a : Fin 3 → ℝ} (ha : ∀ i, a i ∈ Icc lo hi) (hpos : ∀ i, 0 < a i)
    (v : Fin 2 → Mat₂) (K : Mat₂) (F E : ℝ → Mat₂)
    (hF : EqOn F (fun x => K + x ^ 3 • v 0 + x ^ 4 • v 1 + E x) (Icc lo hi))
    (hE : ∀ i j, ContDiffOn ℝ 2 (fun x => E x i j) (Icc lo hi)) (B : Fin 2 → ℝ)
    (hB : ∀ k x, x ∈ Icc lo hi →
      let D : Mat₂ := fun i j =>
        iteratedDerivWithin (k.val + 1) (fun t => E t i j) (Icc lo hi) x
      ‖D‖ ≤ B k)
    (d : Fin 2 → Mat₂) (ε : ℝ) (hd : ‖d - matrixHermiteTail lo hi a F‖ ≤ ε) :
    ‖recoverHighest a d - v 1‖ ≤
      ε * highestRowSum a + (|highestWeight0 a| * B 0 + |highestWeight1 a| * (B 1 / 2)) := by
  let Y := matrixHermiteTail lo hi a F
  let N := matrixHermiteTail lo hi a E
  have herror : recoverHighest a d - v 1 = recoverHighest a (d - Y + N) := by
    rw [← matrixHermiteTail_recoverHighest hinterval ha hpos v K F E hF hE]
    simp only [recoverHighest, Y, N, Pi.add_apply, Pi.sub_apply, smul_add, smul_sub]
    abel
  have hbudget (k : Fin 2) : ‖(d - Y + N) k‖ ≤ ε + B k / ((k.val + 1).factorial : ℝ) :=
    (norm_add_le ((d - Y) k) (N k)).trans (add_le_add
      ((norm_le_pi_norm (d - Y) k).trans hd)
      (norm_matrixHermiteTail_remainder hinterval ha E hE B hB k))
  rw [herror]
  calc
    _ ≤ |highestWeight0 a| * ‖(d - Y + N) 0‖ + |highestWeight1 a| * ‖(d - Y + N) 1‖ := by
      simpa only [recoverHighest, Real.norm_eq_abs, norm_smul] using
        norm_add_le (highestWeight0 a • (d - Y + N) 0) (highestWeight1 a • (d - Y + N) 1)
    _ ≤ |highestWeight0 a| * (ε + B 0 / (((0 : Fin 2).val + 1).factorial : ℝ)) +
        |highestWeight1 a| * (ε + B 1 / (((1 : Fin 2).val + 1).factorial : ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left (hbudget 0) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (hbudget 1) (abs_nonneg _))
    _ = _ := by
      have h0 : ((0 : Fin 2).val + 1).factorial = 1 := rfl
      have h1 : ((1 : Fin 2).val + 1).factorial = 2 := rfl
      norm_num [h0, h1, highestRowSum]
      ring

/-- The sign-saturated rank-one direction attains the direct data error bound at
each positive node tuple, with any prescribed nuisance constant. -/
theorem matrixHermiteTail_highest_attained {lo hi : ℝ} (hinterval : lo < hi)
    {a : Fin 3 → ℝ} (ha : ∀ i, a i ∈ Icc lo hi) (hpos : ∀ i, 0 < a i)
    (K : Mat₂) (ε : ℝ) (hε : 0 ≤ ε) :
    let sample := fun F => matrixHermiteTail lo hi a F
    ∃ P : Mat₂, P.rank = 1 ∧ ‖P‖ = 1 ∧
      ∃ v : Fin 2 → Mat₂,
        (let Y := sample (fun x => K + x ^ 3 • v 0 + x ^ 4 • v 1)
         Y = (fun k => (![-ε, ε] : Fin 2 → ℝ) k • P) ∧ ‖(0 : Fin 2 → Mat₂) - Y‖ = ε) ∧
        v 1 = (ε * highestRowSum a) • P ∧
        ‖recoverHighest a (0 : Fin 2 → Mat₂) - v 1‖ = ε * highestRowSum a := by
  classical
  let P : Mat₂ := Matrix.diagonal (Pi.single (0 : Fin 2) (1 : ℝ))
  have hrank : P.rank = 1 := by
    dsimp only [P]
    rw [Matrix.rank_diagonal, Fintype.card_eq_one_iff]
    refine ⟨⟨0, by simp⟩, fun j => Subtype.ext ?_⟩
    change j.val = (0 : Fin 2)
    by_contra hj
    exact j.property (by simp [Pi.single, Function.update, hj, Ne.symm hj])
  have hP : ‖P‖ = 1 := by
    dsimp only [P]
    rw [Matrix.l2_opNorm_diagonal, Pi.norm_single, norm_one]
  let d : Fin 2 → ℝ := ![-ε, ε]
  let u := inverseTwo a d
  obtain ⟨hu, hd, hhigh, habs⟩ := highestCoefficient_attained a
    hpos ε hε
  change weightedNewtonTail 3 a u = d at hu
  change ∀ k, |d k| = ε at hd
  change u 1 = ε * highestRowSum a at hhigh
  change |u 1| = ε * highestRowSum a at habs
  let v : Fin 2 → Mat₂ := fun k => u k • P
  let F (x : ℝ) := K + x ^ 3 • v 0 + x ^ 4 • v 1
  have hF : EqOn F (fun x => K + x ^ 3 • v 0 + x ^ 4 • v 1 + (0 : Mat₂)) (Icc lo hi) :=
    fun x _ => (add_zero (F x)).symm
  have hY : matrixHermiteTail lo hi a F = fun k => d k • P := by
    rw [matrixHermiteTail_decompose hinterval ha v K F (fun _ => 0) hF
      (fun _ _ => contDiffOn_const)]
    funext k
    apply Matrix.ext
    intro i j
    change weightedNewtonTail 3 a (fun t => u t * P i j) k +
      hermiteTail lo hi a (fun _ => (0 : ℝ)) k = d k * P i j
    rw [hermiteTail_const hinterval ha, Pi.zero_apply, add_zero, ← congrFun hu k]
    have he : (fun t => u t * P i j) = P i j • u := funext fun t => mul_comm _ _
    rw [he, map_smul]
    exact mul_comm _ _
  refine ⟨P, hrank, hP, v, ⟨hY, ?_⟩, ?_, ?_⟩
  · change ‖(0 : Fin 2 → Mat₂) - matrixHermiteTail lo hi a F‖ = ε
    rw [zero_sub, norm_neg]
    have hs (k : Fin 2) : ‖matrixHermiteTail lo hi a F k‖ = ε := by
      rw [hY, norm_smul, Real.norm_eq_abs, hd, hP, mul_one]
    exact le_antisymm ((pi_norm_le_iff_of_nonneg hε).mpr fun k => (hs k).le)
      ((hs 0).ge.trans (norm_le_pi_norm _ 0))
  · change u 1 • P = _
    rw [hhigh]
  · have hv : ‖v 1‖ = ε * highestRowSum a := by
      change ‖u 1 • P‖ = _
      rw [norm_smul, Real.norm_eq_abs, habs, hP, mul_one]
    simpa [recoverHighest] using hv

end D5.S3.Analytic.Interpolation.HermiteHighestCoefficient
