import D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBPolynomialFromInfinity
import D5.S3.VertexAlgebra.CollisionLaurentKernels

/-! Restore the two independent coordinates of the marked HHBB amplitude. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators TensorProduct Topology VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBTwoVariableRational

open ActualLeechHyperbolic (leechData)
open ActualChargedAdjoint (actualForm)
open LatticeHalfFockCorrectedField (correctedField)
open LatticeHalfFockGradedTrace (actualGrade)
open LatticeHalfFockChargedTensorCoefficients (ActualGround)
open Orbifold.NativeOddTwistedIntertwiner (TwistedEven TwistedOdd leechUnit)
open Orbifold.NativeFixedPairField (nu)
open Orbifold.NativeMixedPairField (mu)
open Orbifold.NativeOddUpperRightSkew (rightField)
open NativeFixedPairFourPoint (nu_fourPoint_off_right_grade)
open NativeFixedPairAIterate (fixedAExponent)
open NativeMixedWickChartTransport (MixedParity doubledOccupation)
open NativeMixedComplexSewing (aJointTerm)
open NativeMixedUpperProductCusp (bJointTerm b_inner_coeff_off_grid)
open NativeHHBBPolynomialFromInfinity (hhbb_marked_upper_common_rational)
open OriginalFourMActualChart (Puncture)
open OriginalFourMVariableSupport (wordAt)
open CollisionLaurentKernels.LaurentCollision (Bivariate Rational)

open private occupationGrade_eq from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedPhysicalOverlap
open private b_inner_energy b_outer_pairing_off_grid punctureExcitation_cast wordAt_grade from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedUpperProductCusp
open private pair_off_energy from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeFourHRealSewing

local notation "ℒ" => leechData
local notation "xPoly" => (Polynomial.C (Polynomial.X : Polynomial ℂ))
local notation "zPoly" => (Polynomial.X : Bivariate ℂ)

/-- The homogeneous numerator, with `x` in the coefficient ring and `z` in the outer ring. -/
def homogenizedNumerator (P : Polynomial ℂ) (degree : ℕ) : Bivariate ℂ :=
  ∑ j ∈ Finset.range (degree + 1),
    Polynomial.C (Polynomial.C (P.coeff j)) * xPoly ^ (degree - j) * zPoly ^ j

/-- The three pole bounds depend only on the inserted states' grades. -/
def denominator (M K L : ℕ) : Bivariate ℂ :=
  xPoly ^ ((M + L + 7) / 2) * zPoly ^ ((5 + K + L) / 2) * (xPoly - zPoly) ^ ((6 + M + K) / 2)

/-- The normalized HHBB rational function in the collision theorem's field. -/
def commonRational (P : Polynomial ℂ) (degree M K L : ℕ) : Rational ℂ :=
  algebraMap (Bivariate ℂ) (Rational ℂ) (homogenizedNumerator P degree) /
    algebraMap (Bivariate ℂ) (Rational ℂ) (denominator M K L)

/-- Evaluate the bivariate polynomial at the two labelled coordinates. -/
def evalAt (x z : ℂ) : Bivariate ℂ →+* ℂ :=
  Polynomial.eval₂RingHom (Polynomial.evalRingHom x) z

theorem evalAt_homogenizedNumerator (P : Polynomial ℂ) (degree : ℕ) (x z : ℂ) :
    evalAt x z (homogenizedNumerator P degree) =
      ∑ j ∈ Finset.range (degree + 1), P.coeff j * x ^ (degree - j) * z ^ j := by
  simp only [homogenizedNumerator, evalAt, map_sum, map_mul, map_pow,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Polynomial.coe_evalRingHom, Polynomial.eval_C, Polynomial.eval_X]

theorem evalAt_denominator (M K L : ℕ) (x z : ℂ) :
    evalAt x z (denominator M K L) =
      x ^ ((M + L + 7) / 2) * z ^ ((5 + K + L) / 2) * (x - z) ^ ((6 + M + K) / 2) := by
  simp only [denominator, evalAt, map_mul, map_pow, map_sub,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Polynomial.coe_evalRingHom, Polynomial.eval_X]

theorem evalAt_denominator_ne_zero (M K L : ℕ) {x z : ℂ}
    (hx : x ≠ 0) (hz : z ≠ 0) (hxz : x ≠ z) :
    evalAt x z (denominator M K L) ≠ 0 := by
  rw [evalAt_denominator]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hx) (pow_ne_zero _ hz))
    (pow_ne_zero _ (sub_ne_zero.mpr hxz))

theorem commonRational_mul_denominator (P : Polynomial ℂ) (degree M K L : ℕ) :
    commonRational P degree M K L * algebraMap (Bivariate ℂ) (Rational ℂ) (denominator M K L) =
      algebraMap (Bivariate ℂ) (Rational ℂ) (homogenizedNumerator P degree) := by
  have hden : denominator M K L ≠ 0 := by
    intro h
    exact evalAt_denominator_ne_zero M K L (x := 1) (z := 2)
      (by norm_num) (by norm_num) (by norm_num) (by rw [h, map_zero])
  apply div_mul_cancel₀
  simpa only [map_zero] using (IsFractionRing.injective (Bivariate ℂ) (Rational ℂ)).ne hden

private theorem evalAt_homogenizedNumerator_div (P : Polynomial ℂ) {degree : ℕ}
    (hP : P.natDegree ≤ degree) {x z : ℂ} (hx : x ≠ 0) :
    evalAt x z (homogenizedNumerator P degree) = x ^ degree * P.eval (z / x) := by
  rw [evalAt_homogenizedNumerator, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hP),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hle : j ≤ degree := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hpow : x ^ degree = x ^ (degree - j) * x ^ j := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [hpow, div_pow]
  field_simp [pow_ne_zero j hx]

private theorem degree_balance {M K L N : ℕ}
    (hM : (M : ℤ) % 2 = 0) (hK : (K : ℤ) % 2 = 0)
    (hL : (L : ℤ) % 2 = 1) (hN : (N : ℤ) % 2 = 1) :
    let a : ℕ := (5 + K + L) / 2
    let b : ℕ := (6 + M + K) / 2
    let c : ℕ := (M + L + 7) / 2
    let degree : ℕ := (12 + M + K + L + N) / 2
    let e : ℤ := (N : ℤ) - M - K - L - 6
    e = 2 * (e / 2) ∧ e / 2 + a + b + c = (degree : ℤ) := by
  dsimp only
  push_cast
  omega

private theorem evaluate_homogeneous (P : Polynomial ℂ) {M K L N : ℕ}
    (hM : (M : ℤ) % 2 = 0) (hK : (K : ℤ) % 2 = 0)
    (hL : (L : ℤ) % 2 = 1) (hN : (N : ℤ) % 2 = 1)
    (hP : P.natDegree ≤ (12 + M + K + L + N) / 2)
    {x z : ℂ} (hx : x ≠ 0) (hz : z ≠ 0) (hxz : x ≠ z) :
    let e : ℤ := (N : ℤ) - M - K - L - 6
    let y := z / x
    x ^ (e / 2) * (P.eval y / (y ^ ((5 + K + L) / 2) * (1 - y) ^ ((6 + M + K) / 2))) =
      evalAt x z (homogenizedNumerator P ((12 + M + K + L + N) / 2)) /
        evalAt x z (denominator M K L) := by
  intro e y
  let a : ℕ := (5 + K + L) / 2
  let b : ℕ := (6 + M + K) / 2
  let c : ℕ := (M + L + 7) / 2
  let degree : ℕ := (12 + M + K + L + N) / 2
  have hbalance : e / 2 + a + b + c = (degree : ℤ) :=
    (degree_balance hM hK hL hN).2
  rw [evalAt_homogenizedNumerator_div P hP hx, evalAt_denominator]
  change x ^ (e / 2) * (P.eval y / (y ^ a * (1 - y) ^ b)) =
    (x ^ degree * P.eval y) / (x ^ c * z ^ a * (x - z) ^ b)
  have hy : 1 - y = (x - z) / x := by
    dsimp only [y]
    rw [sub_div, div_self hx]
  have hpow : x ^ (e / 2) * x ^ a * x ^ b * x ^ c = x ^ degree := by
    rw [← zpow_natCast x a, ← zpow_natCast x b, ← zpow_natCast x c, ← zpow_natCast x degree]
    rw [← zpow_add₀ hx, ← zpow_add₀ hx, ← zpow_add₀ hx, hbalance]
  rw [← hpow, hy]
  dsimp only [y]
  rw [div_pow, div_pow]
  have ha := pow_ne_zero a hz
  have hb := pow_ne_zero b (sub_ne_zero.mpr hxz)
  field_simp [pow_ne_zero a hx, pow_ne_zero b hx, pow_ne_zero c hx]

/-- The actual B matrix entry has total doubled mode fixed by energy. This also
applies to the exchanged D matrix entry by interchanging the two H states. -/
theorem bJointTerm_off_total (M K L N : ℕ)
    (u v : TwistedEven) (w b : TwistedOdd)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (hw : w.val ∈ actualGrade ℒ leechUnit L) (hb : b.val ∈ actualGrade ℒ leechUnit N)
    (hKL : Odd ((K : ℤ) + L))
    (X Z : ℂ) (i : ℤ × ℤ) (hi : i.1 + i.2 ≠ (N : ℤ) - M - K - L - 6) :
    bJointTerm false false v w u b X Z i = 0 := by
  rcases i with ⟨j, e⟩
  by_cases hj : ∃ E : ℕ, j = 2 * (E : ℤ) - (6 + (K : ℤ) + L)
  · obtain ⟨E, rfl⟩ := hj
    have he : e ≠ (N : ℤ) - M - 2 * (E : ℤ) := by
      intro he
      apply hi
      dsimp
      omega
    have hgrade := b_inner_energy false K L E v w hv hw hKL
    have hout := b_outer_pairing_off_grid false M N E u b hu hb
      ((mu false v).coeff (2 * (E : ℤ) - (6 + (K : ℤ) + L)) w) hgrade e he
    unfold bJointTerm
    rw [hout, zero_mul]
  · have hinner := b_inner_coeff_off_grid false K L v w hv hw hKL j (fun E h => hj ⟨E, h⟩)
    simp [bJointTerm, hinner]

/-- The actual A matrix entry has the same total doubled mode as B and D. -/
theorem aJointTerm_off_total (M K L N : ℕ)
    (u v : TwistedEven) (w b : TwistedOdd)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (hw : w.val ∈ actualGrade ℒ leechUnit L) (hb : b.val ∈ actualGrade ℒ leechUnit N)
    (hM : Even M) (hK : Even K)
    (D Z : ℂ) (i : ℤ × ℤ) (hi : i.1 + i.2 ≠ (N : ℤ) - M - K - L - 6) :
    aJointTerm u v w b D Z i = 0 := by
  rcases i with ⟨j, e⟩
  by_cases hj : ∃ E : ℕ, j = fixedAExponent M K E
  · obtain ⟨E, rfl⟩ := hj
    have he : e ≠ (N : ℤ) - L - 2 * (E : ℤ) := by
      intro he
      apply hi
      dsimp [fixedAExponent]
      omega
    let m : ℤ := ((M : ℤ) + K + 4) / 2 - E
    obtain ⟨m₀, hm₀⟩ := hM
    obtain ⟨k₀, hk₀⟩ := hK
    have hE : 2 * (E : ℤ) = (M : ℤ) + K + 4 - 2 * m := by
      dsimp only [m]
      omega
    have hmode : fixedAExponent M K E = -2 * m - 2 := by
      unfold fixedAExponent
      omega
    unfold aJointTerm
    rw [hmode, nu_fourPoint_off_right_grade false M K L N m (E : ℤ) e
      u v w.val b.val hu hv hw hb hE he, zero_mul]
  · have hpair := pair_off_energy M K u v hu hv j (fun E h => hj ⟨E, h⟩)
    simp [aJointTerm, hpair]

private theorem scale_modes {X : ℂ} (hX : X ≠ 0) (r s : ℂ) {i : ℤ × ℤ} {e : ℤ}
    (hi : i.1 + i.2 = e) :
    (X * r) ^ i.1 * (X * s) ^ i.2 = X ^ e * (r ^ i.1 * s ^ i.2) := by
  rw [mul_zpow, mul_zpow, ← hi, zpow_add₀ hX]
  ring

private theorem bJointTerm_scale (M K L N : ℕ)
    (u v : TwistedEven) (w b : TwistedOdd)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (hw : w.val ∈ actualGrade ℒ leechUnit L) (hb : b.val ∈ actualGrade ℒ leechUnit N)
    (hKL : Odd ((K : ℤ) + L)) {X : ℂ} (hX : X ≠ 0) (r s : ℂ) (i : ℤ × ℤ) :
    bJointTerm false false v w u b (X * r) (X * s) i =
      X ^ ((N : ℤ) - M - K - L - 6) * bJointTerm false false v w u b r s i := by
  by_cases hi : i.1 + i.2 = (N : ℤ) - M - K - L - 6
  · simp only [bJointTerm, scale_modes hX s r hi]
    ring
  · rw [bJointTerm_off_total M K L N u v w b hu hv hw hb hKL _ _ i hi,
      bJointTerm_off_total M K L N u v w b hu hv hw hb hKL _ _ i hi, mul_zero]

private theorem aJointTerm_scale (M K L N : ℕ)
    (u v : TwistedEven) (w b : TwistedOdd)
    (hu : u.val ∈ actualGrade ℒ leechUnit M) (hv : v.val ∈ actualGrade ℒ leechUnit K)
    (hw : w.val ∈ actualGrade ℒ leechUnit L) (hb : b.val ∈ actualGrade ℒ leechUnit N)
    (hM : Even M) (hK : Even K) {X : ℂ} (hX : X ≠ 0) (r s : ℂ) (i : ℤ × ℤ) :
    aJointTerm u v w b (X * r) (X * s) i =
      X ^ ((N : ℤ) - M - K - L - 6) * aJointTerm u v w b r s i := by
  by_cases hi : i.1 + i.2 = (N : ℤ) - M - K - L - 6
  · simp only [aJointTerm, scale_modes hX r s hi]
    ring
  · rw [aJointTerm_off_total M K L N u v w b hu hv hw hb hM hK _ _ i hi,
      aJointTerm_off_total M K L N u v w b hu hv hw hb hM hK _ _ i hi, mul_zero]

open private sqrt_square zpow_double from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedComplexSewing

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
/-- The actual normalized HHBB terms have a common homogeneous rational value
with pole bounds uniform in the detector grade. Raw B contributes its negative,
while A and the exchanged product D contribute its positive value. -/
theorem hhbb_marked_two_variable_common_rational {ι : Type*} [Finite ι]
    (slot : ι → Puncture) (colour : ι → Fin leechData.rank) (n : ι → ℕ) (l : List ι)
    (hl : l.Nodup) (hpar : MixedParity slot n l)
    (u v : TwistedEven) (w b : TwistedOdd) (p q r d : ActualGround ℒ leechUnit)
    (hu : u.val = wordAt ℒ slot colour n l .P ⊗ₜ[ℂ] p)
    (hv : v.val = wordAt ℒ slot colour n l .Q ⊗ₜ[ℂ] q)
    (hw : w.val = wordAt ℒ slot colour n l .R ⊗ₜ[ℂ] r)
    (hb : b.val = wordAt ℒ slot colour n l .S ⊗ₜ[ℂ] d) :
    let grade (i : Puncture) := (doubledOccupation slot n l i).toNat
    let M := grade .P
    let K := grade .Q
    let L := grade .R
    let N := grade .S
    let a : ℕ := (5 + K + L) / 2
    let b₁ : ℕ := (6 + M + K) / 2
    let degree : ℕ := (12 + M + K + L + N) / 2
    let e : ℤ := (N : ℤ) - M - K - L - 6
    ∃ P : Polynomial ℂ, P.natDegree ≤ degree ∧
      let value (x z : ℂ) := evalAt x z (homogenizedNumerator P degree) /
        evalAt x z (denominator M K L)
      (∀ x z : ℂ, x ≠ 0 → z ≠ 0 → x ≠ z →
        x ^ (e / 2) * (P.eval (z / x) / ((z / x) ^ a * (1 - z / x) ^ b₁)) =
          value x z) ∧
      ∀ X Z : ℂ, X ≠ 0 →
        let x := X ^ (2 : ℕ)
        let z := Z ^ (2 : ℕ)
        let y := z / x
        0 < y.im → Z / X = Complex.sqrt y →
        evalAt x z (denominator M K L) ≠ 0 ∧
        (y ∈ Metric.ball (0 : ℂ) 1 →
          HasSum (fun i => (Z / X) * bJointTerm false false v w u b X Z i) (-(value x z))) ∧
        (∀ D : ℂ, D / X = Complex.sqrt (1 - y) → (1 / 2 : ℝ) < y.re →
          D ^ (2 : ℕ) = x - z ∧
          HasSum (fun i => (Z / X) * aJointTerm u v w b D Z i) (value x z)) ∧
        (1 < ‖y‖ →
          HasSum (fun i => (Z / X) * bJointTerm false false u w v b Z X i) (value x z)) := by
  intro grade M K L N a b₁ degree e
  have ⟨hP, _, _, hB, hA, hD⟩ :=
    hhbb_marked_upper_common_rational slot colour n l hl hpar u v w b p q r d hu hv hw hb
  have hgrade (i : Puncture) : (grade i : ℤ) = doubledOccupation slot n l i := by
    change (((doubledOccupation slot n l i).toNat : ℕ) : ℤ) = _
    rw [occupationGrade_eq slot colour n l i, punctureExcitation_cast]
  have hM : (M : ℤ) % 2 = 0 := by simpa only [M, hgrade] using hpar.1
  have hK : (K : ℤ) % 2 = 0 := by simpa only [K, hgrade] using hpar.2.1
  have hL : (L : ℤ) % 2 = 1 := by simpa only [L, hgrade] using hpar.2.2.1
  have hN : (N : ℤ) % 2 = 1 := by simpa only [N, hgrade] using hpar.2.2.2
  have hMe : Even M := (Int.even_coe_nat M).mp (Int.even_iff.mpr hM)
  have hKe : Even K := (Int.even_coe_nat K).mp (Int.even_iff.mpr hK)
  have hKL : Odd ((K : ℤ) + L) := Int.odd_iff.mpr (by omega)
  have hML : Odd ((M : ℤ) + L) := Int.odd_iff.mpr (by omega)
  have huGrade : u.val ∈ actualGrade ℒ leechUnit M := by
    rw [hu, show M = _ from occupationGrade_eq slot colour n l .P]
    exact wordAt_grade slot colour n l .P p
  have hvGrade : v.val ∈ actualGrade ℒ leechUnit K := by
    rw [hv, show K = _ from occupationGrade_eq slot colour n l .Q]
    exact wordAt_grade slot colour n l .Q q
  have hwGrade : w.val ∈ actualGrade ℒ leechUnit L := by
    rw [hw, show L = _ from occupationGrade_eq slot colour n l .R]
    exact wordAt_grade slot colour n l .R r
  have hbGrade : b.val ∈ actualGrade ℒ leechUnit N := by
    rw [hb, show N = _ from occupationGrade_eq slot colour n l .S]
    exact wordAt_grade slot colour n l .S d
  refine ⟨_, hP, ?_⟩
  intro value
  have hEval {x z : ℂ} (hx : x ≠ 0) (hz : z ≠ 0) (hxz : x ≠ z) :=
    evaluate_homogeneous _ hM hK hL hN hP hx hz hxz
  refine ⟨fun x z hx hz hxz => hEval hx hz hxz, ?_⟩
  intro X Z hX x z y hy hZ
  have hx : x ≠ 0 := pow_ne_zero _ hX
  have hy₀ : y ≠ 0 := by
    intro h
    rw [h] at hy
    simp at hy
  have hy₁ : y ≠ 1 := by
    intro h
    rw [h] at hy
    simp at hy
  have hz : z ≠ 0 := by
    intro h
    exact hy₀ (by simp [y, h])
  have hxz : x ≠ z := by
    intro h
    exact hy₁ (by simp [y, ← h, hx])
  have hRoot : Complex.sqrt y ≠ 0 := by
    intro h
    exact hy₀ (by rw [← sqrt_square y, h, zero_pow (by decide : (2 : ℕ) ≠ 0)])
  have hZroot : Z = X * Complex.sqrt y := by
    rw [mul_comm]
    exact (div_eq_iff hX).mp hZ
  have hscale : X ^ e = x ^ (e / 2) := calc
    X ^ e = X ^ (2 * (e / 2)) :=
      congrArg (fun k : ℤ => X ^ k) (degree_balance hM hK hL hN).1
    _ = x ^ (e / 2) := zpow_double X (e / 2)
  have hNormalize (numerator : ℂ) :
      (Z / X) * (X ^ e * (numerator / (Complex.sqrt y * y ^ a * (1 - y) ^ b₁))) =
        x ^ (e / 2) * (numerator / (y ^ a * (1 - y) ^ b₁)) := by
    rw [hZ, hscale]
    have ha := pow_ne_zero a hy₀
    have hb₁ := pow_ne_zero b₁ (sub_ne_zero.mpr hy₁.symm)
    field_simp
  refine ⟨evalAt_denominator_ne_zero M K L hx hz hxz, ?_, ?_, ?_⟩
  · intro hball
    have hScaled := ((hB y hball hy).mul_left (X ^ e)).congr_fun fun i => by
      simpa only [mul_one, ← hZroot] using
        bJointTerm_scale M K L N u v w b huGrade hvGrade hwGrade hbGrade hKL hX 1
          (Complex.sqrt y) i
    have hNormalized := hScaled.mul_left (Z / X)
    rw [mul_neg, mul_neg, hNormalize, hEval hx hz hxz] at hNormalized
    exact hNormalized
  · intro D hDroot hRight
    have hDmul : D = X * Complex.sqrt (1 - y) := by
      rw [mul_comm]
      exact (div_eq_iff hX).mp hDroot
    have hDsq : D ^ (2 : ℕ) = x - z := by
      rw [hDmul, mul_pow, sqrt_square]
      change x * (1 - z / x) = x - z
      rw [mul_sub, mul_one, ← mul_div_assoc, mul_div_cancel_left₀ _ hx]
    have hScaled := ((hA y hy hRight).mul_left (X ^ e)).congr_fun fun i => by
      simpa only [← hDmul, ← hZroot] using
        aJointTerm_scale M K L N u v w b huGrade hvGrade hwGrade hbGrade hMe hKe hX
          (Complex.sqrt (1 - y)) (Complex.sqrt y) i
    have hNormalized := hScaled.mul_left (Z / X)
    rw [hNormalize, hEval hx hz hxz] at hNormalized
    exact ⟨hDsq, hNormalized⟩
  · intro hExterior
    have hScaled := ((hD y hy hExterior).mul_left (X ^ e)).congr_fun fun i => by
      have hSwap : (N : ℤ) - K - M - L - 6 = e := by dsimp only [e]; ring
      simpa only [mul_one, ← hZroot, hSwap] using
        bJointTerm_scale K M L N v u w b hvGrade huGrade hwGrade hbGrade hML hX
          (Complex.sqrt y) 1 i
    have hNormalized := hScaled.mul_left (Z / X)
    rw [hNormalize, hEval hx hz hxz] at hNormalized
    exact hNormalized

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeHHBBTwoVariableRational
