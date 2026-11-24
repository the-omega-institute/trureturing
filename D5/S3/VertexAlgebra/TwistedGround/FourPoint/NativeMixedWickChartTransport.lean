/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/NativeMixedWickChartTransport
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/NativeMixedWickChartTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Upper-branch chart phases and Fourier transport for two even and two odd occupations. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMNativeLaurent

/-! This is the scalar Gaussian conversion on the real overlap. Identifying
the physical coefficient with the corresponding analytic germ is a separate
problem. Anomaly identification also requires that physical comparison. -/

set_option autoImplicit false

noncomputable section
open scoped BigOperators Matrix

namespace D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedWickChartTransport

open Complex (I)
open LatticeGeneratingFieldLocality
open LatticeDiscriminantTheta (gramReal)
open LatticeTwistedGroundRealization.SignQuotient (ModTwoCharge)
open OriginalFourMChargeCoset (fourierSign quadraticSign)
open OriginalFourMActualChart
open OriginalFourMPhysicalCovariance (relative)
open OriginalFourMSpatialWickPartition (liftedScale)
open OriginalFourMVariableSupport
  (loweredOscillator nativePuncture nativeSector occupationReadout
    native_occupation_fourier_overlap)

variable {X : Type*}

open Classical in
/-- The doubled excitation at a physical puncture, with multiplicity from the
literal list of marks. A mode of index `n` has doubled excitation `2*n+1`. -/
def doubledOccupation (slot : X → Puncture) (n : X → ℕ) (l : List X)
    (i : Puncture) : ℤ :=
  (l.map fun j => if slot j = i then 2 * (n j : ℤ) + 1 else 0).sum

/-- P and Q are H, while R and S are B. -/
def MixedParity (slot : X → Puncture) (n : X → ℕ) (l : List X) : Prop :=
  doubledOccupation slot n l .P % 2 = 0 ∧ doubledOccupation slot n l .Q % 2 = 0 ∧
    doubledOccupation slot n l .R % 2 = 1 ∧ doubledOccupation slot n l .S % 2 = 1

/-- The actual product in the native occupation Fourier overlap. -/
def liftedProduct (slot : X → Puncture) (n : X → ℕ) (l : List X)
    (c : Chart) (y : ℝ) : ℂ :=
  (l.map fun j => liftedScale c y (slot j) (n j)).prod

private theorem liftedScale_zpow {y : ℝ} (hy : 0 < y) (hy₁ : y < 1)
    (c : Chart) (i : Puncture) (m : ℕ) :
    liftedScale c y i m =
      (relative c i * (scaleRoot c y i)⁻¹) ^ (2 * (m : ℤ) + 1) := by
  have hsign : relative c i ^ (2 : ℕ) = 1 := by
    cases c <;> cases i <;> norm_num [relative, relativeB, relativeD]
  have he : (2 * (m : ℤ) + 1) = ((2 * m + 1 : ℕ) : ℤ) := by
    push_cast
    rfl
  rw [he, zpow_natCast, liftedScale, ← (chosen_roots hy hy₁ c i).1, ← inv_pow,
    ← pow_mul, mul_pow, pow_add (relative c i), pow_mul (relative c i), hsign,
    one_pow, pow_one, one_mul, pow_add, pow_one]
  ac_rfl

private theorem scaleRoot_ne {y : ℝ} (hy : 0 < y) (hy₁ : y < 1)
    (c : Chart) (i : Puncture) : scaleRoot c y i ≠ 0 := by
  have h0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have h1 : (1 : ℂ) - y ≠ 0 := by exact_mod_cast (sub_pos.mpr hy₁).ne'
  have h1' : (y : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp h1).symm
  have hs : scale c y i ≠ 0 := by
    cases c <;> cases i <;> simp [scale, h0, h1, h1']
  exact fun h => hs ((chosen_roots hy hy₁ c i).1.symm.trans (by simp [h]))

private theorem liftedProduct_by_puncture {y : ℝ} (hy : 0 < y) (hy₁ : y < 1)
    (slot : X → Puncture) (n : X → ℕ) (l : List X) (c : Chart) :
    let f := fun i => relative c i * (scaleRoot c y i)⁻¹
    liftedProduct slot n l c y =
      f .P ^ doubledOccupation slot n l .P * f .Q ^ doubledOccupation slot n l .Q *
      f .R ^ doubledOccupation slot n l .R * f .S ^ doubledOccupation slot n l .S := by
  classical
  let f := fun i => relative c i * (scaleRoot c y i)⁻¹
  have hf (i : Puncture) : f i ≠ 0 := by
    apply mul_ne_zero _ (inv_ne_zero (scaleRoot_ne hy hy₁ c i))
    cases c <;> cases i <;> norm_num [relative, relativeB, relativeD]
  change liftedProduct slot n l c y =
    f .P ^ doubledOccupation slot n l .P * f .Q ^ doubledOccupation slot n l .Q *
    f .R ^ doubledOccupation slot n l .R * f .S ^ doubledOccupation slot n l .S
  induction l with
  | nil => simp [liftedProduct, doubledOccupation]
  | cons j l ih =>
      change liftedScale c y (slot j) (n j) * liftedProduct slot n l c y = _
      rw [liftedScale_zpow hy hy₁, ih]
      change f (slot j) ^ (2 * (n j : ℤ) + 1) * _ = _
      cases h : slot j <;>
        simp only [doubledOccupation, List.map_cons, List.sum_cons, h, reduceCtorEq,
          ite_true, ite_false, zero_add, zpow_add₀ (hf .P), zpow_add₀ (hf .Q),
          zpow_add₀ (hf .R), zpow_add₀ (hf .S)] <;>
        ring

private abbrev sqrtY (y : ℝ) : ℂ := Real.sqrt y
private abbrev sqrtOneSubY (y : ℝ) : ℂ := Real.sqrt (1-y)

private theorem sqrtY_ne {y : ℝ} (hy : 0 < y) : sqrtY y ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 hy).ne'

private theorem sqrtOneSubY_ne {y : ℝ} (hy₁ : y < 1) : sqrtOneSubY y ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (sub_pos.mpr hy₁)).ne'

private theorem sqrtY_sq {y : ℝ} (hy : 0 < y) : sqrtY y ^ (2 : ℕ) = (y : ℂ) := by
  exact_mod_cast Real.sq_sqrt hy.le

private theorem sqrtOneSubY_sq {y : ℝ} (hy₁ : y < 1) :
    sqrtOneSubY y ^ (2 : ℕ) = 1 - (y : ℂ) := by
  exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr hy₁.le)

private theorem localLift_table (y : ℝ) (c : Chart) :
    let f := fun i => relative c i * (scaleRoot c y i)⁻¹
    let t := sqrtY y
    let u := sqrtOneSubY y
    match c with
    | .A => f .P = u⁻¹ ∧ f .Q = I⁻¹ * u⁻¹ ∧ f .R = t⁻¹ ∧ f .S = t
    | .B => f .P = I⁻¹ ∧ f .Q = t⁻¹ ∧ f .R = I⁻¹ * t⁻¹ ∧ f .S = (-1) * I⁻¹
    | .D => f .P = 1 ∧ f .Q = (-1) * (I⁻¹ * t⁻¹) ∧
        f .R = (-1) * I⁻¹ ∧ f .S = I⁻¹ * t := by
  cases c <;> dsimp only
  · change 1 * (sqrtOneSubY y)⁻¹ = _ ∧ 1 * (I * sqrtOneSubY y)⁻¹ = _ ∧
      1 * (sqrtY y)⁻¹ = _ ∧ 1 * ((sqrtY y)⁻¹)⁻¹ = _
    simp only [one_mul, mul_inv, inv_inv, and_self]
  · change 1 * I⁻¹ = _ ∧ 1 * (sqrtY y)⁻¹ = _ ∧
      1 * (I * sqrtY y)⁻¹ = _ ∧ (-1) * I⁻¹ = _
    simp only [one_mul, mul_inv, and_self]
  · change (1 : ℂ) * (1 : ℂ)⁻¹ = _ ∧ (-1) * (I * sqrtY y)⁻¹ = _ ∧
      (-1) * I⁻¹ = _ ∧ 1 * (I / sqrtY y)⁻¹ = _
    simp only [one_mul, inv_one, div_eq_mul_inv, mul_inv, inv_inv, and_self]

/-- The three lifted-scale products in physical P,Q,R,S order, with
integer powers of the positive real square roots. -/
theorem liftedProduct_phases {y : ℝ} (hy : 0 < y) (hy₁ : y < 1)
    (slot : X → Puncture) (n : X → ℕ) (l : List X) :
    let M := doubledOccupation slot n l .P
    let K := doubledOccupation slot n l .Q
    let L := doubledOccupation slot n l .R
    let N := doubledOccupation slot n l .S
    let t : ℂ := Real.sqrt y
    let u : ℂ := Real.sqrt (1-y)
    liftedProduct slot n l .A y = I ^ (-K) * u ^ (-(M+K)) * t ^ (N-L) ∧
    liftedProduct slot n l .B y = (-1 : ℂ) ^ N * I ^ (-(M+L+N)) * t ^ (-(K+L)) ∧
    liftedProduct slot n l .D y = (-1 : ℂ) ^ (K+L) * I ^ (-(K+L+N)) * t ^ (N-K) := by
  let M := doubledOccupation slot n l .P
  let K := doubledOccupation slot n l .Q
  let L := doubledOccupation slot n l .R
  let N := doubledOccupation slot n l .S
  let t := sqrtY y
  let u := sqrtOneSubY y
  have ht := sqrtY_ne hy
  have hu := sqrtOneSubY_ne hy₁
  have hi := Complex.I_ne_zero
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨hp, hq, hr, hs⟩ := localLift_table y .A
    rw [liftedProduct_by_puncture hy hy₁, hp, hq, hr, hs]
    change (u⁻¹)^M * (I⁻¹*u⁻¹)^K * (t⁻¹)^L * t^N = I^(-K) * u^(-(M+K)) * t^(N-L)
    simp only [mul_zpow, inv_zpow', neg_add]
    rw [zpow_add₀ hu, zpow_sub₀ ht, div_eq_mul_inv, ← zpow_neg]
    ring
  · obtain ⟨hp, hq, hr, hs⟩ := localLift_table y .B
    rw [liftedProduct_by_puncture hy hy₁, hp, hq, hr, hs]
    change (I⁻¹)^M * (t⁻¹)^K * (I⁻¹*t⁻¹)^L * ((-1)*I⁻¹)^N =
      (-1 : ℂ)^N * I^(-(M+L+N)) * t^(-(K+L))
    rw [show -(K + L) = -K + -L by ring, zpow_add₀ ht]
    simp only [mul_zpow, inv_zpow', neg_add, zpow_add₀ hi]
    ring
  · obtain ⟨hp, hq, hr, hs⟩ := localLift_table y .D
    rw [liftedProduct_by_puncture hy hy₁, hp, hq, hr, hs]
    change (1 : ℂ)^M * ((-1)*(I⁻¹*t⁻¹))^K * ((-1)*I⁻¹)^L * (I⁻¹*t)^N =
      (-1 : ℂ)^(K+L) * I^(-(K+L+N)) * t^(N-K)
    simp only [one_zpow, one_mul, mul_zpow, inv_zpow', neg_add,
      zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_add₀ hi]
    rw [zpow_sub₀ ht, div_eq_mul_inv, ← zpow_neg]
    ring

/-- The upper-branch roots of minus the actual chart parameters. -/
def laurentRoot (c : Chart) (y : ℝ) : ℂ :=
  match c with
  | .A => scaleRoot .A y .P / scaleRoot .A y .R
  | .B => scaleRoot .B y .R
  | .D => scaleRoot .D y .S

theorem laurentRoot_values {y : ℝ} (hy₁ : y < 1) :
    laurentRoot .A y = (Real.sqrt ((1-y)/y) : ℂ) ∧
    laurentRoot .B y = I * (Real.sqrt y : ℂ) ∧
    laurentRoot .D y = I / (Real.sqrt y : ℂ) := by
  refine ⟨?_, rfl, rfl⟩
  change sqrtOneSubY y / sqrtY y = _
  rw [Real.sqrt_div (sub_nonneg.mpr hy₁.le), Complex.ofReal_div]

theorem laurentRoot_sq {y : ℝ} (hy : 0 < y) (hy₁ : y < 1) (c : Chart) :
    laurentRoot c y ^ (2 : ℕ) = -parameter c (y : ℂ) := by
  cases c with
  | A =>
      change (sqrtOneSubY y / sqrtY y) ^ (2 : ℕ) = -(1 - (y : ℂ)⁻¹)
      rw [div_pow, sqrtOneSubY_sq hy₁, sqrtY_sq hy, div_eq_mul_inv]
      have h0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
      field_simp
      ring
  | B => exact (chosen_roots hy hy₁ .B .R).1
  | D => exact (chosen_roots hy hy₁ .D .S).1

/-- The upper A sewing root is the actual D period root. It differs from
the positive A Laurent root. -/
theorem upper_sewing_root {y : ℝ} (hy : (1 / 2 : ℝ) < y) (hy₁ : y < 1) :
    periodRoot .D y = I * (Real.sqrt ((1-y)/y) : ℂ) ∧
    periodRoot .D y ^ (2 : ℕ) = parameter .A (y : ℂ) ∧
    ‖periodRoot .D y‖ < 1 ∧ periodRoot .D y ≠ laurentRoot .A y := by
  have hy₀ : 0 < y := by linarith
  have he : periodRoot .D y = I * (Real.sqrt ((1-y)/y) : ℂ) := by
    change I * sqrtOneSubY y / sqrtY y = _
    rw [Real.sqrt_div (sub_nonneg.mpr hy₁.le), Complex.ofReal_div]
    simp only [div_eq_mul_inv, mul_assoc]
  have hs : periodRoot .D y ^ (2 : ℕ) = parameter .A (y : ℂ) :=
    (chosen_roots hy₀ hy₁ .D .P).2
  have hpos : 0 < Real.sqrt ((1-y)/y) := Real.sqrt_pos.2 (div_pos (sub_pos.mpr hy₁) hy₀)
  refine ⟨he, hs, ?_, ?_⟩
  · rw [he, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_of_nonneg hpos.le]
    have hlt : (1-y)/y < 1 := (div_lt_iff₀ hy₀).2 (by linarith)
    have hsqrt := Real.sq_sqrt (div_nonneg (sub_nonneg.mpr hy₁.le) hy₀.le)
    apply (sq_lt_sq₀ hpos.le (zero_le_one : (0 : ℝ) ≤ 1)).mp
    rw [hsqrt, one_pow]
    exact hlt
  · rw [he, (laurentRoot_values hy₁).1]
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, one_mul, zero_add] at hi
    exact hpos.ne' hi

/-- Twice the Laurent exponent. Each external conformal weight is
`(3 + doubledOccupation)/2` at rank 24. -/
def laurentPower (M K L : ℤ) : Chart → ℤ
  | .A => 6 + M + K
  | .B => 6 + K + L
  | .D => 6 + M + L

/-- The fixed BPZ phases `exp(πi(b-2a))` and `exp(πi(2c+d-a-b))`.
The latter includes the upper-lip conversion of the Laurent monomial. -/
def bpzPhase (M K L N : ℤ) : Chart → ℂ
  | .A => I ^ (K - 2*M - 3)
  | .B | .D => I ^ (3 + 2*L + N - M - K)

/-- The integral weight combination `a+b+c-d` on mixed parity. -/
def sigma (M K L N : ℤ) : ℤ := 3 + (M + K + L - N) / 2

/-- The multiplier from the Laurent-normalized readout back to the Gaussian
occupation readout. The inverse BPZ phase is essential in chart A. -/
def readoutMultiplier (M K L N : ℤ) (c : Chart) (y : ℝ) : ℂ :=
  laurentRoot c y ^ laurentPower M K L c * (bpzPhase M K L N c)⁻¹

/-- The full conversion in the physical Gaussian chart units. -/
def chartMultiplier (slot : X → Puncture) (n : X → ℕ) (l : List X)
    (c : Chart) (y : ℝ) : ℂ :=
  ((1 - parameter c (y : ℂ)) ^ (3 : ℕ) * liftedProduct slot n l c y) *
    readoutMultiplier (doubledOccupation slot n l .P) (doubledOccupation slot n l .Q)
      (doubledOccupation slot n l .R) (doubledOccupation slot n l .S) c y

private theorem i_pow_four : I ^ (4 : ℤ) = 1 := by
  change I ^ ((4 : ℕ) : ℤ) = 1
  rw [zpow_natCast, Complex.I_pow_four]

private theorem i_pow_three : I ^ (3 : ℤ) = -I := by
  change I ^ ((3 : ℕ) : ℤ) = -I
  rw [zpow_natCast, pow_succ, Complex.I_sq, neg_one_mul]

private theorem i_zpow_congr {a b : ℤ} (h : a % 4 = b % 4) : I ^ a = I ^ b := by
  have reduce (m : ℤ) : I ^ m = I ^ (m % 4) := by
    conv_lhs => rw [show m = m % 4 + 4 * (m / 4) by omega]
    rw [zpow_add₀ Complex.I_ne_zero, zpow_mul, i_pow_four, one_zpow, mul_one]
  rw [reduce a, reduce b, h]

private theorem sign_zpow (n : ℤ) : (-1 : ℂ) ^ n = I ^ (2*n) := by
  rw [zpow_mul]
  change (-1 : ℂ) ^ n = (I ^ ((2 : ℕ) : ℤ)) ^ n
  rw [zpow_natCast, Complex.I_sq]

/-- The common B and D phase on HHBB is the sign with exponent
`sigma + c`, where `c = (3 + L)/2` is the weight at R. -/
theorem bpzPhase_BD (M K L N : ℤ) (hM : M % 2 = 0) (hK : K % 2 = 0)
    (hL : L % 2 = 1) (hN : N % 2 = 1) :
    let e := sigma M K L N + (L + 3) / 2
    bpzPhase M K L N .B = (-1 : ℂ)^e ∧ bpzPhase M K L N .D = (-1 : ℂ)^e := by
  let e := sigma M K L N + (L + 3) / 2
  have hs : 2 * sigma M K L N = 6 + M + K + L - N := by
    unfold sigma
    omega
  have he : 2*e = 9 + M + K + 2*L - N := by
    dsimp only [e]
    omega
  have h : I ^ (3+2*L+N-M-K) = (-1 : ℂ)^e := by
    rw [sign_zpow]
    apply i_zpow_congr
    omega
  exact ⟨h, h⟩

private theorem sqrtY_evenPower {y : ℝ} (hy : 0 < y) (m : ℤ) :
    sqrtY y ^ (2*m) = (y : ℂ) ^ m := by
  have h : sqrtY y ^ (2 : ℤ) = (y : ℂ) := sqrtY_sq hy
  rw [zpow_mul, h]

private theorem sqrtOneSubY_sixthPower {y : ℝ} (hy₁ : y < 1) :
    sqrtOneSubY y ^ (6 : ℤ) = (1 - (y : ℂ)) ^ (3 : ℕ) := by
  calc
    _ = (sqrtOneSubY y ^ (2 : ℤ)) ^ (3 : ℤ) := zpow_mul _ 2 3
    _ = _ := by
      have h : sqrtOneSubY y ^ (2 : ℤ) = 1 - (y : ℂ) := sqrtOneSubY_sq hy₁
      rw [h]
      exact zpow_natCast _ 3

/-- Equation (37) in the actual chart units. The A and D multipliers
agree, and the B multiplier carries the opposite phase. -/
theorem chartMultiplier_eq {y : ℝ} (hy : 0 < y) (hy₁ : y < 1)
    (slot : X → Puncture) (n : X → ℕ) (l : List X) (hpar : MixedParity slot n l) :
    let s := sigma (doubledOccupation slot n l .P) (doubledOccupation slot n l .Q)
      (doubledOccupation slot n l .R) (doubledOccupation slot n l .S)
    let z : ℂ := y
    chartMultiplier slot n l .A y = -I * (1-z)^3 * z^(-s-3) ∧
    chartMultiplier slot n l .B y = I * (1-z)^3 * z^(3 : ℤ) ∧
    chartMultiplier slot n l .D y = -I * (1-z)^3 * z^(-s-3) := by
  let M := doubledOccupation slot n l .P
  let K := doubledOccupation slot n l .Q
  let L := doubledOccupation slot n l .R
  let N := doubledOccupation slot n l .S
  let s := sigma M K L N
  let z : ℂ := y
  let t := sqrtY y
  let u := sqrtOneSubY y
  have hz : z ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have ht : t ≠ 0 := sqrtY_ne hy
  have hu : u ≠ 0 := sqrtOneSubY_ne hy₁
  have hi := Complex.I_ne_zero
  change M % 2 = 0 ∧ K % 2 = 0 ∧ L % 2 = 1 ∧ N % 2 = 1 at hpar
  obtain ⟨hM, hK, hL, hN⟩ := hpar
  have hs : 2*s = 6 + M + K + L - N := by
    change 2 * (3 + (M + K + L - N) / 2) = _
    omega
  have hpA : I ^ (2*M-2*K+3) = -I :=
    (i_zpow_congr (b := 3) (by omega)).trans i_pow_three
  have hpB : I ^ (3+2*K-2*L) = I := by
    rw [i_zpow_congr (b := 1) (by omega), zpow_one]
  have hpD : I ^ (3+2*M+2*K-2*N) = I := by
    rw [i_zpow_congr (b := 1) (by omega), zpow_one]
  obtain ⟨hprodA, hprodB, hprodD⟩ := liftedProduct_phases hy hy₁ slot n l
  have hA : liftedProduct slot n l .A y * readoutMultiplier M K L N .A y =
      -I * (1-z)^3 * z^(-s) := by
    rw [hprodA]
    change (I^(-K) * u^(-(M+K)) * t^(N-L)) *
      ((u/t)^(6+M+K) * (I^(K-2*M-3))⁻¹) = _
    simp only [div_eq_mul_inv, mul_zpow, inv_zpow', ← zpow_neg]
    calc
      _ = (I^(-K) * I^(-(K-2*M-3))) * (u^(-(M+K)) * u^(6+M+K)) *
          (t^(N-L) * t^(-(6+M+K))) := by ring
      _ = _ := by
        rw [← zpow_add₀ hi, ← zpow_add₀ hu, ← zpow_add₀ ht]
        rw [show -K + -(K-2*M-3) = 2*M-2*K+3 by ring, hpA,
          show -(M+K) + (6+M+K) = 6 by ring, sqrtOneSubY_sixthPower hy₁,
          show N-L + -(6+M+K) = 2*(-s) by omega, sqrtY_evenPower hy]
  have hB : liftedProduct slot n l .B y * readoutMultiplier M K L N .B y =
      I * z^(3 : ℤ) := by
    rw [hprodB]
    change ((-1 : ℂ)^N * I^(-(M+L+N)) * t^(-(K+L))) *
      ((I*t)^(6+K+L) * (I^(3+2*L+N-M-K))⁻¹) = _
    simp only [sign_zpow, mul_zpow, ← zpow_neg]
    calc
      _ = (I^(2*N) * I^(-(M+L+N)) * I^(6+K+L) * I^(-(3+2*L+N-M-K))) *
          (t^(-(K+L)) * t^(6+K+L)) := by ring
      _ = _ := by
        simp only [← zpow_add₀ hi, ← zpow_add₀ ht]
        rw [show 2*N + -(M+L+N) + (6+K+L) + -(3+2*L+N-M-K) = 3+2*K-2*L by ring,
          hpB, show -(K+L) + (6+K+L) = 2*3 by ring, sqrtY_evenPower hy]
  have hD : liftedProduct slot n l .D y * readoutMultiplier M K L N .D y =
      I * z^(-s) := by
    rw [hprodD]
    change ((-1 : ℂ)^(K+L) * I^(-(K+L+N)) * t^(N-K)) *
      ((I/t)^(6+M+L) * (I^(3+2*L+N-M-K))⁻¹) = _
    simp only [sign_zpow, div_eq_mul_inv, mul_zpow, inv_zpow', ← zpow_neg]
    calc
      _ = (I^(2*(K+L)) * I^(-(K+L+N)) * I^(6+M+L) * I^(-(3+2*L+N-M-K))) *
          (t^(N-K) * t^(-(6+M+L))) := by ring
      _ = _ := by
        simp only [← zpow_add₀ hi, ← zpow_add₀ ht]
        rw [show 2*(K+L) + -(K+L+N) + (6+M+L) + -(3+2*L+N-M-K) =
            3+2*M+2*K-2*N by ring, hpD,
          show N-K + -(6+M+L) = 2*(-s) by omega, sqrtY_evenPower hy]
  have hzpow : z^(-s) * (z⁻¹)^(3 : ℕ) = z^(-s-3) := by
    rw [← zpow_natCast, inv_zpow', ← zpow_add₀ hz, sub_eq_add_neg]
    rfl
  have dCube : (1 - parameter .D z) ^ (3 : ℕ) = -((1-z)^3 * (z⁻¹)^3) := by
    have hd : 1 - parameter .D z = -((1-z)*z⁻¹) := by
      change 1 - z⁻¹ = _
      field_simp
      ring
    rw [hd]
    ring
  change chartMultiplier slot n l .A y = -I * (1-z)^3 * z^(-s-3) ∧
    chartMultiplier slot n l .B y = I * (1-z)^3 * z^(3 : ℤ) ∧
    chartMultiplier slot n l .D y = -I * (1-z)^3 * z^(-s-3)
  refine ⟨?_, ?_, ?_⟩
  · rw [chartMultiplier, mul_assoc, hA]
    change (1-(1-z⁻¹))^3 * (-I * (1-z)^3 * z^(-s)) = _
    rw [sub_sub_cancel]
    calc
      _ = -I * (1-z)^3 * (z^(-s) * (z⁻¹)^(3 : ℕ)) := by ring
      _ = _ := by rw [hzpow]
  · rw [chartMultiplier, mul_assoc, hB]
    change (1-z)^3 * (I * z^(3 : ℤ)) = _
    ring
  · rw [chartMultiplier, mul_assoc, hD, dCube]
    calc
      _ = -I * (1-z)^3 * (z^(-s) * (z⁻¹)^(3 : ℕ)) := by ring
      _ = _ := by rw [hzpow]

/-- The period normalization in the original B Fourier overlap. -/
private theorem periodRoot_A_factor {y : ℝ} (hy : 0 < y) :
    (periodRoot .A y ^ (12 : ℕ))⁻¹ = (y : ℂ)^(6 : ℤ) := by
  have hsq : periodRoot .A y ^ (2 : ℕ) = (y : ℂ)⁻¹ := by
    change ((sqrtY y)⁻¹)^(2 : ℕ) = _
    rw [inv_pow, sqrtY_sq hy]
  change (periodRoot .A y ^ (12 : ℕ))⁻¹ = (y : ℂ)^((6 : ℕ) : ℤ)
  rw [show (12 : ℕ) = 2*6 by decide, pow_mul, hsq, inv_pow, inv_inv, zpow_natCast]

/-- The ratio of the scalar Gaussian conversion factors in the Fourier overlaps. -/
theorem chartMultiplier_ratio {y : ℝ} (hy : 0 < y) (hy₁ : y < 1)
    (slot : X → Puncture) (n : X → ℕ) (l : List X) (hpar : MixedParity slot n l) :
    let s := sigma (doubledOccupation slot n l .P) (doubledOccupation slot n l .Q)
      (doubledOccupation slot n l .R) (doubledOccupation slot n l .S)
    chartMultiplier slot n l .D y = chartMultiplier slot n l .A y ∧
    (periodRoot .A y ^ (12 : ℕ))⁻¹ * chartMultiplier slot n l .A y =
      -(chartMultiplier slot n l .B y * (y : ℂ)^(-s)) := by
  let s := sigma (doubledOccupation slot n l .P) (doubledOccupation slot n l .Q)
    (doubledOccupation slot n l .R) (doubledOccupation slot n l .S)
  let z : ℂ := y
  have hz : z ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hpow : z^(6 : ℤ) * z^(-s-3) = z^(3 : ℤ) * z^(-s) := by
    rw [← zpow_add₀ hz, ← zpow_add₀ hz]
    rw [show (6 : ℤ) + (-s-3) = 3 + -s by ring]
  obtain ⟨hA, hB, hD⟩ := chartMultiplier_eq hy hy₁ slot n l hpar
  refine ⟨hD.trans hA.symm, ?_⟩
  rw [periodRoot_A_factor hy, hA, hB]
  change z^(6 : ℤ) * (-I * (1-z)^3 * z^(-s-3)) = -(I * (1-z)^3 * z^(3 : ℤ) * z^(-s))
  calc
    _ = (-I * (1-z)^3) * (z^(6 : ℤ) * z^(-s-3)) := by ring
    _ = _ := by rw [hpow]; ring

/-- The lowest mixed occupation checks all three phases and the full
conversion, including the inverse of `I` in A. -/
theorem lowest_normalization {y : ℝ} (hy : (1 / 2 : ℝ) < y) (hy₁ : y < 1)
    (slot : X → Puncture) (n : X → ℕ) (l : List X)
    (hP : doubledOccupation slot n l .P = 0) (hQ : doubledOccupation slot n l .Q = 0)
    (hR : doubledOccupation slot n l .R = 1) (hS : doubledOccupation slot n l .S = 1) :
    let z : ℂ := y
    sigma 0 0 1 1 = 3 ∧
    bpzPhase 0 0 1 1 .A = I ∧ bpzPhase 0 0 1 1 .B = -1 ∧ bpzPhase 0 0 1 1 .D = -1 ∧
    liftedProduct slot n l .A y = 1 ∧
    liftedProduct slot n l .B y = (Real.sqrt y : ℂ)⁻¹ ∧
    liftedProduct slot n l .D y = (Real.sqrt y : ℂ) ∧
    chartMultiplier slot n l .A y = -I * (1-z)^3 * z^(-6 : ℤ) ∧
    chartMultiplier slot n l .B y = I * (1-z)^3 * z^(3 : ℤ) ∧
    chartMultiplier slot n l .D y = -I * (1-z)^3 * z^(-6 : ℤ) := by
  have hy₀ : 0 < y := by linarith
  have hpar : MixedParity slot n l := by norm_num [MixedParity, hP, hQ, hR, hS]
  have hPhaseA : I ^ (-3 : ℤ) = I := by
    rw [i_zpow_congr (b := 1) (by decide), zpow_one]
  have hPhaseB : I ^ (6 : ℤ) = -1 := by
    rw [i_zpow_congr (b := 2) (by decide)]
    exact Complex.I_sq
  have hLift : I ^ (-2 : ℤ) = -1 := by
    rw [i_zpow_congr (b := 2) (by decide)]
    exact Complex.I_sq
  have hprod := liftedProduct_phases hy₀ hy₁ slot n l
  have hscalar := chartMultiplier_eq hy₀ hy₁ slot n l hpar
  dsimp only at hprod hscalar ⊢
  rw [hP, hQ, hR, hS] at hprod hscalar
  norm_num [hLift, sigma, zpow_neg_one] at hprod hscalar
  refine ⟨rfl, hPhaseA, hPhaseB, hPhaseB, hprod.1, hprod.2.1, hprod.2.2,
    ?_, hscalar.2.1, ?_⟩
  · simpa [zpow_neg, neg_mul] using hscalar.1
  · simpa [zpow_neg, neg_mul] using hscalar.2.2

private theorem laurentRoot_ne {y : ℝ} (hy : 0 < y) (hy₁ : y < 1) (c : Chart) :
    laurentRoot c y ≠ 0 := by
  cases c
  · exact div_ne_zero (sqrtOneSubY_ne hy₁) (sqrtY_ne hy)
  · exact mul_ne_zero Complex.I_ne_zero (sqrtY_ne hy)
  · exact div_ne_zero Complex.I_ne_zero (sqrtY_ne hy)

/-- The existing Gaussian evaluation on the actual lowered occupations,
in each chart's native slot order and with the true D lip. -/
def gaussianOccupation (D : LatticeData) (slot : X → Puncture) (colour : X → Fin D.rank)
    (n : X → ℕ) (l : List X) (c : Chart) (y : ℝ) (a : ModTwoCharge D) : ℂ :=
  let A := loweredOscillator D slot colour c n l ∘ nativePuncture c
  occupationReadout D (A 0) (A 1) (A 2) (A 3) (nativeSector D c y a)

/-- The phase-normalized Gaussian occupation, with the Laurent monomial
represented by a signed integer power of the chosen root of minus the parameter. -/
def normalizedOccupation (D : LatticeData) (slot : X → Puncture)
    (colour : X → Fin D.rank) (n : X → ℕ) (l : List X)
    (c : Chart) (y : ℝ) (a : ModTwoCharge D) : ℂ :=
  let M := doubledOccupation slot n l .P
  let K := doubledOccupation slot n l .Q
  let L := doubledOccupation slot n l .R
  let N := doubledOccupation slot n l .S
  bpzPhase M K L N c * laurentRoot c y ^ (-laurentPower M K L c) *
    gaussianOccupation D slot colour n l c y a

/-- The normalization is invertible on the overlap and gives the scalar
readout relation with the inverse BPZ phase. -/
theorem gaussian_eq_normalized (D : LatticeData) (slot : X → Puncture)
    (colour : X → Fin D.rank) (n : X → ℕ) (l : List X) (c : Chart)
    {y : ℝ} (hy : 0 < y) (hy₁ : y < 1) (a : ModTwoCharge D) :
    let M := doubledOccupation slot n l .P
    let K := doubledOccupation slot n l .Q
    let L := doubledOccupation slot n l .R
    let N := doubledOccupation slot n l .S
    gaussianOccupation D slot colour n l c y a =
      readoutMultiplier M K L N c y * normalizedOccupation D slot colour n l c y a := by
  dsimp only [readoutMultiplier, normalizedOccupation]
  let p := laurentPower (doubledOccupation slot n l .P) (doubledOccupation slot n l .Q)
    (doubledOccupation slot n l .R) c
  let k := bpzPhase (doubledOccupation slot n l .P) (doubledOccupation slot n l .Q)
    (doubledOccupation slot n l .R) (doubledOccupation slot n l .S) c
  let u := laurentRoot c y
  let w := gaussianOccupation D slot colour n l c y a
  change w = (u^p * k⁻¹) * (k * u^(-p) * w)
  have hk : k ≠ 0 := by
    dsimp only [k]
    cases c <;> exact zpow_ne_zero _ Complex.I_ne_zero
  have hu : u ≠ 0 := laurentRoot_ne hy hy₁ c
  symm
  calc
    _ = (u^p * u^(-p)) * (k*k⁻¹) * w := by ring
    _ = _ := by rw [← zpow_add₀ hu, add_neg_cancel, zpow_zero, mul_inv_cancel₀ hk,
      one_mul, one_mul]

/-- The actual Gaussian occupation overlap in Laurent normalization.
The B Fourier sum has the opposite sign and the D Fourier sum retains its sign. -/
theorem normalized_occupation_fourier_overlap {X : Type*} [Fintype X] [DecidableEq X]
    (D : LatticeData) (hu : IsUnit D.G.det) (hD : (gramReal D).PosDef) (h24 : D.rank = 24)
    (slot : X → Puncture) (colour : X → Fin D.rank) (n : X → ℕ) (l : List X)
    (hl : l.Nodup) (hpar : MixedParity slot n l)
    {y : ℝ} (hy : (1 / 2 : ℝ) < y) (hy₁ : y < 1) (a : ModTwoCharge D) :
    let s := sigma (doubledOccupation slot n l .P) (doubledOccupation slot n l .Q)
      (doubledOccupation slot n l .R) (doubledOccupation slot n l .S)
    let F := fun c b => normalizedOccupation D slot colour n l c y b
    (2 : ℂ)^(12 : ℕ) * (y : ℂ)^s * F .B a =
      -(∑ b, fourierSign D a b * quadraticSign D b * F .A b) ∧
    (2 : ℂ)^(12 : ℕ) * F .D a = ∑ b, fourierSign D a b * F .A b := by
  classical
  let s := sigma (doubledOccupation slot n l .P) (doubledOccupation slot n l .Q)
    (doubledOccupation slot n l .R) (doubledOccupation slot n l .S)
  let F := fun c b => normalizedOccupation D slot colour n l c y b
  let V := fun c b =>
    ((1 - parameter c (y : ℂ)) ^ (3 : ℕ) * liftedProduct slot n l c y) *
      gaussianOccupation D slot colour n l c y b
  let z : ℂ := y
  let k : ℂ := (2 : ℂ)^(12 : ℕ)
  let u : ℂ := -I * (1-z)^3 * z^(-s-3)
  let v : ℂ := I * (1-z)^3 * z^(3 : ℤ)
  let sumB : ℂ := ∑ b, fourierSign D a b * quadraticSign D b * F .A b
  let sumD : ℂ := ∑ b, fourierSign D a b * F .A b
  have hy₀ : 0 < y := by linarith
  have hz : z ≠ 0 := Complex.ofReal_ne_zero.mpr hy₀.ne'
  have hz₁ : 1-z ≠ 0 := by
    change (1 : ℂ) - (y : ℂ) ≠ 0
    exact_mod_cast (sub_pos.mpr hy₁).ne'
  have hk : k ≠ 0 := pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)
  have hu₀ : u ≠ 0 :=
    mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (pow_ne_zero _ hz₁))
      (zpow_ne_zero _ hz)
  have hv₀ : v ≠ 0 :=
    mul_ne_zero (mul_ne_zero Complex.I_ne_zero (pow_ne_zero _ hz₁)) (zpow_ne_zero _ hz)
  obtain ⟨_, hwA, hw, _⟩ := upper_sewing_root hy hy₁
  have hover := native_occupation_fourier_overlap D hu hD h24 slot colour
    hy₀ hy₁ hwA hw a n l hl
  change V .D a = k⁻¹ * (∑ b, fourierSign D a b * V .A b) ∧
    V .B a = (periodRoot .A y ^ (12 : ℕ))⁻¹ *
      (k⁻¹ * ∑ b, fourierSign D a b * quadraticSign D b * V .A b) at hover
  have hV (c : Chart) (b : ModTwoCharge D) :
      V c b = chartMultiplier slot n l c y * F c b := by
    dsimp only [V, chartMultiplier, F]
    rw [gaussian_eq_normalized D slot colour n l c hy₀ hy₁ b]
    ring
  obtain ⟨hA, hB, hD'⟩ := chartMultiplier_eq hy₀ hy₁ slot n l hpar
  have sum_A_B : (∑ b, fourierSign D a b * quadraticSign D b * V .A b) = u * sumB := by
    unfold sumB
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hV .A b, hA]
    change _ * (u * F .A b) = u * (_ * F .A b)
    ring
  have sum_A_D : (∑ b, fourierSign D a b * V .A b) = u * sumD := by
    unfold sumD
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hV .A b, hA]
    change _ * (u * F .A b) = u * (_ * F .A b)
    ring
  have hDover : u * F .D a = k⁻¹ * (u * sumD) := by
    have h := hover.1
    rw [hV .D a, hD', sum_A_D] at h
    exact h
  have hBover : v * F .B a = z^(6 : ℤ) * (k⁻¹ * (u * sumB)) := by
    have h := hover.2
    rw [hV .B a, hB, periodRoot_A_factor hy₀, sum_A_B] at h
    exact h
  have hRatio : z^(6 : ℤ) * u = -(v * z^(-s)) := by
    have h := (chartMultiplier_ratio hy₀ hy₁ slot n l hpar).2
    rw [periodRoot_A_factor hy₀, hA, hB] at h
    exact h
  change k * z^s * F .B a = -sumB ∧ k * F .D a = sumD
  constructor
  · apply mul_left_cancel₀ (mul_ne_zero hv₀ (zpow_ne_zero (-s) hz))
    have hinv : z^(-s) * z^s = 1 := zpow_neg_mul_zpow_self s hz
    calc
      _ = (z^(-s) * z^s) * (k * (v * F .B a)) := by ring
      _ = k * (v * F .B a) := by rw [hinv, one_mul]
      _ = (k*k⁻¹) * ((z^(6 : ℤ) * u) * sumB) := by rw [hBover]; ac_rfl
      _ = _ := by rw [mul_inv_cancel₀ hk, one_mul, hRatio, neg_mul, mul_neg]
  · apply mul_left_cancel₀ hu₀
    calc
      _ = k * (u * F .D a) := by ring
      _ = (k*k⁻¹) * (u * sumD) := by rw [hDover]; ac_rfl
      _ = _ := by rw [mul_inv_cancel₀ hk, one_mul]

end D5.S3.VertexAlgebra.TwistedGround.FourPoint.NativeMixedWickChartTransport
