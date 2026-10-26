/- GID: D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockChargedCollision/Kernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite charged collision coefficients and source insertion kernel. -/

import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Derivative
import D5.S3.VertexAlgebra.LatticeHalfFockOriginalTranslation
import D5.S3.VertexAlgebra.LatticeHalfFockOrderedProducts
import D5.S3.VertexAlgebra.LatticeHalfFockGroundProducts
import D5.S3.VertexAlgebra.LatticeActualOrderedProducts
import D5.S3.VertexAlgebra.LatticeActualAnnihilation

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockChargedCollision

open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
  LatticeHalfFockChargedTensorCoefficients LatticeHalfFockCorrectedField
open LatticeHalfFockFockNormalField LatticeHalfFockFiniteCorrection
open MvPolynomial
open scoped BigOperators TensorProduct VertexOperator

noncomputable section

theorem bare_source_product (D : LatticeData) (sigma tau : Charge D) (r : ℤ) :
    ((LatticeAllStateField.Y D (Finsupp.single sigma (1 : Oscillator D)))[[r]])
        (Finsupp.single tau (1 : Oscillator D)) =
      epsilon D sigma tau • Finsupp.single (sigma + tau)
        (creationCoeff D sigma (-r - 1 - bilinear D sigma tau)) := by
  rw [LatticeAllStateField.stateField_ground]
  change rawCoeff D sigma (-r - 1) (Finsupp.single tau 1) = _
  exact LatticeActualOrderedProducts.raw_ground D sigma (-r - 1) tau

private theorem source_creation_step (D : LatticeData) (sigma tau : Charge D) (N : ℕ) :
    LatticeSugawaraConformal.translation D
        (Finsupp.single (sigma + tau) (creationCoeff D sigma N)) =
      (N + 1 : ℂ) • Finsupp.single (sigma + tau) (creationCoeff D sigma (N + 1)) +
        Finsupp.single (sigma + tau)
          (LatticeSugawaraConformal.chargePolynomial D tau * creationCoeff D sigma N) := by
  have vacuumStep := LinearMap.congr_fun
    (LatticeSugawaraConformal.rawCoeff_translation D sigma N)
      (Finsupp.single (0 : Charge D) (1 : Oscillator D))
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    LatticeSugawaraConformal.translation_vacuum, map_zero, sub_zero,
    LatticeActualOrderedProducts.raw_ground] at vacuumStep
  have zeroCocycle : epsilon D sigma 0 = 1 := by
    simp [epsilon, lowerCocycleExponent, paritySign]
  have zeroPairing : bilinear D sigma 0 = 0 := by simp [bilinear]
  simp only [zeroCocycle, zeroPairing, one_smul, add_zero, sub_zero,
    LatticeSugawaraConformal.translation_single] at vacuumStep
  have polynomialStep :
      LatticeSugawaraConformal.oscillatorDerivation D (creationCoeff D sigma N) +
          LatticeSugawaraConformal.chargePolynomial D sigma * creationCoeff D sigma N =
        (N + 1 : ℂ) • creationCoeff D sigma (N + 1) := by
    simpa only [Finsupp.single_eq_same, Finsupp.smul_apply, Int.cast_add,
      Int.cast_natCast, Int.cast_one] using
      congrArg (fun a : Carrier D => a sigma) vacuumStep
  have chargeAdd : LatticeSugawaraConformal.chargePolynomial D (sigma + tau) =
      LatticeSugawaraConformal.chargePolynomial D sigma +
        LatticeSugawaraConformal.chargePolynomial D tau := by
    simp [LatticeSugawaraConformal.chargePolynomial, Int.cast_add, add_smul,
      Finset.sum_add_distrib]
  rw [LatticeSugawaraConformal.translation_single, chargeAdd, add_mul,
    ← add_assoc, polynomialStep, Finsupp.single_add, Finsupp.smul_single]

def chargeInsertion (D : LatticeData) (hu : IsUnit D.G.det)
    (tau : Charge D) (b : Carrier D) : NativeField D hu :=
  ∑ colour : Fin D.rank, (tau colour : ℂ) •
    (singletonLinear D hu (colour, 0) (correctedField D hu b) +
      ∑ n ∈ Finset.range (LatticeSugawaraCurrents.vectorFrequencyBound D b + 1),
        ((halfBinomial 1 * halfBinomial n) / (1 + (n : ℂ))) •
          shiftField D hu (1 + n)
            (correctedField D hu
              (LatticeFiniteNegativeGeneration.neutralMode D colour n b)))

private theorem charge_insertion_eq (D : LatticeData) (hu : IsUnit D.G.det)
    (a tau : Charge D) (p : Oscillator D) :
    correctedField D hu (Finsupp.single a
      (LatticeSugawaraConformal.chargePolynomial D tau * p)) =
        chargeInsertion D hu tau (Finsupp.single a p) := by
  classical
  let L : Oscillator D →ₗ[ℂ] NativeField D hu :=
    (correctedField D hu).comp (Finsupp.lsingle a)
  change L (LatticeSugawaraConformal.chargePolynomial D tau * p) = _
  rw [LatticeSugawaraConformal.chargePolynomial, Finset.sum_mul, map_sum]
  unfold chargeInsertion
  apply Finset.sum_congr rfl
  intro colour member
  rw [smul_mul_assoc, map_smul]
  congr 1
  have insertionLaw := correctedField_negative_current_insertion
    D hu (colour, 0) (Finsupp.single a p)
  simpa [L, LatticeHalfFockFiniteCorrection.sourceWeight,
    LatticeSugawaraCurrents.neutralMode_single,
    LatticeFiniteNegativeGeneration.neutralPolynomialMode] using insertionLaw

theorem corrected_creation_step (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (N : ℕ) (e : ℤ) (x : ActualTensor D hu) :
    (N + 1 : ℂ) •
        (correctedField D hu
          (Finsupp.single (sigma + tau) (creationCoeff D sigma (N + 1)))).coeff e x =
      (((e + 2 : ℤ) : ℂ) / 2) •
          (correctedField D hu
            (Finsupp.single (sigma + tau) (creationCoeff D sigma N))).coeff (e + 2) x -
        (chargeInsertion D hu tau
          (Finsupp.single (sigma + tau) (creationCoeff D sigma N))).coeff e x := by
  have translated := LatticeHalfFockOriginalTranslation.correctedField_translation_physical
    D hu (Finsupp.single (sigma + tau) (creationCoeff D sigma N)) e x
  rw [source_creation_step] at translated
  simp only [map_add, map_smul] at translated
  rw [charge_insertion_eq] at translated
  exact eq_sub_iff_add_eq.mpr (by simpa using translated)

attribute [-simp] PowerSeries.coeff_zero_eq_constantCoeff in
/-- The unit with constant coefficient one representing `(sqrt(1+h)+1)/2`. -/
def collisionUnit : (PowerSeries ℂ)ˣ :=
  (PowerSeries.isUnit_iff_constantCoeff.mpr (show IsUnit
    (PowerSeries.constantCoeff
      ((2 : ℂ)⁻¹ • (PowerSeries.binomialSeries (R := ℂ) ℂ (1 / 2 : ℂ) + 1))) from by
        norm_num [PowerSeries.binomialSeries_coeff,
          ← PowerSeries.coeff_zero_eq_constantCoeff_apply])).unit

/-- The Taylor coefficient of `(1+h)^(a/2) ((sqrt(1+h)+1)/2)^(-2B)`. -/
def collisionScalar (a B : ℤ) (N : ℕ) : ℂ :=
  PowerSeries.coeff N
    (PowerSeries.binomialSeries (R := ℂ) ℂ ((a : ℂ) / 2) *
      ((collisionUnit ^ (-2 * B) : (PowerSeries ℂ)ˣ) : PowerSeries ℂ))

def diagonalTerm (D : LatticeData) (sigma tau : Charge D)
    (N : ℕ) (total offset m : ℤ) : Oscillator D :=
  collisionScalar (m - offset - chargeNorm D sigma) (bilinear D sigma tau) N •
    (halfCreationCoeff D sigma m * halfCreationCoeff D tau (total - m))

theorem diagonal_as_sum (D : LatticeData) (sigma tau : Charge D)
    (N : ℕ) (total offset : ℤ) :
    (∑ᶠ m : ℤ, diagonalTerm D sigma tau N total offset m) =
      if total < 0 then 0 else
        ∑ m ∈ Finset.range (total.toNat + 1),
          diagonalTerm D sigma tau N total offset m := by
  classical
  by_cases negative : total < 0
  · rw [if_pos negative]
    apply finsum_eq_zero_of_forall_eq_zero
    intro m
    by_cases leftNegative : m < 0
    · simp only [diagonalTerm, halfCreationCoeff, if_pos leftNegative,
        zero_mul, smul_zero]
    · simp only [diagonalTerm, halfCreationCoeff,
        if_neg (by omega : ¬ m < 0),
        if_pos (show total - m < 0 by omega), smul_zero, mul_zero]
  · rw [if_neg negative]
    let box := (Finset.range (total.toNat + 1)).image (fun m : ℕ => (m : ℤ))
    have finiteBox : Function.support (diagonalTerm D sigma tau N total offset) ⊆ box := by
      intro m supported
      have lower : 0 ≤ m := by
        by_contra outside
        exact supported (by
          simp [diagonalTerm, halfCreationCoeff, show m < 0 by omega])
      have upper : m ≤ total := by
        by_contra outside
        exact supported (by
          simp [diagonalTerm, halfCreationCoeff, show total - m < 0 by omega])
      exact Finset.mem_image.mpr ⟨m.toNat,
        Finset.mem_range.mpr (by omega), Int.toNat_of_nonneg lower⟩
    rw [finsum_eq_sum_of_support_subset _ finiteBox]
    exact Finset.sum_image (by
      intro a ha b hb equality
      exact Int.ofNat_inj.mp (show (a : ℤ) = (b : ℤ) from equality))

def collisionDiagonal (D : LatticeData) (sigma tau : Charge D)
    (N : ℕ) (e : ℤ) (d : Fin 2 →₀ ℕ) : Oscillator D :=
  let total : ℤ := e + chargeNorm D (sigma + tau) + 2 * N + d 0 + d 1
  if total < 0 then 0 else
    ∑ m ∈ Finset.range (total.toNat + 1),
      diagonalTerm D sigma tau N total (d 0) m

def collisionConvolution (D : LatticeData) (sigma tau : Charge D)
    (N : ℕ) (e : ℤ) : PairPolynomial D →ₗ[Oscillator D] Oscillator D :=
  (Finsupp.lsum (Oscillator D) (fun d : Fin 2 →₀ ℕ =>
    LinearMap.mulRight (Oscillator D) (collisionDiagonal D sigma tau N e d))).comp
      (AddMonoidAlgebra.coeffLinearEquiv (Oscillator D)).toLinearMap

/-- A finite coefficient of the normalized two-charge normal symbol. -/
def collisionOscillator (D : LatticeData) (sigma tau : Charge D)
    (N : ℕ) (e : ℤ) : Module.End ℂ (Oscillator D) :=
  ((collisionConvolution D sigma tau N e).restrictScalars ℂ).comp
    (LatticeHalfFockProductKernel.pairTranslation D sigma tau).toLinearMap

theorem collision_expansion (D : LatticeData) (sigma tau : Charge D)
    (N : ℕ) (e : ℤ) (p : Oscillator D) :
    collisionOscillator D sigma tau N e p =
      ∑ d ∈ (LatticeHalfFockProductKernel.pairTranslation D sigma tau p).support,
        (LatticeHalfFockProductKernel.pairTranslation D sigma tau p).coeff d *
          (∑ᶠ m : ℤ, diagonalTerm D sigma tau N
            (e + chargeNorm D (sigma + tau) + 2 * N + d 0 + d 1) (d 0) m) := by
  simp_rw [diagonal_as_sum]
  rfl

def collisionCoefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (N : ℕ) (e : ℤ) : Module.End ℂ (ActualTensor D hu) :=
  chargeScalar D (sigma + tau) •
    TensorProduct.map (collisionOscillator D sigma tau N e) (groundAction D hu (sigma + tau))

def translatedDegree (D : LatticeData) (sigma tau : Charge D)
    (p : Oscillator D) : ℕ :=
  (LatticeHalfFockProductKernel.pairTranslation D sigma tau p).support.sup
    (fun d => d 0 + d 1)

private theorem collision_lower_bound (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (N : ℕ) (p : Oscillator D) (g : ActualGround D hu)
    (e : ℤ) (lower : e < -chargeNorm D (sigma + tau) - 2 * N -
      translatedDegree D sigma tau p) :
    collisionCoefficient D hu sigma tau N e (p ⊗ₜ[ℂ] g) = 0 := by
  classical
  have zeroOscillator : collisionOscillator D sigma tau N e p = 0 := by
    rw [collision_expansion]
    apply Finset.sum_eq_zero
    intro d member
    have bound : d 0 + d 1 ≤ translatedDegree D sigma tau p :=
      Finset.le_sup (f := fun d : Fin 2 →₀ ℕ => d 0 + d 1) member
    have castBound : (d 0 : ℤ) + d 1 ≤ translatedDegree D sigma tau p := by
      exact_mod_cast bound
    rw [diagonal_as_sum, if_pos (by omega), mul_zero]
  simp [collisionCoefficient, TensorProduct.map_tmul, zeroOscillator]

private theorem collision_tensor_lower_truncation (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (N : ℕ) (x : ActualTensor D hu) :
    ∃ lower : ℤ, ∀ e : ℤ, e < lower → collisionCoefficient D hu sigma tau N e x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by intros; simp⟩
  | tmul p g =>
    exact ⟨-chargeNorm D (sigma + tau) - 2 * N - translatedDegree D sigma tau p,
      fun e lower => collision_lower_bound D hu sigma tau N p g e lower⟩
  | add x y hx hy =>
    obtain ⟨lowerX, hx⟩ := hx
    obtain ⟨lowerY, hy⟩ := hy
    refine ⟨min lowerX lowerY, ?_⟩
    intro e lower
    simp [hx e (lt_of_lt_of_le lower (min_le_left _ _)),
      hy e (lt_of_lt_of_le lower (min_le_right _ _))]

def collisionField (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (N : ℕ) : NativeField D hu :=
  HVertexOperator.of_coeff (collisionCoefficient D hu sigma tau N) (by
    intro x
    obtain ⟨lower, hlower⟩ := collision_tensor_lower_truncation D hu sigma tau N x
    apply Set.IsWF.isPWO
    apply BddBelow.isWF
    refine ⟨lower, ?_⟩
    intro e supported
    by_contra outside
    exact supported (hlower e (by omega)))

def normalCurrent (D : LatticeData) (hu : IsUnit D.G.det)
    (tau : Charge D) : NativeField D hu →ₗ[ℂ] NativeField D hu :=
  ∑ colour : Fin D.rank, (tau colour : ℂ) • singletonLinear D hu (colour, 0)

def collisionR (j : ℕ) : ℂ := halfBinomial j / (j + 1 : ℂ)

/- Formal-series calculation:
   s²=1+h; 2/(s+1)=Σ collisionR j h^j;
   2(1+h) f'=(A-2B+B Σ collisionR j h^j)f.
   The type contains scalar series only, not the desired module law. -/
theorem collisionScalar_recurrence (A B : ℤ) (N : ℕ) :
    (N + 1 : ℂ) * collisionScalar A B (N + 1) =
      ((A : ℂ) / 2 - (N : ℂ) - (B : ℂ)) * collisionScalar A B N +
        ((B : ℂ) / 2) * ∑ j ∈ Finset.range (N + 1),
          collisionR j * collisionScalar A B (N - j) := by
  have collision_binomial_step (z : ℂ) (n : ℕ) :
      (n + 1 : ℂ) * Ring.choose z (n + 1) =
        (z - (n : ℂ)) * Ring.choose z n := by
    simpa [Nat.choose_succ_self_right, Nat.add_sub_cancel_left,
      Ring.choose_one_right, nsmul_eq_mul, mul_comm] using
      (Ring.choose_smul_choose z (n := n + 1) (k := n) (by omega))

  have collision_binomial_derivative (z : ℂ) :
      PowerSeries.derivative (R := ℂ) (PowerSeries.binomialSeries (R := ℂ) ℂ z) =
        PowerSeries.C z * PowerSeries.binomialSeries (R := ℂ) ℂ (z - 1) := by
    apply PowerSeries.ext
    intro n
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul]
    simpa [PowerSeries.binomialSeries_coeff, Nat.choose_one_right,
      Ring.choose_one_right, nsmul_eq_mul, smul_eq_mul, mul_comm] using
      (Ring.choose_smul_choose z (n := n + 1) (k := 1) (by omega))

  have collision_binomial_scaled_derivative (z : ℂ) :
      PowerSeries.derivative (R := ℂ) (PowerSeries.binomialSeries (R := ℂ) ℂ z) *
          (1 + PowerSeries.X) =
        PowerSeries.C z * PowerSeries.binomialSeries (R := ℂ) ℂ z := by
    have oneExponent : PowerSeries.binomialSeries (R := ℂ) ℂ (1 : ℂ) =
        (1 + PowerSeries.X : PowerSeries ℂ) := by
      simpa using (PowerSeries.binomialSeries_nat (R := ℂ) (A := ℂ) 1)
    rw [collision_binomial_derivative, mul_assoc, ← oneExponent,
      ← PowerSeries.binomialSeries_add, sub_add_cancel]

  /- The square-root derivative coefficients obey the half-binomial recurrence. -/
  have collision_sqrt_coefficient (n : ℕ) :
      2 * (n + 1 : ℂ) * PowerSeries.coeff (n + 1)
          (PowerSeries.binomialSeries (R := ℂ) ℂ (1 / 2 : ℂ)) = halfBinomial n := by
    induction n with
    | zero =>
      norm_num [PowerSeries.binomialSeries_coeff, halfBinomial, smul_eq_mul]
    | succ n previous =>
      have step := collision_binomial_step (1 / 2 : ℂ) (n + 1)
      simp only [PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one] at previous ⊢
      rw [half_successor]
      have nonzero : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      apply (eq_div_iff nonzero).mpr
      simp only [Nat.cast_succ, Nat.cast_add, Nat.cast_one] at step previous ⊢
      linear_combination 2 * (n + 1 : ℂ) * step + (-1 / 2 - (n : ℂ)) * previous

  have collision_unit_value :
      (collisionUnit : PowerSeries ℂ) = PowerSeries.C (1 / 2 : ℂ) *
        (PowerSeries.binomialSeries (R := ℂ) ℂ (1 / 2 : ℂ) + 1) := by
    unfold collisionUnit
    rw [IsUnit.unit_spec, PowerSeries.smul_eq_C_mul]
    norm_num

  have collision_R_inverse :
      PowerSeries.mk collisionR = ((collisionUnit⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) := by
    let s := PowerSeries.binomialSeries (R := ℂ) ℂ (1 / 2 : ℂ)
    let R : PowerSeries ℂ := PowerSeries.mk collisionR
    have sqrtSquare : s * s = 1 + PowerSeries.X := by
      rw [← PowerSeries.binomialSeries_add, show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num]
      simpa using (PowerSeries.binomialSeries_nat (R := ℂ) (A := ℂ) 1)
    have shift : R * PowerSeries.X = 2 * (s - 1) := by
      apply PowerSeries.ext
      intro n
      cases n with
      | zero => simp [s]
      | succ n =>
        rw [PowerSeries.coeff_succ_mul_X]
        have coefficient := collision_sqrt_coefficient n
        have nonzero : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
        change PowerSeries.coeff n R = PowerSeries.coeff (n + 1) (2 * (s - 1))
        rw [show (2 : PowerSeries ℂ) = PowerSeries.C (2 : ℂ) by
            exact (map_ofNat (PowerSeries.C (R := ℂ)) 2).symm,
          PowerSeries.coeff_C_mul, map_sub]
        simp only [PowerSeries.coeff_one, Nat.succ_ne_zero, if_false, sub_zero]
        dsimp only [R, collisionR, s]
        simp only [PowerSeries.coeff_mk]
        apply (div_eq_iff nonzero).mpr
        linear_combination -coefficient
    have halfTwice : (2 : PowerSeries ℂ) * PowerSeries.C (1 / 2 : ℂ) = 1 := by
      rw [show (2 : PowerSeries ℂ) = PowerSeries.C (2 : ℂ) by
        exact (map_ofNat (PowerSeries.C (R := ℂ)) 2).symm, ← map_mul]
      norm_num
    have twiceUnit : 2 * (collisionUnit : PowerSeries ℂ) = s + 1 := by
      rw [collision_unit_value, ← mul_assoc, halfTwice, one_mul]
    have product : R * (collisionUnit : PowerSeries ℂ) = 1 := by
      apply PowerSeries.X_mul_injective
      have multiplied := congrArg (fun t : PowerSeries ℂ =>
        t * (collisionUnit : PowerSeries ℂ)) shift
      linear_combination multiplied + (s - 1) * twiceUnit + sqrtSquare
    apply collisionUnit.isUnit.mul_right_cancel
    exact product.trans (by simp)

  have collision_unit_power_derivative (u : (PowerSeries ℂ)ˣ) (k : ℤ) :
      PowerSeries.derivative (R := ℂ) ((u ^ k : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) =
        PowerSeries.C (k : ℂ) * ((u ^ k : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) *
          ((u⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) *
            PowerSeries.derivative (R := ℂ) (u : PowerSeries ℂ) := by
    have natural (n : ℕ) :
        PowerSeries.derivative (R := ℂ) ((u ^ n : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) =
          PowerSeries.C (n : ℂ) * ((u ^ n : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) *
            ((u⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) *
              PowerSeries.derivative (R := ℂ) (u : PowerSeries ℂ) := by
      induction n with
      | zero => simp
      | succ n previous =>
        simp only [pow_succ, Units.val_mul]
        rw [(PowerSeries.derivative (R := ℂ)).leibniz, previous]
        simp only [smul_eq_mul, Nat.cast_succ, Nat.cast_add, Nat.cast_one, map_add, map_one]
        have cancel : (u : PowerSeries ℂ) *
            ((u⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) = 1 := by simp
        linear_combination -(((u ^ n : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) *
          PowerSeries.derivative (R := ℂ) (u : PowerSeries ℂ)) * cancel
    cases k with
    | ofNat n => simpa using natural n
    | negSucc n =>
      have exponent : (Int.negSucc n : ℤ) = -((n + 1 : ℕ) : ℤ) := by omega
      simp only [exponent, zpow_neg, zpow_natCast]
      rw [PowerSeries.derivative_inv, natural]
      simp only [Int.cast_neg, Int.cast_natCast, map_neg, Nat.cast_add, Nat.cast_one]
      have cancel : (( (u ^ (n + 1))⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) *
          ((u ^ (n + 1) : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) = 1 := by
        exact (u ^ (n + 1)).inv_val
      have cancel' :
          (((u ^ (n + 1))⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) ^ 2 *
              ((u ^ (n + 1) : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) =
            (((u ^ (n + 1))⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) := by
        rw [pow_two, mul_assoc, cancel, mul_one]
      norm_num only [Int.cast_add, Int.cast_natCast, Int.cast_one,
        Nat.cast_add, Nat.cast_one]
      calc
        _ = -(PowerSeries.C ((n : ℂ) + 1) *
            (((((u ^ (n + 1))⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) ^ 2 *
              ((u ^ (n + 1) : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)) *
            ((u⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) *
            PowerSeries.derivative (R := ℂ) (u : PowerSeries ℂ))) := by ring
        _ = _ := by rw [cancel']; ring

  let s := PowerSeries.binomialSeries (R := ℂ) ℂ (1 / 2 : ℂ)
  let q : PowerSeries ℂ := collisionUnit
  let R : PowerSeries ℂ := PowerSeries.mk collisionR
  let t := PowerSeries.binomialSeries (R := ℂ) ℂ ((A : ℂ) / 2)
  let g : PowerSeries ℂ := ((collisionUnit ^ (-2 * B) : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)
  let f : PowerSeries ℂ := t * g
  let c : PowerSeries ℂ := PowerSeries.C (1 / 2 : ℂ)
  have halfTwice : (2 : PowerSeries ℂ) * c = 1 := by
    rw [show (2 : PowerSeries ℂ) = PowerSeries.C (2 : ℂ) by
      exact (map_ofNat (PowerSeries.C (R := ℂ)) 2).symm, ← map_mul]
    norm_num
  have twiceUnit : 2 * q = s + 1 := by
    rw [show q = c * (s + 1) from collision_unit_value, ← mul_assoc,
      halfTwice, one_mul]
  have twiceDerivative : 2 * PowerSeries.derivative (R := ℂ) q =
      PowerSeries.derivative (R := ℂ) s := by
    have differentiated := congrArg (PowerSeries.derivative (R := ℂ)) twiceUnit
    rw [show (2 : PowerSeries ℂ) = PowerSeries.C (2 : ℂ) by
      exact (map_ofNat (PowerSeries.C (R := ℂ)) 2).symm,
      (PowerSeries.derivative (R := ℂ)).leibniz] at differentiated
    rw [show (2 : PowerSeries ℂ) = PowerSeries.C (2 : ℂ) by
      exact (map_ofNat (PowerSeries.C (R := ℂ)) 2).symm]
    simpa only [smul_eq_mul, PowerSeries.derivative_C,
      Derivation.map_natCast, map_natCast, mul_zero, add_zero, map_add,
      Derivation.map_one_eq_zero] using differentiated
  have qDerivative : 2 * (1 + PowerSeries.X) * PowerSeries.derivative (R := ℂ) q =
      q - c := by
    calc
      _ = PowerSeries.derivative (R := ℂ) s * (1 + PowerSeries.X) := by
        rw [← twiceDerivative]
        ring
      _ = c * s := collision_binomial_scaled_derivative (1 / 2 : ℂ)
      _ = q - c := by
        linear_combination -c * twiceUnit + q * halfTwice
  have inverseProduct : q * R = 1 := by
    rw [show R = _ from collision_R_inverse]
    exact Units.mul_inv collisionUnit
  have logarithmic : 2 * (1 + PowerSeries.X) * PowerSeries.derivative (R := ℂ) q * R =
      1 - c * R := by
    rw [qDerivative, sub_mul, inverseProduct]
  have tDerivative : PowerSeries.derivative (R := ℂ) t * (1 + PowerSeries.X) =
      PowerSeries.C ((A : ℂ) / 2) * t :=
    collision_binomial_scaled_derivative ((A : ℂ) / 2)
  have gDerivative : PowerSeries.derivative (R := ℂ) g =
      PowerSeries.C ((-2 * B : ℤ) : ℂ) * g * R *
        PowerSeries.derivative (R := ℂ) q := by
    rw [show R = _ from collision_R_inverse]
    exact collision_unit_power_derivative collisionUnit (-2 * B)
  have halfA : PowerSeries.C ((A : ℂ) / 2) = c * PowerSeries.C (A : ℂ) := by
    rw [← map_mul]
    congr 1
    ring
  have minusTwoB : PowerSeries.C ((-2 * B : ℤ) : ℂ) =
      -2 * PowerSeries.C (B : ℂ) := by
      have hcast : ((-2 * B : ℤ) : ℂ) = (-2 : ℂ) * (B : ℂ) := by
        norm_num [Int.cast_mul, Int.cast_neg]
      have hneg : (-2 : PowerSeries ℂ) = PowerSeries.C (-2 : ℂ) := by
        simpa using (map_intCast (PowerSeries.C (R := ℂ)) (-2)).symm
      calc
        PowerSeries.C ((-2 * B : ℤ) : ℂ) =
            PowerSeries.C ((-2 : ℂ) * (B : ℂ)) := by rw [hcast]
        _ = PowerSeries.C (-2 : ℂ) * PowerSeries.C (B : ℂ) := by rw [map_mul]
        _ = -2 * PowerSeries.C (B : ℂ) := by rw [← hneg]
  have ode : 2 * (1 + PowerSeries.X) * PowerSeries.derivative (R := ℂ) f =
      PowerSeries.C ((A : ℂ) - 2 * (B : ℂ)) * f +
        PowerSeries.C (B : ℂ) * (R * f) := by
    calc
      _ = 2 * (PowerSeries.derivative (R := ℂ) t * (1 + PowerSeries.X)) * g +
          t * PowerSeries.C ((-2 * B : ℤ) : ℂ) * g *
            (2 * (1 + PowerSeries.X) * PowerSeries.derivative (R := ℂ) q * R) := by
        dsimp only [f]
        rw [(PowerSeries.derivative (R := ℂ)).leibniz, gDerivative]
        simp only [smul_eq_mul]
        ring
      _ = _ := by
        rw [tDerivative, logarithmic, halfA, minusTwoB]
        simp only [map_sub, map_mul, map_ofNat]
        dsimp only [f]
        linear_combination (PowerSeries.C (A : ℂ) * t * g +
          PowerSeries.C (B : ℂ) * R * t * g) * halfTwice
  have odeExpanded :
      PowerSeries.C (2 : ℂ) * (PowerSeries.derivative (R := ℂ) f +
        PowerSeries.derivative (R := ℂ) f * PowerSeries.X) =
      PowerSeries.C ((A : ℂ) - 2 * (B : ℂ)) * f +
        PowerSeries.C (B : ℂ) * (R * f) := by
    calc
      _ = 2 * (1 + PowerSeries.X) * PowerSeries.derivative (R := ℂ) f := by
        rw [show (2 : PowerSeries ℂ) = PowerSeries.C (2 : ℂ) by
          exact (map_ofNat (PowerSeries.C (R := ℂ)) 2).symm]
        ring
      _ = _ := ode
  have weightedCoefficient : PowerSeries.coeff N
      (PowerSeries.derivative (R := ℂ) f * PowerSeries.X) =
        (N : ℂ) * PowerSeries.coeff N f := by
    cases N with
    | zero => simp
    | succ n =>
      rw [PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_derivative]
      push_cast
      ring
  have convolution : PowerSeries.coeff N (R * f) =
      ∑ j ∈ Finset.range (N + 1), collisionR j * collisionScalar A B (N - j) := by
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    dsimp only [R, f, collisionR, collisionScalar]
    simp only [PowerSeries.coeff_mk, collisionR]
    dsimp [t, g]
  have readout (n : ℕ) : PowerSeries.coeff n f = collisionScalar A B n := rfl
  have coefficient := congrArg (PowerSeries.coeff N) odeExpanded
  rw [PowerSeries.coeff_C_mul] at coefficient
  simp only [map_add] at coefficient
  rw [PowerSeries.coeff_derivative, weightedCoefficient] at coefficient
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, convolution] at coefficient
  simp only [readout] at coefficient
  linear_combination (1 / 2 : ℂ) * coefficient

/- Ordinary source current on the creation exponential. The positive branch
   directly reuses the signed ordinary annihilation_creation theorem, whose
   constructor proof applies actual_exponential_derivation. Negative shifted
   creation degrees are already included in that supplier. No half-mode
   coefficient, target-module law, positivity or homogeneity premise is used. -/
theorem source_neutral_creation (D : LatticeData)
    (sigma tau : Charge D) (N : ℕ) (colour : Fin D.rank) (n : ℕ) :
    LatticeFiniteNegativeGeneration.neutralMode D colour (n : ℤ)
        (Finsupp.single (sigma + tau) (creationCoeff D sigma N)) =
      if n = 0 then
        (bilinear D (unitCharge D colour) (sigma + tau) : ℂ) •
          Finsupp.single (sigma + tau) (creationCoeff D sigma N)
      else
        (bilinear D (unitCharge D colour) sigma : ℂ) •
          Finsupp.single (sigma + tau)
            (creationCoeff D sigma ((N : ℤ) - (n : ℤ))) := by
  classical
  rw [LatticeSugawaraCurrents.neutralMode_single]
  cases n with
  | zero =>
    simp [LatticeFiniteNegativeGeneration.neutralPolynomialMode,
      Finsupp.smul_single]
  | succ k =>
    rw [if_neg (Nat.succ_ne_zero k)]
    have nonzero : (k + 1 : ℂ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero k
    have scalar_cancel :
        (k + 1 : ℂ) * ((k + 1 : ℂ)⁻¹ *
          (bilinear D (unitCharge D colour) sigma : ℂ)) =
            (bilinear D (unitCharge D colour) sigma : ℂ) := by
      rw [← mul_assoc, mul_inv_cancel₀ nonzero, one_mul]
    have polynomial_law :
        LatticeFiniteNegativeGeneration.neutralPolynomialMode D colour (sigma + tau)
            ((k : ℤ) + 1) (creationCoeff D sigma (N : ℤ)) =
          (bilinear D (unitCharge D colour) sigma : ℂ) •
            creationCoeff D sigma ((N : ℤ) - ((k : ℤ) + 1)) := by
      rw [LatticeSugawaraCurrents.neutralPolynomialMode_positive,
        LinearMap.smul_apply]
      simpa only [smul_smul, scalar_cancel, Nat.cast_add, Nat.cast_one] using
        congrArg (fun p : Oscillator D => (k + 1 : ℂ) • p)
          (LatticeActualAnnihilation.annihilation_creation D colour k sigma (N : ℤ))
    simpa only [Nat.cast_succ, Finsupp.smul_single] using
      congrArg (fun p : Oscillator D => Finsupp.single (sigma + tau) p) polynomial_law

private theorem chargeInsertion_weighted_modes (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (N n : ℕ) (within : n ≤ N)
    (modes : ∀ (colour : Fin D.rank) (n : ℕ),
      LatticeFiniteNegativeGeneration.neutralMode D colour (n : ℤ)
          (Finsupp.single (sigma + tau) (creationCoeff D sigma N)) =
        if n = 0 then
          (bilinear D (unitCharge D colour) (sigma + tau) : ℂ) •
            Finsupp.single (sigma + tau) (creationCoeff D sigma N)
        else
          (bilinear D (unitCharge D colour) sigma : ℂ) •
            Finsupp.single (sigma + tau)
              (creationCoeff D sigma ((N : ℤ) - (n : ℤ)))) :
    (∑ colour : Fin D.rank, (tau colour : ℂ) • correctedField D hu
      (LatticeFiniteNegativeGeneration.neutralMode D colour (n : ℤ)
        (Finsupp.single (sigma + tau) (creationCoeff D sigma N)))) =
      (bilinear D sigma tau : ℂ) •
        correctedField D hu
          (Finsupp.single (sigma + tau) (creationCoeff D sigma (N - n))) +
        if n = 0 then
          (chargeNorm D tau : ℂ) •
            correctedField D hu
              (Finsupp.single (sigma + tau) (creationCoeff D sigma N))
        else 0 := by
  classical
  have gram (a : Charge D) :
      (∑ colour : Fin D.rank, (tau colour : ℂ) *
        (bilinear D (unitCharge D colour) a : ℂ)) = (bilinear D tau a : ℂ) := by
    have integral : (∑ colour : Fin D.rank, tau colour *
        bilinear D (unitCharge D colour) a) = bilinear D tau a := by
      simp [bilinear, unitCharge, Finset.mul_sum, mul_assoc]
    exact_mod_cast integral
  have gramZero :
      (bilinear D tau (sigma + tau) : ℂ) =
        (bilinear D sigma tau : ℂ) + (chargeNorm D tau : ℂ) := by
    have integral : bilinear D tau (sigma + tau) =
        bilinear D tau sigma + bilinear D tau tau := by
      simp [bilinear, mul_add, Finset.sum_add_distrib]
    rw [integral, Int.cast_add,
      LatticeFiniteNegativeGeneration.bilinear_symmetric D tau sigma]
    rfl
  simp_rw [modes]
  by_cases zero : n = 0
  · subst n
    simp only [if_pos rfl, if_true, map_smul, smul_smul, Nat.sub_zero]
    rw [← Finset.sum_smul, gram, gramZero, add_smul]
    norm_num [Int.ofNat_zero]
  · have degree : ((N : ℤ) - (n : ℤ)) = ((N - n : ℕ) : ℤ) := by omega
    simp only [if_neg zero, map_smul, smul_smul, degree, add_zero]
    rw [← Finset.sum_smul, gram,
      LatticeFiniteNegativeGeneration.bilinear_symmetric D tau sigma]

set_option maxHeartbeats 8000000 in
private theorem chargeInsertion_weighted_term_alias (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (N n : ℕ) (within : n ≤ N)
    (A : ℕ → NativeField D hu) (term : Fin D.rank → ℕ → NativeField D hu)
    (term_eq : ∀ colour : Fin D.rank,
      term colour n =
        ((halfBinomial 1 * halfBinomial n) / (1 + (n : ℂ))) •
          shiftField D hu (1 + n)
            (correctedField D hu
              (LatticeFiniteNegativeGeneration.neutralMode D colour (n : ℤ)
                (Finsupp.single (sigma + tau) (creationCoeff D sigma N)))))
    (A_eq : ∀ k : ℕ,
      A k = correctedField D hu
        (Finsupp.single (sigma + tau) (creationCoeff D sigma k)))
    (modes : ∀ (colour : Fin D.rank) (n : ℕ),
      LatticeFiniteNegativeGeneration.neutralMode D colour (n : ℤ)
          (Finsupp.single (sigma + tau) (creationCoeff D sigma N)) =
        if n = 0 then
          (bilinear D (unitCharge D colour) (sigma + tau) : ℂ) •
            Finsupp.single (sigma + tau) (creationCoeff D sigma N)
        else
          (bilinear D (unitCharge D colour) sigma : ℂ) •
            Finsupp.single (sigma + tau)
              (creationCoeff D sigma ((N : ℤ) - (n : ℤ)))) :
    (∑ colour : Fin D.rank, (tau colour : ℂ) • term colour n) =
      -((bilinear D sigma tau : ℂ) / 2) •
          (collisionR n • shiftField D hu (1 + n) (A (N - n))) +
        if n = 0 then -((chargeNorm D tau : ℂ) / 2) •
          shiftField D hu 1 (A N) else 0 := by
  have hterm :
      (∑ colour : Fin D.rank, (tau colour : ℂ) • term colour n) =
        ∑ colour : Fin D.rank, (tau colour : ℂ) •
          (((halfBinomial 1 * halfBinomial n) / (1 + (n : ℂ))) •
            shiftField D hu (1 + n)
              (correctedField D hu
                (LatticeFiniteNegativeGeneration.neutralMode D colour (n : ℤ)
                  (Finsupp.single (sigma + tau) (creationCoeff D sigma N))))) := by
    apply Finset.sum_congr rfl
    intro colour member
    rw [term_eq colour]
  rw [hterm, A_eq (N - n), A_eq N]
  have coefficient (n : ℕ) :
      (halfBinomial 1 * halfBinomial n) / (1 + (n : ℂ)) =
        -(1 / 2 : ℂ) * collisionR n := by
    have halfOne : halfBinomial 1 = -(1 / 2 : ℂ) := by norm_num [halfBinomial]
    rw [halfOne]
    dsimp only [collisionR]
    rw [show (1 + (n : ℂ)) = (n + 1 : ℂ) by ring]
    ring
  have transport :
      (∑ colour : Fin D.rank, (tau colour : ℂ) •
        ((halfBinomial 1 * halfBinomial n) / (1 + (n : ℂ))) •
          shiftField D hu (1 + n)
            (correctedField D hu
              (LatticeFiniteNegativeGeneration.neutralMode D colour (n : ℤ)
                (Finsupp.single (sigma + tau) (creationCoeff D sigma N))))) =
      (-(1 / 2 : ℂ) * collisionR n) • shiftField D hu (1 + n)
        (∑ colour : Fin D.rank, (tau colour : ℂ) •
          correctedField D hu
            (LatticeFiniteNegativeGeneration.neutralMode D colour (n : ℤ)
              (Finsupp.single (sigma + tau) (creationCoeff D sigma N)))) := by
    simp only [coefficient, map_sum, map_smul, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro colour member
    congr 1
    ring
  rw [transport]
  rw [chargeInsertion_weighted_modes D hu sigma tau N n within modes]
  by_cases zero : n = 0
  · subst n
    simp only [if_pos rfl, Nat.sub_zero, Nat.add_zero, map_add, map_smul,
      smul_add, collisionR, halfBinomial]
    norm_num
    simp only [smul_smul]
    congr 1 <;> ring
  · simp only [if_neg zero, add_zero, map_smul, smul_smul]
    have degree : ((N : ℤ) - (n : ℤ)) = ((N - n : ℕ) : ℤ) := by omega
    rw [degree]
    rw [show (-(1 / 2 : ℂ) * collisionR n) *
        (bilinear D sigma tau : ℂ) =
        -((bilinear D sigma tau : ℂ) / 2) * collisionR n by ring]

private theorem chargeInsertion_sum_identity (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (N bound : ℕ)
    (A : ℕ → NativeField D hu)
    (term : Fin D.rank → ℕ → NativeField D hu)
    (pad : ∀ colour : Fin D.rank,
      (∑ n ∈ Finset.range (bound + 1), term colour n) =
        ∑ n ∈ Finset.range (N + 1), term colour n)
    (weightedTerm : ∀ n : ℕ, n ≤ N →
      (∑ colour : Fin D.rank, (tau colour : ℂ) • term colour n) =
        -((bilinear D sigma tau : ℂ) / 2) •
          (collisionR n • shiftField D hu (1 + n) (A (N - n))) +
        if n = 0 then -((chargeNorm D tau : ℂ) / 2) •
          shiftField D hu 1 (A N) else 0) :
    (∑ colour : Fin D.rank, (tau colour : ℂ) •
      (singletonLinear D hu (colour, 0) (A N) +
        ∑ n ∈ Finset.range (bound + 1), term colour n)) =
      normalCurrent D hu tau (A N) -
        ((chargeNorm D tau : ℂ) / 2) • shiftField D hu 1 (A N) -
        ((bilinear D sigma tau : ℂ) / 2) •
          ∑ n ∈ Finset.range (N + 1), collisionR n •
            shiftField D hu (1 + n) (A (N - n)) := by
  classical
  have padded :
      (∑ colour : Fin D.rank, (tau colour : ℂ) •
        (singletonLinear D hu (colour, 0) (A N) +
          ∑ n ∈ Finset.range (bound + 1), term colour n)) =
      ∑ colour : Fin D.rank, (tau colour : ℂ) •
        (singletonLinear D hu (colour, 0) (A N) +
          ∑ n ∈ Finset.range (N + 1), term colour n) := by
    apply Finset.sum_congr rfl
    intro colour member
    rw [pad colour]
  rw [padded]
  simp only [smul_add]
  rw [Finset.sum_add_distrib]
  have normal : (∑ colour : Fin D.rank, (tau colour : ℂ) •
      singletonLinear D hu (colour, 0) (A N)) =
      normalCurrent D hu tau (A N) := by
    simp only [normalCurrent, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [normal]
  have swap :
      (∑ colour : Fin D.rank, (tau colour : ℂ) •
        ∑ n ∈ Finset.range (N + 1), term colour n) =
      ∑ n ∈ Finset.range (N + 1),
        ∑ colour : Fin D.rank, (tau colour : ℂ) • term colour n := by
    calc
      _ = ∑ colour : Fin D.rank, ∑ n ∈ Finset.range (N + 1),
          (tau colour : ℂ) • term colour n := by
        apply Finset.sum_congr rfl
        intro colour member
        rw [Finset.smul_sum]
      _ = _ := by rw [Finset.sum_comm]
  rw [swap]
  have terms :
      (∑ n ∈ Finset.range (N + 1),
        ∑ colour : Fin D.rank, (tau colour : ℂ) • term colour n) =
      -((bilinear D sigma tau : ℂ) / 2) •
          (∑ n ∈ Finset.range (N + 1), collisionR n •
            shiftField D hu (1 + n) (A (N - n))) +
        -((chargeNorm D tau : ℂ) / 2) • shiftField D hu 1 (A N) := by
    calc
      _ = ∑ n ∈ Finset.range (N + 1),
          (-((bilinear D sigma tau : ℂ) / 2) •
              (collisionR n • shiftField D hu (1 + n) (A (N - n))) +
            if n = 0 then -((chargeNorm D tau : ℂ) / 2) •
              shiftField D hu 1 (A N) else 0) := by
        apply Finset.sum_congr rfl
        intro n member
        exact weightedTerm n (by have h := Finset.mem_range.mp member; omega)
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.smul_sum]
        simp
  rw [terms]
  module

private theorem chargeInsertion_pad_generic (D : LatticeData) (hu : IsUnit D.G.det)
    (N bound cutoff : ℕ)
    (hcutoff : cutoff = max bound N)
    (term : Fin D.rank → ℕ → NativeField D hu)
    (outsideBound : ∀ (colour : Fin D.rank) (n : ℕ), bound < n → term colour n = 0)
    (outsideDegree : ∀ (colour : Fin D.rank) (n : ℕ), N < n → term colour n = 0) :
    ∀ colour : Fin D.rank,
      (∑ n ∈ Finset.range (bound + 1), term colour n) =
        ∑ n ∈ Finset.range (N + 1), term colour n := by
  intro colour
  have first : (∑ n ∈ Finset.range (bound + 1), term colour n) =
      ∑ n ∈ Finset.range (cutoff + 1), term colour n := by
    apply Finset.sum_subset (Finset.range_mono (by rw [hcutoff]; omega))
    intro n member outside
    exact outsideBound colour n (by
      simp only [Finset.mem_range, not_lt] at outside
      omega)
  have second : (∑ n ∈ Finset.range (N + 1), term colour n) =
      ∑ n ∈ Finset.range (cutoff + 1), term colour n := by
    apply Finset.sum_subset (Finset.range_mono (by rw [hcutoff]; omega))
    intro n member outside
    exact outsideDegree colour n (by
      simp only [Finset.mem_range, not_lt] at outside
      omega)
  exact first.trans second.symm

set_option maxHeartbeats 8000000 in
private theorem chargeInsertion_support_actual (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (N : ℕ) (b : Carrier D) (bound : ℕ)
    (term : Fin D.rank → ℕ → NativeField D hu)
    (bound_eq : bound = LatticeSugawaraCurrents.vectorFrequencyBound D b)
    (b_eq : b = Finsupp.single (sigma + tau) (creationCoeff D sigma N))
    (term_eq : ∀ (colour : Fin D.rank) (n : ℕ),
      term colour n =
        ((halfBinomial 1 * halfBinomial n) / (1 + (n : ℂ))) •
          shiftField D hu (1 + n) (correctedField D hu
            (LatticeFiniteNegativeGeneration.neutralMode D colour (n : ℤ) b)))
    (modes : ∀ (colour : Fin D.rank) (n : ℕ),
      LatticeFiniteNegativeGeneration.neutralMode D colour (n : ℤ)
          (Finsupp.single (sigma + tau) (creationCoeff D sigma N)) =
        if n = 0 then
          (bilinear D (unitCharge D colour) (sigma + tau) : ℂ) •
            Finsupp.single (sigma + tau) (creationCoeff D sigma N)
        else
          (bilinear D (unitCharge D colour) sigma : ℂ) •
            Finsupp.single (sigma + tau)
              (creationCoeff D sigma ((N : ℤ) - (n : ℤ)))) :
    (∀ (colour : Fin D.rank) (n : ℕ), bound < n → term colour n = 0) ∧
      (∀ (colour : Fin D.rank) (n : ℕ), N < n → term colour n = 0) := by
  constructor
  · intro colour n outside
    have vanished := LatticeSugawaraCurrents.neutralMode_vanish D colour b n (by
      rw [bound_eq] at outside
      exact_mod_cast outside)
    rw [term_eq colour n, vanished]
    simp
  · intro colour n outside
    have positive : n ≠ 0 := by omega
    have negative : (N : ℤ) - (n : ℤ) < 0 := by omega
    have vanished : LatticeFiniteNegativeGeneration.neutralMode D colour (n : ℤ) b = 0 := by
      rw [b_eq]
      simpa only [if_neg positive, creationCoeff, dif_pos negative,
        Finsupp.single_zero, smul_zero] using modes colour n
    rw [term_eq colour n, vanished]
    simp

/- Pad the source-mode sum at max(originalCutoff,N+1),
   use zero above original source frequency bound and zero shifted degree
   for n>N, then separate n=0. NEVER assume N<=vectorFrequencyBound S_N.
   h_1=-1/2; n=0 contributes -(B+Qt)/2 at shift 1.
   This is a generic cleanup of the actual chargeInsertion constructor,
   not an assumed compatibility law. -/
set_option maxHeartbeats 4000000 in
theorem chargeInsertion_field_identity (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (N : ℕ) (modes : ∀ (colour : Fin D.rank) (n : ℕ),
      LatticeFiniteNegativeGeneration.neutralMode D colour (n : ℤ)
          (Finsupp.single (sigma + tau) (creationCoeff D sigma N)) =
        if n = 0 then
          (bilinear D (unitCharge D colour) (sigma + tau) : ℂ) •
            Finsupp.single (sigma + tau) (creationCoeff D sigma N)
        else
          (bilinear D (unitCharge D colour) sigma : ℂ) •
            Finsupp.single (sigma + tau)
              (creationCoeff D sigma ((N : ℤ) - (n : ℤ)))) :
    chargeInsertion D hu tau
      (Finsupp.single (sigma + tau) (creationCoeff D sigma N)) =
      normalCurrent D hu tau
        (correctedField D hu
          (Finsupp.single (sigma + tau) (creationCoeff D sigma N))) -
      ((chargeNorm D tau : ℂ) / 2) •
        shiftField D hu 1
          (correctedField D hu
            (Finsupp.single (sigma + tau) (creationCoeff D sigma N))) -
      ((bilinear D sigma tau : ℂ) / 2) •
        ∑ j ∈ Finset.range (N + 1), collisionR j •
          shiftField D hu (1 + j)
            (correctedField D hu
              (Finsupp.single (sigma + tau) (creationCoeff D sigma (N - j)))) := by
  classical
  let b : Carrier D := Finsupp.single (sigma + tau) (creationCoeff D sigma N)
  let A (k : ℕ) : NativeField D hu :=
    correctedField D hu (Finsupp.single (sigma + tau) (creationCoeff D sigma k))
  let bound := LatticeSugawaraCurrents.vectorFrequencyBound D b
  let cutoff := max bound N
  let term (colour : Fin D.rank) (n : ℕ) : NativeField D hu :=
    ((halfBinomial 1 * halfBinomial n) / (1 + (n : ℂ))) •
      shiftField D hu (1 + n) (correctedField D hu
        (LatticeFiniteNegativeGeneration.neutralMode D colour (n : ℤ) b))
  have support := chargeInsertion_support_actual D hu sigma tau N b bound term
    (by rfl) (by rfl) (by intro colour n; rfl) modes
  have outsideBound := support.1
  have outsideDegree := support.2
  have pad := chargeInsertion_pad_generic D hu N bound cutoff (by rfl) term
    outsideBound outsideDegree
  have weightedTerm (n : ℕ) (within : n ≤ N) :
      (∑ colour : Fin D.rank, (tau colour : ℂ) • term colour n) =
        -((bilinear D sigma tau : ℂ) / 2) •
          (collisionR n • shiftField D hu (1 + n) (A (N - n))) +
        if n = 0 then -((chargeNorm D tau : ℂ) / 2) •
          shiftField D hu 1 (A N) else 0 := by
    exact chargeInsertion_weighted_term_alias
      (D := D) (hu := hu) (sigma := sigma) (tau := tau)
      (N := N) (n := n) (within := within) (A := A) (term := term)
      (term_eq := by intro colour; rfl)
      (A_eq := by intro k; rfl) (modes := modes)
  have fieldIdentity : chargeInsertion D hu tau b =
      normalCurrent D hu tau (A N) -
        ((chargeNorm D tau : ℂ) / 2) • shiftField D hu 1 (A N) -
        ((bilinear D sigma tau : ℂ) / 2) •
          ∑ n ∈ Finset.range (N + 1), collisionR n •
            shiftField D hu (1 + n) (A (N - n)) := by
    unfold chargeInsertion
    change (∑ colour : Fin D.rank, (tau colour : ℂ) •
      (singletonLinear D hu (colour, 0) (A N) +
        ∑ n ∈ Finset.range (bound + 1), term colour n)) = _
    exact chargeInsertion_sum_identity
      (D := D) (hu := hu) (sigma := sigma) (tau := tau) (N := N)
      (bound := bound) (A := A) (term := term) pad weightedTerm
  have sumDegree :
      (∑ j ∈ Finset.range (N + 1), collisionR j •
        shiftField D hu (1 + j) (A (N - j))) =
      ∑ j ∈ Finset.range (N + 1), collisionR j •
        shiftField D hu (1 + j)
          (correctedField D hu
            (Finsupp.single (sigma + tau)
              (creationCoeff D sigma ((N : ℤ) - (j : ℤ))))) := by
    apply Finset.sum_congr rfl
    intro j member
    have within : j ≤ N := by
      have h := Finset.mem_range.mp member
      omega
    have degree : ((N - j : ℕ) : ℤ) = (N : ℤ) - (j : ℤ) := by omega
    dsimp only [A]
    rw [degree]
  rw [sumDegree] at fieldIdentity
  exact fieldIdentity

end
end D5.S3.VertexAlgebra.LatticeHalfFockChargedCollision
