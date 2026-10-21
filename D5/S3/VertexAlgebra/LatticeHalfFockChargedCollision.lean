/- GID: D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockChargedCollision
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite signed coefficients for the charged collision comparison. -/

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

private theorem bare_source_product (D : LatticeData) (sigma tau : Charge D) (r : ℤ) :
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

private def chargeInsertion (D : LatticeData) (hu : IsUnit D.G.det)
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

private theorem corrected_creation_step (D : LatticeData) (hu : IsUnit D.G.det)
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

private def diagonalTerm (D : LatticeData) (sigma tau : Charge D)
    (N : ℕ) (total offset m : ℤ) : Oscillator D :=
  collisionScalar (m - offset - chargeNorm D sigma) (bilinear D sigma tau) N •
    (halfCreationCoeff D sigma m * halfCreationCoeff D tau (total - m))

private theorem diagonal_as_sum (D : LatticeData) (sigma tau : Charge D)
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

private def collisionDiagonal (D : LatticeData) (sigma tau : Charge D)
    (N : ℕ) (e : ℤ) (d : Fin 2 →₀ ℕ) : Oscillator D :=
  let total : ℤ := e + chargeNorm D (sigma + tau) + 2 * N + d 0 + d 1
  if total < 0 then 0 else
    ∑ m ∈ Finset.range (total.toNat + 1),
      diagonalTerm D sigma tau N total (d 0) m

private def collisionConvolution (D : LatticeData) (sigma tau : Charge D)
    (N : ℕ) (e : ℤ) : PairPolynomial D →ₗ[Oscillator D] Oscillator D :=
  (Finsupp.lsum (Oscillator D) (fun d : Fin 2 →₀ ℕ =>
    LinearMap.mulRight (Oscillator D) (collisionDiagonal D sigma tau N e d))).comp
      (AddMonoidAlgebra.coeffLinearEquiv (Oscillator D)).toLinearMap

/-- A finite coefficient of the normalized two-charge normal symbol. -/
def collisionOscillator (D : LatticeData) (sigma tau : Charge D)
    (N : ℕ) (e : ℤ) : Module.End ℂ (Oscillator D) :=
  ((collisionConvolution D sigma tau N e).restrictScalars ℂ).comp
    (LatticeHalfFockProductKernel.pairTranslation D sigma tau).toLinearMap

private theorem collision_expansion (D : LatticeData) (sigma tau : Charge D)
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

private def translatedDegree (D : LatticeData) (sigma tau : Charge D)
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

private def normalCurrent (D : LatticeData) (hu : IsUnit D.G.det)
    (tau : Charge D) : NativeField D hu →ₗ[ℂ] NativeField D hu :=
  ∑ colour : Fin D.rank, (tau colour : ℂ) • singletonLinear D hu (colour, 0)

private def collisionR (j : ℕ) : ℂ := halfBinomial j / (j + 1 : ℂ)

/- Formal-series calculation:
   s²=1+h; 2/(s+1)=Σ collisionR j h^j;
   2(1+h) f'=(A-2B+B Σ collisionR j h^j)f.
   The type contains scalar series only, not the desired module law. -/
private theorem collisionScalar_recurrence (A B : ℤ) (N : ℕ) :
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
private theorem source_neutral_creation (D : LatticeData)
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
private theorem chargeInsertion_field_identity (D : LatticeData) (hu : IsUnit D.G.det)
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

private theorem chargeInsertion_closed (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (N : ℕ) (e : ℤ) (x : ActualTensor D hu)
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
    (chargeInsertion D hu tau
      (Finsupp.single (sigma + tau) (creationCoeff D sigma N))).coeff e x =
      (normalCurrent D hu tau
        (correctedField D hu
          (Finsupp.single (sigma + tau) (creationCoeff D sigma N)))).coeff e x -
      ((chargeNorm D tau : ℂ) / 2) •
        (correctedField D hu
          (Finsupp.single (sigma + tau) (creationCoeff D sigma N))).coeff (e + 2) x -
      ((bilinear D sigma tau : ℂ) / 2) •
        ∑ j ∈ Finset.range (N + 1), collisionR j •
          (correctedField D hu
            (Finsupp.single (sigma + tau) (creationCoeff D sigma (N - j)))).coeff
              (e + 2 * ((j : ℤ) + 1)) x := by
  have fieldIdentity := chargeInsertion_field_identity D hu sigma tau N modes
  have evaluated := congrArg
    (fun F : NativeField D hu => F.coeff e x) fieldIdentity
  simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply,
    LinearMap.sub_apply, LinearMap.smul_apply] at evaluated
  rw [map_sum] at evaluated
  rw [Finset.sum_apply] at evaluated
  rw [LinearMap.sum_apply] at evaluated
  have shifted (n : ℕ) :
      (HVertexOperator.coeff
          ((shiftField D hu (1 + n))
            (correctedField D hu
              (Finsupp.single (sigma + tau) (creationCoeff D sigma (N - n))))) e) x =
        (HVertexOperator.coeff
          (correctedField D hu
            (Finsupp.single (sigma + tau) (creationCoeff D sigma (N - n))))
          (e + 2 * ((n : ℤ) + 1))) x := by
    simpa only [Nat.cast_add, Nat.cast_one, add_comm] using
      congrArg (fun L => L x)
        (shiftField_coefficient_public D hu (1 + n)
          (correctedField D hu
            (Finsupp.single (sigma + tau) (creationCoeff D sigma (N - n)))) e)
  have shiftedOne :
      (HVertexOperator.coeff
          ((shiftField D hu 1)
            (correctedField D hu
              (Finsupp.single (sigma + tau) (creationCoeff D sigma N)))) e) x =
        (HVertexOperator.coeff
          (correctedField D hu
            (Finsupp.single (sigma + tau) (creationCoeff D sigma N)))
          (e + 2)) x := by
    exact congrArg (fun L => L x)
      (shiftField_coefficient_public D hu 1
        (correctedField D hu
          (Finsupp.single (sigma + tau) (creationCoeff D sigma N))) e)
  have sumTransport :
      (∑ j ∈ Finset.range (N + 1),
        (HVertexOperator.coeff
          (collisionR j •
            ((shiftField D hu (1 + j))
              (correctedField D hu
                (Finsupp.single (sigma + tau)
                  (creationCoeff D sigma (N - j)))))) e) x) =
        ∑ j ∈ Finset.range (N + 1), collisionR j •
          (HVertexOperator.coeff
            (correctedField D hu
              (Finsupp.single (sigma + tau)
                (creationCoeff D sigma (N - j))))
            (e + 2 * ((j : ℤ) + 1))) x := by
    apply Finset.sum_congr rfl
    intro j member
    simp only [map_smul, Pi.smul_apply, LinearMap.smul_apply]
    rw [shifted j]
  rw [sumTransport] at evaluated
  rw [shiftedOne] at evaluated
  simpa only [HVertexOperator.coeff_of_coeff, Nat.cast_add, Nat.cast_one] using evaluated

private theorem source_closed_recurrence (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (N : ℕ) (e : ℤ) (x : ActualTensor D hu) :
    (N + 1 : ℂ) •
        (correctedField D hu
          (Finsupp.single (sigma + tau) (creationCoeff D sigma (N + 1)))).coeff e x =
      (((e + 2 : ℤ) : ℂ) / 2) •
        (correctedField D hu
          (Finsupp.single (sigma + tau) (creationCoeff D sigma N))).coeff (e + 2) x -
      (normalCurrent D hu tau
        (correctedField D hu
          (Finsupp.single (sigma + tau) (creationCoeff D sigma N)))).coeff e x +
      ((chargeNorm D tau : ℂ) / 2) •
        (correctedField D hu
          (Finsupp.single (sigma + tau) (creationCoeff D sigma N))).coeff (e + 2) x +
      ((bilinear D sigma tau : ℂ) / 2) •
        ∑ j ∈ Finset.range (N + 1), collisionR j •
          (correctedField D hu
            (Finsupp.single (sigma + tau) (creationCoeff D sigma (N - j)))).coeff
              (e + 2 * ((j : ℤ) + 1)) x := by
  rw [corrected_creation_step,
    chargeInsertion_closed D hu sigma tau N e x
      (source_neutral_creation D sigma tau N)]
  module

/- The finite moment readout for the normal current. -/
private def collisionMoment (D : LatticeData) (sigma tau : Charge D)
    (N : ℕ) (e : ℤ) (p : Oscillator D) : Oscillator D :=
  let T := LatticeHalfFockProductKernel.pairTranslation D sigma tau p
  ∑ d ∈ T.support, T.coeff d *
    (let L : ℤ := e + 2 + chargeNorm D (sigma + tau) + 2 * N + d 0 + d 1
     if L < 0 then 0 else
       ∑ m ∈ Finset.range (L.toNat + 1),
         ((((L - (m : ℤ) - (d 1 : ℤ)) : ℤ) : ℂ) / 2) •
           diagonalTerm D sigma tau N L (d 0) m)

/- Arbitrary-input singleton calculation. Negative
   current modes j=-k-1 give n/2 by exponential_derivative;
   nonnegative j=k give -d1/2 by Y*d/dY(pairTranslation p).
   Explicit finite supports: negative branch from collision_lower_bound;
   positive branch from p.vars, with each transformed input read separately. -/
private theorem collision_normal_moment (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (N : ℕ) (e : ℤ)
    (p : Oscillator D) (g : ActualGround D hu) :
    (normalCurrent D hu tau (collisionField D hu sigma tau N)).coeff e
        (p ⊗ₜ[ℂ] g) =
      chargeScalar D (sigma + tau) •
        (collisionMoment D sigma tau N e p ⊗ₜ[ℂ]
          groundAction D hu (sigma + tau) g) := by
  classical
  let F := collisionField D hu sigma tau N
  let v : ActualTensor D hu := p ⊗ₜ[ℂ] g
  let lower : ℤ := min
    (-chargeNorm D (sigma + tau) - 2 * (N : ℤ) -
      (translatedDegree D sigma tau p : ℤ) - e - 3) 0
  let support (colour : Fin D.rank) : Finset (ModeTuple D [(colour, 0)]) :=
    modeBox D [(colour, 0)] lower (LatticeHalfFock.bound D p)
  let oscillatorTerm (colour : Fin D.rank)
      (modes : ModeTuple D [(colour, 0)]) : Oscillator D :=
    if modes.1 < 0 then
      LatticeHalfFock.current D colour modes.1
        (collisionOscillator D sigma tau N (e + 2 * modes.1 + 3) p)
    else collisionOscillator D sigma tau N (e + 2 * modes.1 + 3)
      (LatticeHalfFock.current D colour modes.1 p)
  have flat (colour : Fin D.rank) (modes : ModeTuple D [(colour, 0)]) :
      flatTerm D hu F [(colour, 0)] e v modes =
        chargeScalar D (sigma + tau) •
          (oscillatorTerm colour modes ⊗ₜ[ℂ] groundAction D hu (sigma + tau) g) := by
    rcases modes with ⟨mode, tail⟩
    cases tail
    by_cases negative : mode < 0 <;>
      simp only [F, v, oscillatorTerm, flatTerm, flatCoefficient, jetCurrent,
        jetScalar, Finset.range_zero, Finset.prod_empty, Nat.factorial_zero,
        Nat.cast_one, div_one, one_smul, Nat.cast_zero, mul_zero, add_zero,
        negative, reduceIte, collisionField, HVertexOperator.coeff_of_coeff,
        collisionCoefficient, Module.End.mul_apply, LinearMap.smul_apply,
        LatticeHalfFock.tensorCurrent, LatticeHalfFock.tensorEnd,
        TensorProduct.map_tmul, LinearMap.id_apply, map_smul]
  have oscillatorBelow (q : Oscillator D) (z : ℤ)
      (low : z < -chargeNorm D (sigma + tau) - 2 * (N : ℤ) -
        (translatedDegree D sigma tau q : ℤ)) :
      collisionOscillator D sigma tau N z q = 0 := by
    rw [collision_expansion]
    apply Finset.sum_eq_zero
    intro d member
    have degree := Finset.le_sup (f := fun d : Fin 2 →₀ ℕ => d 0 + d 1) member
    have castDegree : (d 0 : ℤ) + (d 1 : ℤ) ≤ translatedDegree D sigma tau q := by
      exact_mod_cast degree
    rw [diagonal_as_sum, if_pos (by omega), mul_zero]
  have oscillatorSupport (colour : Fin D.rank) :
      Function.support (oscillatorTerm colour) ⊆ support colour := by
    rintro ⟨mode, tail⟩ nonzero
    cases tail
    have lowerBound : lower ≤ mode := by
      by_contra outside
      have negative : mode < 0 := by dsimp [lower] at outside; omega
      have low : e + 2 * mode + 3 <
          -chargeNorm D (sigma + tau) - 2 * (N : ℤ) -
            (translatedDegree D sigma tau p : ℤ) := by
        dsimp [lower] at outside
        omega
      exact nonzero (by
        simp only [oscillatorTerm, if_pos negative, oscillatorBelow p _ low, map_zero])
    have upperBound : mode ≤ (LatticeHalfFock.bound D p : ℤ) := by
      by_contra outside
      have nonnegative : 0 ≤ mode := by omega
      have zero := LatticeHalfFock.current_vanish D colour p mode (by omega)
      exact nonzero (by simp only [oscillatorTerm, if_neg (not_lt.mpr nonnegative),
        zero, map_zero])
    change (mode, ()) ∈ (Finset.Icc lower (LatticeHalfFock.bound D p : ℤ)).product {()}
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨lowerBound, upperBound⟩, Finset.mem_singleton_self ()⟩
  have finiteCoefficient :
      (normalCurrent D hu tau F).coeff e v =
        ∑ colour : Fin D.rank, (tau colour : ℂ) •
          ∑ modes ∈ support colour, flatTerm D hu F [(colour, 0)] e v modes := by
    have expanded : (normalCurrent D hu tau F).coeff e v =
        ∑ colour : Fin D.rank, (tau colour : ℂ) •
          (wordField D hu F [(colour, 0)]).coeff e v := by
      simp [normalCurrent, singletonLinear]
    rw [expanded]
    apply Finset.sum_congr rfl
    intro colour member
    congr 1
    rw [wordField_coefficient]
    apply finsum_eq_sum_of_support_subset
    intro modes supported
    apply oscillatorSupport colour
    intro zero
    exact supported (by rw [flat, zero, TensorProduct.zero_tmul, smul_zero])
  have reduction :
      (normalCurrent D hu tau F).coeff e v =
        chargeScalar D (sigma + tau) •
          ((∑ colour : Fin D.rank, (tau colour : ℂ) •
            ∑ modes ∈ support colour, oscillatorTerm colour modes) ⊗ₜ[ℂ]
              groundAction D hu (sigma + tau) g) := by
    rw [finiteCoefficient]
    simp_rw [flat, TensorProduct.smul_tmul']
    simp only [TensorProduct.sum_tmul, TensorProduct.smul_tmul',
      Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro colour member
    apply Finset.sum_congr rfl
    intro modes mode_member
    congr 1
    module
  change (normalCurrent D hu tau F).coeff e v = _
  rw [reduction]
  apply congrArg (fun q : Oscillator D => chargeScalar D (sigma + tau) •
    (q ⊗ₜ[ℂ] groundAction D hu (sigma + tau) g))
  /- Every helper below is local to this proof.  The polynomial convolution
     is used as a linear map, so its application to T(current p) reads that
     transformed polynomial's own support. -/
  let T := LatticeHalfFockProductKernel.pairTranslation D sigma tau
  let readout (z : ℤ) : PairPolynomial D →ₗ[ℂ] Oscillator D :=
    (collisionConvolution D sigma tau N z).restrictScalars ℂ
  have readout_monomial (z : ℤ) (d : Fin 2 →₀ ℕ) (c : Oscillator D) :
      readout z (MvPolynomial.monomial d c) =
        c * collisionDiagonal D sigma tau N z d := by
      change collisionConvolution D sigma tau N z (MvPolynomial.monomial d c) = _
      simp [collisionConvolution, MvPolynomial.monomial]
  have readout_second_shift (z : ℤ) (w : ℕ) (Q : PairPolynomial D) :
      readout z (MvPolynomial.X 1 ^ w * Q) = readout (z + w) Q := by
    induction Q using MvPolynomial.induction_on' with
    | add Q R hQ hR => simp only [mul_add, map_add, hQ, hR]
    | monomial d c =>
      rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial,
        readout_monomial, readout_monomial]
      simp only [one_mul]
      have diagonal_shift :
          collisionDiagonal D sigma tau N z (Finsupp.single 1 w + d) =
            collisionDiagonal D sigma tau N (z + w) d := by
        unfold collisionDiagonal
        simp only [Finsupp.add_apply, Finsupp.single_eq_same,
          Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), zero_add]
        have total : z + chargeNorm D (sigma + tau) + 2 * (N : ℤ) +
            (d 0 : ℤ) + ((w + d 1 : ℕ) : ℤ) =
            z + w + chargeNorm D (sigma + tau) + 2 * (N : ℤ) + d 0 + d 1 := by
          push_cast
          ring
        rw [total]
      rw [diagonal_shift]
  have euler_monomial (d : Fin 2 →₀ ℕ) (c : Oscillator D) :
      MvPolynomial.X 1 * MvPolynomial.pderiv 1 (MvPolynomial.monomial d c) =
        (d 1 : ℂ) • MvPolynomial.monomial d c := by
    have h := MvPolynomial.X_mul_pderiv_monomial
      (i := (1 : Fin 2)) (m := d) (r := c)
    convert h using 1 <;>
      simp [MvPolynomial.smul_monomial, nsmul_eq_mul, Algebra.smul_def,
        mul_comm]
  have readout_euler (z : ℤ) (Q : PairPolynomial D) :
      readout z (MvPolynomial.X 1 * MvPolynomial.pderiv 1 Q) =
        ∑ d ∈ Q.support, (d 1 : ℂ) •
          (Q.coeff d * collisionDiagonal D sigma tau N z d) := by
    conv_lhs => rw [MvPolynomial.as_sum Q]
    simp only [map_sum, Finset.mul_sum, euler_monomial, map_smul,
      readout_monomial]

  let pairEuler : PairPolynomial D →ₗ[ℂ] PairPolynomial D :=
    (LinearMap.mulLeft ℂ (MvPolynomial.X 1 : PairPolynomial D)).comp
      ((MvPolynomial.pderiv (R := Oscillator D) (1 : Fin 2)).toLinearMap.restrictScalars ℂ)
  /- This is a chain rule on the full polynomial, not a hypothesis of
     homogeneity.  The finite support is q.vars; pderiv counts every
     occurrence of a repeated variable. -/
  have pair_euler (q : Oscillator D) :
      MvPolynomial.X 1 * MvPolynomial.pderiv 1 (T q) =
        ∑ index ∈ q.vars,
          (-((omega D index : ℕ) : ℂ) *
            (bilinear D tau (unitCharge D index.1) : ℂ)) •
            (MvPolynomial.X 1 ^ omega D index * T (MvPolynomial.pderiv index q)) := by
    letI : Algebra (Oscillator D) (PairPolynomial D) := T.toRingHom.toAlgebra
    letI : Module (Oscillator D) (PairPolynomial D) :=
      (T.toRingHom.toAlgebra).toModule
    letI : IsScalarTower ℂ (Oscillator D) (PairPolynomial D) :=
      { smul_assoc := by
          intro c a b
          change T (c • a) * b = c • (T a * b)
          rw [map_smul, smul_mul_assoc] }
    let transportedPartial (index : Index D) :
        Derivation ℂ (Oscillator D) (PairPolynomial D) :=
      { toFun := fun q => T (MvPolynomial.pderiv index q)
        map_add' := by intro q r; simp only [map_add]
        map_smul' := by
          intro c q
          rw [Derivation.map_smul, map_smul]
          rfl
        map_one_eq_zero' := by
          change T (MvPolynomial.pderiv index 1) = 0
          rw [MvPolynomial.pderiv_one, map_zero]
        leibniz' := by
          intro q r
          change T (MvPolynomial.pderiv index (q * r)) =
            T q * T (MvPolynomial.pderiv index r) +
              T r * T (MvPolynomial.pderiv index q)
          rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul]
          ring }
    let delta : Derivation ℂ (Oscillator D) (PairPolynomial D) :=
      { toFun := fun q => pairEuler (T q)
        map_add' := by intro q r; simp only [map_add]
        map_smul' := by
          intro c q
          change pairEuler (T (c • q)) = c • pairEuler (T q)
          rw [map_smul, map_smul]
        map_one_eq_zero' := by
          change pairEuler (T 1) = 0
          dsimp [pairEuler]
          simp
        leibniz' := by
          intro q r
          dsimp
          change pairEuler (T (q * r)) =
            q • pairEuler (T r) + r • pairEuler (T q)
          simp only [Algebra.smul_def]
          change MvPolynomial.X 1 * MvPolynomial.pderiv 1 (T (q * r)) =
            T q * (MvPolynomial.X 1 * MvPolynomial.pderiv 1 (T r)) +
              T r * (MvPolynomial.X 1 * MvPolynomial.pderiv 1 (T q))
          rw [map_mul, MvPolynomial.pderiv_mul]
          ring }
    have derivation_sum_apply
        (s : Finset (Index D))
        (f : Index D → Derivation ℂ (Oscillator D) (PairPolynomial D))
        (r : Oscillator D) : (∑ index ∈ s, f index) r = ∑ index ∈ s, f index r := by
      have h := congrFun (map_sum
        (Derivation.coeFnAddMonoidHom (R := ℂ) (A := Oscillator D)
          (M := PairPolynomial D)) f s) r
      simpa only [Derivation.coeFnAddMonoidHom_apply, Finset.sum_apply] using h
    have expansion : delta q =
        ∑ index ∈ q.vars, delta (MvPolynomial.X index) *
          T (MvPolynomial.pderiv index q) := by
      have h : delta q =
          (∑ index ∈ q.vars, delta (MvPolynomial.X index) • transportedPartial index) q := by
        apply MvPolynomial.derivation_eq_of_forall_mem_vars
        intro index member
        rw [derivation_sum_apply]
        simp [transportedPartial, Derivation.smul_apply,
          MvPolynomial.pderiv_X, Pi.single_apply, apply_ite, member]
      rw [derivation_sum_apply] at h
      change delta q =
        ∑ index ∈ q.vars, delta (MvPolynomial.X index) *
          T (MvPolynomial.pderiv index q) at h
      exact h
    have variableValue (index : Index D) : delta (MvPolynomial.X index) =
        (-((omega D index : ℕ) : ℂ) *
          (bilinear D tau (unitCharge D index.1) : ℂ)) •
            MvPolynomial.X 1 ^ omega D index := by
      change MvPolynomial.X 1 * MvPolynomial.pderiv 1
        (T (MvPolynomial.X index)) = _
      simp only [T, LatticeHalfFockProductKernel.pairTranslation,
        MvPolynomial.eval₂AlgHom_X]
      have coordinate (i : Fin 2) (w : ℕ) (c : Oscillator D) :
          MvPolynomial.X 1 * MvPolynomial.pderiv 1
              (MvPolynomial.C c * MvPolynomial.X i ^ w) =
            ((Finsupp.single i w) 1 : ℂ) •
              (MvPolynomial.C c * MvPolynomial.X i ^ w) := by
        simpa only [MvPolynomial.C_mul_X_pow_eq_monomial] using
          euler_monomial (Finsupp.single i w) c
      simp only [LatticeHalfFockProductKernel.pairTranslationVariable,
        map_sub, mul_sub, MvPolynomial.pderiv_C, mul_zero, mul_neg, coordinate,
        Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
        Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1),
        Nat.cast_zero, zero_smul, sub_zero, zero_sub]
      simp [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm]
    change delta q = _
    rw [expansion]
    apply Finset.sum_congr rfl
    intro index member
    rw [variableValue, smul_mul_assoc]

  have positive_polynomial (q : Oscillator D) :
      (∑ colour : Fin D.rank, (tau colour : ℂ) •
        ∑ k ∈ Finset.range (LatticeHalfFock.bound D q + 1),
          MvPolynomial.X 1 ^ (2 * k + 1) *
            T (LatticeHalfFock.current D colour (k : ℤ) q)) =
        -(1 / 2 : ℂ) •
          (MvPolynomial.X 1 * MvPolynomial.pderiv 1 (T q)) := by
    have gram (other : Fin D.rank) : (∑ colour : Fin D.rank,
        (tau colour : ℂ) * (D.G colour other : ℂ)) =
        (bilinear D tau (unitCharge D other) : ℂ) := by
      have intGram : bilinear D tau (unitCharge D other) =
          ∑ colour : Fin D.rank, tau colour * D.G colour other := by
        simp [bilinear, unitCharge]
      rw [intGram]
      push_cast
      rfl
    have current_sum (k : ℕ) :
        (∑ colour : Fin D.rank, (tau colour : ℂ) •
          LatticeHalfFock.current D colour (k : ℤ) q) =
        ∑ other : Fin D.rank,
          (((k : ℂ) + 1 / 2) *
            (bilinear D tau (unitCharge D other) : ℂ)) •
              MvPolynomial.pderiv (other, k) q := by
      simp only [LatticeHalfFock.current,
        if_neg (by omega : ¬ (k : ℤ) < 0), Int.toNat_natCast,
        LinearMap.smul_apply, LatticeHalfFock.frequency, Int.cast_natCast,
        LatticeActualAnnihilation.annihilate, LatticeSugawaraCurrents.weightedPartial,
        LinearMap.sum_apply, LinearMap.smul_apply, Derivation.coeFn_coe,
        Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro other member
      rw [← Finset.sum_smul]
      congr 1
      calc
        (∑ colour : Fin D.rank,
            (tau colour : ℂ) * (((k : ℂ) + 1 / 2) * (D.G colour other : ℂ))) =
            ((k : ℂ) + 1 / 2) *
              ∑ colour : Fin D.rank, (tau colour : ℂ) * (D.G colour other : ℂ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro colour _
          ring
        _ = _ := by rw [gram]
    have vars_box : q.vars ⊆ (Finset.univ : Finset (Fin D.rank)) ×ˢ
        Finset.range (LatticeHalfFock.bound D q + 1) := by
      intro index member
      have bound := Finset.le_sup (f := fun x : Index D => x.2 + 1) member
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_range.mpr (by
        change index.2 + 1 ≤ LatticeHalfFock.bound D q at bound
        omega)⟩
    have pad :
        (∑ index ∈ q.vars,
          (-((omega D index : ℕ) : ℂ) *
            (bilinear D tau (unitCharge D index.1) : ℂ)) •
            (MvPolynomial.X 1 ^ omega D index * T (MvPolynomial.pderiv index q))) =
        ∑ index ∈ (Finset.univ : Finset (Fin D.rank)) ×ˢ
            Finset.range (LatticeHalfFock.bound D q + 1),
          (-((omega D index : ℕ) : ℂ) *
            (bilinear D tau (unitCharge D index.1) : ℂ)) •
            (MvPolynomial.X 1 ^ omega D index * T (MvPolynomial.pderiv index q)) := by
      apply Finset.sum_subset vars_box
      intro index member absent
      rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars absent, map_zero,
        mul_zero, smul_zero]
    calc
      _ = ∑ k ∈ Finset.range (LatticeHalfFock.bound D q + 1),
          MvPolynomial.X 1 ^ (2 * k + 1) *
            T (∑ colour : Fin D.rank, (tau colour : ℂ) •
              LatticeHalfFock.current D colour (k : ℤ) q) := by
        simp only [map_sum, map_smul, Finset.mul_sum, Finset.smul_sum,
          mul_smul_comm]
        rw [Finset.sum_comm]
      _ = ∑ k ∈ Finset.range (LatticeHalfFock.bound D q + 1),
          ∑ other : Fin D.rank,
            (((k : ℂ) + 1 / 2) * (bilinear D tau (unitCharge D other) : ℂ)) •
              (MvPolynomial.X 1 ^ (2 * k + 1) *
                T (MvPolynomial.pderiv (other, k) q)) := by
        simp only [current_sum, map_sum, map_smul, Finset.mul_sum, mul_smul_comm]
      _ = -(1 / 2 : ℂ) •
          (MvPolynomial.X 1 * MvPolynomial.pderiv 1 (T q)) := by
        rw [pair_euler, pad, Finset.sum_product_right]
        simp only [Finset.smul_sum, smul_smul]
        apply Finset.sum_congr rfl
        intro k member
        apply Finset.sum_congr rfl
        intro other _
        congr 1
        simp only [omega, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
        ring

  have positive_readout :
      (∑ colour : Fin D.rank, (tau colour : ℂ) •
        ∑ k ∈ Finset.range (LatticeHalfFock.bound D p + 1),
          collisionOscillator D sigma tau N (e + 2 * (k : ℤ) + 3)
            (LatticeHalfFock.current D colour (k : ℤ) p)) =
        -(1 / 2 : ℂ) • readout (e + 2)
          (MvPolynomial.X 1 * MvPolynomial.pderiv 1 (T p)) := by
    have h := congrArg (readout (e + 2)) (positive_polynomial p)
    simp only [map_sum, map_smul, readout_second_shift] at h
    have shifts (k : ℕ) : e + 2 + ((2 * k + 1 : ℕ) : ℤ) =
        e + 2 * (k : ℤ) + 3 := by omega
    simpa only [shifts, T, readout, collisionOscillator,
      AlgHom.toLinearMap_apply,
      LinearMap.comp_apply, LinearMap.restrictScalars_apply] using h

  let cutoff : ℕ := (-lower).toNat
  let U (k : ℕ) : Oscillator D :=
    ∑ colour : Fin D.rank, (tau colour : ℂ) • MvPolynomial.X (colour, k)
  let total (d : Fin 2 →₀ ℕ) : ℤ :=
    e + 2 + chargeNorm D (sigma + tau) + 2 * (N : ℤ) + d 0 + d 1
  let creatorDiagonal (d : Fin 2 →₀ ℕ) : Oscillator D :=
    if total d < 0 then 0 else
      ∑ m ∈ Finset.range ((total d).toNat + 1),
        ((((total d - (m : ℤ)) : ℤ) : ℂ) / 2) •
          diagonalTerm D sigma tau N (total d) (d 0) m
  let creatorMoment : Oscillator D :=
    ∑ d ∈ (T p).support, (T p).coeff d * creatorDiagonal d
  have lower_nonpositive : lower ≤ 0 := min_le_right _ _
  have cutoff_cast : (cutoff : ℤ) = -lower :=
    Int.toNat_of_nonneg (by omega)
  have total_bound (d : Fin 2 →₀ ℕ) (member : d ∈ (T p).support) :
      total d < (cutoff : ℤ) := by
    have degree : d 0 + d 1 ≤ translatedDegree D sigma tau p :=
      Finset.le_sup (f := fun d : Fin 2 →₀ ℕ => d 0 + d 1) member
    have degreeCast : (d 0 : ℤ) + d 1 ≤ translatedDegree D sigma tau p := by
      exact_mod_cast degree
    rw [cutoff_cast]
    dsimp [total, lower]
    omega

  /- The two finite diagonals below are compared after multiplying by the
     actual scalar/left-creator coefficient.  No separate copy or exposure
     of the protected signed creation recurrence is introduced. -/
  have negative_diagonal (d : Fin 2 →₀ ℕ) (bounded : total d < (cutoff : ℤ)) :
      (∑ k ∈ Finset.range cutoff, U k *
        collisionDiagonal D sigma tau N (e + 2 - (2 * k + 1 : ℕ)) d) =
        creatorDiagonal d := by
    let L : ℤ := total d
    have shifted_total (k : ℕ) :
        e + 2 - ((2 * k + 1 : ℕ) : ℤ) + chargeNorm D (sigma + tau) +
            2 * (N : ℤ) + (d 0 : ℤ) + d 1 = L - (2 * k + 1 : ℕ) := by
      dsimp [L, total]
      omega
    by_cases negative : L < 0
    · change (∑ k ∈ Finset.range cutoff, U k *
          collisionDiagonal D sigma tau N (e + 2 - (2 * k + 1 : ℕ)) d) =
          if L < 0 then 0 else _
      rw [if_pos negative]
      apply Finset.sum_eq_zero
      intro k member
      simp only [collisionDiagonal, shifted_total,
        if_pos (by omega : L - (2 * k + 1 : ℕ) < 0), mul_zero]
    · have nonnegative : 0 ≤ L := by omega
      have pad (k : ℕ) :
          collisionDiagonal D sigma tau N (e + 2 - (2 * k + 1 : ℕ)) d =
            ∑ m ∈ Finset.range (L.toNat + 1),
              diagonalTerm D sigma tau N (L - (2 * k + 1 : ℕ)) (d 0) m := by
        simp only [collisionDiagonal, shifted_total]
        by_cases outside : L - (2 * k + 1 : ℕ) < 0
        · rw [if_pos outside]
          symm
          apply Finset.sum_eq_zero
          intro m member
          simp [diagonalTerm, halfCreationCoeff,
            show L - (2 * k + 1 : ℕ) - (m : ℤ) < 0 by omega]
          intro hm
          omega
        · rw [if_neg outside]
          apply Finset.sum_subset (Finset.range_mono (by omega))
          intro m member absent
          have large : (L - (2 * k + 1 : ℕ)).toNat < m := by
            have h : ¬ m < (L - (2 * k + 1 : ℕ)).toNat + 1 :=
              by simpa only [Finset.mem_range] using absent
            omega
          simp [diagonalTerm, halfCreationCoeff,
            show L - (2 * k + 1 : ℕ) - (m : ℤ) < 0 by omega]
          intro hm
          omega
      change _ = if L < 0 then 0 else _
      rw [if_neg negative]
      simp_rw [pad, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m member
      have m_bound : (m : ℤ) ≤ L := by
        have hm := Finset.mem_range.mp member
        omega
      let n : ℤ := L - m
      let prefactor : Oscillator D :=
        collisionScalar ((m : ℤ) - d 0 - chargeNorm D sigma)
          (bilinear D sigma tau) N • halfCreationCoeff D sigma m
      have term (k : ℕ) :
          U k * diagonalTerm D sigma tau N (L - (2 * k + 1 : ℕ)) (d 0) m =
            prefactor * U k * halfCreationCoeff D tau (n - (2 * k + 1 : ℕ)) := by
        dsimp [diagonalTerm, prefactor, n]
        have same : L - (2 * (k : ℤ) + 1) - (m : ℤ) =
            L - (m : ℤ) - (2 * (k : ℤ) + 1) := by ring
        rw [same]
        simp only [smul_mul_assoc, mul_smul_comm]
        congr 1
        ring
      have unshifted : diagonalTerm D sigma tau N L (d 0) m =
          prefactor * halfCreationCoeff D tau n := by
        simp only [diagonalTerm, prefactor, n, smul_mul_assoc]
      simp_rw [term]
      rw [unshifted]
      change (∑ k ∈ Finset.range cutoff,
          prefactor * U k * halfCreationCoeff D tau (n - (2 * k + 1 : ℕ))) =
        ((n : ℂ) / 2) • (prefactor * halfCreationCoeff D tau n)
      have n_nonnegative : 0 ≤ n := by dsimp [n]; omega
      have n_bound : n < (cutoff : ℤ) := by dsimp [n, L] at *; omega
      by_cases n_zero : n = 0
      · simp only [n_zero, Int.cast_zero, zero_div, zero_smul]
        apply Finset.sum_eq_zero
        intro k _
        rw [halfCreationCoeff, if_pos (by omega), mul_zero]
      · let degree : ℕ := n.toNat
        let r : ℕ := degree - 1
        have degree_cast : (degree : ℤ) = n := Int.toNat_of_nonneg n_nonnegative
        have degree_positive : 0 < degree := by omega
        have r_succ : r + 1 = degree := by dsimp [r]; omega
        have degree_le_cutoff : degree ≤ cutoff := by omega
        let driver (j : ℕ) : Oscillator D :=
          PowerSeries.coeff j (PowerSeries.derivative (R := Oscillator D)
            (halfCreationSeries D tau)) * halfCreationCoeff D tau (n - 1 - j)
        have even_driver (k : ℕ) : driver (2 * k) =
            (2 : ℂ) • (U k * halfCreationCoeff D tau (n - (2 * k + 1 : ℕ))) := by
          have even : (2 * k) % 2 = 0 := by omega
          have index : (2 * k) / 2 = k := by omega
          have shift : n - 1 - ((2 * k : ℕ) : ℤ) = n - (2 * k + 1 : ℕ) := by omega
          simp only [driver, series_derivative_coeff, if_pos even, index,
            shift, U, smul_mul_assoc]
        have odd_driver (k : ℕ) : driver (2 * k + 1) = 0 := by
          have odd : ¬ (2 * k + 1) % 2 = 0 := by omega
          simp only [driver, series_derivative_coeff, if_neg odd, zero_mul]
        have pairs (b : ℕ) :
            (∑ j ∈ Finset.range (2 * b), driver j) =
              ∑ k ∈ Finset.range b,
                (2 : ℂ) • (U k * halfCreationCoeff D tau (n - (2 * k + 1 : ℕ))) := by
          induction b with
          | zero => simp
          | succ b previous =>
            rw [show 2 * (b + 1) = (2 * b + 1) + 1 by omega,
              Finset.sum_range_succ, Finset.sum_range_succ, previous,
              Finset.sum_range_succ, even_driver, odd_driver, add_zero]
        have pad_driver : (∑ j ∈ Finset.range degree, driver j) =
            ∑ j ∈ Finset.range (2 * cutoff), driver j := by
          apply Finset.sum_subset (Finset.range_mono (by omega))
          intro j member absent
          have high : degree ≤ j := by simpa only [Finset.mem_range, not_lt] using absent
          have neg : n - 1 - (j : ℤ) < 0 := by omega
          simp only [driver, halfCreationCoeff, if_pos neg, mul_zero]
        have coefficient_product : PowerSeries.coeff r
            (halfCreationExponential D tau *
              PowerSeries.derivative (R := Oscillator D) (halfCreationSeries D tau)) =
            ∑ j ∈ Finset.range degree, driver j := by
          have r_succ' : r.succ = degree := by omega
          rw [mul_comm, PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, r_succ']
          apply Finset.sum_congr rfl
          intro j member
          have small : j < degree := Finset.mem_range.mp member
          have nonnegative_shift : 0 ≤ n - 1 - (j : ℤ) := by omega
          have index : (n - 1 - (j : ℤ)).toNat = r - j := by dsimp [r]; omega
          simp only [driver, halfCreationCoeff, if_neg (not_lt.mpr nonnegative_shift), index]
        have differentiated := congrArg
          (fun f : PowerSeries (Oscillator D) =>
            (1 / 2 : ℂ) • (prefactor * PowerSeries.coeff r f))
          (exponential_derivative D tau)
        have left_coefficient :
            (1 / 2 : ℂ) • (prefactor * PowerSeries.coeff r
              (PowerSeries.derivative (R := Oscillator D) (halfCreationExponential D tau))) =
              ((n : ℂ) / 2) • (prefactor * halfCreationCoeff D tau n) := by
          have scaled_coefficient : PowerSeries.coeff r
              (PowerSeries.derivative (R := Oscillator D) (halfCreationExponential D tau)) =
              (degree : ℂ) • PowerSeries.coeff degree (halfCreationExponential D tau) := by
            have cast_degree : (r : Oscillator D) + 1 = (degree : Oscillator D) := by
              exact_mod_cast r_succ
            rw [PowerSeries.coeff_derivative, r_succ, cast_degree]
            simp only [Algebra.smul_def, map_natCast]
            ring
          rw [scaled_coefficient, halfCreationCoeff,
            if_neg (not_lt.mpr n_nonnegative)]
          simp only [degree, mul_smul_comm, smul_smul]
          congr 1
          have complex_degree : (degree : ℂ) = (n : ℂ) := by exact_mod_cast degree_cast
          change (1 / 2 : ℂ) * (degree : ℂ) = (n : ℂ) / 2
          rw [complex_degree]
          ring
        rw [left_coefficient, coefficient_product, pad_driver, pairs] at differentiated
        simp only [Finset.mul_sum, Finset.smul_sum, mul_smul_comm,
          smul_smul, show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul] at differentiated
        simpa only [mul_assoc] using differentiated.symm

  have readout_expansion (z : ℤ) (Q : PairPolynomial D) :
      readout z Q = ∑ d ∈ Q.support,
        Q.coeff d * collisionDiagonal D sigma tau N z d := by
    rfl
  have negative_readout :
      (∑ colour : Fin D.rank, (tau colour : ℂ) •
        ∑ k ∈ Finset.range cutoff,
          MvPolynomial.X (colour, k) *
            collisionOscillator D sigma tau N (e + 2 - (2 * k + 1 : ℕ)) p) =
        creatorMoment := by
    calc
      _ = ∑ k ∈ Finset.range cutoff,
          U k * readout (e + 2 - (2 * k + 1 : ℕ)) (T p) := by
        simp only [U, Finset.sum_mul, smul_mul_assoc, Finset.smul_sum,
          collisionOscillator, readout, T, LinearMap.comp_apply,
          LinearMap.restrictScalars_apply]
        exact Finset.sum_comm
      _ = ∑ d ∈ (T p).support, (T p).coeff d *
          ∑ k ∈ Finset.range cutoff, U k *
            collisionDiagonal D sigma tau N (e + 2 - (2 * k + 1 : ℕ)) d := by
        simp only [readout_expansion, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro d member
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = creatorMoment := by
        apply Finset.sum_congr rfl
        intro d member
        rw [negative_diagonal d (total_bound d member)]

  have moment_decomposition : collisionMoment D sigma tau N e p =
      creatorMoment - (1 / 2 : ℂ) •
        readout (e + 2) (MvPolynomial.X 1 * MvPolynomial.pderiv 1 (T p)) := by
    rw [readout_euler]
    change (∑ d ∈ (T p).support, (T p).coeff d *
        (if total d < 0 then 0 else
          ∑ m ∈ Finset.range ((total d).toNat + 1),
            ((((total d - (m : ℤ) - (d 1 : ℤ)) : ℤ) : ℂ) / 2) •
              diagonalTerm D sigma tau N (total d) (d 0) m)) = _
    dsimp only [creatorMoment]
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d member
    have ordinary_diagonal : collisionDiagonal D sigma tau N (e + 2) d =
        if total d < 0 then 0 else
          ∑ m ∈ Finset.range ((total d).toNat + 1),
            diagonalTerm D sigma tau N (total d) (d 0) m := by rfl
    rw [ordinary_diagonal]
    dsimp only [creatorDiagonal]
    by_cases negative : total d < 0
    · simp only [if_pos negative, mul_zero, smul_zero, sub_zero]
    · simp only [if_neg negative, Finset.mul_sum, Finset.smul_sum,
        mul_smul_comm, smul_smul]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro m mMember
      rw [← sub_smul]
      congr 1
      push_cast
      ring

  have mode_split (colour : Fin D.rank) :
      (∑ modes ∈ support colour, oscillatorTerm colour modes) =
        (∑ k ∈ Finset.range cutoff, MvPolynomial.X (colour, k) *
          collisionOscillator D sigma tau N (e + 2 - (2 * k + 1 : ℕ)) p) +
        ∑ k ∈ Finset.range (LatticeHalfFock.bound D p + 1),
          collisionOscillator D sigma tau N (e + 2 * (k : ℤ) + 3)
            (LatticeHalfFock.current D colour (k : ℤ) p) := by
    let negativeModes : Finset ℤ := (Finset.range cutoff).image (fun k : ℕ => -(k : ℤ) - 1)
    let positiveModes : Finset ℤ :=
      (Finset.range (LatticeHalfFock.bound D p + 1)).image (fun k : ℕ => (k : ℤ))
    have cover : Finset.Icc lower (LatticeHalfFock.bound D p : ℤ) =
        negativeModes ∪ positiveModes := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_union, negativeModes, positiveModes,
        Finset.mem_image, Finset.mem_range]
      constructor
      · intro bounds
        by_cases sign : j < 0
        · left
          refine ⟨(-j - 1).toNat, ?_, ?_⟩ <;> omega
        · right
          refine ⟨j.toNat, ?_, ?_⟩ <;> omega
      · rintro (⟨k, within, rfl⟩ | ⟨k, within, rfl⟩) <;> constructor <;> omega
    have disjoint : Disjoint negativeModes positiveModes := by
      apply Finset.disjoint_left.mpr
      intro j left right
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp left
      obtain ⟨l, hl, eq⟩ := Finset.mem_image.mp right
      omega
    change (∑ modes ∈ (Finset.Icc lower (LatticeHalfFock.bound D p : ℤ)).product {()},
      oscillatorTerm colour modes) = _
    have productSum :
        (∑ modes ∈ (Finset.Icc lower (LatticeHalfFock.bound D p : ℤ)).product {()},
          oscillatorTerm colour modes) =
          ∑ mode ∈ Finset.Icc lower (LatticeHalfFock.bound D p : ℤ),
            ∑ unit ∈ ({()} : Finset Unit), oscillatorTerm colour (mode, unit) := by
      calc
        _ = ∑ modes ∈ (Finset.Icc lower (LatticeHalfFock.bound D p : ℤ)).product {()},
            oscillatorTerm colour (modes.1, modes.2) := by
          apply Finset.sum_congr rfl
          intro modes member
          cases modes
          rfl
        _ = _ := by
          exact Finset.sum_product'
            (s := Finset.Icc lower (LatticeHalfFock.bound D p : ℤ))
            (t := ({()} : Finset Unit))
            (f := fun mode unit => oscillatorTerm colour (mode, unit))
    rw [productSum]
    simp only [Finset.sum_singleton]
    rw [cover, Finset.sum_union disjoint]
    rw [Finset.sum_image (by
      intro a ha b hb equality
      have equality' : (a : ℤ) = (b : ℤ) := by linarith [equality]
      exact_mod_cast equality'),
      Finset.sum_image (by
        intro a ha b hb equality
        have equality' : (a : ℤ) = (b : ℤ) := by
          simpa only using equality
        exact_mod_cast equality')]
    congr 1
    · apply Finset.sum_congr rfl
      intro k member
      have negative : -(k : ℤ) - 1 < 0 := by omega
      have shift : e + 2 * (-(k : ℤ) - 1) + 3 =
          e + 2 - (2 * k + 1 : ℕ) := by omega
      simp only [oscillatorTerm, if_pos negative, LatticeHalfFock.current_negative,
        LinearMap.mulLeft_apply, shift]
  simp_rw [mode_split, smul_add]
  rw [Finset.sum_add_distrib, negative_readout, positive_readout, moment_decomposition]
  rw [neg_smul, sub_eq_add_neg]


/- Finite oscillator sum balance from the scalar recurrence.
   Expand collision_expansion/diagonal_as_sum, put
     L=e+Qa+2(N+1)+d0+d1, n=L-m, A=m-d0-Qs.
   All j terms have the same L, because j<=N.
   The scalar balance is
     (e+2)/2-(n-d1)/2+Qt/2 = A/2-N-B.
   If L<0 every term is zero. Otherwise interchange only the two finite
   sums j<=N and 0<=m<=L, apply scalarStep at each (d,m), distribute.
   This obligation contains neither correctedField nor singletonLinear. -/
private theorem collision_finite_balance (D : LatticeData) (sigma tau : Charge D)
    (N : ℕ) (e : ℤ) (p : Oscillator D)
    (scalarStep : ∀ (A B : ℤ) (k : ℕ),
      (k + 1 : ℂ) * collisionScalar A B (k + 1) =
        ((A : ℂ) / 2 - (k : ℂ) - (B : ℂ)) * collisionScalar A B k +
          ((B : ℂ) / 2) * ∑ j ∈ Finset.range (k + 1),
            collisionR j * collisionScalar A B (k - j)) :
    (N + 1 : ℂ) • collisionOscillator D sigma tau (N + 1) e p =
      (((e + 2 : ℤ) : ℂ) / 2) • collisionOscillator D sigma tau N (e + 2) p -
      collisionMoment D sigma tau N e p +
      ((chargeNorm D tau : ℂ) / 2) • collisionOscillator D sigma tau N (e + 2) p +
      ((bilinear D sigma tau : ℂ) / 2) •
        ∑ j ∈ Finset.range (N + 1), collisionR j •
          collisionOscillator D sigma tau (N - j) (e + 2 * ((j : ℤ) + 1)) p := by
  classical
  have addLeft (a b c : Charge D) : bilinear D (a + b) c =
      bilinear D a c + bilinear D b c := by
    simp [bilinear, add_mul, Finset.sum_add_distrib]
  have addRight (a b c : Charge D) : bilinear D a (b + c) =
      bilinear D a b + bilinear D a c := by
    simp [bilinear, mul_add, Finset.sum_add_distrib]
  have normAdd : chargeNorm D (sigma + tau) =
      chargeNorm D sigma + chargeNorm D tau + 2 * bilinear D sigma tau := by
    unfold chargeNorm
    rw [addLeft, addRight, addRight,
      LatticeFiniteNegativeGeneration.bilinear_symmetric D tau sigma]
    ring
  let T := LatticeHalfFockProductKernel.pairTranslation D sigma tau p
  let total (d : Fin 2 →₀ ℕ) : ℤ :=
    e + chargeNorm D (sigma + tau) + 2 * ((N + 1 : ℕ) : ℤ) + d 0 + d 1
  let moment (d : Fin 2 →₀ ℕ) : Oscillator D :=
    if total d < 0 then 0 else
      ∑ m ∈ Finset.range ((total d).toNat + 1),
        ((((total d - (m : ℤ) - (d 1 : ℤ)) : ℤ) : ℂ) / 2) •
          diagonalTerm D sigma tau N (total d) (d 0) m
  have nowTotal (d : Fin 2 →₀ ℕ) :
      e + 2 + chargeNorm D (sigma + tau) + 2 * (N : ℤ) + d 0 + d 1 =
        total d := by
    dsimp [total]
    push_cast
    ring
  have shiftedTotal (d : Fin 2 →₀ ℕ) (j : ℕ) (within : j ≤ N) :
      e + 2 * ((j : ℤ) + 1) + chargeNorm D (sigma + tau) +
        2 * ((N - j : ℕ) : ℤ) + d 0 + d 1 = total d := by
    dsimp [total]
    omega
  have expand (k : ℕ) (z : ℤ) : collisionOscillator D sigma tau k z p =
      ∑ d ∈ T.support, T.coeff d * collisionDiagonal D sigma tau k z d := by
    rw [collision_expansion]
    simp_rw [diagonal_as_sum]
    rfl
  have momentExpansion : collisionMoment D sigma tau N e p =
      ∑ d ∈ T.support, T.coeff d * moment d := by
    unfold collisionMoment
    apply Finset.sum_congr rfl
    intro d member
    dsimp only [moment]
    rw [nowTotal]
  have diagonalBalance (d : Fin 2 →₀ ℕ) :
      (N + 1 : ℂ) • collisionDiagonal D sigma tau (N + 1) e d =
        (((e + 2 : ℤ) : ℂ) / 2) • collisionDiagonal D sigma tau N (e + 2) d -
          moment d +
        ((chargeNorm D tau : ℂ) / 2) • collisionDiagonal D sigma tau N (e + 2) d +
        ((bilinear D sigma tau : ℂ) / 2) •
          ∑ j ∈ Finset.range (N + 1), collisionR j •
            collisionDiagonal D sigma tau (N - j) (e + 2 * ((j : ℤ) + 1)) d := by
    have now : collisionDiagonal D sigma tau N (e + 2) d =
        if total d < 0 then 0 else
          ∑ m ∈ Finset.range ((total d).toNat + 1),
            diagonalTerm D sigma tau N (total d) (d 0) m := by
      simp only [collisionDiagonal, nowTotal]
    have next : collisionDiagonal D sigma tau (N + 1) e d =
        if total d < 0 then 0 else
          ∑ m ∈ Finset.range ((total d).toNat + 1),
            diagonalTerm D sigma tau (N + 1) (total d) (d 0) m := rfl
    have shifted (j : ℕ) (member : j ∈ Finset.range (N + 1)) :
        collisionDiagonal D sigma tau (N - j) (e + 2 * ((j : ℤ) + 1)) d =
          if total d < 0 then 0 else
            ∑ m ∈ Finset.range ((total d).toNat + 1),
              diagonalTerm D sigma tau (N - j) (total d) (d 0) m := by
      simp only [collisionDiagonal, shiftedTotal d j (by
        have bound := Finset.mem_range.mp member
        omega)]
    rw [next, now]
    have shiftedSum :
        (∑ j ∈ Finset.range (N + 1), collisionR j •
          collisionDiagonal D sigma tau (N - j) (e + 2 * ((j : ℤ) + 1)) d) =
        ∑ j ∈ Finset.range (N + 1), collisionR j •
          (if total d < 0 then 0 else
            ∑ m ∈ Finset.range ((total d).toNat + 1),
              diagonalTerm D sigma tau (N - j) (total d) (d 0) m) := by
      apply Finset.sum_congr rfl
      intro j member
      rw [shifted j member]
    rw [shiftedSum]
    dsimp only [moment]
    by_cases negative : total d < 0
    · simp only [if_pos negative, smul_zero, sub_zero, add_zero,
        Finset.sum_const_zero]
    · simp only [if_neg negative]
      have swap :
          (∑ j ∈ Finset.range (N + 1), collisionR j •
            ∑ m ∈ Finset.range ((total d).toNat + 1),
              diagonalTerm D sigma tau (N - j) (total d) (d 0) m) =
          ∑ m ∈ Finset.range ((total d).toNat + 1),
            ∑ j ∈ Finset.range (N + 1), collisionR j •
              diagonalTerm D sigma tau (N - j) (total d) (d 0) m := by
        simp_rw [Finset.smul_sum]
        rw [Finset.sum_comm]
      rw [swap]
      simp_rw [Finset.smul_sum]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m member
      let A : ℤ := (m : ℤ) - (d 0 : ℤ) - chargeNorm D sigma
      have balance :
          (((e + 2 : ℤ) : ℂ) / 2) -
              (((total d - (m : ℤ) - (d 1 : ℤ) : ℤ) : ℂ) / 2) +
              ((chargeNorm D tau : ℂ) / 2) =
            (A : ℂ) / 2 - (N : ℂ) - (bilinear D sigma tau : ℂ) := by
        dsimp only [A, total]
        rw [normAdd]
        push_cast
        ring
      have coefficient := scalarStep A (bilinear D sigma tau) N
      rw [← balance] at coefficient
      have scalarIdentity := congrArg
        (fun c : ℂ => c • (halfCreationCoeff D sigma (m : ℤ) *
          halfCreationCoeff D tau (total d - (m : ℤ)))) coefficient
      dsimp [A, diagonalTerm] at scalarIdentity ⊢
      rw [smul_smul, smul_smul, smul_smul]
      simp_rw [smul_smul]
      rw [← Finset.sum_smul, ← sub_smul, ← add_smul, ← add_smul]
      convert scalarIdentity using 1
      congr 1
      rw [Finset.mul_sum]
      ring
  have weightedBalance (d : Fin 2 →₀ ℕ) :
      (N + 1 : ℂ) • (T.coeff d * collisionDiagonal D sigma tau (N + 1) e d) =
        (((e + 2 : ℤ) : ℂ) / 2) •
            (T.coeff d * collisionDiagonal D sigma tau N (e + 2) d) -
          T.coeff d * moment d +
        ((chargeNorm D tau : ℂ) / 2) •
          (T.coeff d * collisionDiagonal D sigma tau N (e + 2) d) +
        ((bilinear D sigma tau : ℂ) / 2) •
          ∑ j ∈ Finset.range (N + 1), collisionR j •
            (T.coeff d *
              collisionDiagonal D sigma tau (N - j) (e + 2 * ((j : ℤ) + 1)) d) := by
    have mul_smul (c : ℂ) (q : Oscillator D) :
        T.coeff d * (c • q) = c • (T.coeff d * q) :=
      Algebra.mul_smul_comm c (T.coeff d) q
    have weighted := congrArg (fun q : Oscillator D => T.coeff d * q) (diagonalBalance d)
    simp_rw [mul_smul] at weighted
    simp only [mul_add, mul_sub] at weighted
    simp only [Finset.mul_sum, mul_smul] at weighted
    simpa only [Algebra.smul_mul_assoc, mul_assoc, mul_add, Int.cast_add,
      Int.cast_one] using weighted
  simp_rw [expand]
  rw [momentExpansion]
  have swap :
      (∑ j ∈ Finset.range (N + 1), collisionR j •
        ∑ d ∈ T.support, T.coeff d *
          collisionDiagonal D sigma tau (N - j) (e + 2 * ((j : ℤ) + 1)) d) =
      ∑ d ∈ T.support, ∑ j ∈ Finset.range (N + 1), collisionR j •
        (T.coeff d *
          collisionDiagonal D sigma tau (N - j) (e + 2 * ((j : ℤ) + 1)) d) := by
    simp_rw [Finset.smul_sum]
    rw [Finset.sum_comm]
  rw [swap]
  simp_rw [Finset.smul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d member
  simpa only [Finset.smul_sum] using weightedBalance d

private theorem collision_closed_recurrence (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (N : ℕ) (e : ℤ) (x : ActualTensor D hu) :
    (N + 1 : ℂ) • collisionCoefficient D hu sigma tau (N + 1) e x =
      (((e + 2 : ℤ) : ℂ) / 2) • collisionCoefficient D hu sigma tau N (e + 2) x -
      (normalCurrent D hu tau (collisionField D hu sigma tau N)).coeff e x +
      ((chargeNorm D tau : ℂ) / 2) • collisionCoefficient D hu sigma tau N (e + 2) x +
      ((bilinear D sigma tau : ℂ) / 2) •
        ∑ j ∈ Finset.range (N + 1), collisionR j •
          collisionCoefficient D hu sigma tau (N - j) (e + 2 * ((j : ℤ) + 1)) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p g =>
    rw [collision_normal_moment]
    have balance := congrArg
      (fun q : Oscillator D => chargeScalar D (sigma + tau) •
        (q ⊗ₜ[ℂ] groundAction D hu (sigma + tau) g))
      (collision_finite_balance D sigma tau N e p collisionScalar_recurrence)
    simp only [collisionCoefficient, LinearMap.smul_apply, TensorProduct.map_tmul,
      TensorProduct.add_tmul, TensorProduct.sub_tmul, TensorProduct.smul_tmul',
      TensorProduct.sum_tmul, smul_add, smul_sub, Finset.smul_sum,
      smul_smul, mul_comm, mul_left_comm, mul_assoc] at balance ⊢
    simpa only [smul_smul, mul_comm, mul_left_comm, mul_assoc] using balance
  | add x y hx hy =>
    simp only [map_add, smul_add, Finset.sum_add_distrib] at hx hy ⊢
    linear_combination hx + hy

private theorem collision_scalar_zero (A B : ℤ) : collisionScalar A B 0 = 1 := by
  have constantUnit :
      Units.map PowerSeries.constantCoeff.toMonoidHom collisionUnit = 1 := by
    apply Units.ext
    change PowerSeries.constantCoeff (collisionUnit : PowerSeries ℂ) = 1
    unfold collisionUnit
    rw [IsUnit.unit_spec]
    rw [PowerSeries.constantCoeff_smul, map_add,
      PowerSeries.binomialSeries_constantCoeff, map_one]
    norm_num
  have constantPower : PowerSeries.constantCoeff
      (((collisionUnit ^ (-2 * B) : (PowerSeries ℂ)ˣ)) : PowerSeries ℂ) = 1 := by
    change (((Units.map PowerSeries.constantCoeff.toMonoidHom
      (collisionUnit ^ (-2 * B))) : ℂˣ) : ℂ) = 1
    rw [MonoidHom.map_zpow, constantUnit, one_zpow]
    rfl
  unfold collisionScalar
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [map_mul, constantPower, mul_one]
  rw [PowerSeries.binomialSeries_constantCoeff]

/- Charge addition for the actual half creation series. This coefficient
   induction uses only the public differential equation and constant term.
   Each product coefficient is its finite natural antidiagonal. -/
private theorem half_creation_exponential_add (D : LatticeData) (sigma tau : Charge D) :
    halfCreationExponential D (sigma + tau) =
      halfCreationExponential D sigma * halfCreationExponential D tau := by
  classical
  have logarithms : halfCreationSeries D (sigma + tau) =
      halfCreationSeries D sigma + halfCreationSeries D tau := by
    ext n
    simp only [halfCreationSeries, PowerSeries.coeff_mk, map_add]
    split_ifs <;> simp [Pi.add_apply, Int.cast_add, add_smul,
      Finset.sum_add_distrib, smul_add]
  let product := halfCreationExponential D sigma * halfCreationExponential D tau
  let driver := PowerSeries.derivative (R := Oscillator D)
    (halfCreationSeries D (sigma + tau))
  have productEquation : PowerSeries.derivative (R := Oscillator D) product =
      product * driver := by
    dsimp only [product, driver]
    rw [(PowerSeries.derivative (R := Oscillator D)).leibniz,
      exponential_derivative, exponential_derivative, logarithms, map_add]
    ring
  have sumEquation : PowerSeries.derivative (R := Oscillator D)
      (halfCreationExponential D (sigma + tau)) =
        halfCreationExponential D (sigma + tau) * driver :=
    exponential_derivative D (sigma + tau)
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n previous =>
    cases n with
    | zero =>
      simp only [product, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero,
        Finset.sum_singleton, exponential_constant, one_mul]
    | succ n =>
      have sumRecurrence := congrArg (PowerSeries.coeff n) sumEquation
      have productRecurrence := congrArg (PowerSeries.coeff n) productEquation
      change PowerSeries.coeff n
          (PowerSeries.derivative (R := Oscillator D)
            (halfCreationExponential D (sigma + tau))) = _ at sumRecurrence
      change PowerSeries.coeff n
          (PowerSeries.derivative (R := Oscillator D) product) = _ at productRecurrence
      conv_lhs at sumRecurrence => rw [PowerSeries.coeff_derivative]
      conv_rhs at sumRecurrence => rw [PowerSeries.coeff_mul]
      conv_lhs at productRecurrence => rw [PowerSeries.coeff_derivative]
      conv_rhs at productRecurrence => rw [PowerSeries.coeff_mul]
      have sameConvolution :
          (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
            PowerSeries.coeff ij.1 (halfCreationExponential D (sigma + tau)) *
              PowerSeries.coeff ij.2 driver) =
          ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
            PowerSeries.coeff ij.1 product * PowerSeries.coeff ij.2 driver := by
        apply Finset.sum_congr rfl
        intro ij member
        rw [previous ij.1 (by
          have degree := Finset.HasAntidiagonal.mem_antidiagonal.mp member
          omega)]
      have scaled := sumRecurrence.trans (sameConvolution.trans productRecurrence.symm)
      have nonzero : (n + 1 : Oscillator D) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero n
      exact mul_right_cancel₀ nonzero scaled

/- The finite creation diagonal is the coefficient of the product of the
   two actual half exponentials. Negative total degrees are retained. -/
private theorem collision_diagonal_zero (D : LatticeData) (sigma tau : Charge D)
    (e : ℤ) (d : Fin 2 →₀ ℕ) :
    collisionDiagonal D sigma tau 0 e d =
      halfCreationCoeff D (sigma + tau)
        (e + chargeNorm D (sigma + tau) + d 0 + d 1) := by
  classical
  let total : ℤ := e + chargeNorm D (sigma + tau) + d 0 + d 1
  simp only [collisionDiagonal, Nat.cast_zero, mul_zero, add_zero]
  change (if total < 0 then 0 else
    ∑ m ∈ Finset.range (total.toNat + 1), diagonalTerm D sigma tau 0 total (d 0) m) =
      halfCreationCoeff D (sigma + tau) total
  by_cases negative : total < 0
  · simp [negative, halfCreationCoeff]
  · rw [if_neg negative, halfCreationCoeff, if_neg negative,
      half_creation_exponential_add, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.sum_congr rfl
    intro m member
    have bound := Finset.mem_range.mp member
    have nonnegative : 0 ≤ total - (m : ℤ) := by omega
    have remaining : (total - (m : ℤ)).toNat = total.toNat - m := by omega
    simp only [diagonalTerm, collision_scalar_zero, one_smul,
      halfCreationCoeff, if_neg (show ¬ (m : ℤ) < 0 by omega),
      if_neg (not_lt.mpr nonnegative), Int.toNat_natCast, remaining]

/- This diagonal is an evaluation of a finite polynomial, with no global
   End-valued support claim. It holds for every target polynomial, including
   every polynomial obtained after a current or derivative transformation. -/
private theorem pair_translation_diagonal (D : LatticeData) (sigma tau : Charge D)
    (p : Oscillator D) :
    (MvPolynomial.eval₂AlgHom (Oscillator D)
      (fun _ : Fin 2 => (Polynomial.X : Polynomial (Oscillator D))))
        (LatticeHalfFockProductKernel.pairTranslation D sigma tau p) =
      halfTranslatedPolynomial D (sigma + tau) p := by
  let diagonal : PairPolynomial D →ₐ[Oscillator D] Polynomial (Oscillator D) :=
    MvPolynomial.eval₂AlgHom (Oscillator D) (fun _ : Fin 2 => Polynomial.X)
  have variableValue (i : Index D) :
      diagonal (LatticeHalfFockProductKernel.pairTranslationVariable D sigma tau i) =
        halfTranslationVariable D (sigma + tau) i := by
    have pairing : bilinear D (sigma + tau) (unitCharge D i.1) =
        bilinear D sigma (unitCharge D i.1) + bilinear D tau (unitCharge D i.1) := by
      simp [bilinear, add_mul, Finset.sum_add_distrib]
    simp [diagonal, LatticeHalfFockProductKernel.pairTranslationVariable,
      halfTranslationVariable, pairing, Int.cast_add, add_smul]
    <;> ring
  change diagonal (LatticeHalfFockProductKernel.pairTranslation D sigma tau p) = _
  induction p using MvPolynomial.induction_on with
  | C scalar =>
    simp [diagonal, LatticeHalfFockProductKernel.pairTranslation,
      halfTranslatedPolynomial]
  | add p q hp hq =>
    simp only [LatticeHalfFockProductKernel.pairTranslation,
      halfTranslatedPolynomial, map_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p i hp =>
    change diagonal (LatticeHalfFockProductKernel.pairTranslation D sigma tau
      (p * MvPolynomial.X i)) = _
    simp only [LatticeHalfFockProductKernel.pairTranslation, halfTranslatedPolynomial,
      map_mul, MvPolynomial.eval₂AlgHom_X] at hp ⊢
    rw [hp, variableValue]

private theorem collision_oscillator_zero (D : LatticeData) (sigma tau : Charge D)
    (e : ℤ) (p : Oscillator D) :
    collisionOscillator D sigma tau 0 e p =
      oscillatorCoefficient D (sigma + tau) e p := by
  classical
  let diagonal : PairPolynomial D →ₐ[Oscillator D] Polynomial (Oscillator D) :=
    MvPolynomial.eval₂AlgHom (Oscillator D) (fun _ : Fin 2 => Polynomial.X)
  let readout : Polynomial (Oscillator D) →ₗ[Oscillator D] Oscillator D :=
    LatticeActualProductKernel.coefficientConvolution
      (halfCreationCoeff D (sigma + tau)) (e + chargeNorm D (sigma + tau))
  have collapse (Q : PairPolynomial D) :
      collisionConvolution D sigma tau 0 e Q = readout (diagonal Q) := by
    induction Q using MvPolynomial.induction_on' with
    | add Q R hQ hR => simp only [map_add, hQ, hR]
    | monomial d c =>
      have monomialDiagonal : diagonal (MvPolynomial.monomial d c) =
          Polynomial.monomial (d 0 + d 1) c := by
        change MvPolynomial.eval₂ (algebraMap (Oscillator D) (Polynomial (Oscillator D)))
          (fun _ : Fin 2 => Polynomial.X) (MvPolynomial.monomial d c) = _
        rw [MvPolynomial.eval₂_monomial,
          Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two, ← pow_add]
        change Polynomial.C c * Polynomial.X ^ (d 0 + d 1) = _
        rw [Polynomial.X_pow_eq_monomial]
        simp
      rw [monomialDiagonal]
      have convolutionMonomial :
          collisionConvolution D sigma tau 0 e (MvPolynomial.monomial d c) =
            c * collisionDiagonal D sigma tau 0 e d := by
        simp [collisionConvolution, MvPolynomial.monomial]
      rw [convolutionMonomial]
      change c * collisionDiagonal D sigma tau 0 e d =
        LatticeActualProductKernel.coefficientConvolution
          (halfCreationCoeff D (sigma + tau)) (e + chargeNorm D (sigma + tau))
            (Polynomial.monomial (d 0 + d 1) c)
      rw [LatticeActualProductKernel.coefficientConvolution_monomial,
        collision_diagonal_zero]
      congr 2
      push_cast
      ring
  change collisionConvolution D sigma tau 0 e
    (LatticeHalfFockProductKernel.pairTranslation D sigma tau p) = _
  rw [collapse]
  have diagonalTranslation : diagonal
      (LatticeHalfFockProductKernel.pairTranslation D sigma tau p) =
        halfTranslatedPolynomial D (sigma + tau) p :=
    pair_translation_diagonal D sigma tau p
  rw [diagonalTranslation]
  change LatticeActualProductKernel.coefficientConvolution
    (halfCreationCoeff D (sigma + tau)) (e + chargeNorm D (sigma + tau))
      (halfTranslatedPolynomial D (sigma + tau) p) = _
  rw [LatticeActualProductKernel.coefficientConvolution_expansion]
  change (∑ n ∈ (halfTranslatedPolynomial D (sigma + tau) p).support,
    (halfTranslatedPolynomial D (sigma + tau) p).coeff n *
      halfCreationCoeff D (sigma + tau) (e + chargeNorm D (sigma + tau) + n)) =
        ∑ᶠ n : ℕ, oscillatorTerm D (sigma + tau) e p n
  rw [finsum_eq_sum_of_support_subset _ (term_support D (sigma + tau) e p)]
  rfl

/- The source side reduces Corr(1) to shift 0/empty word, and P_0=1.
   Collision side: t_0=1, E_sigma E_tau=E_(sigma+tau), evaluate the finite
   pairTranslation diagonal X=Y. Compare actual oscillatorCoefficient on
   arbitrary p, then tensor linearity.
   No extra epsilon: groundAction(a) is on both sides. -/
private theorem collision_base (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (e : ℤ) (x : ActualTensor D hu) :
    (correctedField D hu
      (Finsupp.single (sigma + tau) (creationCoeff D sigma (0 : ℕ)))).coeff e x =
      collisionCoefficient D hu sigma tau 0 e x := by
  classical
  have creationZero : creationCoeff D sigma (0 : ℕ) = (1 : Oscillator D) := by
    simpa [creationCoeff] using LatticeSugawaraConformal.exponential_constant D sigma
  rw [creationZero]
  have corrOne : Corr D (sigma + tau) (1 : Oscillator D) =
      Finsupp.single 0 (1 : Oscillator D) := by
    have emptyEnumeration : ([] : List (Index D)).Perm
        (LatticeAllStateField.occurrences D (0 : Index D →₀ ℕ)) := by
      simp [LatticeAllStateField.occurrences]
    have correction := Corr_monomial_enumeration D (sigma + tau) 0 [] emptyEnumeration
    calc
      _ = shiftCoefficients D (1 : Polynomial (Oscillator D)) := by
        simpa only [show (MvPolynomial.monomial 0 (1 : ℂ) : Oscillator D) = 1 by simp,
          correctionWord, map_one] using correction
      _ = _ := by
        apply Finsupp.ext
        intro n
        change (1 : Polynomial (Oscillator D)).coeff n = (Finsupp.single 0 1) n
        simp [Polynomial.coeff_one, Finsupp.single_apply, eq_comm]
  have seedCoefficient :
      (correctedField D hu (Finsupp.single (sigma + tau) (1 : Oscillator D))).coeff e =
        chargedCoefficient D hu (sigma + tau) e := by
    rw [correctedField, Finsupp.lsum_single, correctedPolynomial, LinearMap.comp_apply,
      corrOne, correctedSum, Finsupp.lsum_single, LinearMap.comp_apply]
    rw [shiftField_coefficient_public]
    simp only [Nat.cast_zero, mul_zero, add_zero]
    rw [show (1 : Oscillator D) = MvPolynomial.monomial 0 (1 : ℂ) by simp,
      polynomialField_monomial_public]
    have emptyOccurrences : occurrences D (0 : Index D →₀ ℕ) = [] := by
      simp [occurrences]
    rw [emptyOccurrences]
    apply LinearMap.ext
    intro input
    rw [wordField_coefficient]
    change (∑ᶠ _ : Unit, (chargedField D hu (sigma + tau)).coeff e input) = _
    rw [finsum_eq_single _ ()]
    · simp only [chargedField, HVertexOperator.coeff_of_coeff]
    · intro modes distinct
      exact (distinct (Subsingleton.elim _ _)).elim
  rw [seedCoefficient]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p g =>
    simp only [chargedCoefficient, collisionCoefficient, LinearMap.smul_apply,
      TensorProduct.map_tmul, collision_oscillator_zero]
  | add x y hx hy => simp only [map_add, hx, hy]

/- Full all-N induction. Every coefficient and every actual input is
   quantified INSIDE the induction property. This transports singletonLinear
   as a whole-field operation, including its transformed inputs. -/
theorem charged_allN_draft (D : LatticeData) (hu : IsUnit D.G.det)
    (sigma tau : Charge D) (N : ℕ) :
    ∀ (e : ℤ) (x : ActualTensor D hu),
      (correctedField D hu
        (Finsupp.single (sigma + tau) (creationCoeff D sigma N))).coeff e x =
          collisionCoefficient D hu sigma tau N e x := by
  classical
  induction N using Nat.strong_induction_on with
  | h N previous =>
    cases N with
    | zero => exact collision_base D hu sigma tau
    | succ N =>
      intro e x
      have fields (k : ℕ) (within : k < N + 1) :
          correctedField D hu
            (Finsupp.single (sigma + tau) (creationCoeff D sigma k)) =
              collisionField D hu sigma tau k := by
        apply HVertexOperator.coeff_inj
        funext output
        apply LinearMap.ext
        intro input
        simpa only [collisionField, HVertexOperator.coeff_of_coeff] using
          previous k within output input
      have source := source_closed_recurrence D hu sigma tau N e x
      have collision := collision_closed_recurrence D hu sigma tau N e x
      have currentEquality :
          (normalCurrent D hu tau
            (correctedField D hu
              (Finsupp.single (sigma + tau) (creationCoeff D sigma N)))).coeff e x =
          (normalCurrent D hu tau (collisionField D hu sigma tau N)).coeff e x := by
        rw [fields N (by omega)]
      have lowerTerms :
          (∑ j ∈ Finset.range (N + 1), collisionR j •
            (correctedField D hu
              (Finsupp.single (sigma + tau) (creationCoeff D sigma (N - j)))).coeff
                (e + 2 * ((j : ℤ) + 1)) x) =
          ∑ j ∈ Finset.range (N + 1), collisionR j •
            collisionCoefficient D hu sigma tau (N - j)
              (e + 2 * ((j : ℤ) + 1)) x := by
        apply Finset.sum_congr rfl
        intro j member
        have hmember : j < N + 1 := Finset.mem_range.mp member
        have castSub : ((N - j : ℕ) : ℤ) = (N : ℤ) - (j : ℤ) := by omega
        rw [← castSub]
        rw [previous (N - j) (by omega)]
      simp only [currentEquality, lowerTerms,
        previous N (by omega) (e + 2) x] at source
      have scaled : (N + 1 : ℂ) •
          (correctedField D hu
            (Finsupp.single (sigma + tau) (creationCoeff D sigma (N + 1)))).coeff e x =
          (N + 1 : ℂ) • collisionCoefficient D hu sigma tau (N + 1) e x :=
        source.trans collision.symm
      have nonzero : (N + 1 : ℂ) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero N
      have cancelled := congrArg
        (fun v : ActualTensor D hu => (N + 1 : ℂ)⁻¹ • v) scaled
      have castSucc : ((N + 1 : ℕ) : ℤ) = (N : ℤ) + 1 := by omega
      simpa only [castSucc, smul_smul, inv_mul_cancel₀ nonzero, one_smul] using cancelled

/- Live ordinary-source consumer. Its source type is Carrier D, and only
   its corrected realization acts on ActualTensor D hu. -/
private theorem charged_source_product_allN_draft
    (D : LatticeData) (hu : IsUnit D.G.det) (sigma tau : Charge D)
    (r e : ℤ) (x : ActualTensor D hu) :
    (correctedField D hu
      (((LatticeAllStateField.Y D (Finsupp.single sigma (1 : Oscillator D)))[[r]])
        (Finsupp.single tau (1 : Oscillator D)))).coeff e x =
      if -r - 1 - bilinear D sigma tau < 0 then 0 else
        epsilon D sigma tau • collisionCoefficient D hu sigma tau
          (-r - 1 - bilinear D sigma tau).toNat e x := by
  rw [bare_source_product, map_smul]
  change epsilon D sigma tau •
    (correctedField D hu
      (Finsupp.single (sigma + tau)
        (creationCoeff D sigma (-r - 1 - bilinear D sigma tau)))).coeff e x = _
  by_cases negative : -r - 1 - bilinear D sigma tau < 0
  · simp [negative, creationCoeff]
  · rw [if_neg negative]
    have castDegree :
        (((-r - 1 - bilinear D sigma tau).toNat : ℕ) : ℤ) =
          -r - 1 - bilinear D sigma tau := Int.toNat_of_nonneg (le_of_not_gt negative)
    have comparison := charged_allN_draft D hu sigma tau
      (-r - 1 - bilinear D sigma tau).toNat e x
    rw [castDegree] at comparison
    exact congrArg (fun v : ActualTensor D hu => epsilon D sigma tau • v) comparison

/- The ordinary two-charge normalization and the actual ground product are
   retained explicitly in this coefficient formula on every tensor input. -/
theorem charged_normalized_source_product_allN
    (D : LatticeData) (hu : IsUnit D.G.det) (sigma tau : Charge D)
    (r e : ℤ) (x : ActualTensor D hu) :
    (correctedField D hu
      (((LatticeAllStateField.Y D (Finsupp.single sigma (1 : Oscillator D)))[[r]])
        (Finsupp.single tau (1 : Oscillator D)))).coeff e x =
      if -r - 1 - bilinear D sigma tau < 0 then 0 else
        (chargeScalar D sigma * chargeScalar D tau *
          (2 : ℂ) ^ (-2 * bilinear D sigma tau)) •
          TensorProduct.map
            (collisionOscillator D sigma tau
              (-r - 1 - bilinear D sigma tau).toNat e)
            (groundAction D hu sigma * groundAction D hu tau) x := by
  have addLeft (a b c : Charge D) : bilinear D (a + b) c =
      bilinear D a c + bilinear D b c := by
    simp [bilinear, add_mul, Finset.sum_add_distrib]
  have addRight (a b c : Charge D) : bilinear D a (b + c) =
      bilinear D a b + bilinear D a c := by
    simp [bilinear, mul_add, Finset.sum_add_distrib]
  have normAdd : chargeNorm D (sigma + tau) =
      chargeNorm D sigma + chargeNorm D tau + 2 * bilinear D sigma tau := by
    unfold chargeNorm
    rw [addLeft, addRight, addRight,
      LatticeFiniteNegativeGeneration.bilinear_symmetric D tau sigma]
    ring
  have normalization : chargeScalar D sigma * chargeScalar D tau *
      (2 : ℂ) ^ (-2 * bilinear D sigma tau) = chargeScalar D (sigma + tau) := by
    unfold chargeScalar
    rw [← zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0),
      ← zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0)]
    congr 1
    omega
  rw [charged_source_product_allN_draft]
  by_cases negative : -r - 1 - bilinear D sigma tau < 0
  · simp only [negative, if_true]
  · simp only [negative, if_false]
    rw [normalization, LatticeHalfFockGroundProducts.ground_action_product,
      TensorProduct.map_smul_right]
    simp only [collisionCoefficient, LinearMap.smul_apply, smul_smul, mul_comm]

end
end D5.S3.VertexAlgebra.LatticeHalfFockChargedCollision
