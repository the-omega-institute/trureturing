/- GID: D5/S3/VertexAlgebra/FormalSeries/SupportedChannelSeries
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/SupportedChannelSeries
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite binomial inversion and legal collision coefficients on supported channels. -/

import D5.S3.VertexAlgebra.StateFieldResidueReconstruction
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Substitution

/-! Classical formal-variable binomial transport. The Mathlib binomial-series
supplier retains Scott Carnahan's attribution. No supplier proof is copied.
proof_shape: content
admission_basis: escape-witness
escape_witness: the right lower support makes each inverse coefficient finite;
unrestricted bivariate distributions do not admit this cancellation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.SupportedChannelSeries
open StateFieldResidueReconstruction (integerBinomial)
open scoped BigOperators
noncomputable section

/-- Multiplication by (x-y)^N in exponent coordinates, with x first. -/
def clear {V : Type*} [AddCommGroup V] [Module ℂ V]
    (N : ℕ) (F : ℤ → ℤ → V) (a b : ℤ) : V :=
  ∑ k ∈ Finset.range (N + 1),
    (((-1 : ℂ) ^ k) * (N.choose k : ℂ)) • F (a - N + k) (b - k)


def powerIndex (a b : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b

@[simp] private theorem powerIndex_zero (a b : ℕ) : powerIndex a b 0 = a := by
  simp [powerIndex]
@[simp] private theorem powerIndex_one (a b : ℕ) : powerIndex a b 1 = b := by
  simp [powerIndex]

/-- Zero extension to signed exponents. -/
def extend {R : Type*} [CommRing R] (P : MvPowerSeries (Fin 2) R) (a b : ℤ) : R :=
  if 0 ≤ a ∧ 0 ≤ b then MvPowerSeries.coeff (powerIndex a.toNat b.toNat) P else 0


/-- Finite signed-binomial convolution. Integer upper indices are retained. -/
def binomialTransform {R : Type*} [CommRing R] [Algebra ℂ R]
    (r : ℤ) (f : ℕ → R) (n : ℕ) : R :=
  ∑ j ∈ Finset.range (n + 1),
    (((-1 : ℂ) ^ j) * integerBinomial r j) • f (n - j)

private def kernel (R : Type*) [CommRing R] [Algebra ℂ R] (r : ℤ) : PowerSeries R :=
  PowerSeries.rescale (-1) (PowerSeries.binomialSeries R r)

private theorem kernel_coeff {R : Type*} [CommRing R] [Algebra ℂ R]
    (r : ℤ) (n : ℕ) :
    PowerSeries.coeff n (kernel R r) =
      (((-1 : ℂ) ^ n) * integerBinomial r n) • (1 : R) := by
  simp [kernel, integerBinomial, Algebra.smul_def]

private theorem kernel_add {R : Type*} [CommRing R] [Algebra ℂ R] (r s : ℤ) :
    kernel R (r + s) = kernel R r * kernel R s := by
  simp only [kernel, PowerSeries.binomialSeries_add, map_mul]

private theorem transform_coeff {R : Type*} [CommRing R] [Algebra ℂ R]
    (r : ℤ) (f : ℕ → R) (n : ℕ) :
    binomialTransform r f n =
      PowerSeries.coeff n (kernel R r * PowerSeries.mk f) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [binomialTransform, kernel_coeff, PowerSeries.coeff_mk,
    smul_mul_assoc, one_mul]

/-- Composition of the finite transforms, including negative upper indices.
It is the coefficientwise binomial-series group law. -/
private theorem binomialTransform_add {R : Type*} [CommRing R] [Algebra ℂ R]
    (r s : ℤ) (f : ℕ → R) (n : ℕ) :
    binomialTransform r (binomialTransform s f) n =
      binomialTransform (r + s) f n := by
  rw [transform_coeff, transform_coeff]
  have h : PowerSeries.mk (binomialTransform s f) = kernel R s * PowerSeries.mk f := by
    ext k
    simp only [PowerSeries.coeff_mk, ← transform_coeff]
  rw [h, kernel_add, mul_assoc]

private theorem transform_zero {R : Type*} [CommRing R] [Algebra ℂ R]
    (f : ℕ → R) (n : ℕ) : binomialTransform 0 f n = f n := by
  rw [transform_coeff]
  simp [kernel]

private theorem transform_clear {R : Type*} [CommRing R] [Algebra ℂ R]
    (F : ℤ → ℤ → R) (N B n : ℕ) (s : ℤ)
    (lower : ∀ a b : ℤ, b < -(B : ℤ) → F a b = 0) :
    binomialTransform (N : ℤ)
      (fun k => F (s - k + B) ((k : ℤ) - B)) n =
    clear N F (s + N - n + B) ((n : ℤ) - B) := by
  classical
  let term (k : ℕ) : R :=
    (((-1 : ℂ) ^ k) * (N.choose k : ℂ)) •
      F (s - n + B + k) ((n : ℤ) - B - k)
  have left : binomialTransform (N : ℤ)
      (fun k => F (s - k + B) ((k : ℤ) - B)) n =
      ∑ k ∈ Finset.range (n + 1), term k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := by simpa using Finset.mem_range.mp hk
    simp only [integerBinomial, Ring.choose_natCast, Int.cast_natCast, term]
    congr 2 <;> omega
  have right : clear N F (s + N - n + B) ((n : ℤ) - B) =
      ∑ k ∈ Finset.range (N + 1), term k := by
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only [term]
    congr 2 <;> omega
  rw [left, right]
  rcases le_total n N with h | h
  · apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ h))
    intro k hk hkn
    have low : (n : ℤ) - B - k < -(B : ℤ) := by
      simp only [Finset.mem_range, not_lt] at hkn
      omega
    simp [term, lower _ _ low]
  · symm
    apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ h))
    intro k hk hkN
    have hNk : N < k := by
      simp only [Finset.mem_range, not_lt] at hkN
      omega
    simp [term, Nat.choose_eq_zero_of_lt hNk]

/-- Finite reconstruction on a genuinely lower-supported ordered channel.
No cancellation is performed on unrestricted distributions. -/
theorem supported_reconstruction {R : Type*} [CommRing R] [Algebra ℂ R]
    (F : ℤ → ℤ → R) (N B : ℕ)
    (lower : ∀ a b : ℤ, b < -(B : ℤ) → F a b = 0)
    (a b : ℤ) (nonneg : 0 ≤ b + B) :
    F a b =
      ∑ j ∈ Finset.range ((b + B).toNat + 1),
        (((-1 : ℂ) ^ j) * integerBinomial (-(N : ℤ)) j) •
          clear N F (a + N + j) (b - j) := by
  let n := (b + B).toNat
  let s := a + b
  let f : ℕ → R := fun k => F (s - k + B) ((k : ℤ) - B)
  have hn : (n : ℤ) = b + B := Int.toNat_of_nonneg nonneg
  have inv := binomialTransform_add (-(N : ℤ)) (N : ℤ) f n
  rw [neg_add_cancel, transform_zero] at inv
  have hf : f n = F a b := by
    dsimp [f, s]
    congr 1 <;> omega
  rw [hf] at inv
  rw [← inv]
  change (∑ j ∈ Finset.range (n + 1),
    (((-1 : ℂ) ^ j) * integerBinomial (-(N : ℤ)) j) •
      binomialTransform (N : ℤ) f (n - j)) = _
  apply Finset.sum_congr rfl
  intro j hj
  dsimp only [f]
  have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
  rw [transform_clear F N B (n - j) s lower]
  congr 2 <;> omega




def collisionArguments (R : Type*) [CommRing R] :
    Fin 2 → MvPowerSeries (Fin 2) R :=
  ![MvPowerSeries.X 0 + MvPowerSeries.X 1, MvPowerSeries.X 1]

private theorem collision_hasSubst (R : Type*) [CommRing R] :
    MvPowerSeries.HasSubst (collisionArguments R) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro i
  fin_cases i <;> simp [collisionArguments]

/-- The native legal x=t+y, y=y substitution on infinite power series. -/
def collision {R : Type*} [CommRing R] (P : MvPowerSeries (Fin 2) R) :
    MvPowerSeries (Fin 2) R :=
  MvPowerSeries.subst (collisionArguments R) P

private theorem powerIndex_ext (d : Fin 2 →₀ ℕ) :
    d = powerIndex (d 0) (d 1) := by
  ext i
  fin_cases i <;> simp [powerIndex]

private theorem collision_monomial_coeff {R : Type*} [CommRing R]
    (d : Fin 2 →₀ ℕ) (a b : ℕ) :
    MvPowerSeries.coeff (powerIndex a b)
      (d.prod (fun i n => (collisionArguments R i) ^ n)) =
      if d 1 ≤ b ∧ d 0 = a + (b - d 1) then (d 0).choose a else 0 := by
  classical
  have prod_eq : d.prod (fun i n => (collisionArguments R i) ^ n) =
      (MvPowerSeries.X 0 + MvPowerSeries.X 1) ^ (d 0) *
        (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) ^ (d 1) := by
    rw [Finsupp.prod_of_support_subset d (Finset.subset_univ d.support)]
    · simp [Fin.prod_univ_two, collisionArguments]
    · intro i hi
      simp
  rw [prod_eq, MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_mul_monomial]
  have le_iff : Finsupp.single 1 (d 1) ≤ powerIndex a b ↔ d 1 ≤ b := by
    constructor
    · intro h
      simpa [powerIndex] using h 1
    · intro h i
      fin_cases i <;> simp [powerIndex, h]
  simp only [le_iff]
  by_cases h : d 1 ≤ b
  · rw [if_pos h, mul_one]
    have hp : (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) ^ (d 0) =
        (((MvPolynomial.X 0 + MvPolynomial.X 1 : MvPolynomial (Fin 2) R) ^ (d 0)) :
          MvPowerSeries (Fin 2) R) := by simp
    rw [hp, ← MvPolynomial.coe_pow, MvPolynomial.coeff_coe, MvPolynomial.coeff_add_pow]
    simp [powerIndex, Finsupp.tsub_apply, Finset.mem_antidiagonal, h, eq_comm]
  · simp [h]

/-- Each collision coefficient uses only its finite antidiagonal fiber.
The input series P need not have finite support. -/
theorem collision_coeff {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 2) R) (a b : ℕ) :
    MvPowerSeries.coeff (powerIndex a b) (collision P) =
      ∑ j ∈ Finset.range (b + 1),
        ((a + j).choose a : ℂ) • MvPowerSeries.coeff (powerIndex (a + j) (b - j)) P := by
  classical
  have legal := collision_hasSubst R
  rw [collision, MvPowerSeries.coeff_subst legal]
  let indices := (Finset.range (b + 1)).image (fun j => powerIndex (a + j) (b - j))
  rw [finsum_eq_sum_of_support_subset (s := indices)]
  · rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro j hj
      have hjb : j ≤ b := by simpa using Finset.mem_range.mp hj
      rw [collision_monomial_coeff]
      have cc : (powerIndex (a + j) (b - j)) 1 ≤ b ∧
          (powerIndex (a + j) (b - j)) 0 =
            a + (b - (powerIndex (a + j) (b - j)) 1) := by
        simp only [powerIndex_zero, powerIndex_one]
        constructor <;> omega
      rw [ite_eq_left cc]
      simp only [powerIndex_zero, Algebra.smul_def, smul_eq_mul, map_natCast, Algebra.algebraMap_self_apply, mul_comm]
    · intro i hi j hj h
      have h0 := congrArg (fun d : Fin 2 →₀ ℕ => d 0) h
      simp only [powerIndex, Finsupp.add_apply, Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), add_zero] at h0
      omega
  · intro d hd
    rw [Function.mem_support, ne_eq] at hd
    have conditions : d 1 ≤ b ∧ d 0 = a + (b - d 1) := by
      by_contra h
      apply hd
      rw [collision_monomial_coeff]
      simp only [h, ite_false, Nat.cast_zero, smul_zero]
    apply Finset.mem_image.mpr
    refine ⟨b - d 1, Finset.mem_range.mpr (by omega), ?_⟩
    ext i
    fin_cases i
    · simpa [powerIndex] using conditions.2.symm
    · simpa [powerIndex] using Nat.sub_sub_self conditions.1


private theorem kernel_negative {R : Type*} [CommRing R] [Algebra ℂ R] (a : ℕ) :
    kernel R (-(a : ℤ) - 1) = (PowerSeries.invOneSubPow R (a + 1)).val := by
  have h := congrArg (PowerSeries.rescale (-1 : R))
    (PowerSeries.rescale_neg_one_invOneSubPow (A := R) (a + 1))
  have cancel :
      PowerSeries.rescale (-1 : R)
        (PowerSeries.rescale (-1 : R) (PowerSeries.invOneSubPow R (a + 1)).val) =
      (PowerSeries.invOneSubPow R (a + 1)).val := by
    ext n
    simp only [PowerSeries.coeff_rescale]
    rw [← mul_assoc, ← mul_pow]
    norm_num
  rw [cancel] at h
  simpa only [kernel, Nat.cast_add, Nat.cast_one, neg_add_rev,
    sub_eq_add_neg, add_comm] using h.symm

private theorem negative_weight (a j : ℕ) :
    ((-1 : ℂ) ^ j) * integerBinomial (-(a : ℤ) - 1) j =
      ((a + j).choose a : ℂ) := by
  have h := congrArg (PowerSeries.coeff j) (kernel_negative (R := ℂ) a)
  rw [kernel_coeff, PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose,
    PowerSeries.coeff_mk] at h
  simpa only [smul_eq_mul, mul_one] using h

/-- The finite collision fiber of a common cleared numerator is precisely the
signed integer-binomial transform appearing in the original Borcherds law. -/
theorem cleared_collision_coeff {R : Type*} [CommRing R] [Algebra ℂ R]
    (F : ℤ → ℤ → R) (N A B : ℕ)
    (lower : ∀ x y : ℤ, y < -(B : ℤ) → F x y = 0)
    (P : MvPowerSeries (Fin 2) R)
    (common : ∀ x y : ℤ, clear N F (x - A) (y - B) = extend P x y)
    (a b : ℕ) :
    (∑ i ∈ Finset.range (b + 1),
      (((-1 : ℂ) ^ i) * integerBinomial ((N : ℤ) - a - 1) i) •
        F ((a : ℤ) - A - N + i) ((b : ℤ) - B - i)) =
      MvPowerSeries.coeff (powerIndex a b) (collision P) := by
  let s : ℤ := a + b - A - B - N
  let f : ℕ → R := fun k => F (s - k + B) ((k : ℤ) - B)
  have compose := binomialTransform_add (-(a : ℤ) - 1) (N : ℤ) f b
  rw [show -(a : ℤ) - 1 + N = (N : ℤ) - a - 1 by omega] at compose
  have first :
      (∑ i ∈ Finset.range (b + 1),
        (((-1 : ℂ) ^ i) * integerBinomial ((N : ℤ) - a - 1) i) •
          F ((a : ℤ) - A - N + i) ((b : ℤ) - B - i)) =
      binomialTransform ((N : ℤ) - a - 1) f b := by
    apply Finset.sum_congr rfl
    intro i hi
    have hib : i ≤ b := by simpa using Finset.mem_range.mp hi
    dsimp only [f, s]
    congr 2 <;> omega
  rw [first, ← compose, collision_coeff]
  change (∑ j ∈ Finset.range (b + 1),
    (((-1 : ℂ) ^ j) * integerBinomial (-(a : ℤ) - 1) j) •
      binomialTransform (N : ℤ) f (b - j)) = _
  apply Finset.sum_congr rfl
  intro j hj
  have hjb : j ≤ b := by simpa using Finset.mem_range.mp hj
  rw [negative_weight]
  dsimp only [f]
  rw [transform_clear F N B (b - j) s lower]
  have hx : s + N - (b - j : ℕ) + B = ((a + j : ℕ) : ℤ) - A := by
    dsimp only [s]
    omega
  rw [hx, common]
  simp only [extend, Nat.cast_nonneg, and_self, ite_true, Int.toNat_natCast]

/-- Coefficientwise linear readout, requiring no multiplicative map on states. -/
def mapSeries {R S : Type*} [CommRing R] [Algebra ℂ R]
    [CommRing S] [Algebra ℂ S] (f : R →ₗ[ℂ] S)
    (P : MvPowerSeries (Fin 2) R) : MvPowerSeries (Fin 2) S :=
  fun d => f (MvPowerSeries.coeff d P)

/-- Legal collision transport commutes with arbitrary complex-linear readouts. -/
theorem collision_map {R S : Type*} [CommRing R] [Algebra ℂ R]
    [CommRing S] [Algebra ℂ S] (f : R →ₗ[ℂ] S)
    (P : MvPowerSeries (Fin 2) R) :
    collision (mapSeries f P) = mapSeries f (collision P) := by
  funext d
  change MvPowerSeries.coeff d (collision (mapSeries f P)) =
    f (MvPowerSeries.coeff d (collision P))
  rw [powerIndex_ext d, collision_coeff, collision_coeff]
  simp only [mapSeries, MvPowerSeries.coeff_apply, map_sum, map_smul]

private def positiveTransform {R : Type*} [CommRing R] [Algebra ℂ R]
    (r : ℤ) (f : ℕ → R) (n : ℕ) : R :=
  ∑ j ∈ Finset.range (n + 1), integerBinomial r j • f (n - j)

private theorem positive_coeff {R : Type*} [CommRing R] [Algebra ℂ R]
    (r : ℤ) (f : ℕ → R) (n : ℕ) :
    positiveTransform r f n =
      PowerSeries.coeff n (PowerSeries.binomialSeries R r * PowerSeries.mk f) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [positiveTransform, PowerSeries.binomialSeries_coeff, PowerSeries.coeff_mk,
    integerBinomial, smul_mul_assoc, one_mul, Int.cast_smul_eq_zsmul]

private theorem positive_inverse {R : Type*} [CommRing R] [Algebra ℂ R]
    (A : ℕ) (f : ℕ → R) (n : ℕ) :
    positiveTransform (-(A : ℤ)) (positiveTransform (A : ℤ) f) n = f n := by
  rw [positive_coeff]
  have h : PowerSeries.mk (positiveTransform (A : ℤ) f) =
      PowerSeries.binomialSeries R (A : ℤ) * PowerSeries.mk f := by
    ext k
    simp only [PowerSeries.coeff_mk, ← positive_coeff]
  rw [h, ← mul_assoc, ← PowerSeries.binomialSeries_add, neg_add_cancel]
  simp

/-- Multiplication by (y+t)^A, in t-first coordinates after removing y^A. -/
def positiveClear {R : Type*} [CommRing R] [Algebra ℂ R]
    (A : ℕ) (I : ℤ → ℤ → R) (a b : ℤ) : R :=
  ∑ h ∈ Finset.range (A + 1), (A.choose h : ℂ) • I (a - h) (b + h)

private theorem positive_transform_clear {R : Type*} [CommRing R] [Algebra ℂ R]
    (I : ℤ → ℤ → R) (A N n : ℕ) (s : ℤ)
    (lower : ∀ a b : ℤ, a < -(N : ℤ) → I a b = 0) :
    positiveTransform (A : ℤ) (fun k => I ((k : ℤ) - N) (s - k + N)) n =
      positiveClear A I ((n : ℤ) - N) (s - n + N) := by
  classical
  let term (j : ℕ) : R := (A.choose j : ℂ) •
    I ((n : ℤ) - N - j) (s - n + N + j)
  have left : positiveTransform (A : ℤ)
      (fun k => I ((k : ℤ) - N) (s - k + N)) n =
      ∑ j ∈ Finset.range (n + 1), term j := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
    simp only [integerBinomial, Ring.choose_natCast, Int.cast_natCast, term]
    congr 2 <;> omega
  have right : positiveClear A I ((n : ℤ) - N) (s - n + N) =
      ∑ j ∈ Finset.range (A + 1), term j := rfl
  rw [left, right]
  rcases le_total n A with h | h
  · apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ h))
    intro j hj hjn
    have low : (n : ℤ) - N - j < -(N : ℤ) := by
      simp only [Finset.mem_range, not_lt] at hjn
      omega
    simp [term, lower _ _ low]
  · symm
    apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ h))
    intro j hj hjA
    have hAj : A < j := by simp only [Finset.mem_range, not_lt] at hjA; omega
    simp [term, Nat.choose_eq_zero_of_lt hAj]

/-- Finite inverse expansion in the t-small chamber for the positive factor
(y+t)^A. The t lower bound is necessary, and the signed upper index stays -A. -/
theorem supported_positive_reconstruction {R : Type*} [CommRing R] [Algebra ℂ R]
    (I : ℤ → ℤ → R) (A N : ℕ)
    (lower : ∀ a b : ℤ, a < -(N : ℤ) → I a b = 0)
    (a b : ℤ) (nonneg : 0 ≤ a + N) :
    I a b = ∑ j ∈ Finset.range ((a + N).toNat + 1),
      integerBinomial (-(A : ℤ)) j • positiveClear A I (a - j) (b + j) := by
  let n := (a + N).toNat
  let s := a + b
  let f : ℕ → R := fun k => I ((k : ℤ) - N) (s - k + N)
  have hn : (n : ℤ) = a + N := Int.toNat_of_nonneg nonneg
  have inv := positive_inverse A f n
  have hf : f n = I a b := by dsimp only [f, s]; congr 1 <;> omega
  rw [hf] at inv
  rw [← inv]
  change (∑ j ∈ Finset.range (n + 1), integerBinomial (-(A : ℤ)) j •
    positiveTransform (A : ℤ) f (n - j)) = _
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
  dsimp only [f]
  rw [positive_transform_clear I A N (n - j) s lower]
  dsimp only [s]
  congr 2 <;> omega

end
end D5.S3.VertexAlgebra.SupportedChannelSeries
