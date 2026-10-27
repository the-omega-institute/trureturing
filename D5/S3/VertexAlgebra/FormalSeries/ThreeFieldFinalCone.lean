/- GID: D5/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalCone
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/FormalSeries/ThreeFieldFinalCone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact signed final cone, native coefficient chart, and old Laurent fiber transport. -/
import D5.S3.VertexAlgebra.FormalSeries.ThreeFieldFinalLaurentFiber
import Mathlib.RingTheory.MvPowerSeries.Inverse

/-!
This chart acts on native series and on proved coefficient indices only.
The shifted raw cone is all of N^3; the distinct native input chart is sorted.
The explicit old Laurent expression is preserved. Neither its identification
with a native unit inverse nor its full polynomial action is asserted here.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.VertexAlgebra.ThreeFieldFinalCone
open UniformGradedLocalCorrelator UngradedLocalWordSeries SupportedThreeFieldCollision
open ThreeFieldFinalLaurentFiber
open scoped BigOperators
noncomputable section

/-- Signed raw cone; no individual-coordinate positivity is imposed. -/
def FinalCone (k : ℕ) (a : Fin 3 → ℕ) (e : Exponent 3) : Prop :=
  0 ≤ e 0 + k ∧ 0 ≤ e 0 + e 1 + 3 * k ∧
    0 ≤ e 0 + e 1 + e 2 + 3 * k + a 0 + a 1 + a 2

/-- The inverse chart is defined on EVERY native index, without sortedness. -/
def decode (k : ℕ) (a : Fin 3 → ℕ) (n : Fin 3 → ℕ) : Exponent 3 :=
  ![(n 0 : ℤ) - k, (n 1 : ℤ) - n 0 - 2 * k,
    (n 2 : ℤ) - n 1 - a 0 - a 1 - a 2]

private theorem decode_mem (k : ℕ) (a : Fin 3 → ℕ) (n : Fin 3 → ℕ) :
    FinalCone k a (decode k a n) := by
  simp only [FinalCone, decode, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  omega

/-- All three toNat operations occur AFTER restriction to the signed cone. -/
def coneEquiv (k : ℕ) (a : Fin 3 → ℕ) :
    {e : Exponent 3 // FinalCone k a e} ≃ (Fin 3 → ℕ) where
  toFun e := ![(e.1 0 + k).toNat, (e.1 0 + e.1 1 + 3 * k).toNat,
    (e.1 0 + e.1 1 + e.1 2 + 3 * k + a 0 + a 1 + a 2).toNat]
  invFun n := ⟨decode k a n, decode_mem k a n⟩
  left_inv e := by
    apply Subtype.ext
    funext i
    have h0 := e.2.1
    have h1 := e.2.2.1
    have h2 := e.2.2.2
    fin_cases i <;> dsimp [decode] <;>
      simp only [Int.toNat_of_nonneg h0, Int.toNat_of_nonneg h1,
        Int.toNat_of_nonneg h2] <;> omega
  right_inv n := by
    funext i
    fin_cases i
    · change ((decode k a n) 0 + k).toNat = n 0
      dsimp [decode]
      omega
    · change ((decode k a n) 0 + (decode k a n) 1 + 3 * k).toNat = n 1
      dsimp [decode]
      omega
    · change ((decode k a n) 0 + (decode k a n) 1 + (decode k a n) 2 +
        3 * k + a 0 + a 1 + a 2).toNat = n 2
      dsimp [decode]
      omega

/-- This outside branch is proved in signed arithmetic, before any toNat. -/
theorem old_zero_outside {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (k : ℕ) (a : Fin 3 → ℕ)
    (e : Exponent 3) (he : ¬ FinalCone k a e) :
    laurentCoefficient P k a e = 0 := by
  apply laurentCoefficient_zero
  by_contra hn
  push_neg at hn
  apply he
  dsimp only [FinalCone]
  omega

/-- Q is the native-input chart. Its sorted cone is unrelated to the domain
of coneEquiv. No monomial substitution API or raw substitution is used. -/
def nativeChart {R : Type*} [CommRing R] (P : MvPowerSeries (Fin 3) R) :
    MvPowerSeries (Fin 3) R :=
  fun d => if d 0 ≤ d 1 ∧ d 1 ≤ d 2 then
    MvPowerSeries.coeff (index3 (d 0) (d 1 - d 0) (d 2 - d 1)) P else 0

private theorem nativeChart_coeff {R : Type*} [CommRing R]
    (P : MvPowerSeries (Fin 3) R) (r s t : ℕ) :
    MvPowerSeries.coeff (index3 r s t) (nativeChart P) =
      if r ≤ s ∧ s ≤ t then
        MvPowerSeries.coeff (index3 r (s - r) (t - s)) P else 0 := by
  simp [MvPowerSeries.coeff_apply, nativeChart, index3]

private theorem signed_nonnegative {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (e : Exponent 3)
    (he : ∀ i, 0 ≤ e i) :
    signedExtend P e = MvPowerSeries.coeff
      (index3 (e 0).toNat (e 1).toNat (e 2).toNat) P := by
  rw [signedExtend, if_pos he]
  apply congrArg (fun d : Fin 3 →₀ ℕ => MvPowerSeries.coeff d P)
  ext i
  fin_cases i <;> simp [signedIndex, index3]

/-- A term of the OLD finite fiber is exactly a shifted native Q coefficient.
Both finite bounds come from the old admissibility equations, not a cutoff. -/
private theorem old_input_chart {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (k : ℕ) (a : Fin 3 → ℕ)
    (e : {e : Exponent 3 // FinalCone k a e}) (i : LaurentIndex)
    (hi : i ∈ laurentFiber k a e.1) :
    signedExtend P (laurentInput k a e.1 i) =
      MvPowerSeries.coeff
        (index3 ((coneEquiv k a e) 0 - i.1.1 - i.2.1)
          ((coneEquiv k a e) 1 - i.1.2 - i.2.2)
          ((coneEquiv k a e) 2)) (nativeChart P) := by
  have ha := (mem_laurentFiber_iff k a e.1 i).mp hi
  have h0 := ha.2 0
  have h1 := ha.2 1
  have h2 := ha.2 2
  have hc0 := e.2.1
  have hc1 := e.2.2.1
  have hc2 := e.2.2.2
  let n := coneEquiv k a e
  change signedExtend P (laurentInput k a e.1 i) =
    MvPowerSeries.coeff
      (index3 (n 0 - i.1.1 - i.2.1) (n 1 - i.1.2 - i.2.2) (n 2)) (nativeChart P)
  have n0 : (n 0 : ℤ) = e.1 0 + k := Int.toNat_of_nonneg hc0
  have n1 : (n 1 : ℤ) = e.1 0 + e.1 1 + 3 * k := Int.toNat_of_nonneg hc1
  have n2 : (n 2 : ℤ) =
      e.1 0 + e.1 1 + e.1 2 + 3 * k + a 0 + a 1 + a 2 :=
    Int.toNat_of_nonneg hc2
  simp only [laurentInput, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  have hs : n 0 - i.1.1 - i.2.1 ≤ n 1 - i.1.2 - i.2.2 ∧
      n 1 - i.1.2 - i.2.2 ≤ n 2 := by omega
  rw [signed_nonnegative P _ ha.2, nativeChart_coeff, if_pos hs]
  apply congrArg (fun d : Fin 3 →₀ ℕ => MvPowerSeries.coeff d P)
  congr 1
  · change (e.1 0 + k - i.1.1 - i.2.1).toNat = n 0 - i.1.1 - i.2.1
    omega
  · change (e.1 1 + 2 * k + i.1.1 - i.1.2 + i.2.1 - i.2.2).toNat =
      (n 1 - i.1.2 - i.2.2) - (n 0 - i.1.1 - i.2.1)
    omega
  · change (e.1 2 + a 0 + a 1 + a 2 + i.1.2 + i.2.2).toNat =
      n 2 - (n 1 - i.1.2 - i.2.2)
    omega

/-- Exact transport of the EXISTING expression, including its original fiber
and scalar. This does not identify the sum with coeff(U^-1 Q). -/
private theorem old_coefficient_on_cone {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (k : ℕ) (a : Fin 3 → ℕ)
    (e : {e : Exponent 3 // FinalCone k a e}) :
    laurentCoefficient P k a e.1 =
      ∑ i ∈ laurentFiber k a e.1, laurentWeight k a i •
        MvPowerSeries.coeff
          (index3 ((coneEquiv k a e) 0 - i.1.1 - i.2.1)
            ((coneEquiv k a e) 1 - i.1.2 - i.2.2)
            ((coneEquiv k a e) 2)) (nativeChart P) := by
  rw [laurentCoefficient_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [old_input_chart P k a e i hi]

/-- Every native index, sorted or unsorted, has its exact signed raw target.
The inverse law of coneEquiv is used to obtain this formula. -/
theorem old_coefficient_chart_sum {R : Type*} [CommRing R] [Algebra ℂ R]
    (P : MvPowerSeries (Fin 3) R) (k : ℕ) (a : Fin 3 → ℕ) (n : Fin 3 → ℕ) :
    laurentCoefficient P k a (decode k a n) =
      ∑ i ∈ laurentFiber k a (decode k a n), laurentWeight k a i •
        MvPowerSeries.coeff
          (index3 (n 0 - i.1.1 - i.2.1) (n 1 - i.1.2 - i.2.2) (n 2))
          (nativeChart P) := by
  have h := old_coefficient_on_cone P k a ((coneEquiv k a).symm n)
  have hd : ((coneEquiv k a).symm n).val = decode k a n := rfl
  simpa only [Equiv.apply_symm_apply, hd] using h

/-- Polynomial chart algebra is performed in an ordinary native ring only.
This is not a substitution on a raw coefficient distribution. -/
theorem native_chart_factorization {T : Type*} [CommRing T]
    (X Y Z : T) (k A C D : ℕ) :
    (X * Y * Z) ^ k * (Y * Z) ^ k * (X * Y * Z + Y * Z) ^ k *
      (X * Y * Z + Y * Z + Z) ^ A * (Y * Z + Z) ^ C * Z ^ D =
        X ^ k * Y ^ (3 * k) * Z ^ (3 * k + A + C + D) *
          ((1 + X) ^ k * (1 + Y + X * Y) ^ A * (1 + Y) ^ C) := by
  have hxy : X * Y * Z + Y * Z = (1 + X) * Y * Z := by ring
  have ht : X * Y * Z + Y * Z + Z = (1 + Y + X * Y) * Z := by ring
  have hyz : Y * Z + Z = (1 + Y) * Z := by ring
  rw [ht, hxy, hyz, show 3 * k = k + k + k by omega]
  simp only [mul_pow, pow_add]
  ring

/-- The precise native unit in the final chart. -/
def chartUnitSeries (R : Type*) [CommRing R] (k : ℕ) (a : Fin 3 → ℕ) :
    MvPowerSeries (Fin 3) R :=
  (1 + MvPowerSeries.X 0) ^ k *
    (1 + MvPowerSeries.X 1 + MvPowerSeries.X 0 * MvPowerSeries.X 1) ^ a 0 *
      (1 + MvPowerSeries.X 1) ^ a 1

private theorem chart_constant (R : Type*) [CommRing R] (k : ℕ) (a : Fin 3 → ℕ) :
    MvPowerSeries.constantCoeff (chartUnitSeries R k a) = 1 := by
  simp [chartUnitSeries]

/-- The inverse uses the pinned invOfUnit API, valid over a general CommRing. -/
def chartUnit (R : Type*) [CommRing R] (k : ℕ) (a : Fin 3 → ℕ) :
    (MvPowerSeries (Fin 3) R)ˣ where
  val := chartUnitSeries R k a
  inv := MvPowerSeries.invOfUnit (chartUnitSeries R k a) 1
  val_inv := MvPowerSeries.mul_invOfUnit _ 1 (by simpa using chart_constant R k a)
  inv_val := MvPowerSeries.invOfUnit_mul _ 1 (by simpa using chart_constant R k a)

/-- A genuine native inverse equation. Its coefficient formula remains a
separate obligation; F is not installed as a replacement raw distribution. -/
theorem native_unit_equation {R : Type*} [CommRing R]
    (P : MvPowerSeries (Fin 3) R) (k : ℕ) (a : Fin 3 → ℕ) :
    chartUnitSeries R k a *
      ((↑((chartUnit R k a)⁻¹) : MvPowerSeries (Fin 3) R) * nativeChart P) =
        nativeChart P := by
  change (↑(chartUnit R k a) : MvPowerSeries (Fin 3) R) *
    ((↑((chartUnit R k a)⁻¹) : MvPowerSeries (Fin 3) R) * nativeChart P) = _
  have cancel : (↑(chartUnit R k a) : MvPowerSeries (Fin 3) R) *
      (↑((chartUnit R k a)⁻¹) : MvPowerSeries (Fin 3) R) = 1 :=
    (chartUnit R k a).val_inv
  rw [← mul_assoc, cancel, one_mul]

end
end D5.S3.VertexAlgebra.ThreeFieldFinalCone
