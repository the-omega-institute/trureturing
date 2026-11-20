/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reflection/PeriodicMPSUniformChirality
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reflection/PeriodicMPSUniformChirality
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformAntisymmetricTransfer]
   utility: none
   digest: A uniform nonzero chirality witness. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSUniformAntisymmetricTransfer
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# A rational certificate for periodic MPS chirality

The certificate uses the trace window of the transfer powers. Its finite data
come from `periodic-mps-uniform-chirality-rational-box.py`. All closed arithmetic
checks reduce in the kernel.
-/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformChirality

open scoped Matrix Kronecker
open Matrix

section Arithmetic

private structure Interval where
  lo : ℚ
  hi : ℚ

private def Interval.Contains (I : Interval) (x : ℚ) : Prop := I.lo ≤ x ∧ x ≤ I.hi

private def Interval.point (x : ℚ) : Interval := ⟨x, x⟩

private def Interval.add (a b : Interval) : Interval := ⟨a.lo + b.lo, a.hi + b.hi⟩

private def Interval.neg (a : Interval) : Interval := ⟨-a.hi, -a.lo⟩

private def Interval.mul (a b : Interval) : Interval :=
  ⟨min (min (a.lo * b.lo) (a.lo * b.hi)) (min (a.hi * b.lo) (a.hi * b.hi)),
   max (max (a.lo * b.lo) (a.lo * b.hi)) (max (a.hi * b.lo) (a.hi * b.hi))⟩

local instance : Add Interval := ⟨Interval.add⟩
local instance : Neg Interval := ⟨Interval.neg⟩
local instance : Mul Interval := ⟨Interval.mul⟩

private theorem Interval.contains_add {a b : Interval} {x y : ℚ}
    (hx : a.Contains x) (hy : b.Contains y) : (a + b).Contains (x + y) :=
  ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

private theorem Interval.contains_neg {a : Interval} {x : ℚ}
    (hx : a.Contains x) : (-a).Contains (-x) :=
  ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩

private theorem Interval.contains_mul {a b : Interval} {x y : ℚ}
    (hx : a.Contains x) (hy : b.Contains y) : (a * b).Contains (x * y) := by
  have bound (c : ℚ) : min (c * b.lo) (c * b.hi) ≤ c * y ∧
      c * y ≤ max (c * b.lo) (c * b.hi) := by
    rcases le_total 0 c with hc | hc
    · exact ⟨(min_le_left ..).trans (mul_le_mul_of_nonneg_left hy.1 hc),
        (mul_le_mul_of_nonneg_left hy.2 hc).trans (le_max_right ..)⟩
    · exact ⟨(min_le_right ..).trans (mul_le_mul_of_nonpos_left hy.2 hc),
        (mul_le_mul_of_nonpos_left hy.1 hc).trans (le_max_left ..)⟩
  rcases le_total 0 y with h | h
  · exact ⟨(min_le_left ..).trans ((bound a.lo).1.trans
        (mul_le_mul_of_nonneg_right hx.1 h)),
      (mul_le_mul_of_nonneg_right hx.2 h).trans ((bound a.hi).2.trans (le_max_right ..))⟩
  · exact ⟨(min_le_right ..).trans ((bound a.hi).1.trans
        (mul_le_mul_of_nonpos_right hx.2 h)),
      (mul_le_mul_of_nonpos_right hx.1 h).trans ((bound a.lo).2.trans (le_max_left ..))⟩

private def dot3 {α : Type*} [Add α] [Mul α] (x y : Fin 3 → α) : α :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2

private def dot4 {α : Type*} [Add α] [Mul α] (x y : Fin 4 → α) : α :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3

private theorem Interval.contains_dot3 {a b : Fin 3 → Interval} {x y : Fin 3 → ℚ}
    (hx : ∀ i, (a i).Contains (x i)) (hy : ∀ i, (b i).Contains (y i)) :
    (dot3 a b).Contains (dot3 x y) :=
  contains_add (contains_add (contains_mul (hx 0) (hy 0)) (contains_mul (hx 1) (hy 1)))
    (contains_mul (hx 2) (hy 2))

private theorem Interval.contains_dot4 {a b : Fin 4 → Interval} {x y : Fin 4 → ℚ}
    (hx : ∀ i, (a i).Contains (x i)) (hy : ∀ i, (b i).Contains (y i)) :
    (dot4 a b).Contains (dot4 x y) :=
  contains_add
    (contains_add (contains_add (contains_mul (hx 0) (hy 0)) (contains_mul (hx 1) (hy 1)))
      (contains_mul (hx 2) (hy 2)))
    (contains_mul (hx 3) (hy 3))

/-- The determinant with columns `r`, `C r`, and `C² r`. -/
def krylovDet {α : Type*} [Add α] [Neg α] [Mul α]
    (r : Fin 3 → α) (C : Fin 3 → Fin 3 → α) : α :=
  let u := fun i => dot3 (C i) r
  let v := fun i => dot3 (C i) u
  r 0 * u 1 * v 2 + r 1 * u 2 * v 0 + r 2 * u 0 * v 1 +
    -(r 0 * u 2 * v 1) + -(r 1 * u 0 * v 2) + -(r 2 * u 1 * v 0)

private theorem krylovDet_eq_det {R : Type*} [CommRing R]
    (r : Fin 3 → R) (C : Matrix (Fin 3) (Fin 3) R) :
    krylovDet r C =
      (Matrix.of fun i => ![r i, (C *ᵥ r) i, (C ^ 2 *ᵥ r) i]).det := by
  rw [pow_two, ← mulVec_mulVec]
  simp [krylovDet, dot3, Matrix.det_fin_three, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

private theorem Interval.contains_krylovDet {R : Fin 3 → Interval}
    {M : Fin 3 → Fin 3 → Interval} {r : Fin 3 → ℚ} {C : Fin 3 → Fin 3 → ℚ}
    (hr : ∀ i, (R i).Contains (r i)) (hC : ∀ i j, (M i j).Contains (C i j)) :
    (krylovDet R M).Contains (krylovDet r C) := by
  have hu i := contains_dot3 (hC i) hr
  have hv i := contains_dot3 (hC i) hu
  have h i j k := contains_mul (contains_mul (hr i) (hu j)) (hv k)
  exact contains_add (contains_add (contains_add
    (contains_add (contains_add (h 0 1 2) (h 1 2 0)) (h 2 0 1))
      (contains_neg (h 0 2 1))) (contains_neg (h 1 0 2))) (contains_neg (h 2 1 0))

private def companion : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1; -154, 158, -65, 14]

private def companion8 : Matrix (Fin 4) (Fin 4) ℚ :=
  !![-1338414, 1206550, -414133, 69886;
     -10762444, 9703574, -3336040, 564271;
     -86897734, 78392374, -26974041, 4563754;
     -702818116, 634175398, -218251636, 36918515]

private theorem companion_pow_eight : companion ^ 8 = companion8 := by
  let c2 : Matrix (Fin 4) (Fin 4) ℚ :=
    !![0, 0, 1, 0; 0, 0, 0, 1; -154, 158, -65, 14; -2156, 2058, -752, 131]
  let c4 : Matrix (Fin 4) (Fin 4) ℚ :=
    !![-154, 158, -65, 14; -2156, 2058, -752, 131;
       -20174, 18542, -6457, 1082; -166628, 150782, -51788, 8691]
  have square : companion ^ 2 = c2 := by
    funext i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  have fourth : c2 ^ 2 = c4 := by
    funext i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  have eighth : c4 ^ 2 = companion8 := by
    funext i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  rw [show (8 : ℕ) = (2 * 2) * 2 by decide, pow_mul, pow_mul, square, fourth, eighth]

private abbrev IntWindow := ℤ × ℤ × ℤ × ℤ

private def traceWindow : ℕ → IntWindow
  | 0 => (4, 14, 66, 488)
  | k + 1 => match traceWindow k with
    | (a, b, c, d) => (b, c, d, -154 * a + 158 * b - 65 * c + 14 * d)

/-- The four trace moments starting at a given transfer exponent. -/
def window (k : ℕ) : Fin 4 → ℚ :=
  match traceWindow k with
  | (a, b, c, d) => ![a, b, c, d]

private theorem window_succ (k : ℕ) : window (k + 1) = companion *ᵥ window k := by
  simp only [window, traceWindow]
  generalize traceWindow k = w
  rcases w with ⟨a, b, c, d⟩
  funext i
  fin_cases i <;>
    simp [companion, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Int.cast_add,
      Int.cast_mul, Int.cast_neg, sub_eq_add_neg]

private theorem window_add (k j : ℕ) : window (k + j) = companion ^ j *ᵥ window k := by
  induction j with
  | zero => simp
  | succ j ih => rw [← Nat.add_assoc, window_succ, ih, mulVec_mulVec, pow_succ']

private def projectivize (x : Fin 4 → ℚ) : Fin 4 → ℚ := fun j => x j / x 0

private def box : Fin 4 → Interval := fun j =>
  if j = 0 then Interval.point 1
  else
    let center := projectivize (window 30) j
    ⟨center - 1 / 100000000, center + 1 / 100000000⟩

private def InBox (x : Fin 4 → ℚ) : Prop :=
  0 < x 0 ∧ ∀ j, (box j).Contains (projectivize x j)

private def enclose (row : Fin 4 → ℚ) : Interval :=
  dot4 (fun j => Interval.point (row j)) box

private theorem enclose_contains {x : Fin 4 → ℚ}
    (hx : ∀ j, (box j).Contains (x j)) (row : Fin 4 → ℚ) :
    (enclose row).Contains (dot4 row x) :=
  Interval.contains_dot4 (fun _ => ⟨le_rfl, le_rfl⟩) hx

private theorem dot4_eq_mulVec_apply (A : Matrix (Fin 4) (Fin 4) ℚ) (x : Fin 4 → ℚ)
    (j : Fin 4) : (A *ᵥ x) j = dot4 (A j) x := by
  simp [mulVec, dotProduct, Fin.sum_univ_four, dot4]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem invariance_bounds :
    0 < (enclose (companion8 0)).lo ∧
    (∀ j : Fin 4, 0 ≤ (enclose (fun i => companion8 j i - (box j).lo * companion8 0 i)).lo) ∧
    (∀ j : Fin 4, 0 ≤ (enclose (fun i => (box j).hi * companion8 0 i - companion8 j i)).lo) := by
  decide +kernel

private theorem inBox_step {x : Fin 4 → ℚ} (hx : InBox x) :
    InBox (companion8 *ᵥ x) := by
  let y := companion8 *ᵥ x
  let z := projectivize x
  have hz (j : Fin 4) : dot4 (companion8 j) z = y j / x 0 := by
    change _ = (companion8 *ᵥ x) j / x 0
    rw [dot4_eq_mulVec_apply]
    dsimp [dot4, z, projectivize]
    ring
  have hp := invariance_bounds.1.trans_le (enclose_contains hx.2 (companion8 0)).1
  rw [hz] at hp
  have hy : 0 < y 0 := (div_pos_iff_of_pos_right hx.1).mp hp
  refine ⟨hy, fun j => ⟨(le_div_iff₀ hy).mpr ?_, (div_le_iff₀ hy).mpr ?_⟩⟩
  · have h := (invariance_bounds.2.1 j).trans
      (enclose_contains hx.2 (fun i => companion8 j i - (box j).lo * companion8 0 i)).1
    have hdot :
        dot4 (fun i => companion8 j i - (box j).lo * companion8 0 i) z =
          dot4 (companion8 j) z - (box j).lo * dot4 (companion8 0) z := by
      unfold dot4
      ring
    rw [hdot, hz, hz, ← mul_div_assoc, ← sub_div] at h
    exact sub_nonneg.mp (by simpa using (le_div_iff₀ hx.1).mp h)
  · have h := (invariance_bounds.2.2 j).trans
      (enclose_contains hx.2 (fun i => (box j).hi * companion8 0 i - companion8 j i)).1
    have hdot :
        dot4 (fun i => (box j).hi * companion8 0 i - companion8 j i) z =
          (box j).hi * dot4 (companion8 0) z - dot4 (companion8 j) z := by
      unfold dot4
      ring
    rw [hdot, hz, hz, ← mul_div_assoc, ← sub_div] at h
    exact sub_nonneg.mp (by simpa using (le_div_iff₀ hx.1).mp h)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem box_seeds : ∀ j : Fin 8, InBox (window (30 + j.val)) := by
  unfold InBox Interval.Contains
  decide +kernel

private theorem window_inBox (k : ℕ) (hk : 30 ≤ k) : InBox (window k) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases h : k < 38
    · simpa only [show 30 + (k - 30) = k by omega] using box_seeds ⟨k - 30, by omega⟩
    · have hs : k - 8 + 8 = k := by omega
      have hb := inBox_step (ih (k - 8) (by omega) (by omega))
      rwa [← companion_pow_eight, ← window_add, hs] at hb

private def numeratorRows : Fin 12 → Fin 4 → ℚ :=
  ![![-15738030, 8185329, -2178207, 477099],
    ![-3469620, -1017096, 4873938, -385314],
    ![-39373180, 34059937, -9629377, 768073],
    ![-3945128, 4719122, -1800107, 416726],
    ![-5496700, -1453568, 1516994, 1726],
    ![-7294584, 8165883, -1289739, 72039],
    ![-5496700, -1453568, 1516994, 1726],
    ![-14326378, 5522830, 4848179, -540530],
    ![-41955408, 40459212, -12231936, 981666],
    ![-7294584, 8165883, -1289739, 72039],
    ![-41955408, 40459212, -12231936, 981666],
    ![20460770, -11487806, 191279, 99946]]

private def readoutRow (j : Fin 12) : Fin 4 → ℚ :=
  fun i => numeratorRows j i / 2931357

/-- Index of a one-site Pauli readout in the certificate. -/
def rIndex (i : Fin 3) : Fin 12 := ⟨i.val, by omega⟩

/-- Row-major index of a two-site Pauli readout in the certificate. -/
def cIndex (i j : Fin 3) : Fin 12 := ⟨3 + 3 * i.val + j.val, by omega⟩

/-- Normalization divides by the trace two powers later than the readout exponent. -/
def rationalCoordinate (k : ℕ) (j : Fin 12) : ℚ :=
  dot4 (readoutRow j) (window k) / window k 2

private def projectiveCoordinate (k : ℕ) (j : Fin 12) : ℚ :=
  dot4 (readoutRow j) (projectivize (window k))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem tail_bound :
    (krylovDet (fun i => enclose (readoutRow (rIndex i)))
      (fun i j => enclose (readoutRow (cIndex i j)))).hi < 0 ∧ 0 < (box 2).lo := by
  decide +kernel

private theorem rationalCoordinate_eq_scaled (k : ℕ) (j : Fin 12)
    (h : window k 0 ≠ 0) (h₂ : window k 2 ≠ 0) :
    rationalCoordinate k j = (window k 0 / window k 2) * projectiveCoordinate k j := by
  unfold rationalCoordinate projectiveCoordinate projectivize dot4
  field_simp

private theorem krylovDet_scale {α : Type*} [CommRing α] (s : α)
    (r : Fin 3 → α) (C : Fin 3 → Fin 3 → α) :
    krylovDet (fun i => s * r i) (fun i j => s * C i j) = s ^ 6 * krylovDet r C := by
  unfold krylovDet dot3
  ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2500000 in
private theorem finite_bound : ∀ j : Fin 25, 0 < window (5 + j.val) 2 ∧
    krylovDet (fun i => rationalCoordinate (5 + j.val) (rIndex i))
      (fun i t => rationalCoordinate (5 + j.val) (cIndex i t)) < 0 := by
  decide +kernel

/-- The finite range (exponents 5–29) and the invariant tail (starting at 30)
prove strict negativity and positivity of the mass for every length at least seven. -/
theorem rational_chirality_negative (k : ℕ) (hk : 5 ≤ k) :
    0 < window k 2 ∧
    krylovDet (fun i => rationalCoordinate k (rIndex i))
      (fun i j => rationalCoordinate k (cIndex i j)) < 0 := by
  by_cases h : k < 30
  · simpa only [show 5 + (k - 5) = k by omega] using finite_bound ⟨k - 5, by omega⟩
  · have hb := window_inBox k (by omega)
    have h₂ : 0 < window k 2 :=
      (div_pos_iff_of_pos_right hb.1).mp (tail_bound.2.trans_le (hb.2 2).1)
    have hdet := Interval.contains_krylovDet
      (fun i => enclose_contains hb.2 (readoutRow (rIndex i)))
      (fun i j => enclose_contains hb.2 (readoutRow (cIndex i j)))
    have hsign := hdet.2.trans_lt tail_bound.1
    refine ⟨h₂, ?_⟩
    simp only [rationalCoordinate_eq_scaled k _ hb.1.ne' h₂.ne', krylovDet_scale]
    exact mul_neg_of_pos_of_neg (pow_pos (div_pos hb.1 h₂) _) hsign

end Arithmetic


section Transfer

open PeriodicMPSParentIntersection (Bond)
open PeriodicMPSTwoSiteAmbiguity (rawTwo)
open PeriodicMPSUniformHardCoreLocalization (normalizedMarginal normalizedMarginal_eq_rawTwo)
open PeriodicMPSUniformHardCoreTransferRecurrence (binaryInsertion binaryTransfer)
open PeriodicMPSUniformAntisymmetricTransfer
  (BondMatrix TransferMatrix mixedTransfer mixedRaw mixedRaw_trace conjugateCore
    rawTwo_eq_mixedRaw characteristicRecurrence transferReadout_isSolution)
open Polynomial

private def gaussianI : GaussianInt := ⟨0, 1⟩

private def gaussianCore : Fin 2 → BondMatrix GaussianInt :=
  ![!![1, 1; 0, 2], !![gaussianI, 1; 1, 1 + gaussianI]]

/-- The Gaussian-integer witness core, viewed over the complex numbers. -/
def core (i : Fin 2) : Bond := GaussianInt.toComplex.mapMatrix (gaussianCore i)

private def gaussianBra (i : Fin 2) : BondMatrix GaussianInt :=
  (gaussianCore i).map star

private def TG : TransferMatrix GaussianInt := mixedTransfer gaussianCore gaussianBra
private def T : TransferMatrix ℂ := mixedTransfer core (conjugateCore core)

private theorem map_gaussianBra (i : Fin 2) :
    GaussianInt.toComplex.mapMatrix (gaussianBra i) = conjugateCore core i := by
  ext j k
  exact GaussianInt.toComplex_star _

private theorem map_kronecker {n m : Type*} {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (A : Matrix n n R) (B : Matrix m m R) :
    (A ⊗ₖ B).map f = A.map f ⊗ₖ B.map f := by
  ext i j
  exact map_mul f _ _

private theorem map_TG : GaussianInt.toComplex.mapMatrix TG = T := by
  rw [TG, T, mixedTransfer, mixedTransfer, binaryTransfer, binaryTransfer, map_add]
  simp only [RingHom.mapMatrix_apply, map_kronecker]
  change (_ ⊗ₖ core 0 + _ ⊗ₖ core 1) = _
  rw [show (gaussianBra 0).map GaussianInt.toComplex = _ from map_gaussianBra 0,
    show (gaussianBra 1).map GaussianInt.toComplex = _ from map_gaussianBra 1]

private theorem flat_TG :
    reindex (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4) finProdFinEquiv TG =
      !![2, 1 - gaussianI, 1 + gaussianI, 2;
        -gaussianI, 3 - gaussianI, 1, 3 + gaussianI;
        gaussianI, 1, 3 + gaussianI, 3 - gaussianI;
        1, 1 + gaussianI, 1 - gaussianI, 6] := by
  funext i j
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem TG_charpoly :
    TG.charpoly = X ^ 4 - 14 * X ^ 3 + 65 * X ^ 2 - 158 * X + 154 := by
  rw [← charpoly_reindex (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4), flat_TG,
    Matrix.charpoly, det_succ_row_zero, Fin.sum_univ_four]
  simp only [det_fin_three, submatrix_apply]
  norm_num [Matrix.charmatrix_apply, Matrix.diagonal_apply, Fin.succAbove,
    Fin.castSucc, Fin.succ, Fin.lt_def, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_neg]
  have hsq : (Polynomial.C gaussianI) ^ 2 = -(1 : Polynomial GaussianInt) := by
    rw [← map_pow, show gaussianI ^ 2 = -1 by decide +kernel, map_neg, map_one]
  simp only [map_ofNat]
  linear_combination -(5 * X ^ 2 - 52 * X + 86) * hsq

private theorem T_charpoly :
    T.charpoly = X ^ 4 - 14 * X ^ 3 + 65 * X ^ 2 - 158 * X + 154 := by
  rw [← map_TG, RingHom.mapMatrix_apply, Matrix.charpoly_map, TG_charpoly]
  simp

private def recurrence (R : Type*) [CommRing R] : LinearRecurrence R :=
  ⟨4, ![-154, 158, -65, 14]⟩

private theorem transfer_recurrence :
    characteristicRecurrence T = recurrence ℂ := by
  change LinearRecurrence.mk 4 (fun i => -T.charpoly.coeff i) = _
  congr 1
  funext i
  fin_cases i <;>
    norm_num [T_charpoly, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, ← Polynomial.C_eq_natCast, Polynomial.coeff_C_mul, Polynomial.coeff_C]

private theorem window_next_low (k : ℕ) :
    window (k + 1) 0 = window k 1 ∧
    window (k + 1) 1 = window k 2 ∧
    window (k + 1) 2 = window k 3 ∧
    window (k + 1) 3 =
      -154 * window k 0 + 158 * window k 1 - 65 * window k 2 + 14 * window k 3 := by
  rw [window_succ]
  simp [dot4_eq_mulVec_apply, dot4, companion, sub_eq_add_neg]

private theorem window_shift (k : ℕ) (i : Fin 4) : window k i = window (k + i.val) 0 := by
  fin_cases i
  · rfl
  · exact (window_next_low k).1.symm
  · exact ((window_next_low (k + 1)).1.trans (window_next_low k).2.1).symm
  · exact ((window_next_low (k + 2)).1.trans
      ((window_next_low (k + 1)).2.1.trans (window_next_low k).2.2.1)).symm

private theorem trace_window_recurrence (k : ℕ) :
    window (k + 4) 0 =
      -154 * window k 0 + 158 * window (k + 1) 0 -
        65 * window (k + 2) 0 + 14 * window (k + 3) 0 := by
  rw [show k + 4 = (k + 1) + (3 : Fin 4).val by rfl, ← window_shift]
  rw [(window_next_low k).2.2.2, window_shift k 1, window_shift k 2, window_shift k 3]
  rfl

private theorem window_coordinate_recurrence (k : ℕ) (i : Fin 4) :
    window (k + 4) i =
      -154 * window k i + 158 * window (k + 1) i -
        65 * window (k + 2) i + 14 * window (k + 3) i := by
  rw [window_shift (k + 4) i, window_shift k i, window_shift (k + 1) i,
    window_shift (k + 2) i, window_shift (k + 3) i]
  simpa only [Nat.add_right_comm k _ i.val] using trace_window_recurrence (k + i.val)

private theorem linear_window_isSolution (a : Fin 4 → ℚ) :
    (recurrence ℂ).IsSolution (fun k => (↑(dot4 a (window k)) : ℂ)) := by
  intro k
  change (↑(dot4 a (window (k + 4))) : ℂ) =
    ∑ i : Fin 4, (![-154, 158, -65, 14] : Fin 4 → ℂ) i * (↑(dot4 a (window (k + i.val))) : ℂ)
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Fin.val_zero,
    Fin.val_one, Fin.val_two, Nat.add_zero]
  norm_num
  have h : dot4 a (window (k + 4)) =
    -(154 * dot4 a (window k)) + 158 * dot4 a (window (k + 1)) +
      -(65 * dot4 a (window (k + 2))) + 14 * dot4 a (window (k + 3)) := by
    simp only [dot4, window_coordinate_recurrence]
    ring
  simpa only [map_add, map_mul, map_neg, map_ofNat, Rat.coe_castHom] using
    congrArg (Rat.castHom ℂ) h

private def gaussianPauli (i : Fin 3) : BondMatrix GaussianInt :=
  ![!![0, 1; 1, 0], !![0, -gaussianI; gaussianI, 0], !![1, 0; 0, -1]] i

private def gaussianObservable (j : Fin 12) : TransferMatrix GaussianInt :=
  if hj : j.val < 3 then gaussianPauli ⟨j.val, hj⟩ ⊗ₖ 1
  else gaussianPauli ⟨(j.val - 3) / 3, by omega⟩ ⊗ₖ
    gaussianPauli ⟨(j.val - 3) % 3, by omega⟩

/-- Pauli matrices in the order X, Y, Z, with Y₀₁ = -i. -/
def pauli (i : Fin 3) : Bond := GaussianInt.toComplex.mapMatrix (gaussianPauli i)

private def observable (j : Fin 12) : TransferMatrix ℂ :=
  GaussianInt.toComplex.mapMatrix (gaussianObservable j)

private theorem observable_r (i : Fin 3) : observable (rIndex i) = pauli i ⊗ₖ 1 := by
  have hi : (rIndex i).val < 3 := i.isLt
  simp only [observable, gaussianObservable, dite_eq_left hi, RingHom.mapMatrix_apply, map_kronecker]
  change pauli i ⊗ₖ GaussianInt.toComplex.mapMatrix (1 : BondMatrix GaussianInt) = _
  rw [map_one]

private theorem observable_c (i j : Fin 3) : observable (cIndex i j) = pauli i ⊗ₖ pauli j := by
  have hij : ¬(cIndex i j).val < 3 := by dsimp [cIndex]; omega
  have hi : ((cIndex i j).val - 3) / 3 = i.val := by dsimp [cIndex]; omega
  have hj : ((cIndex i j).val - 3) % 3 = j.val := by dsimp [cIndex]; omega
  simp [observable, gaussianObservable, dite_eq_right hij, RingHom.mapMatrix_apply, map_kronecker,
    pauli, hi, hj]

private def insertion {R : Type*} [CommRing R]
    (ket bra : Fin 2 → BondMatrix R) (O : TransferMatrix R) : TransferMatrix R :=
  ∑ p, ∑ q, O q p • binaryInsertion bra ket q p

private def transferReadout {R : Type*} [CommRing R] (B : TransferMatrix R) :
    TransferMatrix R →ₗ[R] R :=
  (Matrix.traceLinearMap _ R R).comp (LinearMap.mulLeft R B)

private theorem trace_readout_mixedRaw {R : Type*} [CommRing R]
    (ket bra : Fin 2 → BondMatrix R) (O : TransferMatrix R) (k : ℕ) :
    (O * mixedRaw ket bra k).trace =
      transferReadout (insertion ket bra O) (mixedTransfer ket bra ^ k) := by
  change (O * mixedRaw ket bra k).trace =
    (insertion ket bra O * mixedTransfer ket bra ^ k).trace
  simp only [insertion, Finset.sum_mul, smul_mul_assoc, Matrix.trace_sum, Matrix.trace_smul]
  change (∑ q, ∑ p, O q p * (binaryInsertion bra ket q p * mixedTransfer ket bra ^ k).trace) = _
  exact Finset.sum_comm

private theorem map_insertion (j : Fin 12) :
    GaussianInt.toComplex.mapMatrix (insertion gaussianCore gaussianBra (gaussianObservable j)) =
      insertion core (conjugateCore core) (observable j) := by
  unfold insertion
  simp only [map_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  have hB : GaussianInt.toComplex.mapMatrix (binaryInsertion gaussianBra gaussianCore q p) =
      binaryInsertion (conjugateCore core) core q p := by
    unfold binaryInsertion
    rw [RingHom.mapMatrix_apply, map_kronecker]
    change GaussianInt.toComplex.mapMatrix (gaussianBra q.1 * gaussianBra q.2) ⊗ₖ
      GaussianInt.toComplex.mapMatrix (gaussianCore p.1 * gaussianCore p.2) = _
    rw [map_mul, map_mul, map_gaussianBra, map_gaussianBra]
    rfl
  ext i t
  change GaussianInt.toComplex (gaussianObservable j q p *
    binaryInsertion gaussianBra gaussianCore q p i t) = _
  rw [map_mul]
  exact congrArg (fun M : TransferMatrix ℂ => observable j q p * M i t) hB

private def momentSeeds : Fin 4 → Fin 12 → GaussianInt :=
  ![![48, 36, 20, 46, 20, 12, 20, 26, 24, 12, 24, -6],
    ![420, 228, 60, 376, 196, 36, 196, 100, 60, 36, 60, 12],
    ![3546, 2100, 226, 3058, 1796, 222, 1796, 1082, 72, 222, 72, -6],
    ![29004, 18420, 1808, 24740, 15044, 2040, 15044, 10676, 252, 2040, 252, -988]]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem gaussian_moment_seeds (k : Fin 4) (j : Fin 12) :
    (insertion gaussianCore gaussianBra (gaussianObservable j) * TG ^ k.val).trace =
      momentSeeds k j := by
  fin_cases k <;> fin_cases j <;> decide +kernel

private def traceSeeds : Fin 4 → GaussianInt := ![4, 14, 66, 488]

private theorem gaussian_trace_seeds (k : Fin 4) :
    (TG ^ k.val).trace = traceSeeds k := by
  fin_cases k <;> decide +kernel

private theorem trace_initial (k : Fin 4) :
    GaussianInt.toComplex (traceSeeds k) = (window k.val 0 : ℂ) := by
  fin_cases k <;> norm_num [traceSeeds, window, traceWindow, map_ofNat]

set_option maxRecDepth 10000 in
private theorem interpolation_initial (k : Fin 4) (j : Fin 12) :
    GaussianInt.toComplex (momentSeeds k j) = (↑(dot4 (readoutRow j) (window k.val)) : ℂ) := by
  have h : (momentSeeds k j).im = 0 := by
    fin_cases k <;> fin_cases j <;> decide +kernel
  have hr : ((momentSeeds k j).re : ℚ) = dot4 (readoutRow j) (window k.val) := by
    fin_cases k <;> fin_cases j <;> decide +kernel
  rw [show GaussianInt.toComplex (momentSeeds k j) =
      ((momentSeeds k j).re : ℂ) + ((momentSeeds k j).im : ℂ) * Complex.I from rfl,
    h, Int.cast_zero, zero_mul, add_zero, ← Rat.cast_intCast, hr]

private theorem trace_as_window (k : ℕ) : (T ^ k).trace = (window k 0 : ℂ) := by
  have hT := transferReadout_isSolution T (Matrix.traceLinearMap _ ℂ ℂ)
  rw [transfer_recurrence] at hT
  let row : Fin 4 → ℚ := ![1, 0, 0, 0]
  have hr (l : ℕ) : dot4 row (window l) = window l 0 := by simp [row, dot4]
  have hW := linear_window_isSolution row
  simp only [hr] at hW
  have heq := ((recurrence ℂ).eq_iff_eqOn_range_order _ _ hT hW).mpr ?_
  · exact congrFun heq k
  · intro l hl
    have hl' : l < 4 := Finset.mem_range.mp hl
    let a : Fin 4 := ⟨l, hl'⟩
    change (T ^ l).trace = _
    rw [← map_TG, ← map_pow, RingHom.mapMatrix_apply, ← AddMonoidHom.map_trace,
      show l = a.val from rfl, gaussian_trace_seeds, trace_initial]

private theorem moment_as_window (j : Fin 12) (k : ℕ) :
    (observable j * mixedRaw core (conjugateCore core) k).trace =
      (↑(dot4 (readoutRow j) (window k)) : ℂ) := by
  let B := insertion core (conjugateCore core) (observable j)
  have hT := transferReadout_isSolution T (transferReadout B)
  rw [transfer_recurrence] at hT
  have heq := ((recurrence ℂ).eq_iff_eqOn_range_order _ _ hT
    (linear_window_isSolution (readoutRow j))).mpr ?_
  · rw [trace_readout_mixedRaw]
    exact congrFun heq k
  · intro l hl
    have hl' : l < 4 := Finset.mem_range.mp hl
    let a : Fin 4 := ⟨l, hl'⟩
    change (B * T ^ l).trace = _
    rw [show B = _ from (map_insertion j).symm, ← map_TG, ← map_pow, ← map_mul,
      RingHom.mapMatrix_apply, ← AddMonoidHom.map_trace, show l = a.val from rfl,
      gaussian_moment_seeds, interpolation_initial]

/-- Bloch components use Pauli expectation values of the trace-one marginal. -/
noncomputable def blochVector (ρ : TransferMatrix ℂ) (i : Fin 3) : ℝ :=
  ((pauli i ⊗ₖ 1) * ρ).trace.re

/-- The Pauli–Pauli correlations, with the first site indexing rows. -/
noncomputable def blochCorrelation (ρ : TransferMatrix ℂ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => ((pauli i ⊗ₖ pauli j) * ρ).trace.re

private theorem normalized_readout (j : Fin 12) (s : ℕ) :
    (observable j * normalizedMarginal (s + 2) core).trace.re =
      (rationalCoordinate (s + 2) j : ℝ) := by
  rw [normalizedMarginal_eq_rawTwo, rawTwo_eq_mixedRaw, mul_smul_comm, Matrix.trace_smul,
    moment_as_window, mixedRaw_trace, show mixedTransfer core (conjugateCore core) = T from rfl,
    trace_as_window]
  have hshift := window_shift (s + 2) (2 : Fin 4)
  change window (s + 2) 2 = window (s + 2 + 2) 0 at hshift
  rw [← hshift]
  simp [rationalCoordinate, ← Complex.ofReal_ratCast]
  rw [div_eq_mul_inv, mul_comm]

/-- Exact Pauli coordinates of the trace-normalized actual marginal at length
`s + 4`. The transfer exponent of these readouts is `s + 2`. -/
theorem normalizedMarginal_blochCoordinates (s : ℕ) :
    (∀ i, blochVector (normalizedMarginal (s + 2) core) i =
      (rationalCoordinate (s + 2) (rIndex i) : ℝ)) ∧
    (∀ i j, blochCorrelation (normalizedMarginal (s + 2) core) i j =
      (rationalCoordinate (s + 2) (cIndex i j) : ℝ)) := by
  constructor
  · intro i
    simpa only [observable_r, blochVector] using normalized_readout (rIndex i) s
  · intro i j
    simpa only [observable_c, blochCorrelation] using normalized_readout (cIndex i j) s

/-- Every length `n ≥ 7` has positive normalization mass and strictly negative
`det[r, C r, C² r]` for the same Gaussian-integer core. Here `r` and `C` are
the Pauli expectations of the trace-one marginal, with no extra scale factor. -/
theorem normalizedMarginal_chirality_negative (n : ℕ) (hn : 7 ≤ n) :
    let ρ := normalizedMarginal (n - 2) core
    let r := blochVector ρ
    let C : Matrix (Fin 3) (Fin 3) ℝ := blochCorrelation ρ
    0 < (rawTwo core (n - 4)).trace.re ∧
      (Matrix.of fun i => ![r i, (C *ᵥ r) i, (C ^ 2 *ᵥ r) i]).det < 0 := by
  dsimp only
  let s := n - 4
  have hs : s + 2 = n - 2 := by dsimp [s]; omega
  have h := rational_chirality_negative (s + 2) (by omega)
  refine ⟨?_, ?_⟩
  · change 0 < (rawTwo core s).trace.re
    rw [rawTwo_eq_mixedRaw, mixedRaw_trace, show mixedTransfer core (conjugateCore core) = T from rfl,
      trace_as_window]
    have hshift := window_shift (s + 2) (2 : Fin 4)
    change window (s + 2) 2 = window (s + 2 + 2) 0 at hshift
    rw [← hshift, ← Complex.ofReal_ratCast, Complex.ofReal_re]
    exact_mod_cast h.1
  · rw [← hs, ← krylovDet_eq_det (blochVector (normalizedMarginal (s + 2) core))
      (blochCorrelation (normalizedMarginal (s + 2) core))]
    obtain ⟨hr, hc⟩ := normalizedMarginal_blochCoordinates s
    rw [funext hr, funext₂ hc]
    simpa only [krylovDet, dot3, Rat.cast_add, Rat.cast_mul, Rat.cast_neg, Rat.cast_zero] using
      (Rat.cast_lt (K := ℝ)).mpr h.2

end Transfer

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformChirality
