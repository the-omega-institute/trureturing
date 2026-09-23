/- GID: D5/S3/Quantum/Reduction/IsometricCompression
   generality: G
   mirror-B: D5/B/S3/Quantum/Reduction/IsometricCompression
   mirror-E: none(waiver:finite-algebraic-proof)
   anchors: []
   utility: none
   digest: Isometric compression exposes leakage and preserves zero-leakage words. -/

import Mathlib

/-!
# Isometric compression and instrument leakage

The carrier is the actual rectangular complex matrix algebra. Matrix positivity,
Gram-zero detection and finite sums are reused from pinned Mathlib. In particular,
`Matrix.conjTranspose_mul_self_eq_zero` is not reproved. The existing finite Kraus
channel owner is the downstream target; this file does not introduce a second CP
predicate. The polynomial compression identities are the standard orthogonal
projection calculation. No norm, infinite-time, or differential-geometric claim
is encoded by the algebraic results below.
-/

noncomputable section
open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Reduction.IsometricCompression

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {n d m e s : Type*}
  [Fintype n] [DecidableEq n] [Fintype d] [DecidableEq d]
  [Fintype m] [DecidableEq m] [Fintype e] [DecidableEq e]
  [Fintype s]

/-- The orthogonal support of an isometric frame. -/
def support (U : Matrix n d ℂ) : Matrix n n ℂ := U * Uᴴ

/-- Pull back a physical operator to the logical space. -/
def compress (U : Matrix n d ℂ) (A : Matrix n n ℂ) : Matrix d d ℂ :=
  Uᴴ * A * U

/-- The component of a rectangular map outside the output frame. -/
def normal (W : Matrix m e ℂ) (B : Matrix m d ℂ) : Matrix m d ℂ :=
  (1 - support W) * B

private theorem support_star (U : Matrix n d ℂ) : (support U)ᴴ = support U := by
  simp [support, Matrix.conjTranspose_mul]

private theorem support_idempotent (U : Matrix n d ℂ) (hU : Uᴴ * U = 1) :
    support U * support U = support U := by
  calc
    support U * support U = U * (Uᴴ * U) * Uᴴ := by
      simp only [support, Matrix.mul_assoc]
    _ = support U := by rw [hU]; simp [support]

private theorem complement_idempotent (U : Matrix n d ℂ) (hU : Uᴴ * U = 1) :
    (1 - support U) * (1 - support U) = 1 - support U := by
  have hP := support_idempotent U hU
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    hP, sub_self, sub_zero]

/-- The multiplication defect is precisely the excursion through the discarded space. -/
theorem multiplication_defect (U : Matrix n d ℂ) (A B : Matrix n n ℂ) :
    compress U (A * B) - compress U A * compress U B =
      Uᴴ * A * (1 - support U) * B * U := by
  simp only [compress, support, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_one, Matrix.mul_assoc]

/-- Orthogonality makes the normal block's Gram matrix the compressed complement. -/
theorem normal_gram (W : Matrix m e ℂ) (hW : Wᴴ * W = 1)
    (B C : Matrix m d ℂ) :
    (normal W B)ᴴ * normal W C = Bᴴ * (1 - support W) * C := by
  have hs : (1 - support W)ᴴ = 1 - support W := by simp [support_star]
  calc
    (normal W B)ᴴ * normal W C =
        Bᴴ * ((1 - support W) * (1 - support W)) * C := by
      simp only [normal, Matrix.conjTranspose_mul, hs, Matrix.mul_assoc]
    _ = Bᴴ * (1 - support W) * C := by rw [complement_idempotent W hW]

/-- For a self-adjoint left operator, the defect is a cross Gram matrix. -/
theorem hermitian_multiplication_defect (U : Matrix n d ℂ)
    (hU : Uᴴ * U = 1) (A B : Matrix n n ℂ) (hA : Aᴴ = A) :
    compress U (A * B) - compress U A * compress U B =
      (normal U (A * U))ᴴ * normal U (B * U) := by
  rw [normal_gram U hU, Matrix.conjTranspose_mul, hA, multiplication_defect]
  simp only [Matrix.mul_assoc]

/-- Even commuting physical operators can have noncommuting compressions. -/
theorem commutator_defect (U : Matrix n d ℂ) (hU : Uᴴ * U = 1)
    (A B : Matrix n n ℂ) (hA : Aᴴ = A) (hB : Bᴴ = B) :
    compress U A * compress U B - compress U B * compress U A =
      compress U (A * B - B * A) -
        (normal U (A * U))ᴴ * normal U (B * U) +
        (normal U (B * U))ᴴ * normal U (A * U) := by
  have hab := hermitian_multiplication_defect U hU A B hA
  have hba := hermitian_multiplication_defect U hU B A hB
  have hsub : compress U (A * B - B * A) =
      compress U (A * B) - compress U (B * A) := by
    simp only [compress, Matrix.mul_sub, Matrix.sub_mul]
  rw [hsub, ← hab, ← hba]
  abel

/-- Tangential and normal components account for the entire input Gram matrix. -/
theorem compressed_gram_add_leakage (W : Matrix m e ℂ) (hW : Wᴴ * W = 1)
    (B : Matrix m d ℂ) :
    (Wᴴ * B)ᴴ * (Wᴴ * B) + (normal W B)ᴴ * normal W B = Bᴴ * B := by
  rw [normal_gram W hW]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    support, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_assoc]
  abel

/-- Exact instrument normalization balance, allowing different input and output frames. -/
theorem instrument_mass_balance (U : Matrix n d ℂ) (W : Matrix m e ℂ)
    (hU : Uᴴ * U = 1) (hW : Wᴴ * W = 1) (K : s → Matrix m n ℂ)
    (hK : (∑ i, (K i)ᴴ * K i) = 1) :
    (∑ i, (Wᴴ * (K i * U))ᴴ * (Wᴴ * (K i * U))) +
      (∑ i, (normal W (K i * U))ᴴ * normal W (K i * U)) = 1 := by
  calc
    _ = ∑ i, ((Wᴴ * (K i * U))ᴴ * (Wᴴ * (K i * U)) +
        (normal W (K i * U))ᴴ * normal W (K i * U)) := by
      rw [Finset.sum_add_distrib]
    _ = ∑ i, (K i * U)ᴴ * (K i * U) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact compressed_gram_add_leakage W hW (K i * U)
    _ = Uᴴ * (∑ i, (K i)ᴴ * K i) * U := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_sum, Matrix.sum_mul,
        Matrix.mul_assoc]
    _ = 1 := by rw [hK, Matrix.mul_one, hU]

/-- There is no cancellation between positive leakage Gram matrices. -/
theorem sum_gram_eq_zero_iff (R : s → Matrix m d ℂ) :
    (∑ i, (R i)ᴴ * R i) = 0 ↔ ∀ i, R i = 0 := by
  have hnonneg : ∀ i, (0 : Matrix d d ℂ) ≤ (R i)ᴴ * R i :=
    fun i => (Matrix.posSemidef_conjTranspose_mul_self (R i)).nonneg
  constructor
  · intro h i
    exact Matrix.conjTranspose_mul_self_eq_zero.mp
      (congrFun ((Fintype.sum_eq_zero_iff_of_nonneg hnonneg).mp h) i)
  · intro h
    apply (Fintype.sum_eq_zero_iff_of_nonneg hnonneg).mpr
    funext i
    exact Matrix.conjTranspose_mul_self_eq_zero.mpr (h i)

/-- A compressed normalized instrument is normalized exactly when every Kraus map has zero leakage. -/
theorem compressed_instrument_iff (U : Matrix n d ℂ) (W : Matrix m e ℂ)
    (hU : Uᴴ * U = 1) (hW : Wᴴ * W = 1) (K : s → Matrix m n ℂ)
    (hK : (∑ i, (K i)ᴴ * K i) = 1) :
    (∑ i, (Wᴴ * (K i * U))ᴴ * (Wᴴ * (K i * U))) = 1 ↔
      ∀ i, normal W (K i * U) = 0 := by
  have hbalance := instrument_mass_balance U W hU hW K hK
  rw [← sum_gram_eq_zero_iff]
  constructor
  · intro h
    rw [h] at hbalance
    exact (add_left_cancel (show (1 : Matrix d d ℂ) +
      (∑ i, (normal W (K i * U))ᴴ * normal W (K i * U)) = 1 + 0 by
        simpa using hbalance))
  · intro h
    simpa only [h, add_zero] using hbalance

/-- Zero leakage is the concrete intertwining identity, not merely a probability statement. -/
theorem zero_leakage_iff_intertwines (U : Matrix n d ℂ) (W : Matrix m e ℂ)
    (K : Matrix m n ℂ) :
    normal W (K * U) = 0 ↔ K * U = W * (Wᴴ * (K * U)) := by
  simp only [normal, support, Matrix.sub_mul, Matrix.one_mul,
    Matrix.mul_assoc, sub_eq_zero]

/-- Intertwining persists through every finite operator word, including the empty history. -/
theorem word_intertwines {ι : Type*} (U : Matrix n d ℂ)
    (K : ι → Matrix n n ℂ) (k : ι → Matrix d d ℂ)
    (h : ∀ a, K a * U = U * k a) (w : List ι) :
    (w.map K).prod * U = U * (w.map k).prod := by
  induction w with
  | nil => simp
  | cons a w ih =>
      simp only [List.map_cons, List.prod_cons]
      calc
        K a * (w.map K).prod * U = K a * ((w.map K).prod * U) :=
          Matrix.mul_assoc _ _ _
        _ = K a * (U * (w.map k).prod) := by rw [ih]
        _ = (K a * U) * (w.map k).prod := (Matrix.mul_assoc _ _ _).symm
        _ = U * (k a * (w.map k).prod) := by rw [h a, Matrix.mul_assoc]

/-- The same word identity preserves unnormalised branch matrices, so zero-probability branches are not divided out. -/
theorem branch_intertwines (U : Matrix n d ℂ) (A : Matrix n n ℂ)
    (a rho : Matrix d d ℂ) (hA : A * U = U * a) :
    A * (U * rho * Uᴴ) * Aᴴ = U * (a * rho * aᴴ) * Uᴴ := by
  have hstar : Uᴴ * Aᴴ = aᴴ * Uᴴ := by
    simpa only [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose hA
  calc
    _ = (A * U) * rho * (Uᴴ * Aᴴ) := by simp only [Matrix.mul_assoc]
    _ = (U * a) * rho * (aᴴ * Uᴴ) := by rw [hA, hstar]
    _ = _ := by simp only [Matrix.mul_assoc]

#print axioms multiplication_defect
#print axioms normal_gram
#print axioms hermitian_multiplication_defect
#print axioms commutator_defect
#print axioms compressed_gram_add_leakage
#print axioms instrument_mass_balance
#print axioms sum_gram_eq_zero_iff
#print axioms compressed_instrument_iff
#print axioms zero_leakage_iff_intertwines
#print axioms word_intertwines
#print axioms branch_intertwines

end D5.S3.Quantum.Reduction.IsometricCompression
