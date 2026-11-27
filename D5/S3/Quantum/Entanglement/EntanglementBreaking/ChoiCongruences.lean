/- GID: D5/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EntanglementBreaking/ChoiCongruences
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rectangular Choi congruences and the k-entanglement-breaking condition. -/

import OmegaBuild.Commands
import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import D5.S3.Resource.EntanglementWitness

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.Entanglement.EntanglementBreaking

open _root_.Matrix
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Resource.CompositeCones
open D5.S3.Resource.EntanglementWitness
open scoped Kronecker ComplexOrder

/-- Choi matrix in input × output order. -/
def inputChoi {a b : ℕ} (Φ : MatrixMap (Fin a) (Fin b) ℂ) :
    Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ :=
  Φ.choi_matrix.submatrix Prod.swap Prod.swap

def fromInputChoi {a b : ℕ} (W : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    MatrixMap (Fin a) (Fin b) ℂ :=
  MatrixMap.of_choi_matrix (W.submatrix Prod.swap Prod.swap)

@[simp] theorem inputChoi_fromInputChoi {a b : ℕ}
    (W : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    inputChoi (fromInputChoi W) = W := by
  ext ⟨i, u⟩ ⟨j, v⟩
  change (∑ x : Fin a, ∑ y : Fin a, Matrix.single i j (1 : ℂ) x y *
    W (x, u) (y, v)) = W (i, u) (j, v)
  simp [Matrix.single, ite_and]

def amplify {a b : ℕ} (k : ℕ) (Φ : MatrixMap (Fin a) (Fin b) ℂ) :
    MatrixMap (Fin k × Fin a) (Fin k × Fin b) ℂ :=
  MatrixMap.kron (MatrixMap.id (Fin k) ℂ) Φ

/-- Definition 3.1 of Devendra–Mallick–Sumesh. -/
def IsKEB {a b : ℕ} (k : ℕ) (Φ : MatrixMap (Fin a) (Fin b) ℂ) : Prop :=
  (amplify k Φ).IsPositive ∧ ∀ X, X.PosSemidef → separableCone (amplify k Φ X)

theorem amplify_apply {a b k : ℕ} (Φ : MatrixMap (Fin a) (Fin b) ℂ)
    (X : Matrix (Fin k × Fin a) (Fin k × Fin a) ℂ)
    (p q : Fin k) (u v : Fin b) :
    amplify k Φ X (p, u) (q, v) =
      ∑ i : Fin a, ∑ j : Fin a, inputChoi Φ (i, u) (j, v) * X (p, i) (q, j) := by
  rw [amplify, MatrixMap.kron_def]
  simp [MatrixMap.id, Matrix.single, ite_and, inputChoi, MatrixMap.choi_matrix]

/-- Amplification of a pure PSD input is a rectangular congruence of the input-first Choi matrix. -/
theorem amplify_vecMulVec {a b k : ℕ} (Φ : MatrixMap (Fin a) (Fin b) ℂ)
    (A : Matrix (Fin k) (Fin a) ℂ) :
    amplify k Φ (vecMulVec (fun p => A p.1 p.2) (star (fun p => A p.1 p.2))) =
      (A ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) * inputChoi Φ *
        (A ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ))ᴴ := by
  ext ⟨p, u⟩ ⟨q, v⟩
  rw [amplify_apply]
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, conjTranspose_kronecker,
    conjTranspose_one, kronecker_apply, one_apply, conjTranspose_apply, vecMulVec_apply,
    Pi.star_apply]
  simp only [mul_ite, ite_mul, mul_one, zero_mul, mul_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/-- A rectangular local congruence preserves the existing separable cone. -/
theorem separable_local_congruence {a b k : ℕ}
    (A : Matrix (Fin k) (Fin a) ℂ)
    {W : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ} (hW : separableCone W) :
    separableCone ((A ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) * W *
      (A ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ))ᴴ) := by
  rcases hW with ⟨n, P, Q, hPQ, rfl⟩
  refine ⟨n, fun i => A * P i * Aᴴ, Q,
    fun i => ⟨(hPQ i).1.mul_mul_conjTranspose_same A, (hPQ i).2⟩, ?_⟩
  rw [Matrix.mul_sum, Matrix.sum_mul]
  simp only [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, one_mul, mul_one]

/-- Separable rectangular Choi congruences imply the full PSD-input property of Definition 3.1. -/
theorem isKEB_of_choi_congruences {a b k : ℕ} (Φ : MatrixMap (Fin a) (Fin b) ℂ)
    (h : ∀ A : Matrix (Fin k) (Fin a) ℂ,
      separableCone ((A ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ)) * inputChoi Φ *
        (A ⊗ₖ (1 : Matrix (Fin b) (Fin b) ℂ))ᴴ)) :
    IsKEB k Φ := by
  have hsep : ∀ X, X.PosSemidef →
      separableCone (amplify k Φ X) := by
    intro X hX
    obtain ⟨n, s, rfl⟩ := posSemidef_iff_eq_sum_vecMulVec.mp hX
    rw [map_sum]
    refine Finset.sum_induction _ _ (fun _ _ => separableCone_add) separableCone_zero ?_
    intro i _
    let A : Matrix (Fin k) (Fin a) ℂ := fun p q => s i (p, q)
    have he : (fun p : Fin k × Fin a => A p.1 p.2) = s i := by
      funext p
      cases p
      rfl
    simpa only [← amplify_vecMulVec, he] using h A
  exact ⟨fun _ hX => separable_isPosSemidef (hsep _ hX), hsep⟩
