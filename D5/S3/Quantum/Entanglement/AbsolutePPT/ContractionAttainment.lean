/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/ContractionAttainment
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/ContractionAttainment
   mirror-E: none(waiver:source-only-preparation)
   anchors: []
   utility: none
   digest: A dimension-general positive decomposition gives literal APPT contraction rays and a five-row attaining density. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic

/-!
The ordered-pair Kraus identity has a half-weight on both orientations and
includes the diagonal. Thus the diagonal symmetric operator supplies exactly
2 E_aa X E_aa. No order on the first local index type is needed.
Full transpose relates the two partial-transpose conventions. Unitary
conjugation preserves the positive-contraction hypotheses, giving literal APPT.
The five-row coordinate projection yields an attaining family; no upper bound
is asserted.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

open Matrix
open scoped ComplexOrder

namespace D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment
open D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite (APPT partialTranspose)

noncomputable section
section Generic
variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- The elementary operator E_ab tensor I_B. -/
def blockUnit (a b : A) : Matrix (A × B) (A × B) ℂ :=
  Matrix.kronecker (Matrix.single a b (1 : ℂ)) (1 : Matrix B B ℂ)

def symBlock (a b : A) : Matrix (A × B) (A × B) ℂ :=
  blockUnit a b + blockUnit b a

def antiBlock (a b : A) : Matrix (A × B) (A × B) ℂ :=
  blockUnit a b - blockUnit b a

/-- This is first-subsystem transpose, expressed using the project's convention. -/
def firstTranspose (X : Matrix (A × B) (A × B) ℂ) :
    Matrix (A × B) (A × B) ℂ := (partialTranspose X)ᵀ

/-- Ordered pairs include the diagonal; each pair has weight one half. -/
def krausSum (X : Matrix (A × B) (A × B) ℂ) :
    Matrix (A × B) (A × B) ℂ :=
  (1 / 2 : ℂ) • ∑ a : A, ∑ b : A,
    (symBlock a b * X * (symBlock a b)ᴴ +
      antiBlock a b * (1 - X) * (antiBlock a b)ᴴ)

private theorem block_unit_apply (a b i k : A) (j l : B) :
    blockUnit a b (i,j) (k,l) =
      if i = a ∧ k = b ∧ j = l then (1 : ℂ) else 0 := by
  by_cases hia : i = a <;> by_cases hkb : k = b <;> by_cases hjl : j = l <;>
    simp_all [blockUnit, Matrix.kronecker_apply, Matrix.single, Matrix.one_apply, eq_comm]

private theorem block_unit_adjoint (a b : A) :
    (blockUnit a b : Matrix (A × B) (A × B) ℂ)ᴴ = blockUnit b a := by
  ext ⟨i,j⟩ ⟨k,l⟩
  simp only [Matrix.conjTranspose_apply, block_unit_apply]
  by_cases hi : i = b <;> by_cases hk : k = a <;> by_cases hj : j = l <;>
    simp [hi, hk, hj, eq_comm]

private theorem unit_left (a b i k : A) (j l : B)
    (X : Matrix (A × B) (A × B) ℂ) :
    (blockUnit a b * X : Matrix (A × B) (A × B) ℂ) (i,j) (k,l) = if i = a then X (b,j) (k,l) else 0 := by
  by_cases hi : i = a <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, block_unit_apply,
      hi, ite_and, ite_mul, eq_comm]

private theorem unit_right (a b i k : A) (j l : B)
    (X : Matrix (A × B) (A × B) ℂ) :
    (X * blockUnit a b : Matrix (A × B) (A × B) ℂ) (i,j) (k,l) = if k = b then X (i,j) (a,l) else 0 := by
  by_cases hk : k = b <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, block_unit_apply,
      hk, ite_and, mul_ite, eq_comm]

private theorem sandwich_sum (X : Matrix (A × B) (A × B) ℂ) :
    (∑ a : A, ∑ b : A, blockUnit a b * X * blockUnit a b) = firstTranspose X := by
  ext ⟨i,j⟩ ⟨k,l⟩
  simp [Matrix.sum_apply, unit_right, unit_left, firstTranspose,
    partialTranspose, Matrix.transpose_apply]

private theorem unit_gram_sum :
    (∑ a : A, ∑ b : A,
      (blockUnit a b : Matrix (A × B) (A × B) ℂ) * blockUnit b a) =
      (Fintype.card A : ℂ) • 1 := by
  ext ⟨i,j⟩ ⟨k,l⟩
  by_cases hik : i = k
  · subst k
    by_cases hjl : j = l <;>
      simp [Matrix.sum_apply, unit_right, block_unit_apply, Matrix.smul_apply,
        Matrix.one_apply, Prod.mk.injEq, hjl, eq_comm]
  · simp [Matrix.sum_apply, unit_right, block_unit_apply, Matrix.smul_apply,
      Matrix.one_apply, Prod.mk.injEq, hik, eq_comm, ite_and]

private theorem unit_square_sum :
    (∑ a : A, ∑ b : A,
      (blockUnit a b : Matrix (A × B) (A × B) ℂ) * blockUnit a b) = 1 := by
  ext ⟨i,j⟩ ⟨k,l⟩
  by_cases hik : i = k
  · subst k
    by_cases hjl : j = l <;>
      simp [Matrix.sum_apply, unit_right, block_unit_apply, Matrix.one_apply,
        Prod.mk.injEq, hjl, eq_comm, ite_and]
  · simp [Matrix.sum_apply, unit_right, block_unit_apply, Matrix.one_apply,
      Prod.mk.injEq, hik, eq_comm, ite_and]

private theorem pair_expansion (a b : A) (X : Matrix (A × B) (A × B) ℂ) :
    symBlock a b * X * (symBlock a b)ᴴ +
      antiBlock a b * (1-X) * (antiBlock a b)ᴴ =
    (2 : ℂ) • (blockUnit a b * X * blockUnit a b +
      blockUnit b a * X * blockUnit b a) +
    blockUnit a b * blockUnit b a + blockUnit b a * blockUnit a b -
    blockUnit a b * blockUnit a b - blockUnit b a * blockUnit b a := by
  simp only [symBlock, antiBlock, Matrix.conjTranspose_add,
    Matrix.conjTranspose_sub, block_unit_adjoint, smul_add, two_smul]
  noncomm_ring

/-- Exact positive-decomposition identity for every complex matrix, with no
Hermitian, nonsingularity or multiplicity assumption. The scalar subtraction
is in C, so the identity also makes sense when the first index type is empty. -/
theorem kraus_identity (X : Matrix (A × B) (A × B) ℂ) :
    krausSum X = ((Fintype.card A : ℂ) - 1) • 1 + (2 : ℂ) • firstTranspose X := by
  have swapped (f : A → A → Matrix (A × B) (A × B) ℂ) :
      (∑ a : A, ∑ b : A, f b a) = ∑ a : A, ∑ b : A, f a b := by
    rw [Finset.sum_comm]
  have hs := sandwich_sum X
  have hss : (∑ a : A, ∑ b : A, blockUnit b a * X * blockUnit b a) =
      firstTranspose X := by rw [swapped]; exact hs
  have hg := @unit_gram_sum A B _ _ _ _
  have hgs : (∑ a : A, ∑ b : A,
      (blockUnit b a : Matrix (A × B) (A × B) ℂ) * blockUnit a b) =
      (Fintype.card A : ℂ) • 1 := by rw [swapped]; exact hg
  have hq := @unit_square_sum A B _ _ _ _
  have hqs : (∑ a : A, ∑ b : A,
      (blockUnit b a : Matrix (A × B) (A × B) ℂ) * blockUnit b a) = 1 := by
    rw [swapped]; exact hq
  unfold krausSum
  simp only [pair_expansion, smul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.smul_sum]
  rw [hs, hss, hg, hgs, hq, hqs]
  module

/-- The project's second-factor partial transpose is positive after the
dimension-dependent identity shift, for every PSD contraction. -/
theorem partial_transpose_posSemidef (X : Matrix (A × B) (A × B) ℂ)
    (hX : X.PosSemidef) (hC : (1-X).PosSemidef) :
    (((Fintype.card A : ℂ)-1) • 1 + (2 : ℂ) • partialTranspose X).PosSemidef := by
  have hp : (krausSum X).PosSemidef := by
    apply Matrix.PosSemidef.smul _ (show (0 : ℂ) ≤ 1/2 by norm_num [Complex.nonneg_iff])
    apply Matrix.posSemidef_sum
    intro a _
    apply Matrix.posSemidef_sum
    intro b _
    exact (hX.mul_mul_conjTranspose_same (symBlock a b)).add
      (hC.mul_mul_conjTranspose_same (antiBlock a b))
  rw [kraus_identity] at hp
  have ht := hp.transpose
  simpa only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one,
    firstTranspose, Matrix.transpose_transpose] using ht

/-- Literal APPT, quantified over every global unitary of the full tensor
product. The contraction is conjugated before the positive identity is used. -/
theorem contraction_appt (X : Matrix (A × B) (A × B) ℂ)
    (hX : X.PosSemidef) (hC : (1-X).PosSemidef) :
    APPT (((Fintype.card A : ℂ)-1) • 1 + (2 : ℂ) • X) := by
  intro U
  let V : Matrix (A × B) (A × B) ℂ := U
  have hu : V * Vᴴ = 1 := by
    simpa only [V, Unitary.coe_star, Matrix.star_eq_conjTranspose]
      using Unitary.coe_mul_star_self U
  have hp := hX.mul_mul_conjTranspose_same V
  have hq := hC.mul_mul_conjTranspose_same V
  have he : V * (1-X) * Vᴴ = 1 - V * X * Vᴴ := by
    rw [mul_sub, sub_mul, mul_one, hu]
  rw [he] at hq
  have h := partial_transpose_posSemidef (V*X*Vᴴ) hp hq
  have pt_one : partialTranspose (1 : Matrix (A × B) (A × B) ℂ) = 1 := by
    ext ⟨i,j⟩ ⟨k,l⟩
    simp [partialTranspose, Matrix.one_apply, Prod.mk.injEq, eq_comm]
  have pt_add (M N : Matrix (A × B) (A × B) ℂ) :
      partialTranspose (M+N) = partialTranspose M + partialTranspose N := rfl
  have pt_smul (c : ℂ) (M : Matrix (A × B) (A × B) ℂ) :
      partialTranspose (c • M) = c • partialTranspose M := rfl
  change (partialTranspose (V * _ * Vᴴ)).PosSemidef
  simpa only [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul,
    mul_one, hu, pt_add, pt_smul, pt_one] using h

end Generic

/-- Projection onto the first two complete coordinate rows. -/
def fiveRowProjector (n : ℕ) : Matrix (Fin 5 × Fin n) (Fin 5 × Fin n) ℂ :=
  diagonal (fun p => if p.1.val < 2 then 1 else 0)

def fiveRowDensity (n : ℕ) : Matrix (Fin 5 × Fin n) (Fin 5 × Fin n) ℂ :=
  ((1 / (24*(n : ℝ)) : ℝ) : ℂ) •
    ((4 : ℂ) • 1 + (2 : ℂ) • fiveRowProjector n)

private theorem projector_square (n : ℕ) :
    fiveRowProjector n * fiveRowProjector n = fiveRowProjector n := by
  unfold fiveRowProjector
  rw [diagonal_mul_diagonal]
  congr 1
  funext p
  split_ifs <;> norm_num

private theorem projector_positive (n : ℕ) :
    (fiveRowProjector n).PosSemidef ∧ (1-fiveRowProjector n).PosSemidef := by
  have hH : (fiveRowProjector n).IsHermitian := by
    unfold fiveRowProjector
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro p
    split_ifs <;> simp [IsSelfAdjoint]
  have hp : (fiveRowProjector n)ᴴ * fiveRowProjector n = fiveRowProjector n := by
    rw [hH.eq, projector_square]
  have hc : (1-fiveRowProjector n)ᴴ * (1-fiveRowProjector n) = 1-fiveRowProjector n := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hH.eq]
    noncomm_ring [projector_square n]
  exact ⟨hp ▸ posSemidef_conjTranspose_mul_self _,
    hc ▸ posSemidef_conjTranspose_mul_self _⟩

private theorem projector_trace (n : ℕ) : (fiveRowProjector n).trace = 2*(n : ℂ) := by
  rw [fiveRowProjector, Matrix.trace_diagonal, Fintype.sum_prod_type]
  simp [Fin.sum_univ_succ]
  <;> ring

private theorem idempotent_trace_rank {I : Type} [Fintype I] [DecidableEq I]
    (P : Matrix I I ℂ) (hP : P*P=P) : P.trace = (P.rank : ℂ) := by
  have hlin : IsIdempotentElem P.mulVecLin := by
    rw [← Matrix.toLin'_apply']
    change Matrix.toLin' P ∘ₗ Matrix.toLin' P = Matrix.toLin' P
    rw [← Matrix.toLin'_mul, hP]
  have ht := (LinearMap.IsIdempotentElem.isProj_range _ hlin).trace
  have htrace : LinearMap.trace ℂ (I → ℂ) P.mulVecLin = P.trace := by
    rw [← Matrix.toLin'_apply', LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ I),
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  rw [htrace] at ht
  exact ht

/-- A genuine rank-2n five-row coordinate projector gives a trace-one density
with literal APPT and purity 5/(24n), in every positive second dimension. -/
theorem five_row_attainment (n : ℕ) (hn : 0 < n) :
    (fiveRowProjector n).rank = 2*n ∧
    (fiveRowDensity n).PosSemidef ∧ (fiveRowDensity n).trace = 1 ∧
    APPT (fiveRowDensity n) ∧
    (fiveRowDensity n * fiveRowDensity n).trace.re = 5/(24*(n : ℝ)) := by
  have hP := projector_positive n
  have hr : (fiveRowProjector n).rank = 2*n := by
    have ht := idempotent_trace_rank (fiveRowProjector n) (projector_square n)
    rw [projector_trace] at ht
    exact_mod_cast ht.symm
  have hi : (1 : Matrix (Fin 5 × Fin n) (Fin 5 × Fin n) ℂ).trace = 5*(n : ℂ) := by
    simp [Matrix.trace_one, Fintype.card_prod]
  have hnum : APPT ((4 : ℂ) • 1 + (2 : ℂ) • fiveRowProjector n) := by
    simpa only [Fintype.card_fin, Nat.cast_ofNat, show (5 : ℂ)-1=4 by norm_num]
      using contraction_appt (fiveRowProjector n) hP.1 hP.2
  have hs : (0 : ℝ) ≤ 1/(24*(n : ℝ)) := by positivity
  have hd : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hm : ((4 : ℂ) • 1 + (2 : ℂ) • fiveRowProjector n) *
      ((4 : ℂ) • 1 + (2 : ℂ) • fiveRowProjector n) =
      (16 : ℂ) • 1 + (20 : ℂ) • fiveRowProjector n := by
    simp only [mul_add, add_mul, one_mul, mul_one, Matrix.mul_smul,
      Matrix.smul_mul, smul_smul, projector_square]
    module
  refine ⟨hr, ?_, ?_, ?_, ?_⟩
  · exact ((Matrix.PosSemidef.one.smul (by norm_num : (0 : ℂ) ≤ 4)).add
      (hP.1.smul (by norm_num : (0 : ℂ) ≤ 2))).smul (Complex.zero_le_real.mpr hs)
  · simp only [fiveRowDensity, Matrix.trace_smul, Matrix.trace_add, hi,
      projector_trace, smul_eq_mul]
    push_cast
    field_simp [hd]
    <;> ring
  · intro U
    have h := (hnum U).smul (Complex.zero_le_real.mpr hs)
    change (partialTranspose ((U : Matrix _ _ ℂ) * fiveRowDensity n *
      (U : Matrix _ _ ℂ)ᴴ)).PosSemidef
    have pt_smul (c : ℂ) (M : Matrix (Fin 5 × Fin n) (Fin 5 × Fin n) ℂ) :
        partialTranspose (c • M) = c • partialTranspose M := rfl
    simpa only [fiveRowDensity, Matrix.mul_smul, Matrix.smul_mul, pt_smul] using h
  · have he : (fiveRowDensity n * fiveRowDensity n).trace =
        ((5/(24*(n : ℝ)) : ℝ) : ℂ) := by
      simp only [fiveRowDensity, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hm,
        Matrix.trace_smul, Matrix.trace_add, hi, projector_trace, smul_eq_mul]
      push_cast
      field_simp [hd]
      <;> ring
    rw [he, Complex.ofReal_re]

#print axioms kraus_identity
#print axioms partial_transpose_posSemidef
#print axioms contraction_appt
#print axioms five_row_attainment

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment
