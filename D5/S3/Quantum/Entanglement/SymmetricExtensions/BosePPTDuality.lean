/- GID: D5/S3/Quantum/Entanglement/SymmetricExtensions/BosePPTDuality
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/SymmetricExtensions/BosePPTDuality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native SOS necessity and actual cut certificates for Bose PPT duality. -/

import D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseSOSCertificates
import D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseDual

/-! The operator/polynomial duality is the prerequisite in
Gulati--Nechita--Park, Theorems 8.9 and 8.11. The necessity argument uses
closedness of the native SOS coefficient cone; it does not erase a closure
from an operator dual sum. -/

open scoped BigOperators ComplexOrder RealInnerProductSpace
open Matrix MvPolynomial
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPureBound
open D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor
open D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseOccupationTwirl
open D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseCoherentSymbol
open D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseRootTranspose

namespace D5.S3.Quantum.Entanglement.SymmetricExtensions.BosePPTDuality

noncomputable section
set_option backward.isDefEq.respectTransparency false

open private tensorPhase_perm from
  D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseOccupationTwirl
open private cutSwap from
  D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseCoherentSymbol

variable {I L : Type*} [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L]

private lemma partialTranspose_hermitian (S : Finset I)
    (E : Matrix (I → L) (I → L) ℂ) (hE : E.IsHermitian) :
    (partialTransposeOn S E).IsHermitian := by
  ext x y
  exact hE.apply _ _

private lemma trace_partialTranspose_pair (S : Finset I)
    (A B : Matrix (I → L) (I → L) ℂ) :
    (partialTransposeOn S A * B).trace = (A * partialTransposeOn S B).trace := by
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,partialTransposeOn]
  change (∑ x, ∑ y, A (S.piecewise y x) (S.piecewise x y) * B y x) =
    ∑ x, ∑ y, A x y * B (S.piecewise x y) (S.piecewise y x)
  suffices h : (∑ p : (I → L) × (I → L),
      A (S.piecewise p.2 p.1) (S.piecewise p.1 p.2) * B p.2 p.1) =
      ∑ p : (I → L) × (I → L),
        A p.1 p.2 * B (S.piecewise p.1 p.2) (S.piecewise p.2 p.1) by
    simpa only [Fintype.sum_prod_type] using h
  apply Fintype.sum_equiv (cutSwap S)
  intro p
  change _ = A (S.piecewise p.2 p.1) (S.piecewise p.1 p.2) *
    B (S.piecewise (S.piecewise p.2 p.1) (S.piecewise p.1 p.2))
      (S.piecewise (S.piecewise p.1 p.2) (S.piecewise p.2 p.1))
  congr 2 <;> funext i <;> by_cases hi : i ∈ S <;> simp [Finset.piecewise,hi]

/-- The real linear support space for the actual full tensor symmetrizer. -/
def boseSpace : Submodule ℝ (HermitianMat (I → L) ℂ) where
  carrier := {A | P I L * A.mat * P I L = A.mat}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB
    change P I L * A.mat * P I L = A.mat at hA
    change P I L * B.mat * P I L = B.mat at hB
    change P I L * (A.mat+B.mat) * P I L = A.mat+B.mat
    simp only [Matrix.mul_add,Matrix.add_mul,hA,hB]
  smul_mem' := by
    intro c A hA
    change P I L * A.mat * P I L = A.mat at hA
    change P I L * (c • A.mat) * P I L = c • A.mat
    simp only [Matrix.mul_smul,Matrix.smul_mul,hA]

/-- Genuine full Bose support and positivity at every product-basis cut. -/
def bosePPT : Set (HermitianMat (I → L) ℂ) :=
  {A | A ∈ boseSpace ∧ AllCutsPPT A.mat}

private lemma tensorPhase_fixed (z : L → ℂ) :
    P I L *ᵥ tensorPhase z = tensorPhase z :=
  P_mulVec_of_symmetric _ (fun σ x => tensorPhase_perm z x σ)

private lemma coherent_projector_supported (z : L → ℂ) :
    P I L * vecMulVec (tensorPhase z) (star (tensorPhase z)) * P I L =
      vecMulVec (tensorPhase z) (star (tensorPhase z)) := by
  rw [mul_vecMulVec,tensorPhase_fixed,vecMulVec_mul]
  have hr : star (tensorPhase z) ᵥ* P I L = star (tensorPhase z) := by
    rw [← P_hermitian I L,← star_mulVec,tensorPhase_fixed]
  rw [hr]

private lemma psd_of_nonnegative_pairings
    {N : Type*} [Fintype N] [DecidableEq N] (A : HermitianMat N ℂ)
    (h : ∀ B : HermitianMat N ℂ, B.mat.PosSemidef → 0 ≤ inner ℝ B A) :
    A.mat.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg A.H
  intro v
  let B : HermitianMat N ℂ :=
    ⟨vecMulVec v (star v),(Matrix.posSemidef_vecMulVec_self_star v).1⟩
  have hp := h B (Matrix.posSemidef_vecMulVec_self_star v)
  have he : inner ℝ B A = (star v ⬝ᵥ (A.mat *ᵥ v)).re := by
    rw [HermitianMat.inner_eq_re_trace,Matrix.trace_mul_comm]
    change ((A.mat * vecMulVec v (star v)).trace).re = _
    rw [mul_vecMulVec,trace_vecMulVec,dotProduct_comm]
  rw [he] at hp
  exact Complex.nonneg_iff.mpr ⟨hp,(A.H.im_star_dotProduct_mulVec_self v).symm⟩

section SOS

variable {r n : ℕ}

private lemma realSymbol_add
    (A B : Matrix (Fin r → Fin n) (Fin r → Fin n) ℂ) :
    realSymbol (A+B) = realSymbol A + realSymbol B := by
  simp [realSymbol,Matrix.add_apply,Complex.add_re,Finset.sum_add_distrib]

private lemma realSymbol_smul (c : ℝ)
    (A : Matrix (Fin r → Fin n) (Fin r → Fin n) ℂ) :
    realSymbol (c • A) = c • realSymbol A := by
  simp [realSymbol,Matrix.smul_apply,RCLike.real_smul_eq_coe_mul,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    MvPolynomial.smul_eq_C_mul,Finset.mul_sum,C_mul_monomial]

private lemma realSymbol_orthogonal
    (A : HermitianMat (Fin r → Fin n) ℂ)
    (hA : A ∈ (boseSpace (I := Fin r) (L := Fin n)).orthogonal) :
    realSymbol A.mat = 0 := by
  apply MvPolynomial.funext
  intro u
  rw [eval_realSymbol,map_zero]
  let z : Fin n → ℂ := fun i => u i
  let B : HermitianMat (Fin r → Fin n) ℂ :=
    ⟨vecMulVec (tensorPhase z) (star (tensorPhase z)),
      (Matrix.posSemidef_vecMulVec_self_star _).1⟩
  have hB : B ∈ boseSpace := coherent_projector_supported z
  have hp := (Submodule.mem_orthogonal _ _).mp hA B hB
  rw [HermitianMat.inner_eq_re_trace,Matrix.trace_mul_comm] at hp
  change ((A.mat * vecMulVec (tensorPhase z) (star (tensorPhase z))).trace).re = 0 at hp
  rwa [mul_vecMulVec,trace_vecMulVec,dotProduct_comm] at hp

private def realSOSCone : ProperCone ℝ (HermitianMat (Fin r → Fin n) ℂ) where
  carrier := {A | IsSumSq (realSymbol A.mat)}
  zero_mem' := by simpa [realSymbol] using (IsSumSq.zero : IsSumSq (0 : MvPolynomial (Fin n) ℝ))
  add_mem' := by
    intro A B hA hB
    change IsSumSq (realSymbol (A.mat+B.mat))
    rw [realSymbol_add]
    exact hA.add hB
  smul_mem' := by
    intro c A hA
    change IsSumSq (realSymbol (c.val • A.mat))
    rw [realSymbol_smul,MvPolynomial.smul_eq_C_mul]
    have hc : IsSumSq (C c.val : MvPolynomial (Fin n) ℝ) := by
      convert IsSumSq.mul_self (C (Real.sqrt c.val) : MvPolynomial (Fin n) ℝ) using 1
      rw [← map_mul,Real.mul_self_sqrt c.property]
    exact hc.mul hA
  isClosed' := realSymbol_sos_closed

private lemma dual_realSOS_in_bosePPT
    (E : HermitianMat (Fin r → Fin n) ℂ)
    (hE : E ∈ ProperCone.dual (innerₗ (HermitianMat (Fin r → Fin n) ℂ))
      (realSOSCone (r := r) (n := n) : Set (HermitianMat (Fin r → Fin n) ℂ))) : E ∈ bosePPT := by
  constructor
  · have he : E ∈ (boseSpace (I := Fin r) (L := Fin n)).orthogonal.orthogonal := by
      apply (Submodule.mem_orthogonal _ _).mpr
      intro A hA
      have ha : A ∈ realSOSCone := by
        change IsSumSq (realSymbol A.mat)
        rw [realSymbol_orthogonal A hA]
        exact IsSumSq.zero
      have hn : -A ∈ realSOSCone := by
        change IsSumSq (realSymbol (-A).mat)
        rw [realSymbol_orthogonal (-A) ((boseSpace (I := Fin r) (L := Fin n)).orthogonal.neg_mem hA)]
        exact IsSumSq.zero
      have hp := hE ha
      have hm := hE hn
      change 0 ≤ inner ℝ A E at hp
      change 0 ≤ inner ℝ (-A) E at hm
      rw [inner_neg_left] at hm
      linarith
    simpa only [Submodule.orthogonal_orthogonal] using he
  · intro S
    let T : HermitianMat (Fin r → Fin n) ℂ :=
      ⟨partialTransposeOn S E.mat,partialTranspose_hermitian S E.mat E.H⟩
    apply psd_of_nonnegative_pairings T
    intro B hB
    let Z : HermitianMat (Fin r → Fin n) ℂ :=
      ⟨partialTransposeOn S B.mat,partialTranspose_hermitian S B.mat B.H⟩
    have hz : Z ∈ realSOSCone := by
      change IsSumSq (realSymbol (partialTransposeOn S B.mat))
      rw [realSymbol_partialTranspose]
      exact realSymbol_posSemidef_sos B.mat hB
    have hp := hE hz
    change 0 ≤ inner ℝ Z E at hp
    rw [HermitianMat.inner_eq_re_trace] at hp ⊢
    change 0 ≤ ((partialTransposeOn S B.mat * E.mat).trace).re at hp
    rwa [trace_partialTranspose_pair] at hp

/-- Every actual Bose-PPT dual operator has a genuine native SOS real
coherent symbol. Closedness is proved from the coefficient Gram cone. -/
theorem dual_bosePPT_real_sos
    (A : HermitianMat (Fin r → Fin n) ℂ)
    (hA : A ∈ ProperCone.dual (innerₗ (HermitianMat (Fin r → Fin n) ℂ))
      (bosePPT : Set (HermitianMat (Fin r → Fin n) ℂ))) :
    IsSumSq (realSymbol A.mat) := by
  have ha : A ∈ ProperCone.dual (innerₗ (HermitianMat (Fin r → Fin n) ℂ)).flip
      (ProperCone.dual (innerₗ (HermitianMat (Fin r → Fin n) ℂ))
        (realSOSCone (r := r) (n := n) : Set (HermitianMat (Fin r → Fin n) ℂ)) :
          Set (HermitianMat (Fin r → Fin n) ℂ)) := by
    intro E hE
    rw [flip_innerₗ]
    exact hA (dual_realSOS_in_bosePPT E hE)
  rw [ProperCone.dual_flip_dual] at ha
  exact ha

#print axioms dual_bosePPT_real_sos

end SOS
end
end D5.S3.Quantum.Entanglement.SymmetricExtensions.BosePPTDuality
