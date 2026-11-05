/- GID: D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseEdgeSymbol
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/SymmetricExtensions/BoseEdgeSymbol
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coherent symbols of the canonical marginal-adjoint tensor lift. -/

import D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseSOSDuality
import D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseLDUI

/-! The lift is the existing marginal adjoint from DickeExtension. No second
tensor or marginal model is introduced. The polynomial application is due
to Gulati--Nechita--Park, Theorem 8.16. -/

open scoped BigOperators ComplexOrder
open Matrix MvPolynomial
open D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension
open D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseOccupationTwirl

namespace D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseEdgeSymbol

noncomputable section
set_option backward.isDefEq.respectTransparency false

open private edgeLift edge_trace_duality from
  D5.S3.Quantum.Entanglement.SymmetricExtensions.DickeExtension

variable {I L : Type*} [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L]

private lemma tensorPhase_split (a b : I) (hab : a ≠ b) (z : L → ℂ) (x : I → L) :
    tensorPhase z x = z (x a) * z (x b) *
      ∏ i : {k : I // k ≠ a ∧ k ≠ b}, z (x i) := by
  have he : (∏ i : {k : I // k ≠ a ∧ k ≠ b}, z (x i)) =
      ∏ i ∈ ({a,b} : Finset I)ᶜ, z (x i) := by
    symm
    apply Finset.prod_subtype
    intro i
    simp
  rw [he]
  simpa only [tensorPhase,Finset.prod_pair hab] using
    (Finset.prod_mul_prod_compl {a,b} (fun i => z (x i))).symm

private lemma tensorPhase_edgeSplit (a b : I) (hab : a ≠ b) (z : L → ℂ)
    (v : L × L) (c : {k : I // k ≠ a ∧ k ≠ b} → L) :
    tensorPhase z ((edgeSplit a b hab).symm (v,c)) =
      (z v.1 * z v.2) * tensorPhase z c := by
  rw [tensorPhase_split a b hab]
  have ha : ((edgeSplit a b hab).symm (v,c)) a = v.1 := by simp [edgeSplit]
  have hb : ((edgeSplit a b hab).symm (v,c)) b = v.2 := by
    simp [edgeSplit,Ne.symm hab]
  rw [ha,hb]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp [edgeSplit,i.property.1,i.property.2]

/-- The actual adjoint of the unnormalized marginal has the coherent symbol
of the pair multiplied by the norm contribution of the remaining registers. -/
private lemma edgeLift_coherent (a b : I) (hab : a ≠ b)
    (A : Matrix (L × L) (L × L) ℂ) (z : L → ℂ) :
    star (tensorPhase z) ⬝ᵥ (edgeLift a b hab A *ᵥ tensorPhase z) =
      (∑ c : {k : I // k ≠ a ∧ k ≠ b} → L,
        star (tensorPhase z c) * tensorPhase z c) *
      (star (fun v : L × L => z v.1 * z v.2) ⬝ᵥ
        (A *ᵥ (fun v => z v.1 * z v.2))) := by
  let e := edgeSplit (L := L) a b hab
  simp only [dotProduct,Matrix.mulVec,Finset.mul_sum,Pi.star_apply,
    edgeLift,Matrix.submatrix_apply]
  conv_lhs =>
    arg 2
    ext x
    rw [← e.symm.sum_comp]
  rw [← e.symm.sum_comp]
  dsimp only [e]
  simp only [Equiv.apply_symm_apply,Fintype.sum_prod_type]
  simp_rw [tensorPhase_edgeSplit]
  simp only [edgeLift,Matrix.submatrix_apply,Equiv.apply_symm_apply,
    Matrix.kronecker_apply,Matrix.one_apply,mul_ite,ite_mul,mul_one,mul_zero,zero_mul,
    Finset.sum_ite_eq',Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  simp only [Finset.mul_sum,Finset.sum_mul,star_mul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro c hc
  ring

private lemma tensor_norm_sum (z : L → ℂ) :
    (∑ c : I → L, star (tensorPhase z c) * tensorPhase z c) =
      (∑ i : L, star (z i) * z i) ^ Fintype.card I := by
  simp only [tensorPhase,star_prod,← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : I) i => star (z i) * z i)]
  simp

end
end D5.S3.Quantum.Entanglement.SymmetricExtensions.BoseEdgeSymbol
