/- GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/SuperchargeProducts
   generality: I
   mirror-B: D5/B/S3/Quantum/SpinChains/SupersymmetricFermion/SuperchargeProducts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Dressed-fermion support and the three-site split product. -/

/-
fullD_support:
  proof_shape: content
  escape_witness: fullD_support (form 2): A nonzero finite product forces the annihilated bit and every unchanged bit.
  Direct frozen dependencies: qubitZ, tensorOp, Assignment, visibleProjector.
fullSplit_eq_dressed_product:
  proof_shape: content
  escape_witness: fullSplit_eq_dressed_product (form 2): Local tensor multiplication on three consecutive sites determines the cubic sign and projectors.
  Direct frozen dependencies: qubitZ, tensorOp, Assignment, visibleProjector.
admission_basis: escape-witness
Direct frozen dependency keys (GID; statement_id):
Assignment = PredictiveThermodynamic.Physical.Assignment; sha256:186896178b3ea09d109f4546cae53a1b2c485c3990a05a1b88d8deaaae3e423f
Chain dependencies: D5.S3.Quantum.SpinChains.SupersymmetricFermion.DressedOperators; freeze in topological import order.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.SpinChains.SupersymmetricFermion.DressedOperators

set_option linter.unusedSimpArgs false
open scoped BigOperators Matrix Classical
set_option quotPrecheck false in
local notation "tensorOp" => (fun {N : ℕ} (w : Fin N → Matrix Bool Bool ℂ) =>
  Matrix.submatrix
    (D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp (n := N)
      (fun i => Matrix.submatrix (w i) finTwoEquiv finTwoEquiv))
    (fun (s : Fin N → Bool) (i : Fin N) => finTwoEquiv.symm (s i))
    (fun (s : Fin N → Bool) (i : Fin N) => finTwoEquiv.symm (s i)))
open PredictiveThermodynamic.Physical (Assignment visibleProjector)
open D5.S3.Quantum.FiniteDimensional (qubitZ)
local notation "spinZ" => (qubitZ.submatrix finTwoEquiv.symm finTwoEquiv.symm)
local notation "spinP" => ((1 : Matrix Bool Bool ℂ) - visibleProjector)

namespace D5.S3.Quantum.SpinChains.SupersymmetricFermion.SuperchargeProducts
noncomputable section
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.DressedOperators

def fullQ {N : ℕ} (coupling : Fin N → ℝ) : FullOperator N :=
  ∑ i : Fin N, (coupling i : ℂ) • fullD i

theorem fullD_support {N : ℕ} (i : Fin N) (s t : Assignment N)
    (h : fullD i s t ≠ 0) : t i = true ∧ s = Function.update t i false := by
  let tensorProduct {N : ℕ} (w : Fin N → Local) : FullOperator N := tensorOp w
  have spinZ_def : spinZ = Matrix.diagonal (fun b => if b then (-1 : ℂ) else 1) := by
    ext s t
    cases s <;> cases t <;> rfl
  have spinP_def : spinP = Matrix.diagonal (fun b => if b then (0 : ℂ) else 1) := by
    ext s t
    cases s <;> cases t <;> norm_num [visibleProjector, Matrix.diagonal, Matrix.sub_apply]
  have hentry : fullD i s t = ∏ k : Fin N, dressedWord i k (s k) (t k) := by
    simp [fullD, D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp, Matrix.submatrix_apply]
  rw [hentry] at h
  classical
  have hm (k : Fin N) : dressedWord i k (s k) (t k) ≠ 0 := by
    intro hz
    apply h
    exact Finset.prod_eq_zero (Finset.mem_univ k) hz
  have hs : s i = false ∧ t i = true := by
    have hmi := hm i
    simp [dressedWord,Matrix.single] at hmi
    exact hmi
  refine ⟨hs.2, ?_⟩
  funext k
  by_cases hki : k = i
  · subst k
    simp [hs.1]
  · rw [Function.update_of_ne hki]
    have hd : dressedWord i k ∈ [1,spinP,spinZ] := by
      unfold dressedWord
      split_ifs <;> simp_all
    simp at hd
    have he : s k ≠ t k → dressedWord i k (s k) (t k) = 0 := by
      intro hk
      rcases hd with hd | hd | hd <;> rw [hd] <;>
        simp only [spinP_def,spinZ_def,Matrix.one_apply,Matrix.diagonal_apply,hk,if_false]
    by_contra hst
    exact hm k (he hst)

theorem fullSplit_eq_dressed_product {N : ℕ} (j : Fin N)
    (hr : j.val + 2 < N) :
    fullSplit j = (fullD j)ᴴ *
      (fullD (⟨j.val + 2, by omega⟩ : Fin N))ᴴ *
      fullD (⟨j.val + 1, by omega⟩ : Fin N) := by
  let tensorProduct {N : ℕ} (w : Fin N → Local) : FullOperator N := tensorOp w
  have tensorOp_entries {N : ℕ} (w : Fin N → Local) :
      tensorProduct w = (fun s t => ∏ i : Fin N, w i (s i) (t i)) := by
    ext s t
    simp [tensorProduct, D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp,
      Matrix.submatrix_apply]
  have spinZ_def : spinZ = Matrix.diagonal (fun b => if b then (-1 : ℂ) else 1) := by
    ext s t
    cases s <;> cases t <;> rfl
  have spinP_def : spinP = Matrix.diagonal (fun b => if b then (0 : ℂ) else 1) := by
    ext s t
    cases s <;> cases t <;> norm_num [visibleProjector, Matrix.diagonal, Matrix.sub_apply]
  have tensorOp_mul {N : ℕ} (u v : Fin N → Local) :
      tensorProduct u * tensorProduct v = tensorProduct (fun i => u i * v i) := by
    classical
    rw [tensorOp_entries, tensorOp_entries, tensorOp_entries]
    ext s t
    change (∑ x : Assignment N, (∏ i : Fin N, u i (s i) (x i)) * (∏ i : Fin N, v i (x i) (t i))) =
      ∏ i : Fin N, ∑ b : Bool, u i (s i) b * v i b (t i)
    simp_rw [← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun i b => u i (s i) b * v i b (t i))).symm
  have tensorOp_adjoint {N : ℕ} (w : Fin N → Local) :
      (tensorProduct w)ᴴ = tensorProduct (fun i => (w i)ᴴ) := by
    classical
    rw [tensorOp_entries, tensorOp_entries]
    ext s t
    change star (∏ i : Fin N, w i (t i) (s i)) = ∏ i : Fin N, star (w i (t i) (s i))
    simp
  classical
  unfold fullSplit fullD
  rw [tensorOp_adjoint, tensorOp_adjoint, tensorOp_mul, tensorOp_mul]
  congr 1
  funext k
  have hcases : k.val + 1 < j.val ∨ k.val + 1 = j.val ∨ k.val = j.val ∨
      k.val = j.val + 1 ∨ k.val = j.val + 2 ∨ k.val = j.val + 3 ∨
      j.val + 3 < k.val := by omega
  rcases hcases with hk | hk | hk | hk | hk | hk | hk
  all_goals simp (disch := omega) only [dressedWord,splitWord,Fin.lt_def,Fin.ext_iff,if_pos,if_neg]
  all_goals ext s t
  all_goals cases s <;> cases t
  all_goals norm_num [Matrix.single,spinZ_def, qubitZ, finTwoEquiv,spinP_def, visibleProjector,Matrix.mul_apply,
    Matrix.conjTranspose_apply,Matrix.diagonal_apply,Matrix.one_apply,
    Matrix.neg_apply,Matrix.sub_apply,Fintype.sum_bool]

end
end D5.S3.Quantum.SpinChains.SupersymmetricFermion.SuperchargeProducts
