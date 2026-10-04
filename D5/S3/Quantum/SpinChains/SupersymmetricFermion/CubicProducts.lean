/- GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/CubicProducts
   generality: I
   mirror-B: D5/B/S3/Quantum/SpinChains/SupersymmetricFermion/CubicProducts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Local cubic products and their supercharge anticommutator. -/

/-
fullQ_split_localized:
  proof_shape: content
  escape_witness: fullQ_split_localized (form 2): Index separation kills the remote terms and six local products select the surviving neighbours.
  Direct frozen dependencies: Assignment.
fullNumber_left_creator_neighbours:
  proof_shape: content
  escape_witness: fullNumber_left_creator_neighbours (form 2): The left occupation kills one adjacent creator term and keeps the right hopping term.
  Direct frozen dependencies: tensorOp, Assignment, visibleProjector.
fullNumber_right_creator_neighbours:
  proof_shape: content
  escape_witness: fullNumber_right_creator_neighbours (form 2): The right occupation kills one adjacent creator term and keeps the left hopping term.
  Direct frozen dependencies: tensorOp, Assignment, visibleProjector.
admission_basis: escape-witness
Direct frozen dependency keys (GID; statement_id):
Assignment = PredictiveThermodynamic.Physical.Assignment; sha256:186896178b3ea09d109f4546cae53a1b2c485c3990a05a1b88d8deaaae3e423f
Chain dependencies: D5.S3.Quantum.SpinChains.SupersymmetricFermion.SuperchargeProducts; freeze in topological import order.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.SpinChains.SupersymmetricFermion.SuperchargeProducts

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

namespace D5.S3.Quantum.SpinChains.SupersymmetricFermion.CubicProducts
noncomputable section
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.DressedOperators
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.SuperchargeProducts

theorem fullQ_split_localized {N : ℕ} (coupling : Fin N → ℝ)
    (j : Fin N) (hr : j.val + 2 < N) :
    fullQ coupling * fullSplit j + fullSplit j * fullQ coupling =
      ∑ i : Fin N, (coupling i : ℂ) •
        (if i.val + 1 = j.val then fullSplit j * fullD i else
         if i.val = j.val ∨ i.val = j.val + 2 then fullD i * fullSplit j else
         if i.val = j.val + 3 then fullSplit j * fullD i else 0) := by
  have local_split_m1_qr {N : ℕ} (i j : Fin N) (hi : i.val + 1 = j.val) (hr : j.val + 2 < N) :
      fullD i * (fullSplit j) = 0 := by
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
    have tensorOp_zero_at {N : ℕ} (w : Fin N → Local) (i : Fin N)
        (h : w i = 0) : tensorProduct w = 0 := by
      classical
      rw [tensorOp_entries]
      ext s t
      change (∏ k : Fin N, w k (s k) (t k)) = 0
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h]; rfl)
    simp only [fullD,fullSplit]
    rw [tensorOp_mul]
    let k0 : Fin N := ⟨j.val - 1, by omega⟩
    apply tensorOp_zero_at _ k0
    simp (disch := omega) only [dressedWord,splitWord,k0,Fin.lt_def,Fin.ext_iff,if_pos,if_neg]
    ext s t
    cases s <;> cases t <;> norm_num [Matrix.single,spinP_def, visibleProjector,spinZ_def, qubitZ, finTwoEquiv,Matrix.mul_apply,
      Matrix.conjTranspose_apply,Matrix.diagonal_apply,Matrix.one_apply,
      Matrix.sub_apply,Fintype.sum_bool]
  have local_split_p0_rq {N : ℕ} (i j : Fin N) (hi : i.val = j.val + 0) (hr : j.val + 2 < N) :
      (fullSplit j) * fullD i = 0 := by
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
    have tensorOp_zero_at {N : ℕ} (w : Fin N → Local) (i : Fin N)
        (h : w i = 0) : tensorProduct w = 0 := by
      classical
      rw [tensorOp_entries]
      ext s t
      change (∏ k : Fin N, w k (s k) (t k)) = 0
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h]; rfl)
    simp only [fullD,fullSplit]
    rw [tensorOp_mul]
    let k0 : Fin N := ⟨j.val + 1, by omega⟩
    apply tensorOp_zero_at _ k0
    simp (disch := omega) only [dressedWord,splitWord,k0,Fin.lt_def,Fin.ext_iff,if_pos,if_neg]
    ext s t
    cases s <;> cases t <;> norm_num [Matrix.single,spinP_def, visibleProjector,spinZ_def, qubitZ, finTwoEquiv,Matrix.mul_apply,
      Matrix.conjTranspose_apply,Matrix.diagonal_apply,Matrix.one_apply,
      Matrix.sub_apply,Fintype.sum_bool]
  have local_split_p1_qr {N : ℕ} (i j : Fin N) (hi : i.val = j.val + 1) (hr : j.val + 2 < N) :
      fullD i * (fullSplit j) = 0 := by
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
    have tensorOp_zero_at {N : ℕ} (w : Fin N → Local) (i : Fin N)
        (h : w i = 0) : tensorProduct w = 0 := by
      classical
      rw [tensorOp_entries]
      ext s t
      change (∏ k : Fin N, w k (s k) (t k)) = 0
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h]; rfl)
    simp only [fullD,fullSplit]
    rw [tensorOp_mul]
    let k0 : Fin N := ⟨j.val + 0, by omega⟩
    apply tensorOp_zero_at _ k0
    simp (disch := omega) only [dressedWord,splitWord,k0,Fin.lt_def,Fin.ext_iff,if_pos,if_neg]
    ext s t
    cases s <;> cases t <;> norm_num [Matrix.single,spinP_def, visibleProjector,spinZ_def, qubitZ, finTwoEquiv,Matrix.mul_apply,
      Matrix.conjTranspose_apply,Matrix.diagonal_apply,Matrix.one_apply,
      Matrix.sub_apply,Fintype.sum_bool]
  have local_split_p1_rq {N : ℕ} (i j : Fin N) (hi : i.val = j.val + 1) (hr : j.val + 2 < N) :
      (fullSplit j) * fullD i = 0 := by
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
    have tensorOp_zero_at {N : ℕ} (w : Fin N → Local) (i : Fin N)
        (h : w i = 0) : tensorProduct w = 0 := by
      classical
      rw [tensorOp_entries]
      ext s t
      change (∏ k : Fin N, w k (s k) (t k)) = 0
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h]; rfl)
    simp only [fullD,fullSplit]
    rw [tensorOp_mul]
    let k0 : Fin N := ⟨j.val + 1, by omega⟩
    apply tensorOp_zero_at _ k0
    simp (disch := omega) only [dressedWord,splitWord,k0,Fin.lt_def,Fin.ext_iff,if_pos,if_neg]
    ext s t
    cases s <;> cases t <;> norm_num [Matrix.single,spinP_def, visibleProjector,spinZ_def, qubitZ, finTwoEquiv,Matrix.mul_apply,
      Matrix.conjTranspose_apply,Matrix.diagonal_apply,Matrix.one_apply,
      Matrix.sub_apply,Fintype.sum_bool]
  have local_split_p2_rq {N : ℕ} (i j : Fin N) (hi : i.val = j.val + 2) (hr : j.val + 2 < N) :
      (fullSplit j) * fullD i = 0 := by
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
    have tensorOp_zero_at {N : ℕ} (w : Fin N → Local) (i : Fin N)
        (h : w i = 0) : tensorProduct w = 0 := by
      classical
      rw [tensorOp_entries]
      ext s t
      change (∏ k : Fin N, w k (s k) (t k)) = 0
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h]; rfl)
    simp only [fullD,fullSplit]
    rw [tensorOp_mul]
    let k0 : Fin N := ⟨j.val + 1, by omega⟩
    apply tensorOp_zero_at _ k0
    simp (disch := omega) only [dressedWord,splitWord,k0,Fin.lt_def,Fin.ext_iff,if_pos,if_neg]
    ext s t
    cases s <;> cases t <;> norm_num [Matrix.single,spinP_def, visibleProjector,spinZ_def, qubitZ, finTwoEquiv,Matrix.mul_apply,
      Matrix.conjTranspose_apply,Matrix.diagonal_apply,Matrix.one_apply,
      Matrix.sub_apply,Fintype.sum_bool]
  have local_split_p3_qr {N : ℕ} (i j : Fin N) (hi : i.val = j.val + 3) (hr : j.val + 2 < N) :
      fullD i * (fullSplit j) = 0 := by
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
    have tensorOp_zero_at {N : ℕ} (w : Fin N → Local) (i : Fin N)
        (h : w i = 0) : tensorProduct w = 0 := by
      classical
      rw [tensorOp_entries]
      ext s t
      change (∏ k : Fin N, w k (s k) (t k)) = 0
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h]; rfl)
    simp only [fullD,fullSplit]
    rw [tensorOp_mul]
    let k0 : Fin N := ⟨j.val + 2, by omega⟩
    apply tensorOp_zero_at _ k0
    simp (disch := omega) only [dressedWord,splitWord,k0,Fin.lt_def,Fin.ext_iff,if_pos,if_neg]
    ext s t
    cases s <;> cases t <;> norm_num [Matrix.single,spinP_def, visibleProjector,spinZ_def, qubitZ, finTwoEquiv,Matrix.mul_apply,
      Matrix.conjTranspose_apply,Matrix.diagonal_apply,Matrix.one_apply,
      Matrix.sub_apply,Fintype.sum_bool]
  have fullD_far_mixed_anticomm_reverse {N : ℕ} (i j : Fin N)
      (hij : j.val + 1 < i.val) :
      fullD i * (fullD j)ᴴ + (fullD j)ᴴ * fullD i = 0 := by
    have h := congrArg Matrix.conjTranspose (fullD_far_mixed_anticomm j i hij)
    simpa only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_zero] using h
  have triple_anticomm {α : Type} [Ring α] (A B C D : α)
      (hB : A * B + B * A = 0) (hC : A * C + C * A = 0)
      (hD : A * D + D * A = 0) :
      A * (B * C * D) + (B * C * D) * A = 0 := by
    have h1 := eq_neg_of_add_eq_zero_left hB
    have h2 := eq_neg_of_add_eq_zero_left hC
    have h3 := eq_neg_of_add_eq_zero_left hD
    have he : A * (B * C * D) = -(B * C * D * A) := by
      calc
        A * (B * C * D) = (A * B) * C * D := by noncomm_ring
        _ = (-(B * A)) * C * D := by rw [h1]
        _ = -(B * (A * C) * D) := by noncomm_ring
        _ = -(B * (-(C * A)) * D) := by rw [h2]
        _ = B * C * (A * D) := by noncomm_ring
        _ = B * C * (-(D * A)) := by rw [h3]
        _ = -(B * C * D * A) := by noncomm_ring
    rw [he]
    simp
  have fullD_after_split_anticomm {N : ℕ} (i j : Fin N)
      (hij : j.val + 3 < i.val) :
      fullD i * fullSplit j + fullSplit j * fullD i = 0 := by
    have hr : j.val + 2 < N := by omega
    let k : Fin N := ⟨j.val + 2,hr⟩
    let m : Fin N := ⟨j.val + 1,by omega⟩
    have h1 := fullD_far_mixed_anticomm_reverse i j (by omega)
    have h2 := fullD_far_mixed_anticomm_reverse i k (by dsimp [k]; omega)
    have h3 : fullD i * fullD m + fullD m * fullD i = 0 := by
      have ht := fullD_far_anticomm m i (by dsimp [m]; omega)
      simpa only [add_comm] using ht
    rw [fullSplit_eq_dressed_product j hr]
    exact triple_anticomm (fullD i) (fullD j)ᴴ (fullD k)ᴴ (fullD m) h1 h2 h3
  classical
  unfold fullQ
  rw [Finset.sum_mul,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Matrix.smul_mul,Matrix.mul_smul,← smul_add]
  congr 1
  by_cases hp : i.val + 1 = j.val
  · simp [hp,local_split_m1_qr i j hp hr]
  · rw [if_neg hp]
    by_cases hc : i.val = j.val ∨ i.val = j.val + 2
    · rw [if_pos hc]
      rcases hc with hc | hc
      · rw [local_split_p0_rq i j (by omega) hr,add_zero]
      · rw [local_split_p2_rq i j hc hr,add_zero]
    · rw [if_neg hc]
      by_cases hn : i.val = j.val + 3
      · rw [if_pos hn,local_split_p3_qr i j hn hr,zero_add]
      · rw [if_neg hn]
        have hcases : i.val + 1 < j.val ∨ i.val = j.val + 1 ∨ j.val + 3 < i.val := by omega
        rcases hcases with hh | hh | hh
        · exact fullD_before_split_anticomm i j hh
        · rw [local_split_p1_qr i j hh hr,local_split_p1_rq i j hh hr,add_zero]
        · exact fullD_after_split_anticomm i j hh

def symOp {N : ℕ} (A : FullOperator N) : FullOperator N := A + Aᴴ

def creatorNeighbourTerms {N : ℕ} (coupling : Fin N → ℝ) (j : Fin N) : FullOperator N :=
  ∑ i : Fin N, if i.val + 1 = j.val ∨ j.val + 1 = i.val
    then (coupling i : ℂ) • ((fullD j)ᴴ * fullD i) else 0

theorem fullNumber_left_creator_neighbours {N : ℕ} (coupling : Fin N → ℝ)
    (k j : Fin N) (hkj : k.val + 2 = j.val) :
    ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * creatorNeighbourTerms coupling j =
      ∑ i : Fin N, if j.val + 1 = i.val then
        (coupling i : ℂ) • (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * ((fullD j)ᴴ * fullD i)) else 0 := by
  have localOp_as_tensor {N : ℕ} (i : Fin N) :
      ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp i (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) = tensorOp (numberWord i) := by
    classical
    ext s t
    simp only [D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp, D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp,
      Matrix.submatrix_apply, Matrix.of_apply]
    apply Finset.prod_congr rfl
    intro k _
    by_cases h : k = i
    · subst k
      simp [Function.update_self, numberWord, sub_sub_cancel]
    · simp [Function.update_of_ne h, numberWord, h, Matrix.one_apply, Equiv.apply_eq_iff_eq]
  have fullNumber_neighbour_D_zero {N : ℕ} (k i : Fin N)
      (hki : k.val + 1 = i.val ∨ i.val + 1 = k.val) :
      ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * fullD i = 0 := by
    let tensorProduct {N : ℕ} (w : Fin N → Local) : FullOperator N := tensorOp w
    have tensorOp_entries {N : ℕ} (w : Fin N → Local) :
        tensorProduct w = (fun s t => ∏ i : Fin N, w i (s i) (t i)) := by
      ext s t
      simp [tensorProduct, D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp,
        Matrix.submatrix_apply]
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
    have tensorOp_zero_at {N : ℕ} (w : Fin N → Local) (i : Fin N)
        (h : w i = 0) : tensorProduct w = 0 := by
      classical
      rw [tensorOp_entries]
      ext s t
      change (∏ k : Fin N, w k (s k) (t k)) = 0
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h]; rfl)
    classical
    simp only [localOp_as_tensor]
    unfold fullD
    rw [tensorOp_mul]
    apply tensorOp_zero_at _ k
    have hw : dressedWord i k = spinP := by
      unfold dressedWord
      rcases hki with hki | hki
      · simp [hki]
      · have hp : ¬k.val + 1 = i.val := by omega
        have hl : ¬k < i := by simp only [Fin.lt_def]; omega
        have he : k ≠ i := by intro hh; subst k; omega
        simp [hp,hl,he,hki]
    simp only [numberWord,if_pos rfl,hw]
    ext s t
    cases s <;> cases t <;> norm_num [spinP_def, visibleProjector,Matrix.mul_apply,Matrix.sub_apply,
      Matrix.diagonal_apply,Matrix.one_apply,Fintype.sum_bool]
  let tensorProduct {N : ℕ} (w : Fin N → Local) : FullOperator N := tensorOp w
  have tensorOp_entries {N : ℕ} (w : Fin N → Local) :
      tensorProduct w = (fun s t => ∏ i : Fin N, w i (s i) (t i)) := by
    ext s t
    simp [tensorProduct, D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp,
      Matrix.submatrix_apply]
  have spinP_def : spinP = Matrix.diagonal (fun b => if b then (0 : ℂ) else 1) := by
    ext s t
    cases s <;> cases t <;> norm_num [visibleProjector, Matrix.diagonal, Matrix.sub_apply]
  have tensorOp_adjoint {N : ℕ} (w : Fin N → Local) :
      (tensorProduct w)ᴴ = tensorProduct (fun i => (w i)ᴴ) := by
    classical
    rw [tensorOp_entries, tensorOp_entries]
    ext s t
    change star (∏ i : Fin N, w i (t i) (s i)) = ∏ i : Fin N, star (w i (t i) (s i))
    simp
  have spinP_self_adjoint : spinPᴴ = spinP := by
    ext s t
    cases s <;> cases t <;> simp [spinP_def, visibleProjector, Matrix.conjTranspose_apply]
  have fullNumber_self_adjoint {N : ℕ} (i : Fin N) :
      (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp i (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))))ᴴ = ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp i (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) := by
    simp only [localOp_as_tensor]
    rw [tensorOp_adjoint]
    congr 1
    funext k
    simp only [numberWord]
    split_ifs <;> simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,spinP_self_adjoint]
  have fullNumber_creator_commute {N : ℕ} (k j : Fin N) (h : k ≠ j) :
      ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * (fullD j)ᴴ = (fullD j)ᴴ * ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) := by
    have hh := congrArg Matrix.conjTranspose (fullD_number_commute j k h.symm)
    simpa only [Matrix.conjTranspose_mul,fullNumber_self_adjoint] using hh
  have fullNumber_neighbour_hop_zero {N : ℕ} (k j i : Fin N)
      (hkj : k ≠ j) (hki : k.val + 1 = i.val ∨ i.val + 1 = k.val) :
      ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * ((fullD j)ᴴ * fullD i) = 0 := by
    rw [← Matrix.mul_assoc,fullNumber_creator_commute k j hkj,Matrix.mul_assoc,
      fullNumber_neighbour_D_zero k i hki,mul_zero]
  classical
  unfold creatorNeighbourTerms
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hl : i.val + 1 = j.val
  · have hn : ¬j.val + 1 = i.val := by omega
    rw [if_pos (Or.inl hl),Matrix.mul_smul,
      fullNumber_neighbour_hop_zero k j i (by intro h; subst j; omega) (Or.inl (by omega)),
      smul_zero,if_neg hn]
  · by_cases hr : j.val + 1 = i.val
    · simp [hr,Matrix.mul_smul]
    · simp [hl,hr]

theorem fullNumber_right_creator_neighbours {N : ℕ} (coupling : Fin N → ℝ)
    (k j : Fin N) (hkj : j.val + 2 = k.val) :
    ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * creatorNeighbourTerms coupling j =
      ∑ i : Fin N, if i.val + 1 = j.val then
        (coupling i : ℂ) • (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * ((fullD j)ᴴ * fullD i)) else 0 := by
  have localOp_as_tensor {N : ℕ} (i : Fin N) :
      ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp i (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) = tensorOp (numberWord i) := by
    classical
    ext s t
    simp only [D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp, D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp,
      Matrix.submatrix_apply, Matrix.of_apply]
    apply Finset.prod_congr rfl
    intro k _
    by_cases h : k = i
    · subst k
      simp [Function.update_self, numberWord, sub_sub_cancel]
    · simp [Function.update_of_ne h, numberWord, h, Matrix.one_apply, Equiv.apply_eq_iff_eq]
  have fullNumber_neighbour_D_zero {N : ℕ} (k i : Fin N)
      (hki : k.val + 1 = i.val ∨ i.val + 1 = k.val) :
      ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * fullD i = 0 := by
    let tensorProduct {N : ℕ} (w : Fin N → Local) : FullOperator N := tensorOp w
    have tensorOp_entries {N : ℕ} (w : Fin N → Local) :
        tensorProduct w = (fun s t => ∏ i : Fin N, w i (s i) (t i)) := by
      ext s t
      simp [tensorProduct, D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp,
        Matrix.submatrix_apply]
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
    have tensorOp_zero_at {N : ℕ} (w : Fin N → Local) (i : Fin N)
        (h : w i = 0) : tensorProduct w = 0 := by
      classical
      rw [tensorOp_entries]
      ext s t
      change (∏ k : Fin N, w k (s k) (t k)) = 0
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h]; rfl)
    classical
    simp only [localOp_as_tensor]
    unfold fullD
    rw [tensorOp_mul]
    apply tensorOp_zero_at _ k
    have hw : dressedWord i k = spinP := by
      unfold dressedWord
      rcases hki with hki | hki
      · simp [hki]
      · have hp : ¬k.val + 1 = i.val := by omega
        have hl : ¬k < i := by simp only [Fin.lt_def]; omega
        have he : k ≠ i := by intro hh; subst k; omega
        simp [hp,hl,he,hki]
    simp only [numberWord,if_pos rfl,hw]
    ext s t
    cases s <;> cases t <;> norm_num [spinP_def, visibleProjector,Matrix.mul_apply,Matrix.sub_apply,
      Matrix.diagonal_apply,Matrix.one_apply,Fintype.sum_bool]
  let tensorProduct {N : ℕ} (w : Fin N → Local) : FullOperator N := tensorOp w
  have tensorOp_entries {N : ℕ} (w : Fin N → Local) :
      tensorProduct w = (fun s t => ∏ i : Fin N, w i (s i) (t i)) := by
    ext s t
    simp [tensorProduct, D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp,
      Matrix.submatrix_apply]
  have spinP_def : spinP = Matrix.diagonal (fun b => if b then (0 : ℂ) else 1) := by
    ext s t
    cases s <;> cases t <;> norm_num [visibleProjector, Matrix.diagonal, Matrix.sub_apply]
  have tensorOp_adjoint {N : ℕ} (w : Fin N → Local) :
      (tensorProduct w)ᴴ = tensorProduct (fun i => (w i)ᴴ) := by
    classical
    rw [tensorOp_entries, tensorOp_entries]
    ext s t
    change star (∏ i : Fin N, w i (t i) (s i)) = ∏ i : Fin N, star (w i (t i) (s i))
    simp
  have spinP_self_adjoint : spinPᴴ = spinP := by
    ext s t
    cases s <;> cases t <;> simp [spinP_def, visibleProjector, Matrix.conjTranspose_apply]
  have fullNumber_self_adjoint {N : ℕ} (i : Fin N) :
      (((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp i (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))))ᴴ = ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp i (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) := by
    simp only [localOp_as_tensor]
    rw [tensorOp_adjoint]
    congr 1
    funext k
    simp only [numberWord]
    split_ifs <;> simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_one,spinP_self_adjoint]
  have fullNumber_creator_commute {N : ℕ} (k j : Fin N) (h : k ≠ j) :
      ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * (fullD j)ᴴ = (fullD j)ᴴ * ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) := by
    have hh := congrArg Matrix.conjTranspose (fullD_number_commute j k h.symm)
    simpa only [Matrix.conjTranspose_mul,fullNumber_self_adjoint] using hh
  have fullNumber_neighbour_hop_zero {N : ℕ} (k j i : Fin N)
      (hkj : k ≠ j) (hki : k.val + 1 = i.val ∨ i.val + 1 = k.val) :
      ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp k (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * ((fullD j)ᴴ * fullD i) = 0 := by
    rw [← Matrix.mul_assoc,fullNumber_creator_commute k j hkj,Matrix.mul_assoc,
      fullNumber_neighbour_D_zero k i hki,mul_zero]
  classical
  unfold creatorNeighbourTerms
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hr : j.val + 1 = i.val
  · have hn : ¬i.val + 1 = j.val := by omega
    rw [if_pos (Or.inr hr),Matrix.mul_smul,
      fullNumber_neighbour_hop_zero k j i (by intro h; subst j; omega) (Or.inr (by omega)),
      smul_zero,if_neg hn]
  · by_cases hl : i.val + 1 = j.val
    · simp [hl,Matrix.mul_smul]
    · simp [hl,hr]

end
end D5.S3.Quantum.SpinChains.SupersymmetricFermion.CubicProducts
