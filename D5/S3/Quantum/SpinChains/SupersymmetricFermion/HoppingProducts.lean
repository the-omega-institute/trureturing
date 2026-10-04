/- GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/HoppingProducts
   generality: I
   mirror-B: D5/B/S3/Quantum/SpinChains/SupersymmetricFermion/HoppingProducts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Explicit two-site and four-site hopping products. -/

/-
hop_dressed:
  proof_shape: content
  escape_witness: hop_dressed (form 2): Site-position cases identify the two dressed factors with the explicit hopping tensor word.
  Direct frozen dependencies: qubitZ, tensorOp, Assignment, visibleProjector.
split_at_left:
  proof_shape: content
  escape_witness: split_at_left (form 2): Local matrix products at the left cubic endpoint give the right hop and its boundary projector.
  Direct frozen dependencies: qubitZ, tensorOp, Assignment, visibleProjector.
split_at_right:
  proof_shape: content
  escape_witness: split_at_right (form 2): Local matrix products at the right cubic endpoint give the negative left hop and its outer projector.
  Direct frozen dependencies: qubitZ, tensorOp, Assignment, visibleProjector.
split_before:
  proof_shape: content
  escape_witness: split_before (form 2): The predecessor annihilation and cubic split yield the adjoint four-site hopping word.
  Direct frozen dependencies: qubitZ, tensorOp, Assignment, visibleProjector.
split_after:
  proof_shape: content
  escape_witness: split_after (form 2): The successor annihilation and cubic split yield the negative four-site hopping word.
  Direct frozen dependencies: qubitZ, tensorOp, Assignment, visibleProjector.
fullHop_PAt_commute:
  proof_shape: content
  escape_witness: fullHop_PAt_commute (form 2): The empty-site projector commutes with every disjoint local hopping factor.
  Direct frozen dependencies: tensorOp, Assignment, visibleProjector.
admission_basis: escape-witness
Direct frozen dependency keys (GID; statement_id):
tensorOp = D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp; sha256:0da7fdcc843e3d6cb83079e32e80fde7787e167c84a8fb99695fdb5e9ba7ba8e
Assignment = PredictiveThermodynamic.Physical.Assignment; sha256:186896178b3ea09d109f4546cae53a1b2c485c3990a05a1b88d8deaaae3e423f
visibleProjector = PredictiveThermodynamic.Physical.visibleProjector; sha256:43e1e2af782427fc79461c7b3ade37c1b221e7ce50f9bb7165571c1bcbaa1d68
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

namespace D5.S3.Quantum.SpinChains.SupersymmetricFermion.HoppingProducts
noncomputable section
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.DressedOperators

def fullPAt (N j : ℕ) : FullOperator N :=
  tensorOp (fun k : Fin N => if k.val = j then spinP else 1)

def fullLeftP (N j : ℕ) : FullOperator N :=
  tensorOp (fun k : Fin N => if k.val + 1 = j then spinP else 1)

def hopWord {N : ℕ} (j : ℕ) (k : Fin N) : Local :=
  if k.val + 1 = j then spinP else if k.val = j then (Matrix.single false true (1 : ℂ))ᴴ else
  if k.val = j+1 then (Matrix.single false true (1 : ℂ)) else if k.val = j+2 then spinP else 1

def fullHop (N j : ℕ) : FullOperator N :=
  if j+1 < N then tensorOp (hopWord j) else 0

def fourHopWord {N : ℕ} (j : ℕ) (k : Fin N) : Local :=
  if k.val + 1 = j then spinP else if k.val = j then (Matrix.single false true (1 : ℂ))ᴴ else
  if k.val = j+1 then (Matrix.single false true (1 : ℂ)) else if k.val = j+2 then (Matrix.single false true (1 : ℂ))ᴴ else
  if k.val = j+3 then (Matrix.single false true (1 : ℂ)) else if k.val = j+4 then spinP else 1

def fullFourHop (N j : ℕ) : FullOperator N :=
  if j+3 < N then tensorOp (fourHopWord j) else 0

theorem hop_dressed {N : ℕ} (j : Fin N) (hr : j.val + 1 < N) :
    fullHop N j.val = (fullD j)ᴴ * fullD (⟨j.val+1,by omega⟩ : Fin N) := by
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
  simp only [fullHop,if_pos hr,fullD]
  rw [tensorOp_adjoint,tensorOp_mul]
  apply congrArg (fun w : Fin N → Local => tensorProduct w)
  funext k
  have hcases : k.val + 2 < j.val ∨ k.val + 2 = j.val ∨ k.val + 1 = j.val ∨
      k.val = j.val ∨ k.val = j.val + 1 ∨ k.val = j.val + 2 ∨
      k.val = j.val + 3 ∨ k.val = j.val + 4 ∨ j.val + 4 < k.val := by omega
  rcases hcases with hk | hk | hk | hk | hk | hk | hk | hk | hk
  all_goals simp (disch := omega) only [dressedWord,splitWord,hopWord,fourHopWord,
    Fin.lt_def,Fin.ext_iff,if_pos,if_neg,neg_one_smul,one_smul]
  all_goals ext u v
  all_goals cases u <;> cases v
  all_goals norm_num [Matrix.single,spinZ_def, qubitZ, finTwoEquiv,spinP_def, visibleProjector,Matrix.mul_apply,
    Matrix.conjTranspose_apply,Matrix.diagonal_apply,Matrix.one_apply,
    Matrix.neg_apply,Matrix.sub_apply,Fintype.sum_bool]

theorem split_at_left {N : ℕ} (j : Fin N) (hr : j.val + 2 < N) :
    fullD j * fullSplit j = (fullHop N (j.val+1))ᴴ * fullLeftP N j.val := by
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
  have hh : j.val+1+1<N := by omega
  simp only [fullD,fullSplit,fullHop,if_pos hh,fullLeftP]
  rw [tensorOp_mul,tensorOp_adjoint,tensorOp_mul]
  congr 1
  funext k
  have hcases : k.val + 2 < j.val ∨ k.val + 2 = j.val ∨ k.val + 1 = j.val ∨
      k.val = j.val ∨ k.val = j.val + 1 ∨ k.val = j.val + 2 ∨
      k.val = j.val + 3 ∨ k.val = j.val + 4 ∨ j.val + 4 < k.val := by omega
  rcases hcases with hk | hk | hk | hk | hk | hk | hk | hk | hk
  all_goals simp (disch := omega) only [dressedWord,splitWord,hopWord,fourHopWord,
    Fin.lt_def,Fin.ext_iff,if_pos,if_neg,neg_one_smul,one_smul]
  all_goals ext u v
  all_goals cases u <;> cases v
  all_goals norm_num [Matrix.single,spinZ_def, qubitZ, finTwoEquiv,spinP_def, visibleProjector,Matrix.mul_apply,
    Matrix.conjTranspose_apply,Matrix.diagonal_apply,Matrix.one_apply,
    Matrix.neg_apply,Matrix.sub_apply,Fintype.sum_bool]

theorem split_at_right {N : ℕ} (j : Fin N) (hr : j.val + 2 < N) :
    fullD (⟨j.val+2,by omega⟩ : Fin N) * fullSplit j = -(fullHop N j.val * fullPAt N (j.val+3)) := by
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
  have tensorOp_scalar {N : ℕ} (w : Fin N → Local) (k : Fin N) (z : ℂ) :
      tensorProduct (fun i => (if i = k then z else 1) • w i) = z • tensorProduct w := by
    classical
    rw [tensorOp_entries, tensorOp_entries]
    ext s t
    change (∏ i : Fin N, (if i = k then z else 1) * w i (s i) (t i)) = z * ∏ i : Fin N, w i (s i) (t i)
    rw [Finset.prod_mul_distrib]
    simp
  classical
  have hh : j.val+1<N := by omega
  simp only [fullD,fullSplit,fullHop,if_pos hh,fullPAt]
  rw [tensorOp_mul,tensorOp_mul]
  have he : tensorProduct (fun k : Fin N => (if k.val = j.val then (-1 : ℂ) else 1) •
      (hopWord j.val k * (if k.val = j.val+3 then spinP else 1))) =
      -(tensorProduct (fun k : Fin N => hopWord j.val k * (if k.val = j.val+3 then spinP else 1))) := by
    simpa only [Fin.ext_iff,neg_one_smul] using
      (tensorOp_scalar (fun k : Fin N => hopWord j.val k *
        (if k.val = j.val+3 then spinP else 1)) j (-1))

  rw [← he]
  congr 1
  funext k
  have hcases : k.val + 2 < j.val ∨ k.val + 2 = j.val ∨ k.val + 1 = j.val ∨
      k.val = j.val ∨ k.val = j.val + 1 ∨ k.val = j.val + 2 ∨
      k.val = j.val + 3 ∨ k.val = j.val + 4 ∨ j.val + 4 < k.val := by omega
  rcases hcases with hk | hk | hk | hk | hk | hk | hk | hk | hk
  all_goals simp (disch := omega) only [dressedWord,splitWord,hopWord,fourHopWord,
    Fin.lt_def,Fin.ext_iff,if_pos,if_neg,neg_one_smul,one_smul]
  all_goals ext u v
  all_goals cases u <;> cases v
  all_goals norm_num [Matrix.single,spinZ_def, qubitZ, finTwoEquiv,spinP_def, visibleProjector,Matrix.mul_apply,
    Matrix.conjTranspose_apply,Matrix.diagonal_apply,Matrix.one_apply,
    Matrix.neg_apply,Matrix.sub_apply,Fintype.sum_bool]

theorem split_before {N : ℕ} (j : Fin N) (hr : j.val + 2 < N) (hl : 0 < j.val) :
    fullSplit j * fullD (⟨j.val-1,by omega⟩ : Fin N) = (fullFourHop N (j.val-1))ᴴ := by
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
  have hh : j.val-1+3<N := by omega
  simp only [fullD,fullSplit,fullFourHop,if_pos hh]
  rw [tensorOp_mul,tensorOp_adjoint]
  congr 1
  funext k
  have hcases : k.val + 2 < j.val ∨ k.val + 2 = j.val ∨ k.val + 1 = j.val ∨
      k.val = j.val ∨ k.val = j.val + 1 ∨ k.val = j.val + 2 ∨
      k.val = j.val + 3 ∨ k.val = j.val + 4 ∨ j.val + 4 < k.val := by omega
  rcases hcases with hk | hk | hk | hk | hk | hk | hk | hk | hk
  all_goals simp (disch := omega) only [dressedWord,splitWord,hopWord,fourHopWord,
    Fin.lt_def,Fin.ext_iff,if_pos,if_neg,neg_one_smul,one_smul]
  all_goals ext u v
  all_goals cases u <;> cases v
  all_goals norm_num [Matrix.single,spinZ_def, qubitZ, finTwoEquiv,spinP_def, visibleProjector,Matrix.mul_apply,
    Matrix.conjTranspose_apply,Matrix.diagonal_apply,Matrix.one_apply,
    Matrix.neg_apply,Matrix.sub_apply,Fintype.sum_bool]

theorem split_after {N : ℕ} (j : Fin N) (hr : j.val + 3 < N) :
    fullSplit j * fullD (⟨j.val+3,hr⟩ : Fin N) = -(fullFourHop N j.val) := by
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
  have tensorOp_scalar {N : ℕ} (w : Fin N → Local) (k : Fin N) (z : ℂ) :
      tensorProduct (fun i => (if i = k then z else 1) • w i) = z • tensorProduct w := by
    classical
    rw [tensorOp_entries, tensorOp_entries]
    ext s t
    change (∏ i : Fin N, (if i = k then z else 1) * w i (s i) (t i)) = z * ∏ i : Fin N, w i (s i) (t i)
    rw [Finset.prod_mul_distrib]
    simp
  classical
  simp only [fullD,fullSplit,fullFourHop,if_pos hr]
  rw [tensorOp_mul]
  have he : tensorProduct (fun k : Fin N => (if k.val = j.val+1 then (-1 : ℂ) else 1) • fourHopWord j.val k) =
      -tensorProduct (fourHopWord j.val) := by
    let m : Fin N := ⟨j.val+1,by omega⟩
    simpa only [m,Fin.ext_iff,neg_one_smul] using
      (tensorOp_scalar (fourHopWord j.val) m (-1))

  rw [← he]
  congr 1
  funext k
  have hcases : k.val + 2 < j.val ∨ k.val + 2 = j.val ∨ k.val + 1 = j.val ∨
      k.val = j.val ∨ k.val = j.val + 1 ∨ k.val = j.val + 2 ∨
      k.val = j.val + 3 ∨ k.val = j.val + 4 ∨ j.val + 4 < k.val := by omega
  rcases hcases with hk | hk | hk | hk | hk | hk | hk | hk | hk
  all_goals simp (disch := omega) only [dressedWord,splitWord,hopWord,fourHopWord,
    Fin.lt_def,Fin.ext_iff,if_pos,if_neg,neg_one_smul,one_smul]
  all_goals ext u v
  all_goals cases u <;> cases v
  all_goals norm_num [Matrix.single,spinZ_def, qubitZ, finTwoEquiv,spinP_def, visibleProjector,Matrix.mul_apply,
    Matrix.conjTranspose_apply,Matrix.diagonal_apply,Matrix.one_apply,
    Matrix.neg_apply,Matrix.sub_apply,Fintype.sum_bool]

theorem fullHop_PAt_commute (N h k : ℕ) (hk0 : k ≠ h) (hk1 : k ≠ h+1) :
    fullHop N h * fullPAt N k = fullPAt N k * fullHop N h := by
  let tensorProduct {N : ℕ} (w : Fin N → Local) : FullOperator N := tensorOp w
  have tensorOp_entries {N : ℕ} (w : Fin N → Local) :
      tensorProduct w = (fun s t => ∏ i : Fin N, w i (s i) (t i)) := by
    ext s t
    simp [tensorProduct, D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp,
      Matrix.submatrix_apply]
  have tensorOp_mul {N : ℕ} (u v : Fin N → Local) :
      tensorProduct u * tensorProduct v = tensorProduct (fun i => u i * v i) := by
    classical
    rw [tensorOp_entries, tensorOp_entries, tensorOp_entries]
    ext s t
    change (∑ x : Assignment N, (∏ i : Fin N, u i (s i) (x i)) * (∏ i : Fin N, v i (x i) (t i))) =
      ∏ i : Fin N, ∑ b : Bool, u i (s i) b * v i b (t i)
    simp_rw [← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun i b => u i (s i) b * v i b (t i))).symm
  classical
  by_cases hr : h+1<N
  · simp only [fullHop,if_pos hr,fullPAt]
    rw [tensorOp_mul,tensorOp_mul]
    congr 1
    funext i
    by_cases hi : i.val=k
    · have hd : hopWord h i ∈ [1,spinP] := by
        unfold hopWord
        split_ifs <;> simp_all
      simp only [if_pos hi]
      simp at hd
      rcases hd with hd | hd <;> rw [hd] <;> simp
    · simp [hi]
  · simp [fullHop,hr]

def fullOccupationAt (N j : ℕ) : FullOperator N := 1 - fullPAt N j

end
end D5.S3.Quantum.SpinChains.SupersymmetricFermion.HoppingProducts
