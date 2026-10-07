/- GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/DressedOperators
   generality: I
   mirror-B: D5/B/S3/Quantum/SpinChains/SupersymmetricFermion/DressedOperators
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Nearest-neighbor exclusion determines dressed-fermion products. -/

/-
fullD_far_mixed_anticomm:
  proof_shape: content
  escape_witness: fullD_far_mixed_anticomm (form 2): Spatial cases for disjoint and shared neighbour projectors preserve the fermionic sign reversal.
  Direct frozen dependencies: qubitZ, tensorOp, Assignment, visibleProjector.
fullD_far_anticomm:
  proof_shape: content
  escape_witness: fullD_far_anticomm (form 2): The dressed tensor words give opposite products at separated annihilation sites.
  Direct frozen dependencies: qubitZ, tensorOp, Assignment, visibleProjector.
fullD_CAR:
  proof_shape: content
  escape_witness: fullD_CAR (form 2): Occupied and empty local products leave precisely the two empty-neighbour projectors.
  Direct frozen dependencies: qubitZ, tensorOp, Assignment, visibleProjector.
fullD_before_split_anticomm:
  proof_shape: content
  escape_witness: fullD_before_split_anticomm (form 2): Position cases for the annihilator relative to the cubic split give the anticommuting signs.
  Direct frozen dependencies: qubitZ, tensorOp, Assignment, visibleProjector.
fullD_number_same:
  proof_shape: content
  escape_witness: fullD_number_same (form 2): The annihilator absorbs the source occupation and has zero occupied target.
  Direct frozen dependencies: qubitZ, tensorOp, Assignment, visibleProjector.
fullD_number_commute:
  proof_shape: content
  escape_witness: fullD_number_commute (form 2): Site-position cases verify commutation with each distinct occupation operator.
  Direct frozen dependencies: qubitZ, tensorOp, Assignment, visibleProjector.
admission_basis: escape-witness
Direct frozen dependency keys (GID; statement_id):
qubitZ = D5.S3.Quantum.FiniteDimensional.qubitZ; sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c
tensorOp = D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp; sha256:0da7fdcc843e3d6cb83079e32e80fde7787e167c84a8fb99695fdb5e9ba7ba8e
Assignment = PredictiveThermodynamic.Physical.Assignment; sha256:186896178b3ea09d109f4546cae53a1b2c485c3990a05a1b88d8deaaae3e423f
visibleProjector = PredictiveThermodynamic.Physical.visibleProjector; sha256:43e1e2af782427fc79461c7b3ade37c1b221e7ce50f9bb7165571c1bcbaa1d68
Chain dependencies: D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner; freeze in topological import order.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner

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

namespace D5.S3.Quantum.SpinChains.SupersymmetricFermion.DressedOperators
noncomputable section
open D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner

def dressedWord {N : ℕ} (j i : Fin N) : Local :=
  if i.val + 1 = j.val then spinP else if i < j then spinZ else
  if i = j then (Matrix.single false true (1 : ℂ)) else if i.val = j.val + 1 then spinP else 1

def fullD {N : ℕ} (j : Fin N) : FullOperator N := tensorOp (dressedWord j)

theorem fullD_far_mixed_anticomm {N : ℕ} (i j : Fin N)
    (hij : i.val + 1 < j.val) :
    fullD i * (fullD j)ᴴ + (fullD j)ᴴ * fullD i = 0 := by
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
  have tensorOp_scalar {N : ℕ} (w : Fin N → Local) (k : Fin N) (z : ℂ) :
      tensorProduct (fun i => (if i = k then z else 1) • w i) = z • tensorProduct w := by
    classical
    rw [tensorOp_entries, tensorOp_entries]
    ext s t
    change (∏ i : Fin N, (if i = k then z else 1) * w i (s i) (t i)) = z * ∏ i : Fin N, w i (s i) (t i)
    rw [Finset.prod_mul_distrib]
    simp
  have spinA_spinZ : (Matrix.single false true (1 : ℂ)) * spinZ = - (spinZ * (Matrix.single false true (1 : ℂ))) := by
    ext s t
    cases s <;> cases t <;> norm_num [Matrix.single, spinZ_def, qubitZ, finTwoEquiv, Matrix.mul_apply,
      Matrix.diagonal_apply, Fintype.sum_bool]
  have spinZ_self_adjoint : spinZᴴ = spinZ := by
    ext s t
    cases s <;> cases t <;> simp [spinZ_def, qubitZ, finTwoEquiv, Matrix.conjTranspose_apply]
  have spinP_self_adjoint : spinPᴴ = spinP := by
    ext s t
    cases s <;> cases t <;> simp [spinP_def, visibleProjector, Matrix.conjTranspose_apply]
  classical
  have hlt : i < j := by simpa using (show i.val < j.val by omega)
  have hw : (fun k => dressedWord i k * (dressedWord j k)ᴴ) =
      (fun k => (if k = i then (-1 : ℂ) else 1) •
        ((dressedWord j k)ᴴ * dressedWord i k)) := by
    funext k
    by_cases hki : k = i
    · subst k
      have hne : ¬i.val + 1 = j.val := by omega
      have hself : ¬i.val + 1 = i.val := by omega
      simp only [dressedWord, hne, hself, ite_false, lt_self_iff_false,
        ite_true, hlt, spinZ_self_adjoint, neg_one_smul]
      exact spinA_spinZ
    · have hlocal : ∀ (u v : Local), u ∈ [1, spinZ, spinP] →
          v ∈ [1, spinZ, spinP] → u * v = v * u := by
        intro u v hu hv
        simp at hu hv
        rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
          ext s t <;> cases s <;> cases t <;>
          norm_num [spinZ_def, qubitZ, finTwoEquiv, spinP_def, visibleProjector, Matrix.mul_apply, Matrix.diagonal_apply,
            Matrix.one_apply, Fintype.sum_bool]
      by_cases hkj : k = j
      · subst k
        have h1 : ¬j.val + 1 = i.val := by omega
        have h2 : ¬j < i := by simpa using (show ¬j.val < i.val by omega)
        have h3 : ¬j.val = i.val + 1 := by omega
        have h4 : ¬j.val + 1 = j.val := by omega
        simp [dressedWord, h1, h2, h3, h4, hki]
      · have hiDiag : dressedWord i k ∈ [1, spinZ, spinP] := by
          unfold dressedWord
          split_ifs <;> simp_all
        have hjDiag : (dressedWord j k)ᴴ ∈ [1, spinZ, spinP] := by
          unfold dressedWord
          split_ifs <;> simp_all [spinP_self_adjoint, spinZ_self_adjoint]
        simp only [if_neg hki, one_smul]
        exact hlocal _ _ hiDiag hjDiag
  unfold fullD
  rw [tensorOp_adjoint, tensorOp_mul, tensorOp_mul, hw, tensorOp_scalar]
  simp

theorem fullD_far_anticomm {N : ℕ} (i j : Fin N)
    (hij : i.val + 1 < j.val) :
    fullD i * fullD j + fullD j * fullD i = 0 := by
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
  have spinA_spinZ : (Matrix.single false true (1 : ℂ)) * spinZ = - (spinZ * (Matrix.single false true (1 : ℂ))) := by
    ext s t
    cases s <;> cases t <;> norm_num [Matrix.single, spinZ_def, qubitZ, finTwoEquiv, Matrix.mul_apply,
      Matrix.diagonal_apply, Fintype.sum_bool]
  have spinZ_self_adjoint : spinZᴴ = spinZ := by
    ext s t
    cases s <;> cases t <;> simp [spinZ_def, qubitZ, finTwoEquiv, Matrix.conjTranspose_apply]
  have spinP_self_adjoint : spinPᴴ = spinP := by
    ext s t
    cases s <;> cases t <;> simp [spinP_def, visibleProjector, Matrix.conjTranspose_apply]
  classical
  have hlt : i < j := by simpa using (show i.val < j.val by omega)
  have hw : (fun k => dressedWord i k * dressedWord j k) =
      (fun k => (if k = i then (-1 : ℂ) else 1) •
        (dressedWord j k * dressedWord i k)) := by
    funext k
    by_cases hki : k = i
    · subst k
      have hne : ¬i.val + 1 = j.val := by omega
      have hself : ¬i.val + 1 = i.val := by omega
      simp only [dressedWord, hne, hself, ite_false, lt_self_iff_false,
        ite_true, hlt, spinZ_self_adjoint, neg_one_smul]
      exact spinA_spinZ
    · have hlocal : ∀ (u v : Local), u ∈ [1, spinZ, spinP] →
          v ∈ [1, spinZ, spinP] → u * v = v * u := by
        intro u v hu hv
        simp at hu hv
        rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
          ext s t <;> cases s <;> cases t <;>
          norm_num [spinZ_def, qubitZ, finTwoEquiv, spinP_def, visibleProjector, Matrix.mul_apply, Matrix.diagonal_apply,
            Matrix.one_apply, Fintype.sum_bool]
      by_cases hkj : k = j
      · subst k
        have h1 : ¬j.val + 1 = i.val := by omega
        have h2 : ¬j < i := by simpa using (show ¬j.val < i.val by omega)
        have h3 : ¬j.val = i.val + 1 := by omega
        have h4 : ¬j.val + 1 = j.val := by omega
        simp [dressedWord, h1, h2, h3, h4, hki]
      · have hiDiag : dressedWord i k ∈ [1, spinZ, spinP] := by
          unfold dressedWord
          split_ifs <;> simp_all
        have hjDiag : dressedWord j k ∈ [1, spinZ, spinP] := by
          unfold dressedWord
          split_ifs <;> simp_all [spinP_self_adjoint, spinZ_self_adjoint]
        simp only [if_neg hki, one_smul]
        exact hlocal _ _ hiDiag hjDiag
  unfold fullD
  rw [tensorOp_mul, tensorOp_mul, hw, tensorOp_scalar]
  simp

def neighbourPWord {N : ℕ} (j k : Fin N) : Local :=
  if k.val + 1 = j.val ∨ k.val = j.val + 1 then spinP else 1

theorem fullD_CAR {N : ℕ} (i : Fin N) :
    fullD i * (fullD i)ᴴ + (fullD i)ᴴ * fullD i = tensorOp (neighbourPWord i) := by
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
  have tensorOp_update {N : ℕ} (w : Fin N → Local) (i : Fin N) (m : Local)
      (s t : Assignment N) :
      tensorProduct (Function.update w i m) s t =
        m (s i) (t i) * ∏ k ∈ Finset.univ.erase i, w k (s k) (t k) := by
    classical
    simp only [tensorOp_entries]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    rw [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro k hk
    rw [Function.update_of_ne (Finset.mem_erase.mp hk).1]
  have tensorOp_update_add {N : ℕ} (w : Fin N → Local) (i : Fin N) (u v : Local) :
      tensorProduct (Function.update w i (u + v)) =
        tensorProduct (Function.update w i u) + tensorProduct (Function.update w i v) := by
    classical
    ext s t
    simp only [tensorOp_update, Matrix.add_apply]
    ring
  have spinZ_self_adjoint : spinZᴴ = spinZ := by
    ext s t
    cases s <;> cases t <;> simp [spinZ_def, qubitZ, finTwoEquiv, Matrix.conjTranspose_apply]
  have spinZ_square : spinZ * spinZ = (1 : Local) := by
    ext s t
    cases s <;> cases t <;> norm_num [spinZ_def, qubitZ, finTwoEquiv, Matrix.mul_apply,
      Matrix.diagonal_apply, Matrix.one_apply, Fintype.sum_bool]
  have spinA_CAR : (Matrix.single false true (1 : ℂ)) * (Matrix.single false true (1 : ℂ))ᴴ + (Matrix.single false true (1 : ℂ))ᴴ * (Matrix.single false true (1 : ℂ)) = (1 : Local) := by
    ext s t
    cases s <;> cases t <;> norm_num [Matrix.single, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply, Fintype.sum_bool]
  have spinP_self_adjoint : spinPᴴ = spinP := by
    ext s t
    cases s <;> cases t <;> simp [spinP_def, visibleProjector, Matrix.conjTranspose_apply]
  have spinP_square : spinP * spinP = spinP := by
    ext s t
    cases s <;> cases t <;> norm_num [spinP_def, visibleProjector, Matrix.mul_apply,
      Matrix.diagonal_apply, Fintype.sum_bool]
  classical
  have h1 : (fun k => dressedWord i k * (dressedWord i k)ᴴ) =
      Function.update (neighbourPWord i) i ((Matrix.single false true (1 : ℂ)) * (Matrix.single false true (1 : ℂ))ᴴ) := by
    funext k
    by_cases heq : k = i
    · subst k
      have hnot : ¬i.val + 1 = i.val := by omega
      simp [dressedWord, hnot]
    · by_cases hprev : k.val + 1 = i.val
      · simp [dressedWord, neighbourPWord, hprev, heq,
          spinP_self_adjoint, spinP_square]
      · by_cases hlt : k < i
        · have hnxt : ¬k.val = i.val + 1 := by simp only [Fin.lt_def] at hlt; omega
          simp [dressedWord, neighbourPWord, hprev, hlt, hnxt, heq,
            spinZ_self_adjoint, spinZ_square]
        · by_cases hnxt : k.val = i.val + 1
          · simp [dressedWord, neighbourPWord, hprev, hlt, hnxt, heq,
              spinP_self_adjoint, spinP_square]
          · simp [dressedWord, neighbourPWord, hprev, hlt, hnxt, heq]
  have h2 : (fun k => (dressedWord i k)ᴴ * dressedWord i k) =
      Function.update (neighbourPWord i) i ((Matrix.single false true (1 : ℂ))ᴴ * (Matrix.single false true (1 : ℂ))) := by
    funext k
    by_cases heq : k = i
    · subst k
      have hnot : ¬i.val + 1 = i.val := by omega
      simp [dressedWord, hnot]
    · by_cases hprev : k.val + 1 = i.val
      · simp [dressedWord, neighbourPWord, hprev, heq,
          spinP_self_adjoint, spinP_square]
      · by_cases hlt : k < i
        · have hnxt : ¬k.val = i.val + 1 := by simp only [Fin.lt_def] at hlt; omega
          simp [dressedWord, neighbourPWord, hprev, hlt, hnxt, heq,
            spinZ_self_adjoint, spinZ_square]
        · by_cases hnxt : k.val = i.val + 1
          · simp [dressedWord, neighbourPWord, hprev, hlt, hnxt, heq,
              spinP_self_adjoint, spinP_square]
          · simp [dressedWord, neighbourPWord, hprev, hlt, hnxt, heq]
  unfold fullD
  rw [tensorOp_adjoint, tensorOp_mul, tensorOp_mul, h1, h2,
    ← tensorOp_update_add, spinA_CAR]
  have hw : Function.update (neighbourPWord i) i (1 : Local) = neighbourPWord i := by
    apply Function.update_eq_self_iff.mpr
    simp [neighbourPWord]
  rw [hw]

def splitWord {N : ℕ} (j k : Fin N) : Local :=
  if k.val + 1 = j.val then spinP else if k < j then spinZ else
  if k = j then (Matrix.single false true (1 : ℂ))ᴴ else if k.val = j.val + 1 then (Matrix.single false true (1 : ℂ)) else
  if k.val = j.val + 2 then (Matrix.single false true (1 : ℂ))ᴴ else if k.val = j.val + 3 then spinP else 1

def fullSplit {N : ℕ} (j : Fin N) : FullOperator N := tensorOp (splitWord j)

theorem fullD_before_split_anticomm {N : ℕ} (i j : Fin N)
    (hij : i.val + 1 < j.val) :
    fullD i * fullSplit j + fullSplit j * fullD i = 0 := by
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
  have spinA_spinZ : (Matrix.single false true (1 : ℂ)) * spinZ = - (spinZ * (Matrix.single false true (1 : ℂ))) := by
    ext s t
    cases s <;> cases t <;> norm_num [Matrix.single, spinZ_def, qubitZ, finTwoEquiv, Matrix.mul_apply,
      Matrix.diagonal_apply, Fintype.sum_bool]
  classical
  have hlt : i < j := by simp only [Fin.lt_def]; omega
  have hwi : dressedWord i i = (Matrix.single false true (1 : ℂ)) := by simp [dressedWord]
  have htj : splitWord j i = spinZ := by
    have hne : ¬i.val + 1 = j.val := by omega
    simp [splitWord, hne, hlt]
  have hw : (fun k => dressedWord i k * splitWord j k) =
      (fun k => (if k = i then (-1 : ℂ) else 1) •
        (splitWord j k * dressedWord i k)) := by
    funext k
    by_cases hki : k = i
    · subst k
      simp only [hwi, htj, ite_true, neg_one_smul]
      exact spinA_spinZ
    · simp only [if_neg hki, one_smul]
      by_cases hkj : k.val ≥ j.val
      · have hd : dressedWord i k = 1 := by
          have hp : ¬k.val + 1 = i.val := by omega
          have hl : ¬k < i := by simp only [Fin.lt_def]; omega
          have hn : ¬k.val = i.val + 1 := by omega
          simp [dressedWord, hp, hl, hki, hn]
        rw [hd, one_mul, mul_one]
      · have ht : splitWord j k ∈ [spinP,spinZ] := by
          have hl : k < j := by simp only [Fin.lt_def]; omega
          unfold splitWord
          split_ifs <;> simp_all
        have hd : dressedWord i k ∈ [1,spinP,spinZ] := by
          unfold dressedWord
          split_ifs <;> simp_all
        simp at ht hd
        rcases ht with ht | ht <;> rcases hd with hd | hd | hd <;>
          rw [ht,hd] <;> ext s t <;> cases s <;> cases t <;>
          norm_num [spinZ_def, qubitZ, finTwoEquiv, spinP_def, visibleProjector, Matrix.mul_apply, Matrix.diagonal_apply,
            Matrix.one_apply, Fintype.sum_bool]
  unfold fullD fullSplit
  rw [tensorOp_mul, tensorOp_mul, hw, tensorOp_scalar]
  simp

def numberWord {N : ℕ} (i k : Fin N) : Local := if k = i then 1 - spinP else 1

theorem fullD_number_same {N : ℕ} (i : Fin N) :
    fullD i * ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp i (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) = fullD i ∧ ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp i (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * fullD i = 0 := by
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
  have spinA_number : (Matrix.single false true (1 : ℂ)) * (1 - spinP) = (Matrix.single false true (1 : ℂ)) ∧ (1 - spinP) * (Matrix.single false true (1 : ℂ)) = 0 := by
    constructor <;> ext s t <;> cases s <;> cases t <;>
      norm_num [Matrix.single,spinP_def, visibleProjector,Matrix.mul_apply,Matrix.diagonal_apply,
        Matrix.one_apply,Matrix.sub_apply,Fintype.sum_bool]
  classical
  constructor
  · rw [localOp_as_tensor]; unfold fullD
    rw [tensorOp_mul]
    congr 1
    funext k
    by_cases hk : k = i
    · subst k
      simpa [numberWord, dressedWord] using spinA_number.1
    · simp [numberWord, hk]
  · rw [localOp_as_tensor]; unfold fullD
    rw [tensorOp_mul]
    apply tensorOp_zero_at _ i
    simpa [numberWord,dressedWord] using spinA_number.2

theorem fullD_number_commute {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    fullD i * ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp j (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) = ((D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.localOp j (visibleProjector.submatrix finTwoEquiv finTwoEquiv)).submatrix (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k)) (fun (s : Fin N → Bool) k => finTwoEquiv.symm (s k))) * fullD i := by
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
  classical
  simp only [localOp_as_tensor]
  unfold fullD
  rw [tensorOp_mul, tensorOp_mul]
  congr 1
  funext k
  by_cases hk : k = j
  · subst k
    simp only [numberWord, ite_true]
    have hd : dressedWord i j ∈ [1,spinP,spinZ] := by
      unfold dressedWord
      split_ifs <;> simp_all
    simp at hd
    rcases hd with hd | hd | hd <;> rw [hd] <;>
      ext s t <;> cases s <;> cases t <;>
      norm_num [spinP_def, visibleProjector,spinZ_def, qubitZ, finTwoEquiv,Matrix.mul_apply,Matrix.diagonal_apply,
        Matrix.one_apply,Matrix.sub_apply,Fintype.sum_bool]
  · simp [numberWord, hk]

end
end D5.S3.Quantum.SpinChains.SupersymmetricFermion.DressedOperators
