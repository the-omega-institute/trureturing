/- GID: D5/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner
   generality: I
   mirror-B: D5/B/S3/Quantum/SpinChains/SupersymmetricFermion/JordanWigner
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Boolean Jordan-Wigner fermions obey canonical anticommutation relations. -/

/-
fullC_anticomm_of_lt:
  proof_shape: content
  escape_witness: fullC_anticomm_of_lt (form 2): Occupation factors between distinct sites contribute one Jordan-Wigner sign reversal.
  Direct frozen dependencies: qubitZ, tensorOp, Assignment.
fullC_CAR:
  proof_shape: content
  escape_witness: fullC_CAR (form 2): The annihilation/creation products partition the occupied and empty basis configurations.
  Direct frozen dependencies: qubitZ, tensorOp, Assignment.
fullC_mixed_anticomm_of_lt:
  proof_shape: content
  escape_witness: fullC_mixed_anticomm_of_lt (form 2): The local creation factor crosses exactly one parity factor at separated sites.
  Direct frozen dependencies: qubitZ, tensorOp, Assignment.
admission_basis: escape-witness
Direct frozen dependency keys (GID; statement_id):
qubitZ = D5.S3.Quantum.FiniteDimensional.qubitZ; sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c
tensorOp = D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp; sha256:0da7fdcc843e3d6cb83079e32e80fde7787e167c84a8fb99695fdb5e9ba7ba8e
Assignment = PredictiveThermodynamic.Physical.Assignment; sha256:186896178b3ea09d109f4546cae53a1b2c485c3990a05a1b88d8deaaae3e423f
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
import D5.S3.Quantum.Dynamics.ClauseHamiltonian

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

namespace D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner
noncomputable section

abbrev Local := Matrix Bool Bool ℂ

abbrev FullOperator (N : ℕ) := Matrix (Assignment N) (Assignment N) ℂ

def fermionWord {N : ℕ} (j : Fin N) (i : Fin N) : Local :=
  if i < j then spinZ else if i = j then (Matrix.single false true (1 : ℂ)) else 1

def fullC {N : ℕ} (j : Fin N) : FullOperator N := tensorOp (fermionWord j)

def prefixCount {N : ℕ} (t : Assignment N) (j : Fin N) : ℕ :=
  (Finset.univ.filter fun i : Fin N => i < j ∧ t i = true).card

theorem fullC_anticomm_of_lt {N : ℕ} (i j : Fin N) (hij : i < j) :
    fullC i * fullC j + fullC j * fullC i = 0 := by
  let tensorProduct {N : ℕ} (w : Fin N → Local) : FullOperator N := tensorOp w
  have tensorOp_entries {N : ℕ} (w : Fin N → Local) :
      tensorProduct w = (fun s t => ∏ i : Fin N, w i (s i) (t i)) := by
    ext s t
    simp [tensorProduct, D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp,
      Matrix.submatrix_apply]
  have spinZ_def : spinZ = Matrix.diagonal (fun b => if b then (-1 : ℂ) else 1) := by
    ext s t
    cases s <;> cases t <;> rfl
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
  have hw : (fun k => fermionWord i k * fermionWord j k) =
      (fun k => (if k = i then (-1 : ℂ) else 1) •
        (fermionWord j k * fermionWord i k)) := by
    funext k
    by_cases hki : k = i
    · subst k
      simp only [fermionWord, lt_self_iff_false, ite_false, ite_true, hij,
        neg_one_smul]
      exact spinA_spinZ
    · by_cases hkj : k = j
      · subst k
        have hji : ¬j < i := not_lt_of_ge (le_of_lt hij)
        have hne : j ≠ i := ne_of_gt hij
        simp [fermionWord, hji, hne]
      · by_cases hlt : k < i
        · have hlj : k < j := lt_trans hlt hij
          simp [fermionWord, hlt, hlj, hki]
        · by_cases hlj : k < j
          · simp [fermionWord, hlt, hlj, hki, hkj]
          · simp [fermionWord, hlt, hlj, hki, hkj]
  unfold fullC
  rw [tensorOp_mul, tensorOp_mul, hw, tensorOp_scalar]
  simp

theorem fullC_CAR {N : ℕ} (i : Fin N) :
    fullC i * (fullC i)ᴴ + (fullC i)ᴴ * fullC i = (1 : FullOperator N) := by
  let tensorProduct {N : ℕ} (w : Fin N → Local) : FullOperator N := tensorOp w
  have tensorOp_entries {N : ℕ} (w : Fin N → Local) :
      tensorProduct w = (fun s t => ∏ i : Fin N, w i (s i) (t i)) := by
    ext s t
    simp [tensorProduct, D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp,
      Matrix.submatrix_apply]
  have spinZ_def : spinZ = Matrix.diagonal (fun b => if b then (-1 : ℂ) else 1) := by
    ext s t
    cases s <;> cases t <;> rfl
  have tensorOp_mul {N : ℕ} (u v : Fin N → Local) :
      tensorProduct u * tensorProduct v = tensorProduct (fun i => u i * v i) := by
    classical
    rw [tensorOp_entries, tensorOp_entries, tensorOp_entries]
    ext s t
    change (∑ x : Assignment N, (∏ i : Fin N, u i (s i) (x i)) * (∏ i : Fin N, v i (x i) (t i))) =
      ∏ i : Fin N, ∑ b : Bool, u i (s i) b * v i b (t i)
    simp_rw [← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun i b => u i (s i) b * v i b (t i))).symm
  have tensorOp_one {N : ℕ} :
      tensorProduct (fun _ : Fin N => (1 : Local)) = (1 : FullOperator N) := by
    classical
    ext s t
    simp only [tensorOp_entries, Matrix.one_apply]
    by_cases h : s = t
    · subst t
      simp
    · rw [if_neg h]
      have he : ∃ i, s i ≠ t i := by
        by_contra hh
        push Not at hh
        exact h (funext hh)
      obtain ⟨i,hi⟩ := he
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
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
  classical
  have hword1 : (fun k => fermionWord i k * (fermionWord i k)ᴴ) =
      Function.update (fun _ => (1 : Local)) i ((Matrix.single false true (1 : ℂ)) * (Matrix.single false true (1 : ℂ))ᴴ) := by
    funext k
    by_cases heq : k = i
    · subst k
      simp [fermionWord]
    · by_cases hlt : k < i
      · simp [fermionWord, hlt, heq, spinZ_self_adjoint, spinZ_square]
      · simp [fermionWord, hlt, heq]
  have hword2 : (fun k => (fermionWord i k)ᴴ * fermionWord i k) =
      Function.update (fun _ => (1 : Local)) i ((Matrix.single false true (1 : ℂ))ᴴ * (Matrix.single false true (1 : ℂ))) := by
    funext k
    by_cases heq : k = i
    · subst k
      simp [fermionWord]
    · by_cases hlt : k < i
      · simp [fermionWord, hlt, heq, spinZ_self_adjoint, spinZ_square]
      · simp [fermionWord, hlt, heq]
  unfold fullC
  rw [tensorOp_adjoint, tensorOp_mul, tensorOp_mul, hword1, hword2,
    ← tensorOp_update_add, spinA_CAR]
  simpa only [Function.update_eq_self] using (tensorOp_one (N := N))

theorem fullC_mixed_anticomm_of_lt {N : ℕ} (i j : Fin N) (hij : i < j) :
    fullC i * (fullC j)ᴴ + (fullC j)ᴴ * fullC i = 0 := by
  let tensorProduct {N : ℕ} (w : Fin N → Local) : FullOperator N := tensorOp w
  have tensorOp_entries {N : ℕ} (w : Fin N → Local) :
      tensorProduct w = (fun s t => ∏ i : Fin N, w i (s i) (t i)) := by
    ext s t
    simp [tensorProduct, D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.tensorOp,
      Matrix.submatrix_apply]
  have spinZ_def : spinZ = Matrix.diagonal (fun b => if b then (-1 : ℂ) else 1) := by
    ext s t
    cases s <;> cases t <;> rfl
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
  classical
  have hw : (fun k => fermionWord i k * (fermionWord j k)ᴴ) =
      (fun k => (if k = i then (-1 : ℂ) else 1) •
        ((fermionWord j k)ᴴ * fermionWord i k)) := by
    funext k
    by_cases hki : k = i
    · subst k
      simp only [fermionWord, lt_self_iff_false, ite_false, ite_true, hij,
        spinZ_self_adjoint, neg_one_smul]
      exact spinA_spinZ
    · by_cases hkj : k = j
      · subst k
        have hji : ¬j < i := not_lt_of_ge (le_of_lt hij)
        have hne : j ≠ i := ne_of_gt hij
        simp [fermionWord, hji, hne]
      · by_cases hlt : k < i
        · have hlj : k < j := lt_trans hlt hij
          simp [fermionWord, hlt, hlj, hki, spinZ_self_adjoint]
        · by_cases hlj : k < j
          · simp [fermionWord, hlt, hlj, hki, hkj]
          · simp [fermionWord, hlt, hlj, hki, hkj]
  unfold fullC
  rw [tensorOp_adjoint, tensorOp_mul, tensorOp_mul, hw, tensorOp_scalar]
  simp

end
end D5.S3.Quantum.SpinChains.SupersymmetricFermion.JordanWigner
