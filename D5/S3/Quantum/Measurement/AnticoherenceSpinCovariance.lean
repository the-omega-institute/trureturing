/- GID: D5/S3/Quantum/Measurement/AnticoherenceSpinCovariance
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/AnticoherenceSpinCovariance
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Pauli conjugation supplies the orthogonal rotation of collective spin axes. -/

import D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
import D5.S3.Quantum.Codes.StabilizerGenuineEntanglementCommutationRank

/-! The real orthogonal Pauli action used by the spin-four witness channel. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance

open Matrix
open scoped BigOperators
open D5.S3.Quantum.FiniteDimensional (qubitX qubitZ)
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
  (Pauli pauliMatrix tensorOp tensor_mul localOp)

def pauliAxes : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![pauliMatrix Pauli.X, pauliMatrix Pauli.Y, pauliMatrix Pauli.Z]

private lemma pauli_hermitian (a : Fin 3) : (pauliAxes a).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [pauliAxes, pauliMatrix, qubitX, qubitZ, Matrix.mul_apply,
      Fin.sum_univ_two]

private lemma pauli_trace (a : Fin 3) : (pauliAxes a).trace = 0 := by
  fin_cases a <;> norm_num [pauliAxes, pauliMatrix, qubitX, qubitZ, Matrix.trace,
    Fin.sum_univ_two, Matrix.mul_apply]

private lemma pauli_gram (a b : Fin 3) :
    ((pauliAxes a) * pauliAxes b).trace = if a = b then 2 else 0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [pauliAxes, pauliMatrix, qubitX, qubitZ, Matrix.trace,
      Fin.sum_univ_two, Matrix.mul_apply]

private lemma pauli_expansion (x : Matrix (Fin 2) (Fin 2) ℂ)
    (hx : x.IsHermitian) (ht : x.trace = 0) :
    x = ∑ c : Fin 3, ((((x * pauliAxes c).trace.re / 2 : ℝ) : ℂ)) • pauliAxes c := by
  have h0 := congrArg Complex.im (hx.apply 0 0)
  have h1 := congrArg Complex.im (hx.apply 1 1)
  have h2 := congrArg Complex.re (hx.apply 0 1)
  have h3 := congrArg Complex.im (hx.apply 0 1)
  have h4 := congrArg Complex.re ht
  simp only [Complex.star_def, Complex.conj_im] at h0 h1 h3
  simp only [Complex.star_def, Complex.conj_re] at h2
  norm_num [Matrix.trace, Fin.sum_univ_two] at h4
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [pauliAxes, pauliMatrix, qubitX, qubitZ, Matrix.trace,
      Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_succ, Complex.mul_re,
      Complex.mul_im] <;> linarith

set_option backward.isDefEq.respectTransparency false in
theorem pauli_rotation (u : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ∃ r : Matrix (Fin 3) (Fin 3) ℝ, rᵀ * r = 1 ∧
      ∀ a : Fin 3, u.val * pauliAxes a * u.valᴴ =
        ∑ c : Fin 3, (r a c : ℂ) • pauliAxes c := by
  have hu : u.valᴴ * u.val = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp u.property.1
  let r : Matrix (Fin 3) (Fin 3) ℝ :=
    fun a c => ((u.val * pauliAxes a * u.valᴴ * pauliAxes c).trace.re / 2)
  have he (a : Fin 3) : u.val * pauliAxes a * u.valᴴ =
      ∑ c : Fin 3, (r a c : ℂ) • pauliAxes c := by
    apply pauli_expansion
    · change (u.val * pauliAxes a * u.valᴴ)ᴴ = _
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        (pauli_hermitian a).eq, Matrix.mul_assoc]
    · rw [Matrix.trace_mul_cycle, hu, Matrix.one_mul, pauli_trace]
  have hg (a b : Fin 3) :
      ((u.val * pauliAxes a * u.valᴴ) *
        (u.val * pauliAxes b * u.valᴴ)).trace = if a = b then 2 else 0 := by
    calc
      _ = (u.val * (pauliAxes a * pauliAxes b) * u.valᴴ).trace := by
        congr 1
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc u.valᴴ u.val, hu, Matrix.one_mul]
      _ = _ := by
        rw [Matrix.trace_mul_cycle, hu, Matrix.one_mul, pauli_gram]
  have hr : r * rᵀ = 1 := by
    ext a b
    have h := congrArg Complex.re (hg a b)
    rw [he a, he b] at h
    simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, pauli_gram] at h
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      apply_ite, Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] at h
    norm_num at h
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
    by_cases hab : a = b
    · subst b
      simp only [ite_true] at h ⊢
      simp_rw [← mul_assoc] at h
      rw [← Finset.sum_mul] at h
      linarith
    · simp only [hab, ite_false] at h ⊢
      simp_rw [← mul_assoc] at h
      rw [← Finset.sum_mul] at h
      have hh : (∑ c : Fin 3, r b c * r a c) = 0 := by linarith
      simpa only [mul_comm] using hh
  exact ⟨r, mul_eq_one_comm.mp hr, he⟩

theorem orthogonal_sandwich {k n : Type*} [Fintype k] [Fintype n]
    [DecidableEq k] (q : Matrix k k ℂ) (hq : qᵀ * q = 1)
    (s : k → Matrix n n ℂ) (x : Matrix n n ℂ) :
    (∑ a : k, (∑ c : k, q a c • s c) * x * (∑ e : k, q a e • s e)) =
      ∑ c : k, s c * x * s c := by
  have he (c e : k) : (∑ a : k, q a c * q a e) = if c = e then 1 else 0 := by
    have h := congrFun (congrFun hq c) e
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using h
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, he]
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

theorem tensor_unitary (n : ℕ) (u : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    (tensorOp (fun _ : Fin n => u.val))ᴴ * tensorOp (fun _ : Fin n => u.val) = 1 := by
  have ht : (tensorOp (fun _ : Fin n => u.val))ᴴ =
      tensorOp (fun _ : Fin n => u.valᴴ) := by
    ext x y
    simp [tensorOp, Matrix.conjTranspose_apply, map_prod]
  rw [ht, tensor_mul]
  have hu : u.valᴴ * u.val = 1 := Matrix.mem_unitaryGroup_iff'.mp u.property.1
  simp_rw [hu]
  exact D5.S3.Quantum.Codes.StabilizerGenuineEntanglementCommutationRank.coordinate_product_one

theorem local_action {n : ℕ} (k : Fin n) (a : Matrix (Fin 2) (Fin 2) ℂ)
    (f : (Fin n → Fin 2) → ℂ) (x : Fin n → Fin 2) :
    (localOp k a *ᵥ f) x = ∑ b : Fin 2, a (x k) b * f (Function.update x k b) := by
  let e := Equiv.funSplitAt k (Fin 2)
  have he (b : Fin 2) : e.symm (b, fun i => x i.val) = Function.update x k b := by
    funext i
    by_cases hi : i = k <;> simp [e, Equiv.funSplitAt, Equiv.piSplitAt, hi]
  have hk (b : Fin 2) (z : {i : Fin n // i ≠ k} → Fin 2) :
      localOp k a x (e.symm (b, z)) =
        a (x k) b * (if (fun i : {i : Fin n // i ≠ k} => x i.val) = z then 1 else 0) := by
    unfold localOp tensorOp
    rw [Matrix.of_apply, Fintype.prod_eq_mul_prod_subtype_ne _ k]
    simp [e, Equiv.funSplitAt, Equiv.piSplitAt, Matrix.one_apply,
      Fintype.prod_boole, funext_iff]
  change (∑ y : Fin n → Fin 2, localOp k a x y * f y) = _
  rw [← e.symm.sum_comp]
  simp only [Fintype.sum_prod_type, hk, ite_mul, mul_ite, one_mul, zero_mul,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, he]

theorem quadratic_rotation {n : Type*} [Fintype n] [DecidableEq n]
    (d : Matrix n n ℂ) (hd : dᴴ * d = 1) (r : Matrix (Fin 3) (Fin 3) ℝ)
    (hr : rᵀ * r = 1) (j : Fin 3 → Matrix n n ℂ)
    (hj : ∀ a, d * j a * dᴴ = ∑ c : Fin 3, (r a c : ℂ) • j c)
    (a b : Fin 3) :
    d * ((1 / 2 : ℂ) • (j a * j b + j b * j a) -
      (if a = b then (20 / 3 : ℂ) else 0) • 1) * dᴴ =
      ∑ c : Fin 3, ∑ e : Fin 3, ((r a c : ℂ) * (r b e : ℂ)) •
        ((1 / 2 : ℂ) • (j c * j e + j e * j c) -
          (if c = e then (20 / 3 : ℂ) else 0) • 1) := by
  have hd1 : d * dᴴ = 1 := mul_eq_one_comm.mp hd
  have hp (a b : Fin 3) : d * (j a * j b) * dᴴ =
      (∑ c : Fin 3, (r a c : ℂ) • j c) * (∑ e : Fin 3, (r b e : ℂ) • j e) := by
    rw [← hj, ← hj]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc dᴴ d, hd, Matrix.one_mul]
  have hrow : (∑ c : Fin 3, (r a c : ℂ) * (r b c : ℂ)) =
      if a = b then 1 else 0 := by
    have hrr : r * rᵀ = 1 := mul_eq_one_comm.mp hr
    have h := congrArg (fun m : Matrix (Fin 3) (Fin 3) ℝ => m a b) hrr
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h
    exact_mod_cast h
  have hδ : (if a = b then (20 / 3 : ℂ) else 0) =
      (20 / 3 : ℂ) * ∑ c : Fin 3, (r a c : ℂ) * (r b c : ℂ) := by
    rw [hrow]
    split_ifs <;> ring
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hp, hd1, hδ]
  norm_num [Fin.sum_univ_succ]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    smul_add, smul_sub, smul_smul]
  module

end D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance
