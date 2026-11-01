/- GID: D5/S3/Quantum/Measurement/AnticoherenceSpinCovariance
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/AnticoherenceSpinCovariance
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Pauli conjugation supplies the orthogonal rotation of collective spin axes. -/

import D5.S3.Quantum.Dynamics.SpinCoupledEvenHypercubeGroverFixedPoint
import D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm
import D5.S3.QuantumChannels.ChannelTimeReversalNoGo
import D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings

/-! The real orthogonal Pauli action used by the spin-four witness channel. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance

open _root_.Matrix
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open scoped BigOperators
open D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction (pauli)
open D5.S3.Quantum.QuantumChannels.QubitWassersteinCouplings (pauli_hermitian)
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
  (Pauli pauliMatrix tensorOp tensor_mul localOp)

private lemma pauli_gram (a b : Fin 3) :
    ((pauli a) * pauli b).trace = if a = b then 2 else 0 := by
  have h := D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.pauli_trace_pair
    (![Pauli.X, Pauli.Y, Pauli.Z] a) (![Pauli.X, Pauli.Y, Pauli.Z] b)
  simpa only [pauli, show (![Pauli.X, Pauli.Y, Pauli.Z] a =
    ![Pauli.X, Pauli.Y, Pauli.Z] b) ↔ a = b by fin_cases a <;> fin_cases b <;> decide] using h

private lemma pauli_expansion (x : Matrix (Fin 2) (Fin 2) ℂ)
    (hx : x.IsHermitian) (ht : x.trace = 0) :
    x = ∑ c : Fin 3, ((((x * pauli c).trace.re / 2 : ℝ) : ℂ)) • pauli c := by
  have h := D5.S3.QuantumChannels.ChannelTimeReversalNoGo.Qubit.pauli_expansion x
  rw [ht, zero_div, zero_smul, zero_add] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro c _
  rw [Matrix.trace_mul_comm (pauli c) x,
    D5.S3.Quantum.Tomography.PurityPythagorasDecomposition.trace_mul_real_of_hermitian
      x (pauli c) hx (pauli_hermitian c)]
  simp

set_option backward.isDefEq.respectTransparency false in
theorem pauli_rotation (u : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ∃ r : Matrix (Fin 3) (Fin 3) ℝ, rᵀ * r = 1 ∧
      ∀ a : Fin 3, u.val * pauli a * u.valᴴ =
        ∑ c : Fin 3, (r a c : ℂ) • pauli c := by
  have hu : u.valᴴ * u.val = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp u.property.1
  let r : Matrix (Fin 3) (Fin 3) ℝ :=
    fun a c => ((u.val * pauli a * u.valᴴ * pauli c).trace.re / 2)
  have he (a : Fin 3) : u.val * pauli a * u.valᴴ =
      ∑ c : Fin 3, (r a c : ℂ) • pauli c := by
    apply pauli_expansion
    · exact Matrix.isHermitian_mul_mul_conjTranspose u.val (pauli_hermitian a)
    · rw [Matrix.trace_mul_cycle, hu, Matrix.one_mul, D5.S3.QuantumChannels.ChannelTimeReversalNoGo.PauliChannels.sigma_trace]
  have hg (a b : Fin 3) :
      ((u.val * pauli a * u.valᴴ) *
        (u.val * pauli b * u.valᴴ)).trace = if a = b then 2 else 0 := by
    calc
      _ = (u.val * (pauli a * pauli b) * u.valᴴ).trace := by
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
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]

theorem tensor_unitary (n : ℕ) (u : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    (tensorOp (fun _ : Fin n => u.val))ᴴ * tensorOp (fun _ : Fin n => u.val) = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp
    (D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm.tensor_unitary _
      (fun _ => u.property.1))

theorem local_action {n : ℕ} (k : Fin n) (a : Matrix (Fin 2) (Fin 2) ℂ)
    (f : (Fin n → Fin 2) → ℂ) (x : Fin n → Fin 2) :
    (localOp k a *ᵥ f) x = ∑ b : Fin 2, a (x k) b * f (Function.update x k b) := by
  let e := Equiv.funSplitAt k (Fin 2)
  have he (b : Fin 2) : e.symm (b, fun i => x i.val) = Function.update x k b := by
    funext i
    by_cases hi : i = k <;>
      simp [e, Equiv.funSplitAt_symm_apply, hi]
  have hk (b : Fin 2) (z : {i : Fin n // i ≠ k} → Fin 2) :
      localOp k a x (e.symm (b, z)) =
        a (x k) b * (if (fun i : {i : Fin n // i ≠ k} => x i.val) = z then 1 else 0) := by
    unfold localOp tensorOp
    rw [Matrix.of_apply, Fintype.prod_eq_mul_prod_subtype_ne _ k]
    have hy (i : {i : Fin n // i ≠ k}) : e.symm (b, z) i.val = z i := by
      simp only [e, Equiv.funSplitAt_symm_apply, dite_eq_right i.property]
    have hp : (∏ i : {i : Fin n // i ≠ k},
        Function.update (fun _ : Fin n => (1 : Matrix (Fin 2) (Fin 2) ℂ)) k a i.val
          (x i.val) (e.symm (b, z) i.val)) =
        if (fun i : {i : Fin n // i ≠ k} => x i.val) = z then 1 else 0 := by
      calc
        _ = ∏ i : {i : Fin n // i ≠ k},
            if x i.val = z i then (1 : ℂ) else 0 := by
          apply Finset.prod_congr rfl
          intro i _
          rw [Function.update_of_ne i.property, hy]
          rfl
        _ = _ := by simp [Fintype.prod_boole, funext_iff]
    rw [hp, Function.update_self]
    dsimp only [e, Equiv.funSplitAt, Equiv.piSplitAt]
    simp
  change (∑ y : Fin n → Fin 2, localOp k a x y * f y) = _
  rw [← e.symm.sum_comp]
  simp only [Fintype.sum_prod_type, hk, ite_mul, mul_ite, one_mul, zero_mul,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, he]

def collectiveSpin (n : ℕ) (a : Fin 3) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  (1 / 2 : ℂ) • ∑ k : Fin n, localOp k (pauli a)

theorem collective_tensor_rotation (n : ℕ)
    (u : Matrix.specialUnitaryGroup (Fin 2) ℂ) (r : Matrix (Fin 3) (Fin 3) ℝ)
    (hr : ∀ a, u.val * pauli a * u.valᴴ =
      ∑ c : Fin 3, (r a c : ℂ) • pauli c) (a : Fin 3) :
    tensorOp (fun _ : Fin n => u.val) * collectiveSpin n a *
      (tensorOp (fun _ : Fin n => u.val))ᴴ =
        ∑ c : Fin 3, (r a c : ℂ) • collectiveSpin n c := by
  rw [collectiveSpin]
  have hu : u.val * u.valᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp u.property.1
  have ht : (tensorOp (fun _ : Fin n => u.val))ᴴ =
      tensorOp (fun _ : Fin n => u.valᴴ) := by
    exact D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm.tensor_adj _
  have hc (k : Fin n) : tensorOp (fun _ : Fin n => u.val) *
      localOp k (pauli a) * (tensorOp (fun _ : Fin n => u.val))ᴴ =
        localOp k (u.val * pauli a * u.valᴴ) := by
    unfold localOp
    rw [ht, tensor_mul, tensor_mul]
    congr 1
    funext i
    by_cases hi : i = k
    · subst i; simp
    · simp [Function.update_of_ne hi, hu]
  have hm (k : Fin n) (b : Matrix (Fin 2) (Fin 2) ℂ) (x y : Fin n → Fin 2) :
      localOp k b x y = ∑ z : Fin 2, b (x k) z *
        (if Function.update x k z = y then 1 else 0) := by
    simpa only [Matrix.mulVec, dotProduct, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using
      local_action k b (fun z => if z = y then 1 else 0) x
  simp only [collectiveSpin, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum,
    Matrix.sum_mul, hc, hr a]
  ext x y
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, hm]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext k
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem quadratic_rotation {n : Type*} [Fintype n] [DecidableEq n]
    (d : Matrix n n ℂ) (hd : dᴴ * d = 1) (r : Matrix (Fin 3) (Fin 3) ℝ)
    (hr : rᵀ * r = 1) (j : Fin 3 → Matrix n n ℂ)
    (hj : ∀ a, d * j a * dᴴ = ∑ c : Fin 3, (r a c : ℂ) • j c)
    (κ : ℂ) (a b : Fin 3) :
    d * ((1 / 2 : ℂ) • (j a * j b + j b * j a) -
      (if a = b then κ else 0) • 1) * dᴴ =
      ∑ c : Fin 3, ∑ e : Fin 3, ((r a c : ℂ) * (r b e : ℂ)) •
        ((1 / 2 : ℂ) • (j c * j e + j e * j c) -
          (if c = e then κ else 0) • 1) := by
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
    have hh := congrArg Complex.ofReal h
    push_cast at hh
    simpa only [apply_ite, Complex.ofReal_one, Complex.ofReal_zero] using hh
  have hδ : (if a = b then κ else 0) =
      κ * ∑ c : Fin 3, (r a c : ℂ) * (r b c : ℂ) := by
    rw [hrow]
    split_ifs <;> ring
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hp, hd1, hδ]
  norm_num [Fin.sum_univ_succ]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    smul_add, smul_sub, smul_smul]
  module

/-- The normalized Dicke embedding; the spin index counts qubits in state one. -/
def dickeIsometry (n : ℕ) : Matrix (Fin n → Fin 2) (Fin (n + 1)) ℂ :=
  fun x r => if (∑ k, (x k).val) = r.val then
    (Real.sqrt (n.choose r.val : ℝ) : ℂ)⁻¹ else 0

set_option backward.isDefEq.respectTransparency false in
theorem partialTrace_isometries {a b i j : Type*}
    [Fintype a] [Fintype b] [Fintype i] [Fintype j]
    [DecidableEq j] (v : Matrix a i ℂ) (w : Matrix b j ℂ)
    (hw : wᴴ * w = 1) (z : Matrix (i × j) (i × j) ℂ) :
    partialTraceRight (Matrix.kronecker v w * z * (Matrix.kronecker v w)ᴴ) =
      v * partialTraceRight z * vᴴ := by
  have hb (k l : j) : (∑ d : b, w d k * star (w d l)) = if k = l then 1 else 0 := by
    have h := congrFun (congrFun hw l) k
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      mul_comm, eq_comm] using h
  ext x y
  dsimp only [Matrix.kronecker, Matrix.kroneckerMap]
  simp only [partialTraceRight, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.of_apply, Fintype.sum_prod_type, star_mul]
  simp_rw [Finset.sum_mul]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2
    ext k
    rw [Finset.sum_comm]
    arg 2
    ext l
    rw [Finset.sum_comm]
    arg 2
    ext m
    rw [Finset.sum_comm]
  have he (k m : i) (l n : j) :
      (∑ d : b, v x m * w d n * z (m, n) (k, l) *
        (star (w d l) * star (v y k))) =
      v x m * z (m, l) (k, l) * star (v y k) * (if n = l then 1 else 0) := by
    calc
      _ = (v x m * z (m, n) (k, l) * star (v y k)) *
          (∑ d : b, w d n * star (w d l)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        ring
      _ = _ := by rw [hb]; split_ifs with h <;> simp_all
  simp_rw [he]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]

def dickeCoefficient (n w r : ℕ) : ℂ :=
  if w = r then (Real.sqrt (n.choose r : ℝ) : ℂ)⁻¹ else 0

private lemma two_value_sum (n : ℕ) (x : Fin n → Fin 2) (f : Fin 2 → ℂ) :
    (∑ k, f (x k)) = ((n : ℂ) - (∑ k, (x k).val : ℕ)) * f 0 +
      (∑ k, (x k).val : ℕ) * f 1 := by
  let σ := Finset.univ.filter (fun k : Fin n => x k = 1)
  have h := D5.S3.Quantum.Dynamics.SpinCoupledEvenHypercubeGroverFixedPoint.sum_two_values
    σ (f 1) (f 0)
  rw [Nat.cast_sub (card_finset_fin_le σ)] at h
  have he (b : Fin 2) : b.val = if b = 1 then 1 else 0 := by
    fin_cases b <;> simp
  simp_rw [he]
  rw [Finset.sum_boole]
  calc
    _ = ∑ k : Fin n, if k ∈ σ then f 1 else f 0 := by
      apply Finset.sum_congr rfl
      intro k _
      generalize hx : x k = b
      fin_cases b <;> simp [σ, hx]
    _ = _ := by
      rw [h]
      simp only [Nat.cast_id, σ]
      ring

theorem dicke_site_sum (n : ℕ) (a : Matrix (Fin 2) (Fin 2) ℂ)
    (x : Fin n → Fin 2) (r : Fin (n + 1)) :
    (∑ k : Fin n, ∑ b : Fin 2, a (x k) b *
      dickeIsometry n (Function.update x k b) r) =
      ((n : ℂ) - (∑ k, (x k).val : ℕ)) *
        (a 0 0 * dickeCoefficient n (∑ k, (x k).val) r.val +
          a 0 1 * dickeCoefficient n ((∑ k, (x k).val) + 1) r.val) +
      (∑ k, (x k).val : ℕ) *
        (a 1 0 * dickeCoefficient n ((∑ k, (x k).val) - 1) r.val +
          a 1 1 * dickeCoefficient n (∑ k, (x k).val) r.val) := by
  let w := ∑ k, (x k).val
  have hu (k : Fin n) (b : Fin 2) :
      (∑ i, (Function.update x k b i).val) + (x k).val = w + b.val := by
    have he : (fun i => (Function.update x k b i).val) =
        Function.update (fun i => (x i).val) k b.val := by
      exact Function.comp_update Fin.val x k b
    rw [he, Finset.sum_update_of_mem (Finset.mem_univ k)]
    simp only [Finset.sdiff_singleton_eq_erase]
    have h := Finset.add_sum_erase Finset.univ (fun i => (x i).val) (Finset.mem_univ k)
    dsimp only [w]
    omega
  let f : Fin 2 → ℂ :=
    ![a 0 0 * dickeCoefficient n w r.val + a 0 1 * dickeCoefficient n (w + 1) r.val,
      a 1 0 * dickeCoefficient n (w - 1) r.val + a 1 1 * dickeCoefficient n w r.val]
  have hf (k : Fin n) : (∑ b : Fin 2, a (x k) b *
      dickeIsometry n (Function.update x k b) r) = f (x k) := by
    have h0 := hu k 0
    have h1 := hu k 1
    by_cases hk : x k = 0
    · have hz : (∑ i, (Function.update x k 0 i).val) = w := by simp [hk] at h0; omega
      have ho : (∑ i, (Function.update x k 1 i).val) = w + 1 := by simp [hk] at h1; omega
      simp [Fin.sum_univ_two, dickeIsometry, hz, ho, f, hk, dickeCoefficient]
    · have hk1 : x k = 1 := Fin.ext (by have hh := (x k).isLt; omega)
      have hz : (∑ i, (Function.update x k 0 i).val) = w - 1 := by simp [hk1] at h0; omega
      have ho : (∑ i, (Function.update x k 1 i).val) = w := by simp [hk1] at h1; omega
      simp [Fin.sum_univ_two, dickeIsometry, hz, ho, f, hk1, dickeCoefficient]
  simp_rw [hf]
  simpa only [f, Matrix.cons_val_zero, Matrix.cons_val_one] using two_value_sum n x f

end D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance
