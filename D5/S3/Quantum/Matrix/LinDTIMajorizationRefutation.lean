/- GID: D5/S3/Quantum/Matrix/LinDTIMajorizationRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/LinDTIMajorizationRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/LinDTIMajorizationRefutation.claim; result=D5/S3/Quantum/Matrix/LinDTIMajorizationRefutation.result; claim=D5/S3/Quantum/Matrix/LinDTIMajorizationRefutation.claim
   digest: Lin's matrix majorization conjecture fails in dimension three at exponent four. -/

/-
admission_basis: open-problem-resolution (#18700; Refuted)
Direct frozen dependencies: result uses eigenvalue_lower_of_psd_sub_scalar from
D5/S3/Quantum/Measurement/OverlapLowRankDistance, accessed at its original private name.
Declaration statement_id: sha256:ae7ecd4c4168b0be9cf9c1a1782ddcf6ac5a70a635240adfd052834b90fc5eba.
All other declarations have no direct frozen dependencies after same-delivery helpers are inlined.
The absolute-power expression of #18700 is inlined in claim, with no forwarding definition.
It is cfc of the real power on CFC.sqrt of the conjugate-transpose product.
The definitions eigDesc and Majorizes retain the source expressions of #18700.
All certificate data and proof helpers are private; the only public theorem is result.
The public result is the designated refutation result (`basis=refutes`) and is exempt from
four-slot escape registration (CLAUDE.md §3.9).

eigDesc: proof_shape: bind-only; escape_witness: none; consumers: claim, eigDesc_length, eigDesc_mem, eigDesc_sorted.
Majorizes: proof_shape: bind-only; escape_witness: none; consumers: claim, not_majorizes_of_low.
claim: proof_shape: bind-only; escape_witness: none; consumers: result.
absPow_four: proof_shape: bind-only; escape_witness: none; consumers: L_eq, R_eq.
A: proof_shape: bind-only; escape_witness: none; consumers: A_psd, A_star, L_eq, R_eq, result.
B: proof_shape: bind-only; escape_witness: none; consumers: B_ldl, B_psd, B_star, L_eq, R_eq, result.
L: proof_shape: bind-only; escape_witness: none; consumers: L_ldl, L_lower, L_eq, L_herm, result.
R: proof_shape: bind-only; escape_witness: none; consumers: R_eq, R_herm, R_negative, result.
UB: proof_shape: bind-only; escape_witness: none; consumers: B_ldl.
DB: proof_shape: bind-only; escape_witness: none; consumers: B_ldl, B_psd.
UL: proof_shape: bind-only; escape_witness: none; consumers: L_ldl.
DL: proof_shape: bind-only; escape_witness: none; consumers: L_ldl, L_lower.
A_psd: proof_shape: bind-only; escape_witness: none; consumers: A_star, result.
B_ldl: proof_shape: bind-only; escape_witness: none; consumers: B_psd.
B_psd: proof_shape: bind-only; escape_witness: none; consumers: B_star, result.
L_ldl: proof_shape: bind-only; escape_witness: none; consumers: L_lower.
L_lower: proof_shape: bind-only; escape_witness: none; consumers: L_herm, result.
A_star: proof_shape: bind-only; escape_witness: none; consumers: L_eq, R_eq.
B_star: proof_shape: bind-only; escape_witness: none; consumers: L_eq, R_eq.
L_eq: proof_shape: bind-only; escape_witness: none; consumers: result.
R_eq: proof_shape: bind-only; escape_witness: none; consumers: result.
L_herm: proof_shape: bind-only; escape_witness: none; consumers: result.
R_herm: proof_shape: bind-only; escape_witness: none; consumers: result.
v: proof_shape: bind-only; escape_witness: none; consumers: R_negative, result.
R_negative: proof_shape: bind-only; escape_witness: none; consumers: result.
shift_spec: proof_shape: bind-only; escape_witness: none; consumers: psd_of_eig_lower.
psd_of_eig_lower: proof_shape: bind-only; escape_witness: none; consumers: result.
eigDesc_length: proof_shape: bind-only; escape_witness: none; consumers: result.
eigDesc_mem: proof_shape: bind-only; escape_witness: none; consumers: result.
eigDesc_sorted: proof_shape: bind-only; escape_witness: none; consumers: result.
not_majorizes_of_low: proof_shape: bind-only; escape_witness: none; consumers: result.
result: proof_shape: bind-only; escape_witness: none; consumers: none.
-/

import D5.S3.Quantum.Measurement.OverlapLowRankDistance

/-! A rational three-dimensional counterexample to Lin’s eigenvalue majorization. -/

set_option autoImplicit false

namespace D5.S3.Quantum.Matrix.LinDTIMajorizationRefutation

open _root_.Matrix
open scoped ComplexOrder MatrixOrder

/-- `λ(M)`: the eigenvalues of a Hermitian matrix, listed with multiplicity in descending order
(the empty list if `M` is not Hermitian). -/
noncomputable def eigDesc {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : List ℝ :=
  if h : M.IsHermitian then (List.ofFn h.eigenvalues).mergeSort (fun a b => decide (b ≤ a)) else []

/-- `x ≻ y`: `∑_{i ≤ k} x↓_i ≥ ∑_{i ≤ k} y↓_i` for `k = 1, …, n`, and `∑ x_i = ∑ y_i`, for vectors listed
in descending order. -/
def Majorizes (x y : List ℝ) : Prop :=
  (∀ k : ℕ, 1 ≤ k → k ≤ x.length → (y.take k).sum ≤ (x.take k).sum) ∧ x.sum = y.sum

/-- Lin, Commun. Contemp. Math. 19 (2017) 1650044, Conjecture 4.3 ("Let A and B be n × n positive
semidefinite matrices. Then λ(A² + |BA|^p) ≻ λ(A² + |AB|^p) for all p > 0."). -/
def claim : Prop :=
  ∀ n : ℕ, ∀ A B : Matrix (Fin n) (Fin n) ℂ, A.PosSemidef → B.PosSemidef → ∀ p : ℝ, 0 < p →
    Majorizes
      (eigDesc (A ^ 2 + cfc (fun x : ℝ => x ^ p) (CFC.sqrt ((B * A)ᴴ * (B * A)))))
      (eigDesc (A ^ 2 + cfc (fun x : ℝ => x ^ p) (CFC.sqrt ((A * B)ᴴ * (A * B)))))

end D5.S3.Quantum.Matrix.LinDTIMajorizationRefutation

open private eigenvalue_lower_of_psd_sub_scalar from D5.S3.Quantum.Measurement.OverlapLowRankDistance
namespace D5.S3.Quantum.Matrix.LinDTIMajorizationRefutation
open _root_.Matrix
open scoped ComplexOrder MatrixOrder
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
private lemma absPow_four {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    cfc (fun x : ℝ => x ^ (4 : ℝ)) (CFC.sqrt (Xᴴ * X)) = (Xᴴ * X) ^ 2 := by
  simp_rw [show (4 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast]
  rw [cfc_pow_id _ _ (CFC.sqrt_nonneg _).isSelfAdjoint]
  rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, CFC.sq_sqrt _ (Matrix.nonneg_iff_posSemidef.mpr (posSemidef_conjTranspose_mul_self X))]


private noncomputable def A : Matrix (Fin 3) (Fin 3) ℂ := diagonal ![3, 1, 1/2]
private noncomputable def B : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1/2, 1/4, 3/4; 1/4, 3/4, 0; 3/4, 0, 5/2]
private noncomputable def L : Matrix (Fin 3) (Fin 3) ℂ :=
  !![21321/256, 2121/256, 4149/128;
     2121/256, 2333/1024, 6927/2048;
     4149/128, 6927/2048, 59597/4096]
private noncomputable def R : Matrix (Fin 3) (Fin 3) ℂ :=
  !![129085/4096, 11451/1024, 75999/2048;
     11451/1024, 875/128, 9279/512;
     75999/2048, 9279/512, 63245/1024]
private noncomputable def UB : Matrix (Fin 3) (Fin 3) ℂ := !![1, 1/2, 3/2; 0, 1, -3/5; 0, 0, 1]
private noncomputable def DB : Matrix (Fin 3) (Fin 3) ℂ := diagonal ![1/2, 5/8, 23/20]
private noncomputable def UL : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 10605/104813, 41490/104813; 0, 1, 36728885/14319974; 0, 0, 1]
private noncomputable def DL : Matrix (Fin 3) (Fin 3) ℂ :=
  diagonal ![104813/1280, 21479961/536642560, 2041722639/36659133440]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
private lemma A_psd : A.PosSemidef := by
  rw [A, posSemidef_diagonal_iff]
  intro i; fin_cases i <;> norm_num [Complex.le_def]
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
private lemma B_ldl : B = UBᴴ * DB * UB := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [B, UB, DB, Matrix.mul_apply, Fin.sum_univ_three, conjTranspose_apply,
      diagonal_apply, Complex.ext_iff, map_ofNat, map_natCast]
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
private lemma B_psd : B.PosSemidef := by
  rw [B_ldl]
  apply PosSemidef.conjTranspose_mul_mul_same
  rw [DB, posSemidef_diagonal_iff]
  intro i; fin_cases i <;> norm_num [Complex.le_def]
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
private lemma L_ldl : L - (7/5 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) = ULᴴ * DL * UL := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [L, UL, DL, Matrix.mul_apply, Fin.sum_univ_three, conjTranspose_apply,
      diagonal_apply, Matrix.one_apply, Complex.ext_iff, map_ofNat, map_natCast]
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
private lemma L_lower : (L - (7/5 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)).PosSemidef := by
  rw [L_ldl]
  apply PosSemidef.conjTranspose_mul_mul_same
  rw [DL, posSemidef_diagonal_iff]
  intro i; fin_cases i <;> norm_num [Complex.le_def]
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
private lemma A_star : Aᴴ = A := A_psd.isHermitian
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
private lemma B_star : Bᴴ = B := B_psd.isHermitian
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
private lemma L_eq :
    A ^ 2 + cfc (fun x : ℝ => x ^ (4 : ℝ))
      (CFC.sqrt ((B * A)ᴴ * (B * A))) = L := by
  rw [absPow_four, conjTranspose_mul, A_star, B_star]
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [A, B, L, pow_two, Matrix.mul_apply, Fin.sum_univ_three, diagonal_apply, Matrix.vecMul, dotProduct]
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
private lemma R_eq :
    A ^ 2 + cfc (fun x : ℝ => x ^ (4 : ℝ))
      (CFC.sqrt ((A * B)ᴴ * (A * B))) = R := by
  rw [absPow_four, conjTranspose_mul, A_star, B_star]
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [A, B, R, pow_two, Matrix.mul_apply, Fin.sum_univ_three, diagonal_apply, Matrix.vecMul, dotProduct]
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
private lemma L_herm : L.IsHermitian := by
  simpa only [sub_add_cancel] using L_lower.isHermitian.add
    (isHermitian_one.smul (by simp [IsSelfAdjoint] : IsSelfAdjoint (7/5 : ℝ)))
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
private lemma R_herm : R.IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [R, conjTranspose_apply, Complex.ext_iff, map_ofNat, map_natCast]
private noncomputable def v : Fin 3 → ℂ := ![0, -1, 19/64]
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
private lemma R_negative : (star v ⬝ᵥ ((R - (7/5 : ℝ) • 1) *ᵥ v)).re < 0 := by
  norm_num [v, R, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.one_apply, map_ofNat, map_natCast]
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
private lemma shift_spec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (t x : ℝ) :
    x - t ∈ spectrum ℝ (M - t • 1) ↔ x ∈ spectrum ℝ M := by
  have h := spectrum.add_mem_iff (R := ℝ) (a := M) (r := x-t) (s := t)
  simpa [Algebra.algebraMap_eq_smul_one, sub_eq_add_neg, add_comm, sub_add_cancel] using h.symm

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
private lemma psd_of_eig_lower {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : M.IsHermitian)
    (t : ℝ) (hb : ∀ i, t ≤ h.eigenvalues i) : (M - t • 1).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  apply (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ (h.sub (isHermitian_one.smul (by simp [IsSelfAdjoint] : IsSelfAdjoint t)))).mpr
  intro x hx
  have hm : x+t ∈ spectrum ℝ M := by
    apply (shift_spec M t (x+t)).mp
    simpa using hx
  rw [h.spectrum_real_eq_range_eigenvalues] at hm
  obtain ⟨i, hi⟩ := hm
  linarith [hb i]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
private lemma eigDesc_length {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : M.IsHermitian) :
    (eigDesc M).length = n := by simp [eigDesc, h]
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
private lemma eigDesc_mem {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : M.IsHermitian) (x : ℝ) :
    x ∈ eigDesc M ↔ ∃ i, h.eigenvalues i = x := by simp [eigDesc, h]
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
private lemma eigDesc_sorted {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : M.IsHermitian) :
    (eigDesc M).Pairwise (fun a b => b ≤ a) := by
  simpa [eigDesc, h] using (List.sortedGE_mergeSort (l := List.ofFn h.eigenvalues)).pairwise

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
private lemma not_majorizes_of_low {x y : List ℝ} (hx : x.length = 3) (hy : y.length = 3)
    (hys : y.Pairwise (fun a b => b ≤ a)) (t : ℝ)
    (hlow : ∀ z ∈ x, t ≤ z) (hex : ∃ z ∈ y, z < t) :
    ¬ Majorizes x y := by
  obtain ⟨a,b,c,rfl⟩ := List.length_eq_three.mp hx
  obtain ⟨d,e,f,rfl⟩ := List.length_eq_three.mp hy
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hys
  have hc := hlow c (by simp)
  obtain ⟨z,hz,hzt⟩ := hex
  have hf : f < t := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl <;> linarith
  intro hm
  have hs := hm.2
  have htwo := hm.1 2 (by norm_num) (by simp)
  simp only [List.take_succ_cons, List.take_zero, List.sum_cons, List.sum_nil] at htwo
  simp only [List.sum_cons, List.sum_nil] at hs
  linarith

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4000 in
theorem result : ¬ claim := by
  intro hc
  have hm := hc 3 A B A_psd B_psd 4 (by norm_num)
  rw [L_eq, R_eq] at hm
  have hr : ∃ i, R_herm.eigenvalues i < (7/5 : ℝ) := by
    by_contra! hn
    have hp := (psd_of_eig_lower R_herm (7/5) hn).re_dotProduct_nonneg v
    exact (not_lt_of_ge hp) R_negative
  apply not_majorizes_of_low (eigDesc_length L_herm) (eigDesc_length R_herm)
    (eigDesc_sorted R_herm) (7/5) ?_ ?_ hm
  · intro z hz
    obtain ⟨i, rfl⟩ := (eigDesc_mem L_herm z).mp hz
    exact eigenvalue_lower_of_psd_sub_scalar L_herm (7/5) L_lower i
  · obtain ⟨i, hi⟩ := hr
    exact ⟨R_herm.eigenvalues i, (eigDesc_mem R_herm _).mpr ⟨i, rfl⟩, hi⟩
end D5.S3.Quantum.Matrix.LinDTIMajorizationRefutation
