/- GID: D5/S3/Quantum/Information/CommutingEncoding/LocalSiteNormalForm
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/CommutingEncoding/LocalSiteNormalForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Commuting qubit tensor encoders admit diagonal or phased Pauli local forms. -/

import D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm
import D5.S3.Quantum.BlockNorm.EssentiallyHermitian

open scoped BigOperators
open Matrix
open D5.S3.Quantum.FiniteDimensional (qubitX qubitZ qubit_weyl_star)
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm (tensor_adj tensor_unitary)

namespace D5.S3.Quantum.Information.CommutingEncodingReflectionClass

private lemma tensor_factors_proportional {n : ℕ} (X Y : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (h : tensorOp X = tensorOp Y) (hne : tensorOp X ≠ 0) : ∀ j, ∃ c : ℂ, Y j = c • X j := by
  classical
  obtain ⟨x, y, hxy⟩ : ∃ x y, tensorOp X x y ≠ 0 := by
    by_contra! hz
    apply hne
    ext x y; exact hz x y
  have hY : (∏ i, Y i (x i) (y i)) ≠ 0 := by
    change tensorOp Y x y ≠ 0; rwa [← h]
  intro j
  have hrest : (∏ i ∈ Finset.univ.erase j, Y i (x i) (y i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ =>
      Finset.prod_ne_zero_iff.mp hY i (Finset.mem_univ i)
  have entry (Z : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (r t : Fin 2) :
      tensorOp Z (Function.update x j r) (Function.update y j t) =
        Z j r t * ∏ i ∈ Finset.univ.erase j, Z i (x i) (y i) := by
    dsimp only [tensorOp, Matrix.of_apply]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]; simp only [Function.update_self]
    congr 1; apply Finset.prod_congr rfl
    intro i hi; rw [Function.update_of_ne (Finset.ne_of_mem_erase hi),
      Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  refine ⟨(∏ i ∈ Finset.univ.erase j, X i (x i) (y i)) /
    (∏ i ∈ Finset.univ.erase j, Y i (x i) (y i)), ?_⟩
  ext r t; have he := congrFun (congrFun h (Function.update x j r)) (Function.update y j t)
  rw [entry, entry] at he; change Y j r t = _ * X j r t
  rw [div_mul_eq_mul_div, eq_div_iff hrest, mul_comm _ (X j r t)]; exact he.symm
lemma local_commutation_signs {n : ℕ} (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ a j, U a j ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hc : ∀ a b, tensorOp (U a) * tensorOp (U b) = tensorOp (U b) * tensorOp (U a)) :
    ∀ a b j, U a j * U b j = U b j * U a j ∨
      U a j * U b j = -(U b j * U a j) := by
  classical
  intro a b j
  have hunit : tensorOp (fun i => U a i * U b i) ∈
      Matrix.unitaryGroup (Fin n → Fin 2) ℂ :=
    tensor_unitary _ fun i => (Matrix.unitaryGroup (Fin 2) ℂ).mul_mem (hU a i) (hU b i)
  have hne : tensorOp (fun i => U a i * U b i) ≠ 0 := by
    intro hz; have hi := hunit.1; rw [hz, star_zero, zero_mul] at hi; exact zero_ne_one hi
  have heq : tensorOp (fun i => U a i * U b i) = tensorOp (fun i => U b i * U a i) := by
    simpa only [tensor_mul] using hc a b
  obtain ⟨c, he⟩ := tensor_factors_proportional _ _ heq hne j
  have hdet : (U a j * U b j).det ≠ 0 := by
    rw [Matrix.det_mul]; exact mul_ne_zero (Matrix.det_ne_zero_of_left_inverse (hU a j).1)
      (Matrix.det_ne_zero_of_left_inverse (hU b j).1)
  have hc2 : c ^ 2 = 1 := by
    have hd := congrArg Matrix.det he
    rw [Matrix.det_smul, Fintype.card_fin, Matrix.det_mul_comm (U b j)] at hd
    apply mul_right_cancel₀ hdet
    simpa only [one_mul] using hd.symm
  rcases sq_eq_one_iff.mp hc2 with rfl | rfl
  · left
    simpa using he.symm
  · right
    simpa using (congrArg Neg.neg he).symm
private lemma trace_nonzero_commutes (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin 2) ℂ) (ht : Matrix.trace A ≠ 0)
    (hs : A * B = B * A ∨ A * B = -(B * A)) : A * B = B * A := by
  rcases hs with hs | hs
  · exact hs
  · exfalso
    apply ht
    have hi : Bᴴ * (A * B) = -A := by
      rw [hs, mul_neg, ← Matrix.mul_assoc, show Bᴴ * B = 1 from hB.1, Matrix.one_mul]
    have hh := congrArg Matrix.trace hi
    rw [Matrix.trace_mul_cycle', ← Matrix.mul_assoc,
      show B * Bᴴ = 1 from hB.2, Matrix.one_mul, Matrix.trace_neg] at hh
    linear_combination (1 / 2 : ℂ) * hh
private lemma diagonal_site_basis {κ : Type*}
    (A : Matrix (Fin 2) (Fin 2) ℂ) (B : κ → Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hB : ∀ a, B a ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (ht : Matrix.trace A ≠ 0) (hn : ¬ ∃ c : ℂ, A = c • 1)
    (hs : ∀ a, A * B a = B a * A ∨ A * B a = -(B a * A)) : ∃ V ∈ Matrix.unitaryGroup (Fin 2) ℂ,
      ∀ a, ∃ d : Fin 2 → ℂ, V * B a * Vᴴ = diagonal d := by
  classical
  letI : IsStarNormal A := isStarNormal_of_mem_unitary hA
  obtain ⟨K, hK, d, hd⟩ := Matrix.exists_mem_unitaryGroup_star_mul_mul_eq_diagonal A
  have hKd : Kᴴ * A * K = diagonal d := hd
  have hKK : K * Kᴴ = 1 := hK.2
  have hdne : d 0 ≠ d 1 := by
    intro heq; apply hn; refine ⟨d 0, ?_⟩
    have he : diagonal d = d 0 • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, heq]
    calc
      A = K * (Kᴴ * A * K) * Kᴴ := by
        symm
        calc
          _ = (K * Kᴴ) * A * (K * Kᴴ) := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [hKK, Matrix.one_mul, Matrix.mul_one]
      _ = K * (d 0 • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * Kᴴ := by rw [hKd, he]
      _ = _ := by rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hKK]
  refine ⟨Kᴴ, Unitary.star_mem hK, ?_⟩
  intro a; let C := Kᴴ * B a * K
  have hm (X Y : Matrix (Fin 2) (Fin 2) ℂ) : (Kᴴ * X * K) * (Kᴴ * Y * K) = Kᴴ * (X * Y) * K := by
    calc
      _ = Kᴴ * X * (K * Kᴴ) * Y * K := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hKK, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hc : diagonal d * C = C * diagonal d := by
    rw [← hKd]; dsimp only [C]; rw [hm, hm, trace_nonzero_commutes A (B a) (hB a) ht (hs a)]
  have hc01 : C 0 1 = 0 := by
    have hh := congrFun (congrFun hc 0) 1
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at hh
    have hz : (d 0 - d 1) * C 0 1 = 0 := by linear_combination hh
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hdne)
  have hc10 : C 1 0 = 0 := by
    have hh := congrFun (congrFun hc 1) 0
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at hh
    have hz : (d 1 - d 0) * C 1 0 = 0 := by linear_combination hh
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hdne.symm)
  refine ⟨fun i => C i i, ?_⟩
  simp only [Matrix.conjTranspose_conjTranspose]; change C = diagonal (fun i => C i i)
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, hc01, hc10]
private lemma traceless_unitary_phase_reflection (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) (ht : Matrix.trace A = 0) :
    ∃ (c : ℂ) (H : Matrix (Fin 2) (Fin 2) ℂ),
      star c * c = 1 ∧ H.IsHermitian ∧ H * H = 1 ∧ A = c • H := by
  classical
  letI : IsStarNormal A := isStarNormal_of_mem_unitary hA
  obtain ⟨K, hK, d, hd⟩ := Matrix.exists_mem_unitaryGroup_star_mul_mul_eq_diagonal A
  have hKd : Kᴴ * A * K = diagonal d := hd
  have hKK : K * Kᴴ = 1 := hK.2
  have hKtK : Kᴴ * K = 1 := hK.1
  have hd10 : d 1 = -d 0 := by
    have hh : Matrix.trace (diagonal d) = 0 := by
      rw [← hKd, Matrix.trace_mul_cycle, hKK, Matrix.one_mul, ht]
    simp only [Matrix.trace_diagonal, Fin.sum_univ_two] at hh; linear_combination hh
  have hdunit : diagonal d ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [← hKd]; exact (Matrix.unitaryGroup (Fin 2) ℂ).mul_mem
      ((Matrix.unitaryGroup (Fin 2) ℂ).mul_mem (Unitary.star_mem hK) hA) hK
  have hc : star (d 0) * d 0 = 1 := congrFun (Matrix.diagonal_mem_unitary.mp hdunit).1 0
  open D5.S3.Quantum.FiniteDimensional in
    obtain ⟨_, _, hZh, _, hZsq⟩ := qubit_weyl_star
  let Z := D5.S3.Quantum.FiniteDimensional.qubitZ
  have hZherm : Z.IsHermitian := hZh
  have hZsquare : Z * Z = 1 := by simpa only [pow_two] using hZsq
  have hdiag : diagonal d = d 0 • Z := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal, Z, D5.S3.Quantum.FiniteDimensional.qubitZ, hd10]
  refine ⟨d 0, K * Z * Kᴴ, hc,
    Matrix.isHermitian_mul_mul_conjTranspose K hZherm, ?_, ?_⟩
  · calc
      _ = K * Z * (Kᴴ * K) * Z * Kᴴ := by simp only [Matrix.mul_assoc]
      _ = K * (Z * Z) * Kᴴ := by
        rw [hKtK, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hZsquare, Matrix.mul_one, hKK]
  · calc
      A = K * (Kᴴ * A * K) * Kᴴ := by
        symm
        calc
          _ = (K * Kᴴ) * A * (K * Kᴴ) := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [hKK, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by rw [hKd, hdiag, Matrix.mul_smul, Matrix.smul_mul]
private lemma pauli_of_two_signs (A : Matrix (Fin 2) (Fin 2) ℂ) (hsq : A * A = 1)
    (hZ : A * qubitZ = qubitZ * A ∨ A * qubitZ = -(qubitZ * A))
    (hX : A * qubitX = qubitX * A ∨ A * qubitX = -(qubitX * A)) :
    ∃ (c : ℂ) (p : Pauli), star c * c = 1 ∧ A = c • pauliMatrix p := by
  have hs := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hsq
  simp only [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
    Matrix.one_apply_eq] at hs
  have phase (c : ℂ) (hc : c ^ 2 = 1) : star c * c = 1 := by
    rcases sq_eq_one_iff.mp hc with rfl | rfl <;> simp
  rcases hZ with hZ | hZ
  · have hz01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hZ
    have hz10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) hZ
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, qubitZ] at hz01 hz10
    have h01 : A 0 1 = 0 := by linear_combination -(1 / 2 : ℂ) * hz01
    have h10 : A 1 0 = 0 := by linear_combination (1 / 2 : ℂ) * hz10
    have hc : (A 0 0) ^ 2 = 1 := by simpa [h01, h10, pow_two] using hs
    rcases hX with hX | hX
    · have hx := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hX
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, qubitX] at hx
      refine ⟨A 0 0, .I, phase _ hc, ?_⟩
      ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMatrix, h01, h10, hx]
    · have hx := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hX
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, qubitX] at hx
      refine ⟨A 0 0, .Z, phase _ hc, ?_⟩
      ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMatrix, qubitZ, h01, h10, hx]
  · have hz00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hZ
    have hz11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) hZ
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, qubitZ] at hz00 hz11
    have h00 : A 0 0 = 0 := by linear_combination (1 / 2 : ℂ) * hz00
    have h11 : A 1 1 = 0 := by linear_combination -(1 / 2 : ℂ) * hz11
    rcases hX with hX | hX
    · have hx := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hX
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, qubitX] at hx
      have hc : (A 0 1) ^ 2 = 1 := by simpa [h00, hx, pow_two] using hs
      refine ⟨A 0 1, .X, phase _ hc, ?_⟩
      ext i j; fin_cases i <;> fin_cases j <;> simp [pauliMatrix, qubitX, h00, h11, hx]
    · have hx := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hX
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, qubitX] at hx
      have hc : (Complex.I * A 0 1) ^ 2 = 1 := by
        calc
          _ = -(A 0 1 * A 0 1) := by rw [mul_pow, Complex.I_sq]; ring
          _ = 1 := by simpa [h00, hx, mul_neg] using hs
      refine ⟨Complex.I * A 0 1, .Y, phase _ hc, ?_⟩
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [pauliMatrix, qubitX, qubitZ, Matrix.mul_apply, Matrix.vecMul, dotProduct,
          Fin.sum_univ_two, h00, h11, hx, mul_assoc] <;> ring_nf <;> simp
private lemma nonscalar_reflection_frame (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.IsHermitian) (hsq : A * A = 1) (hn : ¬ ∃ c : ℂ, A = c • 1) :
    ∃ V ∈ Matrix.unitaryGroup (Fin 2) ℂ,
      V * A * Vᴴ = qubitZ ∨ V * A * Vᴴ = -qubitZ := by
  classical
  have hu : A ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    change Aᴴ * A = 1; rw [hA.eq, hsq]
  letI : IsStarNormal A := isStarNormal_of_mem_unitary hu
  obtain ⟨K, hK, d, hd⟩ := Matrix.exists_mem_unitaryGroup_star_mul_mul_eq_diagonal A
  have hKd : Kᴴ * A * K = diagonal d := hd
  have hKK : K * Kᴴ = 1 := hK.2
  have hKtK : Kᴴ * K = 1 := hK.1
  have hrec : A = K * diagonal d * Kᴴ := by
    rw [← hKd]; symm; calc
      _ = (K * Kᴴ) * A * (K * Kᴴ) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hKK, Matrix.one_mul, Matrix.mul_one]
  have hdeq : d 0 ≠ d 1 := by
    intro he; apply hn; refine ⟨d 0, ?_⟩
    have hh : diagonal d = d 0 • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, he]
    rw [hrec, hh, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hKK]
  have hd2 : diagonal d * diagonal d = 1 := by
    rw [← hKd]; calc
      _ = Kᴴ * A * (K * Kᴴ) * A * K := by simp only [Matrix.mul_assoc]
      _ = Kᴴ * (A * A) * K := by
        rw [hKK, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hsq, Matrix.mul_one, hKtK]
  have h0 : (d 0) ^ 2 = 1 := by
    simpa only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq,
      Matrix.one_apply_eq, pow_two] using congrArg (fun M => M 0 0) hd2
  have h1 : (d 1) ^ 2 = 1 := by
    simpa only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq,
      Matrix.one_apply_eq, pow_two] using congrArg (fun M => M 1 1) hd2
  have h10 : d 1 = -d 0 := by
    rcases sq_eq_one_iff.mp h0 with h0 | h0 <;>
      rcases sq_eq_one_iff.mp h1 with h1 | h1 <;> simp_all
  refine ⟨Kᴴ, Unitary.star_mem hK, ?_⟩
  simp only [Matrix.conjTranspose_conjTranspose]; rw [hKd]; rcases sq_eq_one_iff.mp h0 with h0 | h0
  · left
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, qubitZ, h0, h10]
  · right
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, qubitZ, h0, h10]
private lemma commuting_Z_reflection_X_sign (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hsq : A * A = 1) (hZ : A * qubitZ = qubitZ * A) :
    A * qubitX = qubitX * A ∨ A * qubitX = -(qubitX * A) := by
  have hz01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hZ
  have hz10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) hZ
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, qubitZ] at hz01 hz10
  have h01 : A 0 1 = 0 := by linear_combination -(1 / 2 : ℂ) * hz01
  have h10 : A 1 0 = 0 := by linear_combination (1 / 2 : ℂ) * hz10
  have h0 : (A 0 0) ^ 2 = 1 := by
    simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, h01, h10, pow_two] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hsq
  have h1 : (A 1 1) ^ 2 = 1 := by
    simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, h01, h10, pow_two] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) hsq
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (h0.trans h1.symm) with he | he
  · left
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, qubitX, h01, h10, he]
  · right
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, qubitX, h01, h10, he]
private lemma anticommuting_Z_reflection_frame (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.IsHermitian) (hsq : A * A = 1) (hZ : A * qubitZ = -(qubitZ * A)) :
    ∃ D ∈ Matrix.unitaryGroup (Fin 2) ℂ,
      D * qubitZ * Dᴴ = qubitZ ∧ D * A * Dᴴ = qubitX := by
  classical
  have hz00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hZ
  have hz11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) hZ
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, qubitZ] at hz00 hz11
  have h00 : A 0 0 = 0 := by linear_combination (1 / 2 : ℂ) * hz00
  have h11 : A 1 1 = 0 := by linear_combination -(1 / 2 : ℂ) * hz11
  have h10 : A 1 0 = star (A 0 1) := by
    simpa only [Matrix.conjTranspose_apply] using
      (congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) hA.eq).symm
  have hz : A 0 1 * star (A 0 1) = 1 := by
    simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, h00, h10] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hsq
  let d : Fin 2 → ℂ := ![1, A 0 1]
  have hd : diagonal d ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [Matrix.diagonal_mem_unitary, Pi.mem_unitary_iff]; intro i; fin_cases i
    · exact one_mem _
    · constructor
      · change star (A 0 1) * A 0 1 = 1; simpa only [mul_comm] using hz
      · change A 0 1 * star (A 0 1) = 1; exact hz
  refine ⟨diagonal d, hd, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, Matrix.conjTranspose_apply,
        d, qubitZ, mul_assoc] <;> exact hz
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, Matrix.conjTranspose_apply,
        d, qubitX, h00, h11, h10, mul_assoc] <;> exact hz
private lemma reflection_axes_two_pauli_frame {κ : Type*} (H : κ → Matrix (Fin 2) (Fin 2) ℂ)
    (hH : ∀ a, (H a).IsHermitian ∧ H a * H a = 1)
    (hs : ∀ a b, H a * H b = H b * H a ∨ H a * H b = -(H b * H a)) :
    ∃ V ∈ Matrix.unitaryGroup (Fin 2) ℂ, ∀ a,
      ((V * H a * Vᴴ) * qubitZ = qubitZ * (V * H a * Vᴴ) ∨
        (V * H a * Vᴴ) * qubitZ = -(qubitZ * (V * H a * Vᴴ))) ∧
      ((V * H a * Vᴴ) * qubitX = qubitX * (V * H a * Vᴴ) ∨
        (V * H a * Vᴴ) * qubitX = -(qubitX * (V * H a * Vᴴ))) := by
  classical
  by_cases hall : ∀ a, ∃ c : ℂ, H a = c • 1
  · refine ⟨1, one_mem _, ?_⟩
    intro a; obtain ⟨c, hc⟩ := hall a; constructor <;> left <;>
      simp only [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one, hc,
        Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  · obtain ⟨a₀, ha₀⟩ := not_forall.mp hall
    obtain ⟨V, hV, hVZ⟩ := nonscalar_reflection_frame (H a₀) (hH a₀).1 (hH a₀).2 ha₀
    let C := Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) ⟨V, hV⟩
    let A (a : κ) := V * H a * Vᴴ
    have hCA (a : κ) : C (H a) = A a := rfl
    have hA (a : κ) : (A a).IsHermitian ∧ A a * A a = 1 := by
      refine ⟨Matrix.isHermitian_mul_mul_conjTranspose V (hH a).1, ?_⟩
      change C (H a) * C (H a) = 1; rw [← map_mul, (hH a).2, map_one]
    have hsA (a b : κ) : A a * A b = A b * A a ∨ A a * A b = -(A b * A a) := by
      rcases hs a b with h | h
      · left
        simpa only [map_mul, hCA] using congrArg C h
      · right
        simpa only [map_mul, map_neg, hCA] using congrArg C h
    have hAZ (a : κ) : A a * qubitZ = qubitZ * A a ∨
        A a * qubitZ = -(qubitZ * A a) := by
      have hh := hsA a a₀
      rcases hVZ with h | h
      · change A a₀ = qubitZ at h; simpa only [h] using hh
      · change A a₀ = -qubitZ at h
        simpa only [h, mul_neg, neg_mul, neg_neg, neg_inj, neg_eq_iff_eq_neg] using hh
    by_cases hallZ : ∀ a, A a * qubitZ = qubitZ * A a
    · exact ⟨V, hV, fun a => ⟨Or.inl (hallZ a),
        commuting_Z_reflection_X_sign (A a) (hA a).2 (hallZ a)⟩⟩
    · obtain ⟨b, hb⟩ := not_forall.mp hallZ
      obtain ⟨D, hD, hDZ, hDX⟩ := anticommuting_Z_reflection_frame (A b) (hA b).1
        (hA b).2 ((hAZ b).resolve_left hb)
      let E := Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) ⟨D, hD⟩
      let B (a : κ) := D * A a * Dᴴ
      have hEB (a : κ) : E (A a) = B a := rfl
      have hEZ : E qubitZ = qubitZ := hDZ
      have hEX : E (A b) = qubitX := hDX
      have hBZ (a : κ) : B a * qubitZ = qubitZ * B a ∨
          B a * qubitZ = -(qubitZ * B a) := by
        rcases hAZ a with h | h
        · left
          simpa only [map_mul, hEB, hEZ] using congrArg E h
        · right
          simpa only [map_mul, map_neg, hEB, hEZ] using congrArg E h
      have hBX (a : κ) : B a * qubitX = qubitX * B a ∨
          B a * qubitX = -(qubitX * B a) := by
        rcases hsA a b with h | h
        · left
          simpa only [map_mul, hEX, hEB] using congrArg E h
        · right
          simpa only [map_mul, map_neg, hEX, hEB] using congrArg E h
      refine ⟨D * V, (Matrix.unitaryGroup (Fin 2) ℂ).mul_mem hD hV, ?_⟩
      intro a
      have he : (D * V) * H a * (D * V)ᴴ = B a := by
        dsimp only [B, A]; rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      rw [he]; exact ⟨hBZ a, hBX a⟩
private lemma reflection_axes_pauli_frame {κ : Type*} (H : κ → Matrix (Fin 2) (Fin 2) ℂ)
    (hH : ∀ a, (H a).IsHermitian ∧ H a * H a = 1)
    (hs : ∀ a b, H a * H b = H b * H a ∨ H a * H b = -(H b * H a)) :
    ∃ V ∈ Matrix.unitaryGroup (Fin 2) ℂ,
      ∃ (c : κ → ℂ) (p : κ → Pauli),
        (∀ a, star (c a) * c a = 1) ∧ (∀ a, V * H a * Vᴴ = c a • pauliMatrix (p a)) := by
  classical
  obtain ⟨V, hV, hv⟩ := reflection_axes_two_pauli_frame H hH hs
  have hsq (a : κ) : (V * H a * Vᴴ) * (V * H a * Vᴴ) = 1 := by
    calc
      _ = V * H a * (Vᴴ * V) * H a * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = V * (H a * H a) * Vᴴ := by
        rw [show Vᴴ * V = 1 from hV.1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [(hH a).2, Matrix.mul_one]; exact hV.2
  have hp (a : κ) := pauli_of_two_signs (V * H a * Vᴴ) (hsq a) (hv a).1 (hv a).2
  choose c p hc he using hp
  exact ⟨V, hV, c, p, hc, he⟩
private lemma pauli_site_frame {κ : Type*} (B : κ → Matrix (Fin 2) (Fin 2) ℂ)
    (hB : ∀ a, B a ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hs : ∀ a b, B a * B b = B b * B a ∨ B a * B b = -(B b * B a))
    (ht : ∀ a, (¬ ∃ c : ℂ, B a = c • 1) → Matrix.trace (B a) = 0) :
    ∃ V ∈ Matrix.unitaryGroup (Fin 2) ℂ,
      ∃ (c : κ → ℂ) (p : κ → Pauli),
        (∀ a, star (c a) * c a = 1) ∧ (∀ a, V * B a * Vᴴ = c a • pauliMatrix (p a)) := by
  classical
  have hnormalize (a : κ) : ∃ (c : ℂ) (H : Matrix (Fin 2) (Fin 2) ℂ),
      star c * c = 1 ∧ H.IsHermitian ∧ H * H = 1 ∧ B a = c • H := by
    by_cases ha : ∃ c : ℂ, B a = c • 1
    · obtain ⟨c, hc⟩ := ha
      have hu : diagonal (fun _ : Fin 2 => c) ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
        rw [← Matrix.smul_one_eq_diagonal, ← hc]; exact hB a
      refine ⟨c, 1, congrFun (Matrix.diagonal_mem_unitary.mp hu).1 0,
        Matrix.isHermitian_one, Matrix.one_mul _, hc⟩
    · exact traceless_unitary_phase_reflection (B a) (hB a) (ht a ha)
  choose c H hc hh hsq he using hnormalize
  have hcn (a : κ) : c a ≠ 0 := by
    intro hz; have hi := hc a; rw [hz, star_zero, zero_mul] at hi; exact zero_ne_one hi
  have hmul (a b : κ) : B a * B b = (c a * c b) • (H a * H b) := by
    rw [he a, he b, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hsign (a b : κ) : H a * H b = H b * H a ∨ H a * H b = -(H b * H a) := by
    have hn : c a * c b ≠ 0 := mul_ne_zero (hcn a) (hcn b)
    rcases hs a b with hab | hab
    · left
      apply (smul_right_injective (Matrix (Fin 2) (Fin 2) ℂ) hn)
      simpa only [hmul, mul_comm (c b) (c a)] using hab
    · right
      apply (smul_right_injective (Matrix (Fin 2) (Fin 2) ℂ) hn)
      simpa only [hmul, mul_comm (c b) (c a), smul_neg] using hab
  obtain ⟨V, hV, d, p, hd, hp⟩ := reflection_axes_pauli_frame H (fun a => ⟨hh a, hsq a⟩) hsign
  refine ⟨V, hV, fun a => c a * d a, p, ?_, ?_⟩
  · intro a; rw [star_mul]; calc
      _ = (star (c a) * c a) * (star (d a) * d a) := by ring
      _ = 1 := by rw [hc a, hd a, one_mul]
  · intro a; rw [he a, Matrix.mul_smul, Matrix.smul_mul, hp a, smul_smul]
lemma local_site_normal_form {κ : Type*} (B : κ → Matrix (Fin 2) (Fin 2) ℂ)
    (hB : ∀ a, B a ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hs : ∀ a b, B a * B b = B b * B a ∨ B a * B b = -(B b * B a)) :
    ∃ V ∈ Matrix.unitaryGroup (Fin 2) ℂ,
      (∀ a, ∃ d : Fin 2 → ℂ, V * B a * Vᴴ = diagonal d) ∨ (∃ (c : κ → ℂ) (p : κ → Pauli),
        (∀ a, star (c a) * c a = 1) ∧ (∀ a, V * B a * Vᴴ = c a • pauliMatrix (p a))) := by
  classical
  by_cases ht : ∃ a, (¬ ∃ c : ℂ, B a = c • 1) ∧ Matrix.trace (B a) ≠ 0
  · obtain ⟨a, hn, ht⟩ := ht
    obtain ⟨V, hV, hd⟩ := diagonal_site_basis (B a) B (hB a) hB ht hn (hs a)
    exact ⟨V, hV, Or.inl hd⟩
  · have htr : ∀ a, (¬ ∃ c : ℂ, B a = c • 1) → Matrix.trace (B a) = 0 := by
      intro a ha; by_contra hh; exact ht ⟨a, ha, hh⟩
    obtain ⟨V, hV, c, p, hc, hp⟩ := pauli_site_frame B hB hs htr
    exact ⟨V, hV, Or.inr ⟨c, p, hc, hp⟩⟩
end D5.S3.Quantum.Information.CommutingEncodingReflectionClass
