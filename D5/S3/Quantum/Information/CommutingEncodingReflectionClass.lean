/- GID: D5/S3/Quantum/Information/CommutingEncodingReflectionClass
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/CommutingEncodingReflectionClass
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Commuting product and reflection encodings give the same qubit state class. -/

import D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm
import D5.S3.Quantum.BlockNorm.EssentiallyHermitian
import D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
import Mathlib.Algebra.Group.AddChar

/-! Commuting qubit product encodings and their local-reflection replacements. -/

open scoped BigOperators
open Matrix
open D5.S3.Quantum.FiniteDimensional (qubitX qubitZ qubit_weyl_star)
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
open D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm (tensor_adj tensor_unitary)

namespace D5.S3.Quantum.Information.CommutingEncodingReflectionClass

/-- A complete orthonormal orbit under pairwise commuting product unitaries. -/
def IsCommutingProductEncoding {n : ℕ} (ψ : (Fin n → Fin 2) → ℂ)
    (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  (∀ a j, U a j ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧
  (∀ a b, tensorOp (U a) * tensorOp (U b) = tensorOp (U b) * tensorOp (U a)) ∧
  (∀ a b, ∑ x, star ((tensorOp (U a) *ᵥ ψ) x) * (tensorOp (U b) *ᵥ ψ) x =
    if a = b then 1 else 0)

/-- A commuting product encoding whose individual qubit factors are Hermitian involutions. -/
def IsCommutingReflectionEncoding {n : ℕ} (ψ : (Fin n → Fin 2) → ℂ)
    (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  IsCommutingProductEncoding ψ U ∧
  (∀ a j, (U a j).IsHermitian ∧ U a j * U a j = 1)

/-- Arbitrary local unitary factors give the same commuting encoding class as reflections. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ ψ : (Fin n → Fin 2) → ℂ,
    (∑ x, ‖ψ x‖ ^ 2 = 1) →
    ((∃ U, IsCommutingProductEncoding ψ U) ↔
      (∃ U, IsCommutingReflectionEncoding ψ U))

private lemma product_encoding_conjugate {n : ℕ}
    (ψ : (Fin n → Fin 2) → ℂ)
    (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : IsCommutingProductEncoding ψ U)
    (V : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hV : ∀ j, V j ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    IsCommutingProductEncoding (tensorOp V *ᵥ ψ)
      (fun a j => V j * U a j * (V j)ᴴ) := by
  classical
  let T := tensorOp V
  have hT := tensor_unitary V hV
  have hTtT : Tᴴ * T = 1 := hT.1
  let C := Unitary.conjStarAlgAut ℂ (Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) ⟨T, hT⟩
  have ht (a) : tensorOp (fun j => V j * U a j * (V j)ᴴ) = C (tensorOp (U a)) := by
    change tensorOp (fun j => V j * U a j * (V j)ᴴ) =
      tensorOp V * tensorOp (U a) * (tensorOp V)ᴴ
    rw [tensor_adj, tensor_mul, tensor_mul]
  have he (a) : tensorOp (fun j => V j * U a j * (V j)ᴴ) *ᵥ (T *ᵥ ψ) =
      T *ᵥ (tensorOp (U a) *ᵥ ψ) := by
    rw [ht]
    change (T * tensorOp (U a) * Tᴴ) *ᵥ (T *ᵥ ψ) = _
    simp only [← Matrix.mulVec_mulVec]
    rw [Matrix.mulVec_mulVec ψ Tᴴ T, hTtT, Matrix.one_mulVec]
  refine ⟨?_, ?_, ?_⟩
  · intro a j
    exact (Matrix.unitaryGroup (Fin 2) ℂ).mul_mem
      ((Matrix.unitaryGroup (Fin 2) ℂ).mul_mem (hV j) (hU.1 a j))
      (Unitary.star_mem (hV j))
  · intro a b
    simp only [ht, ← map_mul, hU.2.1 a b]
  · intro a b
    change star (tensorOp (fun j => V j * U a j * (V j)ᴴ) *ᵥ (T *ᵥ ψ)) ⬝ᵥ
      (tensorOp (fun j => V j * U b j * (V j)ᴴ) *ᵥ (T *ᵥ ψ)) = _
    rw [he a, he b]
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      hTtT, Matrix.vecMul_one]
    exact hU.2.2 a b

private lemma reflection_encoding_conjugate {n : ℕ}
    (ψ : (Fin n → Fin 2) → ℂ)
    (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : IsCommutingReflectionEncoding ψ U)
    (V : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hV : ∀ j, V j ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    IsCommutingReflectionEncoding (tensorOp V *ᵥ ψ)
      (fun a j => V j * U a j * (V j)ᴴ) := by
  refine ⟨product_encoding_conjugate ψ U hU.1 V hV, ?_⟩
  intro a j
  refine ⟨Matrix.isHermitian_mul_mul_conjTranspose (V j) (hU.2 a j).1, ?_⟩
  have hv : (V j)ᴴ * V j = 1 := (hV j).1
  calc
    _ = V j * U a j * ((V j)ᴴ * V j) * U a j * (V j)ᴴ := by
      simp only [Matrix.mul_assoc]
    _ = V j * (U a j * U a j) * (V j)ᴴ := by
      rw [hv, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [(hU.2 a j).2, Matrix.mul_one]; exact (hV j).2

private lemma tensor_factors_proportional {n : ℕ}
    (X Y : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (h : tensorOp X = tensorOp Y) (hne : tensorOp X ≠ 0) :
    ∀ j, ∃ c : ℂ, Y j = c • X j := by
  classical
  obtain ⟨x, y, hxy⟩ : ∃ x y, tensorOp X x y ≠ 0 := by
    by_contra! hz
    apply hne
    ext x y
    exact hz x y
  have hY : (∏ i, Y i (x i) (y i)) ≠ 0 := by
    change tensorOp Y x y ≠ 0
    rwa [← h]
  intro j
  have hrest : (∏ i ∈ Finset.univ.erase j, Y i (x i) (y i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ =>
      Finset.prod_ne_zero_iff.mp hY i (Finset.mem_univ i)
  have entry (Z : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (r t : Fin 2) :
      tensorOp Z (Function.update x j r) (Function.update y j t) =
        Z j r t * ∏ i ∈ Finset.univ.erase j, Z i (x i) (y i) := by
    dsimp only [tensorOp, Matrix.of_apply]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    simp only [Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi),
      Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  refine ⟨(∏ i ∈ Finset.univ.erase j, X i (x i) (y i)) /
    (∏ i ∈ Finset.univ.erase j, Y i (x i) (y i)), ?_⟩
  ext r t
  have he := congrFun (congrFun h (Function.update x j r)) (Function.update y j t)
  rw [entry, entry] at he
  change Y j r t = _ * X j r t
  rw [div_mul_eq_mul_div, eq_div_iff hrest, mul_comm _ (X j r t)]
  exact he.symm

private lemma local_commutation_signs {n : ℕ}
    (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ a j, U a j ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hc : ∀ a b, tensorOp (U a) * tensorOp (U b) =
      tensorOp (U b) * tensorOp (U a)) :
    ∀ a b j, U a j * U b j = U b j * U a j ∨
      U a j * U b j = -(U b j * U a j) := by
  classical
  intro a b j
  have hunit : tensorOp (fun i => U a i * U b i) ∈
      Matrix.unitaryGroup (Fin n → Fin 2) ℂ :=
    tensor_unitary _ fun i => (Matrix.unitaryGroup (Fin 2) ℂ).mul_mem (hU a i) (hU b i)
  have hne : tensorOp (fun i => U a i * U b i) ≠ 0 := by
    intro hz
    have hi := hunit.1
    rw [hz, star_zero, zero_mul] at hi
    exact zero_ne_one hi
  have heq : tensorOp (fun i => U a i * U b i) =
      tensorOp (fun i => U b i * U a i) := by
    simpa only [tensor_mul] using hc a b
  obtain ⟨c, he⟩ := tensor_factors_proportional _ _ heq hne j
  have hdet : (U a j * U b j).det ≠ 0 := by
    rw [Matrix.det_mul]
    exact mul_ne_zero (Matrix.det_ne_zero_of_left_inverse (hU a j).1)
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
    (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hB : ∀ a, B a ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (ht : Matrix.trace A ≠ 0) (hn : ¬ ∃ c : ℂ, A = c • 1)
    (hs : ∀ a, A * B a = B a * A ∨ A * B a = -(B a * A)) :
    ∃ V ∈ Matrix.unitaryGroup (Fin 2) ℂ,
      ∀ a, ∃ d : Fin 2 → ℂ, V * B a * Vᴴ = diagonal d := by
  classical
  letI : IsStarNormal A := isStarNormal_of_mem_unitary hA
  obtain ⟨K, hK, d, hd⟩ := Matrix.exists_mem_unitaryGroup_star_mul_mul_eq_diagonal A
  have hKd : Kᴴ * A * K = diagonal d := hd
  have hKK : K * Kᴴ = 1 := hK.2
  have hdne : d 0 ≠ d 1 := by
    intro heq
    apply hn
    refine ⟨d 0, ?_⟩
    have he : diagonal d = d 0 • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, heq]
    calc
      A = K * (Kᴴ * A * K) * Kᴴ := by
        symm
        calc
          _ = (K * Kᴴ) * A * (K * Kᴴ) := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [hKK, Matrix.one_mul, Matrix.mul_one]
      _ = K * (d 0 • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * Kᴴ := by rw [hKd, he]
      _ = _ := by rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hKK]
  refine ⟨Kᴴ, Unitary.star_mem hK, ?_⟩
  intro a
  let C := Kᴴ * B a * K
  have hm (X Y : Matrix (Fin 2) (Fin 2) ℂ) :
      (Kᴴ * X * K) * (Kᴴ * Y * K) = Kᴴ * (X * Y) * K := by
    calc
      _ = Kᴴ * X * (K * Kᴴ) * Y * K := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hKK, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hc : diagonal d * C = C * diagonal d := by
    rw [← hKd]
    dsimp only [C]
    rw [hm, hm, trace_nonzero_commutes A (B a) (hB a) ht (hs a)]
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
  simp only [Matrix.conjTranspose_conjTranspose]
  change C = diagonal (fun i => C i i)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, hc01, hc10]

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
    simp only [Matrix.trace_diagonal, Fin.sum_univ_two] at hh
    linear_combination hh
  have hdunit : diagonal d ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [← hKd]
    exact (Matrix.unitaryGroup (Fin 2) ℂ).mul_mem
      ((Matrix.unitaryGroup (Fin 2) ℂ).mul_mem (Unitary.star_mem hK) hA) hK
  have hc : star (d 0) * d 0 = 1 :=
    congrFun (Matrix.diagonal_mem_unitary.mp hdunit).1 0
  open D5.S3.Quantum.FiniteDimensional in
    obtain ⟨_, _, hZh, _, hZsq⟩ := qubit_weyl_star
  let Z := D5.S3.Quantum.FiniteDimensional.qubitZ
  have hZherm : Z.IsHermitian := hZh
  have hZsquare : Z * Z = 1 := by simpa only [pow_two] using hZsq
  have hdiag : diagonal d = d 0 • Z := by
    ext i j
    fin_cases i <;> fin_cases j <;>
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

private lemma pauli_of_two_signs (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hsq : A * A = 1)
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
      ext i j
      fin_cases i <;> fin_cases j <;> simp [pauliMatrix, h01, h10, hx]
    · have hx := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) hX
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, qubitX] at hx
      refine ⟨A 0 0, .Z, phase _ hc, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [pauliMatrix, qubitZ, h01, h10, hx]
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
      ext i j
      fin_cases i <;> fin_cases j <;> simp [pauliMatrix, qubitX, h00, h11, hx]
    · have hx := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hX
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, qubitX] at hx
      have hc : (Complex.I * A 0 1) ^ 2 = 1 := by
        calc
          _ = -(A 0 1 * A 0 1) := by rw [mul_pow, Complex.I_sq]; ring
          _ = 1 := by simpa [h00, hx, mul_neg] using hs
      refine ⟨Complex.I * A 0 1, .Y, phase _ hc, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [pauliMatrix, qubitX, qubitZ, Matrix.mul_apply, Matrix.vecMul, dotProduct,
          Fin.sum_univ_two, h00, h11, hx, mul_assoc] <;> ring_nf <;> simp

private lemma nonscalar_reflection_frame (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.IsHermitian) (hsq : A * A = 1) (hn : ¬ ∃ c : ℂ, A = c • 1) :
    ∃ V ∈ Matrix.unitaryGroup (Fin 2) ℂ,
      V * A * Vᴴ = qubitZ ∨ V * A * Vᴴ = -qubitZ := by
  classical
  have hu : A ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    change Aᴴ * A = 1
    rw [hA.eq, hsq]
  letI : IsStarNormal A := isStarNormal_of_mem_unitary hu
  obtain ⟨K, hK, d, hd⟩ := Matrix.exists_mem_unitaryGroup_star_mul_mul_eq_diagonal A
  have hKd : Kᴴ * A * K = diagonal d := hd
  have hKK : K * Kᴴ = 1 := hK.2
  have hKtK : Kᴴ * K = 1 := hK.1
  have hrec : A = K * diagonal d * Kᴴ := by
    rw [← hKd]
    symm
    calc
      _ = (K * Kᴴ) * A * (K * Kᴴ) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hKK, Matrix.one_mul, Matrix.mul_one]
  have hdeq : d 0 ≠ d 1 := by
    intro he
    apply hn
    refine ⟨d 0, ?_⟩
    have hh : diagonal d = d 0 • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, he]
    rw [hrec, hh, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hKK]
  have hd2 : diagonal d * diagonal d = 1 := by
    rw [← hKd]
    calc
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
  simp only [Matrix.conjTranspose_conjTranspose]
  rw [hKd]
  rcases sq_eq_one_iff.mp h0 with h0 | h0
  · left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, qubitZ, h0, h10]
  · right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, qubitZ, h0, h10]

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
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, qubitX, h01, h10, he]
  · right
    ext i j
    fin_cases i <;> fin_cases j <;>
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
    rw [Matrix.diagonal_mem_unitary, Pi.mem_unitary_iff]
    intro i
    fin_cases i
    · exact one_mem _
    · constructor
      · change star (A 0 1) * A 0 1 = 1
        simpa only [mul_comm] using hz
      · change A 0 1 * star (A 0 1) = 1
        exact hz
  refine ⟨diagonal d, hd, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, Matrix.conjTranspose_apply,
        d, qubitZ, mul_assoc] <;> exact hz
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, Matrix.conjTranspose_apply,
        d, qubitX, h00, h11, h10, mul_assoc] <;> exact hz

private lemma reflection_axes_two_pauli_frame {κ : Type*}
    (H : κ → Matrix (Fin 2) (Fin 2) ℂ)
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
    intro a
    obtain ⟨c, hc⟩ := hall a
    constructor <;> left <;>
      simp only [Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one, hc,
        Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  · obtain ⟨a₀, ha₀⟩ := not_forall.mp hall
    obtain ⟨V, hV, hVZ⟩ := nonscalar_reflection_frame (H a₀) (hH a₀).1 (hH a₀).2 ha₀
    let C := Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) ⟨V, hV⟩
    let A (a : κ) := V * H a * Vᴴ
    have hCA (a : κ) : C (H a) = A a := rfl
    have hA (a : κ) : (A a).IsHermitian ∧ A a * A a = 1 := by
      refine ⟨Matrix.isHermitian_mul_mul_conjTranspose V (hH a).1, ?_⟩
      change C (H a) * C (H a) = 1
      rw [← map_mul, (hH a).2, map_one]
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
      · change A a₀ = qubitZ at h
        simpa only [h] using hh
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
        dsimp only [B, A]
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
      rw [he]
      exact ⟨hBZ a, hBX a⟩

private lemma reflection_axes_pauli_frame {κ : Type*}
    (H : κ → Matrix (Fin 2) (Fin 2) ℂ)
    (hH : ∀ a, (H a).IsHermitian ∧ H a * H a = 1)
    (hs : ∀ a b, H a * H b = H b * H a ∨ H a * H b = -(H b * H a)) :
    ∃ V ∈ Matrix.unitaryGroup (Fin 2) ℂ,
      ∃ (c : κ → ℂ) (p : κ → Pauli),
        (∀ a, star (c a) * c a = 1) ∧
        (∀ a, V * H a * Vᴴ = c a • pauliMatrix (p a)) := by
  classical
  obtain ⟨V, hV, hv⟩ := reflection_axes_two_pauli_frame H hH hs
  have hsq (a : κ) : (V * H a * Vᴴ) * (V * H a * Vᴴ) = 1 := by
    calc
      _ = V * H a * (Vᴴ * V) * H a * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = V * (H a * H a) * Vᴴ := by
        rw [show Vᴴ * V = 1 from hV.1, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [(hH a).2, Matrix.mul_one]; exact hV.2
  have hp (a : κ) := pauli_of_two_signs (V * H a * Vᴴ) (hsq a) (hv a).1 (hv a).2
  choose c p hc he using hp
  exact ⟨V, hV, c, p, hc, he⟩

private lemma pauli_site_frame {κ : Type*}
    (B : κ → Matrix (Fin 2) (Fin 2) ℂ)
    (hB : ∀ a, B a ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hs : ∀ a b, B a * B b = B b * B a ∨ B a * B b = -(B b * B a))
    (ht : ∀ a, (¬ ∃ c : ℂ, B a = c • 1) → Matrix.trace (B a) = 0) :
    ∃ V ∈ Matrix.unitaryGroup (Fin 2) ℂ,
      ∃ (c : κ → ℂ) (p : κ → Pauli),
        (∀ a, star (c a) * c a = 1) ∧
        (∀ a, V * B a * Vᴴ = c a • pauliMatrix (p a)) := by
  classical
  have hnormalize (a : κ) : ∃ (c : ℂ) (H : Matrix (Fin 2) (Fin 2) ℂ),
      star c * c = 1 ∧ H.IsHermitian ∧ H * H = 1 ∧ B a = c • H := by
    by_cases ha : ∃ c : ℂ, B a = c • 1
    · obtain ⟨c, hc⟩ := ha
      have hu : diagonal (fun _ : Fin 2 => c) ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
        rw [← Matrix.smul_one_eq_diagonal, ← hc]
        exact hB a
      refine ⟨c, 1, congrFun (Matrix.diagonal_mem_unitary.mp hu).1 0,
        Matrix.isHermitian_one, Matrix.one_mul _, hc⟩
    · exact traceless_unitary_phase_reflection (B a) (hB a) (ht a ha)
  choose c H hc hh hsq he using hnormalize
  have hcn (a : κ) : c a ≠ 0 := by
    intro hz
    have hi := hc a
    rw [hz, star_zero, zero_mul] at hi
    exact zero_ne_one hi
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
  obtain ⟨V, hV, d, p, hd, hp⟩ :=
    reflection_axes_pauli_frame H (fun a => ⟨hh a, hsq a⟩) hsign
  refine ⟨V, hV, fun a => c a * d a, p, ?_, ?_⟩
  · intro a
    rw [star_mul]
    calc
      _ = (star (c a) * c a) * (star (d a) * d a) := by ring
      _ = 1 := by rw [hc a, hd a, one_mul]
  · intro a
    rw [he a, Matrix.mul_smul, Matrix.smul_mul, hp a, smul_smul]

private lemma local_site_normal_form {κ : Type*}
    (B : κ → Matrix (Fin 2) (Fin 2) ℂ)
    (hB : ∀ a, B a ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hs : ∀ a b, B a * B b = B b * B a ∨ B a * B b = -(B b * B a)) :
    ∃ V ∈ Matrix.unitaryGroup (Fin 2) ℂ,
      (∀ a, ∃ d : Fin 2 → ℂ, V * B a * Vᴴ = diagonal d) ∨
      (∃ (c : κ → ℂ) (p : κ → Pauli),
        (∀ a, star (c a) * c a = 1) ∧
        (∀ a, V * B a * Vᴴ = c a • pauliMatrix (p a))) := by
  classical
  by_cases ht : ∃ a, (¬ ∃ c : ℂ, B a = c • 1) ∧ Matrix.trace (B a) ≠ 0
  · obtain ⟨a, hn, ht⟩ := ht
    obtain ⟨V, hV, hd⟩ := diagonal_site_basis (B a) B (hB a) hB ht hn (hs a)
    exact ⟨V, hV, Or.inl hd⟩
  · have htr : ∀ a, (¬ ∃ c : ℂ, B a = c • 1) → Matrix.trace (B a) = 0 := by
      intro a ha
      by_contra hh
      exact ht ⟨a, ha, hh⟩
    obtain ⟨V, hV, c, p, hc, hp⟩ := pauli_site_frame B hB hs htr
    exact ⟨V, hV, Or.inr ⟨c, p, hc, hp⟩⟩

private def pauli_symbol (p : Pauli) : ZMod 2 × ZMod 2 :=
  let b := D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.bellInput p
  (b.2, b.1)

private def word_symbol {n : ℕ} (p : Fin n → Pauli) :
    (Fin n → ZMod 2) × (Fin n → ZMod 2) :=
  (fun j => (pauli_symbol (p j)).1, fun j => (pauli_symbol (p j)).2)

private lemma finite_isotropic_extension {n : ℕ}
    (B : LinearMap.BilinForm (ZMod 2) ((Fin n → ZMod 2) × (Fin n → ZMod 2)))
    (hAlt : B.IsAlt) (hNd : B.Nondegenerate)
    (S : Submodule (ZMod 2) ((Fin n → ZMod 2) × (Fin n → ZMod 2)))
    (hS : ∀ u ∈ S, ∀ v ∈ S, B u v = 0) :
    ∃ L : Submodule (ZMod 2) ((Fin n → ZMod 2) × (Fin n → ZMod 2)),
      S ≤ L ∧ (∀ u ∈ L, ∀ v ∈ L, B u v = 0) ∧ Module.finrank (ZMod 2) L = n := by
  classical
  obtain ⟨L, hSL, hmax⟩ := Finite.exists_le_maximal
    (p := fun L : Submodule (ZMod 2) ((Fin n → ZMod 2) × (Fin n → ZMod 2)) =>
      ∀ u ∈ L, ∀ v ∈ L, B u v = 0) hS
  have hL := hmax.1
  have hperp : B.orthogonal L = L := by
    apply le_antisymm
    · intro x hx
      have hT : ∀ u ∈ L ⊔ Submodule.span (ZMod 2) {x},
          ∀ v ∈ L ⊔ Submodule.span (ZMod 2) {x}, B u v = 0 := by
        intro u hu v hv
        obtain ⟨u, huL, u', hu', rfl⟩ := Submodule.mem_sup.mp hu
        obtain ⟨v, hvL, v', hv', rfl⟩ := Submodule.mem_sup.mp hv
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu'
        obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hv'
        have hxu : B x v = 0 := (hAlt.eq_iff).mp (hx v hvL)
        simp [map_add, hL u huL v hvL, hx u huL, hxu, hAlt.self_eq_zero]
      apply hmax.2 hT le_sup_left
      exact Submodule.mem_sup.mpr
        ⟨0, L.zero_mem, x, Submodule.mem_span_singleton_self x, zero_add x⟩
    · intro x hx y hy
      exact hL y hy x hx
  have hd := B.finrank_orthogonal hNd L
  rw [hperp] at hd
  have hE : Module.finrank (ZMod 2) ((Fin n → ZMod 2) × (Fin n → ZMod 2)) = n + n := by
    simp [Module.finrank_prod]
  rw [hE] at hd
  exact ⟨L, hSL, hL, by omega⟩

private lemma diagonal_on_span {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Matrix ι ι ℂ) (s : Set (Matrix ι ι ℂ))
    (hs : ∀ A ∈ s, (Fᴴ * A * F).IsDiag)
    (A : Matrix ι ι ℂ) (hA : A ∈ Submodule.span ℂ s) :
    (Fᴴ * A * F).IsDiag := by
  induction hA using Submodule.span_induction with
  | mem A hA => exact hs A hA
  | zero => simpa only [Matrix.mul_zero, Matrix.zero_mul] using
      (Matrix.isDiag_zero : (0 : Matrix ι ι ℂ).IsDiag)
  | add A B _ _ hA hB =>
      simpa only [Matrix.mul_add, Matrix.add_mul] using hA.add hB
  | smul c A _ hA =>
      simpa only [Matrix.mul_smul, Matrix.smul_mul] using hA.smul c

private lemma local_forms_isotropic_span {n : ℕ}
    (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ a j, U a j ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hc : ∀ a b, tensorOp (U a) * tensorOp (U b) =
      tensorOp (U b) * tensorOp (U a))
    (V : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hV : ∀ j, V j ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hsites : ∀ j,
      (∀ a, ∃ d : Fin 2 → ℂ, V j * U a j * (V j)ᴴ = diagonal d) ∨
      (∃ (c : Fin (2 ^ n) → ℂ) (p : Fin (2 ^ n) → Pauli),
        (∀ a, star (c a) * c a = 1) ∧
        (∀ a, V j * U a j * (V j)ᴴ = c a • pauliMatrix (p a)))) :
    ∃ (B : LinearMap.BilinForm (ZMod 2) ((Fin n → ZMod 2) × (Fin n → ZMod 2)))
      (S : Submodule (ZMod 2) ((Fin n → ZMod 2) × (Fin n → ZMod 2))),
      B.IsAlt ∧ B.Nondegenerate ∧
      (∀ u v, B u v = BinaryLagrangianGraphForm.sp u v) ∧
      (∀ u ∈ S, ∀ v ∈ S, B u v = 0) ∧
      (∀ a, tensorOp (fun j => V j * U a j * (V j)ᴴ) ∈
        Submodule.span ℂ (wordOp '' {p | word_symbol p ∈ S})) := by
  sorry

private def binary_character {n : ℕ} (x : Fin n → Fin 2) :
    AddChar (Fin n → Fin 2) ℂ where
  toFun a := ∏ j, (-1 : ℂ) ^ ((a j).val * (x j).val)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    change (-1 : ℂ) ^ (((a j + b j) : Fin 2).val * (x j).val) = _
    generalize a j = r
    generalize b j = t
    generalize x j = z
    fin_cases r <;> fin_cases t <;> fin_cases z <;> norm_num

private lemma binary_character_frame {n : ℕ}
    (H : (Fin n → Fin 2) → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (hH : ∀ a, (H a).IsHermitian)
    (hmul : ∀ a b, H (a + b) = H a * H b)
    (htrace : ∀ a, Matrix.trace (H a) = if a = 0 then (2 ^ n : ℂ) else 0) :
    ∃ F : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ,
      F ∈ Matrix.unitaryGroup (Fin n → Fin 2) ℂ ∧
      ∀ a, Fᴴ * H a * F =
        diagonal (fun x => ∏ j, (-1 : ℂ) ^ ((a j).val * (x j).val)) := by
  classical
  let χ (a x : Fin n → Fin 2) : ℂ := binary_character x a
  have hχadd (a b x : Fin n → Fin 2) : χ (a + b) x = χ a x * χ b x :=
    (binary_character x).map_add_eq_mul a b
  have hχstar (a x : Fin n → Fin 2) : star (χ a x) = χ a x := by simp [χ, binary_character]
  have haab (a b : Fin n → Fin 2) : a + (a + b) = b := by
    funext j
    change (a j + (a j + b j) : Fin 2) = b j
    generalize a j = r
    generalize b j = t
    fin_cases r <;> fin_cases t <;> decide
  let P (x : Fin n → Fin 2) := ∑ a, χ a x • H a
  have hPeig (a x : Fin n → Fin 2) : H a * P x = χ a x • P x := by
    let e : (Fin n → Fin 2) ≃ (Fin n → Fin 2) :=
      ⟨fun b => a + b, fun b => a + b, haab a, haab a⟩
    calc
      _ = ∑ b, χ b x • H (a + b) := by
        simp only [P, Matrix.mul_sum, Matrix.mul_smul, ← hmul]
      _ = ∑ b, χ (a + b) x • H b := by
        apply Fintype.sum_equiv e
        intro b
        change χ b x • H (a + b) = χ (a + (a + b)) x • H (a + b)
        rw [haab]
      _ = _ := by simp only [hχadd, mul_smul, P, Finset.smul_sum]
  have hPne (x : Fin n → Fin 2) : P x ≠ 0 := by
    have ht : Matrix.trace (P x) = (2 ^ n : ℂ) := by
      simp [P, Matrix.trace_sum, Matrix.trace_smul, htrace, χ, binary_character]
    intro hz
    rw [hz, Matrix.trace_zero] at ht
    exact (pow_ne_zero n (by norm_num : (2 : ℂ) ≠ 0)) ht.symm
  have hentry (x : Fin n → Fin 2) : ∃ r k, P x r k ≠ 0 := by
    by_contra! hz
    apply hPne x
    ext r k
    exact hz r k
  choose r k hentry using hentry
  let v (x : Fin n → Fin 2) : EuclideanSpace ℂ (Fin n → Fin 2) :=
    WithLp.toLp 2 (fun t => P x t (k x))
  have hv (x) : v x ≠ 0 := by
    intro hz
    apply hentry x
    have hh := congrArg (fun w : EuclideanSpace ℂ (Fin n → Fin 2) => w (r x)) hz
    exact hh
  let f (x : Fin n → Fin 2) : EuclideanSpace ℂ (Fin n → Fin 2) :=
    (‖v x‖ : ℂ)⁻¹ • v x
  have hnorm (x) : ‖f x‖ = 1 := norm_smul_inv_norm (hv x)
  have hraw (a x : Fin n → Fin 2) :
      H a *ᵥ (fun t => P x t (k x)) = χ a x • (fun t => P x t (k x)) := by
    funext t
    exact congrArg (fun M : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ => M t (k x))
      (hPeig a x)
  have heig (a x : Fin n → Fin 2) :
      H a *ᵥ (f x) = χ a x • (f x : (Fin n → Fin 2) → ℂ) := by
    change H a *ᵥ ((‖v x‖ : ℂ)⁻¹ • (fun t => P x t (k x))) =
      χ a x • ((‖v x‖ : ℂ)⁻¹ • (fun t => P x t (k x)))
    rw [Matrix.mulVec_smul, hraw, smul_smul, smul_smul, mul_comm]
  have hsingle (x : Fin n → Fin 2) (j : Fin n) :
      χ (Pi.single j 1) x = (-1 : ℂ) ^ (x j).val := by
    change (∏ i, (-1 : ℂ) ^ (((Pi.single j 1 : Fin n → Fin 2) i).val *
      (x i).val)) = _
    rw [Finset.prod_eq_single j]
    · simp [Pi.single_apply]
    · intro i _ hij
      simp [Pi.single_apply, hij, Ne.symm hij]
    · simp
  have horth (x y : Fin n → Fin 2) (hxy : x ≠ y) :
      (∑ t, star (f x t) * f y t) = 0 := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hxy
    let a : Fin n → Fin 2 := Pi.single j 1
    have hne : χ a y ≠ χ a x := by
      rw [hsingle, hsingle]
      generalize hx : x j = r at *
      generalize hy : y j = t at *
      fin_cases r <;> fin_cases t <;> norm_num at *
    have hh : star (f x : (Fin n → Fin 2) → ℂ) ⬝ᵥ (H a *ᵥ f y) =
        star (H a *ᵥ f x) ⬝ᵥ (f y) := by
      rw [Matrix.star_mulVec, (hH a).eq, Matrix.dotProduct_mulVec]
    rw [heig, heig, star_smul, smul_dotProduct, dotProduct_smul, hχstar] at hh
    have hz : (χ a y - χ a x) * (∑ t, star (f x t) * f y t) = 0 := by
      change (χ a y - χ a x) * (star (f x : (Fin n → Fin 2) → ℂ) ⬝ᵥ f y) = 0
      linear_combination hh
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)
  have hself (x : Fin n → Fin 2) : (∑ t, star (f x t) * f x t) = 1 := by
    have hh : inner ℂ (f x) (f x) = 1 := by
      simp [inner_self_eq_norm_sq_to_K, hnorm]
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply,
      mul_comm] using hh
  let F : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ := fun t x => f x t
  have hF : F ∈ Matrix.unitaryGroup (Fin n → Fin 2) ℂ := by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    ext x y
    change (∑ t, star (f x t) * f y t) = if x = y then 1 else 0
    by_cases hxy : x = y
    · subst y
      simpa using hself x
    · simpa [hxy] using horth x y hxy
  refine ⟨F, hF, ?_⟩
  intro a
  have hHF : H a * F = F * diagonal (χ a) := by
    ext t x
    rw [Matrix.mul_diagonal]
    change (H a *ᵥ (f x)) t = f x t * χ a x
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using congrFun (heig a x) t
  calc
    _ = Fᴴ * (H a * F) := Matrix.mul_assoc _ _ _
    _ = Fᴴ * (F * diagonal (χ a)) := by rw [hHF]
    _ = (Fᴴ * F) * diagonal (χ a) := (Matrix.mul_assoc _ _ _).symm
    _ = _ := by rw [show Fᴴ * F = 1 from hF.1, Matrix.one_mul]; rfl

private lemma hermitian_phased_pauli_reflections {n : ℕ} (hn : 1 ≤ n)
    (c : ℂ) (p : Fin n → Pauli) (hc : star c * c = 1)
    (hh : (c • wordOp p).IsHermitian) :
    ∃ R : Fin n → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ j, (R j).IsHermitian ∧ R j * R j = 1) ∧ tensorOp R = c • wordOp p := by
  classical
  let j₀ : Fin n := ⟨0, by omega⟩
  have hw : (wordOp p)ᴴ = wordOp p :=
    D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.word_hermitian p
  have hwne : wordOp p ≠ 0 :=
    Units.ne_zero
      (D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.wordUnit p)
  have hcs : star c = c := by
    apply smul_left_injective ℂ hwne
    simpa only [Matrix.conjTranspose_smul, hw] using hh.eq
  have hsign : c = 1 ∨ c = -1 := by
    apply sq_eq_one_iff.mp
    simpa only [hcs, pow_two] using hc
  have hpauli (q : Pauli) : (pauliMatrix q).IsHermitian ∧ pauliMatrix q * pauliMatrix q = 1 := by
    refine ⟨D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.pauli_hermitian q,
      ?_⟩
    rw [D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.letter_mul]
    cases q <;>
      simp [D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.letterPhase,
        D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation.letterProduct,
        pauliMatrix]
  refine ⟨fun j => (if j = j₀ then c else 1) • pauliMatrix (p j), ?_, ?_⟩
  · intro j
    dsimp only
    have hs : (if j = j₀ then c else 1) = 1 ∨ (if j = j₀ then c else 1) = -1 := by
      split_ifs <;> simp_all
    rcases hs with hs | hs
    · rw [hs, one_smul]
      exact hpauli (p j)
    · rw [hs, neg_one_smul]
      exact ⟨(hpauli (p j)).1.neg, by simpa only [neg_mul_neg] using (hpauli (p j)).2⟩
  · rw [D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm.tensor_smul]
    have hp : (∏ j : Fin n, if j = j₀ then c else 1) = c := by simp
    rw [hp]
    rfl

private lemma lagrangian_phased_representation {n : ℕ}
    (L : Submodule (ZMod 2) ((Fin n → ZMod 2) × (Fin n → ZMod 2)))
    (hL : ∀ u ∈ L, ∀ v ∈ L, BinaryLagrangianGraphForm.sp u v = 0)
    (hdim : Module.finrank (ZMod 2) L = n) :
    ∃ (H : (Fin n → Fin 2) → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
      (c : (Fin n → Fin 2) → ℂ) (p : (Fin n → Fin 2) → Fin n → Pauli),
      (∀ a, star (c a) * c a = 1) ∧
      (∀ a, H a = c a • wordOp (p a)) ∧
      (∀ a, (H a).IsHermitian) ∧
      (∀ a b, H (a + b) = H a * H b) ∧
      (∀ a, Matrix.trace (H a) = if a = 0 then (2 ^ n : ℂ) else 0) ∧
      (∀ p, word_symbol p ∈ L → wordOp p ∈ Submodule.span ℂ (Set.range H)) := by
  sorry

private lemma lagrangian_reflection_representation {n : ℕ} (hn : 1 ≤ n)
    (L : Submodule (ZMod 2) ((Fin n → ZMod 2) × (Fin n → ZMod 2)))
    (hL : ∀ u ∈ L, ∀ v ∈ L, BinaryLagrangianGraphForm.sp u v = 0)
    (hdim : Module.finrank (ZMod 2) L = n) :
    ∃ R : (Fin n → Fin 2) → Fin n → Matrix (Fin 2) (Fin 2) ℂ,
      (∀ a j, (R a j).IsHermitian ∧ R a j * R a j = 1) ∧
      (∀ a b, tensorOp (R (a + b)) = tensorOp (R a) * tensorOp (R b)) ∧
      (∀ a, Matrix.trace (tensorOp (R a)) = if a = 0 then (2 ^ n : ℂ) else 0) ∧
      (∀ p, word_symbol p ∈ L →
        wordOp p ∈ Submodule.span ℂ (Set.range (fun a => tensorOp (R a)))) := by
  classical
  obtain ⟨H, c, p, hc, he, hH, hmul, htrace, hspan⟩ :=
    lagrangian_phased_representation L hL hdim
  have hex (a : Fin n → Fin 2) :
      ∃ R : Fin n → Matrix (Fin 2) (Fin 2) ℂ,
        (∀ j, (R j).IsHermitian ∧ R j * R j = 1) ∧ tensorOp R = H a := by
    rw [he a]
    exact hermitian_phased_pauli_reflections hn (c a) (p a) (hc a) (by rw [← he a]; exact hH a)
  choose R hR hRop using hex
  refine ⟨R, hR, ?_, ?_, ?_⟩
  · intro a b
    simpa only [hRop] using hmul a b
  · intro a
    simpa only [hRop] using htrace a
  · intro p hp
    simpa only [hRop] using hspan p hp

private lemma lagrangian_character_frame {n : ℕ} (hn : 1 ≤ n)
    (L : Submodule (ZMod 2) ((Fin n → ZMod 2) × (Fin n → ZMod 2)))
    (hL : ∀ u ∈ L, ∀ v ∈ L, BinaryLagrangianGraphForm.sp u v = 0)
    (hdim : Module.finrank (ZMod 2) L = n) :
    ∃ (F : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
      (R : (Fin n → Fin 2) → Fin n → Matrix (Fin 2) (Fin 2) ℂ),
      F ∈ Matrix.unitaryGroup (Fin n → Fin 2) ℂ ∧
      (∀ a j, (R a j).IsHermitian ∧ R a j * R a j = 1) ∧
      (∀ a, Fᴴ * tensorOp (R a) * F =
        diagonal (fun x => ∏ j, (-1 : ℂ) ^ ((a j).val * (x j).val))) ∧
      (∀ p, word_symbol p ∈ L → (Fᴴ * wordOp p * F).IsDiag) := by
  classical
  obtain ⟨R, hR, hmul, htrace, hspan⟩ := lagrangian_reflection_representation hn L hL hdim
  have hH (a) : (tensorOp (R a)).IsHermitian := by
    change (tensorOp (R a))ᴴ = tensorOp (R a)
    rw [tensor_adj]
    congr 1
    funext j
    exact (hR a j).1.eq
  obtain ⟨F, hF, he⟩ := binary_character_frame (fun a => tensorOp (R a)) hH hmul htrace
  refine ⟨F, R, hF, hR, he, ?_⟩
  intro p hp
  apply diagonal_on_span F (Set.range (fun a => tensorOp (R a))) ?_ _ (hspan p hp)
  rintro A ⟨a, rfl⟩
  rw [he a]
  exact Matrix.isDiag_diagonal _

private lemma stabilizer_frame_of_site_normal_forms {n : ℕ} (hn : 1 ≤ n)
    (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ a j, U a j ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hc : ∀ a b, tensorOp (U a) * tensorOp (U b) =
      tensorOp (U b) * tensorOp (U a))
    (V : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hV : ∀ j, V j ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hsites : ∀ j,
      (∀ a, ∃ d : Fin 2 → ℂ, V j * U a j * (V j)ᴴ = diagonal d) ∨
      (∃ (c : Fin (2 ^ n) → ℂ) (p : Fin (2 ^ n) → Pauli),
        (∀ a, star (c a) * c a = 1) ∧
        (∀ a, V j * U a j * (V j)ᴴ = c a • pauliMatrix (p a)))) :
    ∃ (F : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
      (eig : Fin (2 ^ n) → (Fin n → Fin 2) → ℂ)
      (R : (Fin n → Fin 2) → Fin n → Matrix (Fin 2) (Fin 2) ℂ),
      F ∈ Matrix.unitaryGroup (Fin n → Fin 2) ℂ ∧
      (∀ a x, star (eig a x) * eig a x = 1) ∧
      (∀ a, Fᴴ * tensorOp (fun j => V j * U a j * (V j)ᴴ) * F = diagonal (eig a)) ∧
      (∀ a j, (R a j).IsHermitian ∧ R a j * R a j = 1) ∧
      (∀ a, Fᴴ * tensorOp (R a) * F =
        diagonal (fun x => ∏ j, (-1 : ℂ) ^ ((a j).val * (x j).val))) := by
  classical
  obtain ⟨B, S, hAlt, hNd, hB, hS, hspan⟩ :=
    local_forms_isotropic_span U hU hc V hV hsites
  obtain ⟨L, hSL, hL, hdim⟩ := finite_isotropic_extension B hAlt hNd S hS
  have hsp : ∀ u ∈ L, ∀ v ∈ L, BinaryLagrangianGraphForm.sp u v = 0 := by
    intro u hu v hv
    rw [← hB]
    exact hL u hu v hv
  obtain ⟨F, R, hF, hR, hRd, hdiag⟩ := lagrangian_character_frame hn L hsp hdim
  have hd (a) : (Fᴴ * tensorOp (fun j => V j * U a j * (V j)ᴴ) * F).IsDiag := by
    refine diagonal_on_span F (wordOp '' {p : Fin n → Pauli | word_symbol p ∈ L})
      ?_ _ ?_
    · rintro A ⟨p, hp, rfl⟩
      exact hdiag p hp
    · have hincl : wordOp '' {p : Fin n → Pauli | word_symbol p ∈ S} ⊆
          wordOp '' {p : Fin n → Pauli | word_symbol p ∈ L} :=
        Set.image_mono (fun p hp => hSL hp)
      exact Submodule.span_mono hincl (hspan a)
  let eig (a : Fin (2 ^ n)) :=
    Matrix.diag (Fᴴ * tensorOp (fun j => V j * U a j * (V j)ᴴ) * F)
  have he (a) : Fᴴ * tensorOp (fun j => V j * U a j * (V j)ᴴ) * F =
      diagonal (eig a) := (hd a).diagonal_diag.symm
  refine ⟨F, eig, R, hF, ?_, he, hR, hRd⟩
  intro a x
  have hu : tensorOp (fun j => V j * U a j * (V j)ᴴ) ∈
      Matrix.unitaryGroup (Fin n → Fin 2) ℂ := by
    apply tensor_unitary
    intro j
    exact (Matrix.unitaryGroup (Fin 2) ℂ).mul_mem
      ((Matrix.unitaryGroup (Fin 2) ℂ).mul_mem (hV j) (hU a j))
      (Unitary.star_mem (hV j))
  have hdu : diagonal (eig a) ∈ Matrix.unitaryGroup (Fin n → Fin 2) ℂ := by
    rw [← he a]
    exact (Matrix.unitaryGroup (Fin n → Fin 2) ℂ).mul_mem
      ((Matrix.unitaryGroup (Fin n → Fin 2) ℂ).mul_mem (Unitary.star_mem hF) hu) hF
  exact congrFun (Matrix.diagonal_mem_unitary.mp hdu).1 x

private lemma spectral_frame_of_local_signs {n : ℕ} (hn : 1 ≤ n)
    (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : ∀ a j, U a j ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hc : ∀ a b, tensorOp (U a) * tensorOp (U b) =
      tensorOp (U b) * tensorOp (U a))
    (hs : ∀ a b j, U a j * U b j = U b j * U a j ∨
      U a j * U b j = -(U b j * U a j)) :
    ∃ (V : Fin n → Matrix (Fin 2) (Fin 2) ℂ)
      (F : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
      (eig : Fin (2 ^ n) → (Fin n → Fin 2) → ℂ)
      (R : (Fin n → Fin 2) → Fin n → Matrix (Fin 2) (Fin 2) ℂ),
      (∀ j, V j ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧
      F ∈ Matrix.unitaryGroup (Fin n → Fin 2) ℂ ∧
      (∀ a x, star (eig a x) * eig a x = 1) ∧
      (∀ a, Fᴴ * tensorOp (fun j => V j * U a j * (V j)ᴴ) * F = diagonal (eig a)) ∧
      (∀ a j, (R a j).IsHermitian ∧ R a j * R a j = 1) ∧
      (∀ a, Fᴴ * tensorOp (R a) * F =
        diagonal (fun x => ∏ j, (-1 : ℂ) ^ ((a j).val * (x j).val))) := by
  classical
  have hsite (j : Fin n) := local_site_normal_form (fun a => U a j)
    (fun a => hU a j) (fun a b => hs a b j)
  choose V hV hv using hsite
  obtain ⟨F, eig, R, hF, heig, hd, hR, hRd⟩ :=
    stabilizer_frame_of_site_normal_forms hn U hU hc V hV hv
  exact ⟨V, F, eig, R, hV, hF, heig, hd, hR, hRd⟩

private lemma uniform_weights {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℂ) (eig : ι → ι → ℂ)
    (heig : ∀ a x, star (eig a x) * eig a x = 1)
    (ho : ∀ a b, ∑ x, star (c x * eig a x) * (c x * eig b x) =
      if a = b then 1 else 0) :
    ∀ x, (Fintype.card ι : ℂ) * (star (c x) * c x) = 1 := by
  classical
  let M : Matrix ι ι ℂ := fun x a => c x * eig a x
  have hcol : Mᴴ * M = 1 := by
    ext a b
    exact ho a b
  have hrow : M * Mᴴ = 1 := mul_eq_one_comm.mp hcol
  intro x
  have hx := congrFun (congrFun hrow x) x
  rw [Matrix.one_apply_eq] at hx
  change (∑ a, (c x * eig a x) * star (c x * eig a x)) = 1 at hx
  have he (a : ι) : (c x * eig a x) * star (c x * eig a x) = star (c x) * c x := by
    rw [star_mul]
    calc
      _ = (star (c x) * c x) * (star (eig a x) * eig a x) := by ring
      _ = _ := by rw [heig a x, mul_one]
  simpa only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hx

private lemma flat_of_diagonal_encoding {n : ℕ}
    (ψ : (Fin n → Fin 2) → ℂ)
    (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : IsCommutingProductEncoding ψ U)
    (F : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (hF : F ∈ Matrix.unitaryGroup (Fin n → Fin 2) ℂ)
    (eig : Fin (2 ^ n) → (Fin n → Fin 2) → ℂ)
    (heig : ∀ a x, star (eig a x) * eig a x = 1)
    (hd : ∀ a, Fᴴ * tensorOp (U a) * F = diagonal (eig a)) :
    ∀ x, (2 ^ n : ℂ) * (star ((Fᴴ *ᵥ ψ) x) * (Fᴴ *ᵥ ψ) x) = 1 := by
  classical
  let e : (Fin n → Fin 2) ≃ Fin (2 ^ n) :=
    Fintype.equivFinOfCardEq (by simp [Fintype.card_fun])
  let c := Fᴴ *ᵥ ψ
  have hFF : F * Fᴴ = 1 := hF.2
  have he (a : Fin (2 ^ n)) :
      Fᴴ *ᵥ (tensorOp (U a) *ᵥ ψ) = fun x => c x * eig a x := by
    calc
      _ = (Fᴴ * tensorOp (U a) * F) *ᵥ c := by
        dsimp only [c]
        simp only [← Matrix.mulVec_mulVec]
        rw [Matrix.mulVec_mulVec ψ F Fᴴ, hFF, Matrix.one_mulVec]
      _ = _ := by
        rw [hd a]
        ext x
        simp [Matrix.mulVec, dotProduct, Matrix.diagonal, mul_comm]
  have hp (v w : (Fin n → Fin 2) → ℂ) :
      (∑ x, star ((Fᴴ *ᵥ v) x) * (Fᴴ *ᵥ w) x) = ∑ x, star (v x) * w x := by
    change star (Fᴴ *ᵥ v) ⬝ᵥ (Fᴴ *ᵥ w) = star v ⬝ᵥ w
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      Matrix.conjTranspose_conjTranspose, hFF, Matrix.vecMul_one]
  have hw := uniform_weights c (fun a => eig (e a)) (fun a x => heig (e a) x) (by
    intro a b
    calc
      _ = ∑ x, star ((Fᴴ *ᵥ (tensorOp (U (e a)) *ᵥ ψ)) x) *
          (Fᴴ *ᵥ (tensorOp (U (e b)) *ᵥ ψ)) x := by rw [he, he]
      _ = if e a = e b then 1 else 0 := (hp _ _).trans (hU.2.2 (e a) (e b))
      _ = _ := by simp only [e.injective.eq_iff])
  simpa [c, Fintype.card_fun] using hw

private lemma character_orthogonality {n : ℕ} (a b : Fin n → Fin 2) :
    (∑ x : Fin n → Fin 2,
      (∏ j, (-1 : ℂ) ^ ((a j).val * (x j).val)) *
        (∏ j, (-1 : ℂ) ^ ((b j).val * (x j).val))) =
      if a = b then (2 ^ n : ℂ) else 0 := by
  classical
  let ψ : AddChar (Fin n → Fin 2) ℂ := binary_character a + binary_character b
  have hsingle (v : Fin n → Fin 2) (j : Fin n) :
      binary_character v (Pi.single j 1) = (-1 : ℂ) ^ (v j).val := by
    change (∏ i, (-1 : ℂ) ^ (((Pi.single j 1 : Fin n → Fin 2) i).val *
      (v i).val)) = _
    rw [Finset.prod_eq_single j]
    · simp [Pi.single_apply]
    · intro i _ hij
      simp [Pi.single_apply, hij, Ne.symm hij]
    · simp
  have hzero : ψ = 0 ↔ a = b := by
    constructor
    · intro h
      funext j
      have hj := congrArg (fun e : AddChar (Fin n → Fin 2) ℂ => e (Pi.single j 1)) h
      change binary_character a (Pi.single j 1) * binary_character b (Pi.single j 1) = 1 at hj
      rw [hsingle, hsingle] at hj
      generalize ha : a j = r at *
      generalize hb : b j = t at *
      fin_cases r <;> fin_cases t <;> norm_num at *
    · rintro rfl
      ext x
      change binary_character a x * binary_character a x = 1
      change (∏ j, (-1 : ℂ) ^ ((x j).val * (a j).val)) *
        (∏ j, (-1 : ℂ) ^ ((x j).val * (a j).val)) = 1
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_eq_one
      intro j _
      generalize x j = r
      generalize a j = t
      fin_cases r <;> fin_cases t <;> norm_num
  have hs := AddChar.sum_eq_ite ψ
  have hfun (x : Fin n → Fin 2) : ψ x =
      (∏ j, (-1 : ℂ) ^ ((a j).val * (x j).val)) *
        (∏ j, (-1 : ℂ) ^ ((b j).val * (x j).val)) := by
    change (∏ j, (-1 : ℂ) ^ ((x j).val * (a j).val)) *
      (∏ j, (-1 : ℂ) ^ ((x j).val * (b j).val)) = _
    simp only [Nat.mul_comm]
  simpa only [hfun, hzero, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
    Nat.cast_ofNat] using hs

private lemma reflection_encoding_of_flat_frame {n : ℕ}
    (ψ : (Fin n → Fin 2) → ℂ)
    (F : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (hF : F ∈ Matrix.unitaryGroup (Fin n → Fin 2) ℂ)
    (R : (Fin n → Fin 2) → Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hR : ∀ a j, (R a j).IsHermitian ∧ R a j * R a j = 1)
    (hd : ∀ a, Fᴴ * tensorOp (R a) * F =
      diagonal (fun x => ∏ j, (-1 : ℂ) ^ ((a j).val * (x j).val)))
    (hf : ∀ x, (2 ^ n : ℂ) * (star ((Fᴴ *ᵥ ψ) x) * (Fᴴ *ᵥ ψ) x) = 1) :
    ∃ U, IsCommutingReflectionEncoding ψ U := by
  classical
  let e : Fin (2 ^ n) ≃ (Fin n → Fin 2) :=
    (Fintype.equivFinOfCardEq (by simp [Fintype.card_fun])).symm
  let c := Fᴴ *ᵥ ψ
  let χ (a x : Fin n → Fin 2) : ℂ := ∏ j, (-1 : ℂ) ^ ((a j).val * (x j).val)
  have hFF : F * Fᴴ = 1 := hF.2
  have hFtF : Fᴴ * F = 1 := hF.1
  have hN : (2 ^ n : ℂ) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hw (x) : star (c x) * c x = 1 / (2 ^ n : ℂ) := by
    apply (eq_div_iff hN).mpr
    simpa [c, mul_comm] using hf x
  have hs (a x) : star (χ a x) = χ a x := by simp [χ]
  have he (a : Fin n → Fin 2) :
      Fᴴ *ᵥ (tensorOp (R a) *ᵥ ψ) = fun x => c x * χ a x := by
    calc
      _ = (Fᴴ * tensorOp (R a) * F) *ᵥ c := by
        dsimp only [c]
        simp only [← Matrix.mulVec_mulVec]
        rw [Matrix.mulVec_mulVec ψ F Fᴴ, hFF, Matrix.one_mulVec]
      _ = _ := by
        rw [hd a]
        ext x
        simp [Matrix.mulVec, dotProduct, Matrix.diagonal, χ, mul_comm]
  have hp (v w : (Fin n → Fin 2) → ℂ) :
      (∑ x, star ((Fᴴ *ᵥ v) x) * (Fᴴ *ᵥ w) x) = ∑ x, star (v x) * w x := by
    change star (Fᴴ *ᵥ v) ⬝ᵥ (Fᴴ *ᵥ w) = star v ⬝ᵥ w
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      Matrix.conjTranspose_conjTranspose, hFF, Matrix.vecMul_one]
  have horth (a b : Fin n → Fin 2) :
      (∑ x, star ((tensorOp (R a) *ᵥ ψ) x) * (tensorOp (R b) *ᵥ ψ) x) =
        if a = b then 1 else 0 := by
    rw [← hp, he, he]
    have hm (x) : star (c x * χ a x) * (c x * χ b x) =
        (1 / (2 ^ n : ℂ)) * (χ a x * χ b x) := by
      rw [star_mul, hs]
      calc
        _ = (star (c x) * c x) * (χ a x * χ b x) := by ring
        _ = _ := by rw [hw]
    simp_rw [hm]
    rw [← Finset.mul_sum]
    have hsum : (∑ x : Fin n → Fin 2, χ a x * χ b x) =
        if a = b then (2 ^ n : ℂ) else 0 := character_orthogonality a b
    rw [hsum]
    by_cases hab : a = b <;> simp [hab, hN]
  have hi (a : Fin n → Fin 2) : tensorOp (R a) = F * diagonal (χ a) * Fᴴ := by
    have h := congrArg (fun A => F * A * Fᴴ) (hd a)
    have hu (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) :
        F * (Fᴴ * A * F) * Fᴴ = A := by
      calc
        _ = (F * Fᴴ) * A * (F * Fᴴ) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hFF, Matrix.one_mul, Matrix.mul_one]
    rw [hu] at h
    exact h
  have hprod (d g : (Fin n → Fin 2) → ℂ) :
      (F * diagonal d * Fᴴ) * (F * diagonal g * Fᴴ) =
        F * (diagonal d * diagonal g) * Fᴴ := by
    calc
      _ = F * diagonal d * (Fᴴ * F) * diagonal g * Fᴴ := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hFtF, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  refine ⟨fun a => R (e a), ⟨?_, ?_, ?_⟩, fun a j => hR (e a) j⟩
  · intro a j
    apply Matrix.mem_unitaryGroup_iff'.mpr
    change (R (e a) j)ᴴ * R (e a) j = 1
    rw [(hR (e a) j).1.eq]
    exact (hR (e a) j).2
  · intro a b
    rw [hi, hi, hprod, hprod, (Matrix.commute_diagonal (χ (e a)) (χ (e b))).eq]
  · intro a b
    simpa only [e.injective.eq_iff] using horth (e a) (e b)

private lemma product_encoding_to_reflections {n : ℕ} (hn : 1 ≤ n)
    (ψ : (Fin n → Fin 2) → ℂ)
    (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : IsCommutingProductEncoding ψ U) :
    ∃ R, IsCommutingReflectionEncoding ψ R := by
  obtain ⟨V, F, eig, R, hV, hF, heig, hd, hR, hRd⟩ :=
    spectral_frame_of_local_signs hn U hU.1 hU.2.1
      (local_commutation_signs U hU.1 hU.2.1)
  have hUV := product_encoding_conjugate ψ U hU V hV
  obtain ⟨S, hS⟩ := reflection_encoding_of_flat_frame (tensorOp V *ᵥ ψ) F hF R hR hRd
    (flat_of_diagonal_encoding (tensorOp V *ᵥ ψ) _ hUV F hF eig heig hd)
  have hback := reflection_encoding_conjugate (tensorOp V *ᵥ ψ) S hS
    (fun j => (V j)ᴴ) (fun j => Unitary.star_mem (hV j))
  have hstate : tensorOp (fun j => (V j)ᴴ) *ᵥ (tensorOp V *ᵥ ψ) = ψ := by
    rw [← tensor_adj, Matrix.mulVec_mulVec]
    rw [show (tensorOp V)ᴴ * tensorOp V = 1 from (tensor_unitary V hV).1]
    exact Matrix.one_mulVec ψ
  rw [hstate] at hback
  exact ⟨_, hback⟩

private lemma reflection_encoding_to_product {n : ℕ}
    (ψ : (Fin n → Fin 2) → ℂ)
    (U : Fin (2 ^ n) → Fin n → Matrix (Fin 2) (Fin 2) ℂ)
    (hU : IsCommutingReflectionEncoding ψ U) : IsCommutingProductEncoding ψ U :=
  hU.1

/-- Commuting product encodings admit commuting local-reflection replacements. -/
theorem result : claim := by
  intro n hn ψ _hψ
  constructor
  · rintro ⟨U, hU⟩
    exact product_encoding_to_reflections hn ψ U hU
  · rintro ⟨U, hU⟩
    exact ⟨U, reflection_encoding_to_product ψ U hU⟩

end D5.S3.Quantum.Information.CommutingEncodingReflectionClass
