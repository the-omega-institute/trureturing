/- GID: D5/S3/Quantum/Information/CommutingEncodingReflectionClass
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/CommutingEncodingReflectionClass
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Commuting product and reflection encodings give the same qubit state class. -/

import D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm
import D5.S3.Quantum.BlockNorm.EssentiallyHermitian

/-! Commuting qubit product encodings and their local-reflection replacements. -/

open scoped BigOperators
open Matrix
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

private lemma reflection_axes_pauli_frame {κ : Type*}
    (H : κ → Matrix (Fin 2) (Fin 2) ℂ)
    (hH : ∀ a, (H a).IsHermitian ∧ H a * H a = 1)
    (hs : ∀ a b, H a * H b = H b * H a ∨ H a * H b = -(H b * H a)) :
    ∃ V ∈ Matrix.unitaryGroup (Fin 2) ℂ,
      ∃ (c : κ → ℂ) (p : κ → Pauli),
        (∀ a, star (c a) * c a = 1) ∧
        (∀ a, V * H a * Vᴴ = c a • pauliMatrix (p a)) := by
  sorry

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
  sorry

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
  have one_site (r t : Fin 2) :
      (∑ z : Fin 2, (-1 : ℂ) ^ (r.val * z.val) * (-1 : ℂ) ^ (t.val * z.val)) =
        if r = t then 2 else 0 := by
    fin_cases r <;> fin_cases t <;> norm_num [Fin.sum_univ_two]
  calc
    _ = ∏ j, ∑ z : Fin 2,
        (-1 : ℂ) ^ ((a j).val * z.val) * (-1 : ℂ) ^ ((b j).val * z.val) := by
      rw [Fintype.prod_sum]
      simp_rw [Finset.prod_mul_distrib]
    _ = ∏ j, if a j = b j then (2 : ℂ) else 0 := by simp_rw [one_site]
    _ = _ := by
      by_cases hab : a = b
      · subst b
        simp
      · rw [if_neg hab]
        obtain ⟨j, hj⟩ := Function.ne_iff.mp hab
        exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

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
