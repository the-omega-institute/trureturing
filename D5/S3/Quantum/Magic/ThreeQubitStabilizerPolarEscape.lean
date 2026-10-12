/- GID: D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape
   generality: I
   mirror-B: D5/B/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Seven anticommuting Paulis support a three-qubit stabilizer polar escape. -/
import D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
import D5.S3.Quantum.Entanglement.NandiMutualPredictabilityLOCCRefutation
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.Group.Submonoid.Basic
set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder
open D5.S3.Quantum.FiniteDimensional (qubitX qubitZ)
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
  (Pauli pauliMatrix tensorOp wordOp localOp tensor_mul sgn anticomm)
open D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
  (Phase letterProduct letterPhase word_mul word_comm_sign tensor_one wordUnit word_one tensor_trace
    word_hermitian pauli_hermitian)
namespace D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape
abbrev Bits (n : ℕ) := Fin n → Fin 2
abbrev Op (n : ℕ) := Matrix (Bits n) (Bits n) ℂ
def IsState {n : ℕ} (ρ : Op n) : Prop := ρ.PosSemidef ∧ ρ.trace = 1
def tr {n : ℕ} (A : Op n) : ℝ := A.trace.re
def conjugate {n : ℕ} (A : Op n) : Op n := A.map star
private def splitBits (n m : ℕ) (x : Bits (n + m)) : Bits n × Bits m :=
  (fun i => x (Fin.castAdd m i), fun j => x (Fin.natAdd n j))
def tensor {n m : ℕ} (A : Op n) (B : Op m) : Op (n + m) :=
  (Matrix.kronecker A B).submatrix (splitBits n m) (splitBits n m)
private def PauliGroup (n : ℕ) : Set (Op n) :=
  {A | ∃ c : ℂ, Phase c ∧ ∃ w : Fin n → Pauli, A = c • wordOp w}
private abbrev gateH :=
  D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.hadamard
private def gateS : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1, Complex.I]
private def gateCNOT {n : ℕ} (c t : Fin n) : Op n :=
  Matrix.of fun x y => if x = Function.update y t (y t + y c) then 1 else 0
private def gates (n : ℕ) : Set (Op n) :=
  {U | (∃ i : Fin n, U = localOp i gateH) ∨ (∃ i : Fin n, U = localOp i gateS) ∨
    (∃ c t : Fin n, c ≠ t ∧ U = gateCNOT c t)}
private def Clifford (n : ℕ) : Submonoid (Op n) :=
  Submonoid.closure (gates n ∪ (fun U : Op n => Uᴴ) '' gates n)
private def vacuum (n : ℕ) : Op n := Matrix.single (0 : Bits n) 0 1
private def PureStabilizer (n : ℕ) : Set (Op n) :=
  {ρ | ∃ U : Op n, U ∈ Clifford n ∧ ρ = U * vacuum n * Uᴴ}
def STAB (n : ℕ) : Set (Op n) := convexHull ℝ (PureStabilizer n)
private def gammaWords : Fin 7 → Fin 3 → Pauli :=
  ![![.X, .I, .I], ![.Y, .I, .I], ![.Z, .X, .I], ![.Z, .Y, .I],
    ![.Z, .Z, .X], ![.Z, .Z, .Y], ![.Z, .Z, .Z]]
def S : Op 3 := ∑ j : Fin 7, wordOp (gammaWords j)
def sigma : Op 3 := (1 / 56 : ℝ) • ((7 : ℝ) • 1 + S)
def bell : Op 6 := Matrix.of fun x y =>
  if (splitBits 3 3 x).1 = (splitBits 3 3 x).2 ∧
      (splitBits 3 3 y).1 = (splitBits 3 3 y).2 then (1 / 8 : ℂ) else 0
private def splitEquiv (n m : ℕ) : Bits (n + m) ≃ Bits n × Bits m where
  toFun := splitBits n m
  invFun := fun p => Fin.append p.1 p.2
  left_inv := fun x => Fin.append_castAdd_natAdd
  right_inv := by intro p; ext i <;> simp [splitBits]
private lemma tensor_product {n m : ℕ} (A C : Op n) (B D : Op m) :
    tensor A B * tensor C D = tensor (A * C) (B * D) := by
  unfold tensor
  change (A.kronecker B).submatrix (splitEquiv n m) (splitEquiv n m) *
    (C.kronecker D).submatrix (splitEquiv n m) (splitEquiv n m) = _
  rw [Matrix.submatrix_mul_equiv]
  change (A.kronecker B * C.kronecker D).submatrix (splitBits n m) (splitBits n m) = _
  congr 1
  exact (Matrix.mul_kronecker_mul A C B D).symm
private lemma word_square {n : ℕ} (w : Fin n → Pauli) : wordOp w * wordOp w = 1 :=
  (wordUnit w).val_inv
private lemma tensor_adjoint {n : ℕ} (M : Fin n → Matrix (Fin 2) (Fin 2) ℂ) :
    (tensorOp M)ᴴ = tensorOp (fun i => (M i)ᴴ) := by
  ext x y
  simp [tensorOp, Matrix.conjTranspose_apply, star_prod]
private lemma gamma_anticommute (i j : Fin 7) (h : i ≠ j) :
    wordOp (gammaWords i) * wordOp (gammaWords j) =
      -(wordOp (gammaWords j) * wordOp (gammaWords i)) := by
  rw [word_comm_sign]
  have hs : (∏ k : Fin 3, (sgn (gammaWords i k) (gammaWords j k) : ℂ)) = -1 := by
    fin_cases i <;> fin_cases j
    all_goals first | exact (h rfl).elim |
      (norm_num [gammaWords, Fin.prod_univ_succ, sgn, anticomm]; decide)
  rw [hs, neg_one_smul]
private lemma S_adjoint : Sᴴ = S := by
  simp only [S, Matrix.conjTranspose_sum, word_hermitian]
private lemma S_square : S * S = (7 : ℂ) • (1 : Op 3) := by
  let G := fun i => wordOp (gammaWords i)
  let T : Op 3 := ∑ i : Fin 7, ∑ j : Fin 7, if i ≠ j then G i * G j else 0
  have ht : T = -T := by
    dsimp only [T]
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    simp_rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : i = j
    · subst j; simp
    · simp only [h, Ne.symm h, ne_eq, not_false_eq_true, ite_true]
      exact gamma_anticommute j i (Ne.symm h)
  have hz : T = 0 := by
    ext x y
    have h := congrArg (fun A : Op 3 => A x y) ht
    simp only [Matrix.neg_apply] at h
    change T x y = 0
    apply Complex.ext
    · have := congrArg Complex.re h; simp only [Complex.neg_re] at this
      change (T x y).re = 0; linarith
    · have := congrArg Complex.im h; simp only [Complex.neg_im] at this
      change (T x y).im = 0; linarith
  have hd : S * S = (∑ i : Fin 7, G i * G i) + T := by
    change (∑ i : Fin 7, G i) * (∑ i : Fin 7, G i) = _
    change (∑ i : Fin 7, G i) * (∑ i : Fin 7, G i) =
      (∑ i : Fin 7, G i * G i) + ∑ i : Fin 7, ∑ j : Fin 7, if i ≠ j then G i * G j else 0
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Fintype.sum_ite_eq' i (fun j => G i * G j)]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : j = i <;> simp [h, Ne.symm]
  rw [hd, hz, add_zero]
  simp only [G, word_square, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  ext x y
  simp [Matrix.one_apply]
private lemma S_trace : S.trace = 0 := by
  have hg (j : Fin 7) : (wordOp (gammaWords j)).trace = 0 := by
    unfold wordOp
    rw [tensor_trace]
    fin_cases j <;> unfold Matrix.trace <;> norm_num [gammaWords, Fin.prod_univ_succ,
      pauliMatrix, qubitX, qubitZ, Fin.sum_univ_two, Matrix.mul_apply]
  simp only [S, Matrix.trace_sum, hg, Finset.sum_const_zero]
private lemma phase_mul {c d : ℂ} (hc : Phase c) (hd : Phase d) : Phase (c * d) := by
  dsimp only [Phase] at hc hd ⊢
  rcases hc with rfl | rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl | rfl <;>
    simp [Complex.I_mul_I]
private lemma local_adjoint {n : ℕ} (i : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (localOp i A)ᴴ = localOp i Aᴴ := by
  unfold localOp
  rw [tensor_adjoint]
  congr 1
  funext j
  by_cases h : j = i <;> simp [h]
private lemma local_product {n : ℕ} (i : Fin n) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    localOp i A * localOp i B = localOp i (A * B) := by
  unfold localOp
  rw [tensor_mul]
  congr 1
  funext j
  by_cases h : j = i <;> simp [h]
private lemma local_identity {n : ℕ} (i : Fin n) :
    localOp i (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  unfold localOp
  rw [Function.update_eq_self_iff.mpr rfl, tensor_one]
private lemma local_unitary {n : ℕ} (i : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (ha : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) : localOp i A ∈ Matrix.unitaryGroup (Bits n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at ha ⊢
  rw [Matrix.star_eq_conjTranspose] at ha ⊢
  rw [local_adjoint, local_product, ha, local_identity]
private lemma gateS_unitary : gateS ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  rw [Matrix.star_eq_conjTranspose]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [gateS, Matrix.mul_apply, Fin.sum_univ_two]
private def cnotBits {n : ℕ} (c t : Fin n) (x : Bits n) : Bits n :=
  Function.update x t (x t + x c)
private lemma cnot_involutive {n : ℕ} (c t : Fin n) (h : c ≠ t) :
    Function.Involutive (cnotBits c t) := by
  intro x
  funext i
  by_cases hi : i = t
  · subst i
    simp only [cnotBits, Function.update_self, Function.update_of_ne h]
    have hz : ∀ b : Fin 2, b + b = 0 := by decide
    rw [add_assoc, hz, add_zero]
  · simp [cnotBits, hi]
private lemma cnot_action {n : ℕ} (c t : Fin n) (h : c ≠ t) (A : Op n) :
    gateCNOT c t * A * gateCNOT c t = A.submatrix (cnotBits c t) (cnotBits c t) := by
  have hi := cnot_involutive c t h
  ext x y
  have he (z : Bits n) : x = cnotBits c t z ↔ z = cnotBits c t x :=
    ⟨fun e => by rw [e, hi], fun e => by rw [e, hi]⟩
  change (∑ j, (∑ k, (if x = cnotBits c t k then 1 else 0) * A k j) *
    (if j = cnotBits c t y then 1 else 0)) = A (cnotBits c t x) (cnotBits c t y)
  simp only [he, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  simp
private lemma cnot_unitary {n : ℕ} (c t : Fin n) (h : c ≠ t) :
    gateCNOT c t ∈ Matrix.unitaryGroup (Bits n) ℂ ∧ (gateCNOT c t)ᴴ = gateCNOT c t := by
  have hi := cnot_involutive c t h
  have hadj : (gateCNOT c t)ᴴ = gateCNOT c t := by
    ext x y
    have he : y = cnotBits c t x ↔ x = cnotBits c t y :=
      ⟨fun e => by rw [e, hi], fun e => by rw [e, hi]⟩
    change star (if y = cnotBits c t x then (1 : ℂ) else 0) =
      if x = cnotBits c t y then 1 else 0
    simp only [apply_ite star, star_one, star_zero, he]
  refine ⟨?_, hadj⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hadj]
  have hs : gateCNOT c t * gateCNOT c t = 1 := by
    have he : (1 : Op n).submatrix (cnotBits c t) (cnotBits c t) = 1 := by
      ext x y
      simp [Matrix.one_apply, hi.injective.eq_iff]
    simpa only [mul_one, he] using cnot_action c t h (1 : Op n)
  exact hs
private lemma cnot_table (p q : Pauli) : ∃ (d : ℂ) (a b : Pauli), Phase d ∧
    ∀ x y u v : Fin 2, pauliMatrix p x u * pauliMatrix q (y + x) (v + u) =
      d * (pauliMatrix a x u * pauliMatrix b y v) := by
  cases p <;> cases q
  case' I.I => refine ⟨1, .I, .I, Or.inl rfl, ?_⟩
  case' I.X => refine ⟨1, .I, .X, Or.inl rfl, ?_⟩
  case' I.Y => refine ⟨1, .Z, .Y, Or.inl rfl, ?_⟩
  case' I.Z => refine ⟨1, .Z, .Z, Or.inl rfl, ?_⟩
  case' X.I => refine ⟨1, .X, .X, Or.inl rfl, ?_⟩
  case' X.X => refine ⟨1, .X, .I, Or.inl rfl, ?_⟩
  case' X.Y => refine ⟨1, .Y, .Z, Or.inl rfl, ?_⟩
  case' X.Z => refine ⟨-1, .Y, .Y, Or.inr (Or.inl rfl), ?_⟩
  case' Y.I => refine ⟨1, .Y, .X, Or.inl rfl, ?_⟩
  case' Y.X => refine ⟨1, .Y, .I, Or.inl rfl, ?_⟩
  case' Y.Y => refine ⟨-1, .X, .Z, Or.inr (Or.inl rfl), ?_⟩
  case' Y.Z => refine ⟨1, .X, .Y, Or.inl rfl, ?_⟩
  case' Z.I => refine ⟨1, .Z, .I, Or.inl rfl, ?_⟩
  case' Z.X => refine ⟨1, .Z, .X, Or.inl rfl, ?_⟩
  case' Z.Y => refine ⟨1, .I, .Y, Or.inl rfl, ?_⟩
  case' Z.Z => refine ⟨1, .I, .Z, Or.inl rfl, ?_⟩
  all_goals intro x y u v; fin_cases x <;> fin_cases y <;> fin_cases u <;> fin_cases v <;>
    norm_num [pauliMatrix, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two,
      Fin.add_def, Matrix.one_apply]
private lemma cnot_normalizes {n : ℕ} (c t : Fin n) (h : c ≠ t) (w : Fin n → Pauli) :
    gateCNOT c t * wordOp w * (gateCNOT c t)ᴴ ∈ PauliGroup n := by
  obtain ⟨d, a, b, hd, he⟩ := cnot_table (w c) (w t)
  refine ⟨d, hd, Function.update (Function.update w c a) t b, ?_⟩
  rw [(cnot_unitary c t h).2, cnot_action c t h]
  ext x y
  simp only [Matrix.submatrix_apply, wordOp, tensorOp, Matrix.of_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c)]
  rw [← Finset.mul_prod_erase (Finset.univ.erase c) _ (a := t) (by simp [h.symm])]
  conv_rhs => rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c)]
  conv_rhs =>
    rw [← Finset.mul_prod_erase (Finset.univ.erase c) _ (a := t) (by simp [h.symm])]
  simp only [cnotBits, Function.update_self, Function.update_of_ne h]
  rw [← mul_assoc, he, mul_assoc, mul_assoc]
  congr 3
  apply Finset.prod_congr rfl
  intro i hi
  have hic : i ≠ c := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
  have hit : i ≠ t := (Finset.mem_erase.mp hi).1
  simp only [Function.update_of_ne hic, Function.update_of_ne hit]
private lemma local_table (A : Matrix (Fin 2) (Fin 2) ℂ)
    (ha : A = gateH ∨ A = gateS ∨ A = gateSᴴ) (p : Pauli) :
    ∃ (c : ℂ) (q : Pauli), Phase c ∧ A * pauliMatrix p * Aᴴ = c • pauliMatrix q := by
  have hs : (Real.sqrt 2 / 2) ^ 2 = (1 / 2 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rcases ha with rfl | rfl | rfl <;> cases p
  case' inl.I => refine ⟨1, .I, Or.inl rfl, ?_⟩
  case' inl.X => refine ⟨1, .Z, Or.inl rfl, ?_⟩
  case' inl.Y => refine ⟨-1, .Y, Or.inr (Or.inl rfl), ?_⟩
  case' inl.Z => refine ⟨1, .X, Or.inl rfl, ?_⟩
  case' inr.inl.I => refine ⟨1, .I, Or.inl rfl, ?_⟩
  case' inr.inl.X => refine ⟨1, .Y, Or.inl rfl, ?_⟩
  case' inr.inl.Y => refine ⟨-1, .X, Or.inr (Or.inl rfl), ?_⟩
  case' inr.inl.Z => refine ⟨1, .Z, Or.inl rfl, ?_⟩
  case' inr.inr.I => refine ⟨1, .I, Or.inl rfl, ?_⟩
  case' inr.inr.X => refine ⟨-1, .Y, Or.inr (Or.inl rfl), ?_⟩
  case' inr.inr.Y => refine ⟨1, .X, Or.inl rfl, ?_⟩
  case' inr.inr.Z => refine ⟨1, .Z, Or.inl rfl, ?_⟩
  all_goals
    ext i j; fin_cases i <;> fin_cases j
    all_goals apply Complex.ext <;>
      simp [gateH, gateS, D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.hadamard,
        D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.s2, pauliMatrix,
        qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im,
        map_ofNat]
      <;> nlinarith [hs]
private lemma local_normalizes {n : ℕ} (i : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (ha : A = gateH ∨ A = gateS ∨ A = gateSᴴ) (w : Fin n → Pauli) :
    localOp i A * wordOp w * (localOp i A)ᴴ ∈ PauliGroup n := by
  obtain ⟨c, q, hc, hq⟩ := local_table A ha (w i)
  refine ⟨c, hc, Function.update w i q, ?_⟩
  rw [local_adjoint]
  unfold localOp wordOp
  rw [tensor_mul, tensor_mul]
  have he : (fun j => Function.update (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) i A j *
      pauliMatrix (w j) * Function.update (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ)) i Aᴴ j) =
      Function.update (fun j => pauliMatrix (w j)) i (c • pauliMatrix q) := by
    funext j
    by_cases h : j = i <;> simp [h, hq]
  rw [he]
  ext x y
  simp only [tensorOp, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  conv_rhs => rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [Function.update_self, Matrix.smul_apply, smul_eq_mul, mul_assoc]
  congr 2
  apply Finset.prod_congr rfl
  intro j hj
  simp only [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
private lemma H_adjoint : gateHᴴ = gateH := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [gateH, D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.hadamard,
      D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.s2, pauliMatrix,
      qubitX, qubitZ]
private lemma gates_data {n : ℕ} {U : Op n}
    (hu : U ∈ gates n ∪ (fun A : Op n => Aᴴ) '' gates n) :
    U ∈ Matrix.unitaryGroup (Bits n) ℂ ∧
      ∀ w : Fin n → Pauli, U * wordOp w * Uᴴ ∈ PauliGroup n := by
  have hh := D5.S3.Quantum.Entanglement.NandiMutualPredictabilityLOCCRefutation.hadamard_unitary
  have hs := gateS_unitary
  rcases hu with hu | ⟨V, hv, rfl⟩
  · rcases hu with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨c, t, h, rfl⟩
    · exact ⟨local_unitary i _ hh, local_normalizes i _ (Or.inl rfl)⟩
    · exact ⟨local_unitary i _ hs, local_normalizes i _ (Or.inr (Or.inl rfl))⟩
    · exact ⟨(cnot_unitary c t h).1, cnot_normalizes c t h⟩
  · dsimp only
    rcases hv with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨c, t, h, rfl⟩
    · rw [local_adjoint, H_adjoint]
      exact ⟨local_unitary i _ hh, local_normalizes i _ (Or.inl rfl)⟩
    · rw [local_adjoint]
      exact ⟨local_unitary i _ (Unitary.star_mem hs),
        local_normalizes i _ (Or.inr (Or.inr rfl))⟩
    · rw [(cnot_unitary c t h).2]
      exact ⟨(cnot_unitary c t h).1, cnot_normalizes c t h⟩
private lemma clifford_data {n : ℕ} {U : Op n} (hu : U ∈ Clifford n) :
    U ∈ Matrix.unitaryGroup (Bits n) ℂ ∧
      ∀ P ∈ PauliGroup n, U * P * Uᴴ ∈ PauliGroup n := by
  induction hu using Submonoid.closure_induction with
  | mem U hu =>
    obtain ⟨hunit, hn⟩ := gates_data hu
    refine ⟨hunit, ?_⟩
    rintro P ⟨c, hc, w, rfl⟩
    obtain ⟨d, hd, v, hv⟩ := hn w
    refine ⟨c * d, phase_mul hc hd, v, ?_⟩
    simp only [Matrix.mul_smul, Matrix.smul_mul, hv, smul_smul]
  | one =>
    exact ⟨(Matrix.unitaryGroup (Bits n) ℂ).one_mem, fun P hP => by simpa using hP⟩
  | mul U V hU hV ihU ihV =>
    refine ⟨(Matrix.unitaryGroup (Bits n) ℂ).mul_mem ihU.1 ihV.1, ?_⟩
    intro P hP
    simpa only [Matrix.conjTranspose_mul, mul_assoc] using ihU.2 _ (ihV.2 P hP)
private lemma clifford_adjoint {n : ℕ} {U : Op n} (hu : U ∈ Clifford n) :
    Uᴴ ∈ Clifford n := by
  induction hu using Submonoid.closure_induction with
  | mem U hu =>
    apply Submonoid.subset_closure
    rcases hu with h | ⟨V, hV, rfl⟩
    · exact Or.inr ⟨U, h, rfl⟩
    · exact Or.inl (by simpa only [Matrix.conjTranspose_conjTranspose] using hV)
  | one => simp only [Matrix.conjTranspose_one]; exact (Clifford n).one_mem
  | mul U V hU hV ihU ihV =>
    simpa only [Matrix.conjTranspose_mul] using (Clifford n).mul_mem ihV ihU
private lemma pauli_real {n : ℕ} {P : Op n} (hp : P ∈ PauliGroup n) (hh : Pᴴ = P) :
    ∃ (c : ℂ) (w : Fin n → Pauli), (c = 1 ∨ c = -1) ∧ P = c • wordOp w := by
  obtain ⟨c, hc, w, rfl⟩ := hp
  have he := congrArg (fun M : Op n => (M * wordOp w) 0 0) hh
  have hr : star c = c := by
    simpa only [Matrix.conjTranspose_smul, word_hermitian, Matrix.smul_mul, word_square,
      Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, ite_true, mul_one] using he
  refine ⟨c, w, ?_, rfl⟩
  rcases hc with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  all_goals subst c; norm_num [Complex.ext_iff] at hr
private lemma vacuum_word {n : ℕ} (w : Fin n → Pauli) : wordOp w 0 0 = 0 ∨
    (wordOp w * vacuum n = vacuum n ∧ wordOp w 0 0 = 1) := by
  by_cases hd : ∀ i, w i = .I ∨ w i = .Z
  · have he (x : Bits n) : wordOp w x 0 = (1 : Op n) x 0 := by
      calc
        wordOp w x 0 = tensorOp (fun _ : Fin n => (1 : Matrix (Fin 2) (Fin 2) ℂ)) x 0 := by
          dsimp only [wordOp, tensorOp, Matrix.of_apply]
          apply Finset.prod_congr rfl
          intro i _
          rcases hd i with h | h <;> rw [h] <;>
            (generalize x i = b; fin_cases b <;> simp [pauliMatrix, qubitZ, Matrix.one_apply])
        _ = _ := congrArg (fun M : Op n => M x 0) tensor_one
    refine Or.inr ⟨?_, by simpa using he 0⟩
    ext x y
    unfold vacuum
    by_cases hy : y = 0
    · subst y
      rw [Matrix.mul_single_apply_same, mul_one, he, Matrix.one_apply]
      simp only [Matrix.single_apply, and_true, eq_comm]
    · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hy,
        Matrix.single_apply_of_col_ne _ _ (Ne.symm hy)]
  · push Not at hd
    obtain ⟨i, hi, hz⟩ := hd
    apply Or.inl
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    cases h : w i <;> simp_all [pauliMatrix, qubitX, qubitZ]
private lemma pure_expectation {n : ℕ} {U P : Op n} (hu : U ∈ Clifford n)
    (hp : P ∈ PauliGroup n) (hh : Pᴴ = P) :
    (P * (U * vacuum n * Uᴴ)).trace = 0 ∨
      (((P * (U * vacuum n * Uᴴ)).trace = 1 ∨
        (P * (U * vacuum n * Uᴴ)).trace = -1) ∧
        P * (U * vacuum n * Uᴴ) = (P * (U * vacuum n * Uᴴ)).trace •
          (U * vacuum n * Uᴴ)) := by
  have hn := clifford_data (clifford_adjoint hu)
  have hq : (Uᴴ * P * U)ᴴ = Uᴴ * P * U := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hh, mul_assoc]
  obtain ⟨c, w, hc, hw⟩ := pauli_real (by simpa using hn.2 P hp) hq
  have ht : (P * (U * vacuum n * Uᴴ)).trace = c * wordOp w 0 0 := by
    calc
      _ = (Uᴴ * P * U * vacuum n).trace := by
        simpa only [mul_assoc] using Matrix.trace_mul_cycle (P * U) (vacuum n) Uᴴ
      _ = _ := by rw [hw, Matrix.smul_mul, Matrix.trace_smul]; simp [vacuum,
          Matrix.trace_mul_single]
  rcases vacuum_word w with hz | ⟨he, hv⟩
  · exact Or.inl (by rw [ht, hz, mul_zero])
  · have htc : (P * (U * vacuum n * Uᴴ)).trace = c := by rw [ht, hv, mul_one]
    have huR : U * Uᴴ = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using
        Matrix.mem_unitaryGroup_iff.mp (clifford_data hu).1
    refine Or.inr ⟨htc ▸ hc, ?_⟩
    rw [htc]
    calc
      _ = U * ((Uᴴ * P * U) * vacuum n) * Uᴴ := by
        simp only [← mul_assoc, huR, one_mul]
      _ = _ := by rw [hw, Matrix.smul_mul, he, Matrix.mul_smul, Matrix.smul_mul]
private lemma pure_eigenvector {n : ℕ} {U P : Op n} (hu : U ∈ Clifford n)
    (hp : P ∈ PauliGroup n) (hh : Pᴴ = P)
    (he : (P * (U * vacuum n * Uᴴ)).trace ≠ 0) :
    P *ᵥ (U *ᵥ Pi.single 0 1) = (P * (U * vacuum n * Uᴴ)).trace •
      (U *ᵥ Pi.single 0 1) := by
  have hl : Uᴴ * U = 1 := by simpa only [Matrix.star_eq_conjTranspose] using
    Matrix.mem_unitaryGroup_iff'.mp (clifford_data hu).1
  have h := congrArg (fun A : Op n => A * U)
    (((pure_expectation hu hp hh).resolve_left he).2)
  simp only [Matrix.smul_mul, mul_assoc, hl, mul_one] at h
  rw [Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec_single_one]
  ext x
  have hx := congrArg (fun A : Op n => A x 0) h
  simpa only [vacuum, ← mul_assoc, Matrix.mul_single_apply_same, mul_one,
    Matrix.smul_apply, smul_eq_mul, Matrix.col_apply, Pi.smul_apply] using hx
private lemma anticommuting_support {n k : ℕ} (G : Fin k → Op n)
    (hg : ∀ i, G i ∈ PauliGroup n ∧ (G i)ᴴ = G i)
    (ha : ∀ i j, i ≠ j → G i * G j = -(G j * G i)) :
    ∀ ρ ∈ STAB n, tr (ρ * ∑ i, G i) ≤ 1 := by
  have hc : Convex ℝ {ρ : Op n | tr (ρ * ∑ i, G i) ≤ 1} :=
    convex_halfSpace_le ⟨fun A B => by simp [tr, Matrix.add_mul, Matrix.trace_add],
      fun r A => by simp [tr, Matrix.trace_smul]⟩ 1
  apply convexHull_min (t := {ρ : Op n | tr (ρ * ∑ i, G i) ≤ 1}) ?_ hc
  rintro ρ ⟨U, hu, rfl⟩
  let ρ : Op n := U * vacuum n * Uᴴ
  let e : Fin k → ℂ := fun i => (G i * ρ).trace
  have hψ : (U *ᵥ Pi.single 0 1 : Bits n → ℂ) ≠ 0 := by
    intro hz
    have hl : Uᴴ * U = 1 := by simpa only [Matrix.star_eq_conjTranspose] using
      Matrix.mem_unitaryGroup_iff'.mp (clifford_data hu).1
    have hv := congrArg (fun v : Bits n → ℂ => Uᴴ *ᵥ v) hz
    rw [Matrix.mulVec_mulVec, hl, Matrix.one_mulVec, Matrix.mulVec_zero] at hv
    have hc := congrFun hv 0
    simp at hc
  have he (i) : e i = 0 ∨ ((e i = 1 ∨ e i = -1) ∧ G i * ρ = e i • ρ) :=
    pure_expectation hu (hg i).1 (hg i).2
  have hs (i j) (hij : i ≠ j) : e i = 0 ∨ e j = 0 := by
    by_contra h
    push Not at h
    have ei := pure_eigenvector hu (hg i).1 (hg i).2 h.1
    have ej := pure_eigenvector hu (hg j).1 (hg j).2 h.2
    have hi : (G i * G j) *ᵥ (U *ᵥ Pi.single 0 1) =
        (e j * e i) • (U *ᵥ Pi.single 0 1) := by
      rw [← Matrix.mulVec_mulVec, ej, Matrix.mulVec_smul, ei, smul_smul]
    have hj : (G j * G i) *ᵥ (U *ᵥ Pi.single 0 1) =
        (e i * e j) • (U *ᵥ Pi.single 0 1) := by
      rw [← Matrix.mulVec_mulVec, ei, Matrix.mulVec_smul, ej, smul_smul]
    have hh := congrArg (fun M : Op n => M *ᵥ (U *ᵥ Pi.single 0 1)) (ha i j hij)
    simp only [hi, Matrix.neg_mulVec, hj, mul_comm (e j) (e i)] at hh
    have hz : (e i * e j) • (U *ᵥ Pi.single 0 1) = 0 := by
      ext x
      exact CharZero.eq_neg_self_iff.mp (congrFun hh x)
    exact (smul_eq_zero.mp hz).elim (mul_ne_zero h.1 h.2) hψ
  have ht : tr (ρ * ∑ i, G i) = (∑ i, e i).re := by
    unfold tr
    rw [Matrix.mul_sum, Matrix.trace_sum]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => Matrix.trace_mul_comm _ _)
  change tr (ρ * ∑ i, G i) ≤ 1
  rw [ht]
  by_cases hz : ∀ i, e i = 0
  · simp only [hz, Finset.sum_const_zero, Complex.zero_re]; norm_num
  · push Not at hz
    obtain ⟨i, hi⟩ := hz
    have hsum : (∑ j, e j) = e i := Finset.sum_eq_single i
      (fun j _ hj => (hs j i hj).resolve_right hi) (by simp)
    rw [hsum]
    rcases ((he i).resolve_left hi).1 with h | h <;> rw [h] <;> norm_num
private lemma S_support {ρ : Op 3} (hρ : ρ ∈ STAB 3) : tr (ρ * S) ≤ 1 := by
  apply anticommuting_support (fun i : Fin 7 => wordOp (gammaWords i)) ?_
    gamma_anticommute ρ hρ
  intro i
  exact ⟨⟨1, Or.inl rfl, gammaWords i, (one_smul _ _).symm⟩, word_hermitian _⟩
private lemma word_conjugate {n : ℕ} (w : Fin n → Pauli) :
    ∃ c : ℂ, Phase c ∧ conjugate (wordOp w) = c • wordOp w := by
  let d : Pauli → ℂ := fun p => if p = .Y then -1 else 1
  have hd (p) : Phase (d p) := by
    dsimp only [d]; split_ifs <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl)
  have he (p) (x y : Fin 2) : star (pauliMatrix p x y) = d p * pauliMatrix p x y := by
    cases p <;> fin_cases x <;> fin_cases y <;>
      norm_num [d, pauliMatrix, qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two] <;> decide
  refine ⟨∏ i, d (w i), Finset.prod_induction _ _ (fun _ _ => phase_mul)
    (Or.inl rfl) (fun i _ => hd (w i)), ?_⟩
  ext x y
  simp only [conjugate, Matrix.map_apply, wordOp, tensorOp, Matrix.of_apply,
    Matrix.smul_apply, smul_eq_mul, star_prod, he, Finset.prod_mul_distrib]
private lemma conjugate_product {n : ℕ} (A B : Op n) :
    conjugate (A * B) = conjugate A * conjugate B := by
  change (A * B).map (starRingEnd ℂ) = A.map (starRingEnd ℂ) * B.map (starRingEnd ℂ)
  exact Matrix.map_mul
private lemma conjugate_adjoint {n : ℕ} (A : Op n) :
    (conjugate A)ᴴ = conjugate Aᴴ := by ext x y; rfl
private lemma conjugate_neg {n : ℕ} (A : Op n) : conjugate (-A) = -conjugate A := by
  ext x y; exact star_neg _
private lemma conjugate_S_support {ρ : Op 3} (hρ : ρ ∈ STAB 3) :
    tr (ρ * conjugate S) ≤ 1 := by
  have hs : conjugate S = ∑ i : Fin 7, conjugate (wordOp (gammaWords i)) := by
    ext x y
    simp only [conjugate, S, Matrix.map_apply, Matrix.sum_apply, star_sum]
  rw [hs]
  apply anticommuting_support (fun i : Fin 7 => conjugate (wordOp (gammaWords i)))
    ?_ ?_ ρ hρ
  · intro i
    obtain ⟨c, hc, he⟩ := word_conjugate (gammaWords i)
    refine ⟨⟨c, hc, gammaWords i, he⟩, ?_⟩
    rw [conjugate_adjoint, word_hermitian]
  · intro i j h
    have he := congrArg conjugate (gamma_anticommute i j h)
    simpa only [conjugate_product, conjugate_neg] using he
#print axioms clifford_data
#print axioms S_square
#print axioms S_support
#print axioms conjugate_S_support
end D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape
