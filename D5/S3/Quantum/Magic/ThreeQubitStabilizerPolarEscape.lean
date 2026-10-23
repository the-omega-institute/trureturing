/- GID: D5/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape
   generality: I
   mirror-B: D5/B/S3/Quantum/Magic/ThreeQubitStabilizerPolarEscape
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Seven anticommuting Paulis support a three-qubit stabilizer polar escape. -/
import D5.S3.Quantum.Information.SLDSpectralEnergy
import D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
import D5.S3.Quantum.Entanglement.NandiMutualPredictabilityLOCCRefutation
import D5.S3.Quantum.Entanglement.GHZMeasureBiseparableBound
import D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm
import D5.S3.Quantum.Fibers.PhysicalFiber
import D5.S3.Quantum.Measurements.CliffordJointMeasurability.CliffordPathRealizations
import D5.S3.Weil.ZetaLinear.PosIndex
set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder
open D5.S3.Quantum.FiniteDimensional (qubitX qubitZ)
open D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
  (Pauli pauliMatrix tensorOp wordOp localOp tensor_mul sgn anticomm)
open D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence (s2)
open D5.S3.Quantum.Measurement.StabilizerPovmMaximalEntanglementRefutation
  (Operator Phase letterProduct letterPhase word_mul word_comm_sign tensor_one wordUnit word_one
    tensor_trace word_hermitian pauli_hermitian word_trace_pair)
open D5.S3.Quantum.Measurements.CliffordJointMeasurability.CliffordPathRealizations
  (majorana_quadratic_symmetrization)
namespace D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape
abbrev Bits (n : ℕ) := Fin n → Fin 2
abbrev Op (n : ℕ) := Operator n
def IsState {n : ℕ} (ρ : Op n) : Prop :=
  D5.S3.Quantum.Information.SLDSpectralEnergy.IsDensity ρ
def tr {n : ℕ} (A : Op n) : ℝ := RHLinalg.rtrace A
def conjugate {n : ℕ} (A : Op n) : Op n := A.map star
private def splitBits (n m : ℕ) (x : Bits (n + m)) : Bits n × Bits m :=
  (Fin.appendEquiv n m).symm x
def tensor {n m : ℕ} (A : Op n) (B : Op m) : Op (n + m) :=
  (Matrix.kronecker A B).submatrix (splitBits n m) (splitBits n m)
private def PauliGroup (n : ℕ) : Set (Op n) :=
  {A | ∃ c : ℂ, Phase c ∧ ∃ w : Fin n → Pauli, A = c • wordOp w}
abbrev gateH :=
  D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.hadamard
def gateS : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1, Complex.I]
def gateCNOT {n : ℕ} (c t : Fin n) : Op n :=
  Matrix.of fun x y => if x = Function.update y t (y t + y c) then 1 else 0
def gates (n : ℕ) : Set (Op n) :=
  {U | (∃ i : Fin n, U = localOp i gateH) ∨ (∃ i : Fin n, U = localOp i gateS) ∨
    (∃ c t : Fin n, c ≠ t ∧ U = gateCNOT c t)}
def Clifford (n : ℕ) : Submonoid (Op n) :=
  Submonoid.closure (gates n ∪ (fun U : Op n => Uᴴ) '' gates n)
def vacuum (n : ℕ) : Op n :=
  Matrix.single (fun _ : Fin n => Fin.castSucc (Fin.last 0))
    (fun _ : Fin n => Fin.castSucc (Fin.last 0)) 1
def PureStabilizer (n : ℕ) : Set (Op n) :=
  {ρ | ∃ U : Op n, U ∈ Clifford n ∧ ρ = U * vacuum n * Uᴴ}
def STAB (n : ℕ) : Set (Op n) := convexHull ℝ (PureStabilizer n)
def gammaWords : Fin 7 → Fin 3 → Pauli :=
  ![![.X, .I, .I], ![.Y, .I, .I], ![.Z, .X, .I], ![.Z, .Y, .I],
    ![.Z, .Z, .X], ![.Z, .Z, .Y], ![.Z, .Z, .Z]]
def S : Op 3 := ∑ j : Fin 7, wordOp (gammaWords j)
private def sigmaMatrix : Op 3 := (1 / 56 : ℝ) • ((7 : ℝ) • 1 + S)
def sigma : Op 3 := sigmaMatrix
private def bellMatrix : Op 6 := Matrix.of fun x y =>
  if (splitBits 3 3 x).1 = (splitBits 3 3 x).2 ∧
      (splitBits 3 3 y).1 = (splitBits 3 3 y).2 then (1 / 8 : ℂ) else 0
def bell : Op 6 := bellMatrix
def W (s : ℝ) : Op 3 := (1 / (1 + s) : ℝ) • ((1 : Op 3) + s • S)
private lemma gamma_anticommute (i j : Fin 7) (h : i ≠ j) :
    wordOp (gammaWords i) * wordOp (gammaWords j) =
      -(wordOp (gammaWords j) * wordOp (gammaWords i)) := by
  rw [word_comm_sign]
  have hsZ : (∏ k : Fin 3, sgn (gammaWords i k) (gammaWords j k)) = (-1 : ℤ) := by
    fin_cases i <;> fin_cases j
    all_goals first | exact (h rfl).elim | decide
  have hs : (∏ k : Fin 3, (sgn (gammaWords i k) (gammaWords j k) : ℂ)) = -1 := by
    exact_mod_cast hsZ
  rw [hs, neg_one_smul]
private lemma S_adjoint : Sᴴ = S := by
  dsimp only [S] ; simp only [Matrix.conjTranspose_sum, word_hermitian]
private lemma S_square : S * S = (7 : ℂ) • (1 : Op 3) := by
  unfold S
  rw [Finset.sum_mul_sum]
  simpa using
    (majorana_quadratic_symmetrization
      (fun i : Fin 7 => wordOp (gammaWords i))
      (fun i => (wordUnit (gammaWords i)).val_inv) gamma_anticommute (fun _ _ => 1))
private lemma S_trace : S.trace = 0 := by
  have hn : ∀ j : Fin 7, gammaWords j 0 ≠ .I := by decide
  have hg (j : Fin 7) : (wordOp (gammaWords j)).trace = 0 := by
    have h := word_trace_pair (gammaWords j) (fun _ : Fin 3 => Pauli.I)
    rw [word_one, Matrix.mul_one, if_neg (fun e => hn j (congrFun e 0))] at h
    exact h
  unfold S
  simp only [Matrix.trace_sum, hg, Finset.sum_const_zero]
private lemma phase_mul {c d : ℂ} (hc : Phase c) (hd : Phase d) : Phase (c * d) := by
  dsimp only [Phase] at hc hd ⊢
  rcases hc with rfl | rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl | rfl <;>
    simp [Complex.I_mul_I]
lemma local_adjoint {n : ℕ} (i : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (localOp i A)ᴴ = localOp i Aᴴ := by
  unfold localOp
  rw [D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm.tensor_adj]
  congr 1
  funext j
  by_cases h : j = i <;> simp [h]
lemma local_product {n : ℕ} (i : Fin n) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    localOp i A * localOp i B = localOp i (A * B) := by
  unfold localOp
  rw [tensor_mul]
  congr 1
  funext j
  by_cases h : j = i <;> simp [h]
lemma local_identity {n : ℕ} (i : Fin n) :
    localOp i (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  unfold localOp
  rw [Function.update_eq_self_iff.mpr rfl, tensor_one]
private lemma local_unitary {n : ℕ} (i : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (ha : A ∈ Matrix.unitaryGroup (Fin 2) ℂ) : localOp i A ∈ Matrix.unitaryGroup (Bits n) ℂ := by
  apply D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm.tensor_unitary
  intro j
  by_cases h : j = i
  · subst j
    simpa only [Function.update_self] using ha
  · simpa only [Function.update_of_ne h] using (Matrix.unitaryGroup (Fin 2) ℂ).one_mem
private lemma gateS_unitary : gateS ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have h := D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm.gate_unitary
    false (1 : ZMod 2)
  convert h using 1
  delta gateS D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm.gate
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num
private def cnotBits {n : ℕ} (c t : Fin n) (x : Bits n) : Bits n :=
  Function.update x t (x t + x c)
private lemma cnot_involutive {n : ℕ} (c t : Fin n) (h : c ≠ t) :
    Function.Involutive (cnotBits c t) := by
  intro x
  funext i
  by_cases hi : i = t
  · subst i
    dsimp only [cnotBits] ; simp only [Function.update_self, Function.update_of_ne h]
    have hz : ∀ b : Fin 2, b + b = 0 := by decide
    rw [add_assoc, hz, add_zero]
  · dsimp only [cnotBits] ; simp [hi]
private lemma cnot_action {n : ℕ} (c t : Fin n) (h : c ≠ t) (A : Op n) :
    gateCNOT c t * A * gateCNOT c t = A.submatrix (cnotBits c t) (cnotBits c t) := by
  have hi := cnot_involutive c t h
  change (1 : Op n).submatrix id hi.toPerm * A *
    (1 : Op n).submatrix (Equiv.refl (Bits n)) hi.toPerm = _
  rw [Matrix.one_submatrix_mul, Matrix.mul_submatrix_one]
  rfl
private lemma cnot_unitary {n : ℕ} (c t : Fin n) (h : c ≠ t) :
    gateCNOT c t ∈ Matrix.unitaryGroup (Bits n) ℂ ∧ (gateCNOT c t)ᴴ = gateCNOT c t := by
  have hi := cnot_involutive c t h
  have hadj : (gateCNOT c t)ᴴ = gateCNOT c t := by
    ext x y
    have he : y = cnotBits c t x ↔ x = cnotBits c t y :=
      eq_comm.trans hi.eq_iff
    change star (if y = cnotBits c t x then (1 : ℂ) else 0) =
      if x = cnotBits c t y then 1 else 0
    simp only [apply_ite star, star_one, star_zero, he]
  refine ⟨?_, hadj⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, hadj]
  have hs : gateCNOT c t * gateCNOT c t = 1 := by
    have he : (1 : Op n).submatrix (cnotBits c t) (cnotBits c t) = 1 := by
      exact Matrix.submatrix_one_equiv hi.toPerm
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
    dsimp only [pauliMatrix, qubitX, qubitZ] <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two,
      Fin.add_def, Matrix.one_apply]
private lemma cnot_word {n : ℕ} (c t : Fin n) (h : c ≠ t) (w : Fin n → Pauli)
    (d : ℂ) (a b : Pauli)
    (he : ∀ x y u v : Fin 2, pauliMatrix (w c) x u * pauliMatrix (w t) (y + x) (v + u) =
      d * (pauliMatrix a x u * pauliMatrix b y v)) :
    gateCNOT c t * wordOp w * (gateCNOT c t)ᴴ =
      d • wordOp (Function.update (Function.update w c a) t b) := by
  rw [(cnot_unitary c t h).2, cnot_action c t h]
  ext x y
  simp only [Matrix.submatrix_apply, wordOp, tensorOp, Matrix.of_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c)]
  rw [← Finset.mul_prod_erase (Finset.univ.erase c) _ (a := t) (by simp [h.symm])]
  conv_rhs => rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c)]
  conv_rhs =>
    rw [← Finset.mul_prod_erase (Finset.univ.erase c) _ (a := t) (by simp [h.symm])]
  dsimp only [cnotBits] ; simp only [Function.update_self, Function.update_of_ne h]
  rw [← mul_assoc, he, mul_assoc, mul_assoc]
  congr 3
  apply Finset.prod_congr rfl
  intro i hi
  have hic : i ≠ c := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
  have hit : i ≠ t := (Finset.mem_erase.mp hi).1
  simp only [Function.update_of_ne hic, Function.update_of_ne hit]
private lemma cnot_normalizes {n : ℕ} (c t : Fin n) (h : c ≠ t) (w : Fin n → Pauli) :
    gateCNOT c t * wordOp w * (gateCNOT c t)ᴴ ∈ PauliGroup n := by
  obtain ⟨d, a, b, hd, he⟩ := cnot_table (w c) (w t)
  exact ⟨d, hd, Function.update (Function.update w c a) t b, cnot_word c t h w d a b he⟩
private lemma local_table (A : Matrix (Fin 2) (Fin 2) ℂ)
    (ha : A = gateH ∨ A = gateS ∨ A = gateSᴴ) (p : Pauli) :
    ∃ (c : ℂ) (q : Pauli), Phase c ∧ A * pauliMatrix p * Aᴴ = c • pauliMatrix q := by
  have hs := TsirelsonInequality.sqrt_two_inv_mul_self
  rw [← Real.sqrt_div_self, ← pow_two, ← one_div] at hs
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
      dsimp only [gateS, pauliMatrix, gateH,
      D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.hadamard, s2, qubitX,
        qubitZ] <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im,
        map_ofNat]
      <;> nlinarith [hs]
private lemma local_word {n : ℕ} (i : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (w : Fin n → Pauli) (c : ℂ) (q : Pauli)
    (hq : A * pauliMatrix (w i) * Aᴴ = c • pauliMatrix q) :
    localOp i A * wordOp w * (localOp i A)ᴴ = c • wordOp (Function.update w i q) := by
  let R := wordOp (Function.update w i .I)
  have hsplit (p : Pauli) :
      localOp i (pauliMatrix p) * R = wordOp (Function.update w i p) := by
    cases p with
    | I => rw [show pauliMatrix .I = 1 from rfl, local_identity, one_mul]
    | X | Y | Z =>
      unfold localOp
      change tensorOp _ * tensorOp _ = tensorOp _
      rw [tensor_mul]
      congr 1
      funext j
      by_cases hj : j = i
      · subst j
        simp only [Function.update_self, show pauliMatrix .I = 1 from rfl, mul_one]
      · simp only [Function.update_of_ne hj, one_mul]
  have hfactor : wordOp w = localOp i (pauliMatrix (w i)) * R := by
    simpa only [Function.update_eq_self] using (hsplit (w i)).symm
  have hcomm : R * localOp i Aᴴ = localOp i Aᴴ * R := by
    unfold localOp
    change tensorOp _ * tensorOp _ = tensorOp _ * tensorOp _
    rw [tensor_mul, tensor_mul]
    congr 1
    funext j
    by_cases hj : j = i
    · subst j
      simp only [Function.update_self, show pauliMatrix .I = 1 from rfl, one_mul, mul_one]
    · simp only [Function.update_of_ne hj, one_mul, mul_one]
  rw [local_adjoint, hfactor, mul_assoc, mul_assoc, hcomm, ← mul_assoc,
    ← mul_assoc, local_product, local_product, hq]
  unfold localOp
  change tensorOp _ * tensorOp _ = c • tensorOp _
  rw [tensor_mul]
  have he : (fun j => Function.update (fun _ => (1 : Matrix (Fin 2) (Fin 2) ℂ))
      i (c • pauliMatrix q) j * pauliMatrix (Function.update w i .I j)) =
      fun j => Function.update (fun _ => (1 : ℂ)) i c j •
        pauliMatrix (Function.update w i q j) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp only [Function.update_self, show pauliMatrix .I = 1 from rfl, mul_one]
    · simp only [Function.update_of_ne hj, one_mul, one_smul]
  rw [he, D5.S3.Quantum.Information.BinaryStabilizerGraphNormalForm.tensor_smul,
    Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp only [Finset.prod_const_one, mul_one]
private lemma local_normalizes {n : ℕ} (i : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (ha : A = gateH ∨ A = gateS ∨ A = gateSᴴ) (w : Fin n → Pauli) :
    localOp i A * wordOp w * (localOp i A)ᴴ ∈ PauliGroup n := by
  obtain ⟨c, q, hc, hq⟩ := local_table A ha (w i)
  exact ⟨c, hc, Function.update w i q, local_word i A w c q hq⟩
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
    · rw [local_adjoint]
      have hH : gateH.IsHermitian :=
        ((show (pauliMatrix .X).IsHermitian from pauli_hermitian .X).add
          (show (pauliMatrix .Z).IsHermitian from pauli_hermitian .Z)).smul
          (show IsSelfAdjoint s2 from Complex.conj_ofReal _)
      rw [hH]
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
    simpa only [Matrix.conjTranspose_smul, word_hermitian, Matrix.smul_mul,
      show wordOp w * wordOp w = 1 from (wordUnit w).val_inv,
      Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, ite_true, mul_one] using he
  refine ⟨c, w, ?_, rfl⟩
  rcases hc with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  all_goals subst c; have hi := congrArg Complex.im hr; norm_num at hi
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
            (generalize x i = b; fin_cases b <;> (dsimp only [pauliMatrix,
              qubitZ] <;> simp [Matrix.one_apply]))
        _ = _ := congrArg (fun M : Op n => M x 0) tensor_one
    refine Or.inr ⟨?_, by simpa using he 0⟩
    ext x y
    change (wordOp w * (Matrix.single (0 : Bits n) 0 (1 : ℂ) : Op n)) x y =
      (Matrix.single (0 : Bits n) 0 (1 : ℂ) : Op n) x y
    by_cases hy : y = 0
    · subst y
      rw [Matrix.mul_single_apply_same, mul_one, he, Matrix.one_apply]
      simp only [Matrix.single_apply, and_true]
      exact if_congr (show x = 0 ↔ (0 : Bits n) = x from eq_comm) rfl rfl
    · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hy,
        Matrix.single_apply_of_col_ne _ _ (Ne.symm hy)]
  · push Not at hd
    obtain ⟨i, hi, hz⟩ := hd
    apply Or.inl
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    cases h : w i <;> (dsimp only [pauliMatrix, qubitX, qubitZ] ; simp_all)
private lemma pure_expectation {n : ℕ} {U P : Op n} (hu : U ∈ Clifford n)
    (hp : P ∈ PauliGroup n) (hh : Pᴴ = P) :
    (P * (U * vacuum n * Uᴴ)).trace = 0 ∨
      (((P * (U * vacuum n * Uᴴ)).trace = 1 ∨
        (P * (U * vacuum n * Uᴴ)).trace = -1) ∧
        P * (U * vacuum n * Uᴴ) = (P * (U * vacuum n * Uᴴ)).trace •
          (U * vacuum n * Uᴴ)) := by
  have hn := clifford_data (clifford_adjoint hu)
  have hq : (Uᴴ * P * U)ᴴ = Uᴴ * P * U :=
    Matrix.isHermitian_conjTranspose_mul_mul U hh
  obtain ⟨c, w, hc, hw⟩ := pauli_real (by simpa using hn.2 P hp) hq
  have ht : (P * (U * vacuum n * Uᴴ)).trace = c * wordOp w 0 0 := by
    calc
      _ = (Uᴴ * P * U * vacuum n).trace := by
        simpa only [mul_assoc] using Matrix.trace_mul_cycle (P * U) (vacuum n) Uᴴ
      _ = _ := by
        rw [hw, Matrix.smul_mul, Matrix.trace_smul]
        change c • (wordOp w * (Matrix.single (0 : Bits n) 0 (1 : ℂ) : Op n)).trace = _
        rw [Matrix.trace_mul_single] ; simp only [MulOpposite.op_one, one_smul, smul_eq_mul]
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
        simp only [mul_assoc]
        rw [← mul_assoc U Uᴴ, huR, one_mul]
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
  have h' : P * U * vacuum n = (P * (U * vacuum n * Uᴴ)).trace • (U * vacuum n) := by
    simpa only [mul_assoc] using h
  have hx := congrArg (fun A : Op n => A x 0) h'
  change (P * U * (Matrix.single (0 : Bits n) 0 (1 : ℂ) : Op n)) x 0 =
    (P * (U * vacuum n * Uᴴ)).trace • (U * (Matrix.single (0 : Bits n) 0 (1 : ℂ) : Op n)) x 0 at hx
  simpa only [Matrix.mul_single_apply_same, mul_one,
    Matrix.smul_apply, smul_eq_mul, Matrix.col_apply, Pi.smul_apply] using hx
private lemma anticommuting_support {n k : ℕ} (G : Fin k → Op n)
    (hg : ∀ i, G i ∈ PauliGroup n ∧ (G i)ᴴ = G i)
    (ha : ∀ i j, i ≠ j → G i * G j = -(G j * G i)) :
    ∀ ρ ∈ STAB n, tr (ρ * ∑ i, G i) ≤ 1 := by
  have hc : Convex ℝ {ρ : Op n | tr (ρ * ∑ i, G i) ≤ 1} :=
    convex_halfSpace_le ⟨fun A B => by
      dsimp only [tr, RHLinalg.rtrace, RCLike.re_eq_complex_re]
      simp [Matrix.add_mul, Matrix.trace_add],
      fun r A => by
        dsimp only [tr, RHLinalg.rtrace, RCLike.re_eq_complex_re]
        simp [Matrix.trace_smul]⟩ 1
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
    unfold tr RHLinalg.rtrace
    simp only [RCLike.re_eq_complex_re]
    rw [Matrix.mul_sum, Matrix.trace_sum]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => Matrix.trace_mul_comm _ _)
  change tr (ρ * ∑ i, G i) ≤ 1
  rw [ht]
  by_cases hz : ∀ i, e i = 0
  · simp only [hz, Finset.sum_const_zero, Complex.zero_re] ; norm_num
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
      dsimp only [pauliMatrix, qubitX, qubitZ] <;> norm_num [d, Matrix.mul_apply,
        Fin.sum_univ_two] <;> decide
  refine ⟨∏ i, d (w i), Finset.prod_induction _ _ (fun _ _ => phase_mul)
    (Or.inl rfl) (fun i _ => hd (w i)), ?_⟩
  ext x y
  dsimp only [conjugate] ; simp only [Matrix.map_apply, wordOp, tensorOp, Matrix.of_apply,
    Matrix.smul_apply, smul_eq_mul, star_prod, he, Finset.prod_mul_distrib]
private lemma conjugate_S_support {ρ : Op 3} (hρ : ρ ∈ STAB 3) :
    tr (ρ * conjugate S) ≤ 1 := by
  have hs : conjugate S = ∑ i : Fin 7, conjugate (wordOp (gammaWords i)) := by
    ext x y
    dsimp only [conjugate, S] ; simp only [Matrix.map_apply, Matrix.sum_apply, star_sum]
  rw [hs]
  apply anticommuting_support (fun i : Fin 7 => conjugate (wordOp (gammaWords i)))
    ?_ ?_ ρ hρ
  · intro i
    obtain ⟨c, hc, he⟩ := word_conjugate (gammaWords i)
    refine ⟨⟨c, hc, gammaWords i, he⟩, ?_⟩
    exact (show (wordOp (gammaWords i)).IsHermitian from word_hermitian _).map
      star (fun _ => rfl)
  · intro i j h
    have he := congrArg conjugate (gamma_anticommute i j h)
    change Complex.conjAe.mapMatrix (wordOp (gammaWords i) * wordOp (gammaWords j)) =
      Complex.conjAe.mapMatrix (-(wordOp (gammaWords j) * wordOp (gammaWords i))) at he
    change Complex.conjAe.mapMatrix (wordOp (gammaWords i)) *
      Complex.conjAe.mapMatrix (wordOp (gammaWords j)) =
      -(Complex.conjAe.mapMatrix (wordOp (gammaWords j)) *
        Complex.conjAe.mapMatrix (wordOp (gammaWords i)))
    simpa only [map_mul, map_neg] using he

private lemma pure_state {n : ℕ} {U : Op n} (hU : U ∈ Clifford n) :
    IsState (U * vacuum n * Uᴴ) := by
  have hu := clifford_data hU
  refine ⟨?_, ?_⟩
  · change (U * Matrix.single (0 : Bits n) 0 1 * Uᴴ).PosSemidef
    rw [Matrix.single_eq_single_vecMulVec_single]
    simpa only [Matrix.conjTranspose_conjTranspose, Pi.star_single, star_one] using
      (Matrix.posSemidef_vecMulVec_self_star
        (Pi.single (0 : Bits n) (1 : ℂ))).conjTranspose_mul_mul_same Uᴴ
  · rw [Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
    have hleft : Uᴴ * U = 1 := by
      simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hu.1
    calc
      (vacuum n * Uᴴ * U).trace = (vacuum n * (Uᴴ * U)).trace := by
        rw [Matrix.mul_assoc]
      _ = 1 := by rw [hleft, Matrix.mul_one]; exact Matrix.trace_single_eq_same _ _

private lemma stab_state {n : ℕ} {η : Op n} (hη : η ∈ STAB n) : IsState η := by
  refine convexHull_min (t := {A : Op n | IsState A}) ?_ ?_ hη
  · rintro A ⟨U, hU, rfl⟩
    exact pure_state hU
  · have hv : IsState (vacuum n) := by
      simpa only [Matrix.one_mul, Matrix.mul_one, Matrix.conjTranspose_one] using
        (pure_state (U := 1) (Clifford n).one_mem)
    have hc :=
      D5.S3.Quantum.Fibers.PhysicalFiber.finite_dimensional_physical_fiber
        (0 : Op n →ₗ[ℂ] (Empty → ℂ)) (vacuum n) hv.1 hv.2
    change Convex ℝ {A : Op n | A.PosSemidef ∧ A.trace = 1}
    simpa only [true_and, eq_self] using
      (show Convex ℝ {A : Op n | (0 : Empty → ℂ) = 0 ∧ A.PosSemidef ∧ A.trace = 1}
        from hc.2.2)

private lemma H_mem {n : ℕ} (i : Fin n) : localOp i gateH ∈ Clifford n :=
  Submonoid.subset_closure (Or.inl (Or.inl ⟨i, rfl⟩))
private lemma CNOT_mem {n : ℕ} (c t : Fin n) (h : c ≠ t) :
    gateCNOT c t ∈ Clifford n :=
  Submonoid.subset_closure (Or.inl (Or.inr (Or.inr ⟨c, t, h, rfl⟩)))
private lemma cnot_mulVec {n : ℕ} (c t : Fin n) (h : c ≠ t) (v : Bits n → ℂ) :
    gateCNOT c t *ᵥ v = fun x => v (cnotBits c t x) := by
  have hi := cnot_involutive c t h
  change (1 : Op n).submatrix id hi.toPerm *ᵥ v = _
  rw [Matrix.submatrix_mulVec_equiv, Matrix.one_mulVec]
  rfl
private def bellCircuit : Op 6 :=
  gateCNOT 2 5 * gateCNOT 1 4 * gateCNOT 0 3 *
    (localOp 0 gateH * localOp 1 gateH * localOp 2 gateH)
private lemma bellCircuit_mem : bellCircuit ∈ Clifford 6 := by
  unfold bellCircuit
  exact (Clifford 6).mul_mem
    ((Clifford 6).mul_mem ((Clifford 6).mul_mem
      (CNOT_mem 2 5 (by decide)) (CNOT_mem 1 4 (by decide)))
      (CNOT_mem 0 3 (by decide)))
    ((Clifford 6).mul_mem ((Clifford 6).mul_mem (H_mem 0) (H_mem 1)) (H_mem 2))
private lemma bellCircuit_vec : bellCircuit *ᵥ Pi.single 0 1 =
    fun x => if (splitBits 3 3 x).1 = (splitBits 3 3 x).2 then
      ((Real.sqrt 2 / 2 : ℝ) : ℂ) ^ 3 else 0 := by
  have he (x : Bits 6) : (localOp 0 gateH * localOp 1 gateH * localOp 2 gateH : Op 6) x 0 =
      if x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0 then
        ((Real.sqrt 2 / 2 : ℝ) : ℂ) ^ 3 else 0 := by
    have hh (a : Fin 2) : gateH a 0 = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
      fin_cases a <;> (dsimp only [pauliMatrix, gateH,
      D5.S3.Quantum.Information.BinaryStabilizerLocalInequivalence.hadamard,
        s2, qubitX, qubitZ] ; simp)
    unfold localOp
    rw [tensor_mul, tensor_mul]
    simp only [tensorOp, Matrix.of_apply, Fin.prod_univ_succ]
    simp only [Function.update_self, Function.update_of_ne (by decide : (0 : Fin 6) ≠ 1),
      Function.update_of_ne (by decide : (0 : Fin 6) ≠ 2)]
    simp [hh, Matrix.one_apply, pow_succ]
    split_ifs <;> simp_all [mul_assoc]
  unfold bellCircuit
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [cnot_mulVec _ _ (by decide), cnot_mulVec _ _ (by decide),
    cnot_mulVec _ _ (by decide)]
  ext x
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, he]
  have hz (a b : Fin 2) : a + b = 0 ↔ a = b := by revert a b; decide
  have hs : (splitBits 3 3 x).1 = (splitBits 3 3 x).2 ↔
      x 0 = x 3 ∧ x 1 = x 4 ∧ x 2 = x 5 := by
    constructor
    · intro h
      exact ⟨congrFun h 0, congrFun h 1, congrFun h 2⟩
    · rintro ⟨h0, h1, h2⟩
      funext i; fin_cases i <;> assumption
  dsimp only [cnotBits] ; simp [hz, hs, eq_comm]
private lemma bell_prepared : bell = bellCircuit * vacuum 6 * bellCircuitᴴ := by
  rw [show vacuum 6 = Matrix.vecMulVec (Pi.single 0 1) (star (Pi.single 0 1)) from by
    change Matrix.single (0 : Bits 6) 0 1 = _
    simpa only [Pi.star_single, star_one] using
      (Matrix.single_eq_single_vecMulVec_single (α := ℂ) (0 : Bits 6) 0)]
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  rw [← Matrix.star_mulVec, bellCircuit_vec]
  have hs := TsirelsonInequality.sqrt_two_inv_mul_self
  rw [← Real.sqrt_div_self, ← pow_two, ← one_div] at hs
  have hr : ((Real.sqrt 2 / 2 : ℝ) : ℂ) ^ 2 = (1 / 2 : ℂ) := by
    calc
      _ = (((Real.sqrt 2 / 2) ^ 2 : ℝ) : ℂ) := (Complex.ofReal_pow _ _).symm
      _ = ((1 / 2 : ℝ) : ℂ) := congrArg Complex.ofReal hs
      _ = _ := by norm_num
  ext x y
  change (if _ ∧ _ then (1 / 8 : ℂ) else 0) =
    (if _ then _ else 0) * star (if _ then _ else 0)
  by_cases hx : (splitBits 3 3 x).1 = (splitBits 3 3 x).2 <;>
    by_cases hy : (splitBits 3 3 y).1 = (splitBits 3 3 y).2
  all_goals simp only [hx, hy, and_self, and_false, false_and, if_true, if_false,
    star_pow, Complex.star_def, Complex.conj_ofReal, map_zero, mul_zero, zero_mul]
  rw [← pow_add, show (3 + 3 : ℕ) = 2 * 3 from rfl, pow_mul, hr]
  norm_num
private lemma bell_mem : bell ∈ STAB 6 :=
  subset_convexHull ℝ (PureStabilizer 6) ⟨bellCircuit, bellCircuit_mem, bell_prepared⟩
private lemma bell_trace (A B : Op 3) :
    tr (bell * tensor A (conjugate B)) = tr (A * Bᴴ) / 8 := by
  let e : Bits 6 ≃ Bits 3 × Bits 3 :=
    { toFun := splitBits 3 3, invFun := fun p => Fin.append p.1 p.2
      left_inv := fun x => Fin.append_castAdd_natAdd
      right_inv := by
        intro p
        apply Prod.ext
        · funext i; exact Fin.append_left p.1 p.2 i
        · funext i; exact Fin.append_right p.1 p.2 i }
  have ht : (bell * tensor A (conjugate B)).trace = (1 / 8 : ℂ) * (A * Bᴴ).trace := by
    change (∑ x : Bits 6, ∑ y : Bits 6,
      (if (e x).1 = (e x).2 ∧ (e y).1 = (e y).2 then (1 / 8 : ℂ) else 0) *
        (A (e y).1 (e x).1 * star (B (e y).2 (e x).2))) = _
    rw [← e.symm.sum_comp]
    simp only [Equiv.apply_symm_apply]
    conv_lhs => arg 2; ext x; rw [← e.symm.sum_comp]
    simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type, ite_mul, zero_mul]
    simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    unfold Matrix.trace Matrix.diag
    simp only [← Finset.mul_sum, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
    congr 1
    rw [Finset.sum_comm]
  unfold tr RHLinalg.rtrace
  simp only [RCLike.re_eq_complex_re]
  rw [ht]
  simp [Complex.mul_re, div_eq_mul_inv, mul_comm]
private lemma conjugate_linear {n : ℕ} (a b : ℝ) (T : Op n) :
    conjugate (a • 1 + b • T) = a • 1 + b • conjugate T := by
  change Complex.conjAe.mapMatrix (a • 1 + b • T) =
    a • 1 + b • Complex.conjAe.mapMatrix T
  rw [map_add, map_smul, map_smul, map_one]
private lemma linear_square {n : ℕ} (T : Op n)
    (hT : T * T = (7 : ℝ) • 1) (s : ℝ) :
    (1 + s • T) * (1 + s • T) = (1 + 7 * s ^ 2 : ℝ) • 1 + (2 * s) • T := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, hT]
  module
private lemma linear_posDef {n : ℕ} (T : Op n) (hA : Tᴴ = T)
    (hT : T * T = (7 : ℝ) • 1) (s : ℝ) (hs : 7 * s ^ 2 < 1) :
    (1 + s • T).PosDef := by
  let X : Op n := 1 + s • T
  have hx : Xᴴ = X := by
    simp only [X, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
      Matrix.conjTranspose_smul, star_trivial, hA]
  have he : X = (1 / 2 : ℝ) • (X * X + (1 - 7 * s ^ 2 : ℝ) • 1) := by
    dsimp only [X]
    rw [linear_square T hT s]
    module
  change X.PosDef
  have hp : (X * X).PosSemidef := by
    simpa only [hx] using Matrix.posSemidef_self_mul_conjTranspose X
  rw [he]
  exact (Matrix.PosDef.posSemidef_add hp
    (Matrix.PosDef.one.smul (show 0 < 1 - 7 * s ^ 2 by linarith))).smul (by norm_num)
private lemma polar_support (T : Op 3) (s : ℝ) (hs : 0 ≤ s)
    (hT : ∀ η ∈ STAB 3, tr (η * T) ≤ 1) {η : Op 3} (hη : η ∈ STAB 3) :
    tr (η * ((1 / (1 + s) : ℝ) • (1 + s • T))) ≤ 1 := by
  have ht := (stab_state hη).2
  have he : tr (η * ((1 / (1 + s) : ℝ) • (1 + s • T))) =
      (1 + s * tr (η * T)) / (1 + s) := by
    dsimp only [tr, RHLinalg.rtrace, RCLike.re_eq_complex_re]
    simp only [Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one,
      Matrix.trace_smul, Matrix.trace_add, ht, Complex.smul_re, Complex.add_re, Complex.one_re,
      smul_eq_mul]
    ring
  rw [he, div_le_iff₀ (by linarith : 0 < 1 + s)]
  nlinarith [hT η hη]
private lemma S_square_real : S * S = (7 : ℝ) • (1 : Op 3) := by
  rw [S_square]
  ext x y
  simp [Algebra.smul_def]
private lemma conjugate_S_square : conjugate S * conjugate S = (7 : ℝ) • (1 : Op 3) := by
  change S.map (starRingEnd ℂ) * S.map (starRingEnd ℂ) = _
  rw [← Matrix.map_mul, S_square_real]
  change conjugate ((7 : ℝ) • (1 : Op 3)) = _
  have he := conjugate_linear (7 : ℝ) 0 S
  simpa using he
private lemma sigma_state_support : IsState sigma ∧ tr (sigma * S) = 1 := by
  have he : sigma = (1 / 8 : ℝ) • (1 + (1 / 7 : ℝ) • S) := by
    unfold sigma sigmaMatrix
    module
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [he]
    exact ((linear_posDef S S_adjoint S_square_real (1 / 7) (by norm_num)).smul
      (by norm_num : (0 : ℝ) < 1 / 8)).posSemidef
  · dsimp only [sigma, sigmaMatrix]
    simp only [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one, S_trace,
      Fintype.card_fun, Fintype.card_fin]
    norm_num
  · dsimp only [sigma, sigmaMatrix, tr, RHLinalg.rtrace, RCLike.re_eq_complex_re]
    rw [Matrix.smul_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, S_square_real]
    simp only [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one, S_trace,
      Fintype.card_fun, Fintype.card_fin]
    norm_num [Complex.smul_re]
private lemma W_bell (s : ℝ) :
    tr (bell * tensor (W s) (conjugate (W s))) = (1 + 7 * s ^ 2) / (1 + s) ^ 2 := by
  have ha : (W s)ᴴ = W s := by
    dsimp only [W] ; simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_one, star_trivial, S_adjoint]
  rw [bell_trace, ha]
  have he : W s * W s = ((1 / (1 + s) : ℝ) ^ 2) •
      ((1 + 7 * s ^ 2 : ℝ) • 1 + (2 * s) • S) := by
    unfold W
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      linear_square S S_square_real s, ← sq (1 / (1 + s) : ℝ)]
  rw [he]
  have ht : (1 : Op 3).trace = (8 : ℂ) := by
    simp [Matrix.trace_one]
  dsimp only [tr, RHLinalg.rtrace, RCLike.re_eq_complex_re]
  simp only [Matrix.trace_smul, Matrix.trace_add, S_trace, ht, smul_zero,
    add_zero, Complex.smul_re, smul_eq_mul]
  change (1 / (1 + s)) ^ 2 * ((1 + 7 * s ^ 2) * 8) / 8 = _
  simp only [div_pow, one_pow]
  ring
theorem stabilizer_polar_tensor_escape (s : ℝ) (hl : 1 / 3 < s) (hu : 7 * s ^ 2 < 1) :
    (∀ (n : ℕ) (η : Op n), η ∈ STAB n → IsState η) ∧
    (IsState sigma ∧ tr (sigma * S) = 1) ∧
    Sᴴ = S ∧ S * S = (7 : ℂ) • (1 : Op 3) ∧ S.trace = 0 ∧
    (∀ A B : Op 3, tr (bell * tensor A (conjugate B)) = tr (A * Bᴴ) / 8) ∧
    bell ∈ STAB 6 ∧ (W s).PosDef ∧ (conjugate (W s)).PosDef ∧
    (∀ η ∈ STAB 3, tr (η * W s) ≤ 1 ∧ tr (η * conjugate (W s)) ≤ 1) ∧
    tr (bell * tensor (W s) (conjugate (W s))) = (1 + 7 * s ^ 2) / (1 + s) ^ 2 ∧
    1 < tr (bell * tensor (W s) (conjugate (W s))) := by
  have hs : 0 < s := by linarith
  have hc : conjugate (W s) = (1 / (1 + s) : ℝ) • (1 + s • conjugate S) := by
    have he := conjugate_linear (1 / (1 + s)) ((1 / (1 + s)) * s) S
    dsimp only [W] ; simpa only [smul_add, smul_smul] using he
  refine ⟨fun n η hη => stab_state hη, sigma_state_support, S_adjoint, S_square, S_trace,
    bell_trace, bell_mem, (linear_posDef S S_adjoint S_square_real s hu).smul (by positivity),
    ?_, ?_, W_bell s, ?_⟩
  · rw [hc]
    exact (linear_posDef (conjugate S)
      ((show S.IsHermitian from S_adjoint).map star (fun _ => rfl)).eq
      conjugate_S_square s hu).smul (by positivity)
  · intro η hη
    rw [hc]
    exact ⟨polar_support S s hs.le (fun _ h => S_support h) hη,
      polar_support (conjugate S) s hs.le (fun _ h => conjugate_S_support h) hη⟩
  · rw [W_bell, lt_div_iff₀ (sq_pos_of_pos (by linarith : 0 < 1 + s))]
    nlinarith
end D5.S3.Quantum.Magic.ThreeQubitStabilizerPolarEscape
