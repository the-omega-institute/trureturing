/- GID: D5/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant
   generality: G
   mirror-B: D5/B/S3/Quantum/FockSpace/ForbiddenNeighbourDeterminant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Forbidden-neighbour configurations have a Gram determinant and quantum readout. -/

import D5.S1.Words.AdmissibleWords.AdmissibleCount

namespace D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant

open scoped BigOperators Matrix

/-- Binary configurations with no adjacent occupied coordinates. -/
def legalConfiguration {n : Nat} (b : Fin n → Bool) : Prop :=
  ∀ (i j : Fin n), i.val + 1 = j.val → b i = false ∨ b j = false

/-- Finite decidability of the exclusion rule. -/
instance legalConfigurationDecidable {n : Nat} (b : Fin n → Bool) :
    Decidable (legalConfiguration b) :=
  inferInstanceAs (Decidable (∀ i j, i.val + 1 = j.val → b i = false ∨ b j = false))

private theorem legal_cons {n : Nat} (a : Bool) (b : Fin (n+1) → Bool) :
    legalConfiguration (Fin.cons a b) ↔
      (a = false ∨ b 0 = false) ∧ legalConfiguration b := by
  constructor
  · intro h
    constructor
    · simpa using h 0 1 (by simp)
    · intro i j hij
      simpa using h i.succ j.succ (by simpa using hij)
  · rintro ⟨hfront, htail⟩ i j
    refine Fin.cases ?_ (fun i => ?_) i
    · intro hij
      have : j = 1 := Fin.ext (by simpa using hij.symm)
      simpa [this] using hfront
    · intro hij
      revert hij
      refine Fin.cases ?_ (fun j => ?_) j
      · simp
      · intro hij
        simpa using htail i j (by simpa using hij)

private def configPartition {R : Type*} [CommSemiring R] {n : Nat} (w : Fin n → R) : R :=
  ∑ b : Fin n → Bool, if legalConfiguration b then
    ∏ i, w i ^ (b i).toNat else 0

private theorem sum_bool_vectors {R : Type*} [AddCommMonoid R] {n : Nat}
    (f : (Fin (n+1) → Bool) → R) :
    ∑ b, f b = (∑ b : Fin n → Bool, f (Fin.cons false b)) +
      ∑ b : Fin n → Bool, f (Fin.cons true b) := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => Bool))]
  simp [Fintype.sum_prod_type, Fin.consEquiv, add_comm]

private theorem legal_cons_false {n : Nat} (b : Fin n → Bool) :
    legalConfiguration (Fin.cons false b) ↔ legalConfiguration b := by
  constructor
  · intro h i j hij
    simpa using h i.succ j.succ (by simpa using hij)
  · intro h i j
    refine Fin.cases ?_ (fun i => ?_) i
    · simp
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp
      · intro hij
        simpa using h i j (by simpa using hij)

private theorem legal_true_false {n : Nat} (b : Fin n → Bool) :
    legalConfiguration (Fin.cons true (Fin.cons false b)) ↔ legalConfiguration b := by
  simp [legal_cons, legal_cons_false]

private theorem illegal_true_true {n : Nat} (b : Fin n → Bool) :
    ¬ legalConfiguration (Fin.cons true (Fin.cons true b)) := by
  simp [legal_cons]

private theorem config_partition_recurrence {R : Type*} [CommSemiring R] {n : Nat}
    (w : Fin (n+2) → R) :
    configPartition w = configPartition (fun i => w i.succ) +
      w 0 * configPartition (fun i => w i.succ.succ) := by
  unfold configPartition
  rw [sum_bool_vectors]
  congr 1
  · apply Finset.sum_congr rfl
    intro b _
    simp [legal_cons_false, Fin.prod_univ_succ]
  · rw [sum_bool_vectors]
    simp only [legal_true_false, illegal_true_true, ite_false,
      Finset.sum_const_zero, add_zero]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : legalConfiguration b
    · simp [hb, Fin.prod_univ_succ]
    · simp [hb]

private theorem det_sparse_front {R : Type*} [CommRing R] {n : Nat}
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) R)
    (hr : ∀ j : Fin n, A 0 j.succ.succ = 0)
    (hc : ∀ i : Fin n, A i.succ.succ 0 = 0) :
    A.det = A 0 0 * (A.submatrix Fin.succ Fin.succ).det -
      A 0 1 * A 1 0 *
        (A.submatrix (fun i : Fin n => i.succ.succ)
          (fun j : Fin n => j.succ.succ)).det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.succ_zero_eq_one, Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero,
    Fin.val_succ, hr, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero]
  have hminor :
      (A.submatrix Fin.succ (1 : Fin (n+2)).succAbove).det =
      A 1 0 * (A.submatrix (fun i : Fin n => i.succ.succ)
        (fun j : Fin n => j.succ.succ)).det := by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero,
      Matrix.submatrix_apply]
    have hzero : (1 : Fin (n+2)).succAbove 0 = 0 := by
      simp
    rw [hzero]
    simp only [hc, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
    congr 2
  rw [hminor]
  norm_num [Fin.val_one']
  ring

private def pathMatrix {R : Type*} [CommRing R] (n : Nat) (a b : Nat → R) :
    Matrix (Fin n) (Fin n) R := fun i j =>
  if i = j then 1 else if i.val + 1 = j.val then a i.val
    else if j.val + 1 = i.val then b j.val else 0

private theorem path_det_recurrence {R : Type*} [CommRing R] (n : Nat)
    (a b : Nat → R) :
    (pathMatrix (n+2) a b).det =
      (pathMatrix (n+1) (fun i => a (i+1)) (fun i => b (i+1))).det -
        a 0 * b 0 * (pathMatrix n (fun i => a (i+2)) (fun i => b (i+2))).det := by
  rw [det_sparse_front _ (by intros; simp [pathMatrix, Fin.ext_iff])
    (by intros; simp [pathMatrix, Fin.ext_iff])]
  have htail : (pathMatrix (n+2) a b).submatrix Fin.succ Fin.succ =
      pathMatrix (n+1) (fun i => a (i+1)) (fun i => b (i+1)) := by
    ext i j
    simp [pathMatrix, Matrix.submatrix_apply, Fin.ext_iff, Nat.add_right_cancel_iff]
  have htail2 :
      (pathMatrix (n+2) a b).submatrix (fun i : Fin n => i.succ.succ)
        (fun i : Fin n => i.succ.succ) =
      pathMatrix n (fun i => a (i+2)) (fun i => b (i+2)) := by
    ext i j
    simp [pathMatrix, Matrix.submatrix_apply, Fin.ext_iff, Nat.add_right_cancel_iff,
      Nat.add_assoc]
  rw [htail, htail2]
  simp [pathMatrix]

private theorem path_det_eq_configuration (n : Nat) {R : Type*} [CommRing R]
    (a b : Nat → R) :
    (pathMatrix (n+1) a b).det =
      configPartition (fun i : Fin n => -(a i.val * b i.val)) := by
  induction n using Nat.twoStepInduction generalizing a b with
  | zero => simp [pathMatrix, configPartition, legalConfiguration]
  | one =>
    rw [path_det_recurrence]
    simp [pathMatrix, configPartition, legalConfiguration,
      sum_bool_vectors, sub_eq_add_neg]
  | more n ih ih1 =>
    rw [path_det_recurrence, config_partition_recurrence, ih1, ih]
    simp [sub_eq_add_neg, neg_mul, Nat.add_assoc]

private def interleave (d : Nat) : Fin d ⊕ Fin d ≃ Fin (2*d) where
  toFun
    | .inl i => ⟨2*i.val, by omega⟩
    | .inr i => ⟨2*i.val+1, by omega⟩
  invFun k := if k.val % 2 = 0 then .inl ⟨k.val/2, by omega⟩
    else .inr ⟨k.val/2, by omega⟩
  left_inv x := by
    rcases x with i | i
    · simp
    · simp
      apply Fin.ext
      dsimp
      omega
  right_inv k := by
    by_cases h : k.val % 2 = 0
    · simp only [h]
      apply Fin.ext
      dsimp
      omega
    · simp only [h]
      apply Fin.ext
      dsimp
      omega

private def lowerBidiagonalS {R : Type*} [Zero R] (d : Nat) (s : Nat → R) :
    Matrix (Fin d) (Fin d) R := fun i j =>
  if i = j then s (2*i.val) else if j.val+1 = i.val then s (2*j.val+1) else 0

private def upperEdge {R : Type*} [Ring R] (v : R) (s : Nat → R) (i : Nat) : R :=
  if i % 2 = 0 then s i else -v * s i

private def lowerEdge {R : Type*} [Ring R] (v : R) (s : Nat → R) (i : Nat) : R :=
  if i % 2 = 0 then -v * s i else s i

private theorem path_reindex_block {R : Type*} [CommRing R]
    (d : Nat) (v : R) (s : Nat → R) :
    (pathMatrix (2*d) (upperEdge v s) (lowerEdge v s)).submatrix
      (interleave d) (interleave d) =
      Matrix.fromBlocks (1 : Matrix (Fin d) (Fin d) R) (lowerBidiagonalS d s)
        (-v • (lowerBidiagonalS d s).transpose) 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [pathMatrix, interleave, Matrix.submatrix_apply, Matrix.one_apply,
      Fin.ext_iff, show 2*i.val+1 ≠ 2*j.val by omega,
      show 2*j.val+1 ≠ 2*i.val by omega]
  · by_cases hij : i = j
    · subst j
      simp [pathMatrix, interleave, lowerBidiagonalS, Matrix.submatrix_apply,
        upperEdge, Fin.ext_iff]
    · have hne : i.val ≠ j.val := Fin.val_ne_of_ne hij
      simp [pathMatrix, interleave, lowerBidiagonalS, Matrix.submatrix_apply,
        lowerEdge, Fin.ext_iff, hne, show 2*i.val ≠ 2*j.val+1 by omega,
        show (2*j.val+1+1 = 2*i.val) ↔ j.val+1=i.val by omega]
  · by_cases hij : i = j
    · subst j
      simp [pathMatrix, interleave, lowerBidiagonalS, Matrix.submatrix_apply,
        lowerEdge, Fin.ext_iff, show 2*i.val+1+1 ≠ 2*i.val by omega]
    · have hne : j.val ≠ i.val := Fin.val_ne_of_ne (Ne.symm hij)
      simp [pathMatrix, interleave, lowerBidiagonalS, Matrix.submatrix_apply,
        upperEdge, Fin.ext_iff, hne,
        show 2*i.val+1 ≠ 2*j.val by omega,
        show (2*i.val+1+1 = 2*j.val) ↔ i.val+1=j.val by omega]
      split_ifs <;> simp
  · simp [pathMatrix, interleave, Matrix.submatrix_apply, Matrix.one_apply,
      Fin.ext_iff, show 2*i.val+1 ≠ 2*j.val by omega,
      show 2*j.val+1 ≠ 2*i.val by omega]

private theorem config_partition_eq_gram_squares {R : Type*} [CommRing R]
    (d : Nat) (hd : 1 ≤ d) (v : R) (s : Nat → R) :
    configPartition (fun i : Fin (2*d-1) => v * (s i.val)^2) =
      Matrix.det (1 + v • ((lowerBidiagonalS d s).transpose * lowerBidiagonalS d s)) := by
  have hsize : 2*d-1+1 = 2*d := by omega
  have hpath := path_det_eq_configuration (2*d-1) (upperEdge v s) (lowerEdge v s)
  rw [hsize] at hpath
  have hedge : (fun i : Fin (2*d-1) => -(upperEdge v s i.val * lowerEdge v s i.val)) =
      (fun i => v * (s i.val)^2) := by
    funext i
    simp only [upperEdge, lowerEdge]
    split <;> ring
  rw [hedge] at hpath
  rw [← hpath, ← Matrix.det_submatrix_equiv_self (interleave d), path_reindex_block,
    Matrix.det_fromBlocks_one₁₁]
  simp [neg_smul, sub_neg_eq_add]

/-- The total number of occupied coordinates. -/
def occupationCount {n : Nat} (b : Fin n → Bool) : Nat := ∑ i, (b i).toNat

/-- The actual configuration sum as a real polynomial, with no square roots in its coefficients. -/
noncomputable def forbiddenPartition {n : Nat} (w : Fin n → ℝ) : Polynomial ℝ :=
  ∑ b : {b : Fin n → Bool // legalConfiguration b},
    Polynomial.X ^ occupationCount b.val * Polynomial.C (∏ i, w i ^ (b.val i).toNat)

private theorem forbidden_partition_as_config {n : Nat} (w : Fin n → ℝ) :
    forbiddenPartition w = configPartition (fun i => Polynomial.X * Polynomial.C (w i)) := by
  unfold forbiddenPartition configPartition
  conv_rhs => rw [← Finset.sum_filter,
    Finset.sum_subtype _ (p := legalConfiguration) (by simp)]
  apply Finset.sum_congr rfl
  intro b _
  simp [occupationCount, mul_pow, Finset.prod_mul_distrib, ← Finset.prod_pow_eq_pow_sum,
    map_prod, map_pow]
  exact mul_comm _ _

/-- Odd-weight square roots on the diagonal and even-weight square roots on the subdiagonal. -/
noncomputable def lowerBidiagonal {d : Nat} (w : Fin (2*d-1) → ℝ) :
    Matrix (Fin d) (Fin d) ℝ := fun i j =>
  if i = j then Real.sqrt (w ⟨2*i.val, by omega⟩)
  else if h : j.val+1 = i.val then Real.sqrt (w ⟨2*j.val+1, by omega⟩) else 0

private noncomputable def weightAt {n : Nat} (w : Fin n → ℝ) (i : Nat) : ℝ :=
  if h : i < n then w ⟨i,h⟩ else 0

private theorem lower_bidiagonal_map {R : Type*} [CommRing R] (f : ℝ →+* R)
    {d : Nat} (w : Fin (2*d-1) → ℝ) :
    (lowerBidiagonal w).map f = lowerBidiagonalS d (fun i => f (Real.sqrt (weightAt w i))) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [lowerBidiagonal, lowerBidiagonalS, weightAt, show 2*i.val < 2*d-1 by omega]
  · by_cases h : j.val+1=i.val
    · simp [lowerBidiagonal, lowerBidiagonalS, weightAt, hij, h,
        show 2*j.val+1 < 2*d-1 by omega]
    · simp [lowerBidiagonal, lowerBidiagonalS, hij, h]

private theorem forbidden_partition_eq_gram_determinant {d : Nat} (hd : 1 ≤ d)
    (w : Fin (2*d-1) → ℝ) (hw : ∀ i, 0 ≤ w i) :
    forbiddenPartition w = Matrix.det ((1 : Matrix (Fin d) (Fin d) (Polynomial ℝ)) +
      (Polynomial.X : Polynomial ℝ) •
      ((lowerBidiagonal (d := d) w).transpose * lowerBidiagonal w).map Polynomial.C) := by
  rw [forbidden_partition_as_config, Matrix.map_mul, Matrix.transpose_map,
    lower_bidiagonal_map]
  convert config_partition_eq_gram_squares d hd Polynomial.X
    (fun i => Polynomial.C (Real.sqrt (weightAt w i))) using 1
  congr 1
  funext i
  simp [weightAt, i.isLt, ← map_pow, Real.sq_sqrt (hw i)]

/-- The real Gram matrix is positive semidefinite, including singular weights. -/
theorem gramPosSemidef {d : Nat} (w : Fin (2*d-1) → ℝ) :
    ((lowerBidiagonal (d := d) w).transpose * lowerBidiagonal w).PosSemidef := by
  simpa using Matrix.posSemidef_conjTranspose_mul_self (lowerBidiagonal (d := d) w)

/-- The real eigenvalue list of the explicitly constructed Gram matrix. -/
noncomputable def gramEigenvalue {d : Nat} (w : Fin (2*d-1) → ℝ) : Fin d → ℝ :=
  (gramPosSemidef (d := d) w).isHermitian.eigenvalues

private theorem det_one_add_smul_hermitian {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.IsHermitian) (v : ℝ) :
    (1 + v • A).det = ∏ i, (1 + v * hA.eigenvalues i) := by
  let E := Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
  have hm : 1 + v • A = E (1 + v • Matrix.diagonal hA.eigenvalues) := by
    rw [map_add, map_one, map_smul]
    congr 2
    exact hA.spectral_theorem
  rw [hm]
  change ((hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) *
    (1 + v • Matrix.diagonal hA.eigenvalues) *
    star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)).det = _
  rw [Matrix.det_conj_of_mul_eq_one (Unitary.coe_mul_star_self _)
    (Unitary.coe_star_mul_self _)]
  have hdg : (1 : Matrix (Fin d) (Fin d) ℝ) + v • Matrix.diagonal hA.eigenvalues =
      Matrix.diagonal (fun i => 1 + v * hA.eigenvalues i) := by
    ext i j
    by_cases h : i=j <;> simp [h]
  rw [hdg, Matrix.det_diagonal]

private theorem forbidden_partition_factorization {d : Nat} (hd : 1 ≤ d)
    (w : Fin (2*d-1) → ℝ) (hw : ∀ i, 0 ≤ w i) :
    forbiddenPartition w = ∏ i : Fin d,
      (1 + Polynomial.C (gramEigenvalue (d := d) w i) * Polynomial.X) := by
  apply Polynomial.eq_of_infinite_eval_eq
  suffices ∀ v : ℝ, (forbiddenPartition w).eval v =
      (∏ i : Fin d, (1 + Polynomial.C (gramEigenvalue (d := d) w i) * Polynomial.X)).eval v by
    simpa [this] using Set.infinite_univ (α := ℝ)
  intro v
  rw [forbidden_partition_eq_gram_determinant hd w hw]
  change (Polynomial.evalRingHom v) (Matrix.det _) = _
  rw [RingHom.map_det]
  have hm : ((1 : Matrix (Fin d) (Fin d) (Polynomial ℝ)) +
      (Polynomial.X : Polynomial ℝ) •
        ((lowerBidiagonal (d := d) w).transpose * lowerBidiagonal w).map Polynomial.C).map
        (Polynomial.evalRingHom v) =
      1 + v • ((lowerBidiagonal (d := d) w).transpose * lowerBidiagonal w) := by
    ext i j
    by_cases h : i=j <;> simp [h, Matrix.mul_apply, Polynomial.eval_finsetSum]
  rw [RingHom.mapMatrix_apply, hm,
    det_one_add_smul_hermitian _ (gramPosSemidef w).isHermitian]
  simp only [gramEigenvalue, Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_one,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  apply Finset.prod_congr rfl
  intro i _
  rw [mul_comm]

private theorem forbidden_partition_roots_negative {d : Nat} (hd : 1 ≤ d)
    (w : Fin (2*d-1) → ℝ) (hw : ∀ i, 0 ≤ w i) (z : ℂ)
    (hz : (forbiddenPartition w).eval₂ Complex.ofRealHom z = 0) :
    ∃ t : ℝ, t < 0 ∧ z = Complex.ofReal t ∧
      ∃ i : Fin d, 0 < gramEigenvalue w i ∧ t = -(gramEigenvalue w i)⁻¹ := by
  rw [forbidden_partition_factorization hd w hw] at hz
  simp only [Polynomial.eval₂_finsetProd, Polynomial.eval₂_add, Polynomial.eval₂_one,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Finset.prod_eq_zero_iff, Finset.mem_univ, true_and] at hz
  obtain ⟨i, hi⟩ := hz
  have hnonneg : 0 ≤ gramEigenvalue (d := d) w i :=
    (gramPosSemidef w).eigenvalues_nonneg i
  have hne : gramEigenvalue (d := d) w i ≠ 0 := by
    intro h
    simp [h] at hi
  have hpos : 0 < gramEigenvalue (d := d) w i := lt_of_le_of_ne hnonneg (Ne.symm hne)
  refine ⟨-(gramEigenvalue (d := d) w i)⁻¹, neg_neg_of_pos (inv_pos.mpr hpos), ?_, i, hpos, rfl⟩
  have hcz : (gramEigenvalue (d := d) w i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hne
  apply (mul_left_cancel₀ hcz)
  push_cast
  rw [mul_neg, mul_inv_cancel₀ hcz]
  linear_combination hi

private theorem partition_eval {n : Nat} (w : Fin n → ℝ) (r : ℝ) :
    (forbiddenPartition w).eval r =
      ∑ b : {b : Fin n → Bool // legalConfiguration b},
        r ^ occupationCount b.val * ∏ i, w i ^ (b.val i).toNat := by
  simp [forbiddenPartition, Polynomial.eval_finsetSum, Polynomial.eval_prod]

private theorem forbidden_partition_eval_pos {n : Nat} (w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (r : ℝ) (hr : 0 < r) :
    0 < (forbiddenPartition w).eval r := by
  rw [partition_eval]
  let empty : {b : Fin n → Bool // legalConfiguration b} :=
    ⟨fun _ => false, by simp [legalConfiguration]⟩
  have hterm : ∀ b : {b : Fin n → Bool // legalConfiguration b},
      0 ≤ r ^ occupationCount b.val * ∏ i, w i ^ (b.val i).toNat := by
    intro b
    exact mul_nonneg (pow_nonneg hr.le _) (Finset.prod_nonneg fun i _ => pow_nonneg (hw i) _)
  apply Finset.sum_pos' (fun b _ => hterm b)
  refine ⟨empty, Finset.mem_univ _, ?_⟩
  simp [empty, occupationCount]

/-- Configuration amplitudes with the exact half-power normalization. -/
noncomputable def quantumState {n : Nat} (w : Fin n → ℝ) (r : ℝ) :
    {b : Fin n → Bool // legalConfiguration b} → ℂ := fun b =>
  Complex.ofReal ((Real.sqrt ((forbiddenPartition w).eval r))⁻¹ *
    r ^ ((occupationCount b.val : ℝ) / 2) * ∏ i, w i ^ (((b.val i).toNat : ℝ) / 2))

/-- The diagonal occupation-number observable. -/
noncomputable def numberOperator (n : Nat) :
    Matrix {b : Fin n → Bool // legalConfiguration b}
      {b : Fin n → Bool // legalConfiguration b} ℂ :=
  Matrix.diagonal (fun b => (occupationCount b.val : ℂ))

private theorem quantum_state_basis_sum {n : Nat} (w : Fin n → ℝ) (r : ℝ) :
    quantumState w r = (Complex.ofReal (Real.sqrt ((forbiddenPartition w).eval r)))⁻¹ •
      ∑ b : {b : Fin n → Bool // legalConfiguration b},
        Complex.ofReal (r ^ ((occupationCount b.val : ℝ) / 2) *
          ∏ i, w i ^ (((b.val i).toNat : ℝ) / 2)) • Pi.single b (1 : ℂ) := by
  ext b
  simp [quantumState, Finset.sum_apply, Pi.single_apply, mul_assoc]

private theorem half_rpow_sq (x : ℝ) (hx : 0 ≤ x) (k : Nat) :
    (x ^ ((k : ℝ) / 2)) ^ (2 : Nat) = x ^ k := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

private theorem state_weight {n : Nat} (w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (r : ℝ) (hr : 0 < r)
    (b : {b : Fin n → Bool // legalConfiguration b}) :
    star (quantumState w r b) * quantumState w r b =
      Complex.ofReal ((r ^ occupationCount b.val * ∏ i, w i ^ (b.val i).toNat) /
        (forbiddenPartition w).eval r) := by
  have hp := forbidden_partition_eval_pos w hw r hr
  simp only [quantumState, Complex.star_def, Complex.conj_ofReal,
    ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  rw [← sq, mul_pow, mul_pow, inv_pow, Real.sq_sqrt hp.le, half_rpow_sq r hr.le,
    ← Finset.prod_pow]
  simp_rw [half_rpow_sq _ (hw _) _]
  ring

private theorem quantum_state_normalized {n : Nat} (w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (r : ℝ) (hr : 0 < r) :
    dotProduct (star (quantumState w r)) (quantumState w r) = 1 := by
  unfold dotProduct
  simp only [Pi.star_apply, state_weight w hw r hr]
  rw [← Complex.ofReal_sum, ← Finset.sum_div, ← partition_eval,
    div_self (ne_of_gt (forbidden_partition_eval_pos w hw r hr))]
  simp

private theorem number_phase_action (n : Nat) (theta : ℝ)
    (v : {b : Fin n → Bool // legalConfiguration b} → ℂ) :
    (NormedSpace.exp (((theta : ℂ) * Complex.I) • numberOperator n)) *ᵥ v =
      fun b => Complex.exp ((theta : ℂ) * Complex.I) ^ occupationCount b.val * v b := by
  rw [numberOperator, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  ext b
  simp [Matrix.mulVec_diagonal, Pi.exp_def, ← Complex.exp_eq_exp_ℂ,
    mul_comm ((theta : ℂ) * Complex.I), Complex.exp_nat_mul]

private theorem quantum_partition_readout {n : Nat} (w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) (r : ℝ) (hr : 0 < r) (theta : ℝ) :
    dotProduct (star (quantumState w r))
      ((NormedSpace.exp (((theta : ℂ) * Complex.I) • numberOperator n)) *ᵥ quantumState w r) =
      (forbiddenPartition w).eval₂ Complex.ofRealHom
        ((r : ℂ) * Complex.exp ((theta : ℂ) * Complex.I)) /
        Complex.ofReal ((forbiddenPartition w).eval r) := by
  rw [number_phase_action]
  unfold dotProduct
  conv_rhs => rw [forbiddenPartition, Polynomial.eval₂_finsetSum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  simp only [Pi.star_apply, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, Complex.ofRealHom_eq_coe]
  calc
    star (quantumState w r b) *
        (Complex.exp ((theta : ℂ) * Complex.I) ^ occupationCount b.val * quantumState w r b) =
      Complex.exp ((theta : ℂ) * Complex.I) ^ occupationCount b.val *
        (star (quantumState w r b) * quantumState w r b) := by ring
    _ = _ := by
      rw [state_weight w hw r hr]
      push_cast
      rw [mul_pow]
      simp only [forbiddenPartition]
      ring

private theorem legal_iff_adm (n : Nat) (b : Fin n → Bool) :
    legalConfiguration b ↔ D5.S1.Words.AdmissibleWords.AdmissibleCount.Adm n b := by
  induction n using Nat.twoStepInduction with
  | zero => simp [legalConfiguration, D5.S1.Words.AdmissibleWords.AdmissibleCount.Adm]
  | one => simp [legalConfiguration, D5.S1.Words.AdmissibleWords.AdmissibleCount.Adm]
  | more n _ ih =>
    have hb : legalConfiguration b ↔
        (b 0 = false ∨ b 1 = false) ∧ legalConfiguration (Fin.tail b) := by
      conv_lhs => rw [← Fin.cons_self_tail b]
      simpa [Fin.tail, Fin.succ_zero_eq_one] using legal_cons (b 0) (Fin.tail b)
    rw [hb, ih, D5.S1.Words.AdmissibleWords.AdmissibleCount.Adm]
    cases b 0 <;> cases b 1 <;> simp

private theorem configuration_dimension {d : Nat} (hd : 1 ≤ d) :
    Fintype.card {b : Fin (2*d-1) → Bool // legalConfiguration b} = Nat.fib (2*d+1) := by
  calc
    _ = Fintype.card {b : Fin (2*d-1) → Bool //
        D5.S1.Words.AdmissibleWords.AdmissibleCount.Adm (2*d-1) b} :=
      Fintype.card_congr (Equiv.subtypeEquivRight (fun b => legal_iff_adm _ b))
    _ = _ := by
      rw [D5.S1.Words.AdmissibleWords.AdmissibleCount.admissibleWord_card_eq_fib]
      congr 1
      omega

/-- The self-adjoint bipartite single-particle tunnelling matrix. -/
noncomputable def tunnellingMatrix {d : Nat} (w : Fin (2*d-1) → ℝ) :
    Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ :=
  Matrix.fromBlocks 0 (lowerBidiagonal w) (lowerBidiagonal w).transpose 0

private theorem block_characteristic_nonzero {d : Nat} (L : Matrix (Fin d) (Fin d) ℝ)
    (v : ℝ) (hv : v ≠ 0) :
    (v • (1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ) -
      Matrix.fromBlocks 0 L L.transpose 0).det =
      (v^2 • (1 : Matrix (Fin d) (Fin d) ℝ) - L.transpose * L).det := by
  let hinv : Invertible (v • (1 : Matrix (Fin d) (Fin d) ℝ)) :=
    ⟨v⁻¹ • 1, by simp [smul_smul, hv], by simp [smul_smul, hv]⟩
  have hm : v • (1 : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℝ) -
      Matrix.fromBlocks 0 L L.transpose 0 =
      Matrix.fromBlocks (v • 1) (-L) (-L.transpose) (v • 1) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply]
  rw [hm, Matrix.det_fromBlocks₁₁]
  change (v • (1 : Matrix (Fin d) (Fin d) ℝ)).det *
    (v • 1 - -L.transpose * (v⁻¹ • 1) * -L).det = _
  rw [Matrix.det_smul, Matrix.det_one, mul_one,
    ← Matrix.det_smul]
  congr 1
  simp [smul_sub, smul_smul, pow_two, hv]

private theorem eval_pencil {d : Nat} (A : Matrix (Fin d) (Fin d) ℝ)
    (p q : Polynomial ℝ) (v : ℝ) :
    (Matrix.det (p • (1 : Matrix (Fin d) (Fin d) (Polynomial ℝ)) +
      q • A.map Polynomial.C)).eval v = (p.eval v • 1 + q.eval v • A).det := by
  change (Polynomial.evalRingHom v) (Matrix.det _) = _
  rw [RingHom.map_det, RingHom.mapMatrix_apply]
  congr 1
  ext i j
  by_cases h : i=j <;> simp [h]

private theorem tunnelling_characteristic {d : Nat} (w : Fin (2*d-1) → ℝ) :
    (tunnellingMatrix (d := d) w).charpoly = Matrix.det
      ((Polynomial.X ^ 2 : Polynomial ℝ) • (1 : Matrix (Fin d) (Fin d) (Polynomial ℝ)) -
        ((lowerBidiagonal (d := d) w).transpose * lowerBidiagonal w).map Polynomial.C) := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine (Set.infinite_univ.sdiff (Set.finite_singleton (0 : ℝ))).mono ?_
  intro v hv
  have hv0 : v ≠ 0 := hv.2
  have hp := eval_pencil ((lowerBidiagonal (d := d) w).transpose * lowerBidiagonal w)
    (Polynomial.X ^ 2) (-1) v
  simp only [neg_smul, one_smul, ← sub_eq_add_neg, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_neg, Polynomial.eval_one] at hp
  change (tunnellingMatrix w).charpoly.eval v = _
  rw [Matrix.eval_charpoly, hp]
  have hs : Matrix.scalar (Fin d ⊕ Fin d) v = v • 1 := by
    ext i j
    simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]
  rw [hs]
  exact block_characteristic_nonzero (lowerBidiagonal w) v hv0

private theorem tunnelling_partition_characteristic {d : Nat} (hd : 1 ≤ d)
    (w : Fin (2*d-1) → ℝ) (hw : ∀ i, 0 ≤ w i) (v : ℝ) (hv : v ≠ 0) :
    (tunnellingMatrix (d := d) w).charpoly.eval v =
      v ^ (2*d) * (forbiddenPartition w).eval (-(v^2)⁻¹) := by
  rw [tunnelling_characteristic]
  have hp := eval_pencil ((lowerBidiagonal (d := d) w).transpose * lowerBidiagonal w)
    (Polynomial.X ^ 2) (-1) v
  simp only [neg_smul, one_smul, ← sub_eq_add_neg, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_neg, Polynomial.eval_one] at hp
  rw [hp, forbidden_partition_eq_gram_determinant hd w hw]
  have hq := eval_pencil ((lowerBidiagonal (d := d) w).transpose * lowerBidiagonal w)
    1 Polynomial.X (-(v^2)⁻¹)
  simp only [one_smul, Polynomial.eval_one, Polynomial.eval_X] at hq
  rw [hq]
  have hm : v^2 • (1 : Matrix (Fin d) (Fin d) ℝ) -
      (lowerBidiagonal w).transpose * lowerBidiagonal w =
      v^2 • (1 + -(v^2)⁻¹ • ((lowerBidiagonal w).transpose * lowerBidiagonal w)) := by
    simp [smul_add, smul_smul, hv, sub_eq_add_neg]
  rw [hm, Matrix.det_smul]
  simp [pow_mul]

private theorem legal_reverse {n : Nat} (b : Fin n → Bool) :
    legalConfiguration (b ∘ Fin.rev) ↔ legalConfiguration b := by
  constructor
  · intro h i j hij
    have hx := h j.rev i.rev (by simp only [Fin.val_rev]; omega)
    simpa [Function.comp_def, Or.comm] using hx
  · intro h i j hij
    have hx := h j.rev i.rev (by simp only [Fin.val_rev]; omega)
    simpa [Function.comp_def, Or.comm] using hx

private theorem config_reverse {R : Type*} [CommSemiring R] {n : Nat} (w : Fin n → R) :
    configPartition (w ∘ Fin.rev) = configPartition w := by
  unfold configPartition
  conv_rhs => rw [← Equiv.sum_comp (Fin.revPerm.arrowCongr (Equiv.refl Bool))]
  apply Finset.sum_congr rfl
  intro b _
  change (if legalConfiguration b then ∏ i, w i.rev ^ (b i).toNat else 0) =
    (if legalConfiguration (b ∘ Fin.rev) then ∏ i, w i ^ (b i.rev).toNat else 0)
  simp only [legal_reverse]
  congr 1
  rw [← Equiv.prod_comp Fin.revPerm (fun i => w i ^ (b i.rev).toNat)]
  simp

private theorem forbidden_partition_end_recurrence {n : Nat} (w : Fin (n+2) → ℝ) :
    forbiddenPartition w = forbiddenPartition (fun i => w i.castSucc) +
      Polynomial.X * Polynomial.C (w (Fin.last (n+1))) *
        forbiddenPartition (fun i => w i.castSucc.castSucc) := by
  simp only [forbidden_partition_as_config]
  rw [← config_reverse (fun i => Polynomial.X * Polynomial.C (w i)),
    config_partition_recurrence]
  have htail : (fun i : Fin (n+1) =>
      (fun i => Polynomial.X * Polynomial.C (w i)) ((i.succ).rev)) =
      (fun i => Polynomial.X * Polynomial.C (w i.castSucc)) ∘ Fin.rev := by
    funext i
    simp [Fin.rev_succ]
  have htail2 : (fun i : Fin n =>
      (fun i => Polynomial.X * Polynomial.C (w i)) ((i.succ.succ).rev)) =
      (fun i => Polynomial.X * Polynomial.C (w i.castSucc.castSucc)) ∘ Fin.rev := by
    funext i
    simp [Fin.rev_succ]
  change configPartition (fun i : Fin (n+1) => Polynomial.X * Polynomial.C (w i.succ.rev)) +
      (Polynomial.X * Polynomial.C (w (0 : Fin (n+2)).rev)) *
        configPartition (fun i : Fin n => Polynomial.X * Polynomial.C (w i.succ.succ.rev)) = _
  rw [htail, htail2, config_reverse, config_reverse]
  simp

/-- Weighted forbidden-neighbour determinant realization, roots, and normalized quantum readout.
The reciprocal characteristic formula is evaluated away from zero; the preceding polynomial
identity supplies its denominator-cleared continuation at zero. No RH hypothesis is used. -/
theorem forbidden_neighbour_determinant {d : Nat} (hd : 1 ≤ d)
    (w : Fin (2*d-1) → ℝ) (hw : ∀ i, 0 ≤ w i) :
    forbiddenPartition w = Matrix.det ((1 : Matrix (Fin d) (Fin d) (Polynomial ℝ)) +
      (Polynomial.X : Polynomial ℝ) •
        ((lowerBidiagonal (d := d) w).transpose * lowerBidiagonal w).map Polynomial.C) ∧
    ((lowerBidiagonal (d := d) w).transpose * lowerBidiagonal w).PosSemidef ∧
    (∀ i, 0 ≤ gramEigenvalue (d := d) w i) ∧
    forbiddenPartition w = ∏ i ∈ Finset.univ.filter (fun i : Fin d => gramEigenvalue w i ≠ 0),
      (1 + Polynomial.C (gramEigenvalue w i) * Polynomial.X) ∧
    (∀ z : ℂ, (forbiddenPartition w).eval₂ Complex.ofRealHom z = 0 →
      ∃ t : ℝ, t < 0 ∧ z = Complex.ofReal t ∧
        ∃ i : Fin d, 0 < gramEigenvalue w i ∧ t = -(gramEigenvalue w i)⁻¹) ∧
    (tunnellingMatrix (d := d) w).charpoly = Matrix.det
      ((Polynomial.X ^ 2 : Polynomial ℝ) • (1 : Matrix (Fin d) (Fin d) (Polynomial ℝ)) -
        ((lowerBidiagonal (d := d) w).transpose * lowerBidiagonal w).map Polynomial.C) ∧
    (∀ v : ℝ, v ≠ 0 → (tunnellingMatrix (d := d) w).charpoly.eval v =
      v ^ (2*d) * (forbiddenPartition w).eval (-(v^2)⁻¹)) ∧
    (∀ (n : Nat) (u : Fin (n+2) → ℝ),
      forbiddenPartition u = forbiddenPartition (fun i => u i.castSucc) +
        Polynomial.X * Polynomial.C (u (Fin.last (n+1))) *
          forbiddenPartition (fun i => u i.castSucc.castSucc)) ∧
    (∀ r : ℝ, quantumState w r =
      (Complex.ofReal (Real.sqrt ((forbiddenPartition w).eval r)))⁻¹ •
        ∑ b : {b : Fin (2*d-1) → Bool // legalConfiguration b},
          Complex.ofReal (r ^ ((occupationCount b.val : ℝ) / 2) *
            ∏ i, w i ^ (((b.val i).toNat : ℝ) / 2)) • Pi.single b (1 : ℂ)) ∧
    (∀ r : ℝ, 0 < r → dotProduct (star (quantumState w r)) (quantumState w r) = 1) ∧
    (∀ b : {b : Fin (2*d-1) → Bool // legalConfiguration b},
      numberOperator (2*d-1) *ᵥ Pi.single b (1 : ℂ) =
        (occupationCount b.val : ℂ) • Pi.single b (1 : ℂ)) ∧
    (∀ (r theta : ℝ), 0 < r → dotProduct (star (quantumState w r))
      ((NormedSpace.exp (((theta : ℂ) * Complex.I) • numberOperator (2*d-1))) *ᵥ
        quantumState w r) = (forbiddenPartition w).eval₂ Complex.ofRealHom
          ((r : ℂ) * Complex.exp ((theta : ℂ) * Complex.I)) /
            Complex.ofReal ((forbiddenPartition w).eval r)) ∧
    (∀ (P : Polynomial ℝ) (r theta : ℝ), forbiddenPartition w = P → 0 < r →
      dotProduct (star (quantumState w r))
        ((NormedSpace.exp (((theta : ℂ) * Complex.I) • numberOperator (2*d-1))) *ᵥ
          quantumState w r) = P.eval₂ Complex.ofRealHom
            ((r : ℂ) * Complex.exp ((theta : ℂ) * Complex.I)) / Complex.ofReal (P.eval r)) ∧
    (Fintype.card {b : Fin (2*d-1) → Bool // legalConfiguration b} = Nat.fib (2*d+1) ∧
      Fintype.card (Fin d ⊕ Fin d) = 2*d) := by
  refine ⟨forbidden_partition_eq_gram_determinant hd w hw, gramPosSemidef w,
    (gramPosSemidef w).eigenvalues_nonneg, ?_, forbidden_partition_roots_negative hd w hw,
    tunnelling_characteristic w, tunnelling_partition_characteristic hd w hw,
    fun _ u => forbidden_partition_end_recurrence u, quantum_state_basis_sum w,
    quantum_state_normalized w hw,
    ?_, fun r theta hr => quantum_partition_readout w hw r hr theta,
    ?_, configuration_dimension hd, by simp; omega⟩
  · rw [forbidden_partition_factorization hd w hw]
    symm
    apply Finset.prod_subset (Finset.filter_subset _ _)
    intro i _ hi
    have hz : gramEigenvalue (d := d) w i = 0 := by simpa using hi
    simp [hz]
  · intro b
    ext a
    by_cases h : a=b <;> simp [numberOperator, Matrix.mulVec_diagonal, h]
  · intro P r theta hP hr
    rw [← hP]
    exact quantum_partition_readout w hw r hr theta

#print axioms gramPosSemidef
#print axioms forbidden_neighbour_determinant

end D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant
