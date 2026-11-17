/- GID: D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Four correlated half entries have a trace norm fixed by their coordinate kernels. -/

import D5.S3.QuantumBounds.SicMubCorrelationTraceNormEquality
import D5.S3.Quantum.Schatten.TraceNorm
import D5.S3.Quantum.Foundation.FiniteTraceDistance

noncomputable section

namespace D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance

open _root_.Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteTraceDistance

variable {a b m n : Type*} [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b] [Fintype m] [DecidableEq m]
  [Fintype n] [DecidableEq n]

/-- Independent left and right isometric embeddings preserve the rectangular trace norm. -/
theorem traceNorm_two_isometries (A : Matrix m n ℂ)
    (V : Matrix a m ℂ) (W : Matrix b n ℂ)
    (hV : Vᴴ * V = 1) (hW : Wᴴ * W = 1) :
    traceNorm (V * A * Wᴴ) = traceNorm A := by
  simpa using
    D5.S3.QuantumBounds.SicMubCorrelationTraceNormEquality.scaled_isometry_traceNorm
      V W A 1 1 (by norm_num) (by norm_num) (by simpa using hV) (by simpa using hW)

/-- The coordinate inclusion associated with an injection, with zero entries elsewhere. -/
def coordinateEmbedding (e : m ↪ a) : Matrix a m ℂ :=
  fun i j => if i = e j then 1 else 0

/-- Distinct included coordinates form an orthonormal family. -/
theorem coordinateEmbedding_isometry (e : m ↪ a) :
    (coordinateEmbedding e)ᴴ * coordinateEmbedding e = 1 := by
  ext i j
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, coordinateEmbedding,
    Matrix.one_apply, e.injective.eq_iff, eq_comm]

/-- Independent bijective changes of row and column coordinates preserve the trace norm. -/
theorem traceNorm_submatrix_equiv (A : Matrix m n ℂ) (e : a ≃ m) (f : b ≃ n) :
    traceNorm (A.submatrix e f) = traceNorm A := by
  have h := traceNorm_two_isometries A
    (coordinateEmbedding e.symm.toEmbedding) (coordinateEmbedding f.symm.toEmbedding)
    (coordinateEmbedding_isometry _) (coordinateEmbedding_isometry _)
  have he : coordinateEmbedding e.symm.toEmbedding * A *
      (coordinateEmbedding f.symm.toEmbedding)ᴴ = A.submatrix e f := by
    ext i j
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, coordinateEmbedding,
      e.eq_symm_apply, f.eq_symm_apply]
  rwa [he] at h

/-- Plain transpose preserves the trace norm on every finite square index set. -/
theorem traceNorm_transpose (A : Matrix n n ℂ) : traceNorm Aᵀ = traceNorm A := by
  let e := Fintype.equivFin n
  have h := (D5.S3.Quantum.Schatten.TraceNorm.traceNormUINorm (Fintype.card n)).N_transpose
    ((Matrix.reindexAlgEquiv ℂ ℂ e) A)
  change traceNorm ((Aᵀ).submatrix e.symm e.symm) =
    traceNorm (A.submatrix e.symm e.symm) at h
  simpa only [traceNorm_submatrix_equiv] using h

/-- Taking the adjoint preserves the trace norm on every finite square index set. -/
theorem traceNorm_conjTranspose (A : Matrix n n ℂ) : traceNorm Aᴴ = traceNorm A := by
  let e := Fintype.equivFin n
  have h := (D5.S3.Quantum.Schatten.TraceNorm.traceNormUINorm (Fintype.card n)).N_conjTranspose
    ((Matrix.reindexAlgEquiv ℂ ℂ e) A)
  change traceNorm ((Aᴴ).submatrix e.symm e.symm) =
    traceNorm (A.submatrix e.symm e.symm) at h
  simpa only [traceNorm_submatrix_equiv] using h

/-- The adjoint preserves the trace norm of rectangular complex matrices as well. -/
theorem traceNorm_conjTranspose_rect (A : Matrix m n ℂ) : traceNorm Aᴴ = traceNorm A := by
  let V : Matrix (m ⊕ n) m ℂ := coordinateEmbedding Function.Embedding.inl
  let W : Matrix (m ⊕ n) n ℂ := coordinateEmbedding Function.Embedding.inr
  have hV : Vᴴ * V = 1 := coordinateEmbedding_isometry _
  have hW : Wᴴ * W = 1 := coordinateEmbedding_isometry _
  have h := traceNorm_conjTranspose (V * A * Wᴴ)
  have he : (V * A * Wᴴ)ᴴ = W * Aᴴ * Vᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [he, traceNorm_two_isometries Aᴴ W V hW hV,
    traceNorm_two_isometries A V W hV hW] at h
  exact h

end D5.S3.Quantum.Entanglement.PermutationCriteria.NormInvariance

noncomputable section
open _root_.Matrix Finset
open scoped ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Entanglement.PermutationCriteria
open D5.S3.Quantum.Foundation.FiniteTraceDistance

/-- A constant singular value gives its exact trace-norm contribution. -/
theorem traceNorm_of_scalar_gram {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (A : Matrix m n ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hA : Aᴴ * A = (c : ℂ) • ((c : ℂ) • (1 : Matrix n n ℂ))) :
    traceNorm A = c * Fintype.card n := by
  have hp : ((c : ℂ) • (1 : Matrix n n ℂ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr hc)
  have hs : ((c : ℂ) • (1 : Matrix n n ℂ)) *
      ((c : ℂ) • (1 : Matrix n n ℂ)) = Aᴴ * A := by
    rw [hA, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul]
  unfold D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm
  rw [CFC.sqrt_unique hs hp.nonneg, Matrix.trace_smul, Matrix.trace_one]
  simp

/-- The two nonzero entries produced by a one-party mixed state on one side. -/
def mixedColumn : Matrix (Fin 2) (Fin 1) ℂ := fun _ _ => 1 / 2

/-- Two half entries in a column have trace norm sqrt(1/2). -/
theorem traceNorm_mixedColumn : traceNorm mixedColumn = Real.sqrt (1 / 2) := by
  have hs : (Real.sqrt (1 / 2 : ℝ) : ℂ) * (Real.sqrt (1 / 2 : ℝ) : ℂ) = 1 / 2 := by
    rw [← Complex.ofReal_mul, ← pow_two, Real.sq_sqrt (by norm_num)]
    norm_num
  norm_num at hs
  have h := traceNorm_of_scalar_gram mixedColumn (Real.sqrt (1 / 2))
    (Real.sqrt_nonneg _) (by
      ext i j
      fin_cases i
      fin_cases j
      norm_num [mixedColumn, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul, map_div₀, map_ofNat, map_one, hs])
  simpa using h

/-- A scalar half identity is the split one-party block and the doubly crossed Bell block. -/
def halfIdentity (n : ℕ) : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • 1

/-- Each scalar half identity contributes one half per retained coordinate. -/
theorem traceNorm_halfIdentity (n : ℕ) : traceNorm (halfIdentity n) = n / 2 := by
  have hp : (halfIdentity n).PosSemidef :=
    Matrix.PosSemidef.one.smul (show (0 : ℂ) ≤ 1 / 2 by norm_num [Complex.le_def])
  have h := congrArg Complex.re (traceNorm_of_posSemidef hp)
  simpa [halfIdentity, Matrix.trace_smul, Matrix.trace_one, div_eq_mul_inv, mul_comm] using h

/-- All four Bell entries on a single side. -/
def bellColumn : Matrix (Fin 4) (Fin 1) ℂ := fun _ _ => 1 / 2

/-- Four half entries in one column have trace norm one. -/
theorem traceNorm_bellColumn : traceNorm bellColumn = 1 := by
  have h := traceNorm_of_scalar_gram bellColumn 1 (by norm_num) (by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [bellColumn, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Matrix.smul_apply, smul_eq_mul])
  simpa using h

/-- The Bell block with one crossed and one uncrossed equality. -/
def bellOneCross : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ :=
  fun p q => if p.1 = q then 1 / 2 else 0

/-- The singly crossed Bell block has two singular values sqrt(1/2). -/
theorem traceNorm_bellOneCross : traceNorm bellOneCross = 2 * Real.sqrt (1 / 2) := by
  have hs : (Real.sqrt (1 / 2 : ℝ) : ℂ) * (Real.sqrt (1 / 2 : ℝ) : ℂ) = 1 / 2 := by
    rw [← Complex.ofReal_mul, ← pow_two, Real.sq_sqrt (by norm_num)]
    norm_num
  norm_num at hs
  have h := traceNorm_of_scalar_gram bellOneCross (Real.sqrt (1 / 2))
    (Real.sqrt_nonneg _) (by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [bellOneCross, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul, map_div₀, map_ofNat, map_one, hs])
  simpa [mul_comm] using h

/-- One uncrossed Bell equality on each side produces this constant square. -/
def bellSquare : Matrix (Fin 2) (Fin 2) ℂ := fun _ _ => 1 / 2

/-- The constant Bell square is positive semidefinite and has trace norm one. -/
theorem traceNorm_bellSquare : traceNorm bellSquare = 1 := by
  have he : bellSquare = (1 / 2 : ℂ) •
      Matrix.vecMulVec (fun _ : Fin 2 => (1 : ℂ)) (star (fun _ : Fin 2 => (1 : ℂ))) := by
    ext i j
    simp [bellSquare, Matrix.vecMulVec_apply]
  have hp : bellSquare.PosSemidef := by
    rw [he]
    exact (Matrix.posSemidef_vecMulVec_self_star _).smul
      (show (0 : ℂ) ≤ 1 / 2 by norm_num [Complex.le_def])
  have h := congrArg Complex.re (traceNorm_of_posSemidef hp)
  simpa [bellSquare, Matrix.trace, Fin.sum_univ_two] using h

end D5.S3.Quantum.Entanglement.PermutationCriteria

noncomputable section

namespace D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks

open _root_.Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open NormInvariance
open D5.S3.Quantum.Foundation.FiniteTraceDistance

private abbrev Active : Bool → Bool → Type
  | false, false => Fin 1
  | false, true => Fin 2
  | true, false => Fin 2
  | true, true => Fin 2 × Fin 2

private instance (a b : Bool) : Fintype (Active a b) := by
  cases a <;> cases b <;> dsimp [Active] <;> infer_instance

private instance (a b : Bool) : DecidableEq (Active a b) := by
  cases a <;> cases b <;> dsimp [Active] <;> infer_instance

private def project : (a b : Bool) → (Fin 2 × Fin 2) → Active a b
  | false, false => fun _ => 0
  | false, true => Prod.snd
  | true, false => Prod.fst
  | true, true => id

private def restoreCoords : (a b : Bool) → Active a b → (Fin 2 × Fin 2)
  | false, false => fun _ => (0, 0)
  | false, true => fun t => (0, t)
  | true, false => fun t => (t, 0)
  | true, true => id

private theorem project_include (a b : Bool) (x : Active a b) :
    project a b (restoreCoords a b x) = x := by
  cases a <;> cases b
  · exact Subsingleton.elim _ _
  · rfl
  · rfl
  · rfl

private theorem project_eq (a b : Bool) (x y : Fin 2 × Fin 2) :
    project a b x = project a b y ↔
      (a = true → x.1 = y.1) ∧ (b = true → x.2 = y.2) := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  cases a <;> cases b <;> simp [project]

private theorem kernel_embedding {m : Type} (R : Fin 2 × Fin 2 → m) (a b : Bool)
    (hR : ∀ x y, R x = R y ↔
      (a = true → x.1 = y.1) ∧ (b = true → x.2 = y.2)) :
    ∃ e : Active a b ↪ m, ∀ x, e (project a b x) = R x := by
  let e : Active a b ↪ m := ⟨fun x => R (restoreCoords a b x), by
    intro x y h
    have hh := (project_eq a b (restoreCoords a b x) (restoreCoords a b y)).mpr ((hR _ _).mp h)
    simpa only [project_include] using hh⟩
  refine ⟨e, fun x => ?_⟩
  apply (hR _ _).mpr
  exact (project_eq a b _ _).mp (project_include a b (project a b x))

/-- Independent coordinate inclusions send one matrix unit to its included matrix unit. -/
theorem embedded_single {a b m n : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (e : m ↪ a) (f : n ↪ b)
    (i : m) (j : n) (c : ℂ) :
    coordinateEmbedding e * Matrix.single i j c * (coordinateEmbedding f)ᴴ =
      Matrix.single (e i) (f j) c := by
  ext x y
  have hleft : ∀ k, (coordinateEmbedding e * Matrix.single i j c) x k =
      if k = j then coordinateEmbedding e x i * c else 0 := by
    intro k
    by_cases hk : k = j
    · subst k
      simp
    · have hjk := Ne.symm hk
      simp [Matrix.mul_apply, Matrix.single_apply, hk, hjk]
  rw [Matrix.mul_apply]
  simp only [hleft, Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single j]
  · by_cases hx : x = e i <;> by_cases hy : y = f j <;>
      simp [coordinateEmbedding, Matrix.single_apply, hx, hy, eq_comm]
  · intro k _ hk
    simp [hk]
  · simp

/-- A matrix consisting of the four correlated half entries. -/
def fourEntries {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (R : Fin 2 × Fin 2 → m) (C : Fin 2 × Fin 2 → n) : Matrix m n ℂ :=
  ∑ x : Fin 2 × Fin 2, Matrix.single (R x) (C x) (1 / 2)

private theorem embedded_fourEntries {a b m n : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (e : m ↪ a) (f : n ↪ b)
    (R : Fin 2 × Fin 2 → m) (C : Fin 2 × Fin 2 → n) :
    coordinateEmbedding e * fourEntries R C * (coordinateEmbedding f)ᴴ =
      fourEntries (fun x => e (R x)) (fun x => f (C x)) := by
  simp only [fourEntries, Matrix.mul_sum, Matrix.sum_mul, embedded_single]

/-- The three possible Bell trace norms indexed by the number of shared bits. -/
def bellValue : ℕ → ℝ
  | 0 => 1
  | 1 => 2 * Real.sqrt (1 / 2)
  | _ => 2

private theorem canonical_norm (rk rb ck cb : Bool)
    (hK : rk = true ∨ ck = true) (hB : rb = true ∨ cb = true) :
    traceNorm (fourEntries (project rk rb) (project ck cb)) =
      bellValue ((if rk && ck then 1 else 0) + (if rb && cb then 1 else 0)) := by
  cases rk <;> cases rb <;> cases ck <;> cases cb <;>
    simp only [Bool.false_eq_true, eq_self_iff_true, false_or, or_false, true_or, or_true] at hK hB
  all_goals try contradiction
  · change traceNorm (fourEntries (project false false) (project true true)) = 1
    have he : fourEntries (project false false) (project true true) =
        (bellColumn.submatrix finProdFinEquiv (Equiv.refl (Fin 1)))ᴴ := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [fourEntries, project, bellColumn, Matrix.conjTranspose_apply,
          Matrix.submatrix_apply, Matrix.sum_apply, Matrix.add_apply, Matrix.single_apply,
          Fintype.sum_prod_type, Fin.sum_univ_two]
    rw [he, traceNorm_conjTranspose_rect, traceNorm_submatrix_equiv, traceNorm_bellColumn]
  · change traceNorm (fourEntries (project false true) (project true false)) = 1
    have he : fourEntries (project false true) (project true false) = bellSquare := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [fourEntries, project, bellSquare, Matrix.sum_apply, Matrix.add_apply,
          Matrix.single_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
    rw [he, traceNorm_bellSquare]
  · change traceNorm (fourEntries (project false true) (project true true)) =
      2 * Real.sqrt (1 / 2)
    have he : fourEntries (project false true) (project true true) =
        (bellOneCross.submatrix (Equiv.prodComm (Fin 2) (Fin 2)) (Equiv.refl (Fin 2)))ᴴ := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [fourEntries, project, bellOneCross, Matrix.conjTranspose_apply,
          Matrix.submatrix_apply, Matrix.sum_apply, Matrix.add_apply, Matrix.single_apply,
          Fintype.sum_prod_type, Fin.sum_univ_two]
    rw [he, traceNorm_conjTranspose_rect, traceNorm_submatrix_equiv, traceNorm_bellOneCross]
  · change traceNorm (fourEntries (project true false) (project false true)) = 1
    have he : fourEntries (project true false) (project false true) = bellSquare := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [fourEntries, project, bellSquare, Matrix.sum_apply, Matrix.add_apply,
          Matrix.single_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
    rw [he, traceNorm_bellSquare]
  · change traceNorm (fourEntries (project true false) (project true true)) =
      2 * Real.sqrt (1 / 2)
    have he : fourEntries (project true false) (project true true) = bellOneCrossᴴ := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [fourEntries, project, bellOneCross, Matrix.conjTranspose_apply,
          Matrix.sum_apply, Matrix.add_apply, Matrix.single_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
    rw [he, traceNorm_conjTranspose_rect, traceNorm_bellOneCross]
  · change traceNorm (fourEntries (project true true) (project false false)) = 1
    have he : fourEntries (project true true) (project false false) =
        bellColumn.submatrix finProdFinEquiv (Equiv.refl (Fin 1)) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [fourEntries, project, bellColumn, Matrix.submatrix_apply,
          Matrix.sum_apply, Matrix.add_apply, Matrix.single_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
    rw [he, traceNorm_submatrix_equiv, traceNorm_bellColumn]
  · change traceNorm (fourEntries (project true true) (project false true)) =
      2 * Real.sqrt (1 / 2)
    have he : fourEntries (project true true) (project false true) =
        bellOneCross.submatrix (Equiv.prodComm (Fin 2) (Fin 2)) (Equiv.refl (Fin 2)) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [fourEntries, project, bellOneCross, Matrix.submatrix_apply,
          Matrix.sum_apply, Matrix.add_apply, Matrix.single_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
    rw [he, traceNorm_submatrix_equiv, traceNorm_bellOneCross]
  · change traceNorm (fourEntries (project true true) (project true false)) =
      2 * Real.sqrt (1 / 2)
    have he : fourEntries (project true true) (project true false) = bellOneCross := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [fourEntries, project, bellOneCross, Matrix.sum_apply, Matrix.add_apply,
          Matrix.single_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
    rw [he, traceNorm_bellOneCross]
  · change traceNorm (fourEntries (project true true) (project true true)) = 2
    have he : fourEntries (project true true) (project true true) =
        (halfIdentity 4).submatrix finProdFinEquiv finProdFinEquiv := by
      ext i j
      simp only [halfIdentity, Matrix.submatrix_apply, Matrix.smul_apply,
        smul_eq_mul, Matrix.one_apply, finProdFinEquiv.injective.eq_iff]
      fin_cases i <;> fin_cases j <;>
        norm_num [fourEntries, project, Matrix.sum_apply, Matrix.add_apply, Matrix.single_apply,
          Fintype.sum_prod_type, Fin.sum_univ_two]
    rw [he, traceNorm_submatrix_equiv, traceNorm_halfIdentity]
    norm_num

/-- Coordinate kernels alone determine the trace norm of the four correlated entries. -/
theorem traceNorm_fourEntries {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (R : Fin 2 × Fin 2 → m) (C : Fin 2 × Fin 2 → n)
    (rk rb ck cb : Bool) (hK : rk = true ∨ ck = true) (hB : rb = true ∨ cb = true)
    (hR : ∀ x y, R x = R y ↔
      (rk = true → x.1 = y.1) ∧ (rb = true → x.2 = y.2))
    (hC : ∀ x y, C x = C y ↔
      (ck = true → x.1 = y.1) ∧ (cb = true → x.2 = y.2)) :
    traceNorm (fourEntries R C) =
      bellValue ((if rk && ck then 1 else 0) + (if rb && cb then 1 else 0)) := by
  obtain ⟨e, he⟩ := kernel_embedding R rk rb hR
  obtain ⟨f, hf⟩ := kernel_embedding C ck cb hC
  have hmatrix : fourEntries R C =
      coordinateEmbedding e * fourEntries (project rk rb) (project ck cb) *
        (coordinateEmbedding f)ᴴ := by
    rw [embedded_fourEntries]
    congr 1
    · funext x; exact (he x).symm
    · funext x; exact (hf x).symm
  rw [hmatrix, traceNorm_two_isometries _ _ _
    (coordinateEmbedding_isometry _) (coordinateEmbedding_isometry _)]
  exact canonical_norm rk rb ck cb hK hB

#print axioms traceNorm_fourEntries

/-- The three Bell trace norms distinguish every shared-coordinate count up to two. -/
theorem bellValue_injective {a b : ℕ} (ha : a ≤ 2) (hb : b ≤ 2)
    (h : bellValue a = bellValue b) : a = b := by
  have hs := Real.sqrt_nonneg (1 / 2 : ℝ)
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have hlow : 1 < 2 * Real.sqrt (1 / 2 : ℝ) := by nlinarith
  have hhigh : 2 * Real.sqrt (1 / 2 : ℝ) < 2 := by nlinarith
  interval_cases a <;> interval_cases b <;> norm_num [bellValue] at * <;> linarith

#print axioms bellValue_injective

end D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks
