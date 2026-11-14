/- GID: D5/S3/Quantum/Entanglement/PermutationCriteria/Witnesses
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/PermutationCriteria/Witnesses
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Positive trace-one single-party and Bell witnesses for permutation criteria. -/

import D5.S3.Quantum.Entanglement.PermutationCriteria.RowSetRecovery
import D5.S3.Quantum.Entanglement.PermutationCriteria.BellBlocks

noncomputable section

namespace D5.S3.Quantum.Entanglement.PermutationCriteria

open _root_.Matrix Finset
open scoped ComplexOrder MatrixOrder Classical
open NormInvariance

/-- A computational basis string with the same bit on a specified set of parties. -/
def bitPattern {r d : ℕ} (hd : 2 ≤ d) (S : Finset (Fin r)) (t : Fin 2) : Index r d :=
  fun k => if k ∈ S then ⟨t.val, lt_of_lt_of_le t.isLt hd⟩ else ⟨0, by omega⟩

private theorem bitPattern_injective {r d : ℕ} (hd : 2 ≤ d)
    (S : Finset (Fin r)) (hS : S.Nonempty) : Function.Injective (bitPattern hd S) := by
  intro t u h
  obtain ⟨i, hi⟩ := hS
  have he := congrArg (fun v : Index r d => (v i).val) h
  apply Fin.ext
  simpa [bitPattern, hi] using he

/-- Include the two correlated computational basis strings and fill all other entries with zero. -/
def witnessEmbedding {r d : ℕ} (hd : 2 ≤ d) (S : Finset (Fin r))
    (hS : S.Nonempty) : Matrix (Index r d) (Fin 2) ℂ :=
  coordinateEmbedding ⟨bitPattern hd S, bitPattern_injective hd S hS⟩

private theorem witnessEmbedding_isometry {r d : ℕ} (hd : 2 ≤ d)
    (S : Finset (Fin r)) (hS : S.Nonempty) :
    (witnessEmbedding hd S hS)ᴴ * witnessEmbedding hd S hS = 1 :=
  coordinateEmbedding_isometry _

/-- The one-party maximally mixed qubit with every remaining party fixed to zero. -/
def singleWitness {r d : ℕ} (hd : 2 ≤ d) (i : Fin r) :
    Matrix (Index r d) (Index r d) ℂ :=
  let V := witnessEmbedding hd {i} (singleton_nonempty i)
  V * halfIdentity 2 * Vᴴ

private theorem density_embedded {n : Type*} [Fintype n] [DecidableEq n]
    (V : Matrix n (Fin 2) ℂ) (hV : Vᴴ * V = 1)
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : IsDensity A) :
    IsDensity (V * A * Vᴴ) := by
  refine ⟨hA.1.mul_mul_conjTranspose_same V, ?_⟩
  rw [Matrix.trace_mul_cycle, hV, Matrix.one_mul]
  exact hA.2

/-- The single-party mixed witness is a density matrix for every party and local dimension at least two. -/
theorem singleWitness_isDensity {r d : ℕ} (hd : 2 ≤ d) (i : Fin r) :
    IsDensity (singleWitness hd i) := by
  apply density_embedded _ (witnessEmbedding_isometry hd _ _) (halfIdentity 2)
  constructor
  · exact Matrix.PosSemidef.one.smul (show (0 : ℂ) ≤ 1 / 2 by norm_num [Complex.le_def])
  · norm_num [halfIdentity, Matrix.trace_smul, Matrix.trace_one]

/-- The Bell state on two parties, with every remaining party fixed to zero. -/
def bellWitness {r d : ℕ} (hd : 2 ≤ d) (i j : Fin r) :
    Matrix (Index r d) (Index r d) ℂ :=
  let V := witnessEmbedding hd {i, j} (by simp)
  V * bellSquare * Vᴴ

/-- The Bell witness is a positive trace-one operator. -/
theorem bellWitness_isDensity {r d : ℕ} (hd : 2 ≤ d) (i j : Fin r) :
    IsDensity (bellWitness hd i j) := by
  apply density_embedded _ (witnessEmbedding_isometry hd _ _) bellSquare
  constructor
  · have he : bellSquare = (1 / 2 : ℂ) •
        Matrix.vecMulVec (fun _ : Fin 2 => (1 : ℂ))
          (star (fun _ : Fin 2 => (1 : ℂ))) := by
      ext a b
      simp [bellSquare, Matrix.vecMulVec_apply]
    rw [he]
    exact (Matrix.posSemidef_vecMulVec_self_star _).smul
      (show (0 : ℂ) ≤ 1 / 2 by norm_num [Complex.le_def])
  · norm_num [bellSquare, Matrix.trace, Fin.sum_univ_two]

/-- The mixed witness has exactly two diagonal half entries. -/
theorem singleWitness_eq {r d : ℕ} (hd : 2 ≤ d) (i : Fin r) :
    singleWitness hd i =
      Matrix.single (bitPattern hd {i} 0) (bitPattern hd {i} 0) (1 / 2) +
      Matrix.single (bitPattern hd {i} 1) (bitPattern hd {i} 1) (1 / 2) := by
  let e : Fin 2 ↪ Index r d :=
    ⟨bitPattern hd {i}, bitPattern_injective hd {i} (singleton_nonempty i)⟩
  have hb : halfIdentity 2 = Matrix.single 0 0 (1 / 2 : ℂ) + Matrix.single 1 1 (1 / 2) := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [halfIdentity, Matrix.single_apply, Matrix.one_apply]
  change coordinateEmbedding e * halfIdentity 2 * (coordinateEmbedding e)ᴴ = _
  rw [hb]
  simp only [Matrix.mul_add, Matrix.add_mul, BellBlocks.embedded_single]
  rfl

/-- The Bell witness has four half entries on its two correlated basis strings. -/
theorem bellWitness_eq {r d : ℕ} (hd : 2 ≤ d) (i j : Fin r) :
    bellWitness hd i j =
      Matrix.single (bitPattern hd {i, j} 0) (bitPattern hd {i, j} 0) (1 / 2) +
      Matrix.single (bitPattern hd {i, j} 0) (bitPattern hd {i, j} 1) (1 / 2) +
      Matrix.single (bitPattern hd {i, j} 1) (bitPattern hd {i, j} 0) (1 / 2) +
      Matrix.single (bitPattern hd {i, j} 1) (bitPattern hd {i, j} 1) (1 / 2) := by
  let e : Fin 2 ↪ Index r d :=
    ⟨bitPattern hd {i, j}, bitPattern_injective hd {i, j} (by simp)⟩
  have hb : bellSquare =
      Matrix.single 0 0 (1 / 2 : ℂ) + Matrix.single 0 1 (1 / 2) +
      Matrix.single 1 0 (1 / 2) + Matrix.single 1 1 (1 / 2) := by
    ext a b
    fin_cases a <;> fin_cases b <;> norm_num [bellSquare, Matrix.single_apply]
  change coordinateEmbedding e * bellSquare * (coordinateEmbedding e)ᴴ = _
  rw [hb]
  simp only [Matrix.mul_add, Matrix.add_mul, BellBlocks.embedded_single]
  rfl

private def twoPointEmbedding {n : Type*} (u v : n) (h : u ≠ v) : Fin 2 ↪ n :=
  ⟨![u, v], by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all⟩

private def onePointEmbedding {n : Type*} (u : n) : Fin 1 ↪ n :=
  ⟨fun _ => u, fun _ _ _ => Subsingleton.elim _ _⟩

private theorem traceNorm_two_single_same_column {m n : Type*} [Fintype m]
    [DecidableEq m] [Fintype n] [DecidableEq n] (u v : m) (x : n) (huv : u ≠ v) :
    D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm
      (Matrix.single u x (1 / 2 : ℂ) + Matrix.single v x (1 / 2)) =
      Real.sqrt (1 / 2) := by
  let V := coordinateEmbedding (twoPointEmbedding u v huv)
  let W := coordinateEmbedding (onePointEmbedding x)
  have he : Matrix.single u x (1 / 2 : ℂ) + Matrix.single v x (1 / 2) =
      V * mixedColumn * Wᴴ := by
    ext i j
    simp only [V, W, coordinateEmbedding, twoPointEmbedding, onePointEmbedding,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Fin.sum_univ_one, mixedColumn, Matrix.add_apply, Matrix.single_apply,
      Function.Embedding.coeFn_mk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const]
    split_ifs <;> norm_num [RCLike.star_def] at * <;> aesop
  rw [he, traceNorm_two_isometries mixedColumn V W
    (coordinateEmbedding_isometry _) (coordinateEmbedding_isometry _), traceNorm_mixedColumn]

private theorem traceNorm_two_single_same_row {m n : Type*} [Fintype m]
    [DecidableEq m] [Fintype n] [DecidableEq n] (u : m) (x y : n) (hxy : x ≠ y) :
    D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm
      (Matrix.single u x (1 / 2 : ℂ) + Matrix.single u y (1 / 2)) =
      Real.sqrt (1 / 2) := by
  rw [← traceNorm_conjTranspose_rect
    (Matrix.single u x (1 / 2 : ℂ) + Matrix.single u y (1 / 2))]
  simpa only [Matrix.conjTranspose_add, Matrix.conjTranspose_single, star_div₀,
    star_one, star_ofNat] using traceNorm_two_single_same_column x y u hxy

private theorem traceNorm_two_single_separate {m n : Type*} [Fintype m]
    [DecidableEq m] [Fintype n] [DecidableEq n] (u v : m) (x y : n)
    (huv : u ≠ v) (hxy : x ≠ y) :
    D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm
      (Matrix.single u x (1 / 2 : ℂ) + Matrix.single v y (1 / 2)) = 1 := by
  let V := coordinateEmbedding (twoPointEmbedding u v huv)
  let W := coordinateEmbedding (twoPointEmbedding x y hxy)
  have he : Matrix.single u x (1 / 2 : ℂ) + Matrix.single v y (1 / 2) =
      V * halfIdentity 2 * Wᴴ := by
    ext i j
    simp only [V, W, coordinateEmbedding, twoPointEmbedding,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      halfIdentity, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
      Matrix.add_apply, Matrix.single_apply, Function.Embedding.coeFn_mk,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    split_ifs <;> norm_num [RCLike.star_def] at * <;> aesop
  rw [he, traceNorm_two_isometries (halfIdentity 2) V W
    (coordinateEmbedding_isometry _) (coordinateEmbedding_isometry _), traceNorm_halfIdentity]
  norm_num

private def singleImage {r d : ℕ} (hd : 2 ≤ d)
    (σ : Equiv.Perm (Fin (2 * r))) (i : Fin r) (t : Fin 2) :
    Index r d × Index r d :=
  (indexPermutation σ).symm (bitPattern hd {i} t, bitPattern hd {i} t)

private theorem party_eq_iff {r : ℕ} (p : Fin (2 * r)) (i : Fin r) :
    party p = i ↔ p = ketPos i ∨ p = braPos i := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    by_cases hp : p.val % 2 = 0
    · left; apply Fin.ext; dsimp [party, ketPos] at *; omega
    · right; apply Fin.ext; dsimp [party, braPos] at *; omega
  · rintro (rfl | rfl) <;> simp

private theorem merge_equal {r d : ℕ} (a : Index r d) (p : Fin (2 * r)) :
    merge a a p = a (party p) := by
  simp [merge]

private theorem singleRows_eq {r d : ℕ} (hd : 2 ≤ d)
    (σ : Equiv.Perm (Fin (2 * r))) (i : Fin r) :
    (singleImage hd σ i 0).1 = (singleImage hd σ i 1).1 ↔
      (σ (ketPos i)).val % 2 ≠ 0 ∧ (σ (braPos i)).val % 2 ≠ 0 := by
  constructor
  · intro h
    constructor
    · intro hk
      have hp := ketPos_party (σ (ketPos i)) hk
      have he := congrFun h (party (σ (ketPos i)))
      change merge (bitPattern hd {i} 0) (bitPattern hd {i} 0)
          (σ.symm (ketPos (party (σ (ketPos i))))) =
        merge (bitPattern hd {i} 1) (bitPattern hd {i} 1)
          (σ.symm (ketPos (party (σ (ketPos i))))) at he
      rw [hp, Equiv.symm_apply_apply] at he
      simp [merge_equal, bitPattern] at he
    · intro hk
      have hp := ketPos_party (σ (braPos i)) hk
      have he := congrFun h (party (σ (braPos i)))
      change merge (bitPattern hd {i} 0) (bitPattern hd {i} 0)
          (σ.symm (ketPos (party (σ (braPos i))))) =
        merge (bitPattern hd {i} 1) (bitPattern hd {i} 1)
          (σ.symm (ketPos (party (σ (braPos i))))) at he
      rw [hp, Equiv.symm_apply_apply] at he
      simp [merge_equal, bitPattern] at he
  · rintro ⟨hk, hb⟩
    funext k
    change merge (bitPattern hd {i} 0) (bitPattern hd {i} 0) (σ.symm (ketPos k)) =
      merge (bitPattern hd {i} 1) (bitPattern hd {i} 1) (σ.symm (ketPos k))
    rw [merge_equal, merge_equal]
    have h : party (σ.symm (ketPos k)) ≠ i := by
      intro he
      rcases (party_eq_iff _ _).mp he with he | he
      · have hs := congrArg σ he
        simp only [Equiv.apply_symm_apply] at hs
        have hc : (σ (ketPos i)).val % 2 = 0 := by
          rw [← hs]
          simp [ketPos]
        exact hk hc
      · have hs := congrArg σ he
        simp only [Equiv.apply_symm_apply] at hs
        have hc : (σ (braPos i)).val % 2 = 0 := by
          rw [← hs]
          simp [ketPos]
        exact hb hc
    simp [bitPattern, h]

private theorem singleCols_eq {r d : ℕ} (hd : 2 ≤ d)
    (σ : Equiv.Perm (Fin (2 * r))) (i : Fin r) :
    (singleImage hd σ i 0).2 = (singleImage hd σ i 1).2 ↔
      (σ (ketPos i)).val % 2 = 0 ∧ (σ (braPos i)).val % 2 = 0 := by
  constructor
  · intro h
    constructor
    · by_contra hk
      have hp := braPos_party (σ (ketPos i)) hk
      have he := congrFun h (party (σ (ketPos i)))
      change merge (bitPattern hd {i} 0) (bitPattern hd {i} 0)
          (σ.symm (braPos (party (σ (ketPos i))))) =
        merge (bitPattern hd {i} 1) (bitPattern hd {i} 1)
          (σ.symm (braPos (party (σ (ketPos i))))) at he
      rw [hp, Equiv.symm_apply_apply] at he
      simp [merge_equal, bitPattern] at he
    · by_contra hk
      have hp := braPos_party (σ (braPos i)) hk
      have he := congrFun h (party (σ (braPos i)))
      change merge (bitPattern hd {i} 0) (bitPattern hd {i} 0)
          (σ.symm (braPos (party (σ (braPos i))))) =
        merge (bitPattern hd {i} 1) (bitPattern hd {i} 1)
          (σ.symm (braPos (party (σ (braPos i))))) at he
      rw [hp, Equiv.symm_apply_apply] at he
      simp [merge_equal, bitPattern] at he
  · rintro ⟨hk, hb⟩
    funext k
    change merge (bitPattern hd {i} 0) (bitPattern hd {i} 0) (σ.symm (braPos k)) =
      merge (bitPattern hd {i} 1) (bitPattern hd {i} 1) (σ.symm (braPos k))
    rw [merge_equal, merge_equal]
    have h : party (σ.symm (braPos k)) ≠ i := by
      intro he
      rcases (party_eq_iff _ _).mp he with he | he
      · have hs := congrArg σ he
        simp only [Equiv.apply_symm_apply] at hs
        have hc : (σ (ketPos i)).val % 2 ≠ 0 := by
          rw [← hs]
          dsimp [braPos]
          omega
        exact hc hk
      · have hs := congrArg σ he
        simp only [Equiv.apply_symm_apply] at hs
        have hc : (σ (braPos i)).val % 2 ≠ 0 := by
          rw [← hs]
          dsimp [braPos]
          omega
        exact hc hb
    simp [bitPattern, h]

/-- The single-party witness has norm sqrt(1/2) exactly when both local positions
lie on the same output side, and norm one otherwise. -/
theorem singleWitness_traceNorm {r d : ℕ} (hd : 2 ≤ d)
    (σ : Equiv.Perm (Fin (2 * r))) (i : Fin r) :
    D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm (permute σ (singleWitness hd i)) =
      if LabelRecovery.sameSide (RowSetRecovery.rowLabels (rowSet σ) i)
      then Real.sqrt (1 / 2) else 1 := by
  have hside :
      ((singleImage hd σ i 0).1 = (singleImage hd σ i 1).1 ∨
        (singleImage hd σ i 0).2 = (singleImage hd σ i 1).2) ↔
      LabelRecovery.sameSide (RowSetRecovery.rowLabels (rowSet σ) i) := by
    rw [singleRows_eq, singleCols_eq]
    by_cases hk : (σ (ketPos i)).val % 2 = 0 <;>
      by_cases hb : (σ (braPos i)).val % 2 = 0 <;>
      simp [LabelRecovery.sameSide, RowSetRecovery.rowLabels, rowSet, hk, hb]
  have hne : singleImage hd σ i 0 ≠ singleImage hd σ i 1 := by
    intro he
    have hp := (indexPermutation σ).symm.injective he
    have ht := bitPattern_injective hd {i} (singleton_nonempty i) (congrArg Prod.fst hp)
    norm_num at ht
  rw [singleWitness_eq]
  change D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm
    (permute σ (Matrix.single (bitPattern hd {i} 0) (bitPattern hd {i} 0) (1 / 2)) +
      permute σ (Matrix.single (bitPattern hd {i} 1) (bitPattern hd {i} 1) (1 / 2))) = _
  rw [permute_single, permute_single]
  change D5.S3.Quantum.Foundation.FiniteTraceDistance.traceNorm
    (Matrix.single (singleImage hd σ i 0).1 (singleImage hd σ i 0).2 (1 / 2 : ℂ) +
      Matrix.single (singleImage hd σ i 1).1 (singleImage hd σ i 1).2 (1 / 2)) = _
  by_cases hr : (singleImage hd σ i 0).1 = (singleImage hd σ i 1).1
  · have hc : (singleImage hd σ i 0).2 ≠ (singleImage hd σ i 1).2 :=
      fun hc => hne (Prod.ext hr hc)
    rw [if_pos (hside.mp (Or.inl hr)), hr]
    exact traceNorm_two_single_same_row _ _ _ hc
  · by_cases hc : (singleImage hd σ i 0).2 = (singleImage hd σ i 1).2
    · rw [if_pos (hside.mp (Or.inr hc)), hc]
      exact traceNorm_two_single_same_column _ _ _ hr
    · rw [if_neg (fun hs => (hside.mpr hs).elim hr hc)]
      exact traceNorm_two_single_separate _ _ _ _ hr hc

/-- Equality of all density-state permutation norms preserves each party's same-side status. -/
theorem dependent_sameSide {r d : ℕ} (hd : 2 ≤ d)
    {σ μ : Equiv.Perm (Fin (2 * r))} (h : Dependent r d σ μ) (i : Fin r) :
    LabelRecovery.sameSide (RowSetRecovery.rowLabels (rowSet σ) i) ↔
      LabelRecovery.sameSide (RowSetRecovery.rowLabels (rowSet μ) i) := by
  have he := h (singleWitness hd i) (singleWitness_isDensity hd i)
  rw [singleWitness_traceNorm hd σ i, singleWitness_traceNorm hd μ i] at he
  have hs : Real.sqrt (1 / 2 : ℝ) ≠ 1 := by
    intro ht
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    rw [ht] at hsq
    norm_num at hsq
  by_cases hσ : LabelRecovery.sameSide (RowSetRecovery.rowLabels (rowSet σ) i)
  · constructor
    · intro _
      by_contra hμ
      have ht : Real.sqrt (1 / 2 : ℝ) = 1 := by
        simpa only [ite_eq_left hσ, ite_eq_right hμ] using he
      exact hs ht
    · intro _
      exact hσ
  · constructor
    · intro hbad
      exact (hσ hbad).elim
    · intro hμ
      have ht : (1 : ℝ) = Real.sqrt (1 / 2) := by
        simpa only [ite_eq_right hσ, ite_eq_left hμ] using he
      exact (hs ht.symm).elim

end D5.S3.Quantum.Entanglement.PermutationCriteria
