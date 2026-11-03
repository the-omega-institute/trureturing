/- GID: D5/S3/QuadraticForms/StructuredRankOneInertia
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/StructuredRankOneInertia
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Structured real symmetric rank-one downdates retain every singular direction and remove exactly the pivot sign. -/

import D5.S3.Weil.Pick.InvertibleHermitianInertiaPullback
import D5.S3.SpectralTopology.PointGapExactInertia
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic

/-!
The hyperplane and block-congruence mechanism is proposed by Lucid in
MathOverflow question 513954, revision 2 (CC BY-SA 4.0):
https://mathoverflow.net/revisions/513954/2 .
The congruence law is standard Sylvester inertia. No inverse of the original
symmetric matrix is used.
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators

namespace D5.S3.QuadraticForms.StructuredRankOneInertia

open RHLinalg
open D5.S3.Weil.Pick.InvertibleHermitianInertiaPullback

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The quadratic pivot of a real matrix and a vector. -/
def pivot (A : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ := x ⬝ᵥ (A *ᵥ x)

/-- The structured downdate, with its coefficient tied to the quadratic pivot. -/
def downdate (A : Matrix ι ι ℝ) (x : ι → ℝ) : Matrix ι ι ℝ :=
  A - (pivot A x)⁻¹ • vecMulVec (A *ᵥ x) (A *ᵥ x)

private theorem count_roots (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (p : ℝ → Prop) [DecidablePred p] :
    A.charpoly.roots.countP p = (Finset.univ.filter fun i => p (hA.eigenvalues i)).card := by
  rw [hA.roots_charpoly_eq_eigenvalues, Multiset.countP_map]
  simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq]
  rfl

private theorem blockHermitian {κ : Type} {A : Matrix ι ι ℝ} {B : Matrix κ κ ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (fromBlocks A 0 0 B).IsHermitian :=
  hA.fromBlocks (by simp) hB

private theorem block_counts {κ : Type} [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    posIndex (blockHermitian hA hB) = posIndex hA + posIndex hB ∧
    negIndex (blockHermitian hA hB) = negIndex hA + negIndex hB := by
  have hroots : (fromBlocks A 0 0 B).charpoly.roots = A.charpoly.roots + B.charpoly.roots := by
    rw [charpoly_fromBlocks_zero₁₂, Polynomial.roots_mul]
    exact mul_ne_zero A.charpoly_monic.ne_zero B.charpoly_monic.ne_zero
  constructor
  · rw [posIndex, ← count_roots _ (blockHermitian hA hB), hroots,
      Multiset.countP_add, count_roots _ hA, count_roots _ hB]
    rfl
  · rw [negIndex, ← count_roots _ (blockHermitian hA hB) (fun a : ℝ => a < 0), hroots,
      Multiset.countP_add, count_roots _ hA, count_roots _ hB]
    rfl

theorem diagonal_counts (d : ι → ℝ) :
    posIndex (isHermitian_diagonal d) =
      (Finset.univ.filter fun i => 0 < d i).card ∧
    negIndex (isHermitian_diagonal d) =
      (Finset.univ.filter fun i => d i < 0).card := by
  have hroots : (diagonal d).charpoly.roots = Finset.univ.val.map d := by
    rw [charpoly_diagonal, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  constructor
  · rw [posIndex, ← count_roots, hroots, Multiset.countP_map]
    rfl
  · rw [negIndex, ← count_roots _ (isHermitian_diagonal d) (fun a : ℝ => a < 0), hroots, Multiset.countP_map]
    rfl

omit [DecidableEq ι] in
private theorem pairing_symm (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (x v : ι → ℝ) : (A *ᵥ x) ⬝ᵥ v = x ⬝ᵥ (A *ᵥ v) := by
  have hs : Aᵀ = A := by simpa only [conjTranspose_eq_transpose_of_trivial] using hA.eq
  rw [dotProduct_comm, ← dotProduct_transpose_mulVec, hs]

omit [DecidableEq ι] in
private theorem downdate_apply (A : Matrix ι ι ℝ) (x v : ι → ℝ) :
    downdate A x *ᵥ v = A *ᵥ v - ((pivot A x)⁻¹ * ((A *ᵥ x) ⬝ᵥ v)) • (A *ᵥ x) := by
  rw [downdate, sub_mulVec, smul_mulVec, vecMulVec_mulVec]
  simp only [op_smul_eq_smul, smul_smul, smul_eq_mul]

omit [DecidableEq ι] in
/-- The kernel is exactly the direct sum of the original kernel and the pivot line. -/
theorem kernel_split (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (x : ι → ℝ) (h : pivot A x ≠ 0) :
    LinearMap.ker (downdate A x).mulVecLin =
      LinearMap.ker A.mulVecLin ⊔ Submodule.span ℝ {x} ∧
    Disjoint (LinearMap.ker A.mulVecLin) (Submodule.span ℝ {x}) := by
  have hx : x ≠ 0 := by
    intro hx
    simp [pivot, hx] at h
  have hw : A *ᵥ x ≠ 0 := by
    intro hw
    simp [pivot, hw] at h
  have hp : (A *ᵥ x) ⬝ᵥ x = pivot A x := dotProduct_comm _ _
  have hline : Submodule.span ℝ {x} ≤ LinearMap.ker (downdate A x).mulVecLin := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    change downdate A x *ᵥ x = 0
    rw [downdate_apply, hp, inv_mul_cancel₀ h, one_smul, sub_self]
  have hker : LinearMap.ker A.mulVecLin ≤ LinearMap.ker (downdate A x).mulVecLin := by
    intro v hv
    change A *ᵥ v = 0 at hv
    change downdate A x *ᵥ v = 0
    rw [downdate_apply, pairing_symm A hA, hv]
    simp
  constructor
  · apply le_antisymm
    · intro v hv
      change downdate A x *ᵥ v = 0 at hv
      let t := (pivot A x)⁻¹ * ((A *ᵥ x) ⬝ᵥ v)
      have hk : v - t • x ∈ LinearMap.ker A.mulVecLin := by
        change A *ᵥ (v - t • x) = 0
        simpa only [mulVec_sub, mulVec_smul, t, downdate_apply] using hv
      have ht : t • x ∈ Submodule.span ℝ {x} := Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      have := Submodule.add_mem_sup hk ht
      simpa using this
    · exact sup_le hker hline
  · rw [disjoint_iff]
    apply eq_bot_iff.mpr
    intro v hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv.2
    have hc : c • (A *ᵥ x) = 0 := by simpa using hv.1
    have : c = 0 := (smul_eq_zero.mp hc).resolve_right hw
    simp [this]

omit [DecidableEq ι] in
/-- The number of null directions increases by exactly one, even for singular input. -/
theorem nullity_downdate (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (x : ι → ℝ) (h : pivot A x ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (downdate A x).mulVecLin) =
      Module.finrank ℝ (LinearMap.ker A.mulVecLin) + 1 := by
  have hx : x ≠ 0 := by intro hx; simp [pivot, hx] at h
  obtain ⟨hk, hd⟩ := kernel_split A hA x h
  rw [hk]
  have hf := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.ker A.mulVecLin) (Submodule.span ℝ {x})
  rw [hd.eq_bot, finrank_bot, add_zero, finrank_span_singleton hx] at hf
  exact hf

private theorem downdate_hermitian (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (x : ι → ℝ) : (downdate A x).IsHermitian := by
  apply hA.sub
  rw [IsHermitian]
  ext i j
  simp [conjTranspose_apply, vecMulVec, mul_comm]

private abbrev scalarBlock (a : ℝ) : Matrix Unit Unit ℝ := diagonal (fun _ => a)

private theorem upper_congruence (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (x : ι → ℝ) :
    let B := fromBlocks (1 : Matrix ι ι ℝ) (replicateCol Unit x) 0 1
    Bᴴ * fromBlocks A 0 0 (0 : Matrix Unit Unit ℝ) * B =
      fromBlocks A (replicateCol Unit (A *ᵥ x)) (replicateRow Unit (A *ᵥ x))
        (scalarBlock (pivot A x)) := by
  dsimp only
  have hs : Aᵀ = A := by simpa only [conjTranspose_eq_transpose_of_trivial] using hA.eq
  have hrow : replicateRow Unit x * A = replicateRow Unit (A *ᵥ x) := by
    rw [← replicateRow_vecMul, ← mulVec_transpose, hs]
  simp only [fromBlocks_conjTranspose, conjTranspose_one, conjTranspose_zero,
    fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
    Matrix.mul_zero, add_zero, zero_add, conjTranspose_replicateCol, star_trivial,
    ← replicateCol_mulVec, hrow, replicateRow_mul_replicateCol]
  congr 1
  ext i j
  change (A *ᵥ x) ⬝ᵥ x = pivot A x
  exact dotProduct_comm (A *ᵥ x) x

private theorem lower_congruence (A : Matrix ι ι ℝ) (x : ι → ℝ) (h : pivot A x ≠ 0) :
    let w := A *ᵥ x
    let B := fromBlocks (1 : Matrix ι ι ℝ) 0
      (-(pivot A x)⁻¹ • replicateRow Unit w) 1
    Bᴴ * fromBlocks A (replicateCol Unit w) (replicateRow Unit w)
      (scalarBlock (pivot A x)) * B =
      fromBlocks (downdate A x) 0 0 (scalarBlock (pivot A x)) := by
  dsimp only
  simp only [fromBlocks_conjTranspose, conjTranspose_one, conjTranspose_zero,
    conjTranspose_smul, star_trivial, conjTranspose_replicateRow,
    fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
    Matrix.mul_zero, add_zero, zero_add]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [fromBlocks, downdate, scalarBlock, mul_apply, Finset.mul_sum,
      Finset.sum_mul, vecMulVec, h, mul_assoc]
    <;> field_simp [h] <;> ring
  · simp [fromBlocks, scalarBlock, mul_apply, h, mul_assoc]
    <;> field_simp [h] <;> ring
  · simp [fromBlocks, scalarBlock, mul_apply, h, mul_assoc]
  · simp [fromBlocks, scalarBlock, mul_apply, h]

/-- The zero eigenvalue count, including algebraic multiplicity. -/
def zeroIndex {A : Matrix ι ι ℝ} (hA : A.IsHermitian) : ℕ :=
  (Finset.univ.filter fun i => hA.eigenvalues i = 0).card

private theorem zeroIndex_eq_nullity {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    zeroIndex hA = Module.finrank ℝ (LinearMap.ker A.mulVecLin) := by
  have hr := hA.rank_eq_card_non_zero_eigs
  rw [Fintype.card_subtype] at hr
  have hc : zeroIndex hA + A.rank = Fintype.card ι := by
    rw [hr, zeroIndex]
    simpa only [Finset.card_univ] using
      Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun i => hA.eigenvalues i = 0)
  have hn := A.mulVecLin.finrank_range_add_finrank_ker
  simp only [Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_one] at hn
  change A.rank + Module.finrank ℝ (LinearMap.ker A.mulVecLin) = Fintype.card ι at hn
  omega

private theorem congruence_counts {κ : Type} [Fintype κ] [DecidableEq κ]
    {A B : Matrix κ κ ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (P : Matrix κ κ ℝ) (hP : IsUnit P.det) (hp : Pᴴ * A * P = B) :
    posIndex hB = posIndex hA ∧ negIndex hB = negIndex hA := by
  have hi := inertia_invariant_of_isUnit_det hA P hP
  simpa only [hp] using hi

private theorem additive_inertia (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (x : ι → ℝ) (h : pivot A x ≠ 0) :
    posIndex hA = posIndex (downdate_hermitian A hA x) + (if 0 < pivot A x then 1 else 0) ∧
    negIndex hA = negIndex (downdate_hermitian A hA x) + (if pivot A x < 0 then 1 else 0) := by
  let w := A *ᵥ x
  let U : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ := fromBlocks (1 : Matrix ι ι ℝ) (replicateCol Unit x) 0 1
  let L : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ := fromBlocks (1 : Matrix ι ι ℝ) 0 (-(pivot A x)⁻¹ • replicateRow Unit w) 1
  let E : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ := fromBlocks A (replicateCol Unit w) (replicateRow Unit w) (scalarBlock (pivot A x))
  have hU : IsUnit U.det := by simp [U, det_fromBlocks_zero₂₁]
  have hL : IsUnit L.det := by simp [L, det_fromBlocks_zero₁₂]
  have hE : E.IsHermitian := hA.fromBlocks (by simp [conjTranspose_replicateCol])
    (isHermitian_diagonal _)
  have hbase := blockHermitian hA (isHermitian_zero (n := Unit) (α := ℝ))
  have hm := downdate_hermitian A hA x
  have heqU := congruence_counts hbase hE U hU (upper_congruence A hA x)
  have heqL := congruence_counts hE (blockHermitian hm (isHermitian_diagonal _)) L hL
    (lower_congruence A x h)
  have hb0 := block_counts A (0 : Matrix Unit Unit ℝ) hA (isHermitian_zero)
  have hbd := block_counts (downdate A x) (scalarBlock (pivot A x)) hm (isHermitian_diagonal _)
  have hd := diagonal_counts (fun _ : Unit => pivot A x)
  have hz := diagonal_counts (fun _ : Unit => (0 : ℝ))
  have hp0 : posIndex (isHermitian_zero (n := Unit) (α := ℝ)) = 0 := by
    simpa using hz.1
  have hn0 : negIndex (isHermitian_zero (n := Unit) (α := ℝ)) = 0 := by
    simpa using hz.2
  have hpd : posIndex (isHermitian_diagonal (fun _ : Unit => pivot A x)) =
      if 0 < pivot A x then 1 else 0 := by
    split_ifs with hp <;> simpa [hp] using hd.1
  have hnd : negIndex (isHermitian_diagonal (fun _ : Unit => pivot A x)) =
      if pivot A x < 0 then 1 else 0 := by
    split_ifs with hn <;> simpa [hn] using hd.2
  constructor <;> omega

/-- Both complete inertia triples for every real symmetric input, including singular matrices. -/
theorem inertia_downdate (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (x : ι → ℝ) (h : pivot A x ≠ 0) :
    ∃ hM : (downdate A x).IsHermitian,
      (0 < pivot A x → posIndex hA = posIndex hM + 1 ∧
        negIndex hM = negIndex hA ∧ zeroIndex hM = zeroIndex hA + 1) ∧
      (pivot A x < 0 → posIndex hM = posIndex hA ∧
        negIndex hA = negIndex hM + 1 ∧ zeroIndex hM = zeroIndex hA + 1) := by
  have hz := nullity_downdate A hA x h
  have hi := additive_inertia A hA x h
  have hzero : zeroIndex (downdate_hermitian A hA x) = zeroIndex hA + 1 := by
    simpa only [zeroIndex_eq_nullity] using hz
  refine ⟨downdate_hermitian A hA x, ?_, ?_⟩
  · intro hp
    have hn : ¬pivot A x < 0 := not_lt_of_ge hp.le
    simp only [if_pos hp, if_neg hn, add_zero] at hi
    exact ⟨hi.1, hi.2.symm, hzero⟩
  · intro hn
    have hp : ¬0 < pivot A x := not_lt_of_ge hn.le
    simp only [if_pos hn, if_neg hp, add_zero] at hi
    exact ⟨hi.1.symm, hi.2, hzero⟩

#print axioms inertia_downdate
#print axioms kernel_split
#print axioms nullity_downdate

end D5.S3.QuadraticForms.StructuredRankOneInertia
