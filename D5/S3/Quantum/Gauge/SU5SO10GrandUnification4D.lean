/- GID: D5/S3/Quantum/Gauge/SU5SO10GrandUnification4D
   generality: G
   mirror-B: D5/B/S3/Quantum/Gauge/SU5SO10GrandUnification4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unified gauge generators, adjoint and fermion weights, and chiral spinor charges. -/

import OmegaBuild.Commands
import OmegaMath.Algebra.ExteriorSquareTrace
import OmegaMath.LinearAlgebra.Matrix.AdjointIrreducibility
import OmegaMath.LinearAlgebra.Matrix.ComplexRealification
import OmegaMath.LinearAlgebra.SpinorWeights5
import D5.S3.Quantum.Gauge.GaugeUnificationRG4D
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-! The fundamental coordinates list the three color entries before the weak pair.
Compact generators are written in the Hermitian convention. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped Matrix

namespace D5.S3.Quantum.Gauge.SU5SO10GrandUnification4D

abbrev M5 := Matrix (Fin 5) (Fin 5) ℂ
abbrev M3 := Matrix (Fin 3) (Fin 3) ℂ
abbrev M2 := Matrix (Fin 2) (Fin 2) ℂ

private abbrev partition : Fin 3 ⊕ Fin 2 ≃ Fin 5 := finSumFinEquiv

def colorBlock (A : M3) : M5 := reindex partition partition (fromBlocks A 0 0 (0 : M2))
def weakBlock (B : M2) : M5 := reindex partition partition (fromBlocks (0 : M3) 0 0 B)

def hyperchargeWeights : Fin 5 → ℝ := ![-1/3, -1/3, -1/3, 1/2, 1/2]
def weakWeights : Fin 5 → ℝ := ![0, 0, 0, 1/2, -1/2]
def YSM : M5 := diagonal fun i => (hyperchargeWeights i : ℂ)
def TY : M5 := (Real.sqrt (3 / 5) : ℂ) • YSM
def T3 : M5 := diagonal fun i => (weakWeights i : ℂ)
def TColor8 : M5 := ((Real.sqrt 3 : ℂ)⁻¹ / 2) • diagonal ![1, 1, -2, 0, 0]
def Qem : M5 := T3 + YSM

def smEmbedding (A : M3) (B : M2) (s : ℝ) : M5 :=
  colorBlock A + weakBlock B + (s : ℂ) • TY

private theorem trace_reindex_blocks (A : M3) (B : M2)
    (C : Matrix (Fin 3) (Fin 2) ℂ) (D : Matrix (Fin 2) (Fin 3) ℂ) :
    (reindex partition partition (fromBlocks A C D B)).trace = A.trace + B.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.reindex_apply, Matrix.submatrix_apply]
  calc
    _ = ∑ i : Fin 3 ⊕ Fin 2, fromBlocks A C D B i i :=
      partition.symm.sum_comp (fun i : Fin 3 ⊕ Fin 2 => fromBlocks A C D B i i)
    _ = _ := by simp [Fintype.sum_sum_type]

theorem su5_embedding_traceless_hermitian (A : M3) (B : M2) (s : ℝ)
    (hA : A.trace = 0) (hB : B.trace = 0) (sA : A.IsHermitian) (sB : B.IsHermitian) :
    (smEmbedding A B s).trace = 0 ∧ (smEmbedding A B s).IsHermitian := by
  have hy : YSM.IsHermitian := by
    change YSMᴴ = YSM
    simp [YSM, Matrix.diagonal_conjTranspose]
  constructor
  · unfold smEmbedding colorBlock weakBlock
    rw [Matrix.trace_add, Matrix.trace_add, trace_reindex_blocks, trace_reindex_blocks]
    norm_num [hA, hB, TY, YSM, hyperchargeWeights, Fin.sum_univ_succ]
  · change (smEmbedding A B s)ᴴ = smEmbedding A B s
    change Aᴴ = A at sA
    change Bᴴ = B at sB
    simp [smEmbedding, colorBlock, weakBlock, TY, Matrix.reindex_apply,
      Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose, sA, sB, hy.eq]

private theorem ysm_blocks :
    YSM = reindex partition partition
      (fromBlocks ((-1/3 : ℂ) • (1 : M3)) 0 0 ((1/2 : ℂ) • (1 : M2))) := by
  ext i j
  obtain ⟨i, rfl⟩ := partition.surjective i
  obtain ⟨j, rfl⟩ := partition.surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [YSM, hyperchargeWeights, Matrix.diagonal, Matrix.one_apply,
      finSumFinEquiv, Fin.castAdd, Fin.castLE, Fin.natAdd, Fin.ext_iff,
      Matrix.smul_apply, Complex.ofReal_div]

theorem su5_sm_blocks_commute (A : M3) (B : M2) :
    Commute (colorBlock A) (weakBlock B) ∧
    Commute (colorBlock A) YSM ∧ Commute (weakBlock B) YSM ∧
    Commute (colorBlock A) TY ∧ Commute (weakBlock B) TY := by
  have hcolor : Commute (colorBlock A) YSM := by
    unfold Commute SemiconjBy colorBlock
    rw [ysm_blocks]
    change Matrix.reindexAlgEquiv ℂ ℂ partition _ * Matrix.reindexAlgEquiv ℂ ℂ partition _ =
      Matrix.reindexAlgEquiv ℂ ℂ partition _ * Matrix.reindexAlgEquiv ℂ ℂ partition _
    simp [Matrix.fromBlocks_multiply, Matrix.mul_smul]
  have hweak : Commute (weakBlock B) YSM := by
    unfold Commute SemiconjBy weakBlock
    rw [ysm_blocks]
    change Matrix.reindexAlgEquiv ℂ ℂ partition _ * Matrix.reindexAlgEquiv ℂ ℂ partition _ =
      Matrix.reindexAlgEquiv ℂ ℂ partition _ * Matrix.reindexAlgEquiv ℂ ℂ partition _
    simp [Matrix.fromBlocks_multiply, Matrix.mul_smul]
  refine ⟨?_, hcolor, hweak, hcolor.smul_right _, hweak.smul_right _⟩
  unfold Commute SemiconjBy colorBlock weakBlock
  change Matrix.reindexAlgEquiv ℂ ℂ partition _ * Matrix.reindexAlgEquiv ℂ ℂ partition _ =
    Matrix.reindexAlgEquiv ℂ ℂ partition _ * Matrix.reindexAlgEquiv ℂ ℂ partition _
  simp [Matrix.fromBlocks_multiply]

private theorem trace_diag_sq (d : Fin 5 → ℂ) :
    ((diagonal d) ^ 2).trace = ∑ i, (d i)^2 := by
  rw [pow_two, diagonal_mul_diagonal, Matrix.trace_diagonal]
  simp [pow_two]

theorem su5_trace_normalization :
    (TY ^ 2).trace = 1/2 ∧ (T3 ^ 2).trace = 1/2 ∧ (TColor8 ^ 2).trace = 1/2 ∧
    (YSM ^ 2).trace = 5/6 ∧ (YSM ^ 2).trace / (T3 ^ 2).trace = 5/3 := by
  have hy : (YSM ^ 2).trace = 5/6 := by
    rw [YSM, trace_diag_sq]
    norm_num [hyperchargeWeights, Fin.sum_univ_succ]
  have hw : (T3 ^ 2).trace = 1/2 := by
    rw [T3, trace_diag_sq]
    norm_num [weakWeights, Fin.sum_univ_succ]
  have hr : ((Real.sqrt (3/5) : ℝ) : ℂ) ^ 2 = 3/5 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3/5)]
    norm_num
  have hc : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  refine ⟨?_, hw, ?_, hy, by rw [hy, hw]; norm_num⟩
  · rw [TY, smul_pow, Matrix.trace_smul, hy, hr]
    norm_num [smul_eq_mul]
  · rw [TColor8, smul_pow, Matrix.trace_smul, trace_diag_sq, div_pow, inv_pow, hc]
    norm_num [Fin.sum_univ_succ, smul_eq_mul]

theorem su5_electric_charge_traceless :
    Qem = diagonal ![-1/3, -1/3, -1/3, 1, 0] ∧ Qem.trace = 0 := by
  have h : Qem = diagonal ![-1/3, -1/3, -1/3, 1, 0] := by
    rw [Qem, T3, YSM, diagonal_add]
    apply congrArg diagonal
    funext i
    fin_cases i <;> norm_num [hyperchargeWeights, weakWeights, Complex.ofReal_div]
  exact ⟨h, by rw [h]; norm_num [Fin.sum_univ_succ]⟩

theorem su5_weinberg_angle_from_trace :
    (Qem ^ 2).trace = 4/3 ∧ (T3 ^ 2).trace / (Qem ^ 2).trace = 3/8 := by
  have h : (Qem ^ 2).trace = 4/3 := by
    rw [su5_electric_charge_traceless.1, trace_diag_sq]
    norm_num [Fin.sum_univ_succ]
  exact ⟨h, by rw [su5_trace_normalization.2.1, h]; norm_num⟩

abbrev ColorWeak := Matrix (Fin 3) (Fin 2) ℂ
abbrev WeakColor := Matrix (Fin 2) (Fin 3) ℂ

def adjointBlocks (A : M3) (B : M2) (t : ℂ) (C : ColorWeak) (D : WeakColor) : M5 :=
  reindex partition partition
    (fromBlocks (A + (-t/3 : ℂ) • (1 : M3)) C D (B + (t/2 : ℂ) • (1 : M2)))

private theorem color_trace_shift (A : M3) (t : ℂ) :
    (A + (-t/3 : ℂ) • (1 : M3)).trace = A.trace - t := by
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one]
  norm_num [smul_eq_mul]
  ring

private theorem weak_trace_shift (B : M2) (t : ℂ) :
    (B + (t/2 : ℂ) • (1 : M2)).trace = B.trace + t := by
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one]
  norm_num [smul_eq_mul]

/-- The adjoint has unique color, weak, hypercharge, and rectangular coordinates. -/
theorem su5_adjoint_decomposition (M : M5) (hM : M.trace = 0) :
    ∃! p : M3 × M2 × ℂ × ColorWeak × WeakColor,
      p.1.trace = 0 ∧ p.2.1.trace = 0 ∧
      adjointBlocks p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 = M := by
  let N := reindex partition.symm partition.symm M
  have hN : reindex partition partition N = M :=
    (reindex partition partition).apply_symm_apply M
  have htr : N.toBlocks₁₁.trace + N.toBlocks₂₂.trace = 0 := by
    rw [← trace_reindex_blocks N.toBlocks₁₁ N.toBlocks₂₂ N.toBlocks₁₂ N.toBlocks₂₁,
      Matrix.fromBlocks_toBlocks, hN, hM]
  let t := -N.toBlocks₁₁.trace
  let A := N.toBlocks₁₁ - (-t/3 : ℂ) • (1 : M3)
  let B := N.toBlocks₂₂ - (t/2 : ℂ) • (1 : M2)
  have hA : A.trace = 0 := by
    simp [A, t, Matrix.trace_sub, smul_eq_mul]
  have hB : B.trace = 0 := by
    simp [B, t, Matrix.trace_sub, smul_eq_mul]
    linear_combination htr
  have hrep : adjointBlocks A B t N.toBlocks₁₂ N.toBlocks₂₁ = M := by
    simpa only [adjointBlocks, A, B, sub_add_cancel, Matrix.fromBlocks_toBlocks] using hN
  refine ⟨⟨A, B, t, N.toBlocks₁₂, N.toBlocks₂₁⟩, ⟨hA, hB, hrep⟩, ?_⟩
  rintro ⟨A', B', t', C', D'⟩ ⟨hA', hB', hrep'⟩
  have heq := Matrix.fromBlocks_inj.mp
    ((reindex partition partition).injective (hrep'.trans hrep.symm))
  obtain ⟨hc, hC, hD, hw⟩ := heq
  have ht : t' = t := by
    have ht := congrArg Matrix.trace hc
    rw [color_trace_shift, color_trace_shift, hA', hA] at ht
    exact neg_injective (by simpa only [zero_sub] using ht)
  subst t'
  have ha : A' = A := add_right_cancel hc
  have hb : B' = B := add_right_cancel hw
  exact Prod.ext ha (Prod.ext hb (Prod.ext rfl (Prod.ext hC hD)))

abbrev TraceFree (n : ℕ) :=
  LinearMap.ker (Matrix.traceLinearMap (n := Fin n) ℂ ℂ)

private theorem traceFree_rank (n : ℕ) :
    Module.finrank ℂ (TraceFree (n+1)) + 1 = (n+1) * (n+1) := by
  let tr : Matrix (Fin (n+1)) (Fin (n+1)) ℂ →ₗ[ℂ] ℂ := Matrix.traceLinearMap _ _ _
  have h : Function.Surjective tr := fun z => ⟨Matrix.single 0 0 z, by simp [tr]⟩
  have hdim := tr.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr h, finrank_top, Module.finrank_matrix] at hdim
  simpa [tr, add_comm] using hdim

theorem su5_adjoint_dimensions :
    Module.finrank ℂ (TraceFree 5) = 24 ∧
    Module.finrank ℂ (TraceFree 3) = 8 ∧
    Module.finrank ℂ (TraceFree 2) = 3 ∧
    Module.finrank ℂ ColorWeak = 6 ∧ Module.finrank ℂ WeakColor = 6 := by
  have h5 := traceFree_rank 4
  have h3 := traceFree_rank 2
  have h2 := traceFree_rank 1
  change Module.finrank ℂ (TraceFree 5) + 1 = 25 at h5
  change Module.finrank ℂ (TraceFree 3) + 1 = 9 at h3
  change Module.finrank ℂ (TraceFree 2) + 1 = 4 at h2
  refine ⟨by omega, by omega, by omega, ?_, ?_⟩ <;> simp [Module.finrank_matrix]

def commutator {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  A * B - B * A

/-- The commutator acts on each adjoint summand through its two block indices. -/
theorem su5_adjoint_block_action (Ac Bc : M3) (Aw Bw : M2) (y z : ℂ)
    (C : ColorWeak) (D : WeakColor) :
    commutator (adjointBlocks Ac Aw y 0 0) (adjointBlocks Bc Bw z C D) =
      adjointBlocks (commutator Ac Bc) (commutator Aw Bw) 0
        (Ac * C - C * Aw - (5 * y / 6 : ℂ) • C)
        (Aw * D - D * Ac + (5 * y / 6 : ℂ) • D) := by
  let e := Matrix.reindexAlgEquiv ℂ ℂ partition
  unfold adjointBlocks commutator
  change e _ * e _ - e _ * e _ = e _
  rw [← map_mul, ← map_mul, ← map_sub]
  congr 1
  simp only [Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
    neg_zero, zero_div, zero_smul]
  rw [sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]
  congr 1
  · rw [← sub_eq_add_neg]
    simp [Matrix.add_mul, Matrix.mul_add]
    module
  · rw [← sub_eq_add_neg]
    simp [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul]
    module
  · rw [← sub_eq_add_neg]
    simp [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul]
    module
  · rw [← sub_eq_add_neg]
    simp [Matrix.add_mul, Matrix.mul_add]
    module

private theorem smEmbedding_eq_adjointBlocks (A : M3) (B : M2) (s : ℝ) :
    smEmbedding A B s =
      adjointBlocks A B ((s * Real.sqrt (3/5) : ℝ) : ℂ) 0 0 := by
  unfold smEmbedding colorBlock weakBlock TY adjointBlocks
  rw [ysm_blocks]
  ext i j
  obtain ⟨i, rfl⟩ := partition.surjective i
  obtain ⟨j, rfl⟩ := partition.surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.add_apply, Matrix.smul_apply,
      Equiv.symm_apply_apply, Complex.ofReal_mul, smul_eq_mul] <;> ring

theorem su5_sm_embedding_injective (A A' : M3) (B B' : M2) (s s' : ℝ)
    (hA : A.trace = 0) (hA' : A'.trace = 0)
    (h : smEmbedding A B s = smEmbedding A' B' s') :
    A = A' ∧ B = B' ∧ s = s' := by
  rw [smEmbedding_eq_adjointBlocks, smEmbedding_eq_adjointBlocks] at h
  obtain ⟨hc, _, _, hw⟩ := Matrix.fromBlocks_inj.mp
    ((reindex partition partition).injective h)
  have ht := congrArg Matrix.trace hc
  rw [color_trace_shift, color_trace_shift, hA, hA'] at ht
  have hs := Complex.ofReal_injective (neg_injective (by simpa only [zero_sub] using ht))
  have hs' := mul_right_cancel₀ (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3/5)).ne' hs
  subst s'
  exact ⟨add_right_cancel hc, add_right_cancel hw, rfl⟩

/-- Invariant subspaces of the five adjoint blocks are zero or full. -/
theorem su5_adjoint_blocks_irreducible :
    (∀ p : Fin 2,
      let n := (![3, 2] : Fin 2 → ℕ) p
      ∀ S : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ),
      (∀ A ∈ S, A.trace = 0) →
      (∀ A B : Matrix (Fin n) (Fin n) ℂ, A.trace = 0 → B ∈ S → commutator A B ∈ S) →
      S = ⊥ ∨ ∀ A : Matrix (Fin n) (Fin n) ℂ, A.trace = 0 → A ∈ S) ∧
    (∀ p : Fin 2,
      let n := (![3, 2] : Fin 2 → ℕ) p
      let m := (![2, 3] : Fin 2 → ℕ) p
      ∀ S : Submodule ℂ (Matrix (Fin n) (Fin m) ℂ),
      (∀ (A : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin n) (Fin m) ℂ),
        A.trace = 0 → X ∈ S → A * X ∈ S) →
      (∀ (B : Matrix (Fin m) (Fin m) ℂ) (X : Matrix (Fin n) (Fin m) ℂ),
        B.trace = 0 → X ∈ S → X * B ∈ S) →
      S = ⊥ ∨ S = ⊤) ∧
    (∀ S : Submodule ℂ ℂ, S = ⊥ ∨ S = ⊤) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p n S ht hs
    exact OmegaMath.MatrixAdjoint.tracefree_adjoint_irreducible S ht hs
  · intro p n m S hleft hright
    exact OmegaMath.MatrixAdjoint.rectangular_irreducible S hleft hright
  · intro S
    by_cases hb : S = ⊥
    · exact Or.inl hb
    obtain ⟨z, hz, hn⟩ := (Submodule.ne_bot_iff S).mp hb
    refine Or.inr (Submodule.eq_top_iff'.mpr fun x => ?_)
    simpa [smul_eq_mul, div_mul_cancel₀ _ hn] using S.smul_mem (x / z) hz

def E (i j : Fin 5) : M5 := Matrix.single i j 1

private theorem diagonal_commutator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℂ) (M : Matrix ι ι ℂ) (i j : ι) :
    commutator (diagonal d) M i j = (d i - d j) * M i j := by
  simp [commutator, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

private theorem diag_comm_E (d : Fin 5 → ℂ) (i j : Fin 5) :
    commutator (diagonal d) (E i j) = (d i - d j) • E i j := by
  ext k l
  rw [diagonal_commutator]
  by_cases hik : i = k <;> by_cases hjl : j = l <;>
    simp [E, hik, hjl]

def adjointY (i j : Fin 5) : ℝ := hyperchargeWeights i - hyperchargeWeights j

theorem su5_adjoint_hypercharge_eigenvalues (i j : Fin 5) :
    commutator YSM (E i j) = (adjointY i j : ℂ) • E i j ∧
    adjointY i j = if i.val < 3 then (if j.val < 3 then 0 else -5/6)
      else (if j.val < 3 then 5/6 else 0) := by
  refine ⟨?_, ?_⟩
  · simpa [YSM, adjointY] using diag_comm_E (fun k => (hyperchargeWeights k : ℂ)) i j
  · fin_cases i <;> fin_cases j <;> norm_num [adjointY, hyperchargeWeights]

theorem su5_leptoquark_electric_charges (i : Fin 3) :
    commutator Qem (E (i.castAdd 2) 3) = (-4/3 : ℂ) • E (i.castAdd 2) 3 ∧
    commutator Qem (E (i.castAdd 2) 4) = (-1/3 : ℂ) • E (i.castAdd 2) 4 ∧
    commutator Qem (E 3 (i.castAdd 2)) = (4/3 : ℂ) • E 3 (i.castAdd 2) ∧
    commutator Qem (E 4 (i.castAdd 2)) = (1/3 : ℂ) • E 4 (i.castAdd 2) := by
  rw [su5_electric_charge_traceless.1]
  simp only [diag_comm_E]
  fin_cases i <;> norm_num

/-- The ordered wedge coordinates, beginning with the color and weak pairs. -/
def wedgePair : Fin 10 → Fin 5 × Fin 5 :=
  ![(0,3), (0,4), (1,3), (1,4), (2,3), (2,4), (0,1), (0,2), (1,2), (3,4)]

private theorem wedgePair_lt (k : Fin 10) : (wedgePair k).1 < (wedgePair k).2 := by
  fin_cases k <;> decide

private theorem wedgePair_injective : Function.Injective wedgePair := by
  intro a b
  fin_cases a <;> fin_cases b <;> decide

/-- The ten ordered pair coordinates enumerate the exterior basis. -/
def wedgePairEquiv : Fin 10 ≃ {ij : Fin 5 × Fin 5 // ij.1 < ij.2} :=
  Equiv.ofBijective (fun k => ⟨wedgePair k, wedgePair_lt k⟩)
    ⟨fun _ _ h => wedgePair_injective (congrArg Subtype.val h), by
      rintro ⟨⟨i, j⟩, hij⟩
      have h : ∃ k, wedgePair k = (i, j) := by
        revert hij
        fin_cases i <;> fin_cases j <;> decide
      obtain ⟨k, hk⟩ := h
      exact ⟨k, Subtype.ext hk⟩⟩

def dualAction (M : M5) : M5 := -Mᵀ

private def delta (i j : Fin 5) : ℂ := if i = j then 1 else 0

/-- The infinitesimal action on the second exterior power in the ordered wedge basis. -/
def exteriorAction (M : M5) : Matrix (Fin 10) (Fin 10) ℂ := Matrix.of fun a b =>
  let (i, j) := wedgePair a
  let (k, l) := wedgePair b
  M i k * delta j l - M j k * delta i l +
    M j l * delta i k - M i l * delta j k

/-- Coordinates of a decomposable two-vector, in increasing pair orientation. -/
def wedgeCoords (u v : Fin 5 → ℂ) : Fin 10 → ℂ :=
  fun a => u (wedgePair a).1 * v (wedgePair a).2 - u (wedgePair a).2 * v (wedgePair a).1

/-- The infinitesimal action is the exterior-product rule on decomposable vectors. -/
theorem su5_exterior_product_rule (M : M5) (u v : Fin 5 → ℂ) :
    exteriorAction M *ᵥ wedgeCoords u v =
      wedgeCoords (M *ᵥ u) v + wedgeCoords u (M *ᵥ v) := by
  funext a
  fin_cases a <;>
    simp [exteriorAction, wedgeCoords, wedgePair, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, delta, Fin.ext_iff] <;> ring

def dualWeight (h : Fin 5 → ℝ) (i : Fin 5) : ℝ := -h i
def exteriorWeight (h : Fin 5 → ℝ) (i : Fin 10) : ℝ :=
  h (wedgePair i).1 + h (wedgePair i).2

theorem su5_fermion_weight_actions (d : Fin 5 → ℂ) :
    dualAction (diagonal d) = diagonal (fun i => -d i) ∧
    exteriorAction (diagonal d) =
      diagonal (fun k => d (wedgePair k).1 + d (wedgePair k).2) := by
  refine ⟨by simp [dualAction, Matrix.diagonal_neg], ?_⟩
  ext a b
  rcases ha : wedgePair a with ⟨i, j⟩
  rcases hb : wedgePair b with ⟨k, l⟩
  have hij := wedgePair_lt a
  have hkl := wedgePair_lt b
  rw [ha] at hij
  rw [hb] at hkl
  have hdiag : a = b ↔ i = k ∧ j = l := by
    constructor
    · intro h
      rw [h, hb] at ha
      exact Prod.mk.inj ha.symm
    · rintro ⟨rfl, rfl⟩
      exact wedgePair_injective (ha.trans hb.symm)
  have hcross : ¬(j = k ∧ i = l) := by
    rintro ⟨rfl, rfl⟩
    exact (not_lt_of_gt hij) hkl
  simp only [exteriorAction, ha, hb, Matrix.of_apply, Matrix.diagonal_apply, delta, hdiag]
  split_ifs <;> simp_all

def fermionWeight (h : Fin 5 → ℝ) : Fin 15 → ℝ :=
  ![exteriorWeight h 0, exteriorWeight h 1, exteriorWeight h 2, exteriorWeight h 3,
    exteriorWeight h 4, exteriorWeight h 5, exteriorWeight h 6, exteriorWeight h 7,
    exteriorWeight h 8, dualWeight h 0, dualWeight h 1, dualWeight h 2,
    dualWeight h 4, dualWeight h 3, exteriorWeight h 9]

theorem su5_bar5_plus_10_dim :
    Module.finrank ℂ ((Fin 5 ⊕ Fin 10) → ℂ) = 15 := by
  simp

open GaugeUnificationRG4D in
theorem su5_bar5_plus_10_matches_sm_hypercharges :
    fermionWeight hyperchargeWeights = sm15Y ∧
    fermionWeight weakWeights = sm15T3 ∧
    (∑ i, fermionWeight hyperchargeWeights i) = 0 ∧
    (∑ i, (fermionWeight hyperchargeWeights i)^3) = 0 ∧
    (∑ i, (fermionWeight hyperchargeWeights i)^2) = 10/3 ∧
    2 * fermionWeight hyperchargeWeights 0 + fermionWeight hyperchargeWeights 6 +
      fermionWeight hyperchargeWeights 9 = 0 ∧
    3 * fermionWeight hyperchargeWeights 0 + fermionWeight hyperchargeWeights 12 = 0 := by
  have hy : fermionWeight hyperchargeWeights = sm15Y := by
    funext i
    fin_cases i <;>
      norm_num [fermionWeight, exteriorWeight, dualWeight, wedgePair, hyperchargeWeights,
        sm15Y, sm15State, weylY]
  have hw : fermionWeight weakWeights = sm15T3 := by
    funext i
    fin_cases i <;>
      dsimp [sm15T3, sm15State, weylT3, Matrix.cons_val_zero, Matrix.cons_val_succ] <;>
      norm_num [fermionWeight, exteriorWeight, dualWeight, wedgePair, weakWeights]
  refine ⟨hy, hw, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hy]; exact sm15_trace_Y
  · rw [hy]; exact sm15_trace_Y_cube
  · rw [hy]; exact sm15_trace_Y_sq
  · norm_num [fermionWeight, exteriorWeight, dualWeight, wedgePair, hyperchargeWeights]
  · norm_num [fermionWeight, exteriorWeight, dualWeight, wedgePair, hyperchargeWeights]

theorem suN_antisym_cubic_anomaly (N : ℕ) (h : Fin N → ℝ) (hh : ∑ i, h i = 0) :
    (∑ i, ∑ j, if i < j then (h i + h j) ^ 3 else 0) =
      ((N : ℝ) - 4) * ∑ i, h i ^ 3 := by
  change OmegaMath.ExteriorSquareTrace.pairCubes h = _
  rw [OmegaMath.ExteriorSquareTrace.pairCubes_eq, hh]
  ring

theorem su5_cubic_anomaly_cancellation (h : Fin 5 → ℝ) (hh : ∑ i, h i = 0) :
    (∑ i, exteriorWeight h i ^ 3) = ∑ i, h i ^ 3 ∧
    (∑ i, dualWeight h i ^ 3) = -(∑ i, h i ^ 3) ∧
    (∑ i, exteriorWeight h i ^ 3) + (∑ i, dualWeight h i ^ 3) = 0 := by
  have hw : (∑ i, exteriorWeight h i ^ 3) = ∑ i, h i ^ 3 := by
    let e : Fin 10 ↪ Fin 5 × Fin 5 := ⟨wedgePair, wedgePair_injective⟩
    have hs : Finset.univ.map e = Finset.univ.filter
        (fun p : Fin 5 × Fin 5 => p.1 < p.2) := by decide
    have hp : (∑ p ∈ Finset.univ.map e, (h p.1 + h p.2)^3) =
        ∑ i, exteriorWeight h i ^ 3 := by
      rw [Finset.sum_map]
      rfl
    rw [hs, Finset.sum_filter, Fintype.sum_prod_type] at hp
    rw [← hp, suN_antisym_cubic_anomaly 5 h hh]
    norm_num
  have hd : (∑ i, dualWeight h i ^ 3) = -(∑ i, h i ^ 3) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold dualWeight
    ring
  exact ⟨hw, hd, by rw [hw, hd]; ring⟩

def dualBMinusL (i : Fin 5) : ℝ := (-3 + 4 * dualWeight hyperchargeWeights i) / 5
def exteriorBMinusL (a : Fin 10) : ℝ := (1 + 4 * exteriorWeight hyperchargeWeights a) / 5
def adjointBMinusL (i j : Fin 5) : ℝ := 4 * adjointY i j / 5

private theorem dual_b_minus_l_vertex (i j a b : Fin 5) :
    ((dualBMinusL a - dualBMinusL b - adjointBMinusL i j : ℝ) : ℂ) *
      dualAction (E i j) a b = 0 := by
  simp only [dualAction, E, Matrix.neg_apply, Matrix.transpose_apply, Matrix.single_apply]
  by_cases ha : i = b <;> by_cases hb : j = a <;> simp [ha, hb]
  subst b
  subst a
  unfold dualBMinusL dualWeight adjointBMinusL adjointY
  push_cast
  ring

private theorem exterior_b_minus_l_vertex (i j : Fin 5) (a b : Fin 10) :
    ((exteriorBMinusL a - exteriorBMinusL b - adjointBMinusL i j : ℝ) : ℂ) *
      exteriorAction (E i j) a b = 0 := by
  rcases ha : wedgePair a with ⟨p, q⟩
  rcases hb : wedgePair b with ⟨r, s⟩
  let c : ℂ := ((exteriorBMinusL a - exteriorBMinusL b - adjointBMinusL i j : ℝ) : ℂ)
  change c * exteriorAction (E i j) a b = 0
  have hc (h : hyperchargeWeights p + hyperchargeWeights q -
      (hyperchargeWeights r + hyperchargeWeights s) = hyperchargeWeights i - hyperchargeWeights j) :
      c = 0 := by
    dsimp [c, exteriorBMinusL, exteriorWeight, adjointBMinusL, adjointY]
    rw [show (wedgePair a).1 = p from congrArg Prod.fst ha,
      show (wedgePair a).2 = q from congrArg Prod.snd ha,
      show (wedgePair b).1 = r from congrArg Prod.fst hb,
      show (wedgePair b).2 = s from congrArg Prod.snd hb]
    have hz : (1 + 4 * (hyperchargeWeights p + hyperchargeWeights q)) / 5 -
        (1 + 4 * (hyperchargeWeights r + hyperchargeWeights s)) / 5 -
        4 * (hyperchargeWeights i - hyperchargeWeights j) / 5 = 0 := by linarith
    rw [hz, Complex.ofReal_zero]
  simp only [exteriorAction, ha, hb, Matrix.of_apply, E, Matrix.single_apply, delta,
    mul_add, mul_sub, ← mul_assoc]
  have h1 : c * (if i = p ∧ j = r then 1 else 0) * (if q = s then 1 else 0) = 0 := by
    split_ifs with h₁ h₂
    · rcases h₁ with ⟨rfl, rfl⟩
      subst s
      rw [hc (by ring)]
      simp
    all_goals simp
  have h2 : c * (if i = q ∧ j = r then 1 else 0) * (if p = s then 1 else 0) = 0 := by
    split_ifs with h₁ h₂
    · rcases h₁ with ⟨rfl, rfl⟩
      subst s
      rw [hc (by ring)]
      simp
    all_goals simp
  have h3 : c * (if i = q ∧ j = s then 1 else 0) * (if p = r then 1 else 0) = 0 := by
    split_ifs with h₁ h₂
    · rcases h₁ with ⟨rfl, rfl⟩
      subst r
      rw [hc (by ring)]
      simp
    all_goals simp
  have h4 : c * (if i = p ∧ j = s then 1 else 0) * (if q = r then 1 else 0) = 0 := by
    split_ifs with h₁ h₂
    · rcases h₁ with ⟨rfl, rfl⟩
      subst r
      rw [hc (by ring)]
      simp
    all_goals simp
  rw [h1, h2, h3, h4]
  simp

/-- The boson charge equals the difference of the outgoing and incoming
fermion charges at every nonzero matrix element of either action. -/
theorem su5_b_minus_l_conserved (i j : Fin 5) :
    (∀ a b : Fin 5, dualAction (E i j) a b ≠ 0 →
      dualBMinusL a = dualBMinusL b + adjointBMinusL i j) ∧
    (∀ a b : Fin 10, exteriorAction (E i j) a b ≠ 0 →
      exteriorBMinusL a = exteriorBMinusL b + adjointBMinusL i j) := by
  constructor <;> intro a b h
  · have hz := (mul_eq_zero.mp (dual_b_minus_l_vertex i j a b)).resolve_right h
    exact sub_eq_zero.mp (by
      have hz' := Complex.ofReal_injective (hz.trans Complex.ofReal_zero.symm)
      linarith)
  · have hz := (mul_eq_zero.mp (exterior_b_minus_l_vertex i j a b)).resolve_right h
    exact sub_eq_zero.mp (by
      have hz' := Complex.ofReal_injective (hz.trans Complex.ofReal_zero.symm)
      linarith)

/-- Complex realification embeds the special unitary group in real dimension ten. -/
abbrev su5ToSo10 := OmegaMath.ComplexRealification.specialUnitaryToSpecialOrthogonalFin 5

theorem su5_to_so10_injective : Function.Injective su5ToSo10 :=
  OmegaMath.ComplexRealification.specialUnitaryToSpecialOrthogonalFin_injective 5

open OmegaMath.SpinorWeights5 in
theorem so10_su5_fermion_branching (h : Fin 5 → ℝ) (hh : ∑ i, h i = 0) :
    (fun i => cartan h (evenWeight i).1) = Fin.cons 0 (fermionWeight h) := by
  rw [so10_su5_cartan_restriction h hh]
  funext i
  fin_cases i <;> rfl

open OmegaMath.SpinorWeights5 in
theorem so10_su5_b_minus_l_compatibility :
    (fun i => bMinusL (evenWeight i).1) =
      ![1, exteriorBMinusL 0, exteriorBMinusL 1, exteriorBMinusL 2, exteriorBMinusL 3,
        exteriorBMinusL 4, exteriorBMinusL 5, exteriorBMinusL 6, exteriorBMinusL 7,
        exteriorBMinusL 8, dualBMinusL 0, dualBMinusL 1, dualBMinusL 2, dualBMinusL 4,
        dualBMinusL 3, exteriorBMinusL 9] := by
  funext i
  have hi := congrArg Prod.fst (congrFun so10_all_16_fermion_quantum_numbers i)
  fin_cases i <;> norm_num [dualBMinusL, exteriorBMinusL, dualWeight, exteriorWeight,
    wedgePair, hyperchargeWeights] at hi ⊢ <;> linarith

end D5.S3.Quantum.Gauge.SU5SO10GrandUnification4D
