/- GID: D5/S3/Quantum/Gauge/PatiSalamUnification4D
   generality: G
   mirror-B: D5/B/S3/Quantum/Gauge/PatiSalamUnification4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pati–Salam adjoint branching, chiral fermion weights, and compact group covers. -/

import OmegaBuild.Commands
import OmegaMath.Geometry.SU4SO6Cover
import OmegaMath.Geometry.SU2xSU2SO4Cover
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Reindex
import D5.S3.Quantum.Gauge.SU5SO10GrandUnification4D

/-! The fourth color is the lepton coordinate. The adjoint branching uses
complexified generators, and the compact Lie algebra uses skew-Hermitian matrices. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped Matrix

namespace D5.S3.Quantum.Gauge.PatiSalamUnification4D

open SU5SO10GrandUnification4D (TraceFree)

local notation "bracket" => SU5SO10GrandUnification4D.commutator

abbrev M3 := Matrix (Fin 3) (Fin 3) ℂ
abbrev M4 := Matrix (Fin 4) (Fin 4) ℂ
abbrev ColorColumn := Matrix (Fin 3) (Fin 1) ℂ
abbrev ColorRow := Matrix (Fin 1) (Fin 3) ℂ

private abbrev partition : Fin 3 ⊕ Fin 1 ≃ Fin 4 := finSumFinEquiv

def bMinusLGen : M4 := diagonal ![1 / 3, 1 / 3, 1 / 3, -1]

def t15Gen : M4 := Real.sqrt (3 / 8) • bMinusLGen

theorem su4_bMinusL_traceless_and_norm :
    bMinusLGen.trace = 0 ∧ (bMinusLGen * bMinusLGen).trace = 4 / 3 ∧
      (t15Gen * t15Gen).trace = 1 / 2 := by
  have hn : (bMinusLGen * bMinusLGen).trace = 4 / 3 := by
    rw [bMinusLGen, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    norm_num [Fin.sum_univ_succ]
  refine ⟨by norm_num [bMinusLGen, Fin.sum_univ_succ], hn, ?_⟩
  have hs : ((Real.sqrt (3 / 8) : ℝ) : ℂ) ^ 2 = 3 / 8 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3 / 8)]
    norm_num
  rw [show t15Gen = (Real.sqrt (3 / 8) : ℂ) • bMinusLGen by
    ext i j
    simp [t15Gen, Complex.real_smul, smul_eq_mul]]
  rw [← pow_two, smul_pow, Matrix.trace_smul, pow_two bMinusLGen, hn, hs]
  norm_num [smul_eq_mul]

/-- The coordinates are a trace-zero color matrix, the B minus L coefficient,
and the two off-diagonal color representations. -/
def adjointBlocks (A : M3) (t : ℂ) (C : ColorColumn) (D : ColorRow) : M4 :=
  reindex partition partition
    (fromBlocks (A + (t / 3) • (1 : M3)) C D ((-t) • (1 : Matrix (Fin 1) (Fin 1) ℂ)))

def colorBlock (A : M3) : M4 := adjointBlocks A 0 0 0

private theorem bMinusL_blocks : bMinusLGen = adjointBlocks 0 1 0 0 := by
  ext i j
  obtain ⟨i, rfl⟩ := partition.surjective i
  obtain ⟨j, rfl⟩ := partition.surjective j
  simp only [adjointBlocks, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [bMinusLGen, Matrix.diagonal,
      Matrix.one_apply, Matrix.smul_apply, finSumFinEquiv, Fin.castAdd, Fin.castLE, Fin.natAdd,
      Fin.ext_iff]

private theorem trace_reindex_blocks (A : M3) (C : ColorColumn) (D : ColorRow)
    (F : Matrix (Fin 1) (Fin 1) ℂ) :
    (reindex partition partition (fromBlocks A C D F)).trace = A.trace + F.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [partition.symm.sum_comp (fun i : Fin 3 ⊕ Fin 1 => fromBlocks A C D F i i)]
  simp [Fintype.sum_sum_type]

private theorem color_trace_shift (A : M3) (t : ℂ) :
    (A + (t / 3) • (1 : M3)).trace = A.trace + t := by
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one]
  norm_num [smul_eq_mul]

private theorem blocks_trace (A : M3) (t : ℂ) (C : ColorColumn) (D : ColorRow) :
    (adjointBlocks A t C D).trace = A.trace := by
  rw [adjointBlocks, trace_reindex_blocks, color_trace_shift, Matrix.trace_smul,
    Matrix.trace_one]
  norm_num [smul_eq_mul]

/-- The complexification has four uniquely determined coordinates. -/
theorem su4_adjoint_decomposition (M : M4) (hM : M.trace = 0) :
    (∃! p : M3 × ℂ × ColorColumn × ColorRow,
      p.1.trace = 0 ∧ adjointBlocks p.1 p.2.1 p.2.2.1 p.2.2.2 = M) ∧
    Module.finrank ℂ (TraceFree 4) = 15 ∧ Module.finrank ℂ (TraceFree 3) = 8 ∧
    Module.finrank ℂ ℂ = 1 ∧ Module.finrank ℂ ColorColumn = 3 ∧
    Module.finrank ℂ ColorRow = 3 := by
  have h4 := (Matrix.traceLinearMap (n := Fin 4) ℂ ℂ).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr Matrix.trace_surjective, finrank_top, Module.finrank_matrix] at h4
  norm_num at h4
  change 1 + Module.finrank ℂ (TraceFree 4) = 1 + 15 at h4
  refine ⟨?_, Nat.add_left_cancel h4,
    SU5SO10GrandUnification4D.su5_adjoint_dimensions.2.1, ?_, ?_, ?_⟩
  · let N := reindex partition.symm partition.symm M
    have hN : reindex partition partition N = M :=
      (reindex partition partition).apply_symm_apply M
    have htr : N.toBlocks₁₁.trace + N.toBlocks₂₂.trace = 0 := by
      rw [← trace_reindex_blocks N.toBlocks₁₁ N.toBlocks₁₂ N.toBlocks₂₁ N.toBlocks₂₂,
        Matrix.fromBlocks_toBlocks, hN, hM]
    let t := -N.toBlocks₂₂.trace
    let A := N.toBlocks₁₁ - (t / 3) • (1 : M3)
    have hA : A.trace = 0 := by
      simp [A, t, Matrix.trace_sub, smul_eq_mul]
      linear_combination htr
    have hLast : (-t) • (1 : Matrix (Fin 1) (Fin 1) ℂ) = N.toBlocks₂₂ := by
      ext i j
      have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      subst i j
      simp [t, Matrix.trace, Matrix.smul_apply]
    have hrep : adjointBlocks A t N.toBlocks₁₂ N.toBlocks₂₁ = M := by
      simpa only [adjointBlocks, A, sub_add_cancel, hLast, Matrix.fromBlocks_toBlocks] using hN
    refine ⟨⟨A, t, N.toBlocks₁₂, N.toBlocks₂₁⟩, ⟨hA, hrep⟩, ?_⟩
    rintro ⟨A', t', C', D'⟩ ⟨hA', hrep'⟩
    obtain ⟨hc, hC, hD, _⟩ := Matrix.fromBlocks_inj.mp
      ((reindex partition partition).injective (hrep'.trans hrep.symm))
    have ht : t' = t := by
      have ht := congrArg Matrix.trace hc
      rwa [color_trace_shift, color_trace_shift, hA', hA, zero_add, zero_add] at ht
    subst t'
    exact Prod.ext (add_right_cancel hc) (Prod.ext rfl (Prod.ext hC hD))
  all_goals simp [Module.finrank_matrix]

private theorem adjoint_blocks_injective {A A' : M3} {t t' : ℂ}
    (h : adjointBlocks A t 0 0 = adjointBlocks A' t' 0 0) :
    A = A' ∧ t = t' := by
  obtain ⟨h₁₁, _, _, h₂₂⟩ := Matrix.fromBlocks_inj.mp ((reindex partition partition).injective h)
  have ht : t = t' := by
    have hd := congrArg Matrix.trace h₂₂
    simpa [Matrix.trace_smul, smul_eq_mul] using hd
  subst t'
  exact ⟨add_right_cancel h₁₁, rfl⟩

private theorem adjoint_block_action (A B : M3) (t z : ℂ)
    (C : ColorColumn) (D : ColorRow) :
    bracket (adjointBlocks A t 0 0) (adjointBlocks B z C D) =
      adjointBlocks (bracket A B) 0 (A * C + ((4 / 3 : ℂ) * t) • C)
        (-(D * A) - ((4 / 3 : ℂ) * t) • D) := by
  let e := Matrix.reindexAlgEquiv ℂ ℂ partition
  unfold adjointBlocks SU5SO10GrandUnification4D.commutator
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
    simp [Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    module
  · rw [← sub_eq_add_neg]
    simp [Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul]
    module
  · rw [← sub_eq_add_neg]
    simp [smul_smul, mul_comm t z]

theorem su4_sm_subalgebra_commute (A : M3) :
    Commute (colorBlock A) bMinusLGen ∧ Commute (colorBlock A) t15Gen := by
  have h : Commute (colorBlock A) bMinusLGen := by
    apply sub_eq_zero.mp
    change bracket (colorBlock A) bMinusLGen = 0
    rw [colorBlock, bMinusL_blocks, adjoint_block_action]
    simp [SU5SO10GrandUnification4D.commutator, adjointBlocks]
  exact ⟨h, h.smul_right _⟩

/-- The compact real form uses the skew-Hermitian generator i times B minus L. -/
def smEmbedding (A : M3) (s : ℝ) : M4 := adjointBlocks A ((s : ℂ) * Complex.I) 0 0

private theorem real_matrix_smul {n m : Type*} (r : ℝ) (M : Matrix n m ℂ) :
    r • M = (r : ℂ) • M := by
  ext i j
  simp [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]

theorem su4_sm_embedding (A B : M3) (s t : ℝ) :
    (A.trace = 0 → Aᴴ = -A → (smEmbedding A s).trace = 0 ∧
      (smEmbedding A s)ᴴ = -(smEmbedding A s)) ∧
    (smEmbedding A s = smEmbedding B t ↔ A = B ∧ s = t) ∧
    bracket (smEmbedding A s) (smEmbedding B t) = smEmbedding (bracket A B) 0 ∧
    smEmbedding (A + B) (s + t) = smEmbedding A s + smEmbedding B t ∧
    (∀ k : ℝ, smEmbedding (k • A) (k * s) = k • smEmbedding A s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro htrace hskew
    refine ⟨(blocks_trace _ _ _ _).trans htrace, ?_⟩
    have hconj : star ((s : ℂ) * Complex.I) = -((s : ℂ) * Complex.I) := by simp
    let z : ℂ := (s : ℂ) * Complex.I
    let N := fromBlocks (A + (z / 3) • (1 : M3)) (0 : ColorColumn) (0 : ColorRow)
      ((-z) • (1 : Matrix (Fin 1) (Fin 1) ℂ))
    change (N.submatrix partition.symm partition.symm)ᴴ = _
    rw [Matrix.conjTranspose_submatrix]
    change Nᴴ.submatrix partition.symm partition.symm =
      (-N).submatrix partition.symm partition.symm
    congr 1
    dsimp only [N, z]
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_neg]
    simp [hskew, hconj, neg_div, add_comm]
  · constructor
    · intro h
      obtain ⟨hAB, hst⟩ := adjoint_blocks_injective h
      exact ⟨hAB, Complex.ofReal_injective (mul_right_cancel₀ Complex.I_ne_zero hst)⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  · simp [smEmbedding, adjoint_block_action]
  · let e := Matrix.reindexAlgEquiv ℂ ℂ partition
    unfold smEmbedding adjointBlocks
    change e _ = e _ + e _
    rw [← map_add, Matrix.fromBlocks_add]
    apply congrArg e
    rw [Matrix.fromBlocks_inj]
    simp [Complex.ofReal_add, add_mul, add_div, add_smul]
    abel_nf
    simp
  · intro k
    let e := Matrix.reindexAlgEquiv ℂ ℂ partition
    rw [real_matrix_smul k A, real_matrix_smul k (smEmbedding A s)]
    unfold smEmbedding adjointBlocks
    change e _ = (k : ℂ) • e _
    rw [← map_smul, Matrix.fromBlocks_smul]
    simp [Complex.ofReal_mul, smul_add, smul_smul, ← mul_assoc, mul_div_assoc]

theorem su4_adjoint_leptoquark_bMinusL (A : M3) (t : ℂ) (C : ColorColumn) (D : ColorRow) :
    bracket bMinusLGen (adjointBlocks A t C D) =
      adjointBlocks 0 0 ((4 / 3 : ℂ) • C) ((-4 / 3 : ℂ) • D) := by
  rw [bMinusL_blocks, adjoint_block_action]
  simp [SU5SO10GrandUnification4D.commutator, neg_div, ← neg_smul]

/-- Invariance for each non-scalar summand is with respect to the color action. -/
theorem su4_adjoint_blocks_irreducible :
    (∀ S : Submodule ℂ M3, (∀ A ∈ S, A.trace = 0) →
      (∀ A B : M3, A.trace = 0 → B ∈ S → bracket A B ∈ S) →
      S = ⊥ ∨ ∀ A : M3, A.trace = 0 → A ∈ S) ∧
    (∀ S : Submodule ℂ ℂ, S = ⊥ ∨ S = ⊤) ∧
    (∀ S : Submodule ℂ ColorColumn,
      (∀ (A : M3) (C : ColorColumn), A.trace = 0 → C ∈ S → A * C ∈ S) →
      S = ⊥ ∨ S = ⊤) ∧
    (∀ S : Submodule ℂ ColorRow,
      (∀ (D : ColorRow) (A : M3), A.trace = 0 → D ∈ S → D * A ∈ S) →
      S = ⊥ ∨ S = ⊤) := by
  refine ⟨OmegaMath.MatrixAdjoint.tracefree_adjoint_irreducible, ?_, ?_, ?_⟩
  · intro S
    by_cases hb : S = ⊥
    · exact Or.inl hb
    obtain ⟨z, hz, hn⟩ := (Submodule.ne_bot_iff S).mp hb
    refine Or.inr (Submodule.eq_top_iff'.mpr fun x => ?_)
    simpa [smul_eq_mul, div_mul_cancel₀ _ hn] using S.smul_mem (x / z) hz
  · intro S h
    refine OmegaMath.MatrixAdjoint.rectangular_irreducible S h ?_
    intro B C hB hC
    have hzero : B = 0 := by
      ext i j
      fin_cases i
      fin_cases j
      simpa [Matrix.trace, Fin.sum_univ_one] using hB
    simp [hzero]
  · intro S h
    refine OmegaMath.MatrixAdjoint.rectangular_irreducible S ?_ (fun A D hA hD => h D A hA hD)
    intro B D hB hD
    have hzero : B = 0 := by
      ext i j
      fin_cases i
      fin_cases j
      simpa [Matrix.trace, Fin.sum_univ_one] using hB
    simp [hzero]

abbrev PSState := (Fin 4 × Fin 2) ⊕ (Fin 4 × Fin 2)

def ps16Index : PSState ≃ Fin 16 :=
  (Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv

private def weakWeight : Fin 2 → ℝ := ![1 / 2, -1 / 2]
private def colorWeight : Fin 4 → ℝ := ![1 / 3, 1 / 3, 1 / 3, -1]

def psT3L : PSState → ℝ
  | .inl (_, i) => weakWeight i
  | .inr _ => 0

def psT3R : PSState → ℝ
  | .inl _ => 0
  | .inr (_, i) => weakWeight i

def psBMinusL : PSState → ℝ
  | .inl (c, _) => colorWeight c
  | .inr (c, _) => -colorWeight c

def psHypercharge (x : PSState) : ℝ := psT3R x + psBMinusL x / 2
def psElectricCharge (x : PSState) : ℝ := psT3L x + psHypercharge x

theorem ps16_left_right_dims :
    Fintype.card (Fin 4 × Fin 2) = 8 ∧ Fintype.card PSState = 8 + 8 ∧
    (∀ x : PSState, psT3L x ≠ 0 ↔ psT3R x = 0) := by
  refine ⟨by simp, by simp, ?_⟩
  rintro (⟨_, i⟩ | ⟨_, i⟩) <;> fin_cases i <;> norm_num [psT3L, psT3R, weakWeight]

theorem ps16_anomalies_vanish :
    (∑ x : PSState, psT3L x) = 0 ∧ (∑ x : PSState, psT3R x) = 0 ∧
    (∑ x : PSState, psBMinusL x) = 0 ∧ (∑ x : PSState, psHypercharge x) = 0 ∧
    (∑ x : PSState, psElectricCharge x) = 0 ∧
    (∑ x : PSState, psT3L x ^ 2 * psBMinusL x) = 0 ∧
    (∑ x : PSState, psT3R x ^ 2 * psBMinusL x) = 0 ∧
    (∑ x : PSState, psBMinusL x ^ 3) = 0 ∧ (∑ x : PSState, psHypercharge x ^ 3) = 0 ∧
    (∑ x : PSState, psT3L x * psHypercharge x) = 0 ∧
    (∀ l r b : ℝ, (∑ x : PSState, (l * psT3L x + r * psT3R x + b * psBMinusL x) ^ 3) = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_succ, psT3L, weakWeight]
  · norm_num [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_succ, psT3R, weakWeight]
  case refine_11 =>
    intro l r b
    norm_num [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_succ, psT3L, psT3R,
      psBMinusL, weakWeight, colorWeight]
    ring
  all_goals
    norm_num [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_succ, psT3L, psT3R,
      psBMinusL, psHypercharge, psElectricCharge, weakWeight, colorWeight]

/-- Positive physical couplings are expressed in terms of their inverses. -/
def psHyperchargeCoupling (αR αC : ℝ) : ℝ := (αR⁻¹ + (2 / 3 : ℝ) * αC⁻¹)⁻¹

def psNormalizedHyperchargeCoupling (αR αC : ℝ) : ℝ :=
  (5 / 3 : ℝ) * psHyperchargeCoupling αR αC

theorem ps16_traces_and_gut_matching :
    (∑ x : PSState, psT3L x ^ 2) = 2 ∧ (∑ x : PSState, psT3R x ^ 2) = 2 ∧
    (∑ x : PSState, (psBMinusL x / 2) ^ 2) = 4 / 3 ∧
    (∑ x : PSState, psHypercharge x ^ 2) = 10 / 3 ∧
    (∑ x : PSState, psElectricCharge x ^ 2) = 16 / 3 ∧
    (∀ αR αC : ℝ, (psHyperchargeCoupling αR αC)⁻¹ = αR⁻¹ + (2 / 3 : ℝ) * αC⁻¹ ∧
      (psNormalizedHyperchargeCoupling αR αC)⁻¹ =
        (3 / 5 : ℝ) * αR⁻¹ + (2 / 5 : ℝ) * αC⁻¹) ∧
    (∀ αL αR αC : ℝ, 0 < αL → αL = αR → αR = αC →
      psNormalizedHyperchargeCoupling αR αC = αL ∧ αL = αC ∧
      psHyperchargeCoupling αR αC / (αL + psHyperchargeCoupling αR αC) = 3 / 8) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  case refine_6 =>
    intro αR αC
    refine ⟨inv_inv _, ?_⟩
    simp [psNormalizedHyperchargeCoupling, psHyperchargeCoupling, _root_.mul_inv_rev]
    ring
  case refine_7 =>
    rintro αL _ _ hα rfl rfl
    have hY : psHyperchargeCoupling αL αL = (3 / 5 : ℝ) * αL := by
      rw [psHyperchargeCoupling, show αL⁻¹ + 2 / 3 * αL⁻¹ = (5 / 3) * αL⁻¹ by ring]
      norm_num [_root_.mul_inv_rev]
      ring
    refine ⟨?_, rfl, ?_⟩
    · rw [psNormalizedHyperchargeCoupling, hY]
      ring
    · rw [hY]
      field_simp [hα.ne', show αL + 3 / 5 * αL ≠ 0 by positivity]
      ring
  all_goals
    norm_num [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_succ, psT3L, psT3R,
      psBMinusL, psHypercharge, psElectricCharge, weakWeight, colorWeight]

private def halfSpinIndex : Fin 16 → Fin 16 :=
  ![1, 2, 3, 4, 5, 6, 13, 14, 10, 9, 11, 8, 12, 7, 15, 0]

/-- Anti-colors record the missing color in a pair of occupied color coordinates. -/
def ps16ToSpinor : PSState ≃ OmegaMath.SpinorWeights5.EvenWeight :=
  ps16Index.trans
    ((Equiv.ofBijective halfSpinIndex ⟨by decide, by decide⟩).trans
      OmegaMath.SpinorWeights5.evenWeight)

open OmegaMath.SpinorWeights5 in
theorem ps16_matches_so10_spinor16 (x : PSState) :
    let w := (ps16ToSpinor x).1
    psT3L x = t3L w ∧ psT3R x = t3R w ∧ psBMinusL x = bMinusL w ∧
      psHypercharge x = hypercharge w ∧ psElectricCharge x = electricCharge w := by
  have h := congrFun so10_all_16_fermion_quantum_numbers (halfSpinIndex (ps16Index x))
  change (bMinusL (ps16ToSpinor x).1, t3L (ps16ToSpinor x).1, t3R (ps16ToSpinor x).1,
    hypercharge (ps16ToSpinor x).1, electricCharge (ps16ToSpinor x).1) = _ at h
  dsimp only
  rw [Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
  obtain ⟨hb, hl, hr, hy, hq⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals
    first | rw [hb] | rw [hl] | rw [hr] | rw [hy] | rw [hq]
    rcases x with ⟨c, i⟩ | ⟨c, i⟩ <;> fin_cases c <;> fin_cases i <;>
      norm_num [ps16Index, finProdFinEquiv, finSumFinEquiv, Fin.castAdd, Fin.castLE, Fin.natAdd,
        halfSpinIndex, psT3L, psT3R, psBMinusL, psHypercharge, psElectricCharge,
        weakWeight, colorWeight]

open OmegaMath.SU4SO6Cover (SU4 so6OfSU4 so6OfSU4_one so6OfSU4_mul
  so6OfSU4_orthogonal so6OfSU4_det_one so6OfSU4_kernel)
open OmegaMath.SU2xSU2SO4Cover (SU2 su2NegOne so4OfSU2xSU2 so4OfSU2xSU2_one
  so4OfSU2xSU2_mul so4OfSU2xSU2_orthogonal so4OfSU2xSU2_det_one so4OfSU2xSU2_kernel)

abbrev SO6 := Matrix.specialOrthogonalGroup (Fin 6) ℝ
abbrev SO4 := Matrix.specialOrthogonalGroup (Fin 4) ℝ
abbrev SO10 := Matrix.specialOrthogonalGroup (Fin 10) ℝ

private def reindex10 :
    Matrix (Fin 6 ⊕ Fin 4) (Fin 6 ⊕ Fin 4) ℝ ≃+* Matrix (Fin 10) (Fin 10) ℝ :=
  Matrix.reindexRingEquiv ℝ finSumFinEquiv

private def orthogonalBlocks (A : Matrix (Fin 6) (Fin 6) ℝ)
    (B : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 10) (Fin 10) ℝ :=
  reindex10 (Matrix.fromBlocks A 0 0 B)

private theorem orthogonalBlocks_one : orthogonalBlocks 1 1 = 1 := by
  rw [orthogonalBlocks, Matrix.fromBlocks_one, map_one]

private theorem orthogonalBlocks_mul
    (A A' : Matrix (Fin 6) (Fin 6) ℝ) (B B' : Matrix (Fin 4) (Fin 4) ℝ) :
    orthogonalBlocks (A * A') (B * B') = orthogonalBlocks A B * orthogonalBlocks A' B' := by
  unfold orthogonalBlocks
  rw [← map_mul]
  simp [Matrix.fromBlocks_multiply]

private theorem orthogonalBlocks_mem {A : Matrix (Fin 6) (Fin 6) ℝ}
    {B : Matrix (Fin 4) (Fin 4) ℝ} (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 6) ℝ)
    (hB : B ∈ Matrix.specialOrthogonalGroup (Fin 4) ℝ) :
    orthogonalBlocks A B ∈ Matrix.specialOrthogonalGroup (Fin 10) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff'] at hA hB ⊢
  refine ⟨?_, ?_⟩
  · have ht : (orthogonalBlocks A B)ᵀ = orthogonalBlocks Aᵀ Bᵀ := by
      change (Matrix.reindex finSumFinEquiv finSumFinEquiv _ )ᵀ =
        Matrix.reindex finSumFinEquiv finSumFinEquiv _
      rw [Matrix.transpose_reindex, Matrix.fromBlocks_transpose, Matrix.transpose_zero,
        Matrix.transpose_zero]
    rw [ht, ← orthogonalBlocks_mul, hA.1, hB.1, orthogonalBlocks_one]
  · change (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 B)).det = 1
    rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, hA.2, hB.2, mul_one]

/-- The direct sum of the two oriented orthogonal actions on complementary coordinates. -/
def so6SO4ToSO10 : SO6 × SO4 →* SO10 where
  toFun p := ⟨orthogonalBlocks p.1.val p.2.val, orthogonalBlocks_mem p.1.property p.2.property⟩
  map_one' := Subtype.ext orthogonalBlocks_one
  map_mul' p q := Subtype.ext (orthogonalBlocks_mul p.1.val q.1.val p.2.val q.2.val)

private theorem orthogonalBlocks_inj
    {A A' : Matrix (Fin 6) (Fin 6) ℝ} {B B' : Matrix (Fin 4) (Fin 4) ℝ} :
    orthogonalBlocks A B = orthogonalBlocks A' B' ↔ A = A' ∧ B = B' := by
  unfold orthogonalBlocks
  constructor
  · intro h
    obtain ⟨hA, _, _, hB⟩ := Matrix.fromBlocks_inj.mp (reindex10.injective h)
    exact ⟨hA, hB⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem so6SO4ToSO10_injective : Function.Injective so6SO4ToSO10 := by
  intro p q hp
  have h := orthogonalBlocks_inj.mp (congrArg Subtype.val hp)
  exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)

/-- Matrix of the Pati–Salam vector action with the six color coordinates first. -/
def patiSalamToSO10 (U : SU4) (L R : SU2) : Matrix (Fin 10) (Fin 10) ℝ :=
  orthogonalBlocks (so6OfSU4 U) (so4OfSU2xSU2 L R)

theorem patiSalamToSO10_hom (U V : SU4) (L R L' R' : SU2) :
    patiSalamToSO10 (U * V) (L * L') (R * R') =
      patiSalamToSO10 U L R * patiSalamToSO10 V L' R' := by
  rw [patiSalamToSO10, so6OfSU4_mul, so4OfSU2xSU2_mul, orthogonalBlocks_mul]
  rfl

theorem patiSalamToSO10_special_orthogonal (U : SU4) (L R : SU2) :
    (patiSalamToSO10 U L R)ᵀ * patiSalamToSO10 U L R = 1 ∧
      (patiSalamToSO10 U L R).det = 1 := by
  have hA := Matrix.mem_specialOrthogonalGroup_iff.mpr
    ⟨(Matrix.mem_orthogonalGroup_iff' (Fin 6) ℝ).mpr (so6OfSU4_orthogonal U), so6OfSU4_det_one U⟩
  have hB := Matrix.mem_specialOrthogonalGroup_iff.mpr
    ⟨(Matrix.mem_orthogonalGroup_iff' (Fin 4) ℝ).mpr (so4OfSU2xSU2_orthogonal L R), so4OfSU2xSU2_det_one L R⟩
  obtain ⟨hOrthogonal, hDet⟩ := Matrix.mem_specialOrthogonalGroup_iff.mp (orthogonalBlocks_mem hA hB)
  exact ⟨(Matrix.mem_orthogonalGroup_iff' (Fin 10) ℝ).mp hOrthogonal, hDet⟩

theorem patiSalamToSO10_kernel (U : SU4) (L R : SU2) :
    patiSalamToSO10 U L R = 1 ↔
      ((U : M4) = 1 ∨ (U : M4) = -1) ∧
        ((L = 1 ∧ R = 1) ∨ (L = su2NegOne ∧ R = su2NegOne)) := by
  unfold patiSalamToSO10
  rw [← orthogonalBlocks_one, orthogonalBlocks_inj, so6OfSU4_kernel, so4OfSU2xSU2_kernel]

def patiSalamVectorHom : SU4 × SU2 × SU2 →* SO10 where
  toFun p := ⟨patiSalamToSO10 p.1 p.2.1 p.2.2, Matrix.mem_specialOrthogonalGroup_iff.mpr
    ⟨(Matrix.mem_orthogonalGroup_iff' (Fin 10) ℝ).mpr (patiSalamToSO10_special_orthogonal p.1 p.2.1 p.2.2).1,
      (patiSalamToSO10_special_orthogonal p.1 p.2.1 p.2.2).2⟩⟩
  map_one' := Subtype.ext (by
    change patiSalamToSO10 1 1 1 = 1
    rw [patiSalamToSO10, so6OfSU4_one, so4OfSU2xSU2_one, orthogonalBlocks_one])
  map_mul' p q := Subtype.ext (patiSalamToSO10_hom p.1 q.1 p.2.1 p.2.2 q.2.1 q.2.2)

/-- Quotient by the central signs acting identically on the vector representation. -/
def patiSalamQuotientToSO10 : ((SU4 × SU2 × SU2) ⧸ patiSalamVectorHom.ker) →* SO10 :=
  QuotientGroup.kerLift patiSalamVectorHom

theorem patiSalamQuotientToSO10_injective : Function.Injective patiSalamQuotientToSO10 :=
  QuotientGroup.kerLift_injective patiSalamVectorHom

end D5.S3.Quantum.Gauge.PatiSalamUnification4D
