/- GID: D5/S3/Combinatorics/Graph/EdgeComplexityWeakProductRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/EdgeComplexityWeakProductRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/EdgeComplexityWeakProductRefutation.claim; result=D5/S3/Combinatorics/Graph/EdgeComplexityWeakProductRefutation.result; claim=D5/S3/Combinatorics/Graph/EdgeComplexityWeakProductRefutation.claim
   digest: K3 times K3 refutes weak-product closure of edge-complexity equality. -/

/-
   proof_shape: result: bind-only
   escape_witness: none
   admission_basis: open-problem-resolution (#14729; Refuted)
   Direct frozen dependencies (baseline declaration statement_id):
   D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity.fourierRows
     statement_id: sha256:451e620d62dcda126e71307dec0ca40136902b9bdd0b6852af2e51e8a2a51a13
   D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity.fourierRows_gram
     statement_id: sha256:7bbcf29020b4285723d0c681b35adbac6362ca1e0f2698059905d039ec4d2379
   D5/S3/Quantum/Dynamics/PolygonalFourierCouplings.fourier
     statement_id: sha256:0706c337d65e033c10b3e874026fbc51bf5811becfd9777ca8892400ea826c21
   D5/S3/Quantum/Matrix/CartesianVariance.frobSq_eq_sum
     statement_id: sha256:41486c053d8cde79073cf7fd478d3eec15c60ab40b220c770f2f8b9d2ae6c459
   D5/S3/Quantum/Matrix/CartesianVariance.frobSq_star
     statement_id: sha256:cdf34fc009b98387be5688421838c5a62ee1d6d71ed180b7b22481da9adeadc4
   D5/S3/Quantum/Matrix/CommutatorGap.frobSq_unitary_right
     statement_id: sha256:63c2cd1b86c23c2972e5bf796750663ea1953eea0946f6abb48832ba5fa201e7
   D5/S3/StatisticalMechanics/Percolation/DirectProductCyclePathBootstrap.dirProd
     statement_id: sha256:4e00f0c64e9d082383b225b783d1e971e947f09fea65d918317ec234a59e04c5
   D5/S3/Weil/ZetaLinear/VonNeumann.normSqMatrix
     statement_id: sha256:e52dbe98c1d31846023642a54bf054704c393626b7a8169c76de496f1c932bea
   D5/S3/Weil/ZetaLinear/VonNeumann.normSqMatrix_mem_doublyStochastic_of_unitary
     statement_id: sha256:10d84d7748c4e7f110f57a63c8faf31b2da6ecba24f5cdf67b5b36281d5a0757
   D5/S3/Weil/ZetaLinear/PosIndex.frobSq
     statement_id: sha256:a1114d4731d26d6c5ef81acb0a254cdc6e0ed6e629ccb2dcf75d7faa00f4ccce
   D5/S3/Weil/ZetaLinear/PosIndex.rtrace_eq_sum_eigenvalues
     statement_id: sha256:7de56e963243100cb0d7ed9e3a63e24c1f7a82297129182e1158ce2a9aa88e58
   D5/S3/Weil/ZetaLinear/PosIndex.frobSq_hermitian_eq_sum_sq_eigenvalues
     statement_id: sha256:8517f9a9ec34b3ab0b7f30f5025ab007ce87f585c396c39fa4b953498c3fd325
   The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
-/

import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.LinearAlgebra.Matrix.Circulant
import D5.S3.Quantum.QuantumChannels.TomiyamaDiagonalKPositivity
import D5.S3.Quantum.Dynamics.PolygonalFourierCouplings
import D5.S3.Quantum.Matrix.CartesianVariance
import D5.S3.Quantum.Matrix.CommutatorGap
import D5.S3.Weil.ZetaLinear.VonNeumann
import D5.S3.StatisticalMechanics.Percolation.DirectProductCyclePathBootstrap
set_option Elab.async false
open D5.S3.Quantum.Dynamics

noncomputable section
open scoped BigOperators
namespace D5.S3.Combinatorics.Graph.EdgeComplexityWeakProductRefutation
variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

def f (G : SimpleGraph V) [DecidableRel G.Adj]
    (σ : V ≃ Fin (Fintype.card V)) : Fin (Fintype.card V) → Fin (Fintype.card V) → ℝ :=
  fun x y => if G.Adj (σ.symm x) (σ.symm y) then 1 else 0

def fhat {N : ℕ} (a : Fin N → Fin N → ℝ) (m n : Fin N) : ℂ :=
  (1 / N : ℂ) * ∑ x, ∑ y, (a x y : ℂ) *
    Complex.exp (-2 * Real.pi * Complex.I *
      ((m.val * x.val + n.val * y.val : ℕ) : ℂ) / N)

def FR {N : ℕ} (a : Fin N → Fin N → ℝ) : ℝ :=
  (∑ m, ∑ n, ‖fhat a m n‖) /
    Real.sqrt (∑ m, ∑ n, ‖fhat a m n‖ ^ 2)

def FRmin (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  Finset.univ.inf' ⟨Fintype.equivFin V, Finset.mem_univ _⟩
    (fun σ : V ≃ Fin (Fintype.card V) => FR (f G σ))

def energy (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  ∑ j, |(G.isHermitian_adjMatrix ℝ).eigenvalues j|

def size (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ := G.edgeFinset.card

def AttainsEquality (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  0 < size G ∧ FRmin G = energy G / Real.sqrt (2 * size G)

def claim : Prop := ∀ (V W : Type) [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj],
    AttainsEquality G → AttainsEquality H → AttainsEquality (D5.S3.StatisticalMechanics.Percolation.DirectProductCyclePathBootstrap.dirProd G H)

end D5.S3.Combinatorics.Graph.EdgeComplexityWeakProductRefutation

end

noncomputable section
open scoped BigOperators
open Matrix
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.Graph.EdgeComplexityWeakProductRefutation

private abbrev P3 : SimpleGraph (Fin 3 × Fin 3) := D5.S3.StatisticalMechanics.Percolation.DirectProductCyclePathBootstrap.dirProd (⊤ : SimpleGraph (Fin 3)) (⊤ : SimpleGraph (Fin 3))

private theorem k3_indicator (σ : Fin 3 ≃ Fin (Fintype.card (Fin 3))) :
    f (⊤ : SimpleGraph (Fin 3)) σ = fun x y => if x ≠ y then 1 else 0 := by
  funext x y
  simp [f, SimpleGraph.top_adj, σ.symm.injective.ne_iff]

private theorem k3_size : size (⊤ : SimpleGraph (Fin 3)) = 3 := by decide

private theorem p3_size : size P3 = 18 := by decide

private theorem p3_adj (p q : Fin 3 × Fin 3) :
    P3.Adj p q ↔ p.1 ≠ q.1 ∧ p.2 ≠ q.2 := Iff.rfl

private theorem p3_srg : (P3.adjMatrix ℝ) * (P3.adjMatrix ℝ) =
    (2 : ℝ) • (Matrix.of (fun _ _ : Fin 3 × Fin 3 => (1 : ℝ))) + (2 : ℝ) • (1 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℝ) - P3.adjMatrix ℝ := by
  ext ⟨a,b⟩ ⟨c,d⟩
  change (∑ r : Fin 3 × Fin 3,
    (if a ≠ r.1 ∧ b ≠ r.2 then (1 : ℝ) else 0) *
    (if r.1 ≠ c ∧ r.2 ≠ d then (1 : ℝ) else 0)) =
    2 * 1 + 2 * (if (a,b) = (c,d) then 1 else 0) -
    (if a ≠ c ∧ b ≠ d then 1 else 0)
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    (simp only [Fintype.sum_prod_type, Fin.sum_univ_succ]; norm_num only [Prod.mk.injEq, ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk,
      Fin.val_ofNat, not_true_eq_false, not_false_eq_true,
      true_and, false_and, and_true, and_false, if_true, if_false])

private theorem p3_labeled_srg (σ : (Fin 3 × Fin 3) ≃ Fin 9) :
    (Matrix.of (fun x y => if P3.Adj (σ.symm x) (σ.symm y) then (1 : ℝ) else 0)) *
    (Matrix.of (fun x y => if P3.Adj (σ.symm x) (σ.symm y) then (1 : ℝ) else 0)) =
    (2 : ℝ) • (Matrix.of (fun _ _ : Fin 9 => (1 : ℝ))) + (2 : ℝ) • (1 : Matrix (Fin 9) (Fin 9) ℝ) -
    (Matrix.of (fun x y => if P3.Adj (σ.symm x) (σ.symm y) then (1 : ℝ) else 0)) := by
  let T := Matrix.reindexAlgEquiv ℝ ℝ σ
  have h := congrArg T p3_srg
  simp only [map_mul, map_add, map_sub, map_smul, map_one] at h
  have hTA : T (P3.adjMatrix ℝ) = Matrix.of
      (fun x y => if P3.Adj (σ.symm x) (σ.symm y) then (1 : ℝ) else 0) := by
    ext i j; rfl
  have hTJ : T ((Matrix.of (fun _ _ : Fin 3 × Fin 3 => (1 : ℝ)))) = (Matrix.of (fun _ _ : Fin 9 => (1 : ℝ))) := by
    ext i j; rfl
  rw [hTA, hTJ] at h
  exact h

-- Only the first row of the putative matrix identity is used.
private def boolCirculant (b : Fin 9 → Bool) : Matrix (Fin 9) (Fin 9) ℤ :=
  Matrix.circulant (fun i => if b i then 1 else 0)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem no_bool_circulant : ¬ ∃ b : Fin 9 → Bool, ∀ j : Fin 9,
    (boolCirculant b * boolCirculant b) 0 j =
      2 + (if j = 0 then 2 else 0) - boolCirculant b 0 j := by
  intro ⟨b, hb⟩
  have he : b = ![b 0, b 1, b 2, b 3, b 4, b 5, b 6, b 7, b 8] := by
    funext i
    fin_cases i <;> rfl
  rw [he] at hb
  generalize b 0 = b0 at hb
  generalize b 1 = b1 at hb
  generalize b 2 = b2 at hb
  generalize b 3 = b3 at hb
  generalize b 4 = b4 at hb
  generalize b 5 = b5 at hb
  generalize b 6 = b6 at hb
  generalize b 7 = b7 at hb
  generalize b 8 = b8 at hb
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;>
    cases b5 <;> cases b6 <;> cases b7 <;> cases b8
  all_goals (revert hb; decide)

end D5.S3.Combinatorics.Graph.EdgeComplexityWeakProductRefutation

end

noncomputable section
open scoped BigOperators ComplexConjugate
open Matrix Complex
namespace D5.S3.Combinatorics.Graph.EdgeComplexityWeakProductRefutation
open D5.S3.Quantum.QuantumChannels.TomiyamaDiagonalKPositivity
open D5.S3.Quantum.Dynamics.PolygonalFourierCouplings

private theorem fourier_apply_char {N : ℕ} [NeZero N] (m x : Fin N) :
    PolygonalFourierCouplings.fourier N m x =
      ZMod.stdAddChar (-(ZMod.finEquiv N m * ZMod.finEquiv N x)) / Real.sqrt N := by
  have hcast (i : Fin N) : (i.val : ZMod N) = ZMod.finEquiv N i := by
    cases N with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n => exact ZMod.natCast_zmod_val (n := n + 1) i
  have he : -(ZMod.finEquiv N m * ZMod.finEquiv N x) =
      (((-(m.val : ℤ) * (x.val : ℤ)) : ℤ) : ZMod N) := by
    push_cast
    rw [hcast m, hcast x]
    ring
  rw [he, ZMod.stdAddChar_coe]
  simp only [PolygonalFourierCouplings.fourier]
  congr 2
  push_cast
  ring

private theorem fourier_unitary {N : ℕ} [NeZero N] :
    PolygonalFourierCouplings.fourier N ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  have hR := fourierRows_gram N N (le_refl N)
  have hs : (Real.sqrt N : ℂ) * Real.sqrt N = N := by
    exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg N)
  have hT : (Real.sqrt N : ℂ)⁻¹ • fourierRows N N (le_refl N) ∈
      Matrix.unitaryGroup (Fin N) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    change ((Real.sqrt N : ℂ)⁻¹ • fourierRows N N (le_refl N)) *
      ((Real.sqrt N : ℂ)⁻¹ • fourierRows N N (le_refl N))ᴴ = 1
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hR, smul_smul]
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal,
      ← mul_inv, hs, inv_mul_cancel₀ (NeZero.ne (N : ℂ)), one_smul]
  have h := Matrix.map_star_mem_unitaryGroup_iff.mpr hT
  convert h using 1
  ext i j
  simp only [fourier_apply_char, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
    Complex.star_def, map_mul, map_inv₀, Complex.conj_ofReal,
    fourierRows, Fin.castLE_refl, RCLike.star_def, ← AddChar.map_neg_eq_conj]
  rw [mul_comm (ZMod.finEquiv N j), div_eq_mul_inv, mul_comm]

private theorem fourier_apply {N : ℕ} [NeZero N] (m x : Fin N) :
    PolygonalFourierCouplings.fourier N m x = Complex.exp (-2 * Real.pi * Complex.I *
      ((m.val * x.val : ℕ) : ℂ) / N) / Real.sqrt N := by
  simp only [PolygonalFourierCouplings.fourier]
  congr 2
  push_cast
  ring

private theorem fhat_matrix {N : ℕ} [NeZero N] (a : Fin N → Fin N → ℝ) :
    Matrix.of (fhat a) = PolygonalFourierCouplings.fourier N * (Matrix.of a).map (fun r : ℝ => (r : ℂ)) * PolygonalFourierCouplings.fourier N := by
  ext m n
  simp only [Matrix.of_apply, fhat, Matrix.mul_apply, Matrix.map_apply,
    fourier_apply, Finset.sum_mul]
  have hs : (Real.sqrt N : ℂ) * Real.sqrt N = N := by
    exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg N)
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  rw [show ((m.val * x.val + n.val * y.val : ℕ) : ℂ) =
    (m.val : ℂ) * x.val + (n.val : ℂ) * y.val by push_cast; rfl]
  rw [show -2 * (Real.pi : ℂ) * I * ((m.val : ℂ) * x.val + (n.val : ℂ) * y.val) / N =
      -2 * (Real.pi : ℂ) * I * ((m.val : ℂ) * x.val) / N +
      -2 * (Real.pi : ℂ) * I * ((n.val : ℂ) * y.val) / N by ring,
    Complex.exp_add]
  push_cast
  rw [mul_comm (n.val : ℂ) (y.val : ℂ)]
  have hc : (N : ℂ)⁻¹ = (Real.sqrt N : ℂ)⁻¹ * (Real.sqrt N : ℂ)⁻¹ := by
    rw [← mul_inv, hs]
  simp only [div_eq_mul_inv, one_mul, hc]
  ring

end D5.S3.Combinatorics.Graph.EdgeComplexityWeakProductRefutation

end

noncomputable section
open scoped BigOperators ComplexConjugate
open Matrix Complex
namespace D5.S3.Combinatorics.Graph.EdgeComplexityWeakProductRefutation
variable {ι : Type} [Fintype ι] [DecidableEq ι]

private def entryL1 (M : Matrix ι ι ℂ) : ℝ := ∑ i, ∑ j, ‖M i j‖
private def pairing (W M : Matrix ι ι ℂ) : ℝ :=
  ∑ i, ∑ j, (star (W i j) * M i j).re

omit [DecidableEq ι] in
private theorem pairing_trace (W M : Matrix ι ι ℂ) : pairing W M = (Wᴴ * M).trace.re := by
  simp only [pairing, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]

private theorem unitary_column_sq {W : Matrix ι ι ℂ}
    (hW : W ∈ Matrix.unitaryGroup ι ℂ) (j : ι) : ∑ i, ‖W i j‖^2 = 1 := by
  simpa only [RHLinalg.normSqMatrix, Matrix.of_apply] using
    sum_col_of_mem_doublyStochastic
      (RHLinalg.normSqMatrix_mem_doublyStochastic_of_unitary hW) j

private theorem entry_pair_le {W M : Matrix ι ι ℂ}
    (hW : W ∈ Matrix.unitaryGroup ι ℂ) (i j : ι) :
    (star (W i j) * M i j).re ≤ ‖M i j‖ := by
  calc
    _ ≤ ‖star (W i j) * M i j‖ := Complex.re_le_norm _
    _ = ‖W i j‖ * ‖M i j‖ := by rw [norm_mul, norm_star]
    _ ≤ 1 * ‖M i j‖ := mul_le_mul_of_nonneg_right
      (entry_norm_bound_of_unitary hW i j) (norm_nonneg _)
    _ = ‖M i j‖ := one_mul _

private theorem pairing_le_l1 {W M : Matrix ι ι ℂ}
    (hW : W ∈ Matrix.unitaryGroup ι ℂ) : pairing W M ≤ entryL1 M := by
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => entry_pair_le hW i j

private theorem equality_entry_norm {W M : Matrix ι ι ℂ}
    (hW : W ∈ Matrix.unitaryGroup ι ℂ) (heq : pairing W M = entryL1 M)
    (i j : ι) (hm : M i j ≠ 0) : ‖W i j‖ = 1 := by
  have hnonneg (i j : ι) : 0 ≤ ‖M i j‖ - (star (W i j) * M i j).re :=
    sub_nonneg.mpr (entry_pair_le hW i j)
  have hzero : ∑ i, ∑ j, (‖M i j‖ - (star (W i j) * M i j).re) = 0 := by
    simp only [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr heq.symm
  have hrow : ∑ j, (‖M i j‖ - (star (W i j) * M i j).re) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg fun j _ => hnonneg i j)).mp hzero i (Finset.mem_univ i)
  have hentry : ‖M i j‖ - (star (W i j) * M i j).re = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg i j)).mp hrow j (Finset.mem_univ j)
  have hbound := Complex.re_le_norm (star (W i j) * M i j)
  rw [norm_mul, norm_star] at hbound
  have hpos := norm_pos_iff.mpr hm
  have hone := entry_norm_bound_of_unitary hW i j
  nlinarith

private theorem equality_column_unique {W M : Matrix ι ι ℂ}
    (hW : W ∈ Matrix.unitaryGroup ι ℂ) (heq : pairing W M = entryL1 M)
    (i j k : ι) (hi : M i k ≠ 0) (hj : M j k ≠ 0) : i = j := by
  by_contra hne
  have hle := Finset.sum_le_sum_of_subset_of_nonneg
    (s := ({i,j} : Finset ι)) (t := Finset.univ) (f := fun l => ‖W l k‖^2)
    (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  simp only [Finset.sum_pair hne, unitary_column_sq hW,
    equality_entry_norm hW heq i k hi, equality_entry_norm hW heq j k hj] at hle
  norm_num at hle

private theorem equality_gram_diagonal {W M : Matrix ι ι ℂ}
    (hW : W ∈ Matrix.unitaryGroup ι ℂ) (heq : pairing W M = entryL1 M)
    (i j : ι) (hij : i ≠ j) : (M * Mᴴ) i j = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [Matrix.conjTranspose_apply]
  by_cases hi : M i k = 0
  · rw [hi, zero_mul]
  · have hj : M j k = 0 := by
      by_contra hj
      exact hij (equality_column_unique hW heq i j k hi hj)
    rw [hj, star_zero, mul_zero]

end D5.S3.Combinatorics.Graph.EdgeComplexityWeakProductRefutation

end

noncomputable section
open scoped BigOperators ComplexConjugate
open Matrix Complex
namespace D5.S3.Combinatorics.Graph.EdgeComplexityWeakProductRefutation
variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem fhat_parseval {N : ℕ} [NeZero N] (a : Fin N → Fin N → ℝ) :
    ∑ m, ∑ n, ‖fhat a m n‖^2 = ∑ x, ∑ y, (a x y)^2 := by
  calc
    _ = RHLinalg.frobSq (Matrix.of (fhat a)) := by
      rw [D5.S3.Quantum.Matrix.CartesianVariance.frobSq_eq_sum]
      simp only [Matrix.of_apply, Complex.normSq_eq_norm_sq]
      rw [Finset.sum_comm]
    _ = RHLinalg.frobSq ((Matrix.of a).map (fun r : ℝ => (r : ℂ))) := by
      rw [fhat_matrix]
      let U : Matrix.unitaryGroup (Fin N) ℂ := ⟨PolygonalFourierCouplings.fourier N, fourier_unitary⟩
      calc
        RHLinalg.frobSq (PolygonalFourierCouplings.fourier N * (Matrix.of a).map (fun r : ℝ => (r : ℂ)) * PolygonalFourierCouplings.fourier N) =
            RHLinalg.frobSq (PolygonalFourierCouplings.fourier N * (Matrix.of a).map (fun r : ℝ => (r : ℂ))) := by
          exact D5.S3.Quantum.Matrix.CommutatorGap.frobSq_unitary_right _ U
        _ = RHLinalg.frobSq ((PolygonalFourierCouplings.fourier N * (Matrix.of a).map (fun r : ℝ => (r : ℂ)))ᴴ) :=
          (D5.S3.Quantum.Matrix.CartesianVariance.frobSq_star _).symm
        _ = RHLinalg.frobSq (((Matrix.of a).map (fun r : ℝ => (r : ℂ)))ᴴ * (PolygonalFourierCouplings.fourier N)ᴴ) := by
          rw [Matrix.conjTranspose_mul]
        _ = RHLinalg.frobSq (((Matrix.of a).map (fun r : ℝ => (r : ℂ)))ᴴ) := by
          have hU : (PolygonalFourierCouplings.fourier N)ᴴ ∈ Matrix.unitaryGroup (Fin N) ℂ :=
            Unitary.star_mem_iff.mpr fourier_unitary
          exact D5.S3.Quantum.Matrix.CommutatorGap.frobSq_unitary_right _ ⟨(PolygonalFourierCouplings.fourier N)ᴴ, hU⟩
        _ = RHLinalg.frobSq ((Matrix.of a).map (fun r : ℝ => (r : ℂ))) :=
          D5.S3.Quantum.Matrix.CartesianVariance.frobSq_star _
    _ = _ := by
      rw [D5.S3.Quantum.Matrix.CartesianVariance.frobSq_eq_sum]
      simp only [Matrix.map_apply, Matrix.of_apply, Complex.normSq_eq_norm_sq,
        Complex.norm_real, Real.norm_eq_abs, sq_abs]
      rw [Finset.sum_comm]

end D5.S3.Combinatorics.Graph.EdgeComplexityWeakProductRefutation

end

noncomputable section
open scoped BigOperators ComplexConjugate
open Matrix Complex
namespace D5.S3.Combinatorics.Graph.EdgeComplexityWeakProductRefutation


private theorem char_sum {N : ℕ} [NeZero N] (b : ZMod N) :
    ∑ x : Fin N, ZMod.stdAddChar (ZMod.finEquiv N x * b) =
      if b = 0 then (N : ℂ) else 0 := by
  rw [Fintype.sum_equiv (ZMod.finEquiv N).toEquiv
    (fun x => ZMod.stdAddChar (ZMod.finEquiv N x * b))
    (fun x => ZMod.stdAddChar (x * b)) (fun _ => rfl)]
  simpa only [ZMod.card, Nat.cast_ite, Nat.cast_zero] using AddChar.sum_mulShift b (ZMod.isPrimitive_stdAddChar N)

private theorem fourier_sum {N : ℕ} [NeZero N] (m : Fin N) :
    ∑ x, PolygonalFourierCouplings.fourier N m x = (if m = 0 then (N : ℂ) else 0) / Real.sqrt N := by
  simp only [fourier_apply_char, ← Finset.sum_div]
  have h (x : Fin N) : -(ZMod.finEquiv N m * ZMod.finEquiv N x) =
      ZMod.finEquiv N x * (-ZMod.finEquiv N m) := by ring
  have hzero : ZMod.finEquiv N m = 0 ↔ m = 0 := by
    rw [← (ZMod.finEquiv N).map_zero, (ZMod.finEquiv N).injective.eq_iff]
  simp only [h, char_sum, neg_eq_zero, hzero]

private theorem fourier_symm {N : ℕ} [NeZero N] (m x : Fin N) : PolygonalFourierCouplings.fourier N m x = PolygonalFourierCouplings.fourier N x m := by
  simp only [fourier_apply_char, mul_comm]

private theorem fourier_square {N : ℕ} [NeZero N] (m n : Fin N) :
    ((PolygonalFourierCouplings.fourier N * PolygonalFourierCouplings.fourier N) : Matrix (Fin N) (Fin N) ℂ) m n = if m + n = 0 then (1 : ℂ) else 0 := by
  have hs : (Real.sqrt N : ℂ) * Real.sqrt N = N := by
    exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg N)
  have hc : (Real.sqrt N : ℂ)⁻¹ * (Real.sqrt N : ℂ)⁻¹ = (N : ℂ)⁻¹ := by
    rw [← mul_inv, hs]
  rw [Matrix.mul_apply]
  have h (x : Fin N) : PolygonalFourierCouplings.fourier N m x * PolygonalFourierCouplings.fourier N x n =
      (N : ℂ)⁻¹ * ZMod.stdAddChar
        (ZMod.finEquiv N x * (-(ZMod.finEquiv N m + ZMod.finEquiv N n))) := by
    simp only [fourier_apply_char, div_eq_mul_inv]
    rw [show (ZMod.finEquiv N x) * (-(ZMod.finEquiv N m + ZMod.finEquiv N n)) =
      -(ZMod.finEquiv N m * ZMod.finEquiv N x) +
      -(ZMod.finEquiv N x * ZMod.finEquiv N n) by ring, AddChar.map_add_eq_mul]
    rw [← hc]
    ring
  have hzero : ZMod.finEquiv N (m+n) = 0 ↔ m+n = 0 := by
    rw [← (ZMod.finEquiv N).map_zero, (ZMod.finEquiv N).injective.eq_iff]
  simp only [h, ← Finset.mul_sum, char_sum, neg_eq_zero, ← map_add, hzero]
  split_ifs <;> simp [NeZero.ne (N : ℂ)]

private theorem fourier_all_ones {N : ℕ} [NeZero N] (m n : Fin N) :
    ((PolygonalFourierCouplings.fourier N * Matrix.of (fun _ _ => (1 : ℂ)) * PolygonalFourierCouplings.fourier N) : Matrix (Fin N) (Fin N) ℂ) m n =
      if m = 0 ∧ n = 0 then (N : ℂ) else 0 := by
  have hentry : ((PolygonalFourierCouplings.fourier N * Matrix.of (fun _ _ => (1 : ℂ)) * PolygonalFourierCouplings.fourier N) : Matrix (Fin N) (Fin N) ℂ) m n =
      (∑ x, PolygonalFourierCouplings.fourier N m x) * (∑ y, PolygonalFourierCouplings.fourier N n y) := by
    simp only [Matrix.mul_apply, Matrix.of_apply, mul_one]
    rw [← Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro y _
    exact fourier_symm y n
  rw [hentry, fourier_sum, fourier_sum]
  have hs : (Real.sqrt N : ℂ) * Real.sqrt N = N := by
    exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg N)
  by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp only [hm, hn, and_self,
    and_true, and_false, ite_true, ite_false, zero_div, mul_zero, zero_mul]
  rw [div_mul_div_comm, hs]
  exact mul_div_cancel_right₀ _ (NeZero.ne (N : ℂ))

private theorem inverse_diagonal_circulant {N : ℕ} [NeZero N] (d : Fin N → ℂ) :
    ∃ c : Fin N → ℂ, (PolygonalFourierCouplings.fourier N)ᴴ * Matrix.diagonal d * PolygonalFourierCouplings.fourier N = Matrix.circulant c := by
  let c : Fin N → ℂ := fun l => (N : ℂ)⁻¹ *
    ∑ k, d k * ZMod.stdAddChar (ZMod.finEquiv N k * ZMod.finEquiv N l)
  refine ⟨c, ?_⟩
  have hs : (Real.sqrt N : ℂ) * Real.sqrt N = N := by
    exact_mod_cast Real.mul_self_sqrt (Nat.cast_nonneg N)
  have hc : (Real.sqrt N : ℂ)⁻¹ * (Real.sqrt N : ℂ)⁻¹ = (N : ℂ)⁻¹ := by
    rw [← mul_inv, hs]
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply,
    fourier_apply_char, star_div₀, Complex.star_def, Complex.conj_ofReal,
    ← AddChar.map_neg_eq_conj, neg_neg, Matrix.circulant_apply, c,
    Finset.mul_sum, map_sub]
  apply Finset.sum_congr rfl
  intro k _
  rw [show ZMod.finEquiv N k * (ZMod.finEquiv N i - ZMod.finEquiv N j) =
      ZMod.finEquiv N k * ZMod.finEquiv N i +
      -(ZMod.finEquiv N k * ZMod.finEquiv N j) by ring, AddChar.map_add_eq_mul]
  simp only [div_eq_mul_inv]
  rw [← hc]
  ring

end D5.S3.Combinatorics.Graph.EdgeComplexityWeakProductRefutation

end

noncomputable section
open scoped BigOperators
open Matrix
set_option maxRecDepth 10000
namespace D5.S3.Combinatorics.Graph.EdgeComplexityWeakProductRefutation

-- Generic spectral transport, with no eigenvalue ordering needed.
private theorem quadratic_eigen {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (hpoly : A * A - A - (2 : ℝ) • (1 : Matrix ι ι ℝ) = 0) (j : ι) :
    hA.eigenvalues j = 2 ∨ hA.eigenvalues j = -1 := by
  let T := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) (star hA.eigenvectorUnitary)
  have hdiag : T A = Matrix.diagonal hA.eigenvalues := by
    simpa [T] using hA.conjStarAlgAut_star_eigenvectorUnitary
  have h := congrArg T hpoly
  simp only [map_sub, map_mul, map_smul, map_one, map_zero, hdiag] at h
  have he := congrArg (fun B : Matrix ι ι ℝ => B j j) h
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    ite_true, mul_one, Matrix.zero_apply, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_apply, Pi.mul_apply] at he
  have hf : (hA.eigenvalues j - 2) * (hA.eigenvalues j + 1) = 0 := by nlinarith [he]
  rcases mul_eq_zero.mp hf with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

private theorem cubic_eigen {ι : Type} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (hpoly : A * A * A - (3 : ℝ) • (A * A) - (6 : ℝ) • A +
      (8 : ℝ) • (1 : Matrix ι ι ℝ) = 0) (j : ι) :
    hA.eigenvalues j = 4 ∨ hA.eigenvalues j = -2 ∨ hA.eigenvalues j = 1 := by
  let T := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) (star hA.eigenvectorUnitary)
  have hdiag : T A = Matrix.diagonal hA.eigenvalues := by
    simpa [T] using hA.conjStarAlgAut_star_eigenvectorUnitary
  have h := congrArg T hpoly
  simp only [map_add, map_sub, map_mul, map_smul, map_one, map_zero, hdiag] at h
  have he := congrArg (fun B : Matrix ι ι ℝ => B j j) h
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, ite_true, mul_one, Matrix.zero_apply,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, Pi.mul_apply] at he
  have hf : (hA.eigenvalues j - 4) * (hA.eigenvalues j + 2) *
      (hA.eigenvalues j - 1) = 0 := by nlinarith [he]
  rcases mul_eq_zero.mp hf with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr (by linarith))

private theorem k3_poly : ((⊤ : SimpleGraph (Fin 3)).adjMatrix ℝ) * ((⊤ : SimpleGraph (Fin 3)).adjMatrix ℝ) - (⊤ : SimpleGraph (Fin 3)).adjMatrix ℝ -
    (2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) = 0 := by
  ext i j
  change (∑ k : Fin 3, (if i ≠ k then (1 : ℝ) else 0) *
    (if k ≠ j then (1 : ℝ) else 0)) -
    (if i ≠ j then 1 else 0) - 2 * (if i = j then 1 else 0) = 0
  simp only [Fin.sum_univ_succ]
  fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff]

private theorem k3_energy : energy (⊤ : SimpleGraph (Fin 3)) = 4 := by
  let hA := (⊤ : SimpleGraph (Fin 3)).isHermitian_adjMatrix ℝ
  have hsum : ∑ j, hA.eigenvalues j = 0 := by
    have ht := RHLinalg.rtrace_eq_sum_eigenvalues hA
    simpa only [RHLinalg.rtrace, RCLike.re_to_real, Matrix.trace, Matrix.diag_apply,
      SimpleGraph.adjMatrix_apply, SimpleGraph.irrefl, ite_false, Finset.sum_const_zero] using ht.symm
  have habs (j : Fin 3) : |hA.eigenvalues j| = (hA.eigenvalues j + 4) / 3 := by
    rcases quadratic_eigen hA k3_poly j with h | h <;> rw [h] <;> norm_num
  change ∑ j, |hA.eigenvalues j| = 4
  simp_rw [habs]
  rw [← Finset.sum_div, Finset.sum_add_distrib, hsum]
  norm_num

set_option maxHeartbeats 0 in
private theorem p3_poly : (P3.adjMatrix ℝ) * (P3.adjMatrix ℝ) * (P3.adjMatrix ℝ) -
    (3 : ℝ) • ((P3.adjMatrix ℝ) * (P3.adjMatrix ℝ)) -
    (6 : ℝ) • P3.adjMatrix ℝ +
    (8 : ℝ) • (1 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℝ) = 0 := by
  have hAJ : (P3.adjMatrix ℝ) * (Matrix.of (fun _ _ : Fin 3 × Fin 3 => (1 : ℝ))) = (4 : ℝ) • (Matrix.of (fun _ _ : Fin 3 × Fin 3 => (1 : ℝ))) := by
    ext ⟨a,b⟩ q
    change (∑ r : Fin 3 × Fin 3,
      (if a ≠ r.1 ∧ b ≠ r.2 then (1 : ℝ) else 0) * 1) = 4 * 1
    fin_cases a <;> fin_cases b <;>
      (simp only [Fintype.sum_prod_type, Fin.sum_univ_succ]; norm_num [Fin.ext_iff])
  rw [Matrix.mul_assoc]
  simp only [p3_srg, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul,
    Matrix.mul_one, hAJ, smul_smul]
  module

private theorem p3_trace_sq : ((P3.adjMatrix ℝ) * (P3.adjMatrix ℝ)).trace = 36 := by
  rw [p3_srg]
  norm_num [Matrix.trace, Matrix.diag_apply, Matrix.of_apply,
    Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_succ]

private theorem p3_energy : energy P3 = 16 := by
  let hA := P3.isHermitian_adjMatrix ℝ
  have hsum : ∑ j, hA.eigenvalues j = 0 := by
    have ht := RHLinalg.rtrace_eq_sum_eigenvalues hA
    simpa only [RHLinalg.rtrace, RCLike.re_to_real, Matrix.trace, Matrix.diag_apply,
      SimpleGraph.adjMatrix_apply, SimpleGraph.irrefl, ite_false, Finset.sum_const_zero] using ht.symm
  have hsq : ∑ j, (hA.eigenvalues j)^2 = 36 := by
    have ht := RHLinalg.frobSq_hermitian_eq_sum_sq_eigenvalues hA
    simpa only [RHLinalg.frobSq, hA.eq, RCLike.re_to_real, p3_trace_sq] using ht.symm
  have habs (j : Fin 3 × Fin 3) : |hA.eigenvalues j| =
      (2 * (hA.eigenvalues j)^2 - hA.eigenvalues j + 8) / 9 := by
    rcases cubic_eigen hA p3_poly j with h | h | h <;> rw [h] <;> norm_num
  change ∑ j, |hA.eigenvalues j| = 16
  simp_rw [habs]
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, hsq, hsum]
  norm_num

end D5.S3.Combinatorics.Graph.EdgeComplexityWeakProductRefutation

end

noncomputable section
open scoped BigOperators ComplexConjugate
open Matrix Complex
namespace D5.S3.Combinatorics.Graph.EdgeComplexityWeakProductRefutation

private def rawSign : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ := Matrix.of fun p q =>
  (6 * (if P3.Adj p q then 1 else 0) + 3 * (if p = q then 1 else 0) - 2) / 9

set_option maxHeartbeats 0 in
private theorem rawSign_square : rawSign * rawSign = 1 := by
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    (simp only [Matrix.mul_apply, rawSign, Matrix.of_apply, p3_adj,
    Fintype.sum_prod_type, Fin.sum_univ_succ, Matrix.one_apply] <;> norm_num only [Prod.mk.injEq, ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk,
      Fin.val_ofNat, not_true_eq_false, not_false_eq_true,
      true_and, false_and, and_true, and_false, if_true, if_false])

private theorem rawSign_hermitian : rawSignᴴ = rawSign := by
  ext p q
  simp only [rawSign, Matrix.of_apply, Matrix.conjTranspose_apply]
  have hadj : P3.Adj q p ↔ P3.Adj p q := ⟨SimpleGraph.Adj.symm, SimpleGraph.Adj.symm⟩
  by_cases ha : P3.Adj p q <;> by_cases hpq : p = q <;> simp [hadj, ha, hpq, eq_comm]

private theorem rawSign_unitary : rawSign ∈ Matrix.unitaryGroup (Fin 3 × Fin 3) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  change rawSign * rawSignᴴ = 1
  rw [rawSign_hermitian, rawSign_square]

set_option maxHeartbeats 0 in
private theorem rawSign_trace : (rawSign * P3.adjMatrix ℂ).trace = 16 := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, rawSign,
    Matrix.of_apply, SimpleGraph.adjMatrix_apply, p3_adj,
    Fintype.sum_prod_type, Fin.sum_univ_succ]
  norm_num only [Prod.mk.injEq, ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_succ, Fin.val_mk,
      Fin.val_ofNat, not_true_eq_false, not_false_eq_true,
      true_and, false_and, and_true, and_false, if_true, if_false]

private def labeledSign (σ : (Fin 3 × Fin 3) ≃ Fin 9) : Matrix (Fin 9) (Fin 9) ℂ :=
  rawSign.reindex σ σ

private def labeledAdj (σ : (Fin 3 × Fin 3) ≃ Fin 9) : Matrix (Fin 9) (Fin 9) ℂ :=
  (P3.adjMatrix ℂ).reindex σ σ

private theorem labeledSign_unitary (σ : (Fin 3 × Fin 3) ≃ Fin 9) :
    labeledSign σ ∈ Matrix.unitaryGroup (Fin 9) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  let T := Matrix.reindexAlgEquiv ℂ ℂ σ
  have h0 : rawSign * rawSignᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp rawSign_unitary
  have h := congrArg T h0
  simp only [map_mul, map_one] at h
  have hs : T rawSignᴴ = (T rawSign)ᴴ := by ext i j; rfl
  rw [hs] at h
  exact h

private theorem labeledSign_trace (σ : (Fin 3 × Fin 3) ≃ Fin 9) :
    (labeledSign σ * labeledAdj σ).trace = 16 := by
  let T := Matrix.reindexAlgEquiv ℂ ℂ σ
  change (T rawSign * T (P3.adjMatrix ℂ)).trace = 16
  rw [← map_mul]
  have htr (B : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) : (T B).trace = B.trace := by
    simp only [Matrix.trace, Matrix.diag_apply]
    exact Fintype.sum_equiv σ.symm (fun i => B (σ.symm i) (σ.symm i))
      (fun p => B p p) (fun _ => rfl)
  rw [htr, rawSign_trace]

private def productW (σ : (Fin 3 × Fin 3) ≃ Fin 9) : Matrix (Fin 9) (Fin 9) ℂ :=
  PolygonalFourierCouplings.fourier 9 * labeledSign σ * PolygonalFourierCouplings.fourier 9

private def productM (σ : (Fin 3 × Fin 3) ≃ Fin 9) : Matrix (Fin 9) (Fin 9) ℂ :=
  PolygonalFourierCouplings.fourier 9 * labeledAdj σ * PolygonalFourierCouplings.fourier 9

private theorem productW_unitary (σ : (Fin 3 × Fin 3) ≃ Fin 9) :
    productW σ ∈ Matrix.unitaryGroup (Fin 9) ℂ :=
  (Matrix.unitaryGroup _ _).mul_mem
    ((Matrix.unitaryGroup _ _).mul_mem fourier_unitary (labeledSign_unitary σ)) fourier_unitary

private theorem product_trace (σ : (Fin 3 × Fin 3) ≃ Fin 9) :
    ((productW σ)ᴴ * productM σ).trace = 16 := by
  have hF : (PolygonalFourierCouplings.fourier 9)ᴴ * (PolygonalFourierCouplings.fourier 9 : Matrix (Fin 9) (Fin 9) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp fourier_unitary
  have hS : (labeledSign σ)ᴴ = labeledSign σ := by
    simp only [labeledSign, Matrix.conjTranspose_reindex, rawSign_hermitian]
  have hmat : (productW σ)ᴴ * productM σ =
      (PolygonalFourierCouplings.fourier 9)ᴴ * (labeledSign σ * labeledAdj σ) * PolygonalFourierCouplings.fourier 9 := by
    simp only [productW, productM, Matrix.conjTranspose_mul, hS, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (PolygonalFourierCouplings.fourier 9)ᴴ (PolygonalFourierCouplings.fourier 9), hF, Matrix.one_mul]
  have hF' : (PolygonalFourierCouplings.fourier 9 : Matrix (Fin 9) (Fin 9) ℂ) * (PolygonalFourierCouplings.fourier 9)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp fourier_unitary
  rw [hmat, Matrix.trace_mul_cycle, ← Matrix.mul_assoc, hF', Matrix.one_mul,
    labeledSign_trace]


private theorem product_pairing (σ : (Fin 3 × Fin 3) ≃ Fin 9) :
    pairing (productW σ) (productM σ) = 16 := by
  rw [pairing_trace, product_trace]
  rfl

private theorem product_l1_bound (σ : (Fin 3 × Fin 3) ≃ Fin 9) :
    16 ≤ entryL1 (productM σ) := by
  rw [← product_pairing σ]
  exact pairing_le_l1 (productW_unitary σ)

end D5.S3.Combinatorics.Graph.EdgeComplexityWeakProductRefutation

end

noncomputable section
open scoped BigOperators ComplexConjugate
open Matrix Complex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace D5.S3.Combinatorics.Graph.EdgeComplexityWeakProductRefutation

private theorem indicator_matrix {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (σ : V ≃ Fin (Fintype.card V)) :
    (Matrix.of (f G σ)).map (fun r : ℝ => (r : ℂ)) = (G.adjMatrix ℂ).reindex σ σ := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.map_apply, Matrix.of_apply, f, SimpleGraph.adjMatrix_apply]
  split_ifs <;> rfl

private theorem productM_eq_fhat (σ : (Fin 3 × Fin 3) ≃ Fin (Fintype.card (Fin 3 × Fin 3))) :
    productM σ = Matrix.of (fhat (f P3 σ)) := by
  have h := fhat_matrix (f P3 σ)
  rw [indicator_matrix] at h
  exact h.symm

private theorem productM_frob (σ : (Fin 3 × Fin 3) ≃ Fin 9) :
    RHLinalg.frobSq (productM σ) = 36 := by
  rw [productM_eq_fhat, D5.S3.Quantum.Matrix.CartesianVariance.frobSq_eq_sum]
  simp only [Matrix.of_apply, Complex.normSq_eq_norm_sq]
  rw [Finset.sum_comm, fhat_parseval]
  change (∑ p : Fin 9, ∑ q : Fin 9, ((P3.adjMatrix ℝ) (σ.symm p) (σ.symm q))^2) = 36
  have h (p : Fin 9) : ∑ q, ((P3.adjMatrix ℝ) (σ.symm p) (σ.symm q))^2 =
      ∑ q : Fin 3 × Fin 3, ((P3.adjMatrix ℝ) (σ.symm p) q)^2 :=
    Fintype.sum_equiv σ.symm _ _ (fun _ => rfl)
  simp only [h]
  rw [Fintype.sum_equiv σ.symm
    (fun p => ∑ q, ((P3.adjMatrix ℝ) (σ.symm p) q)^2)
    (fun p => ∑ q, ((P3.adjMatrix ℝ) p q)^2) (fun _ => rfl)]
  simp only [SimpleGraph.adjMatrix_apply, p3_adj,
    Fintype.sum_prod_type, Fin.sum_univ_succ]
  norm_num [Fin.ext_iff]

private theorem product_fr_formula (σ : (Fin 3 × Fin 3) ≃ Fin 9) :
    FR (f P3 σ) = entryL1 (productM σ) / 6 := by
  have he : ∑ m, ∑ n, ‖fhat (f P3 σ) m n‖^2 = 36 := by
    calc
      _ = RHLinalg.frobSq (Matrix.of (fhat (f P3 σ))) := by
        rw [D5.S3.Quantum.Matrix.CartesianVariance.frobSq_eq_sum]
        simp only [Matrix.of_apply, Complex.normSq_eq_norm_sq]
        rw [Finset.sum_comm]
      _ = 36 := by rw [← productM_eq_fhat, productM_frob]

  rw [FR, he]
  have hsqrt : Real.sqrt 36 = 6 := by norm_num
  rw [hsqrt]
  change entryL1 (Matrix.of (fhat (f P3 σ))) / 6 = _
  rw [← productM_eq_fhat]

end D5.S3.Combinatorics.Graph.EdgeComplexityWeakProductRefutation

end

noncomputable section
open scoped BigOperators
open Matrix
namespace D5.S3.Combinatorics.Graph.EdgeComplexityWeakProductRefutation

private theorem no_real_circulant (v : Fin 9 → ℝ) (hv : ∀ i, v i = 0 ∨ v i = 1) :
    Matrix.circulant v * Matrix.circulant v ≠
      (2 : ℝ) • (Matrix.of (fun _ _ : Fin 9 => (1 : ℝ))) + (2 : ℝ) • (1 : Matrix (Fin 9) (Fin 9) ℝ) -
      Matrix.circulant v := by
  intro heq
  let b : Fin 9 → Bool := fun i => decide (v i = 1)
  have hb (i : Fin 9) : ((if b i then 1 else 0 : ℤ) : ℝ) = v i := by
    rcases hv i with h | h <;> simp [b, h]
  have hcast (i j : Fin 9) : (boolCirculant b i j : ℝ) = Matrix.circulant v i j := hb (i-j)
  apply no_bool_circulant
  refine ⟨b, fun j => ?_⟩
  apply Int.cast_injective (α := ℝ)
  have hj := congrArg (fun A : Matrix (Fin 9) (Fin 9) ℝ => A 0 j) heq
  simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, Matrix.of_apply] at hj
  push_cast
  simp only [Matrix.mul_apply, Int.cast_sum, Int.cast_mul, hcast]
  simpa only [eq_comm, mul_ite, mul_one, mul_zero, Int.cast_ite, Int.cast_ofNat,
    Int.cast_sub, Matrix.circulant_apply] using hj

end D5.S3.Combinatorics.Graph.EdgeComplexityWeakProductRefutation

end

noncomputable section
open scoped BigOperators ComplexConjugate
open Matrix Complex
namespace D5.S3.Combinatorics.Graph.EdgeComplexityWeakProductRefutation

private theorem square_circulant_of_sparse {N : ℕ} [NeZero N]
    (A : Matrix (Fin N) (Fin N) ℂ) (hA : Aᴴ = A)
    (hsparse : ∀ i j : Fin N, i ≠ j →
      (((PolygonalFourierCouplings.fourier N * A * PolygonalFourierCouplings.fourier N) * (PolygonalFourierCouplings.fourier N * A * PolygonalFourierCouplings.fourier N)ᴴ) :
        Matrix (Fin N) (Fin N) ℂ) i j = 0) :
    ∃ c : Fin N → ℂ, A * A = Matrix.circulant c := by
  let M := PolygonalFourierCouplings.fourier N * A * PolygonalFourierCouplings.fourier N
  let d : Fin N → ℂ := fun i => (M * Mᴴ) i i
  have hdiag : M * Mᴴ = Matrix.diagonal d := by
    ext i j
    by_cases h : i = j
    · subst j; simp only [Matrix.diagonal_apply_eq, d]
    · rw [hsparse i j h, Matrix.diagonal_apply_ne _ h]
  have hF : (PolygonalFourierCouplings.fourier N)ᴴ * (PolygonalFourierCouplings.fourier N : Matrix (Fin N) (Fin N) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp fourier_unitary
  have hF' : (PolygonalFourierCouplings.fourier N : Matrix (Fin N) (Fin N) ℂ) * (PolygonalFourierCouplings.fourier N)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp fourier_unitary
  have hgram : M * Mᴴ = PolygonalFourierCouplings.fourier N * (A * A) * (PolygonalFourierCouplings.fourier N)ᴴ := by
    simp only [M, Matrix.conjTranspose_mul, hA, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (PolygonalFourierCouplings.fourier N) (PolygonalFourierCouplings.fourier N)ᴴ, hF', Matrix.one_mul]
  have hinverse : A * A = (PolygonalFourierCouplings.fourier N)ᴴ * Matrix.diagonal d * PolygonalFourierCouplings.fourier N := by
    rw [← hdiag, hgram]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (PolygonalFourierCouplings.fourier N)ᴴ (PolygonalFourierCouplings.fourier N), hF, Matrix.one_mul]
    simp only [Matrix.mul_one]
  rcases inverse_diagonal_circulant d with ⟨c,hc⟩
  exact ⟨c, hinverse.trans hc⟩

end D5.S3.Combinatorics.Graph.EdgeComplexityWeakProductRefutation

end

noncomputable section
open scoped BigOperators ComplexConjugate
open Matrix Complex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 10000
namespace D5.S3.Combinatorics.Graph.EdgeComplexityWeakProductRefutation

private theorem k3_fhat (σ : Fin 3 ≃ Fin (Fintype.card (Fin 3))) (m n : Fin (Fintype.card (Fin 3))) :
    fhat (f (⊤ : SimpleGraph (Fin 3)) σ) m n =
      (if m = 0 ∧ n = 0 then (3 : ℂ) else 0) -
      (if m + n = 0 then 1 else 0) := by
  have hA : (Matrix.of (f (⊤ : SimpleGraph (Fin 3)) σ)).map (fun r : ℝ => (r : ℂ)) =
      Matrix.of (fun _ _ => (1 : ℂ)) - (1 : Matrix (Fin (Fintype.card (Fin 3))) (Fin (Fintype.card (Fin 3))) ℂ) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.sub_apply, Matrix.one_apply]
    rw [k3_indicator]
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  have h := congrArg (fun M : Matrix (Fin (Fintype.card (Fin 3))) (Fin (Fintype.card (Fin 3))) ℂ => M m n)
    (fhat_matrix (f (⊤ : SimpleGraph (Fin 3)) σ))
  rw [hA, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.sub_apply] at h
  rw [fourier_all_ones (N := Fintype.card (Fin 3)),
    fourier_square (N := Fintype.card (Fin 3))] at h
  simpa only [Matrix.of_apply, Fintype.card_fin, Nat.cast_ofNat] using h

private theorem k3_fourier_l1 (σ : Fin 3 ≃ Fin (Fintype.card (Fin 3))) :
    ∑ m, ∑ n, ‖fhat (f (⊤ : SimpleGraph (Fin 3)) σ) m n‖ = 4 := by
  simp only [k3_fhat]
  change (∑ m : Fin 3, ∑ n : Fin 3,
    ‖(if m = 0 ∧ n = 0 then (3 : ℂ) else 0) -
      (if m + n = 0 then 1 else 0)‖) = 4
  simp only [Fin.sum_univ_three]
  norm_num only [Fin.ext_iff, Fin.val_add, Fin.val_zero, Fin.val_one,
    Fin.coe_ofNat_eq_mod, and_true, and_false, true_and, false_and, ite_true, ite_false,
    sub_zero, zero_sub, sub_self, norm_zero, norm_one, norm_neg, Complex.norm_ofNat,
    show (3 : ℂ) - 1 = 2 by norm_num]

private theorem k3_fourier_sq (σ : Fin 3 ≃ Fin (Fintype.card (Fin 3))) :
    ∑ m, ∑ n, ‖fhat (f (⊤ : SimpleGraph (Fin 3)) σ) m n‖^2 = 6 := by
  rw [fhat_parseval, k3_indicator]
  change (∑ x : Fin 3, ∑ y : Fin 3, (if x ≠ y then (1 : ℝ) else 0)^2) = 6
  simp only [Fin.sum_univ_three]
  norm_num [Fin.ext_iff]

private theorem k3_fr (σ : Fin 3 ≃ Fin (Fintype.card (Fin 3))) : FR (f (⊤ : SimpleGraph (Fin 3)) σ) = 4 / Real.sqrt 6 := by
  rw [FR, k3_fourier_l1, k3_fourier_sq]

private theorem k3_frmin : FRmin (⊤ : SimpleGraph (Fin 3)) = 4 / Real.sqrt 6 := by
  apply le_antisymm
  · have h := Finset.inf'_le (fun σ : Fin 3 ≃ Fin (Fintype.card (Fin 3)) => FR (f (⊤ : SimpleGraph (Fin 3)) σ))
      (Finset.mem_univ (Fintype.equivFin (Fin 3)))
    exact h.trans (k3_fr _).le
  · exact (Finset.le_inf'_iff _ _).mpr (fun σ _ => (k3_fr σ).ge)

private theorem k3_attains : AttainsEquality (⊤ : SimpleGraph (Fin 3)) := by
  constructor
  · rw [k3_size]; decide
  · rw [k3_frmin, k3_energy, k3_size]
    norm_num

end D5.S3.Combinatorics.Graph.EdgeComplexityWeakProductRefutation

end

noncomputable section
open scoped BigOperators ComplexConjugate
open Matrix Complex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace D5.S3.Combinatorics.Graph.EdgeComplexityWeakProductRefutation

private theorem product_l1_ne (σ : (Fin 3 × Fin 3) ≃ Fin 9) :
    entryL1 (productM σ) ≠ 16 := by
  intro heq
  have hpair : pairing (productW σ) (productM σ) = entryL1 (productM σ) := by
    rw [product_pairing, heq]
  have hA : (labeledAdj σ)ᴴ = labeledAdj σ := by
    simp only [labeledAdj, Matrix.conjTranspose_reindex]
    rw [P3.isHermitian_adjMatrix ℂ]
  have hsparse : ∀ i j : Fin 9, i ≠ j →
      (((PolygonalFourierCouplings.fourier 9 * labeledAdj σ * PolygonalFourierCouplings.fourier 9) * (PolygonalFourierCouplings.fourier 9 * labeledAdj σ * PolygonalFourierCouplings.fourier 9)ᴴ) :
        Matrix (Fin 9) (Fin 9) ℂ) i j = 0 :=
    fun i j hij => equality_gram_diagonal (productW_unitary σ) hpair i j hij
  rcases square_circulant_of_sparse (labeledAdj σ) hA hsparse with ⟨c,hc⟩
  let R : Matrix (Fin 9) (Fin 9) ℝ := Matrix.of (f P3 σ)
  have hR : R.map Complex.ofRealHom = labeledAdj σ := by
    exact indicator_matrix P3 σ

  have hRR : (R * R).map Complex.ofRealHom = labeledAdj σ * labeledAdj σ := by
    rw [Matrix.map_mul, hR]
  have hreal : R * R = Matrix.circulant (fun l => (c l).re) := by
    ext i j
    have h := congrArg (fun B : Matrix (Fin 9) (Fin 9) ℂ => (B i j).re) (hRR.trans hc)
    simpa only [Matrix.map_apply, Complex.ofRealHom_eq_coe, Complex.ofReal_re,
      Matrix.circulant_apply] using h
  have hsg : R * R = (2 : ℝ) • (Matrix.of (fun _ _ : Fin 9 => (1 : ℝ))) + (2 : ℝ) • (1 : Matrix (Fin 9) (Fin 9) ℝ) - R :=
    p3_labeled_srg σ
  let v : Fin 9 → ℝ := fun l => 2 + (if l = 0 then 2 else 0) - (c l).re
  have hcir : R = Matrix.circulant v := by
    ext i j
    have h := congrArg (fun B : Matrix (Fin 9) (Fin 9) ℝ => B i j) hsg
    rw [hreal] at h
    simp only [Matrix.circulant_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.one_apply] at h
    simp only [Matrix.circulant_apply, v, sub_eq_zero]
    by_cases hij : i = j <;> simp only [hij, ite_true, ite_false] at h ⊢ <;> linarith
  have hv (l : Fin 9) : v l = 0 ∨ v l = 1 := by
    have h := congrArg (fun B : Matrix (Fin 9) (Fin 9) ℝ => B l 0) hcir
    simp only [R, Matrix.of_apply, f, Matrix.reindex_apply, Matrix.submatrix_apply,
      SimpleGraph.adjMatrix_apply, Matrix.circulant_apply, sub_zero] at h
    split_ifs at h
    · exact Or.inr h.symm
    · exact Or.inl h.symm
  apply no_real_circulant v hv
  rw [← hcir]
  exact hsg

private theorem product_fr_ne (σ : (Fin 3 × Fin 3) ≃ Fin 9) : FR (f P3 σ) ≠ 8/3 := by
  rw [product_fr_formula]
  intro h
  have he : entryL1 (productM σ) = 16 := by linarith
  exact product_l1_ne σ he

private theorem product_fr_strict (σ : (Fin 3 × Fin 3) ≃ Fin 9) : 8/3 < FR (f P3 σ) := by
  have hbound : 8/3 ≤ FR (f P3 σ) := by
    rw [product_fr_formula]
    have hle := product_l1_bound σ
    linarith
  exact lt_of_le_of_ne hbound (Ne.symm (product_fr_ne σ))

private theorem product_frmin_strict : 8/3 < FRmin P3 := by
  unfold FRmin
  exact (Finset.lt_inf'_iff _).mpr (fun σ _ => product_fr_strict σ)

private theorem product_not_attains : ¬ AttainsEquality P3 := by
  intro h
  have he := h.2
  rw [p3_size, p3_energy] at he
  norm_num at he
  have hlt := product_frmin_strict
  linarith

end D5.S3.Combinatorics.Graph.EdgeComplexityWeakProductRefutation

end

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace D5.S3.Combinatorics.Graph.EdgeComplexityWeakProductRefutation

theorem result : ¬ claim := by
  intro h
  have hp := h (Fin 3) (Fin 3) (⊤ : SimpleGraph (Fin 3)) (⊤ : SimpleGraph (Fin 3)) k3_attains k3_attains
  exact product_not_attains hp

end D5.S3.Combinatorics.Graph.EdgeComplexityWeakProductRefutation
