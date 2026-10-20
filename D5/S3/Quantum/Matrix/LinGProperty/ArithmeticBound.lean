/- GID: D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/LinGProperty/ArithmeticBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Trace-corrected Gram comparison for positive block matrices. -/

import D5.S3.Quantum.Schatten.SingularValueOrder
import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Quantum.Matrix.LinGProperty.ScalarPerturbation
import D5.S3.Quantum.Matrix.LinGProperty.PhaseRotation
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
namespace D5.S3.Quantum.Matrix.LinGProperty

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A positive matrix is bounded above by its trace times the identity. -/
theorem trace_identity_sub_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.PosSemidef) :
    (((A.trace.re : ℂ) • (1 : Matrix ι ι ℂ)) - A).PosSemidef := by
  classical
  have ht : A.trace.re = ∑ i, hA.1.eigenvalues i := by
    simpa using congrArg Complex.re hA.1.trace_eq_sum_eigenvalues
  have he (i : ι) : hA.1.eigenvalues i ≤ A.trace.re := by
    rw [ht]
    exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
  let U : Matrix ι ι ℂ := hA.1.eigenvectorUnitary
  have hu : U * Uᴴ = 1 := hA.1.eigenvectorUnitary.property.2
  have hd : (diagonal (fun i => ((A.trace.re - hA.1.eigenvalues i : ℝ) : ℂ))).PosSemidef :=
    PosSemidef.diagonal (fun i => Complex.zero_le_real.mpr (sub_nonneg.mpr (he i)))
  have hs : diagonal (fun i => ((A.trace.re - hA.1.eigenvalues i : ℝ) : ℂ)) =
      (A.trace.re : ℂ) • (1 : Matrix ι ι ℂ) -
        diagonal (fun i => (hA.1.eigenvalues i : ℂ)) := by
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.diagonal_apply, Matrix.one_apply]
  have hh := hd.mul_mul_conjTranspose_same U
  rw [hs, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, hu] at hh
  have hspec : U * diagonal (fun i => (hA.1.eigenvalues i : ℂ)) * Uᴴ = A := by
    have hs := hA.1.spectral_theorem
    change A = U * diagonal (fun i => (hA.1.eigenvalues i : ℂ)) * Uᴴ at hs
    exact hs.symm
  simpa only [hspec] using hh

/-- The discrepancy Gram matrix supplies the precise scalar error in the sum Gram bound. -/
private theorem gram_trace_correction {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (U V : Matrix ι κ ℂ) :
    (((1 / 2 : ℂ) • ((U + V)ᴴ * (U + V)) +
      ((((U - V)ᴴ * (U - V)).trace.re / 2 : ℝ) : ℂ) • (1 : Matrix κ κ ℂ)) -
      (Uᴴ * U + Vᴴ * V)).PosSemidef := by
  have h := (trace_identity_sub_posSemidef ((U - V)ᴴ * (U - V))
    (posSemidef_conjTranspose_mul_self (U - V))).smul
      (show (0 : ℂ) ≤ ((1 / 2 : ℝ) : ℂ) from Complex.zero_le_real.mpr (by norm_num))
  convert h using 1
  ext i j
  simp only [conjTranspose_add, conjTranspose_sub, Matrix.add_mul, Matrix.sub_mul,
    Matrix.mul_add, Matrix.mul_sub, smul_add, smul_sub, smul_smul,
    Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
  push_cast
  ring

/-- The row Gram counterpart of the discrepancy is positive. -/
theorem row_gram_sum_comparison {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (U V : Matrix ι κ ℂ) :
    (((2 : ℂ) • (U * Uᴴ + V * Vᴴ)) - (U + V) * (U + V)ᴴ).PosSemidef := by
  convert posSemidef_self_mul_conjTranspose (U - V) using 1
  ext i j
  simp only [conjTranspose_add, conjTranspose_sub, Matrix.add_mul, Matrix.sub_mul,
    Matrix.mul_add, Matrix.mul_sub, smul_add, Matrix.smul_apply,
    Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
  ring

/-- Unit trace row Grams turn the discrepancy trace into a trace-overlap deficit. -/
private theorem normalized_gram_trace_correction {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (U V : Matrix ι κ ℂ)
    (hU : (U * Uᴴ).trace = 1) (hV : (V * Vᴴ).trace = 1) :
    (((1 / 2 : ℂ) • ((U + V)ᴴ * (U + V)) +
      ((1 - (U * Vᴴ).trace.re : ℝ) : ℂ) • (1 : Matrix κ κ ℂ)) -
      (Uᴴ * U + Vᴴ * V)).PosSemidef := by
  have htU : (Uᴴ * U).trace = 1 := (trace_mul_comm Uᴴ U).trans hU
  have htV : (Vᴴ * V).trace = 1 := (trace_mul_comm Vᴴ V).trans hV
  have htX : (Uᴴ * V).trace = star ((U * Vᴴ).trace) := by
    rw [← trace_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose,
      trace_mul_comm]
  have htY : (Vᴴ * U).trace = (U * Vᴴ).trace := trace_mul_comm _ _
  have ht : ((U - V)ᴴ * (U - V)).trace.re / 2 = 1 - (U * Vᴴ).trace.re := by
    simp only [conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, trace_sub,
      htU, htV, htX, htY, Complex.sub_re, Complex.one_re, Complex.star_def,
      Complex.conj_re]
    ring
  simpa only [ht] using gram_trace_correction U V

/-- Appending a zero block preserves the leading ordered eigenvalues of a positive matrix. -/
private theorem eigenvalues_zero_padding {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosSemidef)
    (hB : (fromBlocks A 0 0 (0 : Matrix (Fin n) (Fin n) ℂ)).IsHermitian)
    (j : Fin (Fintype.card (Fin n))) :
    hB.eigenvalues₀ ⟨j.val, by simp only [Fintype.card_sum, Fintype.card_fin]; have hj := j.isLt; simp only [Fintype.card_fin] at hj; omega⟩ =
      hA.1.eigenvalues₀ j := by
  classical
  have hr : A.charpoly.roots.map (RCLike.re : ℂ → ℝ) = (List.ofFn hA.1.eigenvalues₀ : Multiset ℝ) := by
    rw [hA.1.roots_charpoly_eq_eigenvalues₀, Multiset.map_map]
    simp only [Function.comp_def, RCLike.ofReal_re, Fin.univ_val_map]
  have ha (i : Fin (Fintype.card (Fin n))) : 0 ≤ hA.1.eigenvalues₀ i := by
    simpa only [IsHermitian.eigenvalues, Equiv.symm_apply_apply] using
      hA.eigenvalues_nonneg ((Fintype.equivOfCardEq (Fintype.card_fin _)) i)
  have hp : (List.ofFn hA.1.eigenvalues₀ ++ List.replicate n (0 : ℝ)).SortedGE := by
    rw [List.sortedGE_append]
    refine ⟨hA.1.eigenvalues₀_antitone.sortedGE_ofFn, ?_, ?_⟩
    · simp [List.sortedGE_iff_pairwise]
    · intro a ha' b hb
      have hb' : b = 0 := by simpa using (List.mem_replicate.mp hb).2
      subst b
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha'
      exact ha i
  have hs : List.ofFn hB.eigenvalues₀ = List.ofFn hA.1.eigenvalues₀ ++ List.replicate n 0 := by
    rw [← hB.sort_roots_charpoly_eq_eigenvalues₀, charpoly_fromBlocks_zero₁₂,
      charpoly_zero, Polynomial.roots_mul
        (mul_ne_zero (Matrix.charpoly_monic A).ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)),
      Polynomial.roots_X_pow, Multiset.map_add, hr]
    simp only [Fintype.card_fin, Multiset.map_replicate, Multiset.map_nsmul, Multiset.map_singleton, Multiset.nsmul_singleton, Multiset.map_coe, List.map_replicate, RCLike.zero_re,
      ← Multiset.coe_replicate, ← Multiset.coe_add, Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simpa only [Fintype.card_fin, decide_eq_true_eq, ← List.sortedGE_iff_pairwise] using hp
  have hj := congrArg (fun l : List ℝ => l[j.val]?) hs
  have hsmall : j.val < n := by simpa using j.isLt
  have hbig : j.val < n + n := by omega
  simpa [hsmall, hbig, List.getElem?_append, List.length_ofFn] using hj

theorem eigenvalues_zero_eq_of_charpoly {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A.charpoly = B.charpoly) (j : Fin (Fintype.card ι)) :
    hA.eigenvalues₀ j = hB.eigenvalues₀ j := by
  have he := (hA.eigenvalues_eq_eigenvalues_iff hB).mpr h
  have hj := congrFun he ((Fintype.equivOfCardEq (Fintype.card_fin _)) j)
  simpa only [IsHermitian.eigenvalues, Equiv.symm_apply_apply] using hj

/-- The leading ordered eigenvalues of the two rectangular Grams agree, including zeros. -/
theorem rectangular_gram_eigenvalues {n : ℕ}
    (T : Matrix (Fin n) (Fin n ⊕ Fin n) ℂ)
    (j : Fin (Fintype.card (Fin n))) :
    (isHermitian_conjTranspose_mul_self T).eigenvalues₀
      ⟨j.val, by simp only [Fintype.card_sum, Fintype.card_fin]; have hj := j.isLt; simp only [Fintype.card_fin] at hj; omega⟩ =
      (isHermitian_mul_conjTranspose_self T).eigenvalues₀ j := by
  let Z : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ := fromRows T 0
  have hc : Zᴴ * Z = Tᴴ * T := by
    simp [Z, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows]
  have hr : Z * Zᴴ = fromBlocks (T * Tᴴ) 0 0 (0 : Matrix (Fin n) (Fin n) ℂ) := by
    dsimp [Z]
    rw [conjTranspose_fromRows_eq_fromCols_conjTranspose, fromRows_mul_fromCols]
    simp only [conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul]
  have hB := isHermitian_mul_conjTranspose_self Z
  have hB' : (fromBlocks (T * Tᴴ) 0 0 (0 : Matrix (Fin n) (Fin n) ℂ)).IsHermitian := hr ▸ hB
  have hh := eigenvalues_zero_eq_of_charpoly
    (isHermitian_conjTranspose_mul_self T) hB' (by
      rw [← hc, ← hr]
      exact charpoly_mul_comm Zᴴ Z)
      ⟨j.val, by simp only [Fintype.card_sum, Fintype.card_fin]; have hj := j.isLt; simp only [Fintype.card_fin] at hj; omega⟩
  exact hh.trans (eigenvalues_zero_padding _ (posSemidef_self_mul_conjTranspose T) hB' j)

private theorem eigenvalues_zero_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (e : ι ≃ κ) (j : Fin (Fintype.card ι)) :
    (hA.reindex e).eigenvalues₀ ⟨j.val, by rw [← Fintype.card_congr e]; exact j.isLt⟩ =
      hA.eigenvalues₀ j := by
  have h := (hA.reindex e).sort_roots_charpoly_eq_eigenvalues₀
  rw [charpoly_reindex, hA.sort_roots_charpoly_eq_eigenvalues₀] at h
  have hj := congrArg (fun l : List ℝ => l[j.val]?) h
  have hk : j.val < Fintype.card κ := by rw [← Fintype.card_congr e]; exact j.isLt
  simpa [j.isLt, hk] using hj.symm

theorem eigenvalues_zero_mono_finite {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : (B - A).PosSemidef) (j : Fin (Fintype.card ι)) :
    hA.eigenvalues₀ j ≤ hB.eigenvalues₀ j := by
  let e := Fintype.equivFin ι
  have hp : (B.reindex e e - A.reindex e e).PosSemidef := by
    convert h.submatrix e.symm using 1 <;> rfl
  have hh := Schatten.eigenvalues_zero_mono (hA.reindex e) (hB.reindex e) hp
    ⟨j.val, by simpa using j.isLt⟩
  have hiA := eigenvalues_zero_reindex A hA e j
  have hiB := eigenvalues_zero_reindex B hB e j
  exact hiA.symm.le.trans (hh.trans hiB.le)

theorem eigenvalues_zero_smul_finite {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (r : ℝ) (hr : 0 ≤ r)
    (hB : ((r : ℂ) • A).IsHermitian) (j : Fin (Fintype.card ι)) :
    hB.eigenvalues₀ j = r * hA.eigenvalues₀ j := by
  let e := Fintype.equivFin ι
  have hs : (((r : ℂ) • A).reindex e e) = (r : ℂ) • A.reindex e e := rfl
  have hh := Schatten.eigenvalues_zero_smul (A.reindex e e) (hA.reindex e) r hr
    (hs ▸ hB.reindex e) ⟨j.val, by simpa using j.isLt⟩
  have hi := eigenvalues_zero_reindex ((r : ℂ) • A) hB e j
  have hi' : (hs ▸ hB.reindex e).eigenvalues₀
      ⟨j.val, by simpa using j.isLt⟩ = hB.eigenvalues₀ j := by
    exact (eigenvalues_zero_eq_of_charpoly (hs ▸ hB.reindex e) (hB.reindex e)
      (congrArg Matrix.charpoly hs).symm _).trans hi
  have hiA := eigenvalues_zero_reindex A hA e j
  exact hi'.symm.trans (hh.trans (congrArg (fun x => r * x) hiA))

theorem eigenvalues_zero_add_scalar_finite {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (r : ℝ)
    (hB : (A + (r : ℂ) • 1).IsHermitian) (j : Fin (Fintype.card ι)) :
    hB.eigenvalues₀ j = hA.eigenvalues₀ j + r := by
  let e := Fintype.equivFin ι
  have hs : ((A + (r : ℂ) • 1).reindex e e) = A.reindex e e + (r : ℂ) • 1 := by
    simp [Matrix.reindex_apply, Matrix.submatrix_add, Matrix.submatrix_smul,
      Matrix.submatrix_one_equiv]
  have hh := eigenvalues_zero_add_scalar (A.reindex e e) (hA.reindex e) r
    (hs ▸ hB.reindex e) ⟨j.val, by simpa using j.isLt⟩
  have hi := eigenvalues_zero_reindex (A + (r : ℂ) • 1) hB e j
  have hi' : (hs ▸ hB.reindex e).eigenvalues₀
      ⟨j.val, by simpa using j.isLt⟩ = hB.eigenvalues₀ j := by
    exact (eigenvalues_zero_eq_of_charpoly (hs ▸ hB.reindex e) (hB.reindex e)
      (congrArg Matrix.charpoly hs).symm _).trans hi
  have hiA := eigenvalues_zero_reindex A hA e j
  exact hi'.symm.trans (hh.trans (congrArg (fun x => x + r) hiA))

private theorem dilation_charpoly {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    (fromBlocks 0 X Xᴴ (0 : Matrix (Fin n) (Fin n) ℂ)).charpoly =
      (fromBlocks (diagonal (fun i => (singularValues X i : ℂ))) 0 0
        (-diagonal (fun i => (singularValues X i : ℂ)))).charpoly := by
  obtain ⟨U, V, hX⟩ :=
    D5.S3.Quantum.Foundation.FiniteTraceDistance.exists_svd_sqrt_eigenvalues X
  let D : Matrix (Fin n) (Fin n) ℂ := diagonal (fun i => (singularValues X i : ℂ))
  have hX' : X = U.val * D * V.valᴴ := by simpa [D, singularValues] using hX
  let N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ := fromBlocks U.val U.val V.val (-V.val)
  let M := (1 / 2 : ℂ) • N
  have hUU : U.valᴴ * U.val = 1 := U.property.1
  have hVV : V.valᴴ * V.val = 1 := V.property.1
  have hi : Nᴴ * M = 1 := by
    dsimp [M, N]
    simp only [fromBlocks_conjTranspose, conjTranspose_neg,
      Matrix.mul_smul, fromBlocks_multiply, Matrix.neg_mul, Matrix.mul_neg,
      neg_neg, hUU, hVV]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.fromBlocks, Matrix.one_apply, Matrix.smul_apply] <;> ring
  let B := fromBlocks D 0 0 (-D)
  have hD : Dᴴ = D := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [D, Matrix.diagonal_apply]
    · simp [D, hij, Ne.symm hij, Matrix.diagonal_apply]
  have hxadj : Xᴴ = V.val * D * U.valᴴ := by
    rw [hX', conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hD,
      Matrix.mul_assoc]
  have hXr : U.val * (D * V.valᴴ) = X := by rw [← Matrix.mul_assoc, ← hX']
  have hXar : V.val * (D * U.valᴴ) = Xᴴ := by rw [← Matrix.mul_assoc, ← hxadj]
  have heq : fromBlocks 0 X Xᴴ (0 : Matrix (Fin n) (Fin n) ℂ) = M * B * Nᴴ := by
    dsimp [M, N, B]
    simp only [Matrix.smul_mul, fromBlocks_multiply, fromBlocks_conjTranspose,
      conjTranspose_neg, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add, Matrix.mul_assoc]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.fromBlocks, Matrix.smul_apply, hXr, hXar] <;> ring
  rw [heq, charpoly_mul_comm, ← Matrix.mul_assoc, hi, Matrix.one_mul]

theorem dilation_eigenvalues {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ)
    (hD : (fromBlocks 0 X Xᴴ (0 : Matrix (Fin n) (Fin n) ℂ)).IsHermitian)
    (j : Fin (Fintype.card (Fin n))) :
    hD.eigenvalues₀
      ⟨j.val, by simp only [Fintype.card_sum, Fintype.card_fin]; have hj := j.isLt; simp only [Fintype.card_fin] at hj; omega⟩ =
      singularValuesSorted X j := by
  classical
  let s : Fin n → ℝ := singularValues X
  let B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
    fromBlocks (diagonal (fun i => (s i : ℂ))) 0 0 (-diagonal (fun i => (s i : ℂ)))
  have hBdiag : B = diagonal (fun i => ((Sum.elim s (-s)) i : ℂ)) := by
    ext i k
    rcases i with i | i <;> rcases k with k | k <;>
      simp [B, Matrix.diagonal_apply, Matrix.fromBlocks]
  have hB : B.IsHermitian := by rw [hBdiag]; exact isHermitian_diagonal_of_self_adjoint _ (by ext i; simp [IsSelfAdjoint])
  obtain ⟨σ, hσ⟩ := hB.eigenvalues_eq_of_unitary_similarity_diagonal
    (U := (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)) (by simp)
    (f := Sum.elim s (-s)) (by simpa using hBdiag)
  have hr : B.charpoly.roots.map (RCLike.re : ℂ → ℝ) =
      Finset.univ.val.map (Sum.elim s (-s)) := by
    rw [hB.roots_charpoly_eq_eigenvalues, Multiset.map_map]
    simp only [Function.comp_def, RCLike.ofReal_re]
    conv_lhs => rw [← Multiset.map_univ_val_equiv σ]
    rw [Multiset.map_map]
    exact congrArg (fun f => Finset.univ.val.map f) hσ
  obtain ⟨τ, hτ⟩ := exists_sorting_equiv X
  have hs : Finset.univ.val.map s = (List.ofFn (singularValuesSorted X) : Multiset ℝ) := by
    rw [← Multiset.map_univ_val_equiv τ, Multiset.map_map]
    simp only [Function.comp_def, s, hτ, Fin.univ_val_map]
  have hn : Finset.univ.val.map (-s) =
      (List.ofFn (fun i => -singularValuesSorted X i.rev) : Multiset ℝ) := by
    calc
      Finset.univ.val.map (-s) = (Finset.univ.val.map s).map Neg.neg := by
        rw [Multiset.map_map]; rfl
      _ = (List.ofFn (singularValuesSorted X) : Multiset ℝ).map Neg.neg := by rw [hs]
      _ = Finset.univ.val.map (fun i => -singularValuesSorted X i) := by
        simp only [Fin.univ_val_map, Multiset.map_coe, List.map_ofFn, Function.comp_def]
      _ = Finset.univ.val.map (fun i : Fin (Fintype.card (Fin n)) => -singularValuesSorted X i.rev) := by
        conv_lhs => rw [← Multiset.map_univ_val_equiv Fin.revPerm]
        rw [Multiset.map_map]; rfl
      _ = _ := by rw [Fin.univ_val_map]
  have hr' : (fromBlocks 0 X Xᴴ (0 : Matrix (Fin n) (Fin n) ℂ)).charpoly.roots.map
      (RCLike.re : ℂ → ℝ) =
      ((List.ofFn (singularValuesSorted X) ++
        List.ofFn (fun i => -singularValuesSorted X i.rev)) : Multiset ℝ) := by
    rw [dilation_charpoly X]
    change B.charpoly.roots.map (RCLike.re : ℂ → ℝ) = _
    rw [hr]
    change ((Finset.univ.disjSum Finset.univ).val.map (Sum.elim s (-s))) = _
    rw [Finset.val_disjSum, Multiset.map_disjSum]
    change Finset.univ.val.map s + Finset.univ.val.map (-s) = _
    rw [hs, hn, Multiset.coe_add]
  have hsort : (List.ofFn (singularValuesSorted X) ++
      List.ofFn (fun i => -singularValuesSorted X i.rev)).SortedGE := by
    rw [List.sortedGE_append]
    refine ⟨(singularValuesSorted_antitone X).sortedGE_ofFn, ?_, ?_⟩
    · apply Antitone.sortedGE_ofFn
      intro i k hik
      exact neg_le_neg (singularValuesSorted_antitone X (Fin.rev_le_rev.mpr hik))
    · intro a ha b hb
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hb
      exact (neg_nonpos.mpr (singularValuesSorted_nonneg X _)).trans
        (singularValuesSorted_nonneg X _)
  have hlist : List.ofFn hD.eigenvalues₀ = List.ofFn (singularValuesSorted X) ++
      List.ofFn (fun i => -singularValuesSorted X i.rev) := by
    rw [← hD.sort_roots_charpoly_eq_eigenvalues₀, hr', Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simpa only [decide_eq_true_eq, ← List.sortedGE_iff_pairwise] using hsort
  have hj := congrArg (fun l : List ℝ => l[j.val]?) hlist
  have hsmall : j.val < n := by simpa using j.isLt
  have hbig : j.val < n + n := by omega
  simpa [hsmall, hbig, List.getElem?_append, List.length_ofFn] using hj

private theorem arithmetic_bound_real_trace {n : ℕ}
    (A X B : Matrix (Fin n) (Fin n) ℂ)
    (hW : (fromBlocks A X Xᴴ B).PosSemidef)
    (hA : A.trace = 1) (hB : B.trace = 1)
    (hAp : A.PosSemidef) (hBp : B.PosSemidef)
    (j : Fin (Fintype.card (Fin n))) :
    2 * singularValuesSorted X j ≤
      (hAp.1.add hBp.1).eigenvalues₀ j +
        1 - X.trace.re := by
  classical
  let W := fromBlocks A X Xᴴ B
  let D := fromBlocks (0 : Matrix (Fin n) (Fin n) ℂ) X Xᴴ 0
  let J := fromBlocks (1 : Matrix (Fin n) (Fin n) ℂ) 0 0
    (-1 : Matrix (Fin n) (Fin n) ℂ)
  let k : Fin (Fintype.card (Fin n ⊕ Fin n)) :=
    ⟨j.val, by simp only [Fintype.card_sum, Fintype.card_fin]; have hj := j.isLt; simp only [Fintype.card_fin] at hj; omega⟩
  have hD : D.IsHermitian := isHermitian_zero.fromBlocks rfl isHermitian_zero
  have h2D : ((2 : ℂ) • D).IsHermitian := hD.smul (by simp [IsSelfAdjoint])
  have hflip : (W - (2 : ℂ) • D).PosSemidef := by
    have h := hW.mul_mul_conjTranspose_same J
    convert h using 1
    dsimp [W, D, J]
    rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    ext i l
    rcases i with i | i <;> rcases l with l | l <;>
      simp [Matrix.fromBlocks, Matrix.sub_apply, Matrix.smul_apply] <;> ring
  have hfirst := eigenvalues_zero_mono_finite h2D hW.1 hflip k
  rw [eigenvalues_zero_smul_finite D hD 2 (by norm_num) h2D k,
    dilation_eigenvalues X hD j] at hfirst
  let Z := CFC.sqrt W
  have hZ : Zᴴ = Z := by
    simpa only [Matrix.star_eq_conjTranspose] using (CFC.sqrt_nonneg W).isSelfAdjoint.star_eq
  have hZZ : Z * Zᴴ = W := by
    rw [hZ]
    exact CFC.sqrt_mul_sqrt_self W hW.nonneg
  let U : Matrix (Fin n) (Fin n ⊕ Fin n) ℂ := Z.submatrix Sum.inl id
  let V : Matrix (Fin n) (Fin n ⊕ Fin n) ℂ := Z.submatrix Sum.inr id
  have hrows : fromRows U V = Z := by ext (i | i) l <;> rfl
  have hrows' : fromCols Uᴴ Vᴴ = Zᴴ := by
    rw [← conjTranspose_fromRows_eq_fromCols_conjTranspose, hrows]
  have hblocks : fromBlocks (U * Uᴴ) (U * Vᴴ) (V * Uᴴ) (V * Vᴴ) = W := by
    rw [← fromRows_mul_fromCols, hrows, hrows', hZZ]
  have hUU : U * Uᴴ = A := by
    ext i l
    exact congrArg (fun M => M (Sum.inl i) (Sum.inl l)) hblocks
  have hVV : V * Vᴴ = B := by
    ext i l
    exact congrArg (fun M => M (Sum.inr i) (Sum.inr l)) hblocks
  have hUV : U * Vᴴ = X := by
    ext i l
    exact congrArg (fun M => M (Sum.inl i) (Sum.inr l)) hblocks
  let L := Uᴴ * U + Vᴴ * V
  have hL : L.IsHermitian := (isHermitian_conjTranspose_mul_self U).add
    (isHermitian_conjTranspose_mul_self V)
  have hLL : Zᴴ * Z = L := by
    rw [← hrows, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows]
  have hWL : W.charpoly = L.charpoly := by
    rw [← hZZ, ← hLL]
    exact charpoly_mul_comm Z Zᴴ
  have hspec := eigenvalues_zero_eq_of_charpoly hW.1 hL hWL k
  let T := U + V
  let F := (((1 / 2 : ℝ) : ℂ)) • (Tᴴ * T)
  have hF : F.IsHermitian := (isHermitian_conjTranspose_mul_self T).smul (by simp [IsSelfAdjoint])
  let C := F + ((1 - X.trace.re : ℝ) : ℂ) • 1
  have hC : C.IsHermitian := hF.add (isHermitian_one.smul (by simp [IsSelfAdjoint]))
  have hcorr : (C - L).PosSemidef := by
    convert normalized_gram_trace_correction U V
      (by simpa only [hUU] using hA) (by simpa only [hVV] using hB) using 1
    ext i l
    simp only [T, C, F, L, hUV, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hsecond := eigenvalues_zero_mono_finite hL hC hcorr k
  rw [eigenvalues_zero_add_scalar_finite F hF (1 - X.trace.re) hC k,
    eigenvalues_zero_smul_finite (Tᴴ * T) (isHermitian_conjTranspose_mul_self T)
      (1 / 2) (by norm_num) hF k,
    rectangular_gram_eigenvalues T j] at hsecond
  have hrow : (((2 : ℂ) • (A + B)) - T * Tᴴ).PosSemidef := by
    simpa only [T, hUU, hVV] using row_gram_sum_comparison U V
  have hsum := hAp.1.add hBp.1
  have htwosum : ((2 : ℂ) • (A + B)).IsHermitian := hsum.smul (by simp [IsSelfAdjoint])
  have hthird := eigenvalues_zero_mono_finite (isHermitian_mul_conjTranspose_self T)
    htwosum hrow j
  rw [eigenvalues_zero_smul_finite (A + B) hsum 2 (by norm_num) htwosum j] at hthird
  rw [hspec] at hfirst
  change 2 * singularValuesSorted X j ≤ hsum.eigenvalues₀ j + 1 - X.trace.re
  linarith


/-- The normalized arithmetic singular-value bound includes the trace-overlap deficit. -/
theorem normalized_arithmetic_bound {n : ℕ} {A X B : Matrix (Fin n) (Fin n) ℂ}
    (hW : (fromBlocks A X Xᴴ B).PosSemidef) (hA : A.trace = 1) (hB : B.trace = 1)
    (hAp : A.PosSemidef) (hBp : B.PosSemidef)
    (j : Fin (Fintype.card (Fin n))) :
    2 * singularValuesSorted X j ≤
      (hAp.1.add hBp.1).eigenvalues₀ j + 1 - ‖X.trace‖ := by
  obtain ⟨z, hz, ht⟩ := exists_trace_phase X
  have h := arithmetic_bound_real_trace A (z • X) B
    (block_posSemidef_phase hW z hz) hA hB hAp hBp j
  rw [singularValuesSorted_phase X z hz j, ht, Complex.ofReal_re] at h
  exact h

end D5.S3.Quantum.Matrix.LinGProperty
