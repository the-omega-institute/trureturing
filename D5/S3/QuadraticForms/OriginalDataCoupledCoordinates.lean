/- GID: D5/S3/QuadraticForms/OriginalDataCoupledCoordinates
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/OriginalDataCoupledCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Projection]
   utility: none
   digest: The original observation lift has one coupled Darboux and two-block Williamson coordinate realization. -/

import D5.S3.QuadraticForms.OriginalDataSymplecticSplit
import D5.S3.QuadraticForms.PositiveDefiniteWilliamson
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Matrix.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.QuadraticForms.OriginalDataCoupledCoordinates

open Matrix Module
open D5.S3.QuadraticForms.SymplecticBasis
open D5.S3.QuadraticForms.OriginalDataSymplecticSplit
open D5.S3.QuadraticForms.PositiveDefiniteWilliamson

abbrev Modes (m : ℕ) := Fin m ⊕ Fin m
abbrev Blocks (k h : ℕ) := Modes k ⊕ Modes h
abbrev Jplus (m : ℕ) : Matrix (Modes m) (Modes m) ℝ := -Matrix.J (Fin m) ℝ

/-- Horizontal concatenation, with the visible columns first. -/
def columns {ι α β : Type*} (A : Matrix ι α ℝ) (B : Matrix ι β ℝ) :
    Matrix ι (α ⊕ β) ℝ := fun i => Sum.elim (A i) (B i)

abbrev matrix {α β : Type*} [Fintype α] [DecidableEq α]
    (e : (α → ℝ) ≃ₗ[ℝ] (β → ℝ)) : Matrix β α ℝ :=
  LinearMap.toMatrix' e.toLinearMap

/-- The specified concatenation of visible modes followed by hidden modes. -/
def modeConcat {n k h : ℕ} (hn : n = k + h) : Fin k ⊕ Fin h ≃ Fin n :=
  finSumFinEquiv.trans (finCongr hn.symm)

/-- Block coordinates (qv,pv,qh,ph) label global coordinates (qv,qh,pv,ph). -/
def blockToGlobal {n k h : ℕ} (hn : n = k + h) : Blocks k h ≃ Modes n :=
  (Equiv.sumSumSumComm (Fin k) (Fin k) (Fin h) (Fin h)).trans
    (Equiv.sumCongr (modeConcat hn) (modeConcat hn))

/-- The actual 0/1 permutation, with rows in block order and columns in global order. -/
def canonicalPi {n k h : ℕ} (hn : n = k + h) : Matrix (Blocks k h) (Modes n) ℝ :=
  (1 : Matrix (Modes n) (Modes n) ℝ).submatrix (blockToGlobal hn) id

/-- The same permutation as a linear equivalence of coordinate spaces. -/
def canonicalPiEquiv {n k h : ℕ} (hn : n = k + h) :
    (Modes n → ℝ) ≃ₗ[ℝ] (Blocks k h → ℝ) :=
  LinearEquiv.piCongrLeft' ℝ (fun _ : Modes n => ℝ) (blockToGlobal hn).symm

/-- All eight clauses share these witnesses. Matrices are standard-coordinate matrices;
`T`, `That`, and `R` are actual equivalences, not formal inverses of rectangular arrays. -/
structure CoupledCoordinates {n r : ℕ}
    (S : Matrix (Modes n) (Modes n) ℝ) (O : Matrix (Fin r) (Modes n) ℝ) where
  k : ℕ
  h : ℕ
  rank_eq : r = 2 * k
  modes_eq : n = k + h
  visible_pos : 0 < k
  hidden_pos : 0 < h
  Tv : Matrix (Modes n) (Modes k) ℝ
  Th : Matrix (Modes n) (Modes h) ℝ
  B : (Modes k → ℝ) ≃ₗ[ℝ] (Fin r → ℝ)
  T : (Blocks k h → ℝ) ≃ₗ[ℝ] (Modes n → ℝ)
  -- C1: the original lift and the original kernel, without alternative subspaces.
  tv_injective : Function.Injective Tv.mulVec
  th_injective : Function.Injective Th.mulVec
  tv_range : LinearMap.range Tv.mulVecLin =
    LinearMap.range (S⁻¹ * Oᵀ * (O * S⁻¹ * Oᵀ)⁻¹).mulVecLin
  th_range : LinearMap.range Th.mulVecLin = LinearMap.ker O.mulVecLin
  -- C2 and C3: observation, lift, and actual coordinate assembly.
  observation_visible : O * Tv = matrix B
  observation_hidden : O * Th = 0
  visible_lift : Tv = (S⁻¹ * Oᵀ * (O * S⁻¹ * Oᵀ)⁻¹) * matrix B
  t_apply : ∀ xv xh, T (Sum.elim xv xh) = Tv *ᵥ xv + Th *ᵥ xh
  t_matrix : matrix T = columns Tv Th
  observation_total : O * matrix T = columns (matrix B) 0
  -- C4: both cross blocks and the congruence for this same T.
  symplectic_visible : Tvᵀ * Jplus n * Tv = Jplus k
  symplectic_hidden : Thᵀ * Jplus n * Th = Jplus h
  symplectic_vh : Tvᵀ * Jplus n * Th = 0
  symplectic_hv : Thᵀ * Jplus n * Tv = 0
  symplectic_total : (matrix T)ᵀ * Jplus n * matrix T =
    fromBlocks (Jplus k) 0 0 (Jplus h)
  -- C5: the actual energies, including the inverse Gramian identity.
  energy_visible_pos : (Tvᵀ * S * Tv).PosDef
  energy_hidden_pos : (Thᵀ * S * Th).PosDef
  energy_vh : Tvᵀ * S * Th = 0
  energy_hv : Thᵀ * S * Tv = 0
  energy_visible_gram : Tvᵀ * S * Tv =
    (matrix B)ᵀ * (O * S⁻¹ * Oᵀ)⁻¹ * matrix B
  energy_total : (matrix T)ᵀ * S * matrix T =
    fromBlocks (Tvᵀ * S * Tv) 0 0 (Thᵀ * S * Th)
  -- C6: no arbitrary symplectic replacement is permitted for this permutation.
  pi_entry : ∀ i j, canonicalPi modes_eq i j =
    if blockToGlobal modes_eq i = j then 1 else 0
  pi_apply : ∀ z, canonicalPi modes_eq *ᵥ z =
    Sum.elim
      (Sum.elim (fun i => z (Sum.inl (modeConcat modes_eq (Sum.inl i))))
        (fun i => z (Sum.inr (modeConcat modes_eq (Sum.inl i)))))
      (Sum.elim (fun i => z (Sum.inl (modeConcat modes_eq (Sum.inr i))))
        (fun i => z (Sum.inr (modeConcat modes_eq (Sum.inr i)))))
  pi_equiv_matrix : matrix (canonicalPiEquiv modes_eq) = canonicalPi modes_eq
  pi_inverse_matrix : matrix (canonicalPiEquiv modes_eq).symm = (canonicalPi modes_eq)ᵀ
  pi_left_inverse : (canonicalPi modes_eq)ᵀ * canonicalPi modes_eq = 1
  pi_right_inverse : canonicalPi modes_eq * (canonicalPi modes_eq)ᵀ = 1
  pi_symplectic : (canonicalPi modes_eq)ᵀ *
    fromBlocks (Jplus k) 0 0 (Jplus h) * canonicalPi modes_eq = Jplus n
  permuted_symplectic : (matrix T * canonicalPi modes_eq)ᵀ * Jplus n *
    (matrix T * canonicalPi modes_eq) = Jplus n
  -- C7: universally quantified covectors, always transpose pullbacks.
  covectors : ∀ a, (matrix T)ᵀ *ᵥ (Oᵀ *ᵥ a) = Sum.elim ((matrix B)ᵀ *ᵥ a) 0
  permuted_covectors : ∀ a,
    (matrix T * canonicalPi modes_eq)ᵀ *ᵥ (Oᵀ *ᵥ a) =
    (canonicalPi modes_eq)ᵀ *ᵥ Sum.elim ((matrix B)ᵀ *ᵥ a) 0
  -- C8: the two actual Williamson outputs and one common final map.
  Wv : Matrix (Modes k) (Modes k) ℝ
  Wh : Matrix (Modes h) (Modes h) ℝ
  νv : Fin k → ℝ
  νh : Fin h → ℝ
  wv_mem : Wv ∈ Matrix.symplecticGroup (Fin k) ℝ
  wh_mem : Wh ∈ Matrix.symplecticGroup (Fin h) ℝ
  frequency_visible_pos : ∀ i, 0 < νv i
  frequency_hidden_pos : ∀ i, 0 < νh i
  wv_symplectic : Wvᵀ * Jplus k * Wv = Jplus k
  wh_symplectic : Whᵀ * Jplus h * Wh = Jplus h
  wv_energy : Wvᵀ * (Tvᵀ * S * Tv) * Wv =
    fromBlocks (diagonal νv) 0 0 (diagonal νv)
  wh_energy : Whᵀ * (Thᵀ * S * Th) * Wh =
    fromBlocks (diagonal νh) 0 0 (diagonal νh)
  Bhat : (Modes k → ℝ) ≃ₗ[ℝ] (Fin r → ℝ)
  That : (Blocks k h → ℝ) ≃ₗ[ℝ] (Modes n → ℝ)
  R : (Modes n → ℝ) ≃ₗ[ℝ] (Modes n → ℝ)
  bhat_matrix : matrix Bhat = matrix B * Wv
  that_matrix : matrix That = matrix T * fromBlocks Wv 0 0 Wh
  that_apply : ∀ xv xh, That (Sum.elim xv xh) =
    (Tv * Wv) *ᵥ xv + (Th * Wh) *ᵥ xh
  final_matrix : matrix R = matrix That * canonicalPi modes_eq
  that_visible_range : LinearMap.range (Tv * Wv).mulVecLin =
    LinearMap.range (S⁻¹ * Oᵀ * (O * S⁻¹ * Oᵀ)⁻¹).mulVecLin
  that_hidden_range : LinearMap.range (Th * Wh).mulVecLin = LinearMap.ker O.mulVecLin
  that_visible_lift : Tv * Wv =
    (S⁻¹ * Oᵀ * (O * S⁻¹ * Oᵀ)⁻¹) * matrix Bhat
  that_observation : O * matrix That = columns (matrix Bhat) 0
  that_symplectic : (matrix That)ᵀ * Jplus n * matrix That =
    fromBlocks (Jplus k) 0 0 (Jplus h)
  that_energy : (matrix That)ᵀ * S * matrix That =
    fromBlocks (fromBlocks (diagonal νv) 0 0 (diagonal νv)) 0 0
      (fromBlocks (diagonal νh) 0 0 (diagonal νh))
  final_symplectic : (matrix R)ᵀ * Jplus n * matrix R = Jplus n
  final_energy : (matrix R)ᵀ * S * matrix R =
    (canonicalPi modes_eq)ᵀ *
      fromBlocks (fromBlocks (diagonal νv) 0 0 (diagonal νv)) 0 0
        (fromBlocks (diagonal νh) 0 0 (diagonal νh)) * canonicalPi modes_eq
  that_covectors : ∀ a, (matrix That)ᵀ *ᵥ (Oᵀ *ᵥ a) =
    Sum.elim (Wvᵀ *ᵥ ((matrix B)ᵀ *ᵥ a)) 0
  final_covectors : ∀ a, (matrix R)ᵀ *ᵥ (Oᵀ *ᵥ a) =
    (canonicalPi modes_eq)ᵀ *ᵥ Sum.elim (Wvᵀ *ᵥ ((matrix B)ᵀ *ᵥ a)) 0

private theorem pairing_entry {ι α β : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (A : Matrix ι α ℝ) (B : Matrix ι β ℝ) (i : α) (j : β) :
    (Aᵀ * M * B) i j = M.toBilin' (fun t => A t i) (fun t => B t j) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.toBilin'_apply',
    Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

private theorem columns_congruence {ι α β : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (A : Matrix ι α ℝ) (B : Matrix ι β ℝ) :
    (columns A B)ᵀ * M * columns A B =
      fromBlocks (Aᵀ * M * A) (Aᵀ * M * B) (Bᵀ * M * A) (Bᵀ * M * B) := by
  ext (i | i) (j | j) <;> simp only [pairing_entry, columns,
    Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂]

/-- Original-data C1–C8, with all coordinates and both Williamson blocks coupled.
This source candidate has not been elaborated or kernel checked. -/
theorem original_data_coupled_coordinates
    {n r : ℕ}
    (S : Matrix (Modes n) (Modes n) ℝ)
    (O : Matrix (Fin r) (Modes n) ℝ)
    (K : Matrix (Fin r) (Fin r) ℝ)
    (hS : S.PosDef) (hO : Function.Surjective O.mulVec)
    (hclosed : O * (Jplus n * S) = K * O)
    (hr0 : 0 < r) (hrn : r < 2 * n) : Nonempty (CoupledCoordinates S O) := by
  classical
  let P := O * S⁻¹ * Oᵀ
  let L := S⁻¹ * Oᵀ * P⁻¹
  let U := LinearMap.range L.mulVecLin
  let V := LinearMap.ker O.mulVecLin
  obtain ⟨hP, hOL, ⟨e, he, hei⟩, hcompl, horth, hAltU, hAltV,
      hndU, hndV, henergy, hposU, hposV, hdimU, hdim, hK, hJr, hAL,
      k, h, bU, bV, hbU, hbV, hr, hn⟩ :=
    original_data_symplectic_retract S O K hS hO hclosed
  have hk : 0 < k := by omega
  have hh : 0 < h := by omega
  let Tv : Matrix (Modes n) (Modes k) ℝ := fun i j => (bU j : Modes n → ℝ) i
  let Th : Matrix (Modes n) (Modes h) ℝ := fun i j => (bV j : Modes n → ℝ) i
  have hTv : ∀ x, Tv *ᵥ x = (bU.equivFun.symm x : Modes n → ℝ) := by
    intro x
    ext i
    simp [Tv, Basis.equivFun_symm_apply, Matrix.mulVec, dotProduct, mul_comm]
  have hTh : ∀ x, Th *ᵥ x = (bV.equivFun.symm x : Modes n → ℝ) := by
    intro x
    ext i
    simp [Th, Basis.equivFun_symm_apply, Matrix.mulVec, dotProduct, mul_comm]
  have hTvi : Function.Injective Tv.mulVec := by
    intro x y hxy
    apply bU.equivFun.symm.injective
    apply Subtype.ext
    simpa only [hTv] using hxy
  have hThi : Function.Injective Th.mulVec := by
    intro x y hxy
    apply bV.equivFun.symm.injective
    apply Subtype.ext
    simpa only [hTh] using hxy
  have hTvr : LinearMap.range Tv.mulVecLin = U := by
    ext u
    constructor
    · rintro ⟨x, rfl⟩
      change Tv *ᵥ x ∈ U
      rw [hTv]; exact (bU.equivFun.symm x).property
    · intro hu
      refine ⟨bU.equivFun ⟨u, hu⟩, ?_⟩
      change Tv *ᵥ bU.equivFun ⟨u, hu⟩ = u
      rw [hTv, bU.equivFun.symm_apply_apply]
  have hThr : LinearMap.range Th.mulVecLin = V := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      change Th *ᵥ x ∈ V
      rw [hTh]; exact (bV.equivFun.symm x).property
    · intro hv
      refine ⟨bV.equivFun ⟨v, hv⟩, ?_⟩
      change Th *ᵥ bV.equivFun ⟨v, hv⟩ = v
      rw [hTh, bV.equivFun.symm_apply_apply]
  let B : (Modes k → ℝ) ≃ₗ[ℝ] (Fin r → ℝ) := bU.equivFun.symm.trans e
  have hB : O * Tv = matrix B := by
    ext i j
    change (O *ᵥ Tv.col j) i = _
    have hx := he (bU.equivFun.symm (Pi.single j 1))
    simpa only [B, matrix, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe,
      LinearEquiv.trans_apply, ← hTv, Matrix.mulVec_mulVec,
      Matrix.mulVec_single_one] using (congrArg (fun z => z i) hx).symm
  have hOTh : O * Th = 0 := by
    ext i j
    have hz : O *ᵥ (bV j : Modes n → ℝ) = 0 := (bV j).property
    exact congrArg (fun z => z i) hz
  have hLB : Tv = L * matrix B := by
    ext i j
    have hx := hei (B (Pi.single j 1))
    have hv : (bU.equivFun.symm (Pi.single j 1) : Modes n → ℝ) = Tv *ᵥ Pi.single j 1 :=
      (hTv _).symm
    have hcancel : e.symm (B (Pi.single j 1)) = bU.equivFun.symm (Pi.single j 1) := by
      simp only [B, LinearEquiv.trans_apply, e.symm_apply_apply]
    rw [hcancel, hv] at hx
    have hx' := congrArg (fun z => z i) hx
    calc
      Tv i j = (Tv *ᵥ Pi.single j 1) i := by
        simp only [Matrix.mulVec_single_one, Matrix.col_apply]
      _ = (L *ᵥ B (Pi.single j 1)) i := by
        simpa only [Matrix.col_apply] using hx'
      _ = (L *ᵥ ((matrix B) *ᵥ Pi.single j 1)) i := by
        change (L *ᵥ (B.toLinearMap (Pi.single j 1))) i =
          (L *ᵥ ((matrix B) *ᵥ Pi.single j 1)) i
        rw [LinearMap.toMatrix'_mulVec]
      _ = ((L * matrix B) *ᵥ Pi.single j 1) i := by
        rw [Matrix.mulVec_mulVec]
      _ = (L * matrix B) i j := by
        simpa only [Matrix.mulVec_single_one, Matrix.col_apply]
  let T : (Blocks k h → ℝ) ≃ₗ[ℝ] (Modes n → ℝ) :=
    (LinearEquiv.sumArrowLequivProdArrow (Modes k) (Modes h) ℝ ℝ).trans
      ((bU.equivFun.symm.prodCongr bV.equivFun.symm).trans
        (U.prodEquivOfIsCompl V hcompl))
  have hT : ∀ xv xh, T (Sum.elim xv xh) = Tv *ᵥ xv + Th *ᵥ xh := by
    intro xv xh
    change (bU.equivFun.symm xv : Modes n → ℝ) +
      (bV.equivFun.symm xh : Modes n → ℝ) = _
    rw [hTv, hTh]
  have hTm : matrix T = columns Tv Th := by
    ext i j
    rw [matrix, LinearMap.toMatrix'_apply]
    cases j with
    | inl j =>
      have hs : (Pi.single (Sum.inl j) 1 : Blocks k h → ℝ) =
          Sum.elim (Pi.single j 1) (0 : Modes h → ℝ) := by
        ext (a | a) <;> simp [Pi.single_apply]
      rw [hs]
      change (T (Sum.elim (Pi.single j 1) (0 : Modes h → ℝ))) i = _
      rw [hT]
      simp [columns]
    | inr j =>
      have hs : (Pi.single (Sum.inr j) 1 : Blocks k h → ℝ) =
          Sum.elim (0 : Modes k → ℝ) (Pi.single j 1) := by
        ext (a | a) <;> simp [Pi.single_apply]
      rw [hs]
      change (T (Sum.elim (0 : Modes k → ℝ) (Pi.single j 1))) i = _
      rw [hT]
      simp [columns]
  have hOT : O * matrix T = columns (matrix B) 0 := by
    rw [hTm]
    ext i (j | j)
    · exact congrArg (fun M => M i j) hB
    · exact congrArg (fun M => M i j) hOTh
  -- The Darboux supplier has +delta in the inl/inr block. This fixes q then p.
  have darboux : ∀ {m : ℕ} (W : Submodule ℝ (Modes n → ℝ))
      (b : Basis (Modes m) ℝ W),
      ((Jplus n).toBilin'.restrict W).IsAlt →
      IsSymplecticBasis ((Jplus n).toBilin'.restrict W) b →
      (let A : Matrix (Modes n) (Modes m) ℝ :=
        fun i j => (b j : Modes n → ℝ) i
       Aᵀ * Jplus n * A = Jplus m) := by
    intro m W b ha hb
    let A : Matrix (Modes n) (Modes m) ℝ := fun i j => (b j : Modes n → ℝ) i
    change Aᵀ * Jplus n * A = Jplus m
    have hp : ∀ i j, (Jplus n).toBilin' (b (Sum.inl i)) (b (Sum.inr j)) =
        if i = j then 1 else 0 := by
      intro i j
      by_cases hij : i = j
      · subst j; simpa using hb.inl_inr_self i
      · simpa [hij] using hb.inl_inr_of_ne i j hij
    have hj : Jplus m = fromBlocks (0 : Matrix (Fin m) (Fin m) ℝ) 1 (-1) 0 := by
      ext (i | i) (j | j) <;> simp [Jplus, Matrix.J, Matrix.fromBlocks]
    ext (i | i) (j | j)
    · rw [pairing_entry, hj, Matrix.fromBlocks_apply₁₁]
      exact hb.inl_inl i j
    · rw [pairing_entry, hj, Matrix.fromBlocks_apply₁₂, Matrix.one_apply]
      exact hp i j
    · rw [pairing_entry, hj, Matrix.fromBlocks_apply₂₁, Matrix.neg_apply, Matrix.one_apply]
      have hz := ha.neg_eq (b (Sum.inl j)) (b (Sum.inr i))
      change -(Jplus n).toBilin' (b (Sum.inl j)) (b (Sum.inr i)) =
        (Jplus n).toBilin' (b (Sum.inr i)) (b (Sum.inl j)) at hz
      rw [hp] at hz
      simpa only [eq_comm] using hz.symm
    · rw [pairing_entry, hj, Matrix.fromBlocks_apply₂₂]
      exact hb.inr_inr i j
  have hJv : Tvᵀ * Jplus n * Tv = Jplus k := darboux U bU hAltU hbU
  have hJh : Thᵀ * Jplus n * Th = Jplus h := darboux V bV hAltV hbV
  have hJvh : Tvᵀ * Jplus n * Th = 0 := by
    ext i j
    rw [pairing_entry]
    have hv : (bV j : Modes n → ℝ) ∈ (Jplus n).toBilin'.orthogonal U :=
      horth.symm ▸ (bV j).property
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hv) _ (bU i).property
  have hJT : (Jplus n)ᵀ = -Jplus n := by simp [Jplus]
  have hJhv : Thᵀ * Jplus n * Tv = 0 := by
    have hz := congrArg Matrix.transpose hJvh
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hJT,
      Matrix.transpose_zero] at hz
    have hz' : Thᵀ * (Matrix.J (Fin n) ℝ * Tv) = 0 := by
      simpa only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, neg_neg] using hz
    have hz'' : -(Thᵀ * (Matrix.J (Fin n) ℝ * Tv)) = 0 := neg_eq_zero.mpr hz'
    simpa only [Jplus, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc] using hz''
  have hTJ : (matrix T)ᵀ * Jplus n * matrix T =
      fromBlocks (Jplus k) 0 0 (Jplus h) := by
    rw [hTm, columns_congruence, hJv, hJh, hJvh, hJhv]
  have hSv : (Tvᵀ * S * Tv).PosDef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hS.conjTranspose_mul_mul_same (B := Tv) hTvi
  have hSh : (Thᵀ * S * Th).PosDef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hS.conjTranspose_mul_mul_same (B := Th) hThi
  have hSvh : Tvᵀ * S * Th = 0 := by
    ext i j
    rw [pairing_entry]
    exact henergy (bU i) (bU i).property (bV j) (bV j).property
  have hST : Sᵀ = S := by simpa using hS.1.eq
  have hShv : Thᵀ * S * Tv = 0 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose,
      hST, Matrix.transpose_zero, Matrix.mul_assoc] using congrArg Matrix.transpose hSvh
  have hTS : (matrix T)ᵀ * S * matrix T =
      fromBlocks (Tvᵀ * S * Tv) 0 0 (Thᵀ * S * Th) := by
    rw [hTm, columns_congruence, hSvh, hShv]
  have hPT : Pᵀ = P := by
    simp only [P, Matrix.transpose_mul, Matrix.transpose_nonsing_inv,
      Matrix.transpose_transpose, hST, Matrix.mul_assoc]
  have hSiS : S⁻¹ * S = 1 :=
    Matrix.nonsing_inv_mul S (S.isUnit_iff_isUnit_det.mp hS.isUnit)
  have hLtS : Lᵀ * S = P⁻¹ * O := by
    simp only [L, Matrix.transpose_mul, Matrix.transpose_nonsing_inv,
      hPT, hST, Matrix.transpose_transpose, Matrix.mul_assoc, hSiS, Matrix.mul_one]
  have hLtSL : Lᵀ * S * L = P⁻¹ := by
    rw [hLtS, Matrix.mul_assoc, hOL, Matrix.mul_one]
  have hSgram : Tvᵀ * S * Tv = (matrix B)ᵀ * P⁻¹ * matrix B := by
    conv_lhs => rw [hLB, Matrix.transpose_mul]
    calc
      (matrix B)ᵀ * Lᵀ * S * (L * matrix B) =
          (matrix B)ᵀ * (Lᵀ * S * L) * matrix B := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hLtSL]
  -- The actual finite-index permutation. It is orthogonal because it reindexes 1.
  let eidx := blockToGlobal hn
  let PiMat := canonicalPi hn
  have hPientry : ∀ i j, PiMat i j = if eidx i = j then 1 else 0 := by
    intro i j; rfl
  have hPivec : ∀ z, PiMat *ᵥ z = z ∘ eidx := by
    intro z
    ext i
    simp [PiMat, canonicalPi, eidx, Matrix.mulVec, dotProduct, Matrix.one_apply]
  have hPim : matrix (canonicalPiEquiv hn) = PiMat := by
    ext i j
    change (Pi.single (M := fun _ : Modes n => ℝ) j (1 : ℝ)) (eidx i) =
      (1 : Matrix (Modes n) (Modes n) ℝ) (eidx i) j
    simp only [Pi.single_apply, Matrix.one_apply, eq_comm]
  have hPiinv : matrix (canonicalPiEquiv hn).symm = PiMatᵀ := by
    ext i j
    change (Equiv.piCongrLeft' (fun _ : Modes n => ℝ) eidx.symm).symm
      (Pi.single (M := fun _ : Blocks k h => ℝ) j (1 : ℝ)) i =
        (1 : Matrix (Modes n) (Modes n) ℝ) (eidx j) i
    rw [Equiv.piCongrLeft'_symm]
    change (Pi.single (M := fun _ : Blocks k h => ℝ) j (1 : ℝ)) (eidx.symm i) =
      (1 : Matrix (Modes n) (Modes n) ℝ) (eidx j) i
    by_cases hij : eidx j = i
    · have hs : eidx.symm i = j := by rw [← hij, eidx.symm_apply_apply]
      simp [Pi.single_apply, Matrix.one_apply, hij, hs]
    · have hs : eidx.symm i ≠ j := by
        intro heq
        apply hij
        rw [← heq, eidx.apply_symm_apply]
      simp [Pi.single_apply, Matrix.one_apply, hij, hs, Ne.symm hs]
  have hPil : PiMatᵀ * PiMat = 1 := by
    change (1 : Matrix (Modes n) (Modes n) ℝ)ᵀ.submatrix id eidx *
      (1 : Matrix (Modes n) (Modes n) ℝ).submatrix eidx id = 1
    rw [Matrix.transpose_one, Matrix.submatrix_mul_equiv, Matrix.one_mul, Matrix.submatrix_id_id]
  have hPir : PiMat * PiMatᵀ = 1 := by
    change (1 : Matrix (Modes n) (Modes n) ℝ).submatrix eidx (Equiv.refl _) *
      (1 : Matrix (Modes n) (Modes n) ℝ)ᵀ.submatrix (Equiv.refl _) eidx = 1
    rw [Matrix.transpose_one, Matrix.submatrix_mul_equiv, Matrix.one_mul, Matrix.submatrix_one_equiv]
  have hJreindex : (Jplus n).submatrix eidx eidx =
      fromBlocks (Jplus k) 0 0 (Jplus h) := by
    ext ((i | i) | (i | i)) ((j | j) | (j | j)) <;>
      simp [eidx, blockToGlobal, Equiv.sumSumSumComm, Equiv.sumCongr_apply, Jplus, Matrix.J,
        Matrix.fromBlocks, Matrix.one_apply, Equiv.apply_eq_iff_eq]
  have hPiJ : PiMatᵀ * fromBlocks (Jplus k) 0 0 (Jplus h) * PiMat = Jplus n := by
    rw [← hJreindex]
    change (1 : Matrix (Modes n) (Modes n) ℝ)ᵀ.submatrix id eidx *
      (Jplus n).submatrix eidx eidx *
      (1 : Matrix (Modes n) (Modes n) ℝ).submatrix eidx id = Jplus n
    rw [Matrix.transpose_one, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
      Matrix.one_mul, Matrix.mul_one, Matrix.submatrix_id_id]
  have hTPiMatJ : (matrix T * PiMat)ᵀ * Jplus n * (matrix T * PiMat) = Jplus n := by
    calc
      _ = PiMatᵀ * ((matrix T)ᵀ * Jplus n * matrix T) * PiMat := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Jplus n := by rw [hTJ, hPiJ]
  have hcov : ∀ a, (matrix T)ᵀ *ᵥ (Oᵀ *ᵥ a) = Sum.elim ((matrix B)ᵀ *ᵥ a) 0 := by
    intro a
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hOT]
    ext (i | i) <;> simp [columns, Matrix.mulVec, dotProduct]
  have hcovPiMat : ∀ a, (matrix T * PiMat)ᵀ *ᵥ (Oᵀ *ᵥ a) =
      PiMatᵀ *ᵥ Sum.elim ((matrix B)ᵀ *ᵥ a) 0 := by
    intro a
    rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec, hcov]
  -- The published theorem is applied to exactly the C5 matrices, separately.
  obtain ⟨Wv, νv, hWv, hνv, hWvJ, hWvS⟩ := positive_definite_williamson (Tvᵀ * S * Tv) hSv
  obtain ⟨Wh, νh, hWh, hνh, hWhJ, hWhS⟩ := positive_definite_williamson (Thᵀ * S * Th) hSh
  have hWvJp : Wvᵀ * Jplus k * Wv = Jplus k := by
    simpa only [Matrix.mul_neg, Matrix.neg_mul] using congrArg Neg.neg hWvJ
  have hWhJp : Whᵀ * Jplus h * Wh = Jplus h := by
    simpa only [Matrix.mul_neg, Matrix.neg_mul] using congrArg Neg.neg hWhJ
  have hWvu : IsUnit Wv := (Matrix.isUnit_iff_isUnit_det Wv).mpr
    (SymplecticGroup.symplectic_det hWv)
  have hWhu : IsUnit Wh := (Matrix.isUnit_iff_isUnit_det Wh).mpr
    (SymplecticGroup.symplectic_det hWh)
  let ev : (Modes k → ℝ) ≃ₗ[ℝ] (Modes k → ℝ) :=
    LinearEquiv.ofBijective Wv.mulVecLin
      ⟨Matrix.mulVec_injective_iff_isUnit.mpr hWvu,
        Matrix.mulVec_surjective_iff_isUnit.mpr hWvu⟩
  let eh : (Modes h → ℝ) ≃ₗ[ℝ] (Modes h → ℝ) :=
    LinearEquiv.ofBijective Wh.mulVecLin
      ⟨Matrix.mulVec_injective_iff_isUnit.mpr hWhu,
        Matrix.mulVec_surjective_iff_isUnit.mpr hWhu⟩
  let split := LinearEquiv.sumArrowLequivProdArrow (Modes k) (Modes h) ℝ ℝ
  let ew : (Blocks k h → ℝ) ≃ₗ[ℝ] (Blocks k h → ℝ) :=
    split.trans ((ev.prodCongr eh).trans split.symm)
  let W := fromBlocks Wv 0 0 Wh
  have hew : ∀ x, ew x = W *ᵥ x := by
    intro x
    change Sum.elim (Wv *ᵥ (x ∘ Sum.inl)) (Wh *ᵥ (x ∘ Sum.inr)) = W *ᵥ x
    simp only [W, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, add_zero, zero_add]
  have hewm : matrix ew = W := by
    ext i j
    simp only [matrix, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe, hew,
      Matrix.mulVec_single_one]
    rfl
  let Bhat := ev.trans B
  let That := ew.trans T
  let R := (canonicalPiEquiv hn).trans That
  have hBhat : matrix Bhat = matrix B * Wv := by
    ext i j
    simp only [matrix, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe,
      Bhat, LinearEquiv.trans_apply]
    change B (Wv *ᵥ Pi.single j 1) i = (matrix B * Wv).col j i
    rw [← Matrix.mulVec_single_one, ← Matrix.mulVec_mulVec]
    exact congrArg (fun z => z i)
      (LinearMap.toMatrix'_mulVec B.toLinearMap (Wv *ᵥ Pi.single j 1)).symm
  have hThat : matrix That = matrix T * W := by
    change LinearMap.toMatrix' (T.toLinearMap.comp ew.toLinearMap) = _
    rw [LinearMap.toMatrix'_comp]
    change matrix T * matrix ew = matrix T * W
    rw [hewm]
  have hR : matrix R = matrix That * PiMat := by
    change LinearMap.toMatrix' (That.toLinearMap.comp (canonicalPiEquiv hn).toLinearMap) = _
    rw [LinearMap.toMatrix'_comp]
    change matrix That * matrix (canonicalPiEquiv hn) = matrix That * PiMat
    rw [hPim]
  have hThatapply : ∀ xv xh, That (Sum.elim xv xh) =
      (Tv * Wv) *ᵥ xv + (Th * Wh) *ᵥ xh := by
    intro xv xh
    change T (ew (Sum.elim xv xh)) = _
    rw [hew]
    simp only [W, Matrix.fromBlocks_mulVec, Function.comp_def, Sum.elim_inl,
      Sum.elim_inr, Matrix.zero_mulVec, add_zero, zero_add, hT, Matrix.mulVec_mulVec]
  have hThatvr : LinearMap.range (Tv * Wv).mulVecLin = U := by
    rw [Matrix.mulVecLin_mul]
    change LinearMap.range (Tv.mulVecLin.comp ev.toLinearMap) = U
    rw [LinearEquiv.range_comp, hTvr]
  have hThathr : LinearMap.range (Th * Wh).mulVecLin = V := by
    rw [Matrix.mulVecLin_mul]
    change LinearMap.range (Th.mulVecLin.comp eh.toLinearMap) = V
    rw [LinearEquiv.range_comp, hThr]
  have hThatlift : Tv * Wv = L * matrix Bhat := by
    rw [hBhat, hLB, Matrix.mul_assoc]
  have hThatO : O * matrix That = columns (matrix Bhat) 0 := by
    rw [hThat, ← Matrix.mul_assoc, hOT, hBhat]
    ext i (j | j) <;>
      simp [columns, W, Matrix.mul_apply, Matrix.fromBlocks, Fintype.sum_sum_type]
  have hThatJ : (matrix That)ᵀ * Jplus n * matrix That =
      fromBlocks (Jplus k) 0 0 (Jplus h) := by
    calc
      _ = Wᵀ * ((matrix T)ᵀ * Jplus n * matrix T) * W := by
        rw [hThat]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = fromBlocks (Jplus k) 0 0 (Jplus h) := by
        rw [hTJ]
        simp only [W, Matrix.fromBlocks_transpose, Matrix.transpose_zero,
          Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
          zero_add, add_zero, hWvJp, hWhJp]
  have hThatS : (matrix That)ᵀ * S * matrix That =
      fromBlocks (fromBlocks (diagonal νv) 0 0 (diagonal νv)) 0 0
        (fromBlocks (diagonal νh) 0 0 (diagonal νh)) := by
    calc
      _ = Wᵀ * ((matrix T)ᵀ * S * matrix T) * W := by
        rw [hThat]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by
        rw [hTS]
        simp only [W, Matrix.fromBlocks_transpose, Matrix.transpose_zero,
          Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero,
          zero_add, add_zero, hWvS, hWhS]
  have hRJ : (matrix R)ᵀ * Jplus n * matrix R = Jplus n := by
    calc
      _ = PiMatᵀ * ((matrix That)ᵀ * Jplus n * matrix That) * PiMat := by
        rw [hR]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Jplus n := by rw [hThatJ, hPiJ]
  have hRS : (matrix R)ᵀ * S * matrix R =
      PiMatᵀ * fromBlocks (fromBlocks (diagonal νv) 0 0 (diagonal νv)) 0 0
        (fromBlocks (diagonal νh) 0 0 (diagonal νh)) * PiMat := by
    calc
      _ = PiMatᵀ * ((matrix That)ᵀ * S * matrix That) * PiMat := by
        rw [hR]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hThatS]
  have hThatcov : ∀ a, (matrix That)ᵀ *ᵥ (Oᵀ *ᵥ a) =
      Sum.elim (Wvᵀ *ᵥ ((matrix B)ᵀ *ᵥ a)) 0 := by
    intro a
    rw [hThat, Matrix.transpose_mul, ← Matrix.mulVec_mulVec, hcov]
    simp only [W, Matrix.fromBlocks_transpose, Matrix.transpose_zero,
      Matrix.fromBlocks_mulVec, Function.comp_def, Sum.elim_inl, Sum.elim_inr,
      Matrix.mulVec_zero, Matrix.zero_mulVec, add_zero, zero_add]
  have hRcov : ∀ a, (matrix R)ᵀ *ᵥ (Oᵀ *ᵥ a) =
      PiMatᵀ *ᵥ Sum.elim (Wvᵀ *ᵥ ((matrix B)ᵀ *ᵥ a)) 0 := by
    intro a
    rw [hR, Matrix.transpose_mul, ← Matrix.mulVec_mulVec, hThatcov]
  refine ⟨{
    k := k, h := h, rank_eq := hr, modes_eq := hn,
    visible_pos := hk, hidden_pos := hh, Tv := Tv, Th := Th, B := B, T := T,
    tv_injective := hTvi, th_injective := hThi, tv_range := hTvr, th_range := hThr,
    observation_visible := hB, observation_hidden := hOTh, visible_lift := hLB,
    t_apply := hT, t_matrix := hTm, observation_total := hOT,
    symplectic_visible := hJv, symplectic_hidden := hJh,
    symplectic_vh := hJvh, symplectic_hv := hJhv, symplectic_total := hTJ,
    energy_visible_pos := hSv, energy_hidden_pos := hSh,
    energy_vh := hSvh, energy_hv := hShv, energy_visible_gram := hSgram,
    energy_total := hTS, pi_entry := hPientry, pi_apply := ?_,
    pi_equiv_matrix := hPim, pi_inverse_matrix := hPiinv,
    pi_left_inverse := hPil, pi_right_inverse := hPir,
    pi_symplectic := hPiJ, permuted_symplectic := hTPiMatJ,
    covectors := hcov, permuted_covectors := hcovPiMat,
    Wv := Wv, Wh := Wh, νv := νv, νh := νh, wv_mem := hWv, wh_mem := hWh,
    frequency_visible_pos := hνv, frequency_hidden_pos := hνh,
    wv_symplectic := hWvJp, wh_symplectic := hWhJp,
    wv_energy := hWvS, wh_energy := hWhS,
    Bhat := Bhat, That := That, R := R,
    bhat_matrix := hBhat, that_matrix := hThat, that_apply := hThatapply,
    final_matrix := hR, that_visible_range := hThatvr, that_hidden_range := hThathr,
    that_visible_lift := hThatlift, that_observation := hThatO,
    that_symplectic := hThatJ, that_energy := hThatS,
    final_symplectic := hRJ, final_energy := hRS,
    that_covectors := hThatcov, final_covectors := hRcov }⟩
  intro z
  rw [hPivec]
  ext ((i | i) | (i | i)) <;> rfl

end D5.S3.QuadraticForms.OriginalDataCoupledCoordinates
