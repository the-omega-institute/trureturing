/- GID: D5/S3/Quantum/Recovery/LocalCompression/JointMarginalRank
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/LocalCompression/JointMarginalRank
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The least marginal rank on a positive matrix's joint unitary orbit. -/

import D5.S3.Quantum.Information.PartialTrace.Isometries
import D5.S3.Quantum.ProcessReconstruction.ReconstructionChannels

/-!
The lower bound counts the joint rows above the support of the marginal.
For attainment, place the nonzero eigenvalues into successive product-basis
rows. For related spectral arguments see Reeb–Wolf, arXiv:1306.4352v3,
§3.3, and Fan, DOI 10.1073/pnas.35.11.652, Theorem 1.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Recovery.LocalCompression.JointMarginalRank

open Matrix
open scoped Kronecker BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceRight partialTraceRight_posSemidef)
open D5.S3.Quantum.Measurement.AnticoherenceSpinCovariance (partialTrace_isometries)

private theorem rank_conjugate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitaryGroup ι ℂ) (X : Matrix ι ι ℂ) :
    ((U : Matrix ι ι ℂ) * X * (U : Matrix ι ι ℂ)ᴴ).rank = X.rank := by
  simp only [← Matrix.star_eq_conjTranspose, ← Unitary.coe_star]
  exact (Matrix.rank_mul_eq_left_of_isUnit_det _ _
    ((Matrix.isUnit_iff_isUnit_det _).mp (Unitary.isUnit_coe (U := star U)))).trans
    (Matrix.rank_mul_eq_right_of_isUnit_det _ _
      ((Matrix.isUnit_iff_isUnit_det _).mp (Unitary.isUnit_coe (U := U))))

set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem rank_le_product {m e : ℕ} (X : Matrix (Fin m × Fin e) (Fin m × Fin e) ℂ)
    (hX : X.PosSemidef) : X.rank ≤ (partialTraceRight X).rank * e := by
  classical
  let M := partialTraceRight X
  let hM := (partialTraceRight_posSemidef hX).isHermitian
  let V := star hM.eigenvectorUnitary
  let W : Matrix (Fin m × Fin e) (Fin m × Fin e) ℂ :=
    (V : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ (1 : Matrix (Fin e) (Fin e) ℂ)
  have hW : W ∈ unitaryGroup (Fin m × Fin e) ℂ := by
    rw [mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    dsimp only [W]
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
    rw [show (V : Matrix (Fin m) (Fin m) ℂ) * (V : Matrix (Fin m) (Fin m) ℂ)ᴴ = 1
      from Unitary.coe_mul_star_self V]
    simp
  let Y := W * X * Wᴴ
  have hY : Y.PosSemidef := hX.mul_mul_conjTranspose_same W
  have htrace : partialTraceRight Y = diagonal (fun i => (hM.eigenvalues i : ℂ)) := by
    have h := partialTrace_isometries (V : Matrix (Fin m) (Fin m) ℂ)
      (1 : Matrix (Fin e) (Fin e) ℂ) (by simp) X
    change partialTraceRight Y = (V : Matrix _ _ ℂ) * M * (V : Matrix _ _ ℂ)ᴴ at h
    exact h.trans hM.conjStarAlgAut_star_eigenvectorUnitary
  let s : Finset (Fin m) := Finset.univ.filter fun i => hM.eigenvalues i ≠ 0
  have hs : s.card = M.rank := by
    rw [hM.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  have hrows : Function.support Y.row ⊆
      (↑(s ×ˢ (Finset.univ : Finset (Fin e))) : Set (Fin m × Fin e)) := by
    rw [Function.support_subset_iff']
    intro p hp
    have hp₀ : hM.eigenvalues p.1 = 0 := by simpa [s] using hp
    have hm₀ : (∑ j : Fin e, Y (p.1, j) (p.1, j)) = 0 := by
      change partialTraceRight Y p.1 p.1 = 0
      simp [htrace, hp₀]
    have hDiag : Y p p = 0 := by
      have hr : (∑ j : Fin e, (Y (p.1, j) (p.1, j)).re) = 0 := by
        simpa using congrArg Complex.re hm₀
      have hnonneg (j : Fin e) (_ : j ∈ Finset.univ) :
          0 ≤ (Y (p.1,j) (p.1,j)).re :=
        Complex.nonneg_iff.mp (hY.diag_nonneg (i := (p.1,j))) |>.1
      have he := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hr p.2 (Finset.mem_univ _)
      exact Complex.ext he (Complex.nonneg_iff.mp (hY.diag_nonneg (i := p))).2.symm
    have hk : Y *ᵥ Pi.single p 1 = 0 := hY.dotProduct_mulVec_zero_iff.mp (by
      simp [Pi.star_single, Matrix.mulVec_single_one, single_dotProduct, hDiag])
    funext q
    have hcol := congrFun hk q
    simp only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.zero_apply] at hcol
    have hsymm := congrArg (fun A : Matrix _ _ ℂ => A p q) hY.isHermitian.eq
    simpa [Matrix.conjTranspose_apply, hcol] using hsymm.symm
  calc
    X.rank = Y.rank := (rank_conjugate (⟨W, hW⟩ : unitaryGroup _ ℂ) X).symm
    _ ≤ (s ×ˢ (Finset.univ : Finset (Fin e))).card := Matrix.rank_le_card_of_support_subset _ _ hrows
    _ = M.rank * e := by simp [hs]

private theorem conj_perm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) (Z : Matrix ι ι ℂ) :
    σ.permMatrix ℂ * Z * (σ.permMatrix ℂ)ᴴ = Z.submatrix σ σ := by
  rw [Matrix.conjTranspose_permMatrix]
  change σ.toPEquiv.toMatrix * Z * (σ⁻¹).toPEquiv.toMatrix = _
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  rfl

/-- For a positive semidefinite matrix on a finite product, the exact unitary
minimum is the ceiling of its rank divided by the size of the traced factor. -/
theorem minimum {m e : ℕ} (he : 0 < e)
    (X : Matrix (Fin m × Fin e) (Fin m × Fin e) ℂ) (hX : X.PosSemidef) :
    IsLeast (Set.range (fun U : unitaryGroup (Fin m × Fin e) ℂ =>
      (partialTraceRight ((U : Matrix _ _ ℂ) * X * (U : Matrix _ _ ℂ)ᴴ)).rank))
      ((X.rank + e - 1) / e) := by
  classical
  let k := X.rank
  let r := (k + e - 1) / e
  have hr (d : ℕ) : r ≤ d ↔ k ≤ d * e := by
    change (k + e - 1) / e ≤ d ↔ _
    rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul he, Nat.succ_mul]
    omega
  have hrk : k ≤ r * e := (hr r).mp le_rfl
  have hkm : k ≤ m * e := by simpa [k] using Matrix.rank_le_card_height X
  have hrm : r ≤ m := (hr m).mpr hkm
  have hlower (U : unitaryGroup (Fin m × Fin e) ℂ) :
      r ≤ (partialTraceRight ((U : Matrix _ _ ℂ) * X * (U : Matrix _ _ ℂ)ᴴ)).rank := by
    let A := (U : Matrix (Fin m × Fin e) (Fin m × Fin e) ℂ)
    have h := rank_le_product (A * X * Aᴴ) (hX.mul_mul_conjTranspose_same A)
    have hEq : (A * X * Aᴴ).rank = k := rank_conjugate U X
    rw [hEq] at h
    exact (hr _).mpr h
  let d := hX.isHermitian.eigenvalues
  let ix : Fin m × Fin e ≃ Fin (m * e) := finProdFinEquiv
  have hfirst : Fintype.card {p : Fin m × Fin e // (ix p).val < k} = k := by
    exact (Fintype.card_congr
      (ix.subtypeEquiv (q := fun i => i.val < k) (fun _ => Iff.rfl))).trans
      (Fintype.card_fin_lt_of_le hkm)
  have hnonzero : Fintype.card {p // d p ≠ 0} = k :=
    hX.isHermitian.rank_eq_card_non_zero_eigs.symm
  let perm : {p : Fin m × Fin e // (ix p).val < k} ≃ {p // d p ≠ 0} :=
    Fintype.equivOfCardEq (hfirst.trans hnonzero.symm)
  let σ := perm.extendSubtype
  let P : unitaryGroup (Fin m × Fin e) ℂ := ⟨σ.permMatrix ℂ, by
    rw [mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix,
      ← Matrix.permMatrix_mul]
    simp⟩
  let U := P * star hX.isHermitian.eigenvectorUnitary
  have hdiag : (U : Matrix _ _ ℂ) * X * (U : Matrix _ _ ℂ)ᴴ =
      diagonal (fun p => (d (σ p) : ℂ)) := by
    change Unitary.conjStarAlgAut ℂ _ U X = _
    rw [Unitary.conjStarAlgAut_mul_apply, hX.isHermitian.conjStarAlgAut_star_eigenvectorUnitary]
    change σ.permMatrix ℂ * diagonal (fun p => (d p : ℂ)) * (σ.permMatrix ℂ)ᴴ = _
    rw [conj_perm, Matrix.submatrix_diagonal_equiv]
    rfl
  let a : Fin m → ℂ := fun i => ∑ j : Fin e, (d (σ (i,j)) : ℂ)
  have hmarg : partialTraceRight (diagonal (fun p => (d (σ p) : ℂ))) = diagonal a := by
    ext i i'
    by_cases h : i = i'
    · subst i'
      simp [partialTraceRight, a]
    · simp [partialTraceRight, Prod.mk.injEq, h]
  have ha (i : Fin m) (hi : r ≤ i.val) : a i = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hj : k ≤ (ix (i,j)).val := by
      change k ≤ j.val + e * i.val
      exact hrk.trans ((Nat.mul_le_mul_right e hi).trans (by
        rw [Nat.mul_comm i.val e]
        exact Nat.le_add_left _ _))
    have hz : ¬ d (σ (i,j)) ≠ 0 := perm.extendSubtype_not_mem (i,j) (not_lt.mpr hj)
    exact Complex.ofReal_eq_zero.mpr (not_ne_iff.mp hz)
  have hupper : (partialTraceRight ((U : Matrix _ _ ℂ) * X * (U : Matrix _ _ ℂ)ᴴ)).rank ≤ r := by
    rw [hdiag, hmarg, Matrix.rank_diagonal, ← Fintype.card_fin_lt_of_le hrm]
    exact Fintype.card_le_of_injective
      (fun p : {i // a i ≠ 0} =>
        (⟨p.1, lt_of_not_ge fun h => p.2 (ha _ h)⟩ : {i : Fin m // i.val < r}))
      (fun _ _ h => Subtype.ext (congrArg (fun q : {i : Fin m // i.val < r} => q.val) h))
  exact ⟨⟨U, le_antisymm hupper (hlower U)⟩, fun _ ⟨U', h⟩ => h ▸ hlower U'⟩

#print axioms minimum

end D5.S3.Quantum.Recovery.LocalCompression.JointMarginalRank
