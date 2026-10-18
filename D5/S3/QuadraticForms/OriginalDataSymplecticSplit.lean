/- GID: D5/S3/QuadraticForms/OriginalDataSymplecticSplit
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/OriginalDataSymplecticSplit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.PosDef]
   utility: none
   digest: Positive Hamiltonian closure gives the original energy lift a symplectic orthogonal complement. -/

import D5.S3.QuadraticForms.SymplecticBasis
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.QuadraticForms.OriginalDataSymplecticSplit

open Matrix Module
open LinearMap (BilinForm)
open D5.S3.QuadraticForms.SymplecticBasis

private theorem positive_hamiltonian_restrict
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J S : Matrix ι ι ℝ) (hJJ : J * J = -1)
    (hAlt : J.toBilin'.IsAlt) (hS : S.PosDef)
    (W : Submodule ℝ (ι → ℝ))
    (hW : ∀ x ∈ W, (J * S) *ᵥ x ∈ W) :
    (J.toBilin'.restrict W).Nondegenerate := by
  have hAltW : (J.toBilin'.restrict W).IsAlt := fun x => hAlt x
  apply (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hAltW.isRefl).mpr
  intro x hx
  apply Subtype.ext
  by_contra hne
  have hp : 0 < (x : ι → ℝ) ⬝ᵥ S *ᵥ (x : ι → ℝ) := by
    simpa using hS.dotProduct_mulVec_pos hne
  have hz := hx ⟨(J * S) *ᵥ (x : ι → ℝ), hW x x.property⟩
  change J.toBilin' (x : ι → ℝ) ((J * S) *ᵥ (x : ι → ℝ)) = 0 at hz
  rw [Matrix.toBilin'_apply', Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, hJJ, Matrix.neg_mul, Matrix.one_mul,
    Matrix.neg_mulVec, dotProduct_neg] at hz
  linarith

/-- The lift is fixed by the original positive energy and the original observation map.
The observation restricted to its range has the displayed inverse, and its kernel is
exactly the symplectic orthogonal. Both subspaces receive Darboux bases of these same
restricted forms. No positive-dimension assumption is imposed. -/
theorem original_data_symplectic_retract
    {n r : ℕ}
    (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)
    (O : Matrix (Fin r) (Fin n ⊕ Fin n) ℝ)
    (K : Matrix (Fin r) (Fin r) ℝ)
    (hS : S.PosDef) (hO : Function.Surjective O.mulVec)
    (hclosed : O * ((-Matrix.J (Fin n) ℝ) * S) = K * O) :
    let J := -Matrix.J (Fin n) ℝ
    let P := O * S⁻¹ * Oᵀ
    let L := S⁻¹ * Oᵀ * P⁻¹
    let U := LinearMap.range L.mulVecLin
    let V := LinearMap.ker O.mulVecLin
    let ω := J.toBilin'
    P.PosDef ∧ O * L = 1 ∧
    (∃ e : U ≃ₗ[ℝ] (Fin r → ℝ),
      (∀ u, e u = O *ᵥ (u : (Fin n ⊕ Fin n) → ℝ)) ∧
      (∀ y, (e.symm y : (Fin n ⊕ Fin n) → ℝ) = L *ᵥ y)) ∧
    IsCompl U V ∧ ω.orthogonal U = V ∧
    (ω.restrict U).IsAlt ∧ (ω.restrict V).IsAlt ∧
    (ω.restrict U).Nondegenerate ∧ (ω.restrict V).Nondegenerate ∧
    (∀ u ∈ U, ∀ v ∈ V, S.toBilin' u v = 0) ∧
    (S.toBilin'.restrict U).toQuadraticMap.PosDef ∧
    (S.toBilin'.restrict V).toQuadraticMap.PosDef ∧
    finrank ℝ U = r ∧ finrank ℝ U + finrank ℝ V = 2 * n ∧
    IsUnit K ∧ IsUnit (O * J * Oᵀ) ∧ (J * S) * L = L * K ∧
    (∃ (k h : ℕ)
      (bU : Basis (Fin k ⊕ Fin k) ℝ U)
      (bV : Basis (Fin h ⊕ Fin h) ℝ V),
      IsSymplecticBasis (ω.restrict U) bU ∧
      IsSymplecticBasis (ω.restrict V) bV ∧ r = 2 * k ∧ n = k + h) := by
  classical
  let J := -Matrix.J (Fin n) ℝ
  let P := O * S⁻¹ * Oᵀ
  let L := S⁻¹ * Oᵀ * P⁻¹
  let U := LinearMap.range L.mulVecLin
  let V := LinearMap.ker O.mulVecLin
  let ω := J.toBilin'
  let A := J * S
  change P.PosDef ∧ O * L = 1 ∧ _
  have hJJ : J * J = -1 := by
    simpa only [J, neg_mul_neg] using Matrix.J_squared (Fin n) ℝ
  have hJT : Jᵀ = -J := by
    simp only [J, Matrix.transpose_neg, Matrix.J_transpose, neg_neg]
  have hAlt : ω.IsAlt := by
    intro x
    have h := Matrix.dotProduct_transpose_mulVec J x x
    rw [hJT, Matrix.neg_mulVec, dotProduct_neg] at h
    change J.toBilin' x x = 0
    rw [Matrix.toBilin'_apply']
    linarith
  have hST : Sᵀ = S := by simpa using hS.1.eq
  have hSiS : S⁻¹ * S = 1 :=
    Matrix.nonsing_inv_mul S (S.isUnit_iff_isUnit_det.mp hS.isUnit)
  obtain ⟨Q, hOQ⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hO
  have hQTOT : Qᵀ * Oᵀ = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using
      congrArg Matrix.transpose hOQ
  have hOT : Function.Injective Oᵀ.mulVec := by
    intro x y hxy
    have h := congrArg (fun z => Qᵀ *ᵥ z) hxy
    simpa only [Matrix.mulVec_mulVec, hQTOT, Matrix.one_mulVec] using h
  have hP : P.PosDef := by
    simpa only [P, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] using
      hS.inv.conjTranspose_mul_mul_same (B := Oᵀ) hOT
  have hPT : Pᵀ = P := by simpa using hP.1.eq
  have hPPi : P * P⁻¹ = 1 :=
    Matrix.mul_nonsing_inv P (P.isUnit_iff_isUnit_det.mp hP.isUnit)
  have hOL : O * L = 1 := by
    calc
      O * L = P * P⁻¹ := by simp only [P, L, Matrix.mul_assoc]
      _ = 1 := hPPi
  have hleft : Function.LeftInverse O.mulVec L.mulVec := by
    intro y
    rw [Matrix.mulVec_mulVec, hOL, Matrix.one_mulVec]
  let e : U ≃ₗ[ℝ] (Fin r → ℝ) :=
    (LinearEquiv.ofLeftInverse (f := L.mulVecLin) hleft).symm
  have hLtS : Lᵀ * S = P⁻¹ * O := by
    simp only [L, Matrix.transpose_mul, Matrix.transpose_nonsing_inv,
      hPT, hST, Matrix.transpose_transpose, Matrix.mul_assoc, hSiS, Matrix.mul_one]
  have henergy : ∀ u ∈ U, ∀ v ∈ V, S.toBilin' u v = 0 := by
    rintro u ⟨y, rfl⟩ v hv
    change S.toBilin' (L *ᵥ y) v = 0
    rw [Matrix.toBilin'_apply', dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec,
      Matrix.mulVec_mulVec, hLtS, ← Matrix.mulVec_mulVec]
    change y ⬝ᵥ P⁻¹ *ᵥ (O *ᵥ v) = 0
    rw [show O *ᵥ v = 0 from hv, Matrix.mulVec_zero, dotProduct_zero]
  have hcompl : IsCompl U V := by
    constructor
    · rw [disjoint_iff_inf_le]
      rintro x ⟨⟨y, rfl⟩, hxV⟩
      have hy : y = 0 := (hleft y).symm.trans hxV
      simpa only [Submodule.mem_bot, hy, Matrix.mulVecLin_apply, Matrix.mulVec_zero]
    · rw [codisjoint_iff_le_sup]
      intro z _
      apply Submodule.mem_sup.mpr
      refine ⟨L *ᵥ (O *ᵥ z), ⟨O *ᵥ z, rfl⟩,
        z - L *ᵥ (O *ᵥ z), ?_, by rw [add_comm, sub_add_cancel]⟩
      change O *ᵥ (z - L *ᵥ (O *ᵥ z)) = 0
      rw [Matrix.mulVec_sub, hleft, sub_self]
  have hJinj : Function.Injective J.mulVec := by
    intro x y hxy
    have h := congrArg (fun z => J *ᵥ z) hxy
    simpa only [Matrix.mulVec_mulVec, hJJ, Matrix.neg_mulVec,
      Matrix.one_mulVec, neg_inj] using h
  have hSinj := Matrix.mulVec_injective_iff_isUnit.mpr hS.isUnit
  have hAinj : Function.Injective A.mulVec := by
    intro x y hxy
    apply hSinj
    apply hJinj
    simpa only [A, Matrix.mulVec_mulVec] using hxy
  have hAV : ∀ v ∈ V, A *ᵥ v ∈ V := by
    intro v hv
    change O *ᵥ (A *ᵥ v) = 0
    rw [Matrix.mulVec_mulVec, show O * A = K * O from hclosed,
      ← Matrix.mulVec_mulVec, show O *ᵥ v = 0 from hv, Matrix.mulVec_zero]
  have hndV : (ω.restrict V).Nondegenerate :=
    positive_hamiltonian_restrict J S hJJ hAlt hS V hAV
  have hnd : ω.Nondegenerate := by
    have hJunit : IsUnit J := Matrix.mulVec_injective_iff_isUnit.mp hJinj
    exact (Matrix.nondegenerate_of_det_ne_zero
      (J.isUnit_iff_isUnit_det.mp hJunit).ne_zero).toBilin'
  let AV : V →ₗ[ℝ] V := A.mulVecLin.restrict hAV
  have hAVsurj : Function.Surjective AV := by
    apply LinearMap.surjective_of_injective
    intro x y hxy
    apply Subtype.ext
    apply hAinj
    exact congrArg Subtype.val hxy
  have hcross : ∀ u ∈ U, ∀ v ∈ V, ω u v = 0 := by
    intro u hu v hv
    obtain ⟨w, hw⟩ := hAVsurj ⟨v, hv⟩
    have hwv : A *ᵥ (w : (Fin n ⊕ Fin n) → ℝ) = v := congrArg Subtype.val hw
    rw [← hwv]
    change J.toBilin' u ((J * S) *ᵥ (w : (Fin n ⊕ Fin n) → ℝ)) = 0
    rw [Matrix.toBilin'_apply', Matrix.mulVec_mulVec,
      ← Matrix.mul_assoc, hJJ, Matrix.neg_mul, Matrix.one_mul,
      Matrix.neg_mulVec, dotProduct_neg]
    have he : (u : (Fin n ⊕ Fin n) → ℝ) ⬝ᵥ S *ᵥ (w : (Fin n ⊕ Fin n) → ℝ) = 0 := by
      simpa only [Matrix.toBilin'_apply'] using henergy u hu w.1 w.2
    exact neg_eq_zero.mpr he
  have hUle : U ≤ ω.orthogonal V := by
    intro u hu
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro v hv
    simpa only [hcross u hu v hv, neg_zero] using (hAlt.neg_eq u v).symm
  have hVcompl : IsCompl V (ω.orthogonal V) :=
    LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hAlt.isRefl hndV
  have hUeq : U = ω.orthogonal V := by
    apply Submodule.eq_of_le_of_finrank_eq hUle
    have hd₁ := Submodule.finrank_add_eq_of_isCompl hcompl.symm
    have hd₂ := Submodule.finrank_add_eq_of_isCompl hVcompl
    omega
  have horth : ω.orthogonal U = V := by
    rw [hUeq]
    exact LinearMap.BilinForm.orthogonal_orthogonal hnd hAlt.isRefl V
  have hndU : (ω.restrict U).Nondegenerate := by
    apply LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal ω hAlt.isRefl
    simpa only [horth] using hcompl.disjoint
  have hAltU : (ω.restrict U).IsAlt := fun x => hAlt x
  have hAltV : (ω.restrict V).IsAlt := fun x => hAlt x
  have hpos : ∀ W : Submodule ℝ ((Fin n ⊕ Fin n) → ℝ),
      (S.toBilin'.restrict W).toQuadraticMap.PosDef := by
    intro W x hx
    have hx' : (x : (Fin n ⊕ Fin n) → ℝ) ≠ 0 := fun h => hx (Subtype.ext h)
    simpa [Matrix.toBilin'_apply'] using hS.dotProduct_mulVec_pos hx'
  have hdimU : finrank ℝ U = r := by simpa using e.finrank_eq
  have hdim : finrank ℝ U + finrank ℝ V = 2 * n := by
    simpa [two_mul] using Submodule.finrank_add_eq_of_isCompl hcompl
  have hAsurj : Function.Surjective A.mulVec :=
    LinearMap.surjective_of_injective (f := A.mulVecLin) hAinj
  have hKunit : IsUnit K := by
    apply Matrix.mulVec_surjective_iff_isUnit.mp
    intro y
    obtain ⟨x, hx⟩ := hO y
    obtain ⟨z, hz⟩ := hAsurj x
    refine ⟨O *ᵥ z, ?_⟩
    rw [Matrix.mulVec_mulVec, ← show O * A = K * O from hclosed,
      ← Matrix.mulVec_mulVec, hz, hx]
  have hSSi : S * S⁻¹ = 1 :=
    Matrix.mul_nonsing_inv S (S.isUnit_iff_isUnit_det.mp hS.isUnit)
  have hKP : K * P = O * J * Oᵀ := by
    calc
      K * P = (K * O) * S⁻¹ * Oᵀ := by simp only [P, Matrix.mul_assoc]
      _ = (O * (J * S)) * S⁻¹ * Oᵀ := by rw [hclosed]
      _ = O * (J * (S * S⁻¹)) * Oᵀ := by simp only [Matrix.mul_assoc]
      _ = O * J * Oᵀ := by rw [hSSi, Matrix.mul_one]
  have hJrunit : IsUnit (O * J * Oᵀ) := hKP ▸ hKunit.mul hP.isUnit
  have hAU : ∀ u ∈ U, A *ᵥ u ∈ U := by
    intro u hu
    rw [hUeq, LinearMap.BilinForm.mem_orthogonal_iff]
    intro v hv
    change J.toBilin' v ((J * S) *ᵥ u) = 0
    rw [Matrix.toBilin'_apply', Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
      hJJ, Matrix.neg_mul, Matrix.one_mul, Matrix.neg_mulVec, dotProduct_neg]
    apply neg_eq_zero.mpr
    have he : u ⬝ᵥ S *ᵥ v = 0 := by
      simpa only [Matrix.toBilin'_apply'] using henergy u hu v hv
    have hs := Matrix.dotProduct_transpose_mulVec S u v
    rw [hST] at hs
    exact hs.symm.trans he
  have hproj : ∀ u ∈ U, L *ᵥ (O *ᵥ u) = u := by
    rintro u ⟨y, rfl⟩
    exact congrArg (fun z => L *ᵥ z) (hleft y)
  have hALv : ∀ y, A *ᵥ (L *ᵥ y) = L *ᵥ (K *ᵥ y) := by
    intro y
    have hp := hproj (A *ᵥ (L *ᵥ y)) (hAU _ ⟨y, rfl⟩)
    have ho : O *ᵥ (A *ᵥ (L *ᵥ y)) = K *ᵥ y := by
      rw [Matrix.mulVec_mulVec, show O * A = K * O from hclosed,
        ← Matrix.mulVec_mulVec, hleft]
    rw [ho] at hp
    exact hp.symm
  have hAL : A * L = L * K := by
    ext i j
    change (A *ᵥ L.col j) i = (L *ᵥ K.col j) i
    have h := congrArg (fun z => z i) (hALv (Pi.single j 1))
    simpa only [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] using h
  obtain ⟨k, bU, hbU⟩ := exists_isSymplecticBasis hAltU hndU
  obtain ⟨h, bV, hbV⟩ := exists_isSymplecticBasis hAltV hndV
  have hk : finrank ℝ U = 2 * k := by
    simpa [two_mul] using Module.finrank_eq_card_basis bU
  have hh : finrank ℝ V = 2 * h := by
    simpa [two_mul] using Module.finrank_eq_card_basis bV
  refine ⟨hP, hOL, ⟨e, ?_, ?_⟩, hcompl, horth, hAltU, hAltV,
    hndU, hndV, henergy, hpos U, hpos V, hdimU, hdim,
    hKunit, hJrunit, hAL,
    k, h, bU, bV, hbU, hbV, ?_, ?_⟩
  · intro u; rfl
  · intro y; rfl
  · omega
  · omega

end D5.S3.QuadraticForms.OriginalDataSymplecticSplit
