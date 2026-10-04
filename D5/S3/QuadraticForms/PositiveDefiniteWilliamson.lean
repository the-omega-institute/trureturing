/- GID: D5/S3/QuadraticForms/PositiveDefiniteWilliamson
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/PositiveDefiniteWilliamson
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite positive real quadratic form admits one positive symplectic congruence. -/

/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

Modified: bounded source selection, explicit universe and namespace, direct target-pin
imports, local complement/block/coordinate normalization, and proof-local positive frequencies.
Adapted from https://github.com/kaplan196883/QIQT-H/blob/0313e288c7ab3d3868c73ccdc6a68242efc0214a/lean/mathlib/QIQTH/WilliamsonNormalForm.lean
The full Apache 2.0 license accompanies this source packet and is already distributed
by the receiving repository's LICENSE. Target: Lean v4.33.0, Mathlib
db584cd6d46c92f209a44c0f1c829460d327499d.
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace D5.S3.QuadraticForms.PositiveDefiniteWilliamson

open Matrix Module
open scoped MatrixOrder InnerProductSpace RealInnerProductSpace

/-- Strong induction constructs a complete oriented paired orthonormal basis of
an even-dimensional real inner product space for an arbitrary skew operator.
The zero-dimensional and zero-operator branches are included. -/
theorem skew_paired_basis_induction : ∀ (n : ℕ) {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (a : E →ₗ[ℝ] E),
    (∀ x y, ⟪a x, y⟫_ℝ = -⟪x, a y⟫_ℝ) → finrank ℝ E = n → Even n →
    ∃ (κ : Type) (_ : Fintype κ) (b : OrthonormalBasis (κ ⊕ κ) ℝ E) (ν : κ → ℝ),
      (∀ k, 0 ≤ ν k) ∧
      (∀ k, a (b (Sum.inl k)) = -ν k • b (Sum.inr k)) ∧
      (∀ k, a (b (Sum.inr k)) = ν k • b (Sum.inl k)) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro E _ _ _ a ha hn hEven
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · refine ⟨Empty, inferInstance,
        OrthonormalBasis.mk (v := fun k => isEmptyElim k) (Orthonormal.of_isEmpty (𝕜 := ℝ) _) ?_,
        fun k => k.elim, fun k => k.elim, fun k => k.elim, fun k => k.elim⟩
      have hcard : Fintype.card (Empty ⊕ Empty) = finrank ℝ E := by rw [hn, hn0]; simp
      exact (linearIndependent_empty_type.span_eq_top_of_card_eq_finrank' hcard).ge
    · obtain ⟨t, ht⟩ := hEven
      have hn2 : 2 ≤ n := by omega
      obtain ⟨p, q, ν, hp1, hq1, hpq, hν0, hap, haq⟩ :
          ∃ (p q : E) (ν : ℝ), ‖p‖ = 1 ∧ ‖q‖ = 1 ∧ ⟪p, q⟫_ℝ = 0 ∧ 0 ≤ ν ∧
            a p = -ν • q ∧ a q = ν • p := by
        by_cases hazero : a = 0
        · have : Nontrivial E := Module.nontrivial_of_finrank_pos
            (show 0 < finrank ℝ E by rw [hn]; exact hnpos)
          obtain ⟨x, hx⟩ := exists_ne (0 : E)
          have hxne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
          set u := (‖x‖⁻¹ : ℝ) • x with hudef
          have hu1 : ‖u‖ = 1 := by
            rw [hudef, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (norm_pos_iff.mpr hx),
              inv_mul_cancel₀ hxne]
          have huneq : u ≠ 0 := by rw [hudef]; exact smul_ne_zero (inv_ne_zero hxne) hx
          have hdimperp : 0 < finrank ℝ (ℝ ∙ u)ᗮ := by
            have h1 := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ u)
            rw [finrank_span_singleton huneq] at h1
            omega
          have : Nontrivial ↥((ℝ ∙ u)ᗮ) := Module.nontrivial_of_finrank_pos hdimperp
          obtain ⟨y', hy'⟩ := exists_ne (0 : ↥((ℝ ∙ u)ᗮ))
          have hyne : (y' : E) ≠ 0 := by simpa only [ne_eq, Submodule.coe_eq_zero] using hy'
          have hynorm : ‖(y' : E)‖ ≠ 0 := norm_ne_zero_iff.mpr hyne
          set w := (‖(y' : E)‖⁻¹ : ℝ) • (y' : E) with hwdef
          have hw1 : ‖w‖ = 1 := by
            rw [hwdef, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (norm_pos_iff.mpr hyne),
              inv_mul_cancel₀ hynorm]
          have huw : ⟪u, w⟫_ℝ = 0 := by
            rw [hwdef, real_inner_smul_right,
              Submodule.mem_orthogonal_singleton_iff_inner_right.mp y'.2, mul_zero]
          exact ⟨u, w, 0, hu1, hw1, huw, le_refl 0, by simp [hazero], by simp [hazero]⟩
        · have : Nontrivial E := Module.nontrivial_of_finrank_pos
            (show 0 < finrank ℝ E by rw [hn]; exact hnpos)
          obtain ⟨v₀, hv₀ne⟩ := DFunLike.ne_iff.mp hazero
          rw [LinearMap.zero_apply] at hv₀ne
          have hv₀0 : v₀ ≠ 0 := fun h => hv₀ne (by rw [h, map_zero])
          have hTsymm : (a ∘ₗ a).IsSymmetric := by
            intro x y
            simp only [LinearMap.comp_apply]
            rw [ha (a x) y, ha x (a y), neg_neg]
          set μ₀ : ℝ :=
            ⨅ z : {z : E // z ≠ 0}, RCLike.re ⟪(a ∘ₗ a) (z : E), (z : E)⟫_ℝ / ‖(z : E)‖ ^ 2 with hμ₀
          have hev : Module.End.HasEigenvalue (a ∘ₗ a) μ₀ :=
            hTsymm.hasEigenvalue_iInf_of_finiteDimensional
          have hbdd : BddBelow (Set.range fun z : {z : E // z ≠ 0} =>
              RCLike.re ⟪(a ∘ₗ a) (z : E), (z : E)⟫_ℝ / ‖(z : E)‖ ^ 2) := by
            refine ⟨-‖(a.toContinuousLinearMap : E →L[ℝ] E)‖ ^ 2, ?_⟩
            rintro _ ⟨⟨z, hz⟩, rfl⟩
            change -‖(a.toContinuousLinearMap : E →L[ℝ] E)‖ ^ 2
              ≤ RCLike.re ⟪(a ∘ₗ a) z, z⟫_ℝ / ‖z‖ ^ 2
            have hz2 : 0 < ‖z‖ ^ 2 := pow_pos (norm_pos_iff.mpr hz) 2
            have hnum : RCLike.re ⟪(a ∘ₗ a) (z : E), (z : E)⟫_ℝ = -‖a z‖ ^ 2 := by
              rw [RCLike.re_to_real]; simp only [LinearMap.comp_apply]
              rw [ha (a z) z, real_inner_self_eq_norm_sq]
            rw [hnum, neg_div, neg_le_neg_iff, div_le_iff₀ hz2]
            have hle : ‖a z‖ ≤ ‖(a.toContinuousLinearMap : E →L[ℝ] E)‖ * ‖z‖ := by
              have h := (a.toContinuousLinearMap).le_opNorm z
              rwa [LinearMap.coe_toContinuousLinearMap'] at h
            calc ‖a z‖ ^ 2 = ‖a z‖ * ‖a z‖ := pow_two _
              _ ≤ (‖(a.toContinuousLinearMap : E →L[ℝ] E)‖ * ‖z‖)
                    * (‖(a.toContinuousLinearMap : E →L[ℝ] E)‖ * ‖z‖) :=
                  mul_self_le_mul_self (norm_nonneg _) hle
              _ = ‖(a.toContinuousLinearMap : E →L[ℝ] E)‖ ^ 2 * ‖z‖ ^ 2 := by ring
          have hfv₀ : RCLike.re ⟪(a ∘ₗ a) v₀, v₀⟫_ℝ / ‖v₀‖ ^ 2 < 0 := by
            have hnum : RCLike.re ⟪(a ∘ₗ a) v₀, v₀⟫_ℝ = -‖a v₀‖ ^ 2 := by
              rw [RCLike.re_to_real]; simp only [LinearMap.comp_apply]
              rw [ha (a v₀) v₀, real_inner_self_eq_norm_sq]
            rw [hnum]
            exact div_neg_of_neg_of_pos (neg_lt_zero.mpr (pow_pos (norm_pos_iff.mpr hv₀ne) 2))
              (pow_pos (norm_pos_iff.mpr hv₀0) 2)
          have hμ₀neg : μ₀ < 0 := by
            rw [hμ₀]; exact lt_of_le_of_lt (ciInf_le hbdd ⟨v₀, hv₀0⟩) hfv₀
          obtain ⟨u₀, hu₀ev⟩ := hev.exists_hasEigenvector
          have hu₀0 : u₀ ≠ 0 := hu₀ev.2
          have hTu₀ : (a ∘ₗ a) u₀ = μ₀ • u₀ := hu₀ev.apply_eq_smul
          have hu₀norm : ‖u₀‖ ≠ 0 := norm_ne_zero_iff.mpr hu₀0
          set u := (‖u₀‖⁻¹ : ℝ) • u₀ with hudef
          have hu1 : ‖u‖ = 1 := by
            rw [hudef, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (norm_pos_iff.mpr hu₀0),
              inv_mul_cancel₀ hu₀norm]
          have hTu : (a ∘ₗ a) u = μ₀ • u := by rw [hudef, map_smul, hTu₀, smul_comm]
          have hau_ne : a u ≠ 0 := by
            intro h
            have h1 : ⟪(a ∘ₗ a) u, u⟫_ℝ = μ₀ := by
              rw [hTu, real_inner_smul_left, real_inner_self_eq_norm_sq, hu1]; norm_num
            have h2 : ⟪(a ∘ₗ a) u, u⟫_ℝ = 0 := by
              simp only [LinearMap.comp_apply, h, map_zero, inner_zero_left]
            rw [h2] at h1; linarith
          set ν := ‖a u‖ with hνdef
          have hνpos : 0 < ν := by rw [hνdef]; exact norm_pos_iff.mpr hau_ne
          have hνne : ν ≠ 0 := hνpos.ne'
          have hνsq : ν ^ 2 = -μ₀ := by
            have h3 : ⟪(a ∘ₗ a) u, u⟫_ℝ = -‖a u‖ ^ 2 := by
              simp only [LinearMap.comp_apply]; rw [ha (a u) u, real_inner_self_eq_norm_sq]
            have h4 : ⟪(a ∘ₗ a) u, u⟫_ℝ = μ₀ := by
              rw [hTu, real_inner_smul_left, real_inner_self_eq_norm_sq, hu1]; norm_num
            rw [hνdef]; linarith
          set w := (ν⁻¹ : ℝ) • a u with hwdef
          have hw1 : ‖w‖ = 1 := by
            rw [hwdef, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hνpos, ← hνdef,
              inv_mul_cancel₀ hνne]
          have hawu : ν • w = a u := by
            rw [hwdef, smul_smul, mul_inv_cancel₀ hνne, one_smul]
          have hscalar : ν⁻¹ * μ₀ = -ν := by
            have hμ : μ₀ = -ν ^ 2 := by rw [hνsq]; ring
            rw [hμ, mul_neg, pow_two, ← mul_assoc, inv_mul_cancel₀ hνne, one_mul]
          have haw : a w = -ν • u := by
            rw [hwdef, map_smul, ← LinearMap.comp_apply, hTu, smul_smul, hscalar]
          have huw : ⟪u, w⟫_ℝ = 0 := by
            rw [hwdef, real_inner_smul_right]
            have h5 := ha u u
            have h5' := real_inner_comm u (a u)
            have h6 : ⟪u, a u⟫_ℝ = 0 := by linarith [h5, h5']
            rw [h6, mul_zero]
          exact ⟨w, u, ν, hw1, hu1, by rw [real_inner_comm]; exact huw, hνpos.le, haw, hawu.symm⟩
      set P : Submodule ℝ E := Submodule.span ℝ (Set.range ![p, q]) with hPdef
      have hon_pq : Orthonormal ℝ ![p, q] := by
        rw [orthonormal_vecCons_iff]
        refine ⟨hp1, ?_, ?_⟩
        · intro i
          fin_cases i
          change ⟪p, q⟫_ℝ = 0
          exact hpq
        · rw [orthonormal_vecCons_iff]
          exact ⟨hq1, fun i => i.elim0, Orthonormal.of_isEmpty (𝕜 := ℝ) _⟩
      have hpP : p ∈ P := Submodule.subset_span ⟨0, by simp⟩
      have hqP : q ∈ P := Submodule.subset_span ⟨1, by simp⟩
      have hfinP : finrank ℝ P = 2 := by
        rw [hPdef, finrank_span_eq_card hon_pq.linearIndependent]; simp
      have hinv : ∀ x ∈ P, a x ∈ P := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem z hz =>
            obtain ⟨i, rfl⟩ := hz
            fin_cases i
            · change a p ∈ P
              rw [hap]; exact P.smul_mem _ hqP
            · change a q ∈ P
              rw [haq]; exact P.smul_mem _ hpP
        | zero => simp
        | add x y _ _ ihx ihy => rw [map_add]; exact P.add_mem ihx ihy
        | smul c x _ ihx => rw [map_smul]; exact P.smul_mem c ihx
      have hadj : a.adjoint = -a := by
        apply Eq.symm
        apply (LinearMap.eq_adjoint_iff (-a) a).mpr
        intro x y
        rw [LinearMap.neg_apply, inner_neg_left, ha x y, neg_neg]
      have hinvAdj : P ∈ Module.End.invtSubmodule a.adjoint := by
        rw [hadj]
        change ∀ x ∈ P, (-a) x ∈ P
        intro x hx
        simpa only [LinearMap.neg_apply] using P.neg_mem (hinv x hx)
      have hinvC : ∀ x ∈ Pᗮ, a x ∈ Pᗮ :=
        Module.End.mem_invtSubmodule_adjoint_iff.mp hinvAdj
      set aC : ↥(Pᗮ) →ₗ[ℝ] ↥(Pᗮ) := a.restrict hinvC with haCdef
      have haC_coe : ∀ x : ↥(Pᗮ), ((aC x : ↥(Pᗮ)) : E) = a (x : E) := by
        intro x; rw [haCdef]; rfl
      have haC : ∀ x y : ↥(Pᗮ), ⟪aC x, y⟫_ℝ = -⟪x, aC y⟫_ℝ := by
        intro x y
        rw [Submodule.coe_inner, Submodule.coe_inner, haC_coe, haC_coe]
        exact ha x y
      have hsum := Submodule.finrank_add_finrank_orthogonal P
      rw [hfinP, hn] at hsum
      have hlt : finrank ℝ Pᗮ < n := by omega
      have hEvenPerp : Even (finrank ℝ Pᗮ) := ⟨t - 1, by omega⟩
      obtain ⟨κ', instκ', bC, νC, hνC, hCinl, hCinr⟩ :=
        IH (finrank ℝ Pᗮ) hlt aC haC rfl hEvenPerp
      let : Fintype κ' := instκ'
      let : DecidableEq κ' := Classical.decEq κ'
      set vv : (Unit ⊕ κ') ⊕ (Unit ⊕ κ') → E :=
        Sum.elim (Sum.elim (fun _ => p) (fun k => (bC (Sum.inl k) : E)))
                 (Sum.elim (fun _ => q) (fun k => (bC (Sum.inr k) : E))) with hvvdef
      set νfull : Unit ⊕ κ' → ℝ := Sum.elim (fun _ => ν) νC with hνfulldef
      have hbb : ∀ z z' : κ' ⊕ κ',
          ⟪(bC z : E), (bC z' : E)⟫_ℝ = if z = z' then (1 : ℝ) else 0 := by
        intro z z'; rw [← Submodule.coe_inner]; exact orthonormal_iff_ite.mp bC.orthonormal z z'
      have hPbot : ∀ z : κ' ⊕ κ', ∀ x ∈ P, ⟪x, (bC z : E)⟫_ℝ = 0 :=
        fun z x hx => Submodule.inner_right_of_mem_orthogonal hx (bC z).2
      have hon : Orthonormal ℝ vv := by
        rw [orthonormal_iff_ite]
        have hqp : ⟪q, p⟫_ℝ = 0 := by rw [real_inner_comm]; exact hpq
        have hpbC : ∀ z, ⟪p, (bC z : E)⟫_ℝ = 0 := fun z => hPbot z p hpP
        have hqbC : ∀ z, ⟪q, (bC z : E)⟫_ℝ = 0 := fun z => hPbot z q hqP
        have hbCp : ∀ z, ⟪(bC z : E), p⟫_ℝ = 0 := fun z => by rw [real_inner_comm]; exact hpbC z
        have hbCq : ∀ z, ⟪(bC z : E), q⟫_ℝ = 0 := fun z => by rw [real_inner_comm]; exact hqbC z
        rintro ((⟨⟩ | k) | (⟨⟩ | k)) ((⟨⟩ | l) | (⟨⟩ | l)) <;>
          simp [hvvdef, hp1, hq1, hpq, hqp, hpbC, hqbC, hbCp, hbCq, hbb]
      have hcardC : finrank ℝ Pᗮ = Fintype.card (κ' ⊕ κ') := finrank_eq_card_basis bC.toBasis
      have hcard : Fintype.card ((Unit ⊕ κ') ⊕ (Unit ⊕ κ')) = finrank ℝ E := by
        simp only [Fintype.card_sum, Fintype.card_unit] at hcardC ⊢
        omega
      have hspan : ⊤ ≤ Submodule.span ℝ (Set.range vv) :=
        (hon.linearIndependent.span_eq_top_of_card_eq_finrank' hcard).ge
      set b : OrthonormalBasis ((Unit ⊕ κ') ⊕ (Unit ⊕ κ')) ℝ E :=
        OrthonormalBasis.mk hon hspan with hbdef
      have hbcoe : ⇑b = vv := OrthonormalBasis.coe_mk hon hspan
      refine ⟨Unit ⊕ κ', inferInstance, b, νfull, ?_, ?_, ?_⟩
      · intro k
        rcases k with ⟨⟩ | k'
        · simpa only [hνfulldef, Sum.elim_inl] using hν0
        · simpa only [hνfulldef, Sum.elim_inr] using hνC k'
      · intro k
        rw [hbcoe]
        rcases k with ⟨⟩ | k'
        · simp only [hvvdef, hνfulldef, Sum.elim_inl, Sum.elim_inr]; exact hap
        · simp only [hvvdef, hνfulldef, Sum.elim_inl, Sum.elim_inr]
          rw [← haC_coe, hCinl k', Submodule.coe_smul]
      · intro k
        rw [hbcoe]
        rcases k with ⟨⟩ | k'
        · simp only [hvvdef, hνfulldef, Sum.elim_inl, Sum.elim_inr]; exact haq
        · simp only [hvvdef, hνfulldef, Sum.elim_inl, Sum.elim_inr]
          rw [← haC_coe, hCinr k', Submodule.coe_smul]

/-- A positive real quadratic form on an arbitrary finite set of mode pairs has
one actual symplectic congruence with strictly positive paired frequencies.
Both symplectic relations use the same S and Mathlib's J; empty mode sets are allowed. -/
theorem positive_definite_williamson {l : Type u} [Fintype l] [DecidableEq l]
    (M : Matrix (l ⊕ l) (l ⊕ l) ℝ) (hM : M.PosDef) :
    ∃ (S : Matrix (l ⊕ l) (l ⊕ l) ℝ) (ν : l → ℝ),
      S ∈ Matrix.symplecticGroup l ℝ ∧ (∀ i, 0 < ν i) ∧
        Sᵀ * Matrix.J l ℝ * S = Matrix.J l ℝ ∧
          Sᵀ * M * S = Matrix.fromBlocks (Matrix.diagonal ν) 0 0 (Matrix.diagonal ν) := by
  classical
  set R : Matrix (l ⊕ l) (l ⊕ l) ℝ := CFC.sqrt M with hR
  have hM0 : (0 : Matrix (l ⊕ l) (l ⊕ l) ℝ) ≤ M := Matrix.nonneg_iff_posSemidef.mpr hM.posSemidef
  have hRR : R * R = M := CFC.sqrt_mul_sqrt_self M hM0
  have hRsymm : Rᵀ = R := by
    rw [hR, ← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact ((Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg M)).isHermitian).eq
  have hMdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM.isUnit
  have hRdet : IsUnit R.det := by
    apply isUnit_of_mul_isUnit_left (y := R.det)
    rw [← Matrix.det_mul, hRR]; exact hMdet
  set Ri : Matrix (l ⊕ l) (l ⊕ l) ℝ := R⁻¹ with hRi
  have hRiR : Ri * R = 1 := Matrix.nonsing_inv_mul R hRdet
  have hRRi : R * Ri = 1 := Matrix.mul_nonsing_inv R hRdet
  have hRisymm : Riᵀ = Ri := by rw [hRi, Matrix.transpose_nonsing_inv, hRsymm]
  have hRiMRi : Ri * M * Ri = 1 := by
    have e : Ri * M * Ri = (Ri * R) * (R * Ri) := by rw [← hRR]; simp only [Matrix.mul_assoc]
    rw [e, hRiR, hRRi, Matrix.one_mul]
  set A : Matrix (l ⊕ l) (l ⊕ l) ℝ := R * Matrix.J l ℝ * R with hA_def
  have hA : Aᵀ = -A := by
    rw [hA_def, Matrix.transpose_mul, Matrix.transpose_mul, hRsymm,
      Matrix.J_transpose, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  have hAunit : IsUnit A := by
    apply (Matrix.isUnit_iff_isUnit_det A).mpr
    rw [hA_def, Matrix.det_mul, Matrix.det_mul]
    exact (hRdet.mul (Matrix.isUnit_det_J l ℝ)).mul hRdet
  have hY : ∃ (O : Matrix (l ⊕ l) (l ⊕ l) ℝ) (ν : l → ℝ),
      O ∈ Matrix.orthogonalGroup (l ⊕ l) ℝ ∧ (∀ i, 0 < ν i) ∧
        Oᵀ * A * O = Matrix.fromBlocks 0 (Matrix.diagonal ν) (-(Matrix.diagonal ν)) 0 := by
    set a : EuclideanSpace ℝ (l ⊕ l) →ₗ[ℝ] EuclideanSpace ℝ (l ⊕ l) :=
      Matrix.toEuclideanLin A with ha_def
    have hadj : a.adjoint = -a := by
      rw [ha_def, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
          Matrix.conjTranspose_eq_transpose_of_trivial, hA, map_neg]
    have ha : ∀ x y, ⟪a x, y⟫_ℝ = -⟪x, a y⟫_ℝ := by
      intro x y
      rw [← LinearMap.adjoint_inner_right, hadj, LinearMap.neg_apply, inner_neg_right]
    have ha_injective : Function.Injective a := by
      intro x y hxy
      apply WithLp.ofLp_injective 2
      apply Matrix.mulVec_injective_of_isUnit hAunit
      have hcoords := congrArg WithLp.ofLp hxy
      change A *ᵥ WithLp.ofLp x = A *ᵥ WithLp.ofLp y at hcoords
      exact hcoords
    have hdim : Even (finrank ℝ (EuclideanSpace ℝ (l ⊕ l))) := by
      rw [finrank_euclideanSpace, Fintype.card_sum]
      exact ⟨Fintype.card l, rfl⟩
    obtain ⟨κ, instκ, b, ν₀, hν₀pos, hblk1, hblk2⟩ :=
      skew_paired_basis_induction (finrank ℝ (EuclideanSpace ℝ (l ⊕ l))) a ha rfl hdim
    let : Fintype κ := instκ
    let : DecidableEq κ := Classical.decEq κ
    have hcard : Fintype.card κ = Fintype.card l := by
      have h1 : finrank ℝ (EuclideanSpace ℝ (l ⊕ l)) = Fintype.card (κ ⊕ κ) :=
        finrank_eq_card_basis b.toBasis
      rw [finrank_euclideanSpace] at h1
      simp only [Fintype.card_sum] at h1
      omega
    set e : κ ≃ l := Fintype.equivOfCardEq hcard with he_def
    set b' : OrthonormalBasis (l ⊕ l) ℝ (EuclideanSpace ℝ (l ⊕ l)) :=
      b.reindex (e.sumCongr e) with hb'_def
    set ν : l → ℝ := fun i => ν₀ (e.symm i) with hν_def
    have hν : ∀ i, 0 ≤ ν i := fun i => hν₀pos (e.symm i)
    have hb'inl : ∀ i, b' (Sum.inl i) = b (Sum.inl (e.symm i)) := by
      intro i
      rw [hb'_def, b.reindex_apply, Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inl]
    have hb'inr : ∀ i, b' (Sum.inr i) = b (Sum.inr (e.symm i)) := by
      intro i
      rw [hb'_def, b.reindex_apply, Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inr]
    have hBlk1 : ∀ i, a (b' (Sum.inl i)) = -ν i • b' (Sum.inr i) := by
      intro i; rw [hb'inl i, hblk1 (e.symm i), hb'inr i]
    have hBlk2 : ∀ i, a (b' (Sum.inr i)) = ν i • b' (Sum.inl i) := by
      intro i; rw [hb'inr i, hblk2 (e.symm i), hb'inl i]
    have hνpos : ∀ i, 0 < ν i := by
      intro i
      by_contra hnpos
      have hz : ν i = 0 := le_antisymm (le_of_not_gt hnpos) (hν i)
      have hzero : a (b' (Sum.inl i)) = 0 := by
        rw [hBlk1 i, hz]
        simp
      have hbzero : b' (Sum.inl i) = 0 :=
        ha_injective (hzero.trans (map_zero a).symm)
      exact b'.orthonormal.ne_zero (Sum.inl i) hbzero
    set stdB := EuclideanSpace.basisFun (l ⊕ l) ℝ with hstdB
    set O : Matrix (l ⊕ l) (l ⊕ l) ℝ := stdB.toBasis.toMatrix b' with hO_def
    have hOrth : O ∈ Matrix.orthogonalGroup (l ⊕ l) ℝ :=
      stdB.toMatrix_orthonormalBasis_mem_orthogonal b'
    have hOreverse : Oᵀ = b'.toBasis.toMatrix stdB := by
      ext i j
      simp only [hO_def, Matrix.transpose_apply, Basis.toMatrix_apply,
        OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.repr_apply_apply, real_inner_comm]
    have hstandard : LinearMap.toMatrix stdB.toBasis stdB.toBasis a = A := by
      change LinearMap.toMatrix (EuclideanSpace.basisFun (l ⊕ l) ℝ).toBasis
        (EuclideanSpace.basisFun (l ⊕ l) ℝ).toBasis (Matrix.toEuclideanLin A) = A
      rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]
    have hMatCoordinate : Oᵀ * A * O = LinearMap.toMatrixOrthonormal b' a := by
      rw [hOreverse, hO_def, ← hstandard]
      change b'.toBasis.toMatrix stdB.toBasis *
        LinearMap.toMatrix stdB.toBasis stdB.toBasis a *
          stdB.toBasis.toMatrix b'.toBasis = LinearMap.toMatrix b'.toBasis b'.toBasis a
      exact basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
        b'.toBasis stdB.toBasis b'.toBasis stdB.toBasis a
    have hMatEntry : ∀ i j, (Oᵀ * A * O) i j = ⟪b' i, a (b' j)⟫_ℝ := by
      intro i j
      rw [hMatCoordinate]
      exact LinearMap.toMatrixOrthonormal_apply_apply b' a i j
    have hNormal : Oᵀ * A * O
        = Matrix.fromBlocks 0 (Matrix.diagonal ν) (-(Matrix.diagonal ν)) 0 := by
      ext i j
      rw [hMatEntry i j]
      rcases j with k | k
      · rw [hBlk1 k, real_inner_smul_right, orthonormal_iff_ite.mp b'.orthonormal i (Sum.inr k)]
        rcases i with p | p
        · rw [Matrix.fromBlocks_apply₁₁]; simp
        · rw [Matrix.fromBlocks_apply₂₁, Matrix.neg_apply, Matrix.diagonal_apply]
          by_cases hpk : p = k <;> simp [hpk]
      · rw [hBlk2 k, real_inner_smul_right, orthonormal_iff_ite.mp b'.orthonormal i (Sum.inl k)]
        rcases i with p | p
        · rw [Matrix.fromBlocks_apply₁₂, Matrix.diagonal_apply]
          by_cases hpk : p = k <;> simp [hpk]
        · rw [Matrix.fromBlocks_apply₂₂]; simp
    exact ⟨O, ν, hOrth, hνpos, hNormal⟩
  obtain ⟨O, ν, hOrth, hν, hNormal⟩ := hY
  have hdd : Matrix.diagonal (fun i => Real.sqrt (ν i))
        * Matrix.diagonal (fun i => Real.sqrt (ν i)) = Matrix.diagonal ν := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact Real.mul_self_sqrt (hν i).le
  set E : Matrix (l ⊕ l) (l ⊕ l) ℝ :=
    Matrix.fromBlocks 0 (Matrix.diagonal (fun i => Real.sqrt (ν i)))
      (Matrix.diagonal (fun i => Real.sqrt (ν i))) 0 with hE
  have hEsymm : Eᵀ = E := by
    rw [hE, Matrix.fromBlocks_transpose]
    simp only [Matrix.transpose_zero, Matrix.diagonal_transpose]
  have hEE : E * E = Matrix.fromBlocks (Matrix.diagonal ν) 0 0 (Matrix.diagonal ν) := by
    rw [hE, Matrix.fromBlocks_multiply]
    simp only [mul_zero, zero_mul, add_zero, zero_add, hdd]
  have hsq : (fun i => Real.sqrt (ν i) * Real.sqrt (ν i)) = ν := by
    funext i; exact Real.mul_self_sqrt (hν i).le
  have hEJE : E * Matrix.J l ℝ * E
      = Matrix.fromBlocks 0 (Matrix.diagonal ν) (-(Matrix.diagonal ν)) 0 := by
    rw [hE, show Matrix.J l ℝ = Matrix.fromBlocks 0 (-1) 1 0 from rfl,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [mul_zero, zero_mul, add_zero, zero_add, Matrix.mul_neg,
      Matrix.neg_mul, mul_one, Matrix.diagonal_mul_diagonal, hsq]
  set S : Matrix (l ⊕ l) (l ⊕ l) ℝ := Ri * O * E with hS
  have hOO : Oᵀ * O = 1 := (Matrix.mem_orthogonalGroup_iff' (l ⊕ l) ℝ).mp hOrth
  have hOOt : O * Oᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (l ⊕ l) ℝ).mp hOrth
  have hSt : Sᵀ = E * (Oᵀ * Ri) := by
    rw [hS, Matrix.transpose_mul, Matrix.transpose_mul, hRisymm, hEsymm]
  have hDiagEq : Sᵀ * M * S = Matrix.fromBlocks (Matrix.diagonal ν) 0 0 (Matrix.diagonal ν) := by
    have hk : Sᵀ * M * S = E * (Oᵀ * (Ri * M * Ri) * O) * E := by
      rw [hSt, hS]; simp only [Matrix.mul_assoc]
    rw [hk, hRiMRi, mul_one, hOO, mul_one, hEE]
  have hSympForm : S * Matrix.J l ℝ * Sᵀ = Matrix.J l ℝ := by
    have hk : S * Matrix.J l ℝ * Sᵀ = Ri * O * (E * Matrix.J l ℝ * E) * Oᵀ * Ri := by
      rw [hSt, hS]; simp only [Matrix.mul_assoc]
    rw [hk, hEJE, ← hNormal, hA_def]
    have hfin : Ri * O * (Oᵀ * (R * Matrix.J l ℝ * R) * O) * Oᵀ * Ri
        = Ri * ((O * Oᵀ) * (R * Matrix.J l ℝ * R) * (O * Oᵀ)) * Ri := by
      simp only [Matrix.mul_assoc]
    rw [hfin]
    simp only [hOOt, Matrix.one_mul, Matrix.mul_one]
    have hRiARi : Ri * (R * Matrix.J l ℝ * R) * Ri = Matrix.J l ℝ := by
      have e : Ri * (R * Matrix.J l ℝ * R) * Ri = (Ri * R) * Matrix.J l ℝ * (R * Ri) := by
        simp only [Matrix.mul_assoc]
      rw [e, hRiR, hRRi, Matrix.one_mul, Matrix.mul_one]
    exact hRiARi
  have hSymp : S ∈ Matrix.symplecticGroup l ℝ :=
    SymplecticGroup.mem_iff.mpr hSympForm
  exact ⟨S, ν, hSymp, hν, SymplecticGroup.mem_iff'.mp hSymp, hDiagEq⟩

#print axioms skew_paired_basis_induction
#print axioms positive_definite_williamson

end D5.S3.QuadraticForms.PositiveDefiniteWilliamson
