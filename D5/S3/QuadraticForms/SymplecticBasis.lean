/- GID: D5/S3/QuadraticForms/SymplecticBasis
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/SymplecticBasis
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite-dimensional nondegenerate alternating form has a symplectic basis. -/

import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.Finite

/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in
  docs/reports/qmutualinfo/csd-lean4-LICENSE.txt (complete upstream LICENSE).
Authors: Zayn Blore
Attributed port of zblore/csd-lean4,
  CsdLean4/Mathlib/LinearAlgebra/BilinearForm/SymplecticBasis.lean,
  immutable revision 39182b9e91a2791f5acb5ceaa2612ed71da921b5.
Source: https://github.com/zblore/csd-lean4/blob/39182b9e91a2791f5acb5ceaa2612ed71da921b5/CsdLean4/Mathlib/LinearAlgebra/BilinearForm/SymplecticBasis.lean
Original source SHA-256: 0aad253cae916206016ca59cdfe15c23a113dc84c78636551f69e3677d1add36.
Adaptation: repository namespace and header; induction, plane index equivalence and
  final reindexing are proof-local; pairing, sum and even-dimension companions omitted.
The pinned upstream tree has no NOTICE file or applicable NOTICE chain.
Retirement: when this repository changes its own pinned Mathlib revision, check that
  pin for an equivalent finite-dimensional alternating nondegenerate basis theorem.
  If present, replace all uses with the pinned declaration and remove this port.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.QuadraticForms.SymplecticBasis

open Module Submodule LinearMap.BilinForm
open LinearMap (BilinForm)

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

/-- A basis `e` indexed by `ι ⊕ ι` is **symplectic** for `B` when the `inl`-vectors (the `p`'s)
are pairwise `B`-orthogonal, so are the `inr`-vectors (the `q`'s), and `B pᵢ qⱼ = δᵢⱼ`. -/
structure IsSymplecticBasis (B : BilinForm K V) {ι : Type*} (e : Basis (ι ⊕ ι) K V) :
    Prop where
  inl_inl : ∀ i j, B (e (Sum.inl i)) (e (Sum.inl j)) = 0
  inr_inr : ∀ i j, B (e (Sum.inr i)) (e (Sum.inr j)) = 0
  inl_inr_self : ∀ i, B (e (Sum.inl i)) (e (Sum.inr i)) = 1
  inl_inr_of_ne : ∀ i j, i ≠ j → B (e (Sum.inl i)) (e (Sum.inr j)) = 0

/-- Attributed finite-dimensional Darboux construction, including the zero space.
The pairing convention has B(p_i,q_i)=+1; it is opposite to Mathlib's Matrix.J.
This theorem constructs a basis of a supplied form, without normalizing its energy. -/
theorem exists_isSymplecticBasis [FiniteDimensional K V] {B : BilinForm K V}
    (hB : B.IsAlt) (hnd : B.Nondegenerate) :
    ∃ (n : ℕ) (e : Basis (Fin n ⊕ Fin n) K V), IsSymplecticBasis B e := by
  let planeSumEquiv : ∀ (ι : Type v), Fin 2 ⊕ (ι ⊕ ι) ≃ Option ι ⊕ Option ι := fun ι => {
    toFun
      | Sum.inl i => ![Sum.inl none, Sum.inr none] i
      | Sum.inr (Sum.inl i) => Sum.inl (some i)
      | Sum.inr (Sum.inr i) => Sum.inr (some i)
    invFun
      | Sum.inl none => Sum.inl 0
      | Sum.inl (some i) => Sum.inr (Sum.inl i)
      | Sum.inr none => Sum.inl 1
      | Sum.inr (some i) => Sum.inr (Sum.inr i)
    left_inv := by
      rintro (i | i | i)
      · fin_cases i <;> rfl
      · rfl
      · rfl
    right_inv := by rintro ((_ | i) | (_ | i)) <;> rfl }
  have construction : ∀ (n : ℕ),
      ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (B : BilinForm K V),
        B.IsAlt → B.Nondegenerate → finrank K V = n →
        ∃ (ι : Type v) (_ : Fintype ι) (e : Basis (ι ⊕ ι) K V), IsSymplecticBasis B e := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro V _ _ _ B hB hnd hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · -- the trivial space
      have : Subsingleton V := Module.finrank_zero_iff.mp hn
      exact ⟨PEmpty, inferInstance, Basis.empty V,
        ⟨fun i => i.elim, fun i => i.elim, fun i => i.elim, fun i => i.elim⟩⟩
    · have : Nontrivial V := Module.finrank_pos_iff.mp (hn ▸ hpos)
      obtain ⟨p, hp⟩ := exists_ne (0 : V)
      -- a partner `q` with `B p q = 1`
      obtain ⟨q', hq'⟩ : ∃ q', B p q' ≠ 0 := by
        by_contra h
        push Not at h
        exact hp (hnd.1 p h)
      set q : V := (B p q')⁻¹ • q' with hq
      have hpq : B p q = 1 := by
        rw [hq, smul_right, inv_mul_cancel₀ hq']
      have hpp : B p p = 0 := hB.self_eq_zero p
      have hqq : B q q = 0 := hB.self_eq_zero q
      have hqp : B q p = -1 := by
        rw [← hB.neg_eq p q, hpq]
      have hrefl : B.IsRefl := hB.isRefl
      -- the symplectic plane `W = span {p, q}`
      have hli : LinearIndependent K ![p, q] := by
        rw [LinearIndependent.pair_iff' hp]
        intro a ha
        have h := congrArg (B p) ha
        rw [smul_right, hpp, mul_zero, hpq] at h
        exact zero_ne_one h
      set W : Submodule K V := span K (Set.range ![p, q]) with hW
      have hpW : p ∈ W := subset_span ⟨0, rfl⟩
      have hqW : q ∈ W := subset_span ⟨1, rfl⟩
      have hWrank : finrank K W = 2 := by
        rw [hW, finrank_span_eq_card hli, Fintype.card_fin]
      -- the form is non-degenerate on the plane
      have hWnd : (B.restrict W).Nondegenerate := by
        refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft (B := B.restrict W)
          (hrefl.domRestrict W)).mpr ?_
        intro w hw
        obtain ⟨c, hc⟩ := (mem_span_range_iff_exists_fun K).mp w.2
        have h0 : c 0 = 0 := by
          have h := hw ⟨q, hqW⟩
          rw [restrict_apply, ← hc] at h
          simpa [Fin.sum_univ_two, hpq, hqq] using h
        have h1 : c 1 = 0 := by
          have h := hw ⟨p, hpW⟩
          rw [restrict_apply, ← hc] at h
          simpa [Fin.sum_univ_two, hpp, hqp] using h
        ext
        rw [← hc]
        simp [Fin.sum_univ_two, h0, h1]
      have hc : IsCompl W (B.orthogonal W) :=
        isCompl_orthogonal_of_restrict_nondegenerate hrefl hWnd
      set W' : Submodule K V := B.orthogonal W with hW'
      have horth : ∀ (w : W') (x : V), x ∈ W → B x w = 0 := fun w x hx =>
        mem_orthogonal_iff.mp w.2 x hx
      have horth' : ∀ (w : W') (x : V), x ∈ W → B w x = 0 := fun w x hx =>
        hrefl.eq_zero (horth w x hx)
      -- the form is non-degenerate on the complement
      have hW'nd : (B.restrict W').Nondegenerate := by
        refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft (B := B.restrict W')
          (hrefl.domRestrict W')).mpr ?_
        intro w hw
        ext
        rw [Submodule.coe_zero]
        refine hnd.1 (w : V) fun z => ?_
        have hz : z ∈ W ⊔ W' := by
          rw [hc.sup_eq_top]
          exact Submodule.mem_top
        obtain ⟨y, hy, z', hz', rfl⟩ := Submodule.mem_sup.mp hz
        rw [map_add, horth' w y hy]
        have h2 : B (w : V) z' = 0 := by simpa using hw ⟨z', hz'⟩
        rw [h2, add_zero]
      have hW'alt : (B.restrict W').IsAlt := fun x => by
        rw [restrict_apply]
        exact hB.self_eq_zero _
      have hW'rank : finrank K W' = n - 2 := by
        rw [hW', finrank_orthogonal hnd W, hWrank, hn]
      obtain ⟨ι, _, f, hf⟩ :=
        ih (n - 2) (by omega) W' (B.restrict W') hW'alt hW'nd hW'rank
      -- assemble the basis of `V` from the plane and the complement
      let bW : Basis (Fin 2) K W := Basis.span hli
      have hbW : ∀ i, (bW i : V) = ![p, q] i := fun i =>
        congrArg Subtype.val (Basis.span_apply hli i)
      let e : Basis (Option ι ⊕ Option ι) K V :=
        ((bW.prod f).map (Submodule.prodEquivOfIsCompl W W' hc)).reindex (planeSumEquiv ι)
      have he_p : e (Sum.inl none) = p := by
        simp [e, Basis.reindex_apply, planeSumEquiv, Basis.map_apply, Basis.prod_apply, hbW]
      have he_q : e (Sum.inr none) = q := by
        simp [e, Basis.reindex_apply, planeSumEquiv, Basis.map_apply, Basis.prod_apply, hbW]
      have he_l : ∀ i, e (Sum.inl (some i)) = (f (Sum.inl i) : V) := by
        intro i
        simp [e, Basis.reindex_apply, planeSumEquiv, Basis.map_apply, Basis.prod_apply]
      have he_r : ∀ i, e (Sum.inr (some i)) = (f (Sum.inr i) : V) := by
        intro i
        simp [e, Basis.reindex_apply, planeSumEquiv, Basis.map_apply, Basis.prod_apply]
      refine ⟨Option ι, inferInstance, e, ⟨?_, ?_, ?_, ?_⟩⟩
      · rintro (_ | i) (_ | j)
        · rw [he_p]
          exact hpp
        · rw [he_p, he_l]
          exact horth _ _ hpW
        · rw [he_l, he_p]
          exact horth' _ _ hpW
        · rw [he_l, he_l]
          simpa using hf.inl_inl i j
      · rintro (_ | i) (_ | j)
        · rw [he_q]
          exact hqq
        · rw [he_q, he_r]
          exact horth _ _ hqW
        · rw [he_r, he_q]
          exact horth' _ _ hqW
        · rw [he_r, he_r]
          simpa using hf.inr_inr i j
      · rintro (_ | i)
        · rw [he_p, he_q]
          exact hpq
        · rw [he_l, he_r]
          simpa using hf.inl_inr_self i
      · rintro (_ | i) (_ | j) hij
        · exact absurd rfl hij
        · rw [he_p, he_r]
          exact horth _ _ hpW
        · rw [he_l, he_q]
          exact horth' _ _ hqW
        · rw [he_l, he_r]
          exact (by simpa using hf.inl_inr_of_ne i j fun h => hij (h ▸ rfl))
  obtain ⟨ι, _, e, he⟩ := construction (finrank K V) V B hB hnd rfl
  let σ := Fintype.equivFin ι
  refine ⟨Fintype.card ι, e.reindex (σ.sumCongr σ), ⟨?_, ?_, ?_, ?_⟩⟩
  · intro i j
    simp only [Basis.reindex_apply, Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inl]
    exact he.inl_inl _ _
  · intro i j
    simp only [Basis.reindex_apply, Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inr]
    exact he.inr_inr _ _
  · intro i
    simp only [Basis.reindex_apply, Equiv.sumCongr_symm, Equiv.sumCongr_apply,
      Sum.map_inl, Sum.map_inr]
    exact he.inl_inr_self _
  · intro i j hij
    simp only [Basis.reindex_apply, Equiv.sumCongr_symm, Equiv.sumCongr_apply,
      Sum.map_inl, Sum.map_inr]
    exact he.inl_inr_of_ne _ _ (σ.symm.injective.ne hij)

#print axioms exists_isSymplecticBasis

end D5.S3.QuadraticForms.SymplecticBasis
