import GRH.Lib.GaloisRep.BaseChange.ParahoricColumns
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Exponents, U-operators and spherical vectors at pro-p Iwahori level; conjugacy in I t I
(known result; see Lib.LocalGL.Tadic.ChainLemma).

This file: U operator preserves character eigenspaces of the parahoric stabilising a line. -/
seal Finset.univ Finset.sum Finset.prod

open Valued WithZero Matrix Subgroup Pi


variable {E} [Field E] [NumberField E] {w : FinPlace E} {N} [NeZero N] {g : GL (Fin N) (LocField w)}
  (ρ : Rep ℂ (GL (Fin N) (LocField w))) [IsSmoothRep ρ.ρ]

/-- For g in GL_N(𝒪_w) whose first column vanishes modulo w below the diagonal, some u in the
pro-p Iwahori subgroup `proIwahori` makes the first row of ug zero off the diagonal. -/
lemma exists_clear_first_row (hg : g ∈ blockParahoric (min 1)) : ∃ u ∈ proIwahori, ∀ j ≠ 0,
  (u * g :) 0 j = 0 := by refine ⟨.mk'' (updateRow 1 0
  ((g⁻¹ 0 0)⁻¹ • g⁻¹ 0)) ?_, ?_⟩ <;> simp [mem_proIwahori, updateRow_mul, ← cramer_transpose_apply,
  smul_vecMul, -coe_units_inv, ← mul_apply_eq_vecMul, updateRow_apply] <;> grind [one_pos, sub_self,
  mem_intGL, v.mem_integer_iff, exists_v_entry_eq_one_of_mem_intGL hg.1 0, inv_one, map_inv₀]

/-- The vectors fixed by the pro-p Iwahori group on which each k in the parahoric subgroup
`blockParahoric` f acts by the scalar c(k). -/
noncomputable def parahoricEigenspace f (c : _ → ℂ) := levelSpace ρ.ρ proIwahori ⊓ by
  use! {z | ∀ k ∈ blockParahoric f, ρ k z = c k • z} <;> simp_all [smul_comm (c _)]

/-- For smooth ρ, a uniformiser ϖ and any function χ, the pro-p Iwahori Hecke operator of
diag(ϖ,1,…,1) preserves the pro-p Iwahori fixed vectors on which each integral k fixing the
first coordinate line modulo ϖ acts by χ of its top left entry. -/
lemma heckeCoset_mem_parahoricEigenspace {ϖ : (LocField w)ˣ} (hϖ : v ϖ.1 =
  exp (-1)) {χ} : let t := diagGL (mulSingle 0 ϖ)
  parahoricEigenspace ρ (min 1) (χ ∘ (· 0 0)) ∈ (heckeCoset ρ.ρ proIwahori t).invtSubmodule := by
  intro t y ⟨h₀, (hy : ∀ k, _)⟩
  -- the mean over the stabiliser `S` of `y`, normal in the parahoric, which contains `proIwahori`
  let S := blockParahoric (min 1) ⊓ (MulAction.stabilizer _ y).comap ρ.ρ.toHomUnits
  have : CompactSpace S := (isCompact_residuePreimage.inter_right
    (isClosed_of_isOpen _ (isOpen_of_mem_nhds _ (IsSmoothRep.eventually_fixed y)))).compactSpace
  have D k (hk : k ∈ blockParahoric _) : ρ k (compactMean _ S (ρ t y)) = compactMean _ proIwahori (ρ
    t (ρ k y)) := .trans (compactMean_eq_self _ fun g ↦ by simpa using (apply_compactMean (H := S)
    ⟨(blockParahoric _).mul_mem (mul_mem (inv_mem hk) (proIwahori_le_blockParahoric (by omega) g.2))
    hk, show ρ _ y = y by simp; simp_all⟩ _)).symm <| map_compactMean_of_const (_ ∘ₗ _) fun g ⟨h,
    (_ : ρ g y = y)⟩ ↦ (exists_clear_first_row (mul_mem hk h)).elim
    -- conjugation by `t` keeps the action on `y` of an element with cleared first row
    fun u ⟨hu, r⟩ ↦ have m := mul_mem (proIwahori_le_blockParahoric (by omega) hu) (mul_mem hk h)
    by simpa [h₀ ⟨u, hu⟩, t, *] using congr(compactMean ρ.ρ proIwahori (ρ
      t $(((hy _ (conj_monomial_mem_blockParahoric (mulSingle (0 : Fin N) ϖ) 1 ⊤
      ⟨m, by simp⟩ (by grind [Equiv.Perm.one_apply, Units.val_one, log_one, log_exp])).1).trans
      (by simp [← map_inv, mul_comm])).trans (hy _ m).symm)))
  simp_all [parahoricEigenspace, heckeCoset_mulSingle_zero_eq hϖ, by simpa using D 1, t,
    smul_comm (χ _)]
