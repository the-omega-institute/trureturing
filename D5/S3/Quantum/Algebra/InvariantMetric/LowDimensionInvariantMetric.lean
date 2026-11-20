/- GID: D5/S3/Quantum/Algebra/InvariantMetric/LowDimensionInvariantMetric
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/InvariantMetric/LowDimensionInvariantMetric
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Lie algebras with an invariant form in dimension at most three. -/

import Mathlib.Algebra.Lie.InvariantForm
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Real.Sqrt

/-!
# Lie algebras with an invariant form in dimension at most three

A bilinear form `Φ` on a Lie algebra `L` is invariant (`Φ.lieInvariant L`) when
`Φ ⁅x, y⁆ z = -Φ y ⁅x, z⁆` for all `x y z`, that is, when every `ad x` is skew for `Φ`.
No symmetry of `Φ` is assumed anywhere in this file.

For an invariant form a bracket `⁅x, y⁆` is orthogonal to both `x` and `y`, in either slot of
the form. Two consequences are proved.

* `isLieAbelian_of_finrank_le_two`: over a field, a Lie algebra of dimension at most two with a
  left-separating invariant form is abelian. If `⁅x, y⁆ ≠ 0`, then `x, y` are linearly
  independent and span `L`, and `Φ ⁅x, y⁆` vanishes on `x` and on `y`, hence on `L`.
* `exists_basis_bracket_eq_smul_cross`: a non-abelian real Lie algebra of dimension three with
  an invariant form positive on nonzero vectors has a basis, orthonormal for the form, in whose
  coordinates the bracket is `c` times the cross product for some `c > 0`. If `⁅x, y⁆ ≠ 0`,
  the vectors `x`, `⁅x, y⁆` and `⁅x, ⁅x, y⁆⁆` are non-zero and pairwise orthogonal; after
  normalisation the bracket of the first two is a positive multiple of the third, and invariance
  then fixes every structure constant.

In the first statement each hypothesis is needed: without invariance, take the
two-dimensional affine Lie algebra with the standard dot product; without separation, the same
algebra with the zero form; without finite dimension, `so(3)` plus an infinite-dimensional
abelian summand, whose `finrank` is zero. In the second statement positivity cannot be
weakened to non-degeneracy: `sl(2, ℝ)` with its Killing form is invariant and non-degenerate.
-/

namespace D5.S3.Quantum.Algebra.InvariantMetric.LowDimensionInvariantMetric

open Module

section Orthogonality

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  {Φ : LinearMap.BilinForm R L}

/-- For an invariant form, `⁅x, y⁆` is orthogonal to `x` in the left slot. -/
private theorem bracket_left_self (hΦ : Φ.lieInvariant L) (x y : L) : Φ ⁅x, y⁆ x = 0 := by
  rw [hΦ x y x, lie_self, map_zero, neg_zero]

/-- For an invariant form, `⁅x, y⁆` is orthogonal to `y` in the left slot. -/
private theorem bracket_left_right (hΦ : Φ.lieInvariant L) (x y : L) : Φ ⁅x, y⁆ y = 0 := by
  rw [← lie_skew, map_neg, LinearMap.neg_apply, hΦ y x y, lie_self, map_zero, neg_zero,
    neg_zero]

/-- For an invariant form, `⁅x, y⁆` is orthogonal to `x` in the right slot. -/
private theorem self_bracket_right (hΦ : Φ.lieInvariant L) (x y : L) : Φ x ⁅x, y⁆ = 0 := by
  have h := hΦ x x y
  rw [lie_self, map_zero, LinearMap.zero_apply] at h
  exact neg_eq_zero.mp h.symm

/-- For an invariant form, `⁅x, y⁆` is orthogonal to `y` in the right slot. -/
private theorem right_bracket_right (hΦ : Φ.lieInvariant L) (x y : L) : Φ y ⁅x, y⁆ = 0 := by
  have h := hΦ x y y
  rw [bracket_left_right hΦ] at h
  exact neg_eq_zero.mp h.symm

end Orthogonality

/-- A Lie algebra of dimension at most two over a field that carries a left-separating
invariant bilinear form is abelian. -/
theorem isLieAbelian_of_finrank_le_two {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [FiniteDimensional K L]
    (Φ : LinearMap.BilinForm K L) (hΦ : Φ.lieInvariant L) (hsep : LinearMap.SeparatingLeft Φ)
    (hL : finrank K L ≤ 2) :
    IsLieAbelian L := by
  refine ⟨fun x y => ?_⟩
  by_contra hxy
  have hx : x ≠ 0 := by
    rintro rfl
    exact hxy (zero_lie y)
  have hli : LinearIndependent K ![x, y] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      have h := congrArg (fun w => ⁅x, w⁆) hst
      simp only [lie_add, lie_smul, lie_self, smul_zero, zero_add, lie_zero] at h
      exact (smul_eq_zero.mp h).resolve_right hxy
    subst ht
    rw [zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.mp hst).resolve_right hx, rfl⟩
  have hcard : Fintype.card (Fin 2) = finrank K L := by
    have h1 := finrank_span_eq_card hli
    have h2 := Submodule.finrank_le (Submodule.span K (Set.range ![x, y]))
    rw [Fintype.card_fin] at h1 ⊢
    omega
  have hspan := hli.span_eq_top_of_card_eq_finrank' hcard
  have hzero : Φ ⁅x, y⁆ = 0 := by
    refine LinearMap.ext_on_range hspan fun i => ?_
    fin_cases i
    · simp [bracket_left_self hΦ]
    · simp [bracket_left_right hΦ]
  exact hxy (hsep _ fun z => by rw [hzero, LinearMap.zero_apply])

section Real

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] {Φ : LinearMap.BilinForm ℝ L}

/-- A vector with positive square under a real bilinear form has a positive multiple of
square one. -/
private theorem exists_smul_self_eq_one {a : L} (ha : 0 < Φ a a) :
    ∃ s : ℝ, 0 < s ∧ Φ (s • a) (s • a) = 1 := by
  have hq : 0 < √(Φ a a) := Real.sqrt_pos.mpr ha
  refine ⟨(√(Φ a a))⁻¹, inv_pos.mpr hq, ?_⟩
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [show (√(Φ a a))⁻¹ * ((√(Φ a a))⁻¹ * Φ a a) = Φ a a / (√(Φ a a) * √(Φ a a)) by ring,
    Real.mul_self_sqrt ha.le, div_self ha.ne']

/-- If a three-dimensional real Lie algebra with an invariant form has vectors `e₁, e₂, e₃`
of square one with `Φ e₁ e₂ = Φ e₂ e₁ = 0` and `⁅e₁, e₂⁆ = κ • e₃`, `κ > 0`, then it has a
`Φ`-orthonormal basis in whose coordinates the bracket is a positive multiple of the cross
product. -/
private theorem cross_frame (hΦ : Φ.lieInvariant L) (hL : finrank ℝ L = 3) {e₁ e₂ e₃ : L}
    {κ : ℝ} (hκ : 0 < κ) (h11 : Φ e₁ e₁ = 1) (h22 : Φ e₂ e₂ = 1) (h33 : Φ e₃ e₃ = 1)
    (h12 : Φ e₁ e₂ = 0) (h21 : Φ e₂ e₁ = 0) (hb : ⁅e₁, e₂⁆ = κ • e₃) :
    ∃ (b : Basis (Fin 3) ℝ L) (c : ℝ), 0 < c ∧
      (∀ i j, Φ (b i) (b j) = if i = j then 1 else 0) ∧
      ∀ x y : L, b.equivFun ⁅x, y⁆ = c • crossProduct (b.equivFun x) (b.equivFun y) := by
  have h13 : Φ e₁ e₃ = 0 := by
    have h := self_bracket_right hΦ e₁ e₂
    rw [hb, map_smul, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_left hκ.ne'
  have h31 : Φ e₃ e₁ = 0 := by
    have h := bracket_left_self hΦ e₁ e₂
    rw [hb, map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_left hκ.ne'
  have h23 : Φ e₂ e₃ = 0 := by
    have h := right_bracket_right hΦ e₁ e₂
    rw [hb, map_smul, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_left hκ.ne'
  have h32 : Φ e₃ e₂ = 0 := by
    have h := bracket_left_right hΦ e₁ e₂
    rw [hb, map_smul, LinearMap.smul_apply, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_left hκ.ne'
  let v : Fin 3 → L := ![e₁, e₂, e₃]
  have hON : ∀ i j, Φ (v i) (v j) = if i = j then 1 else 0 := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [v, h11, h22, h33, h12, h21, h13, h31, h23, h32]
  have hli : LinearIndependent ℝ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h := congrArg (fun z => Φ z (v i)) hg
    simpa [map_sum, hON] using h
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hL])
  have hbv : ⇑b = v := coe_basisOfLinearIndependentOfCardEqFinrank hli _
  have hcoord : ∀ z, b.equivFun z = fun k => Φ z (v k) := by
    intro z
    funext k
    conv_rhs => rw [← b.sum_repr z]
    simp [map_sum, hbv, hON, Basis.equivFun_apply]
  have hexp : ∀ z, z = Φ z e₁ • e₁ + Φ z e₂ • e₂ + Φ z e₃ • e₃ := by
    intro z
    conv_lhs => rw [← b.sum_repr z]
    simp [Fin.sum_univ_three, ← Basis.equivFun_apply, hcoord, hbv, v]
  have hb21 : ⁅e₂, e₁⁆ = -(κ • e₃) := by rw [← lie_skew, hb]
  have hb23 : ⁅e₂, e₃⁆ = κ • e₁ := by
    have h1 : Φ ⁅e₂, e₃⁆ e₁ = κ := by
      rw [hΦ e₂ e₃ e₁, hb21]
      simp [h33]
    refine (hexp _).trans ?_
    rw [h1, bracket_left_self hΦ, bracket_left_right hΦ, zero_smul, zero_smul, add_zero,
      add_zero]
  have hb32 : ⁅e₃, e₂⁆ = -(κ • e₁) := by rw [← lie_skew, hb23]
  have hb31 : ⁅e₃, e₁⁆ = κ • e₂ := by
    have h2 : Φ ⁅e₃, e₁⁆ e₂ = κ := by
      rw [hΦ e₃ e₁ e₂, hb32]
      simp [h11]
    refine (hexp _).trans ?_
    rw [h2, bracket_left_self hΦ, bracket_left_right hΦ, zero_smul, zero_smul, add_zero,
      zero_add]
  have hb13 : ⁅e₁, e₃⁆ = -(κ • e₂) := by rw [← lie_skew, hb31]
  refine ⟨b, κ, hκ, fun i j => by rw [hbv]; exact hON i j, fun x y => ?_⟩
  let B₁ : L →ₗ[ℝ] L →ₗ[ℝ] (Fin 3 → ℝ) :=
    (LieModule.toEnd ℝ L L : L →ₗ[ℝ] Module.End ℝ L).compr₂ b.equivFun.toLinearMap
  let B₂ : L →ₗ[ℝ] L →ₗ[ℝ] (Fin 3 → ℝ) :=
    κ • crossProduct.compl₁₂ b.equivFun.toLinearMap b.equivFun.toLinearMap
  have hB : B₁ = B₂ := by
    refine b.ext fun i => b.ext fun j => ?_
    simp only [B₁, B₂, LinearMap.compr₂_apply, LinearMap.smul_apply, LinearMap.compl₁₂_apply,
      LieHom.coe_toLinearMap, LieModule.toEnd_apply_apply, LinearEquiv.coe_coe, hcoord, hbv]
    funext k
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp [v, cross_apply, hb, hb21, hb23, hb32, hb31, hb13, h11, h22, h33, h12, h21, h13, h31,
        h23, h32]
  have h := LinearMap.congr_fun₂ hB x y
  simpa [B₁, B₂] using h

end Real

/-- A non-abelian real Lie algebra of dimension three with an invariant bilinear form that is
positive on nonzero vectors has a basis, orthonormal for the form, in whose coordinates the
bracket is a positive multiple of the cross product. Evaluating the conclusion on basis vectors
gives `⁅b 0, b 1⁆ = c • b 2`, `⁅b 1, b 2⁆ = c • b 0` and `⁅b 2, b 0⁆ = c • b 1`, and
orthonormality on a basis shows that the form is symmetric. -/
theorem exists_basis_bracket_eq_smul_cross {L : Type*} [LieRing L] [LieAlgebra ℝ L]
    (Φ : LinearMap.BilinForm ℝ L) (hΦ : Φ.lieInvariant L) (hpos : ∀ x : L, x ≠ 0 → 0 < Φ x x)
    (hL : finrank ℝ L = 3) (hna : ¬ IsLieAbelian L) :
    ∃ (b : Basis (Fin 3) ℝ L) (c : ℝ), 0 < c ∧
      (∀ i j, Φ (b i) (b j) = if i = j then 1 else 0) ∧
      ∀ x y : L, b.equivFun ⁅x, y⁆ = c • crossProduct (b.equivFun x) (b.equivFun y) := by
  obtain ⟨x, y, hxy⟩ : ∃ x y : L, ⁅x, y⁆ ≠ 0 := by
    by_contra h
    exact hna ⟨fun x y => by_contra fun hne => h ⟨x, y, hne⟩⟩
  have hx : x ≠ 0 := by
    rintro rfl
    exact hxy (zero_lie y)
  have hxw : ⁅x, ⁅x, y⁆⁆ ≠ 0 := by
    intro h
    have h1 := hΦ x ⁅x, y⁆ y
    rw [h, map_zero, LinearMap.zero_apply] at h1
    have h2 := hpos _ hxy
    linarith
  obtain ⟨s, hs, hs1⟩ := exists_smul_self_eq_one (hpos x hx)
  obtain ⟨t, ht, ht1⟩ := exists_smul_self_eq_one (hpos _ hxy)
  have huv : ⁅s • x, t • ⁅x, y⁆⁆ ≠ 0 := by
    simp [smul_lie, lie_smul, hs.ne', ht.ne', hxw]
  have h12 : Φ (s • x) (t • ⁅x, y⁆) = 0 := by
    simp [self_bracket_right hΦ]
  have h21 : Φ (t • ⁅x, y⁆) (s • x) = 0 := by
    simp [bracket_left_self hΦ]
  obtain ⟨r, hr, hr1⟩ := exists_smul_self_eq_one (hpos _ huv)
  refine cross_frame hΦ hL (inv_pos.mpr hr) hs1 ht1 hr1 h12 h21 ?_
  rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

end D5.S3.Quantum.Algebra.InvariantMetric.LowDimensionInvariantMetric
