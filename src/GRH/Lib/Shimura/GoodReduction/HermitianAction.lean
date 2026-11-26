import GRH.Lib.Shimura.GoodReduction.ThetaOrthogonality
import GRH.Lib.Shimura.AbelianScheme.ThetaFamily
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Good reduction of unitary PEL abelian varieties, in analytic form (no toric
degeneration) (known result; see Lib.Shimura.GoodReduction.ArcReduction).

This file: Polarised torus with multiplications: canonical multiplier, normalised translations,
isogeny kernels and degree. -/

noncomputable section

open Complex ComplexConjugate QuotientAddGroup LinearMap LinearEquiv NeZero Algebra.IsAlgebraic


variable {V R : Type} [FinComplexSpace V] [CommRing R] [StarRing R] (L : Submodule ℤ V) (B :
  LatticeForm L) (F : R →+* V →L[ℂ] V) (β : R) [IsDomain R] [Module.Finite ℤ R]

/-- B is a positive definite hermitian form with Riemann form integral on L, the action F of R
preserves L with ā adjoint to a, and β̄ = 1 − β. -/
structure IsHermitianAction where
  map_mem a : ∀ l ∈ L, F a l ∈ L
  conj_symm x y : B x y = conj (B y x)
  pos : ∀ x ≠ 0, 0 < (B x x).re
  adjoint a x y : B (F a x) y = B x (F (star a) y)
  riemannForm_integral : ∀ᵉ (l ∈ L) (m ∈ L), ∃ n : ℤ, B.riemannForm l m = n
  star_eq_one_sub : star β = 1 - β

variable {L} {B} {F} {β} {x : V} {y : V} {f : V → ℂ} (h : IsHermitianAction L B F β) (a : R)
  [NeZero a]

instance : NeZero (star a) := ⟨by simp [ne]⟩

omit [StarRing R] [IsDomain R] [Module.Finite ℤ R] in
lemma action_comm r s x : F r (F s x) = F s (F r x) := congr($((Commute.all ..).map F) _)

omit [StarRing R] in
lemma action_injective : (⇑(F a)).Injective := (exists_smul_eq_mul ℤ 1 (ne a)).elim fun b ⟨_, r,
  e⟩ x y k ↦ by simpa [k, r, action_comm a, ← Int.cast_smul_eq_zsmul ℂ] using congr(F $e x = F $e y)

omit [StarRing R] in
@[simp] lemma action_isInvertible : (F a).IsInvertible :=
  ⟨(ofInjectiveEndo _ (action_injective a)).toContinuousLinearEquiv, rfl⟩

namespace IsHermitianAction

/-- The canonical multiplier x ↦ exp(πi E(βx, x)) of the hermitian data, where E is the Riemann
form of B. -/
@[simp] abbrev multiplier (_ : IsHermitianAction L B F β) := canonicalMultiplier B (F β)

/-- Normalised translation by x, acting on functions V → ℂ: the twisted translation
`thetaShift` for B, divided by exp(πi E(βx, x)), E the Riemann form of B. -/
@[simp] abbrev normShift (_ : IsHermitianAction L B F β) := normalizedShift B (F β)

/-- The lattice a⁻¹L: the additive subgroup of the vectors y of V with ay in L, where a acts
through F. -/
def divLattice (_ : IsHermitianAction L B F β) a := L.toAddSubgroup.comap (F a).toAddMonoidHom

/-- The kernel of multiplication by a on the torus V/L. -/
abbrev MulKernel := _ ⧸ L.toAddSubgroup.addSubgroupOf (h.divLattice a)

omit [IsDomain R] [Module.Finite ℤ R] [NeZero a] in
@[simp] lemma map_divLattice_mem (z : h.divLattice a) : F a z ∈ L := z.2

omit [IsDomain R] [Module.Finite ℤ R] [NeZero a] in
lemma out_mem_iff_eq_zero (z : h.MulKernel a) : z.out.1 ∈ L ↔ z = 0 :=
  (out_eq' z ▸ eq_zero_iff _).symm

include h

section

omit [IsDomain R] [Module.Finite ℤ R]

lemma riemannForm_beta u w : B.riemannForm (F β u) w =
  B.riemannForm u w - B.riemannForm u (F β w) := by simp [riemannForm, h.4, h.6]; ring

lemma isAppellHumbert : IsAppellHumbert B h.multiplier := by grind
  [isAppellHumbert_canonicalMultiplier, riemannForm_beta, IsHermitianAction, conj_re]

lemma riemannPhase_eq_one {a} (hx : x ∈ B.dualLattice) (hy : F (star a) y ∈ L) :
  B.riemannPhase (F a x) y = 1 :=
  by grind [hx _ hy, riemannForm_def, IsHermitianAction, Circle.coe_eq_one, fourierChar_eq_one]

lemma multiplier_eq_exp : h.multiplier x = exp (B x (F (star β) x) - B x x / 2) := by grind
  [canonicalMultiplier, h.isAppellHumbert.sub_eq_riemannForm, IsHermitianAction]

lemma nsmul {m} (hm : m ≠ 0) : IsHermitianAction L (m • B) F β := by use h.1, ?_, ?_, ?_,
  (h.isAppellHumbert.nsmul _).le_dualLattice, h.6 <;> simp_all [← h.2, hm.pos, h.3, h.4]

end

variable [IsFullRankLattice L]

lemma card_mulKernel : Nat.card (h.MulKernel a) = (F a).det * conj (F a).det :=
  relIndex_comap_lattice (h.1 a) (action_injective a)

instance : Fintype (h.MulKernel a) := AddSubgroup.fintypeOfIndexNeZero (ne_of_apply_ne _
  ((h.card_mulKernel a).trans_ne (by simp [det_eq_zero_iff_ker_ne_bot, ker_eq_bot,
  action_injective])))

/-- Let f be fixed by the normalised translations by aL, ξ a character of the finite kernel of a
on V/L, and s = ∑_k ξ(−k)·(translate of f by ak). If ay ∈ L, the normalised translation by
ay multiplies s by ξ(y). -/
lemma normShift_sum_eq_char_smul (hf : ∀ l ∈ L, h.normShift (F a l) f = f) (ξ :
  AddChar (h.MulKernel a) ℂ) (y : h.divLattice a) {s}
  (hs : s = ∑ k, ξ (-k) • h.normShift (F a k.out) f) : h.normShift (F a y) s = ξ y • s := by
  rw [hs, map_sum, Finset.smul_sum, Fintype.sum_equiv (.addLeft ↑y)]
  intro k; have ⟨l, e⟩ := mk_out_eq_add (L.toAddSubgroup.addSubgroupOf _) (y + k.out)
  nth_rw 1 [← hf _ l.2]
  simp_all [h.isAppellHumbert.normalizedShift_normalizedShift h.riemannForm_beta,
    ↓h.riemannPhase_eq_one (h.5 _ _) (h.1 ..), smul_smul, ← ξ.map_add_eq_mul, add_mem, add_assoc]
