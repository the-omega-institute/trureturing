import GRH.Lib.LocalGL.Green.MackeyFormula
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Green's characters of GL_n(F_q) and the parabolic-induction ring (known result; see
Lib.LocalGL.Green.LabelDegree).

This file: Frobenius reciprocity between parabolic induction and block means on GL_n(F_q). -/

open Finset Fint LinearMap Module MulAction Pointwise Submodule GeneralLinearGroup

attribute [local simp] LinearMap.ext_iff

variable {k V} [Field k] [Finite k] [AddCommGroup V] [Module k V] [Module.Finite k V] {F H} (n)

omit [Finite k] in
lemma Hall.simClassOf_out_eq_one_iff {a : End k V} : (∀ x, (simClassOf a).out.2 x = x) ↔ a = 1 :=
  (exists_equiv_simClassOf_out a).rec (by simp [·.surjective.forall, ← ·])

lemma Hall.rankInner_eq_classInner_simClassOf : rankInner (finrank k V) F H =
  @classInner (End k V)ˣ (F <| simClassOf ·.1) (H <| simClassOf ·.1) :=
  finMean_equiv (congrLinearEquiv _).1 (by congr! <;> exact (Quot.sound ⟨_, rfl⟩).symm)

/-- For class functions F, H on matrices over the finite field k, the average over GL_ι(k) of
conj F(g) · H(g) is the inner product `Hall.rankInner` of F and H in rank |ι|. -/
lemma Hall.classInner_evalGL {ι} [Fintype ι] : @classInner (GL ι k) F.evalGL H.evalGL =
  rankInner (Fintype.card ι) F H := by simp_rw [← finrank_pi k, rankInner_eq_classInner_simClassOf,
  classInner, finMean_equiv Matrix.GeneralLinearGroup.toLin.1]; rfl

/-- Frobenius reciprocity for the induction product over a finite field k: the rank n pairing
⟨A∗B, X⟩ equals the sum over i + j = n of the rank i pairings of A with `Hall.skew` j B
X. -/
lemma Hall.rankInner_mul_eq_sum_skew (X A B : Hall k) :
    rankInner n (A * B) X = ∑ p ∈ antidiagonal n, rankInner p.1 A (skew p.2 B X) := by
  let d (U : Submodule k (Fin n → k)) := finrank k U
  have S g {U y} h (H : d y = _) := eq_of_le_of_finrank_eq (map_le_iff_le_comap.2 h)
    (((toLinearEquiv g).finrank_map_eq U).trans H.symm)
  rw [Nat.antidiagonal_eq_map, sum_map, rankInner, finMean, ← fun M ↦ (sum_comp (M · / (#_ : ℂ))
    d).trans (.symm (sum_congr (f := M) (Subset.antisymm (fun _ _ ↦ mem_image.2 ⟨_, mem_univ _,
    (finrank_range_of_inj (finrank_le_iff_exists_linearMap.1 (by aesop)).choose_spec).trans
    (finrank_fin_fun k)⟩) (by simp [subset_iff, (finrank_le _).trans, d])) (by simp [field])))]
  simp [mul_simClassOf, sum_mul, sum_sigma']
  rw [← Equiv.sum_comp (ι := Σ U, stabilizer _ U) (.mk (⟨_, _, map_le_iff_le_comap.1 ·.2.2.le⟩)
    fun ⟨g, U, h⟩ ↦ ⟨U, g, S _ h rfl⟩), Fintype.sum_sigma, sum_div]; congr with U
  have ⟨Z, h⟩ := U.exists_isCompl; let e := Z.prodEquivOfIsCompl U h.symm
  rw [← card_orbit_mul_card_stabilizer_eq_card_group _ U, Nat.cast_mul, div_mul_eq_div_div_swap,
    ← finMean_eq, finMean_equiv ⟨fun t ↦ (⟨congrLinearEquiv e (ofLinearEquiv (.skewProd
    t.2.1.toLinearEquiv t.1.toLinearEquiv t.2.2)), S (congrLinearEquiv e _) (Subtype.forall'.2
    (by simp [e])) rfl⟩ : stabilizer _ U), fun ⟨g, H⟩ ↦ (ofLinearEquiv (g.toLinearEquiv.ofSubmodules
    _ _ (id H)), congrLinearEquiv (U.quotientEquivOfIsCompl Z h) (ofLinearEquiv (Quotient.equiv U U
    g.toLinearEquiv (id H))), U.projectionOnto Z h ∘ₗ domRestrict g Z), by aesop_cat, fun _ ↦ by
    ext : 2; simp [e]; grind [projection_add_projection_eq_self]⟩ fun _ ↦ rfl]
  simp [↓Equiv.coe_fn_mk, d, finMean_prod, rankInner_eq_classInner_simClassOf,
    blockAverage_simClassOf, skew, classInner, mul_assoc, ← finMean_const_mul,
    by simpa using e.finrank_eq.symm]
  congr! <;> [skip; apply simClassOf_endOnQuot (s :=
    projectionOnto_surjective h.symm); apply simClassOf_eq_of_equiv
    e.symm _; use fun ⟨g, h⟩ ↦ h ▸ (toLinearEquiv g).finrank_map_eq U, fun H ↦
    (exists_linearEquiv_restrict_eq (.ofFinrankEq _ _ H.symm)).rec fun g e ↦ ⟨_, S (ofLinearEquiv g)
    (by simp [← e ⟨·, ·⟩]) H⟩] <;> simp [e, StableSubspace.endOnSub, restrict_apply, add_comm]
