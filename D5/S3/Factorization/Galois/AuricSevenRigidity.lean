/- GID: D5/S3/Factorization/Galois/AuricSevenRigidity
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/AuricSevenRigidity
   mirror-E: none(waiver:algebraically-proved)
   anchors: [mathlib/module/Mathlib.Algebra.Algebra.Operations, mathlib/module/Mathlib.LinearAlgebra.Dimension.Free]
   utility: none
   digest: Low intersection multiplicities and quotient inclusion force homothety in degree seven. -/

import Mathlib.Algebra.Algebra.Operations
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Prod
import Mathlib.RingTheory.Trace.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Quotient rigidity in degree seven

All quotients and products are taken in the original extension field. The
intersection multiplicity counts the dimension of the intersection with the
actual multiplicative translate, rather than a formal label space.
-/

namespace D5.S3.Factorization.Galois.AuricSevenRigidity

open Module Submodule

set_option maxRecDepth 4000
set_option maxHeartbeats 200000

variable {F D : Type*} [Field F] [Field D] [Algebra F D]

/-- Nonzero quotients of elements of a subspace, in the same field. -/
def quotientSet (W : Submodule F D) : Set D :=
  {r | ∃ u ∈ W, ∃ v ∈ W, u ≠ 0 ∧ v ≠ 0 ∧ u / v = r}

/-- Multiplicative translation inside the extension field. -/
def translate (r : D) (W : Submodule F D) : Submodule F D :=
  W.map (LinearMap.mulLeft F r)

/-- The original low-intersection condition, only outside the base field. -/
def LowIntersection (U : Submodule F D) : Prop :=
  ∀ r : D, r ≠ 0 → r ∉ Set.range (algebraMap F D) →
    finrank F (U ⊓ translate r U : Submodule F D) ≤ 1

private noncomputable def mulEquiv (a : D) (ha : a ≠ 0) : D ≃ₗ[F] D where
  toLinearMap := LinearMap.mulLeft F a
  invFun x := a⁻¹ * x
  left_inv x := by simp [ha]
  right_inv x := by simp [ha]

private lemma translate_finrank (a : D) (ha : a ≠ 0) (W : Submodule F D) :
    finrank F (translate a W) = finrank F W :=
  (mulEquiv a ha).finrank_map_eq W

private lemma mem_translate {a x : D} {W : Submodule F D} :
    x ∈ translate a W ↔ ∃ y ∈ W, a * y = x := Iff.rfl

private lemma translate_inf (a : D) (ha : a ≠ 0) (W Z : Submodule F D) :
    translate a (W ⊓ Z) = translate a W ⊓ translate a Z := by
  exact Submodule.map_inf (LinearMap.mulLeft F a) (mulEquiv a ha).injective

private lemma translate_translate (a b : D) (W : Submodule F D) :
    translate a (translate b W) = translate (a * b) W := by
  simp only [translate, ← Submodule.map_comp]
  congr 1
  ext x
  simp

private lemma translate_one (W : Submodule F D) : translate 1 W = W := by
  ext x
  simp [mem_translate]

private lemma translated_intersection (U : Submodule F D) (p q : D) (hp : p ≠ 0) :
    finrank F (translate p U ⊓ translate q U : Submodule F D) =
      finrank F (U ⊓ translate (q / p) U : Submodule F D) := by
  have he : translate p (U ⊓ translate (q / p) U) =
      translate p U ⊓ translate q U := by
    rw [translate_inf p hp, translate_translate]
    congr 1
    field_simp
  rw [← he, translate_finrank p hp]

private lemma ratio_not_base {p q : D} (hp : p ≠ 0)
    (h : LinearIndependent F ![q, p]) : q / p ∉ Set.range (algebraMap F D) := by
  rintro ⟨c, hc⟩
  apply (linearIndependent_fin2.mp h).2 c
  simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [Algebra.smul_def]
  rw [hc]
  exact div_mul_cancel₀ q hp

private lemma product_finrank_lower [FiniteDimensional F D] [CharZero F]
    (hD : finrank F D = 7) (U V : Submodule F D)
    (hU : finrank F U = 3) (hV : finrank F V = 3)
    (hlow : LowIntersection U) : 6 ≤ finrank F (U * V : Submodule F D) := by
  classical
  by_contra hn
  have hn' : finrank F (U * V : Submodule F D) ≤ 5 := by omega
  let T := Algebra.traceForm F D
  have hT := traceForm_nondegenerate F D
  have hortho : finrank F (T.orthogonal (U * V)) ≥ 2 := by
    rw [LinearMap.BilinForm.finrank_orthogonal hT, hD]
    omega
  obtain ⟨b, hb⟩ := exists_linearIndependent_of_le_finrank hortho
  let p : D := b 1
  let q : D := b 0
  have hpair : LinearIndependent F ![q, p] := by
    convert hb.map' (T.orthogonal (U * V)).subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective) using 1
    ext i
    fin_cases i <;> rfl
  have hp : p ≠ 0 := (linearIndependent_fin2.mp hpair).1
  have hq : q ≠ 0 := hpair.ne_zero 0
  have hcontained (a : T.orthogonal (U * V)) : translate (a : D) U ≤ T.orthogonal V := by
    rintro x ⟨u, hu, rfl⟩ v hv
    have ht := a.property (u * v) (Submodule.mul_mem_mul hu hv)
    simpa only [T, Algebra.traceForm_apply, LinearMap.mulLeft_apply, mul_assoc, mul_left_comm, mul_comm] using ht
  have hsup : translate p U ⊔ translate q U ≤ T.orthogonal V :=
    sup_le (hcontained (b 1)) (hcontained (b 0))
  have hbound := Submodule.finrank_mono hsup
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (translate p U) (translate q U)
  have hlow' := hlow (q / p) (div_ne_zero hq hp) (ratio_not_base hp hpair)
  rw [translate_finrank p hp, translate_finrank q hq,
    translated_intersection U p q hp] at hsum
  rw [LinearMap.BilinForm.finrank_orthogonal hT, hD, hV] at hbound
  omega


private def relationMap (U : Submodule F D) (v : Fin 3 → D) :
    (Fin 3 → U) →ₗ[F] D where
  toFun x := ∑ i, v i * (x i : D)
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a x := by simp [Algebra.smul_def, Finset.mul_sum, mul_left_comm]

private lemma relationMap_range (U V : Submodule F D) (b : Basis (Fin 3) F V) :
    (relationMap U (fun i ↦ (b i : D))).range = U * V := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    change (∑ i, (b i : D) * (x i : D)) ∈ U * V
    exact Submodule.sum_mem _ fun i _ ↦ by
      simpa [mul_comm] using Submodule.mul_mem_mul (x i).property (b i).property
  · apply Submodule.mul_le.mpr
    intro u hu v hv
    let v' : V := ⟨v, hv⟩
    refine ⟨fun i ↦ (b.repr v' i) • (⟨u, hu⟩ : U), ?_⟩
    simp only [relationMap, LinearMap.coe_mk, AddHom.coe_mk,
      Submodule.coe_smul, Algebra.smul_def]
    change (∑ i, (b i : D) * (algebraMap F D (b.repr v' i) * u)) = u * v
    have hb := congrArg (fun z : V ↦ (z : D)) (b.sum_repr v')
    simp only [Submodule.coe_sum, Submodule.coe_smul, Algebra.smul_def] at hb
    calc
      _ = u * ∑ i, algebraMap F D (b.repr v' i) * (b i : D) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = u * v := by rw [hb]

private lemma relation_finrank [FiniteDimensional F D] [CharZero F]
    (hD : finrank F D = 7) (U V : Submodule F D)
    (hU : finrank F U = 3) (hV : finrank F V = 3)
    (hlow : LowIntersection U) (b : Basis (Fin 3) F V) :
    finrank F (relationMap U (fun i ↦ (b i : D))).ker ≤ 3 := by
  have h := (relationMap U (fun i ↦ (b i : D))).finrank_range_add_finrank_ker
  have hp := product_finrank_lower hD U V hU hV hlow
  rw [relationMap_range] at h
  simp only [Module.finrank_pi_fintype, Fintype.card_fin, hU, Finset.sum_const,
    Finset.card_univ, smul_eq_mul] at h
  omega

private lemma plane_relation [FiniteDimensional F D]
    (U V : Submodule F D) (hU : finrank F U = 3)
    (hQ : quotientSet U ⊆ quotientSet V) (b : Basis (Fin 3) F V)
    (ell : U →ₗ[F] F) :
    ∃ x : Fin 3 → U, x ≠ 0 ∧
      relationMap U (fun i ↦ (b i : D)) x = 0 ∧ ∀ i, ell (x i) = 0 := by
  classical
  have hd := ell.finrank_range_add_finrank_ker
  have hr : finrank F ell.range ≤ 1 := by
    simpa using ell.range.finrank_le
  have hk : 2 ≤ finrank F ell.ker := by omega
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (R := F) (M := ell.ker) hk
  have hvPair : LinearIndependent F ![v 0, v 1] := by
    convert hv using 1
    ext i
    fin_cases i <;> rfl
  have hn (i : Fin 2) : ((v i : U) : D) ≠ 0 := by
    intro h
    exact hv.ne_zero i (Subtype.ext (Subtype.ext h))
  have hquot : ((v 0 : U) : D) / ((v 1 : U) : D) ∈ quotientSet U :=
    ⟨(v 0 : U), (v 0 : U).property, (v 1 : U), (v 1 : U).property,
      hn 0, hn 1, rfl⟩
  obtain ⟨c, hc, d, hdV, hc0, hd0, hcd⟩ := hQ hquot
  let c' : V := ⟨c, hc⟩
  let d' : V := ⟨d, hdV⟩
  let x : Fin 3 → U := fun i ↦ b.repr d' i • (v 0 : U) - b.repr c' i • (v 1 : U)
  refine ⟨x, ?_, ?_, ?_⟩
  · intro hx
    have hcoeff (i : Fin 3) : b.repr d' i = 0 := by
      have hi : b.repr d' i • (v 0 : U) = b.repr c' i • (v 1 : U) := by
        exact sub_eq_zero.mp (congrFun hx i)
      have hiKer : b.repr d' i • v 0 = b.repr c' i • v 1 := Subtype.ext hi
      exact (hvPair.eq_zero_of_pair' hiKer).1
    have hz : d' = 0 := b.repr.injective (by ext i; simp [hcoeff i])
    exact hd0 (congrArg Subtype.val hz)
  · have hbC := congrArg (fun z : V ↦ (z : D)) (b.sum_repr c')
    have hbD := congrArg (fun z : V ↦ (z : D)) (b.sum_repr d')
    simp only [Submodule.coe_sum, Submodule.coe_smul, Algebra.smul_def] at hbC hbD
    simp only [relationMap, x, LinearMap.coe_mk, AddHom.coe_mk,
      Submodule.coe_sub, Submodule.coe_smul, Algebra.smul_def]
    change (∑ i, (b i : D) *
      (algebraMap F D (b.repr d' i) * (v 0 : U) -
       algebraMap F D (b.repr c' i) * (v 1 : U))) = 0
    have heq : ((v 0 : U) : D) * d - c * ((v 1 : U) : D) = 0 := by
      have h := (div_eq_div_iff (hn 1) hd0).mp hcd.symm
      exact sub_eq_zero.mpr h
    calc
      _ = (∑ i, algebraMap F D (b.repr d' i) * (b i : D)) * (v 0 : U) -
          (∑ i, algebraMap F D (b.repr c' i) * (b i : D)) * (v 1 : U) := by
        simp only [Finset.sum_mul, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [hbC, hbD]; simpa [c', d', mul_comm] using heq
  · intro i
    simp only [x, map_sub, map_smul]
    have h0 : ell (v 0 : U) = 0 := (v 0).property
    have h1 : ell (v 1 : U) = 0 := (v 1).property
    simp [h0, h1]


private lemma zero_third_relation [FiniteDimensional F D]
    (U : Submodule F D) (hlow : LowIntersection U)
    (s t : U) (w : D) (hst : LinearIndependent F ![t, s])
    (x : Fin 3 → U)
    (hx : relationMap U ![(s : D), (t : D), w] x = 0) (hz : x 2 = 0) :
    ∃ a : F, x = a • ![t, -s, 0] := by
  have hs : (s : D) ≠ 0 := by
    exact fun h ↦ (linearIndependent_fin2.mp hst).1 (Subtype.ext h)
  have ht : (t : D) ≠ 0 := by exact fun h ↦ hst.ne_zero 0 (Subtype.ext h)
  have hstd : LinearIndependent F ![(t : D), (s : D)] := by
    convert hst.map' U.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective) using 1
    ext i
    fin_cases i <;> rfl
  have hlow' := hlow ((t : D) / s) (div_ne_zero ht hs) (ratio_not_base hs hstd)
  let I := U ⊓ translate ((t : D) / s) U
  have htI : (t : D) ∈ I := ⟨t.property, s, s.property, div_mul_cancel₀ _ hs⟩
  have hspan : Submodule.span F {(t : D)} ≤ I := by
    exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr htI)
  have hI : I = Submodule.span F {(t : D)} := by
    exact (Submodule.eq_of_le_of_finrank_le hspan (by
      rw [finrank_span_singleton ht]
      exact hlow')).symm
  have hrel : (s : D) * (x 0 : D) + (t : D) * (x 1 : D) = 0 := by
    simpa [relationMap, Fin.sum_univ_three, hz] using hx
  have hxI : (x 0 : D) ∈ I := by
    refine ⟨(x 0).property, -(x 1 : D), U.neg_mem (x 1).property, ?_⟩
    apply (mul_left_cancel₀ hs)
    calc
      (s : D) * ((t : D) / s * -(x 1 : D)) = -(t : D) * (x 1 : D) := by
        field_simp
      _ = (s : D) * (x 0 : D) := by
        exact by simpa [neg_mul] using (eq_neg_of_add_eq_zero_left hrel).symm
  rw [hI, Submodule.mem_span_singleton] at hxI
  obtain ⟨a, ha⟩ := hxI
  have hx0 : x 0 = a • t := by exact Subtype.ext ha.symm
  have hx1 : x 1 = a • (-s) := by
    apply Subtype.ext
    apply mul_left_cancel₀ ht
    have hr := hrel
    rw [show (x 0 : D) = algebraMap F D a * (t : D) from by simpa [Algebra.smul_def] using ha.symm] at hr
    simp only [Submodule.coe_smul, Submodule.coe_neg, Algebra.smul_def]
    change (t : D) * (x 1 : D) = (t : D) * (algebraMap F D a * -(s : D))
    calc
      _ = -((s : D) * (algebraMap F D a * (t : D))) := eq_neg_of_add_eq_zero_right hr
      _ = _ := by ring
  refine ⟨a, ?_⟩
  ext i
  fin_cases i <;> simp [hx0, hx1, hz]

private def thirdProjection (U : Submodule F D) (s t : U) (w : D) :
    (relationMap U ![(s : D), (t : D), w]).ker →ₗ[F] U :=
  (LinearMap.proj 2).comp (relationMap U ![(s : D), (t : D), w]).ker.subtype

private lemma thirdProjection_kernel [FiniteDimensional F D]
    (U : Submodule F D) (hlow : LowIntersection U)
    (s t : U) (w : D) (hst : LinearIndependent F ![t, s]) :
    finrank F (thirdProjection U s t w).ker = 1 := by
  classical
  let A : (relationMap U ![(s : D), (t : D), w]).ker :=
    ⟨![t, -s, 0], by simp [relationMap, Fin.sum_univ_three]; ring⟩
  have hA : A ≠ 0 := by
    intro h
    have ht : t = 0 := congrFun (congrArg Subtype.val h) 0
    exact hst.ne_zero 0 ht
  let R : Submodule F (Fin 3 → U) := (relationMap U ![(s : D), (t : D), w]).ker
  have heq : (thirdProjection U s t w).ker = Submodule.span F {A} := by
    apply le_antisymm
    · intro x hx
      have hx2 : x.val 2 = 0 := hx
      obtain ⟨a, ha⟩ := zero_third_relation U hlow s t w hst x.val x.property hx2
      apply (Submodule.mem_span_singleton (R := F) (M := R)).mpr
      refine ⟨a, ?_⟩
      apply Subtype.ext
      exact ha.symm
    · apply Submodule.span_le.mpr
      intro x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      change A.val 2 = 0
      rfl
  rw [heq]
  exact finrank_span_singleton (K := F)
    (V := (relationMap U ![(s : D), (t : D), w]).ker) hA


private lemma dual_nonzero_pair {E : Type*} [AddCommGroup E] [Module F E]
    (s z : E) (hs : s ≠ 0) (hz : z ≠ 0) :
    ∃ ell : E →ₗ[F] F, ell s ≠ 0 ∧ ell z ≠ 0 := by
  classical
  by_cases h : LinearIndependent F ![s, z]
  · obtain ⟨ell, hell⟩ := Module.exists_dual_forall_apply_eq_one h.linearIndepOn_univ
    refine ⟨ell, ?_, ?_⟩
    · simpa using (hell 0 (Set.mem_univ _)).trans_ne one_ne_zero
    · simpa using (hell 1 (Set.mem_univ _)).trans_ne one_ne_zero
  · have hdep : ∃ c : F, c • z = s := by
      by_contra hn
      push Not at hn
      exact h (linearIndependent_fin2.mpr ⟨hz, by simpa using hn⟩)
    obtain ⟨c, hc⟩ := hdep
    obtain ⟨ell, hell⟩ := Module.Projective.exists_dual_eq_one F hz
    refine ⟨ell, ?_, by rw [hell]; exact one_ne_zero⟩
    rw [← hc, map_smul, hell, smul_eq_mul, mul_one]
    intro hzero
    apply hs
    rw [← hc, hzero, zero_smul]

private lemma projection_finrank [FiniteDimensional F D]
    (U : Submodule F D) (hlow : LowIntersection U)
    (s t : U) (w : D) (hst : LinearIndependent F ![t, s])
    (hR : finrank F (relationMap U ![(s : D), (t : D), w]).ker ≤ 3)
    (hplane : ∀ ell : U →ₗ[F] F, ∃ x : Fin 3 → U, x ≠ 0 ∧
      relationMap U ![(s : D), (t : D), w] x = 0 ∧ ∀ i, ell (x i) = 0) :
    finrank F (thirdProjection U s t w).range = 2 := by
  classical
  let f : (relationMap U ![(s : D), (t : D), w]).ker →ₗ[F] U :=
    thirdProjection U s t w
  have hker : finrank F f.ker = 1 := thirdProjection_kernel U hlow s t w hst
  have hrank := LinearMap.finrank_range_add_finrank_ker (K := F)
    (V := (relationMap U ![(s : D), (t : D), w]).ker) (V₂ := U) f
  have hle : finrank F f.range ≤ 2 := by omega
  suffices ¬ finrank F f.range ≤ 1 by
    change finrank F f.range = 2
    omega
  intro hn
  haveI : Module.Free F f.range := Module.Free.of_divisionRing (K := F) (V := f.range)
  obtain ⟨z, hgen⟩ := (finrank_le_one_iff (K := F) (V := f.range)).mp hn
  have hs : s ≠ 0 := (linearIndependent_fin2.mp hst).1
  have hzgen : ∃ z₀ : U, z₀ ≠ 0 ∧ ∀ x ∈ f.range, ∃ a : F, a • z₀ = x := by
    by_cases hz : (z : U) = 0
    · refine ⟨s, hs, ?_⟩
      intro x hx
      obtain ⟨a, ha⟩ := hgen ⟨x, hx⟩
      have hx0 : x = 0 := by
        have := congrArg Subtype.val ha
        simpa [hz] using this.symm
      exact ⟨0, by simp [hx0]⟩
    · refine ⟨z, hz, ?_⟩
      intro x hx
      obtain ⟨a, ha⟩ := hgen ⟨x, hx⟩
      exact ⟨a, congrArg Subtype.val ha⟩
  obtain ⟨z₀, hz₀, hzgen⟩ := hzgen
  obtain ⟨ell, hells, hellz⟩ := dual_nonzero_pair (F := F) (E := U) s z₀ hs hz₀
  obtain ⟨x, hx0, hxR, hxell⟩ := hplane ell
  have hxrange : x 2 ∈ f.range := ⟨⟨x, hxR⟩, rfl⟩
  obtain ⟨c, hc⟩ := hzgen _ hxrange
  have hc0 : c = 0 := by
    have he := congrArg ell hc
    rw [map_smul, hxell 2, smul_eq_mul] at he
    exact (mul_eq_zero.mp he).resolve_right hellz
  have hx2 : x 2 = 0 := by simpa [hc0] using hc.symm
  obtain ⟨a, ha⟩ := zero_third_relation U hlow s t w hst x hxR hx2
  have ha0 : a = 0 := by
    have he := hxell 1
    rw [ha] at he
    simp only [Pi.smul_apply, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
      map_smul, map_neg, smul_eq_mul, mul_neg, neg_eq_zero] at he
    exact (mul_eq_zero.mp he).resolve_right hells
  apply hx0
  rw [ha, ha0, zero_smul]

private lemma flat_cancellation (U : Submodule F D) (b : Basis (Fin 3) F U)
    (s t x y : U) (w : D)
    (hrel : (s : D) * x + (t : D) * y + w * (b 0 : D) = 0)
    (h₀ : b.repr s 1 * b.repr x 1 + b.repr t 1 * b.repr y 1 = 0)
    (h₁ : b.repr s 1 * b.repr x 2 + b.repr s 2 * b.repr x 1 +
      b.repr t 1 * b.repr y 2 + b.repr t 2 * b.repr y 1 = 0)
    (h₂ : b.repr s 2 * b.repr x 2 + b.repr t 2 * b.repr y 2 = 0) : w ∈ U := by
  let c (v : U) (i : Fin 3) : D := algebraMap F D (b.repr v i)
  have hexp (v : U) : (v : D) =
      c v 0 * (b 0 : D) + c v 1 * (b 1 : D) + c v 2 * (b 2 : D) := by
    have hv := congrArg (fun v : U ↦ (v : D)) (b.sum_repr v)
    simpa only [Submodule.coe_sum, Submodule.coe_smul, Fin.sum_univ_three, Submodule.coe_add, Submodule.coe_smul,
      Algebra.smul_def, c] using hv.symm
  let E : U := b.repr s 0 • x + b.repr x 0 • (s - b.repr s 0 • b 0) +
    b.repr t 0 • y + b.repr y 0 • (t - b.repr t 0 • b 0)
  have hflat : ((s : D) - c s 0 * (b 0 : D)) * ((x : D) - c x 0 * (b 0 : D)) +
      ((t : D) - c t 0 * (b 0 : D)) * ((y : D) - c y 0 * (b 0 : D)) = 0 := by
    calc
      _ = algebraMap F D (b.repr s 1 * b.repr x 1 + b.repr t 1 * b.repr y 1) *
          (b 1 : D)^2 +
        algebraMap F D (b.repr s 1 * b.repr x 2 + b.repr s 2 * b.repr x 1 +
          b.repr t 1 * b.repr y 2 + b.repr t 2 * b.repr y 1) * (b 1 : D) * (b 2 : D) +
        algebraMap F D (b.repr s 2 * b.repr x 2 + b.repr t 2 * b.repr y 2) *
          (b 2 : D)^2 := by
        rw [hexp s, hexp t, hexp x, hexp y]
        simp only [map_add, map_mul, c]
        ring
      _ = 0 := by rw [h₀, h₁, h₂]; simp
  have hfactor : (s : D) * x + (t : D) * y = (b 0 : D) * (E : D) := by
    simp only [E, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sub, Algebra.smul_def]
    change (s : D) * x + (t : D) * y = (b 0 : D) *
      (c s 0 * (x : D) + c x 0 * ((s : D) - c s 0 * (b 0 : D)) +
       c t 0 * (y : D) + c y 0 * ((t : D) - c t 0 * (b 0 : D)))
    calc
      _ = (b 0 : D) *
        (c s 0 * (x : D) + c x 0 * ((s : D) - c s 0 * (b 0 : D)) +
         c t 0 * (y : D) + c y 0 * ((t : D) - c t 0 * (b 0 : D))) +
        (((s : D) - c s 0 * (b 0 : D)) * ((x : D) - c x 0 * (b 0 : D)) +
         ((t : D) - c t 0 * (b 0 : D)) * ((y : D) - c y 0 * (b 0 : D))) := by ring
      _ = _ := by rw [hflat, add_zero]
  have hb0 : (b 0 : D) ≠ 0 := by
    intro h
    exact b.ne_zero 0 (Subtype.ext h)
  have hw : w = -(E : D) := by
    apply mul_left_cancel₀ hb0
    calc
      (b 0 : D) * w = -((s : D) * x + (t : D) * y) := by
        simpa [mul_comm] using eq_neg_of_add_eq_zero_right hrel
      _ = (b 0 : D) * -(E : D) := by rw [hfactor]; ring
  rw [hw]
  exact U.neg_mem E.property

private lemma three_coefficients [CharZero F]
    (s₁ s₂ t₁ t₂ x₁ x₂ y₁ y₂ : F)
    (h : ∀ j : F, (s₁ + j * s₂) * (x₁ + j * x₂) +
      (t₁ + j * t₂) * (y₁ + j * y₂) = 0) :
    s₁ * x₁ + t₁ * y₁ = 0 ∧
    s₁ * x₂ + s₂ * x₁ + t₁ * y₂ + t₂ * y₁ = 0 ∧
    s₂ * x₂ + t₂ * y₂ = 0 := by
  have hzero := h 0
  have hplus := h 1
  have hminus := h (-1)
  simp only [zero_mul, add_zero] at hzero
  have hmid : (2 : F) * (s₁ * x₂ + s₂ * x₁ + t₁ * y₂ + t₂ * y₁) = 0 := by
    linear_combination hplus - hminus
  have hmid' := (mul_eq_zero.mp hmid).resolve_left two_ne_zero
  refine ⟨hzero, hmid', ?_⟩
  linear_combination hplus - hzero - hmid'

private lemma relation_rigidity [FiniteDimensional F D] [CharZero F]
    (U : Submodule F D) (hU : finrank F U = 3) (hlow : LowIntersection U)
    (s t : U) (w : D) (hst : LinearIndependent F ![t, s])
    (hR : finrank F (relationMap U ![(s : D), (t : D), w]).ker ≤ 3)
    (hplane : ∀ ell : U →ₗ[F] F, ∃ x : Fin 3 → U, x ≠ 0 ∧
      relationMap U ![(s : D), (t : D), w] x = 0 ∧ ∀ i, ell (x i) = 0) : w ∈ U := by
  classical
  let f : (relationMap U ![(s : D), (t : D), w]).ker →ₗ[F] U :=
    thirdProjection U s t w
  let P : Submodule F U := f.range
  have hP : finrank F P = 2 := projection_finrank U hlow s t w hst hR hplane
  haveI : Module.Free F P := Module.Free.of_divisionRing (K := F) (V := P)
  let bP : Basis (Fin 2) F P := Module.finBasisOfFinrankEq F P hP
  let z : U := bP 0
  let z' : U := bP 1
  have hzpair : LinearIndependent F ![z, z'] := by
    have h := LinearIndependent.map' (R := F) (M := P) (M' := U)
      bP.linearIndependent P.subtype (Submodule.ker_subtype _)
    convert h using 1
    ext i
    fin_cases i <;> rfl
  obtain ⟨e, he⟩ := exists_linearIndependent_snoc_of_lt_finrank hzpair (by rw [hU]; decide)
  let b : Basis (Fin 3) F U := basisOfLinearIndependentOfCardEqFinrank he (by simp [hU])
  have hb (i : Fin 3) : b i = (Fin.snoc ![z, z'] e : Fin 3 → U) i := by
    exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank he (by simp [hU])) i
  have hb0 : b 0 = z := by simp [hb]
  have hb1 : b 1 = z' := by simp [hb]
  obtain ⟨B, hB⟩ := (bP 0).property
  have hB2 : B.val 2 = z := hB
  have hdet (j : F) :
      (b.repr s 1 + j * b.repr s 2) * (b.repr (B.val 0) 1 + j * b.repr (B.val 0) 2) +
      (b.repr t 1 + j * b.repr t 2) * (b.repr (B.val 1) 1 + j * b.repr (B.val 1) 2) = 0 := by
    let ell : U →ₗ[F] F := b.coord 1 + j • b.coord 2
    have hz : ell z = 0 := by rw [← hb0]; simp [ell]
    have hz' : ell z' = 1 := by rw [← hb1]; simp [ell]
    obtain ⟨X, hX0, hXR, hXell⟩ := hplane ell
    let q : P := ⟨X 2, ⟨⟨X, hXR⟩, rfl⟩⟩
    have hq : (q : U) = bP.repr q 0 • z + bP.repr q 1 • z' := by
      have hq := congrArg (fun q : P ↦ (q : U)) (bP.sum_repr q)
      simpa only [Submodule.coe_sum, Submodule.coe_smul, Fin.sum_univ_two,
        Submodule.coe_add, Submodule.coe_smul, z, z'] using hq.symm
    have hc1 : bP.repr q 1 = 0 := by
      have h := congrArg ell hq
      simp only [map_add, map_smul, hz, hz', smul_eq_mul,
        mul_one, mul_zero, zero_add] at h
      exact h.symm.trans (hXell 2)
    let c := bP.repr q 0
    have hX2 : X 2 = c • z := by simpa [hc1, c, q] using hq
    let Y : Fin 3 → U := X - c • B.val
    have hBR : relationMap U ![(s : D), (t : D), w] B.val = 0 := B.property
    have hYR : relationMap U ![(s : D), (t : D), w] Y = 0 := by
      simp only [Y, map_sub, map_smul, hXR, hBR, smul_zero, sub_zero]
    have hY2 : Y 2 = 0 := by simp [Y, hX2, hB2]
    obtain ⟨a, ha⟩ := zero_third_relation U hlow s t w hst Y hYR hY2
    have hX : X = a • ![t, -s, 0] + c • B.val := by
      rw [← ha]
      exact (sub_add_cancel X (c • B.val)).symm
    have hac : a ≠ 0 ∨ c ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hX0 (by simpa [hn.1, hn.2] using hX)
    have he0 : a * ell t + c * ell (B.val 0) = 0 := by
      have h := hXell 0
      rw [hX] at h
      simpa only [Pi.add_apply, Pi.smul_apply, Fin.isValue, Matrix.cons_val_zero,
        map_add, map_smul, smul_eq_mul] using h
    have he1 : -(a * ell s) + c * ell (B.val 1) = 0 := by
      have h := hXell 1
      rw [hX] at h
      simpa only [Pi.add_apply, Pi.smul_apply, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_zero, map_add, map_smul, map_neg, smul_eq_mul, mul_neg] using h
    have hd : ell s * ell (B.val 0) + ell t * ell (B.val 1) = 0 := by
      by_cases hc : c = 0
      · have ha0 : a ≠ 0 := hac.resolve_right (not_ne_iff.mpr hc)
        have ht0 : ell t = 0 := by
          have h : a * ell t = 0 := by simpa [hc] using he0
          exact (mul_eq_zero.mp h).resolve_left ha0
        have hs0 : ell s = 0 := by
          have h : a * ell s = 0 := by simpa [hc] using he1
          exact (mul_eq_zero.mp h).resolve_left ha0
        simp [hs0, ht0]
      · have h : c * (ell s * ell (B.val 0) + ell t * ell (B.val 1)) = 0 := by
          linear_combination ell s * he0 + ell t * he1
        exact (mul_eq_zero.mp h).resolve_left hc
    simpa [ell, Basis.coord_apply] using hd
  obtain ⟨h₀, h₁, h₂⟩ := three_coefficients
    (b.repr s 1) (b.repr s 2) (b.repr t 1) (b.repr t 2)
    (b.repr (B.val 0) 1) (b.repr (B.val 0) 2)
    (b.repr (B.val 1) 1) (b.repr (B.val 1) 2) hdet
  apply flat_cancellation U b s t (B.val 0) (B.val 1) w ?_ h₀ h₁ h₂
  have h := B.property
  simpa [relationMap, Fin.sum_univ_three, hB2, ← hb0] using h

/-- The third vector of a basis sharing a plane with the first subspace belongs
there too, under the original quotient and low-intersection assumptions. -/
theorem shared_plane_third_vector [CharZero F]
    (hD : finrank F D = 7) (U V : Submodule F D)
    (hU : finrank F U = 3) (hlow : LowIntersection U)
    (hQ : quotientSet U ⊆ quotientSet V) (bV : Basis (Fin 3) F V)
    (hs : (bV 0 : D) ∈ U) (ht : (bV 1 : D) ∈ U) : (bV 2 : D) ∈ U := by
  haveI : FiniteDimensional F D := Module.finite_of_finrank_pos (by omega)
  let s : U := ⟨bV 0, hs⟩
  let t : U := ⟨bV 1, ht⟩
  let w : D := bV 2
  have hV : finrank F V = 3 := by simpa using Module.finrank_eq_card_basis bV
  have hpairV : LinearIndependent F ![bV 1, bV 0] := by
    convert bV.linearIndependent.comp ![(1 : Fin 3), 0] (by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all) using 1
    ext i
    fin_cases i <;> rfl
  have hpairD : LinearIndependent F ![(bV 1 : D), (bV 0 : D)] := by
    convert hpairV.map' V.subtype (Submodule.ker_subtype _) using 1
    ext i
    fin_cases i <;> rfl
  have hpair : LinearIndependent F ![t, s] := by
    apply LinearIndependent.of_comp U.subtype
    convert hpairD using 1
    ext i
    fin_cases i <;> rfl
  have hvals : (fun i ↦ (bV i : D)) = ![(s : D), (t : D), w] := by
    ext i
    fin_cases i <;> rfl
  have hR : finrank F (relationMap U ![(s : D), (t : D), w]).ker ≤ 3 := by
    rw [← hvals]
    exact relation_finrank hD U V hU hV hlow bV
  apply relation_rigidity U hU hlow s t w hpair hR
  intro ell
  rw [← hvals]
  exact plane_relation U V hU hQ bV ell

private lemma quotientSet_translate (a : D) (ha : a ≠ 0) (U : Submodule F D) :
    quotientSet (translate a U) = quotientSet U := by
  ext r
  constructor
  · rintro ⟨u, ⟨x, hx, rfl⟩, v, ⟨y, hy, rfl⟩, hu, hv, heq⟩
    have hx0 : x ≠ 0 := by intro h; simp [h] at hu
    have hy0 : y ≠ 0 := by intro h; simp [h] at hv
    refine ⟨x, hx, y, hy, hx0, hy0, ?_⟩
    simpa only [LinearMap.mulLeft_apply, mul_div_mul_left _ _ ha] using heq
  · rintro ⟨u, hu, v, hv, hu0, hv0, heq⟩
    refine ⟨a * u, ⟨u, hu, rfl⟩, a * v, ⟨v, hv, rfl⟩,
      mul_ne_zero ha hu0, mul_ne_zero ha hv0, ?_⟩
    simpa only [mul_div_mul_left _ _ ha] using heq

/-- Original degree-seven quotient rigidity: the multiplier is in the extension
field and no intersection condition is imposed on the second subspace. -/
theorem original_lemma40_3 [CharZero F]
    (hD : finrank F D = 7) (U V : Submodule F D)
    (hU : finrank F U = 3) (hV : finrank F V = 3)
    (hlow : LowIntersection U) (hQ : quotientSet U ⊆ quotientSet V) :
    ∃ γ : D, γ ≠ 0 ∧ V = translate γ U := by
  classical
  haveI : FiniteDimensional F D := Module.finite_of_finrank_pos (by omega)
  let bU : Basis (Fin 3) F U := Module.finBasisOfFinrankEq F U hU
  let s : U := bU 0
  let t : U := bU 1
  have hs : (s : D) ≠ 0 := by intro h; exact bU.ne_zero 0 (Subtype.ext h)
  have ht : (t : D) ≠ 0 := by intro h; exact bU.ne_zero 1 (Subtype.ext h)
  have hquot : (s : D) / t ∈ quotientSet U := ⟨s, s.property, t, t.property, hs, ht, rfl⟩
  obtain ⟨c, hc, d, hd, hc0, hd0, hcd⟩ := hQ hquot
  let γ := d / (t : D)
  have hγ : γ ≠ 0 := div_ne_zero hd0 ht
  have hγt : γ * (t : D) = d := div_mul_cancel₀ d ht
  have hγs : γ * (s : D) = c := by
    have h := (div_eq_div_iff hd0 ht).mp hcd
    apply mul_right_cancel₀ ht
    calc
      γ * (s : D) * (t : D) = γ * (t : D) * (s : D) := by ring
      _ = c * (t : D) := by rw [hγt]; simpa [mul_comm] using h.symm
  let W := translate γ⁻¹ V
  have hW : finrank F W = 3 := by rw [translate_finrank _ (inv_ne_zero hγ), hV]
  have hsW : (s : D) ∈ W := by
    refine ⟨c, hc, ?_⟩
    change γ⁻¹ * c = s
    rw [← hγs, ← mul_assoc, inv_mul_cancel₀ hγ, one_mul]
  have htW : (t : D) ∈ W := by
    refine ⟨d, hd, ?_⟩
    change γ⁻¹ * d = t
    rw [← hγt, ← mul_assoc, inv_mul_cancel₀ hγ, one_mul]
  let sW : W := ⟨s, hsW⟩
  let tW : W := ⟨t, htW⟩
  have hstU : LinearIndependent F ![s, t] := by
    convert bU.linearIndependent.comp ![(0 : Fin 3), 1] (by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all) using 1
    ext i
    fin_cases i <;> rfl
  have hstD : LinearIndependent F ![(s : D), (t : D)] := by
    convert hstU.map' U.subtype (Submodule.ker_subtype _) using 1
    ext i
    fin_cases i <;> rfl
  have hstW : LinearIndependent F ![sW, tW] := by
    apply LinearIndependent.of_comp W.subtype
    convert hstD using 1
    ext i
    fin_cases i <;> rfl
  obtain ⟨wW, hw⟩ := exists_linearIndependent_snoc_of_lt_finrank hstW (by rw [hW]; decide)
  let bW : Basis (Fin 3) F W := basisOfLinearIndependentOfCardEqFinrank hw (by simp [hW])
  have hbW (i : Fin 3) : bW i = (Fin.snoc ![sW, tW] wW : Fin 3 → W) i := by
    exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hw (by simp [hW])) i
  have hQW : quotientSet U ⊆ quotientSet W := by
    rw [quotientSet_translate _ (inv_ne_zero hγ)]
    exact hQ
  have hthird : (bW 2 : D) ∈ U := shared_plane_third_vector hD U W hU hlow hQW bW
    (by simp [hbW, sW]) (by simp [hbW, tW])
  have hWU : W ≤ U := by
    intro v hv
    have hrepr := congrArg (fun v : W ↦ (v : D)) (bW.sum_repr ⟨v, hv⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hrepr
    change (∑ i, bW.repr ⟨v, hv⟩ i • (bW i : D)) = v at hrepr
    rw [← hrepr]
    apply U.sum_mem
    intro i _
    apply U.smul_mem
    fin_cases i
    · simp [hbW, sW]
    · simp [hbW, tW]
    · exact hthird
  have hWeq : W = U := Submodule.eq_of_le_of_finrank_le hWU (by rw [hW, hU])
  refine ⟨γ, hγ, ?_⟩
  have hundo : translate γ W = V := by
    change translate γ (translate γ⁻¹ V) = V
    rw [translate_translate, mul_inv_cancel₀ hγ, translate_one]
  rw [hWeq] at hundo
  exact hundo.symm

end D5.S3.Factorization.Galois.AuricSevenRigidity
