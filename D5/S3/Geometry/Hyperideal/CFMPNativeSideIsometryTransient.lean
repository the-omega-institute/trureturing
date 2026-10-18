import D5.S3.Geometry.Hyperideal.CFMPNativeCapMetricTransient
import D5.S3.Geometry.Hyperideal.CFMPNativeInverseTransient
import D5.S3.Geometry.HyperbolicPlaneRealization
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Topology.MetricSpace.Isometry
import Batteries.Tactic.OpenPrivate

/-!
Temporary exact application evidence. SOURCE ONLY; NOT COMPILED.
The inverse supplier is itself uncompiled. No kernel, axiom-audit, admission,
classification, novelty, or retention result is asserted by this source.
All declarations in this file have zero canonical retention.
-/

noncomputable section
open scoped BigOperators Matrix
open Set
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments

namespace NativeCornerExtractionSource

open private B_apply B_symm lift_ne_zero
  from D5.S3.Geometry.Hyperideal.CFMPNativeCapMetricTransient
open private temporary_dual_support_conclusion
  from D5.S3.Geometry.Hyperideal.CFMPNativeInverseTransient

namespace NativeSideIsometryTransient

set_option autoImplicit false

private theorem pair_sum_right (u : V) (a : Fin 4 → ℝ) (v : Fin 4 → V) :
    B u (∑ i, a i • v i) = ∑ i, a i * B u (v i) := by
  simp only [map_sum, map_smul, smul_eq_mul]

private theorem pair_sum_left (a : Fin 4 → ℝ) (v : Fin 4 → V) (u : V) :
    B (∑ i, a i • v i) u = ∑ i, a i * B (v i) u := by
  rw [B_symm, pair_sum_right]
  apply Finset.sum_congr rfl
  intro i _
  rw [B_symm u (v i)]

private def rows (d : NativeSupportCorners) (a : V) : V :=
  a ᵥ* (d.cap : Matrix (Fin 4) (Fin 4) ℝ)

private theorem rows_sum (d : NativeSupportCorners) (a : V) :
    rows d a = ∑ i, a i • d.cap i := by
  funext k
  simp [rows, Matrix.vecMul, dotProduct, Finset.sum_apply]

private def capBasis (d : NativeSupportCorners) : Module.Basis (Fin 4) ℝ V :=
  basisOfLinearIndependentOfCardEqFinrank (actual_corner_cap_independent d)
    (by simp [V, Module.finrank_fin_fun])

private theorem capBasis_apply (d : NativeSupportCorners) (i : Fin 4) :
    capBasis d i = d.cap i := by
  simp [capBasis]

private theorem rows_surjective (d : NativeSupportCorners) (X : V) :
    ∃ a : V, rows d a = X := by
  refine ⟨fun i => (capBasis d).repr X i, ?_⟩
  rw [rows_sum]
  simpa only [capBasis_apply] using (capBasis d).sum_repr X

/- The mixed basis has the original side normal at f, and original cap normals
at the other three indices. Pairing with side_f removes its coefficient;
the supplied independence of the four caps removes the remaining coefficients. -/
private def mixed (d : NativeSupportCorners) (f : Fin 4) (i : Fin 4) : V :=
  if i = f then d.side f else d.cap i

private theorem mixed_independent (d : NativeSupportCorners) (f : Fin 4) :
    LinearIndependent ℝ (mixed d f) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha
  have hpair (i : Fin 4) :
      B (d.side f) (mixed d f i) = if i = f then 1 else 0 := by
    by_cases hi : i = f
    · subst i
      simp only [mixed, if_pos rfl, ite_true, d.side_unit]
    · simp only [mixed, if_neg hi]
      rw [B_symm]
      exact d.orthogonal_incidence i f hi
  have haf : a f = 0 := by
    have he := congrArg (fun X : V => B (d.side f) X) ha
    have hv : B (d.side f) (∑ i, a i • mixed d f i) = a f := by
      rw [pair_sum_right]
      simp [hpair]
    rw [hv, LinearMap.BilinForm.zero_right] at he
    exact he
  have hc : (∑ i, a i • d.cap i) = 0 := by
    calc
      (∑ i, a i • d.cap i) = ∑ i, a i • mixed d f i := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i = f
        · subst i
          simp only [haf, zero_smul]
        · rw [mixed, if_neg hi]
      _ = 0 := ha
  exact Fintype.linearIndependent_iff.mp (actual_corner_cap_independent d) a hc

private def mixedBasis (d : NativeSupportCorners) (f : Fin 4) :
    Module.Basis (Fin 4) ℝ V :=
  basisOfLinearIndependentOfCardEqFinrank (mixed_independent d f)
    (by simp [V, Module.finrank_fin_fun])

private theorem mixedBasis_apply (d : NativeSupportCorners) (f i : Fin 4) :
    mixedBasis d f i = mixed d f i := by
  simp [mixedBasis]

private theorem mixed_gram (d e : NativeSupportCorners) (f : Fin 4)
    (hlen : ∀ i j, i ≠ f → j ≠ f → i ≠ j →
      dist (d.corner i j) (d.corner j i) = dist (e.corner i j) (e.corner j i))
    (i j : Fin 4) :
    B (mixed e f i) (mixed e f j) = B (mixed d f i) (mixed d f j) := by
  by_cases hi : i = f
  · subst i
    by_cases hj : j = f
    · subst j
      simp only [mixed, if_pos rfl, ite_true, d.side_unit, e.side_unit]
    · simp only [mixed, if_pos rfl, ite_true, if_neg hj]
      rw [B_symm (e.side f) (e.cap j), B_symm (d.side f) (d.cap j),
        e.orthogonal_incidence j f hj, d.orthogonal_incidence j f hj]
  · by_cases hj : j = f
    · subst j
      simp only [mixed, if_neg hi, if_pos rfl, ite_true,
        e.orthogonal_incidence i f hi, d.orthogonal_incidence i f hi]
    · simp only [mixed, if_neg hi, if_neg hj]
      by_cases hij : i = j
      · subst j
        rw [d.cap_unit, e.cap_unit]
      · rw [actual_corner_cap_pair e i j hij,
          actual_corner_cap_pair d i j hij, hlen i j hi hj hij]

private theorem mixed_linear_equivalence (d e : NativeSupportCorners) (f : Fin 4)
    (hlen : ∀ i j, i ≠ f → j ≠ f → i ≠ j →
      dist (d.corner i j) (d.corner j i) = dist (e.corner i j) (e.corner j i)) :
    ∃ L : V ≃ₗ[ℝ] V,
      (∀ X Y, B (L X) (L Y) = B X Y) ∧
      L (d.side f) = e.side f ∧
      (∀ i, i ≠ f → L (d.cap i) = e.cap i) := by
  classical
  let b := mixedBasis d f
  let c := mixedBasis e f
  let L : V ≃ₗ[ℝ] V := b.equiv c (Equiv.refl (Fin 4))
  have hmap (i : Fin 4) : L (b i) = c i := by
    simp only [L, Module.Basis.equiv_apply, Equiv.refl_apply]
  have hg (i j : Fin 4) : B (c i) (c j) = B (b i) (b j) := by
    simpa only [b, c, mixedBasis_apply] using mixed_gram d e f hlen i j
  have hsum (X : V) : L X = ∑ i, b.repr X i • c i := by
    calc
      L X = L (∑ i, b.repr X i • b i) := congrArg L (b.sum_repr X).symm
      _ = ∑ i, b.repr X i • c i := by simp only [map_sum, map_smul, hmap]
  refine ⟨L, ?_, ?_, ?_⟩
  · intro X Y
    have hexpand : B X Y =
        ∑ i, b.repr X i * ∑ j, b.repr Y j * B (b i) (b j) := by
      calc
        B X Y = B (∑ i, b.repr X i • b i) (∑ j, b.repr Y j • b j) := by
          rw [b.sum_repr, b.sum_repr]
        _ = _ := by
          rw [pair_sum_left]
          simp_rw [pair_sum_right]
    rw [hsum, hsum, pair_sum_left]
    simp_rw [pair_sum_right, hg]
    exact hexpand.symm
  · have hm := hmap f
    simpa only [b, c, mixedBasis_apply, mixed, if_pos rfl, ite_true] using hm
  · intro i hi
    have hm := hmap i
    simpa only [b, c, mixedBasis_apply, mixed, if_neg hi] using hm

/- This is the inverse of the supplier's two oriented cap formulas. It recovers
ordered endpoints from the ORIGINAL caps, including the positive square root. -/
private theorem corner_lift_formula (d : NativeSupportCorners) (i j : Fin 4)
    (hij : i ≠ j) :
    let c := Real.cosh (dist (d.corner i j) (d.corner j i))
    let s := Real.sqrt (c ^ 2 - 1)
    0 < s ∧ s • lift (d.corner i j) = c • d.cap i + d.cap j := by
  intro c s
  let X := lift (d.corner i j)
  let Y := lift (d.corner j i)
  obtain ⟨hc, hs, hi, hj⟩ := actual_corner_oriented_caps d i j hij
  change 1 < c at hc
  change 0 < s at hs
  change d.cap i = (c / s) • X - (1 / s) • Y at hi
  change d.cap j = (c / s) • Y - (1 / s) • X at hj
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hz : 0 < c ^ 2 - 1 := by nlinarith only [hc]
  have hs2 : s ^ 2 = c ^ 2 - 1 := Real.sq_sqrt hz.le
  have hquot : (c ^ 2 - 1) / s = s := by
    apply (div_eq_iff hs0).mpr
    nlinarith only [hs2]
  refine ⟨hs, ?_⟩
  change s • X = c • d.cap i + d.cap j
  rw [hi, hj]
  funext k
  change s * X k = c * ((c / s) * X k - (1 / s) * Y k) +
    ((c / s) * Y k - (1 / s) * X k)
  calc
    s * X k = ((c ^ 2 - 1) / s) * X k := by rw [hquot]
    _ = _ := by ring

private theorem map_corner_lift (d e : NativeSupportCorners) (f : Fin 4)
    (L : V ≃ₗ[ℝ] V)
    (hcap : ∀ i, i ≠ f → L (d.cap i) = e.cap i)
    (hlen : ∀ i j, i ≠ f → j ≠ f → i ≠ j →
      dist (d.corner i j) (d.corner j i) = dist (e.corner i j) (e.corner j i))
    (i j : Fin 4) (hi : i ≠ f) (hj : j ≠ f) (hij : i ≠ j) :
    L (lift (d.corner i j)) = lift (e.corner i j) := by
  let c := Real.cosh (dist (d.corner i j) (d.corner j i))
  let s := Real.sqrt (c ^ 2 - 1)
  obtain ⟨hs, hd⟩ := corner_lift_formula d i j hij
  change 0 < s at hs
  change s • lift (d.corner i j) = c • d.cap i + d.cap j at hd
  have he : s • lift (e.corner i j) = c • e.cap i + e.cap j := by
    simpa only [c, s, hlen i j hi hj hij] using (corner_lift_formula e i j hij).2
  have hscaled : s • L (lift (d.corner i j)) = s • lift (e.corner i j) := by
    calc
      s • L (lift (d.corner i j)) = L (s • lift (d.corner i j)) := by
        rw [map_smul]
      _ = L (c • d.cap i + d.cap j) := congrArg L hd
      _ = c • e.cap i + e.cap j := by
        rw [map_add, map_smul, hcap i hi, hcap j hj]
      _ = s • lift (e.corner i j) := he.symm
  funext k
  have hk := congrFun hscaled k
  change s * L (lift (d.corner i j)) k = s * lift (e.corner i j) k at hk
  exact mul_left_cancel₀ (ne_of_gt hs) hk

private theorem pair_avoiding (f : Fin 4) :
    ∃ i j : Fin 4, i ≠ f ∧ j ≠ f ∧ i ≠ j := by
  fin_cases f <;> decide

/- A mapped future anchor decides the entire sheet. No time orientation is an
additional hypothesis of the native terminal statement. -/
private theorem future_from_anchor (L : V ≃ₗ[ℝ] V)
    (hB : ∀ X Y, B (L X) (L Y) = B X Y)
    (p₀ q₀ : HyperbolicThreeSpace) (hanchor : L (lift p₀) = lift q₀)
    (p : HyperbolicThreeSpace) :
    lorentz (L (lift p)) (L (lift p)) = -1 ∧ 0 < L (lift p) 3 := by
  have hu : lorentz (L (lift p)) (L (lift p)) = -1 := by
    rw [← B_apply, hB, B_apply, lift_unit]
  refine ⟨hu, ?_⟩
  apply D5.S3.Geometry.HyperbolicPlaneRealization.positive_time_of_pair
    (lift q₀) (L (lift p)) (lift_unit q₀) hu (lift_time q₀)
  rw [← hanchor, ← B_apply, hB, B_apply, lift_cosh]
  exact neg_lt_zero.mpr (Real.cosh_pos _)

private theorem ambient_isometry (L : V ≃ₗ[ℝ] V)
    (hB : ∀ X Y, B (L X) (L Y) = B X Y)
    (p₀ q₀ : HyperbolicThreeSpace) (hanchor : L (lift p₀) = lift q₀) :
    ∃ E : HyperbolicThreeSpace ≃ᵢ HyperbolicThreeSpace,
      ∀ p, lift (E p) = L (lift p) := by
  have hBi (X Y : V) : B (L.symm X) (L.symm Y) = B X Y := by
    simpa only [L.apply_symm_apply] using (hB (L.symm X) (L.symm Y)).symm
  have hanchori : L.symm (lift q₀) = lift p₀ := by
    rw [← hanchor, L.symm_apply_apply]
  let F : HyperbolicThreeSpace → HyperbolicThreeSpace := fun p =>
    project (L (lift p))
      (future_from_anchor L hB p₀ q₀ hanchor p).1
      (future_from_anchor L hB p₀ q₀ hanchor p).2
  let G : HyperbolicThreeSpace → HyperbolicThreeSpace := fun q =>
    project (L.symm (lift q))
      (future_from_anchor L.symm hBi q₀ p₀ hanchori q).1
      (future_from_anchor L.symm hBi q₀ p₀ hanchori q).2
  have hF (p : HyperbolicThreeSpace) : lift (F p) = L (lift p) :=
    lift_of_coordinates _ _ (future_from_anchor L hB p₀ q₀ hanchor p).1
      (future_from_anchor L hB p₀ q₀ hanchor p).2 rfl
  have hG (q : HyperbolicThreeSpace) : lift (G q) = L.symm (lift q) :=
    lift_of_coordinates _ _ (future_from_anchor L.symm hBi q₀ p₀ hanchori q).1
      (future_from_anchor L.symm hBi q₀ p₀ hanchori q).2 rfl
  have hGF (p : HyperbolicThreeSpace) : G (F p) = p := by
    apply lift_injective
    rw [hG, hF, L.symm_apply_apply]
  have hFG (q : HyperbolicThreeSpace) : F (G q) = q := by
    apply lift_injective
    rw [hF, hG, L.apply_symm_apply]
  have hdist : Isometry F := by
    apply Isometry.of_dist_eq
    intro p q
    apply Real.cosh_strictMonoOn.injOn dist_nonneg dist_nonneg
    have hpq := hB (lift p) (lift q)
    rw [← hF p, ← hF q, B_apply, B_apply, lift_cosh, lift_cosh] at hpq
    exact neg_injective hpq
  let E : HyperbolicThreeSpace ≃ᵢ HyperbolicThreeSpace :=
    { toEquiv :=
        { toFun := F
          invFun := G
          left_inv := hGF
          right_inv := hFG }
      isometry_toFun := hdist }
  exact ⟨E, hF⟩

private theorem cap_offdiagonal_lt (d : NativeSupportCorners) (i j : Fin 4)
    (hij : i ≠ j) : B (d.cap i) (d.cap j) < -1 := by
  rw [actual_corner_cap_pair d i j hij]
  have hc := Real.one_lt_cosh.mpr
    (ne_of_gt (actual_corner_length_positive d i j hij))
  linarith only [hc]

/- The omitted cap inequality is strictly negative, not an extra premise.
A nonzero nonnegative coefficient vector supported away from f has a positive
entry away from f; every corresponding off-diagonal Gram entry is < -1. -/
private theorem omitted_cap_strict (d : NativeSupportCorners) (f : Fin 4)
    (a : V) (haf : a f = 0) (ha : ∀ i, 0 ≤ a i) (hne : a ≠ 0) :
    B (d.cap f) (rows d a) < 0 := by
  classical
  have hpos : ∃ i, 0 < a i := by
    by_contra hn
    push_neg at hn
    apply hne
    funext i
    exact le_antisymm (hn i) (ha i)
  have hnonpos (i : Fin 4) : a i * B (d.cap f) (d.cap i) ≤ 0 := by
    by_cases hi : i = f
    · subst i
      simp only [haf, zero_mul, le_refl]
    · exact mul_nonpos_of_nonneg_of_nonpos (ha i)
        (le_of_lt (lt_trans (cap_offdiagonal_lt d f i (Ne.symm hi)) (by norm_num)))
  have hsum : (∑ i, a i * B (d.cap f) (d.cap i)) < ∑ _i : Fin 4, (0 : ℝ) := by
    apply Finset.sum_lt_sum
    · intro i _
      exact hnonpos i
    · obtain ⟨i, hi⟩ := hpos
      have hif : i ≠ f := by
        intro heq
        subst i
        rw [haf] at hi
        exact lt_irrefl 0 hi
      exact ⟨i, Finset.mem_univ i, mul_neg_of_pos_of_neg hi
        (lt_trans (cap_offdiagonal_lt d f i (Ne.symm hif)) (by norm_num))⟩
  rw [rows_sum, pair_sum_right]
  simpa only [Finset.sum_const_zero] using hsum

private theorem coefficients_ne_zero (d : NativeSupportCorners)
    (p : HyperbolicThreeSpace) (a : V) (hX : rows d a = lift p) : a ≠ 0 := by
  intro hz
  apply lift_ne_zero p
  rw [← hX, hz, rows_sum]
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]

/- Literal face membership in the original eight halfspaces, reduced to the
three face cap inequalities. The inverse supplier owns coefficient halfspaces. -/
private theorem side_face_coefficients (d : NativeSupportCorners) (f : Fin 4)
    (p : HyperbolicThreeSpace) :
    p ∈ sideFacet d.P d.side f ↔
      ∃ a : V, rows d a = lift p ∧ a f = 0 ∧
        (∀ i, 0 ≤ a i) ∧
        (∀ i, i ≠ f → B (d.cap i) (rows d a) ≤ 0) := by
  obtain ⟨_, hbeta, hsupport⟩ := temporary_dual_support_conclusion d
  constructor
  · rintro ⟨hp, hf⟩
    obtain ⟨a, hX⟩ := rows_surjective d (lift p)
    have hb : (∀ i, B (d.cap i) (rows d a) ≤ 0) ∧
        (∀ i, B (d.side i) (rows d a) ≤ 0) := by
      rw [hX]
      simpa only [d.body_halfspaces, Set.mem_setOf_eq] using hp
    have ha := ((hsupport a).2.2).mp hb
    have haf : a f = 0 := by
      have hh : B (d.cap f) (d.side f) * a f = 0 := by
        rw [← (hsupport a).2.1 f]
        change B (d.side f) (rows d a) = 0
        rw [hX]
        exact hf
      exact (mul_eq_zero.mp hh).resolve_left (ne_of_lt (hbeta f))
    exact ⟨a, hX, haf, ha.1, fun i _ => hb.1 i⟩
  · rintro ⟨a, hX, haf, ha, hcaps⟩
    have hc (i : Fin 4) : B (d.cap i) (rows d a) ≤ 0 := by
      by_cases hi : i = f
      · subst i
        exact (omitted_cap_strict d f a haf ha (coefficients_ne_zero d p a hX)).le
      · exact hcaps i hi
    have hb : (∀ i, B (d.cap i) (rows d a) ≤ 0) ∧
        (∀ i, B (d.side i) (rows d a) ≤ 0) := by
      apply ((hsupport a).2.2).mpr
      refine ⟨ha, ?_⟩
      intro i
      rw [← (hsupport a).1 i]
      exact hc i
    refine ⟨?_, ?_⟩
    · rw [d.body_halfspaces]
      change (∀ i, B (d.cap i) (lift p) ≤ 0) ∧
        (∀ i, B (d.side i) (lift p) ≤ 0)
      rw [← hX]
      exact hb
    · change B (d.side f) (lift p) = 0
      rw [← hX]
      change B (d.side f) (a ᵥ* (d.cap : Matrix (Fin 4) (Fin 4) ℝ)) = 0
      rw [(hsupport a).2.1 f, haf, mul_zero]

private theorem face_omitted_cap_strict (d : NativeSupportCorners) (f : Fin 4)
    (p : HyperbolicThreeSpace) (hp : p ∈ sideFacet d.P d.side f) :
    B (d.cap f) (lift p) < 0 := by
  obtain ⟨a, hX, haf, ha, _⟩ := (side_face_coefficients d f p).mp hp
  rw [← hX]
  exact omitted_cap_strict d f a haf ha (coefficients_ne_zero d p a hX)

private theorem map_rows (d e : NativeSupportCorners) (f : Fin 4)
    (L : V ≃ₗ[ℝ] V) (hcap : ∀ i, i ≠ f → L (d.cap i) = e.cap i)
    (a : V) (haf : a f = 0) : L (rows d a) = rows e a := by
  rw [rows_sum, rows_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i = f
  · subst i
    simp only [haf, zero_smul, map_zero]
  · rw [map_smul, hcap i hi]

private theorem face_forward (d e : NativeSupportCorners) (f : Fin 4)
    (L : V ≃ₗ[ℝ] V) (hB : ∀ X Y, B (L X) (L Y) = B X Y)
    (hcap : ∀ i, i ≠ f → L (d.cap i) = e.cap i)
    (p q : HyperbolicThreeSpace) (hq : lift q = L (lift p))
    (hp : p ∈ sideFacet d.P d.side f) : q ∈ sideFacet e.P e.side f := by
  obtain ⟨a, hX, haf, ha, hc⟩ := (side_face_coefficients d f p).mp hp
  have hY : rows e a = lift q := by
    rw [← map_rows d e f L hcap a haf, hX, hq]
  apply (side_face_coefficients e f q).mpr
  refine ⟨a, hY, haf, ha, ?_⟩
  intro i hi
  rw [← hcap i hi, ← map_rows d e f L hcap a haf, hB]
  exact hc i hi

private theorem same_labels (d e : NativeSupportCorners) (f : Fin 4)
    (hlen : ∀ i j, i ≠ f → j ≠ f → i ≠ j →
      dist (d.corner i j) (d.corner j i) = dist (e.corner i j) (e.corner j i)) :
    ∃ E : HyperbolicThreeSpace ≃ᵢ HyperbolicThreeSpace,
      (∀ p, p ∈ sideFacet d.P d.side f ↔ E p ∈ sideFacet e.P e.side f) ∧
      (∀ i j, i ≠ f → j ≠ f → i ≠ j → E (d.corner i j) = e.corner i j) ∧
      (∀ p, p ∈ sideFacet d.P d.side f → ∀ i,
        (p ∈ capFacet d.P d.cap i ↔ E p ∈ capFacet e.P e.cap i)) ∧
      (∀ p, p ∈ sideFacet d.P d.side f → ∀ i, i ≠ f →
        (B (d.side i) (lift p) = 0 ↔ B (e.side i) (lift (E p)) = 0)) := by
  obtain ⟨L, hB, _hside, hcap⟩ := mixed_linear_equivalence d e f hlen
  have hcorner := map_corner_lift d e f L hcap hlen
  obtain ⟨i₀, j₀, hi₀, hj₀, hij₀⟩ := pair_avoiding f
  obtain ⟨E, hE⟩ := ambient_isometry L hB (d.corner i₀ j₀) (e.corner i₀ j₀)
    (hcorner i₀ j₀ hi₀ hj₀ hij₀)
  have hBi (X Y : V) : B (L.symm X) (L.symm Y) = B X Y := by
    simpa only [L.apply_symm_apply] using (hB (L.symm X) (L.symm Y)).symm
  have hcapi (i : Fin 4) (hi : i ≠ f) : L.symm (e.cap i) = d.cap i := by
    rw [← hcap i hi, L.symm_apply_apply]
  have hface (p : HyperbolicThreeSpace) :
      p ∈ sideFacet d.P d.side f ↔ E p ∈ sideFacet e.P e.side f := by
    constructor
    · exact face_forward d e f L hB hcap p (E p) (hE p)
    · intro hp
      apply face_forward e d f L.symm hBi hcapi (E p) p _ hp
      rw [hE, L.symm_apply_apply]
  have hcap_value (p : HyperbolicThreeSpace) (i : Fin 4) (hi : i ≠ f) :
      B (e.cap i) (lift (E p)) = B (d.cap i) (lift p) := by
    rw [hE, ← hcap i hi, hB]
  refine ⟨E, hface, ?_, ?_, ?_⟩
  · intro i j hi hj hij
    apply lift_injective
    rw [hE]
    exact hcorner i j hi hj hij
  · intro p hp i
    have hq := (hface p).mp hp
    change (p ∈ d.P ∧ B (d.cap i) (lift p) = 0) ↔
      (E p ∈ e.P ∧ B (e.cap i) (lift (E p)) = 0)
    by_cases hi : i = f
    · subst i
      have hd := ne_of_lt (face_omitted_cap_strict d f p hp)
      have he := ne_of_lt (face_omitted_cap_strict e f (E p) hq)
      simp only [hd, he, and_false]
    · rw [hcap_value p i hi]
      simp only [hp.1, hq.1, true_and]
  · intro p hp i _hi
    obtain ⟨a, hX, haf, _ha, _hc⟩ := (side_face_coefficients d f p).mp hp
    have hY : rows e a = lift (E p) := by
      rw [← map_rows d e f L hcap a haf, hX, hE]
    obtain ⟨_, hbd, hsd⟩ := temporary_dual_support_conclusion d
    obtain ⟨_, hbe, hse⟩ := temporary_dual_support_conclusion e
    rw [← hX, ← hY]
    change (B (d.side i) (a ᵥ* (d.cap : Matrix (Fin 4) (Fin 4) ℝ)) = 0) ↔
      (B (e.side i) (a ᵥ* (e.cap : Matrix (Fin 4) (Fin 4) ℝ)) = 0)
    rw [(hsd a).2.1 i, (hse a).2.1 i]
    simp only [mul_eq_zero, ne_of_lt (hbd i), ne_of_lt (hbe i), false_or]

/- Relabelling changes no native body, normal, or ordered corner; it only
precomposes their indices. It introduces no geometric assumption. -/
private def relabel (d : NativeSupportCorners) (σ : Equiv.Perm (Fin 4)) :
    NativeSupportCorners where
  P := d.P
  cap := fun i => d.cap (σ i)
  side := fun i => d.side (σ i)
  corner := fun i j => d.corner (σ i) (σ j)
  cap_unit := fun i => d.cap_unit (σ i)
  side_unit := fun i => d.side_unit (σ i)
  body_halfspaces := by
    rw [d.body_halfspaces]
    ext p
    change ((∀ i, B (d.cap i) (lift p) ≤ 0) ∧
      (∀ i, B (d.side i) (lift p) ≤ 0)) ↔
      ((∀ i, B (d.cap (σ i)) (lift p) ≤ 0) ∧
        (∀ i, B (d.side (σ i)) (lift p) ≤ 0))
    constructor
    · rintro ⟨hc, hs⟩
      exact ⟨fun i => hc (σ i), fun i => hs (σ i)⟩
    · rintro ⟨hc, hs⟩
      constructor
      · intro i
        simpa only [σ.apply_symm_apply] using hc (σ.symm i)
      · intro i
        simpa only [σ.apply_symm_apply] using hs (σ.symm i)
  corner_mem := fun i j hij => d.corner_mem (σ i) (σ j) (σ.injective.ne hij)
  cap_incidence := by
    intro i j hij r
    change (d.corner (σ i) (σ j) ∈ capFacet d.P d.cap (σ r)) ↔ r = i
    rw [d.cap_incidence (σ i) (σ j) (σ.injective.ne hij) (σ r)]
    exact σ.injective.eq_iff
  side_incidence := by
    intro i j hij r
    change (d.corner (σ i) (σ j) ∈ sideFacet d.P d.side (σ r)) ↔ r ≠ i ∧ r ≠ j
    rw [d.side_incidence (σ i) (σ j) (σ.injective.ne hij) (σ r)]
    constructor
    · rintro ⟨hri, hrj⟩
      exact ⟨fun h => hri (congrArg σ h), fun h => hrj (congrArg σ h)⟩
    · rintro ⟨hri, hrj⟩
      exact ⟨fun h => hri (σ.injective h), fun h => hrj (σ.injective h)⟩
  orthogonal_incidence := fun j i hji =>
    d.orthogonal_incidence (σ j) (σ i) (σ.injective.ne hji)

/-- SOURCE-ONLY terminal statement. Only the three unordered face edge lengths
are matched (the displayed ordered formulation repeats each length twice).
The entire literal closed native face is transported in both directions, along
with its six ordered corners, all cap traces, and remaining side-support traces.
The cap-f traces are both empty, by the strict omitted-cap proof above. -/
theorem native_closed_side_face_isometry
    (d dprime : NativeSupportCorners) (f : Fin 4) (sigma : Equiv.Perm (Fin 4))
    (hlen : ∀ i j, i ≠ f → j ≠ f → i ≠ j →
      dist (d.corner i j) (d.corner j i) =
        dist (dprime.corner (sigma i) (sigma j)) (dprime.corner (sigma j) (sigma i))) :
    ∃ E : HyperbolicThreeSpace ≃ᵢ HyperbolicThreeSpace,
      (∀ p, p ∈ sideFacet d.P d.side f ↔
        E p ∈ sideFacet dprime.P dprime.side (sigma f)) ∧
      (∀ i j, i ≠ f → j ≠ f → i ≠ j →
        E (d.corner i j) = dprime.corner (sigma i) (sigma j)) ∧
      (∀ p, p ∈ sideFacet d.P d.side f → ∀ i,
        (p ∈ capFacet d.P d.cap i ↔
          E p ∈ capFacet dprime.P dprime.cap (sigma i))) ∧
      (∀ p, p ∈ sideFacet d.P d.side f → ∀ i, i ≠ f →
        (B (d.side i) (lift p) = 0 ↔
          B (dprime.side (sigma i)) (lift (E p)) = 0)) := by
  exact same_labels d (relabel dprime sigma) f hlen

end NativeSideIsometryTransient
end NativeCornerExtractionSource

namespace NativeCornerExtractionSource.NativeSideIsometryTransient
set_option pp.universes true
#check pair_sum_right
#print axioms pair_sum_right
#check pair_sum_left
#print axioms pair_sum_left
#check rows
#print axioms rows
#check rows_sum
#print axioms rows_sum
#check capBasis
#print axioms capBasis
#check capBasis_apply
#print axioms capBasis_apply
#check rows_surjective
#print axioms rows_surjective
#check mixed
#print axioms mixed
#check mixed_independent
#print axioms mixed_independent
#check mixedBasis
#print axioms mixedBasis
#check mixedBasis_apply
#print axioms mixedBasis_apply
#check mixed_gram
#print axioms mixed_gram
#check mixed_linear_equivalence
#print axioms mixed_linear_equivalence
#check corner_lift_formula
#print axioms corner_lift_formula
#check map_corner_lift
#print axioms map_corner_lift
#check pair_avoiding
#print axioms pair_avoiding
#check future_from_anchor
#print axioms future_from_anchor
#check ambient_isometry
#print axioms ambient_isometry
#check cap_offdiagonal_lt
#print axioms cap_offdiagonal_lt
#check omitted_cap_strict
#print axioms omitted_cap_strict
#check coefficients_ne_zero
#print axioms coefficients_ne_zero
#check side_face_coefficients
#print axioms side_face_coefficients
#check face_omitted_cap_strict
#print axioms face_omitted_cap_strict
#check map_rows
#print axioms map_rows
#check face_forward
#print axioms face_forward
#check same_labels
#print axioms same_labels
#check relabel
#print axioms relabel
#check native_closed_side_face_isometry
#print axioms native_closed_side_face_isometry
end NativeCornerExtractionSource.NativeSideIsometryTransient
