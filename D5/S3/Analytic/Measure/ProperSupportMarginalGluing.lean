/- GID: D5/S3/Analytic/Measure/ProperSupportMarginalGluing
   generality: G
   mirror-B: D5/B/S3/Analytic/Measure/ProperSupportMarginalGluing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Common normalized profiles from factorizations of deleted marginals. -/

module

public import OmegaBuild.Commands
public import D5.S3.Combinatorics.Hypergraphs.FinnerProductMeasure
import D5.S3.Analytic.Measure.ProductSupportIntersection
import D5.S3.Analytic.Measure.NormalizedHolderEquality
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

compile_only_with_mathlib

/-! # Proper-support marginal gluing under a product probability law -/

@[expose] public section

open MeasureTheory Function Finset Filter
open scoped ENNReal BigOperators Classical

noncomputable section
set_option autoImplicit false

namespace D5.S3.Analytic.Measure.ProperSupportMarginalGluing

variable {I : Type*} [Fintype I] {X : I → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, MeasureTheory.Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

omit [Fintype I] in
private lemma marginal_fixed [DecidableEq I] (u : Finset I)
    {f : (∀ i, X i) → ℝ≥0∞} {S : Set I} (hd : DependsOn f S)
    (hu : Disjoint S (u : Set I)) : lmarginal μ u f = f := by
  ext x
  have hc (y : ∀ i : u, X i) : f (updateFinset x u y) = f x := by
    apply hd
    intro i hi
    have hni : i ∉ u := fun h => Set.disjoint_left.mp hu hi h
    simp [updateFinset, hni]
  change (∫⁻ y : ∀ i : u, X i, f (updateFinset x u y)
    ∂MeasureTheory.Measure.pi (fun i : u => μ i)) = f x
  simp_rw [hc]
  simp

omit [Fintype I] in
private lemma marginal_idem [DecidableEq I] (u : Finset I)
    (f : (∀ i, X i) → ℝ≥0∞) :
    lmarginal μ u (lmarginal μ u f) = lmarginal μ u f := by
  apply marginal_fixed
  · intro x y hxy
    exact lmarginal_congr μ f hxy
  · exact disjoint_compl_left

omit [Fintype I] in
private lemma marginal_absorb_singleton [DecidableEq I] (u : Finset I)
    {f : (∀ i, X i) → ℝ≥0∞} (hf : Measurable f) {k : I} (hk : k ∈ u) :
    lmarginal μ u (lmarginal μ {k} f) = lmarginal μ u f := by
  conv_lhs => rw [← insert_erase hk,
    lmarginal_insert' _ (hf.lmarginal μ) (notMem_erase k u)]
  conv_rhs => rw [← insert_erase hk, lmarginal_insert' _ hf (notMem_erase k u)]
  simpa only [lmarginal_singleton] using
    congrArg (lmarginal μ (u.erase k)) (marginal_idem μ {k} f)

private lemma integral_coordinate_product (s : Finset I) (h : ∀ i, X i → ℝ≥0∞)
    (hm : ∀ i, Measurable (h i)) :
    (∫⁻ x, ∏ i ∈ s, h i (x i) ∂MeasureTheory.Measure.pi μ) =
      ∏ i ∈ s, ∫⁻ t, h i t ∂μ i := by
  classical
  have H (h : ∀ i, X i → ℝ≥0∞) (hm : ∀ i, Measurable (h i)) :
      (∫⁻ x, ∏ i, h i (x i) ∂MeasureTheory.Measure.pi μ) =
        ∏ i, ∫⁻ t, h i t ∂μ i := by
    let e := (Fintype.equivFin I).symm
    rw [← (measurePreserving_piCongrLeft μ e).lintegral_comp_emb
      (MeasurableEquiv.measurableEmbedding _)]
    simp only [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft,
      Equiv.piCongrLeft_apply_apply]
    exact D5.S3.Combinatorics.Hypergraphs.FinnerProductMeasure.lintegral_fin_prod (fun i => μ (e i))
      (fun i => h (e i)) (fun i => hm (e i))
  let g : ∀ i, X i → ℝ≥0∞ := fun i t => if i ∈ s then h i t else 1
  have hg (i : I) : Measurable (g i) := by
    dsimp [g]
    split_ifs <;> fun_prop
  have hp (x : ∀ i, X i) : (∏ i, g i (x i)) = ∏ i ∈ s, h i (x i) :=
    prod_ite_mem_eq s (fun i => h i (x i))
  rw [← funext hp, H g hg]
  have hi (i : I) : (∫⁻ t, g i t ∂μ i) = if i ∈ s then (∫⁻ t, h i t ∂μ i) else 1 := by
    dsimp [g]
    split_ifs <;> simp
  simp_rw [hi]
  exact prod_ite_mem_eq s (fun i => ∫⁻ t, h i t ∂μ i)

private lemma marginal_coordinate_product [DecidableEq I] (s : Finset I)
    (h : ∀ i, X i → ℝ≥0∞) (hm : ∀ i, Measurable (h i))
    (hi : ∀ i, ∫⁻ t, h i t ∂μ i = 1) (k : I) :
    lmarginal μ (univ.erase k) (fun x => ∏ i ∈ s, h i (x i)) =
      fun x => if k ∈ s then h k (x k) else 1 := by
  classical
  let g : ∀ i, X i → ℝ≥0∞ := fun i t => if i ∈ s then h i t else 1
  have gm (i : I) : Measurable (g i) := by
    dsimp [g]
    split_ifs <;> fun_prop
  have gi (i : I) : ∫⁻ t, g i t ∂μ i = 1 := by
    dsimp [g]
    split_ifs <;> simp [hi]
  have hp (x : ∀ i, X i) : (∏ i, g i (x i)) = ∏ i ∈ s, h i (x i) := by
    exact prod_ite_mem_eq s (fun i => h i (x i))
  ext x
  rw [← funext hp]
  let u : Finset I := univ.erase k
  have he (y : ∀ i : u, X i) :
      (∏ i, g i (updateFinset x u y i)) =
        g k (x k) * ∏ i : u, g i (y i) := by
    rw [← prod_erase_mul _ _ (mem_univ k), mul_comm]
    have hk : updateFinset x u y k = x k := by simp [u, updateFinset]
    rw [hk]
    congr 1
    change (∏ i ∈ u, g i (updateFinset x u y i)) = _
    rw [← prod_coe_sort u (fun i => g i (updateFinset x u y i))]
    apply prod_congr rfl
    intro i hiu
    simp [updateFinset, i.property]
  change (∫⁻ y : ∀ i : u, X i, ∏ i, g i (updateFinset x u y i)
    ∂MeasureTheory.Measure.pi (fun i : u => μ i)) = _
  simp_rw [he]
  rw [lintegral_const_mul _ (show Measurable
    (fun y : ∀ i : u, X i => ∏ i : u, g i (y i)) from
      Finset.measurable_fun_prod _ (fun i _ => (gm i).comp (measurable_pi_apply i)))]
  have hi' : (∫⁻ y : ∀ i : u, X i, ∏ i : u, g i (y i)
      ∂MeasureTheory.Measure.pi (fun i : u => μ i)) = 1 := by
    rw [integral_coordinate_product (fun i : u => μ i) univ
      (fun i : u => g i) (fun i => gm i)]
    simp [gi]
  rw [hi', mul_one]

private lemma profile_integral [DecidableEq I]
    {f : (∀ i, X i) → ℝ≥0∞} (hf : Measurable f)
    (hi : ∫⁻ x, f x ∂MeasureTheory.Measure.pi μ = 1)
    (a : ∀ i, X i) (i : I) :
    (∫⁻ t, lmarginal μ (univ.erase i) f (update a i t) ∂μ i) = 1 := by
  rw [← lmarginal_insert _ hf (notMem_erase i univ), insert_erase (mem_univ i)]
  simpa using hi

omit [∀ i, IsProbabilityMeasure (μ i)] in
private lemma profile_evaluation [DecidableEq I]
    (f : (∀ i, X i) → ℝ≥0∞) (a x : ∀ i, X i) (i : I) :
    lmarginal μ (univ.erase i) f (update a i (x i)) =
      lmarginal μ (univ.erase i) f x := by
  apply lmarginal_congr
  intro k hk
  have hki : k = i := by simpa using hk
  subst k
  simp

private lemma canonical_factor [DecidableEq I] (S : Finset I)
    {f : (∀ i, X i) → ℝ≥0∞} (hf : Measurable f)
    (h : ∀ i, X i → ℝ≥0∞) (hm : ∀ i, Measurable (h i))
    (hi : ∀ i, ∫⁻ t, h i t ∂μ i = 1)
    (he : f =ᵐ[MeasureTheory.Measure.pi μ] (fun x => ∏ i ∈ S, h i (x i)))
    {k : I} (hk : k ∈ S) :
    lmarginal μ (univ.erase k) f =ᵐ[MeasureTheory.Measure.pi μ]
      (fun x => h k (x k)) := by
  have H := D5.S3.Analytic.Measure.ProductSupportIntersection.marginal_congr_ae μ
    (univ.erase k) hf (Finset.measurable_fun_prod _
      (fun i _ => (hm i).comp (measurable_pi_apply i))) he
  change lmarginal μ (univ.erase k) f =ᵐ[MeasureTheory.Measure.pi μ]
    lmarginal μ (univ.erase k) (fun x => ∏ i ∈ S, h i (x i)) at H
  rw [marginal_coordinate_product μ S h hm hi k] at H
  simpa only [ite_eq_left hk] using H

private lemma proper_assembly [DecidableEq I] {J : Type*}
    (s : Finset I) (S : J → Finset I) (f : J → (∀ i, X i) → ℝ≥0∞)
    (hf : ∀ j, Measurable (f j)) (hd : ∀ j, DependsOn (f j) (S j))
    (hi : ∀ j, ∫⁻ x, f j x ∂MeasureTheory.Measure.pi μ = 1)
    (hs : ∀ j, S j ⊆ s) (hp : ∀ j, S j ≠ s)
    (hl : ∀ k ∈ s, ∃ h : ∀ i, X i → ℝ≥0∞,
      (∀ i, Measurable (h i)) ∧ (∀ i, ∫⁻ t, h i t ∂μ i = 1) ∧
      ∀ j, lmarginal μ {k} (f j) =ᵐ[MeasureTheory.Measure.pi μ]
        (fun x => ∏ i ∈ (S j).erase k, h i (x i))) :
    ∃ h : ∀ i, X i → ℝ≥0∞, (∀ i, Measurable (h i)) ∧
      (∀ i, ∫⁻ t, h i t ∂μ i = 1) ∧
      ∀ j, f j =ᵐ[MeasureTheory.Measure.pi μ] (fun x => ∏ i ∈ S j, h i (x i)) := by
  classical
  let a : ∀ i, X i := fun i => Classical.choice (nonempty_of_isProbabilityMeasure (μ i))
  let p (i : I) (hi : ∃ j, i ∈ S j) : J := Classical.choose hi
  have hpm (i : I) (hi : ∃ j, i ∈ S j) : i ∈ S (p i hi) := Classical.choose_spec hi
  let h : ∀ i, X i → ℝ≥0∞ := fun i t =>
    if his : ∃ j, i ∈ S j then lmarginal μ (univ.erase i) (f (p i his)) (update a i t) else 1
  have hm (i : I) : Measurable (h i) := by
    dsimp [h]
    split_ifs with his
    · exact ((hf (p i his)).lmarginal μ).comp (measurable_update a)
    · exact measurable_const
  have hu (i : I) : ∫⁻ t, h i t ∂μ i = 1 := by
    dsimp [h]
    split_ifs with his
    · exact profile_integral μ (hf _) (hi _) a i
    · simp
  refine ⟨h, hm, hu, ?_⟩
  intro j
  have hn : ∃ k ∈ s, k ∉ S j := by
    by_contra H
    push Not at H
    exact hp j (Subset.antisymm (hs j) H)
  obtain ⟨k, hks, hkj⟩ := hn
  obtain ⟨g, gm, gu, ge⟩ := hl k hks
  have hmatch : ∀ i ∈ S j, (fun x : ∀ i, X i => h i (x i)) =ᵐ[MeasureTheory.Measure.pi μ]
      (fun x => g i (x i)) := by
    intro i hij
    have his : ∃ j, i ∈ S j := ⟨j, hij⟩
    have hik : i ≠ k := ne_of_mem_of_not_mem hij hkj
    have hip : i ∈ (S (p i his)).erase k := mem_erase.mpr ⟨hik, hpm i his⟩
    have H := canonical_factor μ ((S (p i his)).erase k) ((hf _).lmarginal μ)
      g gm gu (ge _) hip
    have hki : k ∈ (univ : Finset I).erase i := by simp [hik.symm]
    rw [marginal_absorb_singleton μ _ (hf _) hki] at H
    filter_upwards [H] with x hx
    dsimp [h]
    rw [dite_eq_left his, profile_evaluation]
    exact hx
  have hprod : (fun x : ∀ i, X i => ∏ i ∈ S j, h i (x i)) =ᵐ[MeasureTheory.Measure.pi μ]
      (fun x => ∏ i ∈ S j, g i (x i)) := by
    have H := (eventually_all_finset (S j)).mpr hmatch
    filter_upwards [H] with x hx
    exact prod_congr rfl (fun i hi => hx i hi)
  have hfix : lmarginal μ {k} (f j) = f j := by
    apply marginal_fixed μ _ (hd j)
    simpa using hkj
  have H := ge j
  rw [hfix, erase_eq_of_notMem hkj] at H
  exact H.trans hprod.symm

/-- Normalized factorizations of every one-coordinate-deleted marginal glue to
one common normalized factorization of all original proper-support rows.
The hypotheses provide actual factorizations under the original product law. -/
theorem exists_common_profiles_of_deleted_marginal_factorizations
    {J : Type*} (s : Finset I) (S : J → Finset I)
    (f : J → (∀ i, X i) → ℝ≥0∞)
    (hf : ∀ j, Measurable (f j)) (hd : ∀ j, DependsOn (f j) (S j))
    (hpos : ∀ j, 0 < ∫⁻ x, f j x ∂MeasureTheory.Measure.pi μ)
    (hfin : ∀ j, (∫⁻ x, f j x ∂MeasureTheory.Measure.pi μ) ≠ ∞)
    (hs : ∀ j, S j ⊆ s) (hp : ∀ j, S j ≠ s)
    (hl : ∀ k ∈ s, ∃ h : ∀ i, X i → ℝ≥0∞,
      (∀ i, Measurable (h i)) ∧ (∀ i, ∫⁻ t, h i t ∂μ i = 1) ∧
      ∀ j, lmarginal μ {k} (f j) =ᵐ[MeasureTheory.Measure.pi μ]
        (fun x => (∫⁻ y, f j y ∂MeasureTheory.Measure.pi μ) *
          ∏ i ∈ (S j).erase k, h i (x i))) :
    ∃ h : ∀ i, X i → ℝ≥0∞, (∀ i, Measurable (h i)) ∧
      (∀ i, ∫⁻ t, h i t ∂μ i = 1) ∧
      ∀ j, f j =ᵐ[MeasureTheory.Measure.pi μ]
        (fun x => (∫⁻ y, f j y ∂MeasureTheory.Measure.pi μ) *
          ∏ i ∈ S j, h i (x i)) := by
  classical
  let m (j : J) := ∫⁻ x, f j x ∂MeasureTheory.Measure.pi μ
  let q (j : J) (x : ∀ i, X i) := (m j)⁻¹ * f j x
  have qm (j : J) : Measurable (q j) := measurable_const.mul (hf j)
  have qd (j : J) : DependsOn (q j) (S j) := by
    intro x y hxy
    exact congrArg ((m j)⁻¹ * ·) (hd j hxy)
  have qu (j : J) : ∫⁻ x, q j x ∂MeasureTheory.Measure.pi μ = 1 := by
    rw [show q j = fun x => (m j)⁻¹ * f j x from rfl,
      lintegral_const_mul _ (hf j)]
    exact ENNReal.inv_mul_cancel (hpos j).ne' (hfin j)
  have ql : ∀ k ∈ s, ∃ h : ∀ i, X i → ℝ≥0∞,
      (∀ i, Measurable (h i)) ∧ (∀ i, ∫⁻ t, h i t ∂μ i = 1) ∧
      ∀ j, lmarginal μ {k} (q j) =ᵐ[MeasureTheory.Measure.pi μ]
        (fun x => ∏ i ∈ (S j).erase k, h i (x i)) := by
    intro k hk
    obtain ⟨h, hm, hu, he⟩ := hl k hk
    refine ⟨h, hm, hu, ?_⟩
    intro j
    have ht : lmarginal μ {k} (q j) =
        fun x => (m j)⁻¹ * lmarginal μ {k} (f j) x := by
      ext x
      change (∫⁻ y, (m j)⁻¹ * f j (updateFinset x {k} y)
        ∂MeasureTheory.Measure.pi (fun i : ({k} : Finset I) => μ i)) = _
      exact lintegral_const_mul _ ((hf j).comp measurable_updateFinset)
    rw [ht]
    filter_upwards [he j] with x hx
    rw [hx, ← mul_assoc, ENNReal.inv_mul_cancel (hpos j).ne' (hfin j), one_mul]
  obtain ⟨h, hm, hu, he⟩ := proper_assembly μ s S q qm qd qu hs hp ql
  refine ⟨h, hm, hu, ?_⟩
  intro j
  filter_upwards [he j] with x hx
  have hh := congrArg (m j * ·) hx
  change m j * ((m j)⁻¹ * f j x) = _ at hh
  rw [← mul_assoc, ENNReal.mul_inv_cancel (hpos j).ne' (hfin j), one_mul] at hh
  exact hh

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private lemma marginal_integral [DecidableEq I] (u : Finset I)
    {f : (∀ i, X i) → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, lmarginal μ u f x ∂MeasureTheory.Measure.pi μ) =
      ∫⁻ x, f x ∂MeasureTheory.Measure.pi μ := by
  have H : lmarginal μ u (lmarginal μ u f) = lmarginal μ u f :=
    marginal_idem μ u f
  exact lintegral_eq_of_lmarginal_eq u (hf.lmarginal μ) hf H

private lemma deleted_saturation {J : Type*} [Fintype J]
    (S : J → Finset I) (q : J → (∀ i, X i) → ℝ≥0∞) (w : J → ℝ)
    (hm : ∀ j, Measurable (q j)) (hd : ∀ j, DependsOn (q j) (S j))
    (hi : ∀ j, ∫⁻ x, q j x ∂MeasureTheory.Measure.pi μ = 1)
    (hw : ∀ j, 0 ≤ w j)
    (hb : ∀ i, ∑ j ∈ univ.filter (fun j => i ∈ S j), w j ≤ 1)
    (he : ∫⁻ x, ∏ j, q j x ^ w j ∂MeasureTheory.Measure.pi μ = 1) (k : I) :
    (∫⁻ x, ∏ j, lmarginal μ {k} (q j) x ^ w j ∂MeasureTheory.Measure.pi μ) = 1 := by
  classical
  let p := fun j => lmarginal μ {k} (q j)
  have pm (j : J) : Measurable (p j) := (hm j).lmarginal μ
  have pd (j : J) : DependsOn (p j) ((S j : Set I) \ {k}) := by
    simpa only [p, coe_singleton] using
      D5.S3.Analytic.Measure.ProductSupportIntersection.marginal_depends μ {k} (hd j)
  have upper := D5.S3.Combinatorics.Hypergraphs.FinnerProductMeasure.finner_product_measure
    μ (fun j => (S j : Set I) \ {k}) p w pm pd hw (by
      intro i
      by_cases hik : i = k
      · subst i; simp
      · simpa only [Set.mem_sdiff, Set.mem_singleton_iff, hik, not_false_eq_true,
          and_true, mem_coe] using hb i)
  have pu (j : J) : ∫⁻ x, p j x ∂MeasureTheory.Measure.pi μ = 1 :=
    (marginal_integral μ {k} (hm j)).trans (hi j)
  simp only [pu, ENNReal.one_rpow, prod_const_one] at upper
  apply le_antisymm upper
  have lower := lintegral_mono (μ := MeasureTheory.Measure.pi μ)
    (D5.S3.Combinatorics.Hypergraphs.FinnerProductMeasure.marginal_estimate
      μ (fun j => (S j : Set I)) q w hm hd hw
      (by simpa only [mem_coe] using hb) {k})
  rw [marginal_integral μ {k}
    (Finset.measurable_fun_prod _ (fun j _ => (hm j).pow_const _)), he] at lower
  exact lower

private lemma product_rpow_sum {J : Type*} (t : Finset J) (w : J → ℝ)
    (hw : ∀ j ∈ t, 0 ≤ w j) (z : ℝ≥0∞) :
    (∏ j ∈ t, z ^ w j) = z ^ (∑ j ∈ t, w j) := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert j t hj ih =>
    rw [prod_insert hj, sum_insert hj,
      ih (fun k hk => hw k (mem_insert_of_mem hk)),
      ENNReal.rpow_add_of_nonneg _ _ (hw j (mem_insert_self ..))
        (sum_nonneg (fun k hk => hw k (mem_insert_of_mem hk)))]

omit [Fintype I] [∀ i, MeasurableSpace (X i)] in
private lemma balanced_product {J : Type*} [Fintype J]
    (s : Finset I) (S : J → Finset I) (w : J → ℝ)
    (hs : ∀ j, S j ⊆ s) (hw : ∀ j, 0 ≤ w j)
    (hb : ∀ i ∈ s, ∑ j ∈ univ.filter (fun j => i ∈ S j), w j = 1)
    (h : ∀ i, X i → ℝ≥0∞) (x : ∀ i, X i) :
    (∏ j, (∏ i ∈ S j, h i (x i)) ^ w j) = ∏ i ∈ s, h i (x i) := by
  classical
  have row (j : J) : (∏ i ∈ S j, h i (x i)) ^ w j =
      ∏ i ∈ s, if i ∈ S j then h i (x i) ^ w j else 1 := by
    rw [← ENNReal.prod_rpow_of_nonneg (hw j)]
    calc
      _ = ∏ i ∈ S j, if i ∈ S j then h i (x i) ^ w j else 1 := by
        apply prod_congr rfl
        intro i hi
        rw [ite_eq_left hi]
      _ = _ := prod_subset (hs j) (by intro i _ hi; rw [ite_eq_right hi])
  simp_rw [row]
  rw [Finset.prod_comm]
  apply prod_congr rfl
  intro i his
  rw [← prod_filter, product_rpow_sum _ w (fun j _ => hw j), hb i his,
    ENNReal.rpow_one]

private lemma constant_unit
    {q : (∀ i, X i) → ℝ≥0∞} (hd : DependsOn q ∅)
    (hi : ∫⁻ x, q x ∂MeasureTheory.Measure.pi μ = 1) : q = fun _ => 1 := by
  let a : ∀ i, X i := fun i => Classical.choice (nonempty_of_isProbabilityMeasure (μ i))
  have H : q = fun _ => q a := funext (fun x => hd.empty x a)
  rw [H] at hi
  funext x
  exact (hd.empty x a).trans (by simpa using hi)

private lemma singleton_profiles {J : Type*} [Fintype J]
    (k : I) (S : J → Finset I) (q : J → (∀ i, X i) → ℝ≥0∞) (w : J → ℝ)
    (hm : ∀ j, Measurable (q j)) (hd : ∀ j, DependsOn (q j) (S j))
    (hi : ∀ j, ∫⁻ x, q j x ∂MeasureTheory.Measure.pi μ = 1)
    (hs : ∀ j, S j ⊆ {k}) (hw : ∀ j, 0 < w j)
    (hb : ∑ j ∈ univ.filter (fun j => k ∈ S j), w j = 1)
    (he : ∫⁻ x, ∏ j, q j x ^ w j ∂MeasureTheory.Measure.pi μ = 1) :
    ∃ h : ∀ i, X i → ℝ≥0∞, (∀ i, Measurable (h i)) ∧
      (∀ i, ∫⁻ t, h i t ∂μ i = 1) ∧
      ∀ j, q j =ᵐ[MeasureTheory.Measure.pi μ] (fun x => ∏ i ∈ S j, h i (x i)) := by
  classical
  let t := univ.filter (fun j => k ∈ S j)
  have empty_row (j : J) (hj : j ∉ t) : q j = fun _ => 1 := by
    apply constant_unit μ _ (hi j)
    have hS : S j = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro i hiS
      have hik : i = k := by simpa using hs j hiS
      subst i
      exact hj (mem_filter.mpr ⟨mem_univ _, hiS⟩)
    simpa only [hS, coe_empty] using hd j
  have tnon : t.Nonempty := by
    by_contra H
    have ht : t = ∅ := not_nonempty_iff_eq_empty.mp H
    change ∑ j ∈ t, w j = 1 at hb
    simp [ht] at hb
  obtain ⟨j₀, hj₀⟩ := tnon
  have hqt : (fun x => ∏ j : t, q j x ^ w j) = fun x => ∏ j, q j x ^ w j := by
    funext x
    rw [prod_coe_sort t (fun j => q j x ^ w j)]
    apply prod_subset (subset_univ t)
    intro j _ hj
    rw [empty_row j hj, ENNReal.one_rpow]
  have equal := (D5.S3.Analytic.Measure.NormalizedHolderEquality.lintegral_prod_rpow_eq_one_iff
    (MeasureTheory.Measure.pi μ) (fun j : t => q j) (fun j : t => w j)
    (fun j => (hm j).aemeasurable) (fun j => hi j) (fun j => hw j)
    (by rw [sum_coe_sort]; exact hb)).mp (by simpa only [hqt] using he)
  let a : ∀ i, X i := fun i => Classical.choice (nonempty_of_isProbabilityMeasure (μ i))
  let h : ∀ i, X i → ℝ≥0∞ := fun i z =>
    if hik : i = k then q j₀ (update a i z) else 1
  have full (x : ∀ i, X i) : h k (x k) = q j₀ x := by
    simp only [h, dite_true]
    apply hd j₀
    intro i hiS
    have hik : i = k := by simpa using hs j₀ hiS
    subst i
    simp
  have hm' (i : I) : Measurable (h i) := by
    dsimp [h]
    split_ifs <;> fun_prop
  have hu (i : I) : ∫⁻ z, h i z ∂μ i = 1 := by
    by_cases hik : i = k
    · subst i
      have H : lmarginal μ {k} (q j₀) = fun _ => ∫⁻ z, h k z ∂μ k := by
        rw [lmarginal_singleton]
        funext x
        apply lintegral_congr
        intro z
        exact (full (update x k z)).symm.trans (by simp)
      have H' := marginal_integral μ {k} (hm j₀)
      rw [H, hi j₀] at H'
      simpa using H'
    · simp [h, hik]
  refine ⟨h, hm', hu, ?_⟩
  intro j
  by_cases hj : j ∈ t
  · have hS : S j = {k} := Subset.antisymm (hs j)
      (singleton_subset_iff.mpr (mem_filter.mp hj).2)
    have H := equal (⟨j, hj⟩ : t) ⟨j₀, hj₀⟩
    filter_upwards [H] with x hx
    simpa only [hS, prod_singleton, full] using hx
  · rw [empty_row j hj]
    have hS : S j = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro i hiS
      have hik : i = k := by simpa using hs j hiS
      subst i
      exact hj (mem_filter.mpr ⟨mem_univ _, hiS⟩)
    simp [hS]

universe uJ

private def ActiveConclusion {J : Type uJ} (S : J → Finset I)
    (q : J → (∀ i, X i) → ℝ≥0∞) : Prop :=
  ∃ h : ∀ i, X i → ℝ≥0∞, (∀ i, Measurable (h i)) ∧
    (∀ i, ∫⁻ t, h i t ∂μ i = 1) ∧
    ∀ j, q j =ᵐ[MeasureTheory.Measure.pi μ] (fun x => ∏ i ∈ S j, h i (x i))

private def ActiveHypotheses {J : Type uJ} [Fintype J] (s : Finset I)
    (S : J → Finset I) (q : J → (∀ i, X i) → ℝ≥0∞) (w : J → ℝ) : Prop :=
  (∀ j, Measurable (q j)) ∧ (∀ j, DependsOn (q j) (S j)) ∧
  (∀ j, ∫⁻ x, q j x ∂MeasureTheory.Measure.pi μ = 1) ∧
  (∀ j, S j ⊆ s) ∧ (∀ j, 0 < w j) ∧
  (∀ i ∈ s, ∑ j ∈ univ.filter (fun j => i ∈ S j), w j = 1) ∧
  (∀ a ∈ s, ∀ b ∈ s, (∀ j, a ∈ S j ↔ b ∈ S j) → a = b) ∧
  (∫⁻ x, ∏ j, q j x ^ w j ∂MeasureTheory.Measure.pi μ = 1)

private lemma proper_step (s : Finset I)
    (ih : ∀ t ⊂ s, ∀ {J : Type uJ} [Fintype J]
      (S : J → Finset I) (q : J → (∀ i, X i) → ℝ≥0∞) (w : J → ℝ),
      ActiveHypotheses μ t S q w → ActiveConclusion μ S q)
    {J : Type uJ} [Fintype J] (S : J → Finset I)
    (q : J → (∀ i, X i) → ℝ≥0∞) (w : J → ℝ)
    (H : ActiveHypotheses μ s S q w) (hp : ∀ j, S j ≠ s) : ActiveConclusion μ S q := by
  classical
  obtain ⟨hm, hd, hi, hs, hw, hb, hsep, he⟩ := H
  apply proper_assembly μ s S q hm hd hi hs hp
  intro k hk
  let p := fun j => lmarginal μ {k} (q j)
  have hd' (j : J) : DependsOn (p j) ((S j).erase k) := by
    simpa only [coe_erase, coe_singleton] using
      D5.S3.Analytic.Measure.ProductSupportIntersection.marginal_depends μ {k} (hd j)
  apply ih (s.erase k) (erase_ssubset hk) (fun j => (S j).erase k) p w
  refine ⟨fun j => (hm j).lmarginal μ, hd', ?_, ?_, hw, ?_, ?_, ?_⟩
  · intro j
    exact (marginal_integral μ {k} (hm j)).trans (hi j)
  · intro j
    exact erase_subset_erase k (hs j)
  · intro i his
    have hik := (mem_erase.mp his).1
    have Hfilter : univ.filter (fun j => i ∈ (S j).erase k) =
        univ.filter (fun j => i ∈ S j) := by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_erase]
      exact and_iff_right hik
    convert hb i (mem_of_mem_erase his) using 1
    congr 1
  · intro a ha b hb' hab
    apply hsep a (mem_of_mem_erase ha) b (mem_of_mem_erase hb')
    intro j
    exact ⟨fun hj => (mem_erase.mp ((hab j).mp
      (mem_erase.mpr ⟨(mem_erase.mp ha).1, hj⟩))).2,
      fun hj => (mem_erase.mp ((hab j).mpr
        (mem_erase.mpr ⟨(mem_erase.mp hb').1, hj⟩))).2⟩
  · apply deleted_saturation μ S q w hm hd hi (fun j => (hw j).le) _ he k
    intro i
    by_cases his : i ∈ s
    · exact (hb i his).le
    · have hn (j : J) : i ∉ S j := fun hj => his (hs j hj)
      simp [hn]

private lemma full_step (s : Finset I) (hcard : 1 < s.card)
    (ih : ∀ t ⊂ s, ∀ {J : Type uJ} [Fintype J]
      (S : J → Finset I) (q : J → (∀ i, X i) → ℝ≥0∞) (w : J → ℝ),
      ActiveHypotheses μ t S q w → ActiveConclusion μ S q)
    {J : Type uJ} [Fintype J] (S : J → Finset I)
    (q : J → (∀ i, X i) → ℝ≥0∞) (w : J → ℝ)
    (H : ActiveHypotheses μ s S q w) : ActiveConclusion μ S q := by
  classical
  obtain ⟨hm, hd, hi, hs, hw, hb, hsep, he⟩ := H
  let P := univ.filter (fun j => S j ≠ s)
  let r : ℝ := 1 - ∑ j ∈ Pᶜ, w j
  have mask (j : J) (hj : j ∈ Pᶜ) : S j = s := by simpa [P] using hj
  have budget (i : I) (his : i ∈ s) :
      (∑ j ∈ univ.filter (fun j : P => i ∈ S j), w j) = r := by
    have Hsplit := sum_add_sum_compl P (fun j => if i ∈ S j then w j else 0)
    have Hfull : (∑ j ∈ Pᶜ, if i ∈ S j then w j else 0) = ∑ j ∈ Pᶜ, w j := by
      apply sum_congr rfl
      intro j hj
      rw [mask j hj, ite_eq_left his]
    rw [Hfull] at Hsplit
    have Hb := hb i his
    rw [sum_filter] at Hb
    rw [sum_filter, sum_coe_sort P (fun j => if i ∈ S j then w j else 0)]
    convert (eq_sub_iff_add_eq.mpr (Hsplit.trans Hb)) using 1
  have rpos : 0 < r := by
    by_contra hn
    have rn : r ≤ 0 := le_of_not_gt hn
    have emptyinc (i : I) (his : i ∈ s) (j : P) : i ∉ S j := by
      intro hij
      have hle : w j ≤ ∑ j ∈ univ.filter (fun j : P => i ∈ S j), w j :=
        by
          convert single_le_sum (s := univ.filter (fun j : P => i ∈ S j))
            (f := fun j : P => w j) (fun j _ => (hw j).le)
            (mem_filter.mpr ⟨mem_univ j, hij⟩) using 1
      rw [budget i his] at hle
      exact (not_le_of_gt (hw j)) (hle.trans rn)
    obtain ⟨a, ha, b, hb', hab⟩ := one_lt_card.mp hcard
    apply hab
    apply hsep a ha b hb'
    intro j
    by_cases hj : j ∈ P
    · exact iff_of_false (emptyinc a ha ⟨j, hj⟩) (emptyinc b hb' ⟨j, hj⟩)
    · rw [mask j (mem_compl.mpr hj)]
      exact iff_of_true ha hb'
  let v : P → ℝ := fun j => w j / r
  have vp (j : P) : 0 < v j := div_pos (hw j) rpos
  have vb (i : I) (his : i ∈ s) :
      (∑ j ∈ univ.filter (fun j : P => i ∈ S j), v j) = 1 := by
    dsimp [v]
    rw [← sum_div]
    have H := budget i his
    change (∑ j ∈ univ.filter (fun j : P => i ∈ S j), w j) / r = 1
    rw [H, div_self rpos.ne']
  let Q : (∀ i, X i) → ℝ≥0∞ := fun x => ∏ j : P, q j x ^ v j
  have Qm : Measurable Q := Finset.measurable_fun_prod _ (fun j _ => (hm j).pow_const _)
  have Qle : (∫⁻ x, Q x ∂MeasureTheory.Measure.pi μ) ≤ 1 := by
    have H := D5.S3.Combinatorics.Hypergraphs.FinnerProductMeasure.finner_product_measure
      μ (fun j : P => (S j : Set I)) (fun j : P => q j) v
      (fun j => hm j) (fun j => hd j) (fun j => (vp j).le) (by
        intro i
        by_cases his : i ∈ s
        · simpa only [mem_coe] using (vb i his).le
        · have hn (j : P) : i ∉ S j := fun hj => his (hs j hj)
          simp [hn])
    simpa only [hi, ENNReal.one_rpow, prod_const_one] using H
  have Qpower (x : ∀ i, X i) : Q x ^ r = ∏ j ∈ P, q j x ^ w j := by
    dsimp [Q]
    rw [← ENNReal.prod_rpow_of_nonneg rpos.le]
    simp_rw [← ENNReal.rpow_mul, v, div_mul_cancel₀ (h := rpos.ne')]
    exact prod_attach P (fun j => q j x ^ w j)
  have split (x : ∀ i, X i) :
      (∏ j, q j x ^ w j) = Q x ^ r * ∏ j ∈ Pᶜ, q j x ^ w j := by
    rw [Qpower, prod_mul_prod_compl]
  have Qunit : ∫⁻ x, Q x ∂MeasureTheory.Measure.pi μ = 1 := by
    have Hb := ENNReal.lintegral_mul_prod_norm_pow_le (μ := MeasureTheory.Measure.pi μ)
      Pᶜ Qm.aemeasurable (fun j _ => (hm j).aemeasurable) r
      (by dsimp [r]; ring) rpos.le (fun j _ => (hw j).le)
    simp only [hi, ENNReal.one_rpow, prod_const_one, mul_one] at Hb
    have Hsplit : (∫⁻ x, Q x ^ r * ∏ j ∈ Pᶜ, q j x ^ w j
        ∂MeasureTheory.Measure.pi μ) = 1 := by simpa only [← split] using he
    rw [Hsplit] at Hb
    apply le_antisymm Qle
    exact (ENNReal.rpow_le_rpow_iff rpos).mp (by simpa using Hb)
  have Hp : ActiveHypotheses μ s (fun j : P => S j) (fun j : P => q j) v := by
    refine ⟨fun j => hm j, fun j => hd j, fun j => hi j, fun j => hs j, vp, ?_, ?_, Qunit⟩
    · intro i his
      exact vb i his
    intro a ha b hb' hab
    apply hsep a ha b hb'
    intro j
    by_cases hj : j ∈ P
    · exact hab ⟨j, hj⟩
    · rw [mask j (mem_compl.mpr hj)]
      exact iff_of_true ha hb'
  obtain ⟨h, hmeas, hunit, hrep⟩ := proper_step μ s ih (fun j : P => S j)
    (fun j : P => q j) v Hp (fun j => (mem_filter.mp j.property).2)
  have Qrep : Q =ᵐ[MeasureTheory.Measure.pi μ] (fun x => ∏ i ∈ s, h i (x i)) := by
    have Hrep : ∀ᵐ x ∂MeasureTheory.Measure.pi μ, ∀ j : P,
        q j x = ∏ i ∈ S j, h i (x i) := ae_all_iff.mpr hrep
    filter_upwards [Hrep] with x hx
    dsimp [Q]
    simp_rw [hx]
    exact balanced_product s (fun j : P => S j) v (fun j => hs j)
      (fun j => (vp j).le) vb h x
  let z : Option ↥(Pᶜ) → (∀ i, X i) → ℝ≥0∞ := fun j => j.elim Q (fun j => q j)
  let a : Option ↥(Pᶜ) → ℝ := fun j => j.elim r (fun j => w j)
  have ze : ∫⁻ x, ∏ j, z j x ^ a j ∂MeasureTheory.Measure.pi μ = 1 := by
    have zp (x : ∀ i, X i) : (∏ j, z j x ^ a j) =
        Q x ^ r * ∏ j ∈ Pᶜ, q j x ^ w j := by
      rw [Fintype.prod_option]
      change Q x ^ r * (∏ j : ↥(Pᶜ), q j x ^ w j) = _
      rw [prod_coe_sort (Pᶜ) (fun j => q j x ^ w j)]
    simpa only [zp, ← split] using he
  have equal := (D5.S3.Analytic.Measure.NormalizedHolderEquality.lintegral_prod_rpow_eq_one_iff
    (MeasureTheory.Measure.pi μ) z a
    (by intro j; cases j with | none => exact Qm.aemeasurable | some j => exact (hm j).aemeasurable)
    (by intro j; cases j with | none => exact Qunit | some j => exact hi j)
    (by intro j; cases j with | none => exact rpos | some j => exact hw j)
    (by rw [Fintype.sum_option]; change r + (∑ j : ↥(Pᶜ), w j) = 1
        rw [sum_coe_sort]; dsimp [r]; ring)).mp ze
  refine ⟨h, hmeas, hunit, ?_⟩
  intro j
  by_cases hj : j ∈ P
  · exact hrep ⟨j, hj⟩
  · have H := equal (some ⟨j, mem_compl.mpr hj⟩) none
    have H' := H.trans Qrep
    dsimp [z] at H'
    simpa only [mask j (mem_compl.mpr hj)] using H'

private theorem normalized_forward : ∀ s : Finset I, ∀ {J : Type uJ} [Fintype J]
    (S : J → Finset I) (q : J → (∀ i, X i) → ℝ≥0∞) (w : J → ℝ),
    ActiveHypotheses μ s S q w → ActiveConclusion μ S q := by
  classical
  intro s
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    intro J inst S q w H
    by_cases hcard : 1 < s.card
    · exact full_step μ s hcard ih S q w H
    obtain ⟨hm, hd, hi, hs, hw, hb, hsep, he⟩ := H
    by_cases hempty : s = ∅
    · refine ⟨fun _ _ => 1, fun _ => measurable_const, ?_, ?_⟩
      · intro i; simp
      · intro j
        have hS : S j = ∅ := subset_empty.mp (hempty ▸ hs j)
        have hq : q j = fun _ => 1 := constant_unit μ
          (by simpa only [hS, coe_empty] using hd j) (hi j)
        simp [hS, hq]
    · obtain ⟨k, hk⟩ := nonempty_iff_ne_empty.mpr hempty
      have hsone : s = {k} := Subset.antisymm
        (fun i hiS => mem_singleton.mpr ((card_le_one.mp (Nat.le_of_not_gt hcard)) i hiS k hk))
        (singleton_subset_iff.mpr hk)
      exact singleton_profiles μ k S q w hm hd hi (fun j => hsone ▸ hs j)
        hw (hb k hk) he

/-- Equality in balanced Finner with separated coordinate incidence patterns.
All masses and almost-everywhere equalities use the original product law. -/
theorem finner_equality_iff_common_profiles {J : Type uJ} [Fintype J]
    (S : J → Finset I) (f : J → (∀ i, X i) → ℝ≥0∞) (w : J → ℝ)
    (hf : ∀ j, Measurable (f j)) (hd : ∀ j, DependsOn (f j) (S j))
    (hpos : ∀ j, 0 < ∫⁻ x, f j x ∂MeasureTheory.Measure.pi μ)
    (hfin : ∀ j, (∫⁻ x, f j x ∂MeasureTheory.Measure.pi μ) ≠ ∞)
    (hw : ∀ j, 0 < w j)
    (hb : ∀ i, ∑ j ∈ univ.filter (fun j => i ∈ S j), w j = 1)
    (hsep : ∀ a b, (∀ j, a ∈ S j ↔ b ∈ S j) → a = b) :
    (∫⁻ x, ∏ j, f j x ^ w j ∂MeasureTheory.Measure.pi μ) =
        ∏ j, (∫⁻ x, f j x ∂MeasureTheory.Measure.pi μ) ^ w j ↔
      ∃ h : ∀ i, X i → ℝ≥0∞, (∀ i, Measurable (h i)) ∧
        (∀ i, ∫⁻ t, h i t ∂μ i = 1) ∧
        ∀ j, f j =ᵐ[MeasureTheory.Measure.pi μ]
          (fun x => (∫⁻ y, f j y ∂MeasureTheory.Measure.pi μ) *
            ∏ i ∈ S j, h i (x i)) := by
  classical
  let m (j : J) := ∫⁻ x, f j x ∂MeasureTheory.Measure.pi μ
  let q (j : J) (x : ∀ i, X i) := (m j)⁻¹ * f j x
  have qm (j : J) : Measurable (q j) := measurable_const.mul (hf j)
  have qd (j : J) : DependsOn (q j) (S j) := by
    intro x y hxy
    exact congrArg ((m j)⁻¹ * ·) (hd j hxy)
  have qu (j : J) : ∫⁻ x, q j x ∂MeasureTheory.Measure.pi μ = 1 := by
    rw [show q j = fun x => (m j)⁻¹ * f j x from rfl, lintegral_const_mul _ (hf j)]
    exact ENNReal.inv_mul_cancel (hpos j).ne' (hfin j)
  have fq (j : J) (x : ∀ i, X i) : f j x = m j * q j x := by
    dsimp [q]
    rw [← mul_assoc, ENNReal.mul_inv_cancel (hpos j).ne' (hfin j), one_mul]
  let M : ℝ≥0∞ := ∏ j, m j ^ w j
  have Mzero : M ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    intro j hj
    exact mt (ENNReal.rpow_eq_zero_iff_of_pos (hw j)).mp (hpos j).ne'
  have Mtop : M ≠ ∞ := ENNReal.prod_ne_top (fun j _ =>
    ENNReal.rpow_ne_top_of_nonneg (hw j).le (hfin j))
  have prodq (x : ∀ i, X i) : (∏ j, f j x ^ w j) = M * ∏ j, q j x ^ w j := by
    calc
      _ = ∏ j, (m j * q j x) ^ w j :=
        prod_congr rfl (fun j _ => congrArg (fun z : ℝ≥0∞ => z ^ w j) (fq j x))
      _ = ∏ j, (m j ^ w j * q j x ^ w j) :=
        prod_congr rfl (fun j _ => ENNReal.mul_rpow_of_nonneg _ _ (hw j).le)
      _ = _ := prod_mul_distrib
  have intq : (∫⁻ x, ∏ j, f j x ^ w j ∂MeasureTheory.Measure.pi μ) =
      M * (∫⁻ x, ∏ j, q j x ^ w j ∂MeasureTheory.Measure.pi μ) := by
    simp_rw [prodq]
    exact lintegral_const_mul _ (Finset.measurable_fun_prod _ (fun j _ => (qm j).pow_const _))
  have normalize : ((∫⁻ x, ∏ j, f j x ^ w j ∂MeasureTheory.Measure.pi μ) = M) ↔
      (∫⁻ x, ∏ j, q j x ^ w j ∂MeasureTheory.Measure.pi μ) = 1 := by
    rw [intq]
    constructor
    · intro H
      apply (ENNReal.mul_right_inj Mzero Mtop).mp
      simpa only [mul_one] using H
    · intro H
      rw [H, mul_one]
  constructor
  · intro he
    have qe : ∫⁻ x, ∏ j, q j x ^ w j ∂MeasureTheory.Measure.pi μ = 1 := normalize.mp he
    obtain ⟨h, hm, hu, hq⟩ := normalized_forward μ univ S q w
      ⟨qm, qd, qu, fun j => subset_univ _, hw, fun i _ => hb i,
        fun a _ b _ => hsep a b, qe⟩
    refine ⟨h, hm, hu, ?_⟩
    intro j
    filter_upwards [hq j] with x hx
    exact (fq j x).trans (congrArg (m j * ·) hx)
  · rintro ⟨h, hm, hu, he⟩
    apply normalize.mpr
    have qrep (j : J) : q j =ᵐ[MeasureTheory.Measure.pi μ]
        (fun x => ∏ i ∈ S j, h i (x i)) := by
      filter_upwards [he j] with x hx
      change (m j)⁻¹ * f j x = _
      rw [hx, ← mul_assoc, ENNReal.inv_mul_cancel (hpos j).ne' (hfin j), one_mul]
    have allrep := ae_all_iff.mpr qrep
    have H : (fun x => ∏ j, q j x ^ w j) =ᵐ[MeasureTheory.Measure.pi μ]
        (fun x => ∏ i, h i (x i)) := by
      filter_upwards [allrep] with x hx
      simp_rw [hx]
      exact balanced_product univ S w (fun j => subset_univ _) (fun j => (hw j).le)
        (fun i _ => hb i) h x
    rw [lintegral_congr_ae H, integral_coordinate_product μ univ h hm]
    simp [hu]

end D5.S3.Analytic.Measure.ProperSupportMarginalGluing
