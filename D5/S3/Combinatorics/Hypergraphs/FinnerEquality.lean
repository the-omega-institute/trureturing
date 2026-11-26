/- GID: D5/S3/Combinatorics/Hypergraphs/FinnerEquality
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Hypergraphs/FinnerEquality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Common coordinate profiles for balanced Finner saturation. -/

module

public import D5.S3.Combinatorics.Hypergraphs.FinnerProductMeasure
public import D5.S3.Analytic.Measure.NormalizedHolderEquality
import D5.S3.Analytic.Measure.ProductSupportIntersection

/-! # Balanced Finner equality and canonical coordinate marginals -/

@[expose] public section

open MeasureTheory Function Finset Filter
open scoped ENNReal BigOperators Classical

noncomputable section
set_option autoImplicit false

namespace D5.S3.Combinatorics.Hypergraphs.FinnerEquality

variable {I : Type*} [Fintype I] {X : I → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, MeasureTheory.Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]

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

private lemma marginal_idem [DecidableEq I] (u : Finset I)
    (f : (∀ i, X i) → ℝ≥0∞) :
    lmarginal μ u (lmarginal μ u f) = lmarginal μ u f := by
  apply marginal_fixed
  · intro x y hxy
    exact lmarginal_congr μ f hxy
  · exact disjoint_compl_left

private lemma integral_marginal [DecidableEq I] (u : Finset I)
    {f : (∀ i, X i) → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, lmarginal μ u f x ∂MeasureTheory.Measure.pi μ) =
      ∫⁻ x, f x ∂MeasureTheory.Measure.pi μ :=
  lintegral_eq_of_lmarginal_eq u (hf.lmarginal μ) hf (marginal_idem μ u f)

private lemma marginal_absorb_singleton [DecidableEq I] (u : Finset I)
    {f : (∀ i, X i) → ℝ≥0∞} (hf : Measurable f) {k : I} (hk : k ∈ u) :
    lmarginal μ u (lmarginal μ {k} f) = lmarginal μ u f := by
  conv_lhs => rw [← insert_erase hk,
    lmarginal_insert' _ (hf.lmarginal μ) (notMem_erase k u)]
  conv_rhs => rw [← insert_erase hk, lmarginal_insert' _ hf (notMem_erase k u)]
  change lmarginal μ (u.erase k) (lmarginal μ {k} (lmarginal μ {k} f)) =
    lmarginal μ (u.erase k) (lmarginal μ {k} f)
  rw [marginal_idem]

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
    simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft,
      Function.comp_def, Equiv.piCongrLeft_apply_apply]
    exact FinnerProductMeasure.lintegral_fin_prod (fun i => μ (e i))
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
    rw [prod_coe_sort]
    apply prod_congr rfl
    intro i hiu
    simp only [u] at hiu
    simp [updateFinset, hiu]
  change (∫⁻ y : ∀ i : u, X i, ∏ i, g i (updateFinset x u y i)
    ∂MeasureTheory.Measure.pi (fun i : u => μ i)) = _
  simp_rw [he]
  rw [lintegral_const_mul _ (Finset.measurable_fun_prod _
    (fun i _ => (gm i).comp (measurable_pi_apply i)))]
  have hi' : (∫⁻ y : ∀ i : u, X i, ∏ i : u, g i (y i)
      ∂MeasureTheory.Measure.pi (fun i : u => μ i)) = 1 := by
    rw [integral_coordinate_product (fun i : u => μ i) univ
      (fun i : u => g i) (fun i => gm i)]
    simp [gi]
  rw [hi', mul_one]
  rfl

private lemma profile_integral [DecidableEq I]
    {f : (∀ i, X i) → ℝ≥0∞} (hf : Measurable f)
    (hi : ∫⁻ x, f x ∂MeasureTheory.Measure.pi μ = 1)
    (a : ∀ i, X i) (i : I) :
    (∫⁻ t, lmarginal μ (univ.erase i) f (update a i t) ∂μ i) = 1 := by
  rw [← lmarginal_insert _ hf (notMem_erase i univ), insert_erase (mem_univ i)]
  simpa using hi

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
  simpa only [marginal_coordinate_product μ S h hm hi k, if_pos hk] using H

private lemma proper_assembly [DecidableEq I] {J : Type*} [Fintype J]
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
    split_ifs <;> fun_prop
  have hu (i : I) : ∫⁻ t, h i t ∂μ i = 1 := by
    dsimp [h]
    split_ifs with his
    · exact profile_integral μ (hf _) (hi _) a i
    · simp
  refine ⟨h, hm, hu, ?_⟩
  intro j
  have hn : ∃ k ∈ s, k ∉ S j := by
    by_contra H
    push_neg at H
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
    rw [dif_pos his, profile_evaluation]
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
theorem exists_common_profiles_of_deleted_marginal_factorizations [DecidableEq I]
    {J : Type*} [Fintype J] (s : Finset I) (S : J → Finset I)
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
  simpa only [q, ← mul_assoc, ENNReal.mul_inv_cancel (hpos j).ne' (hfin j), one_mul]
    using hh

end D5.S3.Combinatorics.Hypergraphs.FinnerEquality
