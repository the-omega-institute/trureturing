/- GID: D5/S3/Combinatorics/Hypergraphs/FinnerProductMeasure
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Hypergraphs/FinnerProductMeasure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finner's fractional hypergraph inequality on product probability spaces. -/

module

public import OmegaBuild.Commands
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Marginal
public import Mathlib.Logic.Function.DependsOn
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

compile_only_with_mathlib

/-! # Fractional hypergraph Finner inequality for a common product probability law -/

@[expose] public section

open MeasureTheory Finset Function
open scoped BigOperators ENNReal Classical

noncomputable section
set_option autoImplicit false

namespace D5.S3.Combinatorics.Hypergraphs.FinnerProductMeasure

set_option backward.isDefEq.respectTransparency false in
lemma lintegral_fin_prod {n : ℕ} {E : Fin n → Type*} {mE : ∀ i, MeasurableSpace (E i)} (μ : (i : Fin n) → Measure (E i)) [∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = ∫⁻ x : E 0 × ((i : Fin n) → E (Fin.succ i)), f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i) ∂((μ 0).prod (Measure.pi (fun i => μ i.succ))) :=
        by
        rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]; simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ, Fin.zero_succAbove, cast_eq, Fin.cons_zero]
      _ = (∫⁻ x, f 0 x ∂μ 0) * ∏ i : Fin n, ∫⁻ x, f (Fin.succ i) x ∂μ i.succ := by
        rw [lintegral_prod_mul (μ := μ 0) (ν := Measure.pi (fun i : Fin n => μ i.succ)) (f := f 0) (g := fun (x : (i : Fin n) → E i.succ) => ∏ i : Fin n, f i.succ (x i)) (hf 0).aemeasurable
            (by exact (Finset.measurable_prod _ (fun i _ => (hf i.succ).comp (measurable_pi_apply i))).aemeasurable),
          ih _ _ (fun i => hf i.succ)]
      _ = _ := by exact Eq.symm (Fin.prod_univ_succAbove (fun i => ∫⁻ (x : E i), f i x ∂μ i) 0)

private lemma probability_holder {A J : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν] (t : Finset J)
    (h : J → A → ℝ≥0∞) (w : J → ℝ)
    (hm : ∀ j ∈ t, Measurable (h j)) (hw : ∀ j ∈ t, 0 ≤ w j)
    (hb : ∑ j ∈ t, w j ≤ 1) :
    (∫⁻ a, ∏ j ∈ t, h j a ^ w j ∂ν) ≤
      ∏ j ∈ t, (∫⁻ a, h j a ∂ν) ^ w j := by
  have H := ENNReal.lintegral_mul_prod_norm_pow_le (μ := ν) t
    (g := fun _ => 1) aemeasurable_const (fun j hj => (hm j hj).aemeasurable)
    (1 - ∑ j ∈ t, w j) (sub_add_cancel _ _) (sub_nonneg.mpr hb) hw
  simpa only [ENNReal.one_rpow, one_mul, lintegral_const, measure_univ, mul_one] using H

private lemma holder_with_constants {A J : Type*} [MeasurableSpace A] [Fintype J]
    (ν : Measure A) [IsProbabilityMeasure ν] (t : Finset J)
    (h : J → A → ℝ≥0∞) (c : J → ℝ≥0∞) (w : J → ℝ)
    (hm : ∀ j, Measurable (h j)) (hw : ∀ j, 0 ≤ w j)
    (hb : ∑ j ∈ t, w j ≤ 1)
    (hc : ∀ j ∉ t, ∀ a, h j a = c j) :
    (∫⁻ a, ∏ j, h j a ^ w j ∂ν) ≤
      ∏ j, (∫⁻ a, h j a ∂ν) ^ w j := by
  classical
  have hs (a : A) : (∏ j, h j a ^ w j) =
      (∏ j ∈ t, h j a ^ w j) * ∏ j ∈ tᶜ, c j ^ w j := by
    rw [← prod_mul_prod_compl t]
    congr 1
    exact prod_congr rfl fun j hj => congrArg (fun z : ℝ≥0∞ => z ^ w j)
      (hc j (mem_compl.mp hj) a)
  have hi (j : J) (hj : j ∈ tᶜ) : (∫⁻ a, h j a ∂ν) = c j := by
    simp_rw [hc j (mem_compl.mp hj)]
    simp
  calc
    (∫⁻ a, ∏ j, h j a ^ w j ∂ν) =
        (∫⁻ a, ∏ j ∈ t, h j a ^ w j ∂ν) * ∏ j ∈ tᶜ, c j ^ w j := by
      simp_rw [hs]
      exact lintegral_mul_const _ (t.measurable_fun_prod fun j _ => (hm j).pow_const _)
    _ ≤ (∏ j ∈ t, (∫⁻ a, h j a ∂ν) ^ w j) * ∏ j ∈ tᶜ, c j ^ w j :=
      mul_le_mul_left (probability_holder ν t h w (fun j _ => hm j)
        (fun j _ => hw j) hb) _
    _ = ∏ j, (∫⁻ a, h j a ∂ν) ^ w j := by
      rw [← prod_mul_prod_compl t]
      congr 1
      exact prod_congr rfl fun j hj => congrArg (fun z : ℝ≥0∞ => z ^ w j) (hi j hj).symm

private lemma marginal_update {I : Type*} [DecidableEq I] {X : I → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (μ i)] (s : Finset I)
    {f : (∀ i, X i) → ℝ≥0∞} (hf : Measurable f) {S : Set I}
    (hd : DependsOn f S) {i : I} (hi : i ∉ S) (x : ∀ i, X i) (y : X i) :
    lmarginal μ s f (update x i y) = lmarginal μ s f x := by
  by_cases his : i ∈ s
  · exact lmarginal_update_of_mem μ his f x y
  · rw [lmarginal_update_of_notMem hf his]
    have he : (f ∘ (update · i y)) = f := by
      funext z
      apply hd
      intro k hk
      exact update_of_ne (ne_of_mem_of_not_mem hk hi) y z
    rw [he]

lemma marginal_estimate {I J : Type*} [DecidableEq I] [Fintype J]
    {X : I → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (S : J → Set I) (f : J → (∀ i, X i) → ℝ≥0∞) (w : J → ℝ)
    (hf : ∀ j, Measurable (f j)) (hd : ∀ j, DependsOn (f j) (S j))
    (hw : ∀ j, 0 ≤ w j)
    (hb : ∀ i, ∑ j ∈ Finset.univ.filter (fun j => i ∈ S j), w j ≤ 1)
    (s : Finset I) :
    lmarginal μ s (fun x => ∏ j, f j x ^ w j) ≤
      fun x => ∏ j, lmarginal μ s (f j) x ^ w j := by
  classical
  have hF : Measurable (fun x => ∏ j, f j x ^ w j) :=
    Finset.measurable_fun_prod _ (fun j _ => (hf j).pow_const _)
  induction s using Finset.induction with
  | empty => simp
  | @insert i s his ih =>
    intro x
    rw [lmarginal_insert _ hF his x]
    calc
      (∫⁻ y, lmarginal μ s (fun z => ∏ j, f j z ^ w j) (update x i y) ∂μ i) ≤
          ∫⁻ y, ∏ j, lmarginal μ s (f j) (update x i y) ^ w j ∂μ i :=
        lintegral_mono fun y => ih (update x i y)
      _ ≤ ∏ j, (∫⁻ y, lmarginal μ s (f j) (update x i y) ∂μ i) ^ w j := by
        apply holder_with_constants (μ i) (Finset.univ.filter (fun j => i ∈ S j))
          (fun j y => lmarginal μ s (f j) (update x i y))
          (fun j => lmarginal μ s (f j) x) w
        · exact fun j => ((hf j).lmarginal μ).comp (measurable_update x)
        · exact hw
        · exact hb i
        · intro j hj y
          apply marginal_update μ s (hf j) (hd j)
          simpa using hj
      _ = ∏ j, lmarginal μ (insert i s) (f j) x ^ w j := by
        congr 1
        funext j
        rw [lmarginal_insert _ (hf j) his x]

/-- Finner's inequality for measurable coordinate-supported ENNReal factors on a
finite product of probability spaces, with nonnegative real incidence weights. -/
theorem finner_product_measure {I J : Type*} [Fintype I] [Fintype J]
    {X : I → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (S : J → Set I) (f : J → (∀ i, X i) → ℝ≥0∞) (w : J → ℝ)
    (hf : ∀ j, Measurable (f j)) (hd : ∀ j, DependsOn (f j) (S j))
    (hw : ∀ j, 0 ≤ w j)
    (hb : ∀ i, ∑ j ∈ Finset.univ.filter (fun j => i ∈ S j), w j ≤ 1) :
    (∫⁻ x, ∏ j, f j x ^ w j ∂Measure.pi μ) ≤
      ∏ j, (∫⁻ x, f j x ∂Measure.pi μ) ^ w j := by
  classical
  let x : ∀ i, X i := fun i => Classical.choice (nonempty_of_isProbabilityMeasure (μ i))
  simpa only [lmarginal_univ] using marginal_estimate μ S f w hf hd hw hb univ x

end D5.S3.Combinatorics.Hypergraphs.FinnerProductMeasure
