/- GID: D5/S3/Combinatorics/Graph/L1Jung
   generality: G
   mirror-B: none(waiver:covered-by-chordal-banach-exact-strata-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact measurable Jung centers in real L¹ -/

import OmegaBuild.Commands
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

compile_only_with_mathlib

/-!
Omega original.

# Exact measurable Jung centers in real L¹

For every measure space and every m ≥ 1, a family of 2m+1 real L¹ functions of
pairwise distance at most D ≥ 0 has an L¹ center of radius (1-1/(2m))D.
The median is an exact lattice order statistic, so its measurability and L¹
membership are built into its construction. Strict scalar median dominance
integrates to a deletion bound; explicit nonnegative weights give the center.

The finite-set form pads smaller families with repeated observations.
-/

open MeasureTheory
open scoped ENNReal

namespace ChordalL1

/-- The exact pointwise median of three real-valued L¹ functions. -/
noncomputable def median3 {E : Type*} [Lattice E] (a b c : E) : E :=
  (a ⊓ b) ⊔ ((a ⊓ c) ⊔ (b ⊓ c))

lemma real_median3_pair (a b c : ℝ) :
    |a - median3 a b c| + |b - median3 a b c| = |a - b| := by
  change |a - max (min a b) (max (min a c) (min b c))| +
    |b - max (min a b) (max (min a c) (min b c))| = |a-b|
  rcases le_total a b with hab | hba <;>
    rcases le_total a c with hac | hca <;>
    rcases le_total b c with hbc | hcb <;>
    simp [abs_of_nonneg, abs_of_nonpos, *]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

lemma coe_median3 (a b c : Lp ℝ 1 μ) :
    ⇑(median3 a b c) =ᵐ[μ] fun t => median3 (a t) (b t) (c t) := by
  filter_upwards [Lp.coeFn_sup (a ⊓ b) ((a ⊓ c) ⊔ (b ⊓ c)),
    Lp.coeFn_sup (a ⊓ c) (b ⊓ c), Lp.coeFn_inf a b,
    Lp.coeFn_inf a c, Lp.coeFn_inf b c] with t h₀ h₁ h₂ h₃ h₄
  simpa only [median3, Pi.sup_apply, Pi.inf_apply, h₁, h₂, h₃, h₄] using h₀

lemma integrable_dist (a b : Lp ℝ 1 μ) :
    Integrable (fun t => dist (a t) (b t)) μ := by
  simpa only [Real.dist_eq, Pi.sub_apply] using
    ((memLp_one_iff_integrable.mp (Lp.memLp a)).sub
      (memLp_one_iff_integrable.mp (Lp.memLp b))).abs

/-- Real L¹ is a median metric space: the median lies on each pairwise geodesic. -/
theorem median3_dist_pair (a b c : Lp ℝ 1 μ) :
    dist a (median3 a b c) + dist b (median3 a b c) = dist a b := by
  rw [L1.dist_eq_integral_dist, L1.dist_eq_integral_dist,
    L1.dist_eq_integral_dist, ← integral_add (integrable_dist _ _) (integrable_dist _ _)]
  apply integral_congr_ae
  filter_upwards [coe_median3 a b c] with t ht
  simp only [ht, Real.dist_eq]
  exact real_median3_pair _ _ _

/-- A metric tripod in a real normed space has radius at most half its diameter. -/
theorem exists_center_of_tripod {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (x : ι → E) (p : E) {D : ℝ} (hD : 0 ≤ D)
    (hpair : ∀ i j, i ≠ j → dist (x i) p + dist (x j) p ≤ D) :
    ∃ c : E, ∀ i, dist (x i) c ≤ D / 2 := by
  classical
  by_cases h : ∀ i, dist (x i) p ≤ D / 2
  · exact ⟨p, h⟩
  push Not at h
  obtain ⟨i, hi⟩ := h
  let r := dist (x i) p
  have hr : 0 < r := lt_of_le_of_lt (by linarith) hi
  let t : ℝ := (r - D / 2) / r
  have ht0 : 0 ≤ t := div_nonneg (by dsimp [r]; linarith) hr.le
  have ht1 : t ≤ 1 := (div_le_one hr).mpr (by linarith)
  have htr : t * r = r - D / 2 := div_mul_cancel₀ _ hr.ne'
  let c := p + t • (x i - p)
  have hpc : dist p c = t * r := by
    simp [c, r, dist_eq_norm, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht0]
  have hic : dist (x i) c = (1 - t) * r := by
    rw [dist_eq_norm]
    have he : x i - c = (1 - t) • (x i - p) := by dsimp [c]; module
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht1)]
    simp only [r, dist_eq_norm]
  refine ⟨c, fun j => ?_⟩
  by_cases hji : j = i
  · subst j; rw [hic]; nlinarith
  · have hj := hpair j i hji
    have hjc := dist_triangle (x j) p c
    rw [hpc] at hjc
    dsimp only [r] at htr
    dsimp only [r] at hjc
    linarith

/-- The three-point Jung upper bound in an arbitrary real L¹(μ), including D = 0. -/
theorem exists_center_three (x : Fin 3 → Lp ℝ 1 μ) {D : ℝ} (hD : 0 ≤ D)
    (hdiam : ∀ i j, dist (x i) (x j) ≤ D) :
    ∃ c : Lp ℝ 1 μ, ∀ i, dist (x i) c ≤ D / 2 := by
  let p := median3 (x 0) (x 1) (x 2)
  have hp01 : dist (x 0) p + dist (x 1) p = dist (x 0) (x 1) :=
    median3_dist_pair _ _ _
  have hp02 : dist (x 0) p + dist (x 2) p = dist (x 0) (x 2) := by
    have he : median3 (x 0) (x 2) (x 1) = p := by dsimp [p, median3]; ac_rfl
    simpa only [he] using median3_dist_pair (x 0) (x 2) (x 1)
  have hp12 : dist (x 1) p + dist (x 2) p = dist (x 1) (x 2) := by
    have he : median3 (x 1) (x 2) (x 0) = p := by dsimp [p, median3]; ac_rfl
    simpa only [he] using median3_dist_pair (x 1) (x 2) (x 0)
  apply exists_center_of_tripod x p hD
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num at * <;>
    linarith [hdiam 0 1, hdiam 0 2, hdiam 1 2]

/-- Insertion network using lattice operations; no measurable choices are needed. -/
def latticeInsert {E : Type*} [Lattice E] (a : E) : List E → List E
  | [] => [a]
  | b :: l => (a ⊓ b) :: latticeInsert (a ⊔ b) l

def latticeSort {E : Type*} [Lattice E] : List E → List E
  | [] => []
  | a :: l => latticeInsert a (latticeSort l)

@[simp] lemma length_latticeInsert {E : Type*} [Lattice E] (a : E) (l : List E) :
    (latticeInsert a l).length = l.length + 1 := by
  induction l generalizing a <;> simp [latticeInsert, *]

@[simp] lemma length_latticeSort {E : Type*} [Lattice E] (l : List E) :
    (latticeSort l).length = l.length := by
  induction l <;> simp [latticeSort, *]

lemma latticeInsert_perm (a : ℝ) (l : List ℝ) : List.Perm (latticeInsert a l) (a :: l) := by
  induction l generalizing a with
  | nil => exact List.Perm.refl _
  | cons b l ih =>
    rcases le_total a b with h | h
    · simpa [latticeInsert, inf_of_le_left h, sup_of_le_right h] using (ih b).cons a
    · simpa [latticeInsert, inf_of_le_right h, sup_of_le_left h] using
        ((ih a).cons b).trans (List.Perm.swap a b l)

lemma latticeSort_perm (l : List ℝ) : List.Perm (latticeSort l) l := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons a l ih => exact (latticeInsert_perm a _).trans (ih.cons a)

lemma le_latticeInsert (r a : ℝ) (l : List ℝ) (ha : r ≤ a)
    (hl : ∀ b ∈ l, r ≤ b) : ∀ b ∈ latticeInsert a l, r ≤ b := by
  intro b hb
  have hp := (latticeInsert_perm a l).mem_iff.mp hb
  rcases List.mem_cons.mp hp with h | h
  · simpa [h] using ha
  · exact hl _ h

lemma sorted_latticeInsert (a : ℝ) (l : List ℝ) (hl : l.SortedLE) :
    (latticeInsert a l).SortedLE := by
  induction l generalizing a with
  | nil => simpa [latticeInsert, List.sortedLE_cons] using (List.sortedLE_nil : ([] : List ℝ).SortedLE)
  | cons b l ih =>
    rw [List.sortedLE_cons] at hl
    rw [latticeInsert, List.sortedLE_cons]
    refine ⟨?_, ih _ hl.2⟩
    apply le_latticeInsert
    · exact inf_le_left.trans le_sup_left
    · intro c hc
      exact inf_le_right.trans (hl.1 c hc)

lemma sorted_latticeSort (l : List ℝ) : (latticeSort l).SortedLE := by
  induction l with
  | nil => exact List.sortedLE_nil
  | cons a l ih => exact sorted_latticeInsert _ _ ih

noncomputable def median5 {E : Type*} [Lattice E] (x : Fin 5 → E) : E :=
  (latticeSort (List.ofFn x)).get ⟨2, by simp⟩

lemma five_decompose {E : Type*} (l : List E) (h : l.length = 5) :
    ∃ a b c d e, l = [a,b,c,d,e] := by
  rcases l with _ | ⟨a,l⟩ <;> simp at h
  rcases l with _ | ⟨b,l⟩ <;> simp at h
  rcases l with _ | ⟨c,l⟩ <;> simp at h
  rcases l with _ | ⟨d,l⟩ <;> simp at h
  rcases l with _ | ⟨e,l⟩ <;> simp at h
  have hl : l = [] := h
  exact ⟨a,b,c,d,e,by simp [hl]⟩

/-- Strict odd-median dominance, strong enough to delete any one observation. -/
lemma real_median5_cost (x : Fin 5 → ℝ) (q : ℝ) :
    (∑ i, |x i - median5 x|) + |median5 x - q| ≤ ∑ i, |x i - q| := by
  obtain ⟨a,b,c,d,e,he⟩ := five_decompose (latticeSort (List.ofFn x)) (by simp)
  have hs := sorted_latticeSort (List.ofFn x)
  rw [he] at hs
  have horder : a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ e := by
    have hm : Monotone (fun i : Fin 5 => ([a,b,c,d,e] : List ℝ).get i) := hs
    exact ⟨hm (show (0 : Fin 5) ≤ 1 by decide),
      hm (show (1 : Fin 5) ≤ 2 by decide),
      hm (show (2 : Fin 5) ≤ 3 by decide), hm (show (3 : Fin 5) ≤ 4 by decide)⟩
  have hm : median5 x = c := by
    have hh := congrArg (fun l : List ℝ => l[2]?) he
    simpa [median5, List.getElem?_eq_getElem] using hh
  have hsum (r : ℝ) : (∑ i, |x i-r|) = |a-r|+|b-r|+|c-r|+|d-r|+|e-r| := by
    have hh := ((latticeSort_perm (List.ofFn x)).map (fun z => |z-r|)).sum_eq
    rw [he] at hh
    simp only [List.map_ofFn, List.sum_ofFn] at hh
    simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      add_assoc, Function.comp_apply] using hh.symm
  rw [hm, hsum c, hsum q]
  have ha : a ≤ c := horder.1.trans horder.2.1
  have hc : c ≤ e := horder.2.2.1.trans horder.2.2.2
  have h₁ := abs_sub_le a q e
  have h₂ := abs_sub_le b q d
  rw [abs_of_nonpos (sub_nonpos.mpr (ha.trans hc))] at h₁
  rw [abs_of_nonpos (sub_nonpos.mpr (horder.2.1.trans horder.2.2.1))] at h₂
  rw [abs_sub_comm q e] at h₁
  rw [abs_sub_comm q d] at h₂
  rw [abs_of_nonpos (sub_nonpos.mpr ha), abs_of_nonpos (sub_nonpos.mpr horder.2.1),
    sub_self, abs_zero, abs_of_nonneg (sub_nonneg.mpr horder.2.2.1),
    abs_of_nonneg (sub_nonneg.mpr hc)]
  linarith



lemma coe_latticeInsert (a : Lp ℝ 1 μ) (l : List (Lp ℝ 1 μ)) :
    ∀ᵐ t ∂μ, (latticeInsert a l).map (fun f => f t) =
      latticeInsert (a t) (l.map (fun f => f t)) := by
  induction l generalizing a with
  | nil => exact Filter.Eventually.of_forall (fun t => rfl)
  | cons b l ih =>
    filter_upwards [ih (a ⊔ b), Lp.coeFn_inf a b, Lp.coeFn_sup a b] with t ht hi hs
    simp only [latticeInsert, List.map_cons, ht, hi, hs, Pi.inf_apply, Pi.sup_apply]

lemma coe_latticeSort (l : List (Lp ℝ 1 μ)) :
    ∀ᵐ t ∂μ, (latticeSort l).map (fun f => f t) =
      latticeSort (l.map (fun f => f t)) := by
  induction l with
  | nil => exact Filter.Eventually.of_forall (fun t => rfl)
  | cons a l ih =>
    filter_upwards [coe_latticeInsert a (latticeSort l), ih] with t ht hl
    simpa only [latticeSort, List.map_cons, hl] using ht

lemma coe_median5 (x : Fin 5 → Lp ℝ 1 μ) :
    ⇑(median5 x) =ᵐ[μ] fun t => median5 (fun i => x i t) := by
  filter_upwards [coe_latticeSort (List.ofFn x)] with t ht
  have hh := congrArg (fun l : List ℝ => l[2]?) ht
  simp only [List.getElem?_map, List.map_ofFn] at hh
  simpa [median5, List.getElem?_eq_getElem] using hh

/-- Integrated strict dominance for the measurable five-point median. -/
theorem median5_cost (x : Fin 5 → Lp ℝ 1 μ) (q : Lp ℝ 1 μ) :
    (∑ i, dist (x i) (median5 x)) + dist (median5 x) q ≤ ∑ i, dist (x i) q := by
  simp_rw [L1.dist_eq_integral_dist]
  rw [← integral_finsetSum _ (fun i _ => integrable_dist (x i) (median5 x)),
    ← integral_finsetSum _ (fun i _ => integrable_dist (x i) q),
    ← integral_add (integrable_finsetSum _ (fun i _ => integrable_dist (x i) (median5 x)))
      (integrable_dist (median5 x) q)]
  apply integral_mono_ae
    ((integrable_finsetSum _ (fun i _ => integrable_dist (x i) (median5 x))).add
      (integrable_dist (median5 x) q))
    (integrable_finsetSum _ (fun i _ => integrable_dist (x i) q))
  filter_upwards [coe_median5 x] with t ht
  simpa only [Pi.add_apply, ht, Real.dist_eq] using real_median5_cost (fun i => x i t) (q t)


/-- Deleting one observation preserves median minimality in actual L¹. -/
theorem median5_delete_cost (x : Fin 5 → Lp ℝ 1 μ) (j : Fin 5) (q : Lp ℝ 1 μ) :
    ∑ i ∈ Finset.univ.erase j, dist (x i) (median5 x) ≤
      ∑ i ∈ Finset.univ.erase j, dist (x i) q := by
  have h := median5_cost x q
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j),
      ← Finset.sum_erase_add _ _ (Finset.mem_univ j)] at h
  have ht := dist_triangle (x j) (median5 x) q
  linarith

/-- The four largest deviations from the five-point median have sum at most 3D. -/
theorem median5_delete_bound (x : Fin 5 → Lp ℝ 1 μ) {D : ℝ}
    (hdiam : ∀ i j, dist (x i) (x j) ≤ D) (j : Fin 5) :
    ∑ i ∈ Finset.univ.erase j, dist (x i) (median5 x) ≤ 3 * D := by
  let s := Finset.univ.erase j
  have hcard : s.card = 4 := by simp [s]
  have hc (l : Fin 5) (hl : l ∈ s) :
      ∑ i ∈ s, dist (x i) (x l) ≤ 3 * D := by
    have hh (i : Fin 5) : dist (x i) (x l) ≤ if i = l then 0 else D := by
      by_cases hi : i = l
      · simp [hi]
      · simpa only [ite_eq_right hi] using hdiam i l
    calc
      _ ≤ ∑ i ∈ s, (if i = l then 0 else D) := Finset.sum_le_sum (fun i _ => hh i)
      _ = 3 * D := by
        have heq (i : Fin 5) : (if i = l then 0 else D) =
            D - (if i = l then D else 0) := by split_ifs <;> ring
        simp_rw [heq]
        rw [Finset.sum_sub_distrib]
        simp [Finset.sum_ite_eq', hl, hcard]
        ring
  have hsum : 4 * (∑ i ∈ s, dist (x i) (median5 x)) ≤ 4 * (3 * D) := by
    calc
      _ = ∑ l ∈ s, (∑ i ∈ s, dist (x i) (median5 x)) := by simp [hcard]
      _ ≤ ∑ l ∈ s, (∑ i ∈ s, dist (x i) (x l)) :=
        Finset.sum_le_sum (fun l _ => median5_delete_cost x j (x l))
      _ ≤ ∑ l ∈ s, (3 * D) := Finset.sum_le_sum hc
      _ = _ := by simp [hcard]
  dsimp only [s] at hsum
  linarith


/-- Distance to a convex combination, with its own coefficient removed exactly. -/
lemma dist_weighted_center {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype ι] [DecidableEq ι] (x : ι → E) (p : E) (a : ℝ) (b : ι → ℝ)
    (ha : 0 ≤ a) (hb : ∀ i, 0 ≤ b i) (hs : a + ∑ i, b i = 1)
    {D : ℝ} (hdiam : ∀ i j, dist (x i) (x j) ≤ D) (i : ι) :
    dist (x i) (a • p + ∑ j, b j • x j) ≤
      a * dist (x i) p + (1-a-b i) * D := by
  have he : x i - (a • p + ∑ j, b j • x j) =
      a • (x i-p) + ∑ j, b j • (x i-x j) := by
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
    have hb_sum : ∑ j, b j = 1-a := by linarith
    rw [hb_sum, sub_smul, one_smul]
    module
  rw [dist_eq_norm, he]
  calc
    _ ≤ ‖a • (x i-p)‖ + ∑ j, ‖b j • (x i-x j)‖ :=
      (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ = a * dist (x i) p + ∑ j, b j * dist (x i) (x j) := by
      simp_rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha,
        abs_of_nonneg (hb _), ← dist_eq_norm]
    _ ≤ a * dist (x i) p + ∑ j ∈ Finset.univ.erase i, b j * D := by
      apply add_le_add le_rfl
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      simp only [dist_self, mul_zero, add_zero]
      exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hdiam i j) (hb j))
    _ = _ := by
      rw [← Finset.sum_mul]
      have hsum := Finset.sum_erase_add Finset.univ b (Finset.mem_univ i)
      congr 1
      congr 1
      linarith


/-- The explicit five-point weighting step, abstracted from its median construction. -/
theorem exists_center_five_of_sorted_deviations {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (x : Fin 5 → E) (p : E) {D : ℝ} (hD : 0 < D)
    (hdiam : ∀ i j, dist (x i) (x j) ≤ D)
    (hdesc : Antitone (fun i => dist (x i) p))
    (hdev : dist (x 0) p + dist (x 1) p + dist (x 2) p + dist (x 3) p ≤ 3*D) :
    ∃ c : E, ∀ i, dist (x i) c ≤ (3/4 : ℝ)*D := by
  let d := fun i => dist (x i) p
  let r := d 3
  have h₀ : r ≤ d 0 := hdesc (by decide : (0 : Fin 5) ≤ 3)
  have h₁ : r ≤ d 1 := hdesc (by decide : (1 : Fin 5) ≤ 3)
  have h₂ : r ≤ d 2 := hdesc (by decide : (2 : Fin 5) ≤ 3)
  have h₄ : d 4 ≤ r := hdesc (by decide : (3 : Fin 5) ≤ 4)
  have hsmall : r < D := by dsimp [r, d] at *; linarith
  let T := 4*(D-r)
  have hT : 0 < T := by dsimp [T]; linarith
  let a := D/T
  let b : Fin 5 → ℝ := ![(d 0-r)/T, (d 1-r)/T, (d 2-r)/T,
    (3*D-(d 0+d 1+d 2+r))/T, 0]
  have ha : 0 ≤ a := div_nonneg hD.le hT.le
  have hb : ∀ i, 0 ≤ b i := by
    intro i
    fin_cases i <;> norm_num [b]
    · exact div_nonneg (sub_nonneg.mpr h₀) hT.le
    · exact div_nonneg (sub_nonneg.mpr h₁) hT.le
    · exact div_nonneg (sub_nonneg.mpr h₂) hT.le
    · exact div_nonneg (by dsimp [d, r] at *; linarith) hT.le
  have hs : a + ∑ i, b i = 1 := by
    simp only [b, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero]
    dsimp [a, T]
    field_simp
    ring
  have hbase : a*(D-r) = D/4 := by
    dsimp [a, T]
    field_simp
  have himprove (i : Fin 5) : D/4 ≤ a*(D-d i)+b i*D := by
    fin_cases i
    · dsimp [b, a, T]
      field_simp
      ring_nf
      exact le_rfl
    · dsimp [b, a, T]
      field_simp
      ring_nf
      exact le_rfl
    · dsimp [b, a, T]
      field_simp
      ring_nf
      exact le_rfl
    · have hp := mul_nonneg (hb 3) hD.le
      change D/4 ≤ a*(D-r)+b 3*D
      linarith
    · have hp := mul_nonneg ha (sub_nonneg.mpr h₄)
      have hz : b 4 = 0 := rfl
      change D/4 ≤ a*(D-d 4)+b 4*D
      rw [hz, zero_mul]
      nlinarith
  refine ⟨a • p + ∑ j, b j • x j, fun i => ?_⟩
  have hc := dist_weighted_center x p a b ha hb hs hdiam i
  have hi := himprove i
  dsimp only [d] at hi
  nlinarith


/-- The five-point Jung upper bound in arbitrary real L¹(μ), including D = 0. -/
theorem exists_center_five (x : Fin 5 → Lp ℝ 1 μ) {D : ℝ} (hD : 0 ≤ D)
    (hdiam : ∀ i j, dist (x i) (x j) ≤ D) :
    ∃ c : Lp ℝ 1 μ, ∀ i, dist (x i) c ≤ (3/4 : ℝ)*D := by
  classical
  rcases eq_or_lt_of_le hD with hzero | hpos
  · subst D
    exact ⟨x 0, fun i => by simpa using hdiam i 0⟩
  let p := median5 x
  let σ := Tuple.sort (fun i => -dist (x i) p)
  let y : Fin 5 → Lp ℝ 1 μ := fun i => x (σ i)
  have hdesc : Antitone (fun i => dist (y i) p) := by
    intro i j hij
    have hh := Tuple.monotone_sort (fun i => -dist (x i) p) hij
    dsimp only [Function.comp_apply] at hh
    exact neg_le_neg_iff.mp hh
  have hd : ∀ i j, dist (y i) (y j) ≤ D := fun i j => hdiam _ _
  have hdev : dist (y 0) p + dist (y 1) p + dist (y 2) p + dist (y 3) p ≤ 3*D := by
    have hb := median5_delete_bound x hdiam (σ 4)
    have hsum := Equiv.sum_comp σ (fun i => dist (x i) p)
    have he := Finset.sum_erase_add Finset.univ (fun i => dist (x i) p)
      (Finset.mem_univ (σ 4))
    have hy : ∑ i, dist (y i) p = ∑ i, dist (x i) p := hsum
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hy
    change (∑ i ∈ Finset.univ.erase (σ 4), dist (x i) p) ≤ 3*D at hb
    change (∑ i ∈ Finset.univ.erase (σ 4), dist (x i) p) + dist (y 4) p =
      ∑ i, dist (x i) p at he
    have he' : (∑ i ∈ Finset.univ.erase (σ 4), dist (x i) p) + dist (y 4) p =
        ∑ i, dist (y i) p := he.trans hsum.symm
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at he'
    change (∑ i ∈ Finset.univ.erase (σ 4), dist (x i) p) + dist (y 4) p =
      dist (y 0) p + (dist (y 1) p + (dist (y 2) p + (dist (y 3) p + dist (y 4) p))) at he'
    linarith
  obtain ⟨c, hc⟩ := exists_center_five_of_sorted_deviations y p hpos hd hdesc hdev
  refine ⟨c, fun i => ?_⟩
  simpa only [y, Equiv.apply_symm_apply] using hc (σ.symm i)

/-- Exact odd order statistic, constructed inside L¹ by a lattice sorting network. -/
noncomputable def oddMedian {E : Type*} [Lattice E] (m : ℕ)
    (x : Fin (m+(m+1)) → E) : E :=
  (latticeSort (List.ofFn x)).get ⟨m, by simp⟩

lemma sorted_odd_cost (m : ℕ) (y : Fin (m+(m+1)) → ℝ) (hy : Monotone y) (q : ℝ) :
    (∑ i, |y i-y ⟨m, by omega⟩|) + |y ⟨m, by omega⟩-q| ≤ ∑ i, |y i-q| := by
  let c := y ⟨m, by omega⟩
  let a : Fin m → ℝ := fun i => y (i.castAdd (m+1))
  let b : Fin m → ℝ := fun i => y (Fin.natAdd m i.succ)
  have hsplit (f : ℝ → ℝ) : (∑ i, f (y i)) = (∑ i, f (a i)) + f c + ∑ i, f (b i) := by
    rw [Fin.sum_univ_add, Fin.sum_univ_succ]
    change (∑ i, f (a i)) + (f (y (Fin.natAdd m 0)) + ∑ i, f (b i)) =
      (∑ i, f (a i)) + f c + ∑ i, f (b i)
    have hc : y (Fin.natAdd m 0) = c := congrArg y (Fin.ext (by simp))
    rw [hc]
    ring
  have hpair (i : Fin m) : |a i-c|+|b i-c| ≤ |a i-q|+|b i-q| := by
    have ha : a i ≤ c := hy (by change i.val ≤ m; omega)
    have hb : c ≤ b i := hy (by change m ≤ m+i.succ.val; omega)
    have hh := abs_sub_le (a i) q (b i)
    rw [abs_sub_comm q (b i)] at hh
    rw [abs_of_nonpos (sub_nonpos.mpr (ha.trans hb))] at hh
    rw [abs_of_nonpos (sub_nonpos.mpr ha), abs_of_nonneg (sub_nonneg.mpr hb)]
    linarith
  rw [hsplit (fun z => |z-c|), hsplit (fun z => |z-q|)]
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpair i)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hh
  dsimp only [c] at *
  simp only [sub_self, abs_zero] at *
  linarith

lemma real_oddMedian_cost (m : ℕ) (x : Fin (m+(m+1)) → ℝ) (q : ℝ) :
    (∑ i, |x i-oddMedian m x|) + |oddMedian m x-q| ≤ ∑ i, |x i-q| := by
  classical
  let σ := Tuple.sort x
  let y := x ∘ σ
  have hy : Monotone y := Tuple.monotone_sort x
  have he : latticeSort (List.ofFn x) = List.ofFn y :=
    ((latticeSort_perm _).trans (σ.ofFn_comp_perm x).symm).eq_of_sortedLE
      (sorted_latticeSort _) hy.sortedLE_ofFn
  have hm : oddMedian m x = y ⟨m, by omega⟩ := by
    have hh := congrArg (fun l : List ℝ => l[m]?) he
    have hx : m < (latticeSort (List.ofFn x)).length := by simp
    have hy' : m < (List.ofFn y).length := by simp
    rw [List.getElem?_eq_getElem hx, List.getElem?_eq_getElem hy'] at hh
    simpa only [oddMedian, List.get_eq_getElem, List.getElem_ofFn] using Option.some.inj hh
  have hsum (r : ℝ) : (∑ i, |y i-r|) = ∑ i, |x i-r| :=
    Equiv.sum_comp σ (fun i => |x i-r|)
  have hh := sorted_odd_cost m y hy q
  rw [hsum, hsum, ← hm] at hh
  exact hh

lemma coe_oddMedian (m : ℕ) (x : Fin (m+(m+1)) → Lp ℝ 1 μ) :
    ⇑(oddMedian m x) =ᵐ[μ] fun t => oddMedian m (fun i => x i t) := by
  filter_upwards [coe_latticeSort (List.ofFn x)] with t ht
  have hh := congrArg (fun l : List ℝ => l[m]?) ht
  simp only [List.getElem?_map, List.map_ofFn] at hh
  simpa [oddMedian, List.getElem?_eq_getElem] using hh

/-- Strict median dominance for every odd number of arbitrary real L¹ functions. -/
theorem oddMedian_cost (m : ℕ) (x : Fin (m+(m+1)) → Lp ℝ 1 μ) (q : Lp ℝ 1 μ) :
    (∑ i, dist (x i) (oddMedian m x)) + dist (oddMedian m x) q ≤ ∑ i, dist (x i) q := by
  simp_rw [L1.dist_eq_integral_dist]
  rw [← integral_finsetSum _ (fun i _ => integrable_dist (x i) (oddMedian m x)),
    ← integral_finsetSum _ (fun i _ => integrable_dist (x i) q),
    ← integral_add (integrable_finsetSum _ (fun i _ => integrable_dist (x i) (oddMedian m x)))
      (integrable_dist (oddMedian m x) q)]
  apply integral_mono_ae
    ((integrable_finsetSum _ (fun i _ => integrable_dist (x i) (oddMedian m x))).add
      (integrable_dist (oddMedian m x) q))
    (integrable_finsetSum _ (fun i _ => integrable_dist (x i) q))
  filter_upwards [coe_oddMedian m x] with t ht
  simpa only [Pi.add_apply, ht, Real.dist_eq] using real_oddMedian_cost m (fun i => x i t) (q t)


/-- General explicit weighting step. There are n+2 points and n+1 retained deviations. -/
theorem exists_center_of_sorted_deviations {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (n : ℕ) (x : Fin (n+2) → E) (p : E) {D : ℝ} (hD : 0 < D)
    (hdiam : ∀ i j, dist (x i) (x j) ≤ D)
    (hdesc : Antitone (fun i => dist (x i) p))
    (hdev : (∑ i : Fin (n+1), dist (x i.castSucc) p) ≤ (n:ℝ)*D) :
    ∃ c : E, ∀ i, dist (x i) c ≤ (1-1/((n:ℝ)+1))*D := by
  classical
  let d := fun i => dist (x i) p
  let j : Fin (n+2) := ⟨n, by omega⟩
  let l : Fin (n+2) := Fin.last (n+1)
  let r := d j
  let N : ℝ := (n:ℝ)+1
  let S := ∑ i : Fin (n+1), d i.castSucc
  have hN : 0 < N := by dsimp [N]; positivity
  have hSr : N*r ≤ S := by
    calc
      _ = ∑ i : Fin (n+1), r := by simp [N, Nat.cast_add, Nat.cast_one]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => hdesc (by
        change i.val ≤ n
        omega))
  have hsmall : r < D := by
    by_contra hh
    have hh' : D ≤ r := le_of_not_gt hh
    have hh'' := mul_le_mul_of_nonneg_left hh' hN.le
    dsimp only [N,S,d] at *
    nlinarith
  let T := N*(D-r)
  have hT : 0 < T := mul_pos hN (sub_pos.mpr hsmall)
  let a := D/T
  let slack := (n:ℝ)*D-S
  have hslack : 0 ≤ slack := sub_nonneg.mpr hdev
  have ha : 0 ≤ a := div_nonneg hD.le hT.le
  let u : Fin (n+2) → ℝ := fun i => if i=l then 0 else (d i-r)/T
  let v : Fin (n+2) → ℝ := fun i => if i=j then slack/T else 0
  let b := fun i => u i+v i
  have hu0 (i : Fin (n+2)) : 0 ≤ u i := by
    dsimp [u]
    split_ifs with hi
    · exact le_rfl
    · apply div_nonneg _ hT.le
      apply sub_nonneg.mpr
      apply hdesc
      change i.val ≤ n
      have hil : i.val ≠ n+1 := by
        intro he
        apply hi
        apply Fin.ext
        simpa [l] using he
      omega
  have hv0 (i : Fin (n+2)) : 0 ≤ v i := by
    dsimp [v]
    split_ifs
    · exact div_nonneg hslack hT.le
    · exact le_rfl
  have hb (i : Fin (n+2)) : 0 ≤ b i := add_nonneg (hu0 i) (hv0 i)
  have hu : (∑ i, u i) = (S-N*r)/T := by
    rw [Fin.sum_univ_castSucc]
    simp only [u, l, Fin.castSucc_ne_last, ite_false, ite_true, add_zero]
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    simp [S,N, Nat.cast_add, Nat.cast_one]
  have hv : (∑ i, v i) = slack/T := by simp [v]
  have hs : a+∑ i, b i = 1 := by
    simp only [b, Finset.sum_add_distrib, hu, hv]
    dsimp [a,slack,T,N]
    field_simp
    ring
  have hbase : a*(D-r) = D/N := by
    dsimp [a,T]
    field_simp
  have himprove (i : Fin (n+2)) : D/N ≤ a*(D-d i)+b i*D := by
    by_cases hil : i=l
    · subst i
      have hrl : d l ≤ r := hdesc (by change n ≤ n+1; omega)
      have hh := mul_nonneg ha (sub_nonneg.mpr hrl)
      have hh' := mul_nonneg (hb l) hD.le
      nlinarith
    · have he : a*(D-d i)+u i*D = D/N := by
        simp only [u, ite_eq_right hil]
        dsimp [a,T]
        field_simp
        ring
      have hh := mul_nonneg (hv0 i) hD.le
      dsimp only [b]
      nlinarith
  refine ⟨a • p + ∑ i, b i • x i, fun i => ?_⟩
  have hc := dist_weighted_center x p a b ha hb hs hdiam i
  have hi := himprove i
  dsimp only [d] at hi
  change dist (x i) (a • p + ∑ j, b j • x j) ≤ (1-1/N)*D
  have hdiv : D/N = (1/N)*D := by ring
  rw [hdiv] at hi
  nlinarith


/-- Median dominance gives a sharp sum bound after deletion, in any finite family. -/
lemma delete_bound_of_strict_cost {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (x : Fin (n+2) → E) (p : E)
    (hcost : ∀ q, (∑ i, dist (x i) p)+dist p q ≤ ∑ i, dist (x i) q)
    {D : ℝ} (hdiam : ∀ i j, dist (x i) (x j) ≤ D) (j : Fin (n+2)) :
    ∑ i ∈ Finset.univ.erase j, dist (x i) p ≤ (n:ℝ)*D := by
  classical
  let s := Finset.univ.erase j
  have hcard : s.card = n+1 := by simp [s]
  have hdelete (q : E) : (∑ i ∈ s, dist (x i) p) ≤ ∑ i ∈ s, dist (x i) q := by
    have h := hcost q
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j),
      ← Finset.sum_erase_add _ _ (Finset.mem_univ j)] at h
    have ht := dist_triangle (x j) p q
    dsimp only [s]
    linarith
  have hc (l : Fin (n+2)) (hl : l ∈ s) : (∑ i ∈ s, dist (x i) (x l)) ≤ (n:ℝ)*D := by
    have hh (i : Fin (n+2)) : dist (x i) (x l) ≤ if i=l then 0 else D := by
      by_cases hi : i=l
      · simp [hi]
      · simpa only [ite_eq_right hi] using hdiam i l
    calc
      _ ≤ ∑ i ∈ s, (if i=l then 0 else D) := Finset.sum_le_sum (fun i _ => hh i)
      _ = _ := by
        have heq (i : Fin (n+2)) : (if i=l then 0 else D) =
            D-(if i=l then D else 0) := by split_ifs <;> ring
        simp_rw [heq]
        rw [Finset.sum_sub_distrib]
        simp [hl,hcard,Nat.cast_add,Nat.cast_one]
        ring
  have hsum : ((n:ℝ)+1)*(∑ i ∈ s, dist (x i) p) ≤ ((n:ℝ)+1)*((n:ℝ)*D) := by
    calc
      _ = ∑ l ∈ s, (∑ i ∈ s, dist (x i) p) := by simp [hcard,Nat.cast_add,Nat.cast_one]
      _ ≤ ∑ l ∈ s, (∑ i ∈ s, dist (x i) (x l)) := Finset.sum_le_sum (fun l _ => hdelete (x l))
      _ ≤ ∑ l ∈ s, ((n:ℝ)*D) := Finset.sum_le_sum hc
      _ = _ := by simp [hcard,Nat.cast_add,Nat.cast_one]
  exact (mul_le_mul_iff_of_pos_left (by positivity : 0 < (n:ℝ)+1)).mp hsum

/-- The source's explicit Jung weighting construction from the strict median property. -/
theorem exists_center_of_strict_median {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (x : Fin (n+2) → E) (p : E)
    (hcost : ∀ q, (∑ i, dist (x i) p)+dist p q ≤ ∑ i, dist (x i) q)
    {D : ℝ} (hD : 0 ≤ D) (hdiam : ∀ i j, dist (x i) (x j) ≤ D) :
    ∃ c : E, ∀ i, dist (x i) c ≤ (1-1/((n:ℝ)+1))*D := by
  classical
  rcases eq_or_lt_of_le hD with hzero | hpos
  · subst D
    exact ⟨x 0, fun i => by simpa using hdiam i 0⟩
  let σ := Tuple.sort (fun i => -dist (x i) p)
  let y : Fin (n+2) → E := fun i => x (σ i)
  have hdesc : Antitone (fun i => dist (y i) p) := by
    intro i j hij
    have hh := Tuple.monotone_sort (fun i => -dist (x i) p) hij
    dsimp only [Function.comp_apply] at hh
    exact neg_le_neg_iff.mp hh
  have hd : ∀ i j, dist (y i) (y j) ≤ D := fun i j => hdiam _ _
  have hdev : (∑ i : Fin (n+1), dist (y i.castSucc) p) ≤ (n:ℝ)*D := by
    have hb := delete_bound_of_strict_cost n x p hcost hdiam (σ (Fin.last (n+1)))
    have hsum := Equiv.sum_comp σ (fun i => dist (x i) p)
    have he := Finset.sum_erase_add Finset.univ (fun i => dist (x i) p)
      (Finset.mem_univ (σ (Fin.last (n+1))))
    have he' : (∑ i ∈ Finset.univ.erase (σ (Fin.last (n+1))), dist (x i) p) +
        dist (y (Fin.last (n+1))) p = ∑ i, dist (y i) p := he.trans hsum.symm
    rw [Fin.sum_univ_castSucc] at he'
    linarith
  obtain ⟨c,hc⟩ := exists_center_of_sorted_deviations n y p hpos hd hdesc hdev
  refine ⟨c,fun i => ?_⟩
  simpa only [y,Equiv.apply_symm_apply] using hc (σ.symm i)


/-- General odd-cardinality Jung bound in arbitrary L¹ of real-valued functions. -/
theorem exists_center_odd_sum (m : ℕ) (hm : 1 ≤ m)
    (x : Fin (m+(m+1)) → Lp ℝ 1 μ) {D : ℝ} (hD : 0 ≤ D)
    (hdiam : ∀ i j, dist (x i) (x j) ≤ D) :
    ∃ c : Lp ℝ 1 μ, ∀ i, dist (x i) c ≤ (1-1/(2*(m:ℝ)))*D := by
  classical
  let n := 2*m-1
  have hn : n+1 = 2*m := by dsimp [n]; omega
  have hN : (n:ℝ)+1 = 2*(m:ℝ) := by exact_mod_cast hn
  let e : Fin (n+2) ≃ Fin (m+(m+1)) := finCongr (by dsimp [n]; omega)
  let y := x ∘ e
  let p := oddMedian m x
  have hcost (q : Lp ℝ 1 μ) : (∑ i, dist (y i) p)+dist p q ≤ ∑ i, dist (y i) q := by
    have hl := Equiv.sum_comp e (fun i => dist (x i) p)
    have hr := Equiv.sum_comp e (fun i => dist (x i) q)
    change (∑ i, dist (x (e i)) p)+dist p q ≤ ∑ i, dist (x (e i)) q
    rw [hl,hr]
    exact oddMedian_cost m x q
  obtain ⟨c,hc⟩ := exists_center_of_strict_median n y p hcost hD (fun i j => hdiam _ _)
  refine ⟨c,fun i => ?_⟩
  simpa only [y,Function.comp_apply,Equiv.apply_symm_apply,hN] using hc (e.symm i)

/-- Standard 2m+1 indexing for the full odd L¹ Jung upper bound. -/
theorem exists_center_odd (m : ℕ) (hm : 1 ≤ m)
    (x : Fin (2*m+1) → Lp ℝ 1 μ) {D : ℝ} (hD : 0 ≤ D)
    (hdiam : ∀ i j, dist (x i) (x j) ≤ D) :
    ∃ c : Lp ℝ 1 μ, ∀ i, dist (x i) c ≤ (1-1/(2*(m:ℝ)))*D := by
  let e : Fin (m+(m+1)) ≃ Fin (2*m+1) := finCongr (by omega)
  let y := x ∘ e
  obtain ⟨c,hc⟩ := exists_center_odd_sum m hm y hD (fun i j => hdiam _ _)
  refine ⟨c,fun i => ?_⟩
  simpa only [y,Function.comp_apply,Equiv.apply_symm_apply] using hc (e.symm i)


/-- The finite-set interface for chordal extension: pad smaller families by duplicates. -/
theorem exists_center_finset_odd {ι : Type*} (m : ℕ) (hm : 1 ≤ m)
    (s : Finset ι) (p : ι → Lp ℝ 1 μ) {D : ℝ} (hD : 0 ≤ D)
    (hcard : s.card ≤ 2*m+1)
    (hdiam : ∀ i ∈ s, ∀ j ∈ s, ‖p i-p j‖ ≤ D) :
    ∃ c : Lp ℝ 1 μ, ∀ i ∈ s, ‖p i-c‖ ≤ (1-1/(2*(m:ℝ)))*D := by
  classical
  by_cases hs : s.Nonempty
  · let e := s.equivFin
    let f : Fin (2*m+1) → ι := fun i =>
      if hi : i.val < s.card then (e.symm ⟨i.val,hi⟩).val else hs.choose
    have hf (i : Fin (2*m+1)) : f i ∈ s := by
      dsimp only [f]
      split_ifs
      · exact (e.symm _).property
      · exact hs.choose_spec
    have hcover (i : ι) (hi : i ∈ s) : ∃ j : Fin (2*m+1), f j=i := by
      let z := e ⟨i,hi⟩
      have hz : z.val < 2*m+1 := lt_of_lt_of_le z.isLt hcard
      refine ⟨⟨z.val,hz⟩,?_⟩
      change (if h : z.val < s.card then (e.symm ⟨z.val,h⟩).val else hs.choose)=i
      rw [dite_eq_left z.isLt]
      exact congrArg Subtype.val (e.symm_apply_apply ⟨i,hi⟩)
    obtain ⟨c,hc⟩ := exists_center_odd m hm (fun i => p (f i)) hD (fun i j => by
      simpa only [dist_eq_norm] using hdiam (f i) (hf i) (f j) (hf j))
    refine ⟨c,fun i hi => ?_⟩
    obtain ⟨j,hj⟩ := hcover i hi
    simpa only [hj,dist_eq_norm] using hc j
  · refine ⟨0,fun i hi => ?_⟩
    exact (hs ⟨i,hi⟩).elim

end ChordalL1
