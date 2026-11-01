/- GID: D5/S3/Analytic/Interpolation/SeparatedJumpRectangles
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/SeparatedJumpRectangles
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Disjoint rectangles capture the square energy of every separated complex jump. -/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace D5.S3.Analytic.Interpolation.SeparatedJumpRectangles

variable {ι : Type*} [Fintype ι]

/-- The finite prefix, without any hypothesis on the total mass. -/
def prefix (x : ι → ℝ) (c : ι → ℂ) (u : ℝ) : ℂ :=
  ∑ i, if x i ≤ u then c i else 0

/-- A half-open neighborhood divided into equal halves by its jump. -/
def nodeWindow (x : ι → ℝ) (g : ℝ) (i : ι) : Set ℝ :=
  Ico (x i - g / 4) (x i + g / 4)

/-- The interval of earlier prefix observations paired with a jump neighborhood. -/
def baseWindow (x : ι → ℝ) (a : ℝ) (i : ι) : Set ℝ :=
  Icc (x i - 7 * a / 4) (x i - 5 * a / 4)

theorem measurable_prefix (x : ι → ℝ) (c : ι → ℂ) : Measurable (prefix x c) := by
  classical
  unfold prefix
  apply Finset.measurable_sum
  intro i _
  simpa only [Set.indicator, mem_Ici] using
    (measurable_const : Measurable (fun _ : ℝ => c i)).indicator measurableSet_Ici

theorem norm_prefix_le (x : ι → ℝ) (c : ι → ℂ) (u : ℝ) :
    ‖prefix x c u‖ ≤ ∑ i, ‖c i‖ := by
  classical
  unfold prefix
  calc
    ‖∑ i, if x i ≤ u then c i else 0‖ ≤ ∑ i, ‖if x i ≤ u then c i else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, ‖c i‖ := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs <;> simp

private def otherPrefix (x : ι → ℝ) (c : ι → ℂ) (i : ι) : ℂ := by
  classical
  exact ∑ j ∈ Finset.univ.erase i, if x j ≤ x i then c j else 0

private theorem node_comparison (x : ι → ℝ) {g : ℝ} (hg : 0 < g)
    (hsep : ∀ i j, i ≠ j → g ≤ |x i - x j|)
    (i j : ι) (hji : j ≠ i) {u : ℝ} (hu : u ∈ nodeWindow x g i) :
    x j ≤ u ↔ x j ≤ x i := by
  have hs := hsep j i hji
  change x i - g / 4 ≤ u ∧ u < x i + g / 4 at hu
  constructor
  · intro hju
    by_contra hji'
    have hlt : x i < x j := lt_of_not_ge hji'
    rw [abs_of_pos (sub_pos.mpr hlt)] at hs
    linarith [hu.2]
  · intro hji'
    rw [abs_of_nonpos (sub_nonpos.mpr hji')] at hs
    linarith [hu.1]

private theorem prefix_on_window (x : ι → ℝ) (c : ι → ℂ) {g : ℝ}
    (hg : 0 < g) (hsep : ∀ i j, i ≠ j → g ≤ |x i - x j|)
    (i : ι) {u : ℝ} (hu : u ∈ nodeWindow x g i) :
    prefix x c u = otherPrefix x c i + if x i ≤ u then c i else 0 := by
  classical
  calc
    prefix x c u = (∑ j ∈ Finset.univ.erase i, if x j ≤ u then c j else 0) +
        (if x i ≤ u then c i else 0) :=
      (Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i)).symm
    _ = otherPrefix x c i + if x i ≤ u then c i else 0 := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [node_comparison x hg hsep i j (Finset.mem_erase.mp hj).1 hu]

private theorem prefix_on_left (x : ι → ℝ) (c : ι → ℂ) {g : ℝ}
    (hg : 0 < g) (hsep : ∀ i j, i ≠ j → g ≤ |x i - x j|)
    (i : ι) {u : ℝ} (hu : u ∈ Ico (x i - g / 4) (x i)) :
    prefix x c u = otherPrefix x c i := by
  have hu' : u ∈ nodeWindow x g i := ⟨hu.1, by linarith [hu.2]⟩
  rw [prefix_on_window x c hg hsep i hu', if_neg (not_le.mpr hu.2), add_zero]

private theorem prefix_on_right (x : ι → ℝ) (c : ι → ℂ) {g : ℝ}
    (hg : 0 < g) (hsep : ∀ i j, i ≠ j → g ≤ |x i - x j|)
    (i : ι) {u : ℝ} (hu : u ∈ Ico (x i) (x i + g / 4)) :
    prefix x c u = otherPrefix x c i + c i := by
  have hu' : u ∈ nodeWindow x g i := ⟨by linarith [hu.1], hu.2⟩
  rw [prefix_on_window x c hg hsep i hu', if_pos hu.1]

private theorem two_point_square (A z : ℂ) :
    Complex.normSq z / 2 ≤ Complex.normSq A + Complex.normSq (A + z) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
  nlinarith [sq_nonneg (2 * A.re + z.re), sq_nonneg (2 * A.im + z.im)]

/-- Each jump is captured uniformly, independently of the preceding prefix value. -/
theorem node_window_energy_lower_bound (x : ι → ℝ) (c : ι → ℂ) {g : ℝ}
    (hg : 0 < g) (hsep : ∀ i j, i ≠ j → g ≤ |x i - x j|) (i : ι) (v : ℝ) :
    g / 8 * Complex.normSq (c i) ≤
      ∫ u : ℝ in nodeWindow x g i, Complex.normSq (prefix x c u - prefix x c v) := by
  let A := otherPrefix x c i - prefix x c v
  let f : ℝ → ℝ := fun u => Complex.normSq (prefix x c u - prefix x c v)
  have hleft : EqOn f (fun _ => Complex.normSq A) (Ico (x i - g / 4) (x i)) := by
    intro u hu
    dsimp only [f, A]
    rw [prefix_on_left x c hg hsep i hu]
  have hright : EqOn f (fun _ => Complex.normSq (A + c i))
      (Ico (x i) (x i + g / 4)) := by
    intro u hu
    dsimp only [f, A]
    rw [prefix_on_right x c hg hsep i hu]
    congr 1
    ring
  have hiL : IntegrableOn f (Ico (x i - g / 4) (x i)) := by
    apply (integrableOn_const (by simp) :
      IntegrableOn (fun _ : ℝ => Complex.normSq A) (Ico (x i - g / 4) (x i))).congr_fun
      (fun u hu => (hleft hu).symm) measurableSet_Ico
  have hiR : IntegrableOn f (Ico (x i) (x i + g / 4)) := by
    apply (integrableOn_const (by simp) :
      IntegrableOn (fun _ : ℝ => Complex.normSq (A + c i))
        (Ico (x i) (x i + g / 4))).congr_fun
      (fun u hu => (hright hu).symm) measurableSet_Ico
  have hdis : Disjoint (Ico (x i - g / 4) (x i)) (Ico (x i) (x i + g / 4)) := by
    apply Set.disjoint_left.mpr
    intro u hu hv
    exact (not_lt_of_ge hv.1) hu.2
  have hsplit : nodeWindow x g i =
      Ico (x i - g / 4) (x i) ∪ Ico (x i) (x i + g / 4) := by
    exact (Ico_union_Ico_eq_Ico (by linarith) (by linarith)).symm
  have hvalL : (∫ u : ℝ in Ico (x i - g / 4) (x i), f u) =
      (g / 4) * Complex.normSq A := by
    rw [setIntegral_congr_fun measurableSet_Ico hleft, setIntegral_const,
      Real.volume_real_Ico_of_le (by linarith), smul_eq_mul]
    ring
  have hvalR : (∫ u : ℝ in Ico (x i) (x i + g / 4), f u) =
      (g / 4) * Complex.normSq (A + c i) := by
    rw [setIntegral_congr_fun measurableSet_Ico hright, setIntegral_const,
      Real.volume_real_Ico_of_le (by linarith), smul_eq_mul]
    ring
  change g / 8 * Complex.normSq (c i) ≤ ∫ u : ℝ in nodeWindow x g i, f u
  rw [hsplit, setIntegral_union hdis measurableSet_Ico hiL hiR, hvalL, hvalR]
  have htwo := mul_le_mul_of_nonneg_left (two_point_square A (c i)) (by linarith : 0 ≤ g / 4)
  nlinarith

/-- The jump neighborhoods of separated nodes are genuinely disjoint. -/
theorem window_disjoint (x : ι → ℝ) {g : ℝ} (hg : 0 < g)
    (hsep : ∀ i j, i ≠ j → g ≤ |x i - x j|) :
    Pairwise (Disjoint on nodeWindow x g) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro u hu hv
  change x i - g / 4 ≤ u ∧ u < x i + g / 4 at hu
  change x j - g / 4 ≤ u ∧ u < x j + g / 4 at hv
  have hs := hsep i j hij
  rcases le_total (x i) (x j) with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)] at hs
    linarith [hu.2, hv.1]
  · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hs
    linarith [hv.2, hu.1]

/-- Every capturing rectangle lies in the full averaging strip. -/
theorem rect_subset_strip (x : ι → ℝ) {g a : ℝ} (hg : 0 < g) (hga : g ≤ a)
    (i : ι) : nodeWindow x g i ×ˢ baseWindow x a i ⊆
      {p : ℝ × ℝ | a ≤ p.1 - p.2 ∧ p.1 - p.2 ≤ 2 * a} := by
  rintro ⟨u, v⟩ ⟨hu, hv⟩
  change x i - g / 4 ≤ u ∧ u < x i + g / 4 at hu
  change x i - 7 * a / 4 ≤ v ∧ v ≤ x i - 5 * a / 4 at hv
  constructor <;> dsimp only <;> linarith [hu.1, hu.2, hv.1, hv.2]

end D5.S3.Analytic.Interpolation.SeparatedJumpRectangles
