/- GID: D5/S3/Fourier/Concentration/HighCosineThreshold
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/HighCosineThreshold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact three-level minimizer for the first two cosine moments near threshold one. -/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! A three-level finite-readout certificate and its application to a cyclic cosine grid. -/

open Finset Filter
open scoped Topology

noncomputable section

namespace D5.S3.Fourier.Concentration.HighCosineThreshold

def second (x : ℝ) : ℝ := 2 * x ^ 2 - 1

def difference (x : ℝ) : ℝ := x - second x

/-- The fraction of the noncentral mass placed at the upper off-center level. -/
def upperFraction (u l : ℝ) : ℝ := -difference l / (difference u - difference l)

/-- The common first and second moment of the noncentral mass. -/
def tailMoment (u l : ℝ) : ℝ :=
  upperFraction u l * u + (1 - upperFraction u l) * l

def count {ι : Type*} [Fintype ι] (c : ι → ℝ) (x : ℝ) : ℝ := by
  classical
  exact ((univ.filter (fun i => c i = x)).card : ℝ)

/-- Uniform weights within each of the three supporting levels. -/
def weights {ι : Type*} [Fintype ι] (c : ι → ℝ) (u l r : ℝ) (i : ι) : ℝ := by
  classical
  exact if c i = 1 then 1 - r
    else if c i = u then r * upperFraction u l / count c u
    else if c i = l then r * (1 - upperFraction u l) / count c l else 0

/-- The squared mass of the three-level law with a unique top entry. -/
def exactEnergy {ι : Type*} [Fintype ι] (c : ι → ℝ) (u l r : ℝ) : ℝ :=
  (1 - r) ^ 2 +
    r ^ 2 * ((upperFraction u l) ^ 2 / count c u +
      (1 - upperFraction u l) ^ 2 / count c l)

private theorem count_pos {ι : Type*} [Fintype ι] {c : ι → ℝ} {x : ℝ}
    (hx : ∃ i, c i = x) : 0 < count c x := by
  classical
  obtain ⟨i, hi⟩ := hx
  change 0 < ((univ.filter (fun j => c j = x)).card : ℝ)
  exact Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩)

private theorem integrate_weights {ι : Type*} [Fintype ι] {c : ι → ℝ}
    {z : ι} (hz : ∀ i, c i = 1 ↔ i = z) {u l r : ℝ}
    (hu : u < 1) (hl : l < u) (hnu : 0 < count c u) (hnl : 0 < count c l)
    (f : ι → ℝ) (fu fl : ℝ)
    (hfU : ∀ i, c i = u → f i = fu) (hfL : ∀ i, c i = l → f i = fl) :
    ∑ i, weights c u l r i * f i =
      (1 - r) * f z + r * upperFraction u l * fu + r * (1 - upperFraction u l) * fl := by
  classical
  let p := upperFraction u l
  have hsplit (i : ι) : weights c u l r i * f i =
      (if i = z then (1 - r) * f z else 0) +
      (if c i = u then (r * p / count c u) * fu else 0) +
      (if c i = l then (r * (1 - p) / count c l) * fl else 0) := by
    by_cases ht : c i = 1
    · have hiz := (hz i).mp ht
      simp [weights, hiz, (hz z).mpr rfl, hu.ne', (hl.trans hu).ne']
    · by_cases hi : c i = u
      · simp [weights, hi, hu.ne, mt (hz i).mpr ht, hl.ne', hfU i hi, p]
      · by_cases hj : c i = l
        · simp [weights, hj, (hl.trans hu).ne, hl.ne, mt (hz i).mpr ht, hfL i hj, p]
        · simp [weights, ht, hi, hj, mt (hz i).mpr ht]
  simp only [hsplit, sum_add_distrib, sum_ite_eq', mem_univ, ite_true, ← sum_filter,
    sum_const, nsmul_eq_mul]
  change (1 - r) * f z + count c u * (r * p / count c u * fu) +
    count c l * (r * (1 - p) / count c l * fl) = _
  field_simp [hnu.ne', hnl.ne']
  dsimp only [p]
  ring

private theorem weights_moments {ι : Type*} [Fintype ι] {c : ι → ℝ} {z : ι}
    (hz : ∀ i, c i = 1 ↔ i = z) {u l a : ℝ} (hu : u < 1) (hl : l < u)
    (hnu : 0 < count c u) (hnl : 0 < count c l)
    (hgu : 0 < difference u) (hgl : difference l < 0) (hb : tailMoment u l < 1) :
    let r := (1 - a) / (1 - tailMoment u l)
    let v := weights c u l r
    (∑ i, v i) = 1 ∧ (∑ i, v i * c i) = a ∧ (∑ i, v i * second (c i)) = a := by
  let p := upperFraction u l
  let b := tailMoment u l
  let r := (1 - a) / (1 - b)
  let v := weights c u l r
  have hg : 0 < difference u - difference l := sub_pos.mpr (hgl.trans hgu)
  have hra : r * (1 - b) = 1 - a := div_mul_cancel₀ _ (sub_pos.mpr hb).ne'
  have hbal : p * second u + (1 - p) * second l = b := by
    change _ = p * u + (1 - p) * l
    have he : p * (difference u - difference l) = -difference l :=
      div_mul_cancel₀ _ hg.ne'
    unfold difference at he
    linarith
  have hmass : (∑ i, v i) = 1 := by
    simpa only [mul_one] using
      (integrate_weights hz hu hl hnu hnl (fun _ => 1) 1 1 (fun _ _ => rfl) (fun _ _ => rfl)).trans
        (by ring : (1 - r) * 1 + r * upperFraction u l * 1 + r * (1 - upperFraction u l) * 1 = 1)
  have hfirst : (∑ i, v i * c i) = a := by
    rw [integrate_weights hz hu hl hnu hnl c u l (fun _ h => h) (fun _ h => h), (hz z).mpr rfl]
    change (1 - r) * 1 + r * p * u + r * (1 - p) * l = a
    change r * (1 - (p * u + (1 - p) * l)) = 1 - a at hra
    linear_combination -hra
  have hsecond : (∑ i, v i * second (c i)) = a := by
    rw [integrate_weights hz hu hl hnu hnl (fun i => second (c i)) (second u) (second l)
        (fun _ h => congrArg second h) (fun _ h => congrArg second h), (hz z).mpr rfl]
    have htop : second 1 = 1 := by norm_num [second]
    rw [htop]
    change (1 - r) * 1 + r * p * second u + r * (1 - p) * second l = a
    linear_combination r * hbal - hra
  exact ⟨hmass, hfirst, hsecond⟩

def topCoeff (u l r : ℝ) : ℝ := (1 - r) / ((1 - u) * (1 - l))

def upperCoeff (u l nu r : ℝ) : ℝ :=
  (r * upperFraction u l / nu) / ((u - 1) * (u - l))

def lowerCoeff (u l nl r : ℝ) : ℝ :=
  (r * (1 - upperFraction u l) / nl) / ((l - 1) * (l - u))

def polynomial (u l nu nl r x : ℝ) : ℝ :=
  topCoeff u l r * (x - u) * (x - l) +
    upperCoeff u l nu r * (x - 1) * (x - l) +
    lowerCoeff u l nl r * (x - 1) * (x - u)

def firstMultiplier (u l nu nl r : ℝ) : ℝ :=
  -(topCoeff u l r * (u + l) + upperCoeff u l nu r * (1 + l) +
    lowerCoeff u l nl r * (1 + u))

def secondMultiplier (u l nu nl r : ℝ) : ℝ :=
  (topCoeff u l r + upperCoeff u l nu r + lowerCoeff u l nl r) / 2

theorem polynomial_expand (u l nu nl r x : ℝ) :
    polynomial u l nu nl r x =
      (topCoeff u l r * u * l + upperCoeff u l nu r * l + lowerCoeff u l nl r * u +
        secondMultiplier u l nu nl r) +
      firstMultiplier u l nu nl r * x + secondMultiplier u l nu nl r * second x := by
  unfold polynomial firstMultiplier secondMultiplier second
  ring

theorem polynomial_values {u l : ℝ} (hu : u < 1) (hl : l < u) (nu nl r : ℝ) :
    polynomial u l nu nl r 1 = 1 - r ∧
    polynomial u l nu nl r u = r * upperFraction u l / nu ∧
    polynomial u l nu nl r l = r * (1 - upperFraction u l) / nl := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [polynomial, topCoeff, sub_self, mul_zero, zero_mul, add_zero]
    field_simp [sub_ne_zero.mpr hu.ne', sub_ne_zero.mpr (hl.trans hu).ne']
  · simp only [polynomial, upperCoeff, sub_self, mul_zero, zero_mul, zero_add, add_zero]
    field_simp [sub_ne_zero.mpr hu.ne, sub_ne_zero.mpr hl.ne']
  · simp only [polynomial, lowerCoeff, sub_self, mul_zero, zero_add, add_zero]
    field_simp [sub_ne_zero.mpr (hl.trans hu).ne, sub_ne_zero.mpr hl.ne]

def slope (atZero atOne : ℝ) : ℝ := 1 - atOne / atZero

def certificateSlopes {ι : Type*} [Fintype ι] (c : ι → ℝ) (u l : ℝ) : Finset ℝ := by
  classical
  let β := firstMultiplier u l (count c u) (count c l)
  let γ := secondMultiplier u l (count c u) (count c l)
  let P := polynomial u l (count c u) (count c l)
  exact insert 1 (insert (slope (β 0) (β 1)) (insert (slope (γ 0) (γ 1))
    ((univ.filter (fun i => l < c i ∧ c i < u)).image
      (fun i => slope (P 0 (c i)) (P 1 (c i))))))

theorem one_mem_slopes {ι : Type*} [Fintype ι] (c : ι → ℝ) (u l : ℝ) :
    1 ∈ certificateSlopes c u l := by
  classical
  simp [certificateSlopes]

def slopeBound {ι : Type*} [Fintype ι] (c : ι → ℝ) (u l : ℝ) : ℝ :=
  (certificateSlopes c u l).sup' ⟨1, one_mem_slopes c u l⟩ id

private theorem one_le_bound {ι : Type*} [Fintype ι] (c : ι → ℝ) (u l : ℝ) :
    1 ≤ slopeBound c u l :=
  le_sup' id (one_mem_slopes c u l)

/-- The lower threshold at which one of the interpolation certificate's inequalities
first becomes an equality. It is computed by a finite maximum of slopes. -/
def criticalThreshold {ι : Type*} [Fintype ι] (c : ι → ℝ) (u l : ℝ) : ℝ :=
  1 - (1 - tailMoment u l) / slopeBound c u l

private theorem affine_sign {f : ℝ → ℝ} {r : ℝ} (h₀ : 0 < f 0)
    (haff : f r = (1 - r) * f 0 + r * f 1) :
    0 ≤ f r ↔ r * slope (f 0) (f 1) ≤ 1 := by
  have h : f r = f 0 * (1 - r * slope (f 0) (f 1)) := by
    rw [haff, slope]
    field_simp [h₀.ne']
    ring
  rw [h, mul_nonneg_iff_of_pos_left h₀, sub_nonneg]

private theorem signs_iff {ι : Type*} [Fintype ι] (c : ι → ℝ) {u l r : ℝ}
    (hu : u < 1) (hl : l < u) (hs : u + l < 0) (hr : 0 ≤ r) :
    let β := firstMultiplier u l (count c u) (count c l)
    let γ := secondMultiplier u l (count c u) (count c l)
    let P := polynomial u l (count c u) (count c l)
    r * slopeBound c u l ≤ 1 ↔
      r ≤ 1 ∧ 0 ≤ β r ∧ 0 ≤ γ r ∧
        ∀ i, l < c i → c i < u → P r (c i) ≤ 0 := by
  classical
  dsimp only
  let β := firstMultiplier u l (count c u) (count c l)
  let γ := secondMultiplier u l (count c u) (count c l)
  let P := polynomial u l (count c u) (count c l)
  have ht : 0 < topCoeff u l 0 := by
    unfold topCoeff
    exact div_pos (by norm_num) (mul_pos (sub_pos.mpr hu) (sub_pos.mpr (hl.trans hu)))
  have hb0 : 0 < β 0 := by
    simp [β, firstMultiplier, upperCoeff, lowerCoeff, mul_neg_of_pos_of_neg ht hs]
  have hg0 : 0 < γ 0 := by
    simp [γ, secondMultiplier, upperCoeff, lowerCoeff, ht]
  have hb := affine_sign (r := r) hb0 (by
    unfold β firstMultiplier topCoeff upperCoeff lowerCoeff
    simp only [div_eq_mul_inv]
    ring)
  have hg := affine_sign (r := r) hg0 (by
    unfold γ secondMultiplier topCoeff upperCoeff lowerCoeff
    simp only [div_eq_mul_inv]
    ring)
  have hP (i : ι) (h₁ : l < c i) (h₂ : c i < u) :
      P r (c i) ≤ 0 ↔ r * slope (P 0 (c i)) (P 1 (c i)) ≤ 1 := by
    have hp0 : 0 < (fun t => -P t (c i)) 0 := by
      apply neg_pos.mpr
      simp only [P, polynomial, upperCoeff, lowerCoeff, zero_mul, zero_div, add_zero]
      exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg ht (sub_neg.mpr h₂)) (sub_pos.mpr h₁)
    have hp := affine_sign (f := fun t => -P t (c i)) (r := r) hp0 (by
      unfold P polynomial topCoeff upperCoeff lowerCoeff
      simp only [div_eq_mul_inv]
      ring)
    simpa [slope] using hp
  have hbound : r * slopeBound c u l ≤ 1 ↔
      ∀ s ∈ certificateSlopes c u l, r * s ≤ 1 := by
    constructor
    · intro h s hs'
      exact (mul_le_mul_of_nonneg_left (le_sup' id hs') hr).trans h
    · intro h
      obtain ⟨s, hs', he⟩ := exists_mem_eq_sup' (H := ⟨1, one_mem_slopes c u l⟩) id
      change slopeBound c u l = s at he
      rw [he]
      exact h s hs'
  change _ ↔ r ≤ 1 ∧ 0 ≤ β r ∧ 0 ≤ γ r ∧ ∀ i, l < c i → c i < u → P r (c i) ≤ 0
  rw [hbound, hb, hg]
  simp only [certificateSlopes, Finset.forall_mem_insert, mul_one, forall_mem_image,
    mem_filter, mem_univ, true_and]
  change (r ≤ 1 ∧ r * slope (β 0) (β 1) ≤ 1 ∧ r * slope (γ 0) (γ 1) ≤ 1 ∧
    ∀ ⦃x : ι⦄, l < c x ∧ c x < u → r * slope (P 0 (c x)) (P 1 (c x)) ≤ 1) ↔ _
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨h₁, h₂, h₃, fun i hi hj => (hP i hi hj).mpr (h₄ (x := i) ⟨hi, hj⟩)⟩
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨h₁, h₂, h₃, fun {i} hi => (hP i hi.1 hi.2).mp (h₄ i hi.1 hi.2)⟩

theorem weights_eq_max {ι : Type*} [Fintype ι] (c : ι → ℝ)
    {u l r : ℝ} (hu : u < 1) (hl : l < u)
    (hlevels : ∀ i, c i = 1 ∨ (l ≤ c i ∧ c i ≤ u))
    (hr : 0 ≤ r) (hr₁ : r ≤ 1) (hp : 0 ≤ upperFraction u l)
    (hp₁ : upperFraction u l ≤ 1)
    (hcut : ∀ i, l < c i → c i < u → polynomial u l (count c u) (count c l) r (c i) ≤ 0)
    (i : ι) : weights c u l r i = max 0 (polynomial u l (count c u) (count c l) r (c i)) := by
  classical
  have hlu := hl.trans hu
  obtain ⟨htop, hupper, hlower⟩ := polynomial_values hu hl (count c u) (count c l) r
  rcases hlevels i with ht | ⟨hlo, hhi⟩
  · rw [ht, htop, max_eq_right (sub_nonneg.mpr hr₁)]
    simp [weights, ht]
  by_cases hi : c i = u
  · rw [hi, hupper, max_eq_right (div_nonneg (mul_nonneg hr hp) (count_pos ⟨i, hi⟩).le)]
    simp [weights, hi, hu.ne]
  by_cases hj : c i = l
  · have hnonneg := div_nonneg (mul_nonneg hr (sub_nonneg.mpr hp₁)) (count_pos ⟨i, hj⟩).le
    rw [hj, hlower, max_eq_right hnonneg]
    simp [weights, hj, hlu.ne, hl.ne]
  rw [max_eq_left (hcut i (lt_of_le_of_ne hlo (Ne.symm hj)) (lt_of_le_of_ne hhi hi))]
  simp [weights, hi, hj, ne_of_lt (hhi.trans_lt hu)]

/-- A positive part of a linear combination of two readouts gives a squared-distance
lower bound when the corresponding moments of the candidate are no larger. -/
private theorem squared_distance_le_gap {ι : Type*} [Fintype ι] (c d v w : ι → ℝ)
    {α β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hv : ∀ i, v i = max 0 (α + β * c i + γ * d i))
    (hw : ∀ i, 0 ≤ w i) (hmass : ∑ i, w i = ∑ i, v i)
    (hc : (∑ i, v i * c i) ≤ ∑ i, w i * c i)
    (hd : (∑ i, v i * d i) ≤ ∑ i, w i * d i) :
    (∑ i, (w i - v i) ^ 2) ≤ (∑ i, w i ^ 2) - ∑ i, v i ^ 2 := by
  let raw (i : ι) := α + β * c i + γ * d i
  have hpoint (i : ι) : raw i * (w i - v i) ≤ v i * (w i - v i) := by
    have hvi : v i = max 0 (raw i) := hv i
    rcases le_total 0 (raw i) with h | h
    · rw [hvi, max_eq_right h]
    · simpa only [hvi, max_eq_left h, sub_zero, zero_mul] using
        mul_nonpos_of_nonpos_of_nonneg h (hw i)
  have hraw : (∑ i, raw i * (w i - v i)) =
      α * ((∑ i, w i) - ∑ i, v i) +
        β * ((∑ i, w i * c i) - ∑ i, v i * c i) +
        γ * ((∑ i, w i * d i) - ∑ i, v i * d i) := by
    simp only [← sum_sub_distrib, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun _ _ => by unfold raw; ring
  have hraw₀ : 0 ≤ ∑ i, raw i * (w i - v i) := by
    rw [hraw, hmass, sub_self, mul_zero, zero_add]
    exact add_nonneg (mul_nonneg hβ (sub_nonneg.mpr hc)) (mul_nonneg hγ (sub_nonneg.mpr hd))
  have hdot := hraw₀.trans (sum_le_sum fun i _ => hpoint i)
  have he : (∑ i, (w i - v i) ^ 2) + 2 * (∑ i, v i * (w i - v i)) =
      (∑ i, w i ^ 2) - ∑ i, v i ^ 2 := by
    rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun _ _ => by ring
  linarith

/-- Feasibility, exact energy, and the squared-distance certificate for a given threshold. -/
def IsCertified {ι : Type*} [Fintype ι] (c : ι → ℝ) (u l a : ℝ) : Prop :=
  let r := (1 - a) / (1 - tailMoment u l)
  let v := weights c u l r
  (∀ i, 0 ≤ v i) ∧ (∑ i, v i) = 1 ∧
    (∑ i, v i * c i) = a ∧ (∑ i, v i * (2 * (c i) ^ 2 - 1)) = a ∧
    (∑ i, v i ^ 2) = exactEnergy c u l r ∧
    ∀ w : ι → ℝ, (∀ i, 0 ≤ w i) → (∑ i, w i) = 1 →
      a ≤ (∑ i, w i * c i) → a ≤ (∑ i, w i * (2 * (c i) ^ 2 - 1)) →
      (∑ i, (w i - v i) ^ 2) ≤ (∑ i, w i ^ 2) - exactEnergy c u l r ∧
      ((∑ i, w i ^ 2) = exactEnergy c u l r → w = v)

private theorem ordered_levels {u l : ℝ} (hs : u + l < 0)
    (hgu : 0 < u - (2 * u ^ 2 - 1)) (hgl : l - (2 * l ^ 2 - 1) < 0) :
    u < 1 ∧ l < u := by
  have hp : 0 < (1 - u) * (2 * u + 1) := by nlinarith only [hgu]
  have ⟨hu, hu'⟩ : u < 1 ∧ -(1 / 2) < u := by
    rcases mul_pos_iff.mp hp with hyp | hyp <;> constructor <;> linarith [hyp.1, hyp.2]
  have hn : (1 - l) * (2 * l + 1) < 0 := by nlinarith only [hgl]
  have hlow : 2 * l + 1 < 0 := by
    rcases mul_neg_iff.mp hn with hyp | hyp <;> linarith [hyp.1, hyp.2]
  exact ⟨hu, by linarith⟩

private theorem tailMoment_lt_cutoff {ι : Type*} [Fintype ι] {c : ι → ℝ} {u l : ℝ}
    (hu : u < 1) (hl : l < u) (hs : u + l < 0)
    (hgu : 0 < difference u) (hgl : difference l < 0) (hnu : 0 < count c u) :
    tailMoment u l < criticalThreshold c u l := by
  have hproduct : 0 < (1 - u) * (2 * u + 1) := by
    unfold difference second at hgu
    nlinarith only [hgu]
  have hu_low := (mul_pos_iff_of_pos_left (sub_pos.mpr hu)).mp hproduct
  let p := upperFraction u l
  let b := tailMoment u l
  let B := slopeBound c u l
  let nu := count c u
  let nl := count c l
  have hg : 0 < difference u - difference l := sub_pos.mpr (hgl.trans hgu)
  have hp : 0 < p := div_pos (neg_pos.mpr hgl) hg
  have hp₁ : p < 1 := (div_lt_one hg).mpr (by linarith)
  have hb : b < 1 := by
    change p * u + (1 - p) * l < 1
    nlinarith [mul_nonneg (sub_nonneg.mpr hp₁.le) (sub_nonneg.mpr hl.le)]
  have hB : 1 < B := by
    by_contra! h
    obtain ⟨_, hβ, hγ, _⟩ := (signs_iff c hu hl hs (r := 1) zero_le_one).mp
      (by simpa only [one_mul] using h)
    have hP := polynomial_values hu hl nu nl 1
    have h₁ := polynomial_expand u l nu nl 1 1
    have h₂ := polynomial_expand u l nu nl 1 u
    rw [hP.1, sub_self] at h₁
    rw [hP.2.1, one_mul] at h₂
    have hw : 0 < p / nu := div_pos hp hnu
    have hdiff : 0 ≤ second 1 - second u := by
      unfold second
      nlinarith [mul_nonneg (sub_nonneg.mpr hu.le) (show 0 ≤ 1 + u by linarith)]
    have hle := add_nonneg (mul_nonneg hβ (sub_nonneg.mpr hu.le)) (mul_nonneg hγ hdiff)
    change 0 ≤ firstMultiplier u l nu nl 1 * (1 - u) +
      secondMultiplier u l nu nl 1 * (second 1 - second u) at hle
    change 0 < upperFraction u l / nu at hw
    nlinarith only [h₁, h₂, hw, hle]
  have hd : (1 - b) / B < 1 - b := (div_lt_iff₀ (zero_lt_one.trans hB)).mpr (by
    nlinarith [mul_pos (sub_pos.mpr hb) (sub_pos.mpr hB)])
  change b < 1 - (1 - b) / B
  linarith

/-- For a finite readout with a unique top value one, both moments bind near one.
The off-center extreme levels must straddle the zero of the moment difference,
and their sum must be negative. -/
theorem high_threshold_certificate {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (z : ι) (hz : ∀ i, c i = 1 ↔ i = z) {u l : ℝ}
    (hs : u + l < 0)
    (hgu : 0 < u - (2 * u ^ 2 - 1)) (hgl : l - (2 * l ^ 2 - 1) < 0)
    (hlevels : ∀ i, c i = 1 ∨ (l ≤ c i ∧ c i ≤ u))
    (huAtt : ∃ i, c i = u) (hlAtt : ∃ i, c i = l) :
    tailMoment u l < criticalThreshold c u l ∧ criticalThreshold c u l < 1 ∧
      ∀ a, criticalThreshold c u l ≤ a → a ≤ 1 → IsCertified c u l a := by
  classical
  obtain ⟨hu, hl⟩ := ordered_levels hs hgu hgl
  change 0 < difference u at hgu
  change difference l < 0 at hgl
  let p := upperFraction u l
  let b := tailMoment u l
  let nu := count c u
  let nl := count c l
  have hnu : 0 < nu := count_pos huAtt
  have hnl : 0 < nl := count_pos hlAtt
  have hg : 0 < difference u - difference l := sub_pos.mpr (hgl.trans hgu)
  have hp : 0 < p := div_pos (neg_pos.mpr hgl) hg
  have hp₁ : p < 1 := (div_lt_one hg).mpr (by linarith)
  have hb : b < 1 := by
    calc
      b = p * u + (1 - p) * l := rfl
      _ ≤ u := by nlinarith [mul_nonneg (sub_nonneg.mpr hp₁.le) (sub_nonneg.mpr hl.le)]
      _ < 1 := hu
  let B := slopeBound c u l
  have hB : 0 < B := zero_lt_one.trans_le (one_le_bound c u l)
  refine ⟨tailMoment_lt_cutoff hu hl hs hgu hgl hnu,
    sub_lt_self _ (div_pos (sub_pos.mpr hb) hB), ?_⟩
  intro a ha ha₁
  let r := (1 - a) / (1 - b)
  let v := weights c u l r
  have hr : 0 ≤ r := div_nonneg (sub_nonneg.mpr ha₁) (sub_nonneg.mpr hb.le)
  have hra : r * (1 - b) = 1 - a := div_mul_cancel₀ _ (sub_pos.mpr hb).ne'
  have hrB : r * B ≤ 1 := by
    change 1 - (1 - b) / B ≤ a at ha
    have h : 1 - a ≤ (1 - b) / B := by linarith
    have hm := (le_div_iff₀ hB).mp h
    apply (le_of_mul_le_mul_right ?_ (sub_pos.mpr hb))
    calc
      r * B * (1 - b) = (r * (1 - b)) * B := by ring
      _ ≤ 1 * (1 - b) := by rwa [hra, one_mul]
  obtain ⟨hr₁, hβ, hγ, hc⟩ := (signs_iff c hu hl hs hr).mp hrB
  have hv := weights_eq_max c hu hl hlevels hr hr₁ hp.le hp₁.le hc
  obtain ⟨hmass, hfirst, hsecond⟩ := weights_moments hz hu hl hnu hnl hgu hgl hb (a := a)
  have henergy : (∑ i, v i ^ 2) = exactEnergy c u l r := by
    have hU (i : ι) (hi : c i = u) : v i = r * p / nu := by simp [v, weights, hi, hu.ne, p, nu]
    have hL (i : ι) (hi : c i = l) : v i = r * (1 - p) / nl := by
      simp [v, weights, hi, (hl.trans hu).ne, hl.ne, p, nl]
    have hZ : v z = 1 - r := by simp [v, weights, (hz z).mpr rfl]
    simp only [pow_two]
    rw [integrate_weights hz hu hl hnu hnl v _ _ hU hL, hZ]
    unfold exactEnergy
    change (1 - r) * (1 - r) + r * p * (r * p / nu) +
      r * (1 - p) * (r * (1 - p) / nl) = _
    ring
  refine ⟨fun i => hv i ▸ le_max_left _ _, hmass, hfirst, hsecond, henergy, ?_⟩
  intro w hw hws hwc hwd
  have hd := squared_distance_le_gap c (fun i => second (c i)) v w hβ hγ
    (fun i => (hv i).trans (congrArg (max 0) (polynomial_expand u l nu nl r (c i))))
    hw (hws.trans hmass.symm)
    (hfirst.trans_le hwc) (hsecond.trans_le hwd)
  rw [henergy] at hd
  refine ⟨hd, ?_⟩
  intro he
  rw [he, sub_self] at hd
  funext i
  have hi := single_le_sum (f := fun j => (w j - v j) ^ 2)
    (fun j _ => sq_nonneg (w j - v j)) (mem_univ i)
  have hz' : (w i - v i) ^ 2 = 0 := le_antisymm (hi.trans hd) (sq_nonneg _)
  exact sub_eq_zero.mp (by simpa [pow_two] using hz')

private theorem exists_descent {ι : Type*} [Fintype ι] (c d v e : ι → ℝ)
    (hv : ∀ i, 0 ≤ v i) (hs : ∀ i, e i < 0 → 0 < v i)
    (hm : ∑ i, e i = 0) (hc : 0 ≤ ∑ i, e i * c i) (hd : 0 ≤ ∑ i, e i * d i)
    (hneg : (∑ i, e i * v i) < 0) :
    ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = (∑ i, v i) ∧
      (∑ i, v i * c i) ≤ (∑ i, w i * c i) ∧ (∑ i, v i * d i) ≤ (∑ i, w i * d i) ∧
      (∑ i, w i ^ 2) < (∑ i, v i ^ 2) := by
  let Q := ∑ i, e i ^ 2
  let D := ∑ i, e i * v i
  have hcont : Continuous (fun t : ℝ => t * Q + 2 * D) := by fun_prop
  have hzero : ContinuousAt (fun _ : ℝ => (0 : ℝ)) 0 := continuousAt_const
  have he0 : (0 : ℝ) * Q + 2 * D < 0 := by dsimp only [D]; linarith
  have hlocal : ∀ᶠ t : ℝ in 𝓝 0, t * Q + 2 * D < 0 ∧
      ∀ i, e i < 0 → 0 < v i + t * e i := by
    refine (hcont.continuousAt.eventually_lt hzero he0).and (Filter.eventually_all.mpr ?_)
    intro i
    by_cases hi : e i < 0
    · have hf : Continuous (fun t : ℝ => v i + t * e i) := by fun_prop
      have hpos : 0 < v i + 0 * e i := by simpa using hs i hi
      exact (hzero.eventually_lt hf.continuousAt hpos).mono (fun _ h _ => h)
    · exact Filter.Eventually.of_forall (fun _ h => (hi h).elim)
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp hlocal
  let t := δ / 2
  have ht : 0 < t := by dsimp only [t]; linarith
  have htδ : dist t (0 : ℝ) < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht]
    dsimp only [t]
    linarith
  obtain ⟨henergy, hpositive⟩ := hnear htδ
  refine ⟨fun i => v i + t * e i, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rcases lt_or_ge (e i) 0 with h | h
    · exact (hpositive i h).le
    · exact add_nonneg (hv i) (mul_nonneg ht.le h)
  · simp only [sum_add_distrib, ← mul_sum, hm, mul_zero, add_zero]
  · simp only [add_mul, sum_add_distrib, mul_assoc, ← mul_sum]
    exact le_add_of_nonneg_right (mul_nonneg ht.le hc)
  · simp only [add_mul, sum_add_distrib, mul_assoc, ← mul_sum]
    exact le_add_of_nonneg_right (mul_nonneg ht.le hd)
  · have he : (∑ i, (v i + t * e i) ^ 2) =
        (∑ i, v i ^ 2) + t * (t * Q + 2 * D) := by
      dsimp only [Q, D]
      simp only [mul_add, mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun _ _ => by ring
    rw [he]
    exact add_lt_of_neg_right _ (mul_neg_of_pos_of_neg ht henergy)

private def spike {ι : Type*} (j : ι) (t : ℝ) (i : ι) : ℝ := by
  classical
  exact if i = j then t else 0

private theorem sum_spike {ι : Type*} [Fintype ι] (j : ι) (t : ℝ) (f : ι → ℝ) :
    ∑ i, spike j t i * f i = t * f j := by
  classical
  simp only [spike, ite_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]

private def adjust {ι : Type*} (z j k : ι) (u l m f s : ℝ) (i : ι) : ℝ :=
  spike z (((s + m) / 2 - (u + l) * f + u * l * m) / ((1 - u) * (1 - l))) i +
    spike j (((s + m) / 2 - (1 + l) * f + l * m) / ((u - 1) * (u - l))) i +
    spike k (((s + m) / 2 - (1 + u) * f + u * m) / ((l - 1) * (l - u))) i

private theorem sum_adjust {ι : Type*} [Fintype ι] (c : ι → ℝ) (z j k : ι)
    {u l : ℝ} (hu : u < 1) (hl : l < u)
    (hz : c z = 1) (hj : c j = u) (hk : c k = l)
    (m f s : ℝ) (v : ι → ℝ) (α β γ : ℝ)
    (hv : ∀ i, i = z ∨ i = j ∨ i = k → v i = α + β * c i + γ * second (c i)) :
    ∑ i, adjust z j k u l m f s i * v i = α * m + β * f + γ * s := by
  simp only [adjust, add_mul, sum_add_distrib, sum_spike, hv z (Or.inl rfl),
    hv j (Or.inr (Or.inl rfl)), hv k (Or.inr (Or.inr rfl)), hz, hj, hk, second]
  field_simp [sub_ne_zero.mpr hu.ne, sub_ne_zero.mpr hu.ne', sub_ne_zero.mpr hl.ne,
    sub_ne_zero.mpr hl.ne', sub_ne_zero.mpr (hl.trans hu).ne,
    sub_ne_zero.mpr (hl.trans hu).ne']
  ring

/-- From the common tail moment up to the certificate boundary, excluding the boundary,
some feasible law has strictly smaller squared mass. -/
theorem exists_smaller_energy_below_threshold {ι : Type*} [Fintype ι] (c : ι → ℝ)
    (z j k : ι) {u l a : ℝ} (htop : ∀ i, c i = 1 ↔ i = z) (hj : c j = u) (hk : c k = l)
    (hs : u + l < 0)
    (hgu : 0 < u - (2 * u ^ 2 - 1)) (hgl : l - (2 * l ^ 2 - 1) < 0)
    (ha : tailMoment u l ≤ a) (hac : a < criticalThreshold c u l) :
    let r := (1 - a) / (1 - tailMoment u l)
    let v := weights c u l r
    ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
      a ≤ (∑ i, w i * c i) ∧ a ≤ (∑ i, w i * (2 * (c i) ^ 2 - 1)) ∧
      (∑ i, w i ^ 2) < (∑ i, v i ^ 2) := by
  classical
  have hz : c z = 1 := (htop z).mpr rfl
  obtain ⟨hu, hl⟩ := ordered_levels hs hgu hgl
  change 0 < difference u at hgu
  change difference l < 0 at hgl
  let p := upperFraction u l
  let b := tailMoment u l
  let r := (1 - a) / (1 - b)
  let v := weights c u l r
  let nu := count c u
  let nl := count c l
  let P := polynomial u l nu nl r
  let β := firstMultiplier u l nu nl r
  let γ := secondMultiplier u l nu nl r
  let α := topCoeff u l r * u * l + upperCoeff u l nu r * l + lowerCoeff u l nl r * u + γ
  have hνu : 0 < nu := count_pos ⟨j, hj⟩
  have hνl : 0 < nl := count_pos ⟨k, hk⟩
  have hg : 0 < difference u - difference l := sub_pos.mpr (hgl.trans hgu)
  have hp : 0 < p := div_pos (neg_pos.mpr hgl) hg
  have hp₁ : p < 1 := (div_lt_one hg).mpr (by linarith)
  have hb : b < 1 := by
    change p * u + (1 - p) * l < 1
    nlinarith [mul_nonneg (sub_nonneg.mpr hp₁.le) (sub_nonneg.mpr hl.le)]
  have hB := zero_lt_one.trans_le (one_le_bound c u l)
  have ha₁ : a < 1 := hac.trans (sub_lt_self _ (div_pos (sub_pos.mpr hb) hB))
  have hr : 0 < r := div_pos (sub_pos.mpr ha₁) (sub_pos.mpr hb)
  have hr_le : r ≤ 1 := (div_le_one (sub_pos.mpr hb)).mpr (by linarith)
  have hposU : 0 < v j := by
    simpa [v, weights, hj, hu.ne] using div_pos (mul_pos hr hp) hνu
  have hposL : 0 < v k := by
    simpa [v, weights, hk, (hl.trans hu).ne, hl.ne] using
      div_pos (mul_pos hr (sub_pos.mpr hp₁)) hνl
  have hnonneg (i : ι) : 0 ≤ v i := by
    by_cases h₁ : c i = 1
    · simpa [v, weights, h₁] using sub_nonneg.mpr hr_le
    · by_cases h₂ : c i = u
      · simpa [v, weights, h₂, hu.ne] using (div_pos (mul_pos hr hp) hνu).le
      · by_cases h₃ : c i = l
        · simpa [v, weights, h₃, (hl.trans hu).ne, hl.ne] using
            (div_pos (mul_pos hr (sub_pos.mpr hp₁)) hνl).le
        · simp [v, weights, h₁, h₂, h₃]
  let d (i : ι) := second (c i)
  obtain ⟨hmass, hfirst, hsecond⟩ := weights_moments htop hu hl hνu hνl hgu hgl hb (a := a)
  suffices ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = (∑ i, v i) ∧
      (∑ i, v i * c i) ≤ (∑ i, w i * c i) ∧ (∑ i, v i * d i) ≤ (∑ i, w i * d i) ∧
      (∑ i, w i ^ 2) < (∑ i, v i ^ 2) by
    obtain ⟨w, hw, hwm, hwc, hwd, hwe⟩ := this
    exact ⟨w, hw, hwm.trans hmass, hfirst.symm.trans_le hwc, hsecond.symm.trans_le hwd, hwe⟩
  rcases lt_or_eq_of_le ha with ha_lt | ha_eq
  swap
  · have hEq : a = b := ha_eq.symm
    have hr_eq : r = 1 := by
      dsimp only [r]
      rw [hEq, div_self (sub_ne_zero.mpr hb.ne')]
    have hvz : v z = 0 := by simp [v, weights, hz, hr_eq]
    let e (i : ι) := spike z 1 i - v i
    have he (f : ι → ℝ) : (∑ i, e i * f i) = f z - ∑ i, v i * f i := by
      simp only [e, sub_mul, sum_sub_distrib, sum_spike, one_mul]
    have henergy : 0 < ∑ i, v i ^ 2 :=
      sum_pos' (fun i _ => sq_nonneg (v i)) ⟨j, mem_univ j, sq_pos_of_pos hposU⟩
    refine exists_descent c d v e hnonneg (fun i hi => ?_) ?_ ?_ ?_ ?_
    · have hspike : 0 ≤ spike z 1 i := by simp [spike, apply_ite]
      change spike z 1 i - v i < 0 at hi
      linarith
    · have hm : (∑ i, v i) = 1 := hmass
      simpa only [mul_one, hm, sub_self] using he (fun _ => 1)
    · rw [he, hz, hfirst]
      exact sub_nonneg.mpr ha₁.le
    · have hdz : d z = 1 := by norm_num [d, second, hz]
      rw [he, hdz, hsecond]
      exact sub_nonneg.mpr ha₁.le
    · rw [he, hvz, zero_sub]
      simpa only [pow_two] using neg_neg_of_pos henergy
  have hr₁ : r < 1 := (div_lt_one (sub_pos.mpr hb)).mpr (by linarith)
  have hrB : 1 < r * slopeBound c u l := by
    change a < 1 - (1 - b) / slopeBound c u l at hac
    have h := (div_lt_iff₀ hB).mp (show (1 - b) / slopeBound c u l < 1 - a by linarith)
    have he : r * (1 - b) = 1 - a := div_mul_cancel₀ _ (sub_pos.mpr hb).ne'
    apply lt_of_mul_lt_mul_right ?_ (sub_nonneg.mpr hb.le)
    calc
      1 * (1 - b) = 1 - b := one_mul _
      _ < (1 - a) * slopeBound c u l := h
      _ = r * slopeBound c u l * (1 - b) := by rw [← he]; ring
  have hposZ : 0 < v z := by simpa [v, weights, hz] using sub_pos.mpr hr₁
  have hvP (i : ι) (hi : i = z ∨ i = j ∨ i = k) : v i = α + β * c i + γ * second (c i) := by
    have hvals := polynomial_values hu hl nu nl r
    have he : v i = P (c i) := by
      rcases hi with rfl | rfl | rfl
      · simpa [v, weights, hz, P] using hvals.1.symm
      · simpa [v, weights, hj, hu.ne, P] using hvals.2.1.symm
      · simpa [v, weights, hk, (hl.trans hu).ne, hl.ne, P] using hvals.2.2.symm
    exact he.trans (polynomial_expand u l nu nl r (c i))
  have hadjust (m f s : ℝ) :
      (∑ i, adjust z j k u l m f s i) = m ∧
      (∑ i, adjust z j k u l m f s i * c i) = f ∧
      (∑ i, adjust z j k u l m f s i * d i) = s ∧
      (∑ i, adjust z j k u l m f s i * v i) = α * m + β * f + γ * s := by
    refine ⟨?_, ?_, ?_, sum_adjust c z j k hu hl hz hj hk m f s v α β γ hvP⟩
    · simpa using sum_adjust c z j k hu hl hz hj hk m f s (fun _ => 1) 1 0 0
        (fun _ _ => by ring)
    · simpa using sum_adjust c z j k hu hl hz hj hk m f s c 0 1 0 (fun _ _ => by ring)
    · simpa using sum_adjust c z j k hu hl hz hj hk m f s d 0 0 1
        (fun _ _ => by dsimp [d]; ring)
  have hsupport (m f s : ℝ) (i : ι) (hi : ¬ (i = z ∨ i = j ∨ i = k)) :
      adjust z j k u l m f s i = 0 := by
    simp [adjust, spike, not_or.mp hi, not_or.mp (not_or.mp hi).2]
  have hactive (i : ι) (hi : i = z ∨ i = j ∨ i = k) : 0 < v i := by
    rcases hi with rfl | rfl | rfl
    · exact hposZ
    · exact hposU
    · exact hposL
  have hdir (m f s : ℝ) (i : ι) (hi : adjust z j k u l m f s i < 0) : 0 < v i := by
    by_contra! hn
    have h := hsupport m f s i (fun hh => (not_lt_of_ge hn) (hactive i hh))
    linarith
  by_cases hβ : 0 ≤ β
  · by_cases hγ : 0 ≤ γ
    · have hn : ¬ ∀ i, l < c i → c i < u → P (c i) ≤ 0 := by
        intro h
        exact (not_le_of_gt hrB) ((signs_iff c hu hl hs hr.le).mpr ⟨hr₁.le, hβ, hγ, h⟩)
      push Not at hn
      obtain ⟨i, hi₁, hi₂, hiP⟩ := hn
      let e (x : ι) := spike i 1 x + adjust z j k u l (-1) (-c i) (-d i) x
      obtain ⟨hm, hf, hd, hv⟩ := hadjust (-1) (-c i) (-d i)
      have hi0 : v i = 0 := by
        simp [v, weights, ne_of_lt (hi₂.trans hu), hi₁.ne', hi₂.ne]
      have he (f : ι → ℝ) : (∑ x, e x * f x) =
          f i + ∑ x, adjust z j k u l (-1) (-c i) (-d i) x * f x := by
        simp only [e, add_mul, sum_add_distrib, sum_spike, one_mul]
      refine exists_descent c d v e hnonneg ?_ ?_ ?_ ?_ ?_
      · intro x hx
        apply hdir (-1) (-c i) (-d i) x
        have hx₁ : 0 ≤ spike i 1 x := by simp [spike, apply_ite]
        change spike i 1 x + adjust z j k u l (-1) (-c i) (-d i) x < 0 at hx
        linarith
      · have h := he (fun _ => 1)
        simp only [mul_one, hm, add_neg_cancel] at h
        exact h
      · rw [he, hf, add_neg_cancel]
      · rw [he, hd, add_neg_cancel]
      · rw [he, hi0, zero_add, hv]
        have hP := polynomial_expand u l nu nl r (c i)
        change 0 < P (c i) at hiP
        change P (c i) = α + β * c i + γ * d i at hP
        linarith
    · obtain ⟨hm, hf, hd, hv⟩ := hadjust 0 0 1
      refine exists_descent c d v _ hnonneg (hdir 0 0 1) hm ?_ ?_ ?_
      · simp [hf]
      · simp [hd]
      · simpa using hv.trans_lt (by simpa using lt_of_not_ge hγ)
  · obtain ⟨hm, hf, hd, hv⟩ := hadjust 0 1 0
    refine exists_descent c d v _ hnonneg (hdir 0 1 0) hm ?_ ?_ ?_
    · simp [hf]
    · simp [hd]
    · simpa using hv.trans_lt (by simpa using lt_of_not_ge hβ)

/-- The first cosine readout on the canonical residue representatives. -/
def cyclicReadout (q : ℕ) (k : Fin q) : ℝ :=
  Real.cos (2 * Real.pi * (k.val : ℝ) / q)

/-- The largest off-center cosine level. -/
def cyclicUpper (q : ℕ) : ℝ := Real.cos (2 * Real.pi / q)

/-- The smallest cosine level, attained at the integer part of half the modulus. -/
def cyclicLower (q : ℕ) : ℝ := Real.cos (2 * Real.pi * ((q / 2 : ℕ) : ℝ) / q)

/-- A nonzero residue folds into the positive half of the cosine grid. -/
theorem cyclic_fold {q : ℕ} (k : Fin q) (hk : k.val ≠ 0) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ q / 2 ∧
      cyclicReadout q k = Real.cos (2 * Real.pi * (n : ℝ) / q) ∧
      (n = k.val ∨ n = q - k.val) := by
  have hbound := k.isLt
  by_cases h : k.val ≤ q / 2
  · exact ⟨k.val, by omega, h, rfl, Or.inl rfl⟩
  · refine ⟨q - k.val, by omega, by omega, ?_, Or.inr rfl⟩
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    have hangle : 2 * Real.pi * ((q - k.val : ℕ) : ℝ) / q =
        2 * Real.pi - 2 * Real.pi * (k.val : ℝ) / q := by
      rw [Nat.cast_sub hbound.le]
      field_simp
    rw [cyclicReadout, hangle, Real.cos_two_pi_sub]

/-- On every cycle of modulus at least four, the three-level law uniquely minimizes
squared mass for joint first- and second-cosine thresholds sufficiently close to one. -/
theorem cyclic_high_threshold_certificate {q : ℕ} (hq : 4 ≤ q) :
    let c := cyclicReadout q
    let u := cyclicUpper q
    let l := cyclicLower q
    let square := fun x : ℝ => x ^ 2
    tailMoment u l < criticalThreshold c u l ∧ criticalThreshold c u l < 1 ∧
      (∀ a, criticalThreshold c u l ≤ a → a ≤ 1 → IsCertified c u l a) ∧
      ∀ a, tailMoment u l ≤ a → a < criticalThreshold c u l →
        let v := weights c u l ((1 - a) / (1 - tailMoment u l))
        ∃ w : Fin q → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
          a ≤ (∑ i, w i * c i) ∧ a ≤ (∑ i, w i * (2 * (c i) ^ 2 - 1)) ∧
          (∑ i, square (w i)) < (∑ i, square (v i)) := by
  let z : Fin q := ⟨0, by omega⟩
  let one : Fin q := ⟨1, by omega⟩
  let half : Fin q := ⟨q / 2, by omega⟩
  let step : ℝ := 2 * Real.pi / q
  let θ (n : ℕ) : ℝ := step * n
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hstep : 0 < step := by dsimp [step]; positivity
  have hstepq : step * q = 2 * Real.pi := div_mul_cancel₀ _ hqR.ne'
  have hθ₀ (n : ℕ) : 0 ≤ θ n := mul_nonneg hstep.le (Nat.cast_nonneg _)
  have hθmono : Monotone θ := fun _ _ h => mul_le_mul_of_nonneg_left (by exact_mod_cast h) hstep.le
  have hhalf : θ (q / 2) ≤ Real.pi := by
    have h : (2 : ℝ) * ((q / 2 : ℕ) : ℝ) ≤ q := by
      exact_mod_cast (show 2 * (q / 2) ≤ q by omega)
    have hm := mul_le_mul_of_nonneg_left h hstep.le
    dsimp only [θ]
    nlinarith
  have hquarter : θ 1 ≤ Real.pi / 2 := by
    have h : (4 : ℝ) ≤ q := by exact_mod_cast hq
    have hm := mul_le_mul_of_nonneg_left h hstep.le
    dsimp only [θ, Nat.cast_one]
    nlinarith
  have hnearPi : Real.pi - θ 1 < θ (q / 2) := by
    have h : (q : ℝ) < 2 * ((q / 2 : ℕ) : ℝ) + 2 := by
      exact_mod_cast (show q < 2 * (q / 2) + 2 by omega)
    have hm := mul_lt_mul_of_pos_left h hstep
    dsimp only [θ, Nat.cast_one]
    nlinarith
  have hthird : 2 * Real.pi / 3 < θ (q / 2) := by
    have h : (q : ℝ) < 3 * ((q / 2 : ℕ) : ℝ) := by
      exact_mod_cast (show q < 3 * (q / 2) by omega)
    have hm := mul_lt_mul_of_pos_left h hstep
    dsimp only [θ]
    nlinarith
  have hread (k : Fin q) : cyclicReadout q k = Real.cos (θ k.val) := by
    unfold cyclicReadout θ step
    rw [div_mul_eq_mul_div]
  have hu : cyclicUpper q = Real.cos (θ 1) := by simp [cyclicUpper, θ, step]
  have hl : cyclicLower q = Real.cos (θ (q / 2)) := by
    unfold cyclicLower θ step
    rw [div_mul_eq_mul_div]
  have hfold (k : Fin q) (hk : k ≠ z) :
      ∃ n : ℕ, 1 ≤ n ∧ n ≤ q / 2 ∧ cyclicReadout q k = Real.cos (θ n) := by
    obtain ⟨n, hn, hh, he, _⟩ := cyclic_fold k (fun h => hk (Fin.ext h))
    exact ⟨n, hn, hh, by simpa only [θ, step, div_mul_eq_mul_div] using he⟩
  have htop : cyclicUpper q < 1 := by
    rw [hu, ← Real.cos_zero]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl
      ((hθmono (show 1 ≤ q / 2 by omega)).trans hhalf) (by simpa [θ] using hstep)
  have hlo : cyclicLower q < -(1 / 2 : ℝ) := by
    rw [hl, ← Real.cos_pi_div_three, ← Real.cos_pi_sub]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith [Real.pi_pos]) hhalf
      (by linarith [hthird])
  have hsum : cyclicUpper q + cyclicLower q < 0 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi
      (show 0 ≤ Real.pi - θ 1 by linarith [hquarter, Real.pi_pos]) hhalf hnearPi
    rw [Real.cos_pi_sub, ← hu, ← hl] at h
    linarith
  have hzero : cyclicReadout q z = 1 := by simp [cyclicReadout, z]
  have hrange (k : Fin q) (hk : k ≠ z) :
      cyclicLower q ≤ cyclicReadout q k ∧ cyclicReadout q k ≤ cyclicUpper q := by
    obtain ⟨n, hn₁, hn₂, hk'⟩ := hfold k hk
    rw [hk', hu, hl]
    exact ⟨Real.cos_le_cos_of_nonneg_of_le_pi (hθ₀ n) hhalf (hθmono hn₂),
      Real.cos_le_cos_of_nonneg_of_le_pi (hθ₀ 1) ((hθmono hn₂).trans hhalf) (hθmono hn₁)⟩
  have huniq (i : Fin q) : cyclicReadout q i = 1 ↔ i = z := by
    constructor
    · intro hi
      by_contra hne
      have h := (hrange i hne).2
      linarith
    · rintro rfl
      exact hzero
  let u := cyclicUpper q
  let l := cyclicLower q
  have hgu : 0 < u - (2 * u ^ 2 - 1) := by
    have hn : 0 ≤ cyclicUpper q := by
      rw [hu, ← Real.cos_pi_div_two]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (hθ₀ 1) (by linarith [Real.pi_pos]) hquarter
    have h := mul_pos (sub_pos.mpr htop) (show 0 < 2 * cyclicUpper q + 1 by linarith)
    dsimp only [u]
    nlinarith
  have hgl : l - (2 * l ^ 2 - 1) < 0 := by
    have h := mul_neg_of_pos_of_neg (show 0 < 1 - cyclicLower q by linarith)
      (show 2 * cyclicLower q + 1 < 0 by linarith)
    dsimp only [l]
    nlinarith
  have hlevels (i : Fin q) : cyclicReadout q i = 1 ∨ l ≤ cyclicReadout q i ∧ cyclicReadout q i ≤ u := by
    by_cases hi : i = z
    · exact Or.inl ((huniq i).mpr hi)
    · exact Or.inr (hrange i hi)
  have huAtt : cyclicReadout q one = u := (hread one).trans hu.symm
  have hlAtt : cyclicReadout q half = l := (hread half).trans hl.symm
  obtain ⟨hcut, hlt, hcert⟩ :=
    high_threshold_certificate (cyclicReadout q) z huniq hsum hgu hgl hlevels ⟨one, huAtt⟩ ⟨half, hlAtt⟩
  exact ⟨hcut, hlt, hcert, fun _ ha hac =>
    exists_smaller_energy_below_threshold (cyclicReadout q) z one half huniq huAtt hlAtt
      hsum hgu hgl ha hac⟩

end D5.S3.Fourier.Concentration.HighCosineThreshold
