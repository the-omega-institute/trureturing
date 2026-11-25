/- GID: D5/S3/Analytic/Probability/FiniteNegativeRegression
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/FiniteNegativeRegression
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Upper-event criteria and conditional means for finite negative dependence. -/

import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.UpperLower.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Sort
import Mathlib.Order.Fin.Tuple
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import D5.S3.Analytic.Probability.FiniteOrderedStrassen
import D5.S3.Analytic.Probability.ThreeBitCubeConditionalMeans

/-! Finite negative dependence via exact marginal laws and upper-event tests. -/

set_option autoImplicit false

open scoped Classical
open Finset

namespace D5.S3.Analytic.Probability.FiniteNegativeRegression

noncomputable section

variable {α β γ : Type*} [Fintype α]

/-- Expectation under a finite probability mass function. -/
def expect (p : PMF α) (f : α → ℝ) : ℝ := ∑ x, (p x).toReal * f x

/-- Covariance under a finite probability mass function. -/
def cov (p : PMF α) (f g : α → ℝ) : ℝ :=
  expect p (fun x => f x * g x) - expect p f * expect p g

/-- Weighted sum on a fiber of a finite projection. -/
def fiberSum (q : α → β) (b : β) (w : α → ℝ) : ℝ :=
  ∑ x ∈ univ.filter (fun x => q x = b), w x

/-- Real probability mass of a projection fiber. -/
def mass (p : PMF α) (q : α → β) (b : β) : ℝ :=
  fiberSum q b (fun x => (p x).toReal)

/-- Conditional mean on a projection fiber of positive mass. -/
def cond (p : PMF α) (q : α → β) (b : β) (f : α → ℝ) : ℝ :=
  fiberSum q b (fun x => (p x).toReal * f x) / mass p q b

/-- The real indicator of a set. -/
def event (U : Set β) (x : β) : ℝ := if x ∈ U then 1 else 0

variable {ι : Type*} {C : ι → Type*}

/-- Projection to the coordinates in a block. -/
def project (I : Finset ι) (x : ∀ i, C i) (i : I) : C i := x i

variable [∀ i, Fintype (C i)] [Fintype ι] [∀ i, LinearOrder (C i)]

/-- Full negative regression for disjoint response and conditioning blocks. -/
def FullNRD (p : PMF (∀ i, C i)) : Prop :=
  ∀ (I J : Finset ι), Disjoint I J → ∀ (f : (∀ i : I, C i) → ℝ), Monotone f →
    ∀ (a b : ∀ j : J, C j), a ≤ b →
      0 < mass p (project J) a → 0 < mass p (project J) b →
        cond p (project J) b (f ∘ project I) ≤ cond p (project J) a (f ∘ project I)

/-- Negative association for increasing real tests on disjoint blocks. -/
def NA (p : PMF (∀ i, C i)) : Prop :=
  ∀ (I J : Finset ι), Disjoint I J → ∀ (f : (∀ i : I, C i) → ℝ)
    (g : (∀ j : J, C j) → ℝ), Monotone f → Monotone g →
      cov p (f ∘ project I) (g ∘ project J) ≤ 0

/-- The product of the cardinalities of the actual one-coordinate supports. -/
def marginalProduct (p : PMF (∀ i, C i)) : ℕ :=
  ∏ i, Fintype.card ((p.map (fun x => x i)).support : Set (C i))

omit [Fintype ι] [∀ i, Fintype (C i)] [∀ i, LinearOrder (C i)] in
omit [Fintype ι] [∀ i, Fintype (C i)] [∀ i, LinearOrder (C i)] [Fintype α] in
private theorem upper_test_induction [Fintype β] [Preorder β] (w : β → ℝ)
    (hw : ∑ x, w x = 0) (hU : ∀ U : Set β, IsUpperSet U → ∑ x, w x * event U x ≤ 0)
    (f : β → ℝ) (hf : Monotone f) : ∑ x, w x * f x ≤ 0 := by
  suffices H : ∀ s : Finset ℝ, ∀ g : β → ℝ, Monotone g →
      (∀ x, g x ∈ s) → ∑ x, w x * g x ≤ 0 from
    H (univ.image f) f hf (by simp)
  intro s
  refine Finset.strongInductionOn s ?_
  intro s ih g hg hgs
  by_cases hs : s.Nonempty
  · let a := s.max' hs
    have ha : a ∈ s := max'_mem _ _
    let t := s.erase a
    by_cases ht : t.Nonempty
    · let b := t.max' ht
      have hb : b ∈ t := max'_mem _ _
      have hba : b ≤ a := le_max' _ _ (mem_of_mem_erase hb)
      have hcap (x : β) : min (g x) b ∈ t := by
        by_cases hx : g x = a
        · simpa [hx, min_eq_right hba] using hb
        · have hx' : g x ∈ t := mem_erase.mpr ⟨hx, hgs x⟩
          have hxb : g x ≤ b := le_max' _ _ hx'
          rwa [min_eq_left hxb]
      have hclip := ih t (erase_ssubset ha) (fun x => min (g x) b)
        (fun _ _ h => min_le_min (hg h) le_rfl) hcap
      have htail := hU {x | a ≤ g x} (fun _ _ hxy hx => hx.trans (hg hxy))
      have hsplit (x : β) : g x = min (g x) b + (a - b) * event {y | a ≤ g y} x := by
        by_cases hx : g x = a
        · simp [event, hx, min_eq_right hba]
        · have hx' : g x ∈ t := mem_erase.mpr ⟨hx, hgs x⟩
          have hlt : g x < a := lt_of_le_of_ne (le_max' _ _ (hgs x)) hx
          have hxb : g x ≤ b := le_max' _ _ hx'
          simp [event, hlt.not_ge, min_eq_left hxb]
      calc
        ∑ x, w x * g x =
            (∑ x, w x * min (g x) b) + (a - b) * ∑ x, w x * event {y | a ≤ g y} x := by
              rw [mul_sum, ← sum_add_distrib]
              apply sum_congr rfl
              intro x _
              calc
                w x * g x = w x * (min (g x) b + (a - b) * event {y | a ≤ g y} x) :=
                  congrArg (w x * ·) (hsplit x)
                _ = _ := by ring
        _ ≤ 0 := add_nonpos hclip (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hba) htail)
    · have hconst (x : β) : g x = a := by
        by_contra h
        exact ht ⟨g x, mem_erase.mpr ⟨h, hgs x⟩⟩
      simp [hconst, ← sum_mul, hw]
  · have : IsEmpty β := ⟨fun x => hs ⟨g x, hgs x⟩⟩
    simp

omit [Fintype ι] [∀ i, Fintype (C i)] [∀ i, LinearOrder (C i)] in
private theorem sum_by_fibers [Fintype β] (q : α → β) (w : α → ℝ) (g : β → ℝ) :
    ∑ b, fiberSum q b w * g b = ∑ x, w x * g (q x) := by
  rw [← Finset.sum_fiberwise univ q (fun x => w x * g (q x))]
  apply sum_congr rfl
  intro b _
  rw [fiberSum, sum_mul]
  apply sum_congr (by ext x; simp)
  intro x hx
  rw [(mem_filter.mp hx).2]

/-- Upper-event inequalities suffice for full negative regression, including zero fibers. -/
theorem fullNRD_of_upper (p : PMF (∀ i, C i))
    (h : ∀ (I J : Finset ι), Disjoint I J → ∀ U : Set (∀ i : I, C i), IsUpperSet U →
      ∀ (a b : ∀ j : J, C j), a ≤ b →
        0 < mass p (project J) a → 0 < mass p (project J) b →
        cond p (project J) b (event U ∘ project I) ≤
          cond p (project J) a (event U ∘ project I)) :
    ∀ (I J : Finset ι), Disjoint I J → ∀ (f : (∀ i : I, C i) → ℝ), Monotone f →
    ∀ (a b : ∀ j : J, C j), a ≤ b →
      0 < mass p (project J) a → 0 < mass p (project J) b →
        cond p (project J) b (f ∘ project I) ≤ cond p (project J) a (f ∘ project I) := by
  intro I J hd f hf a b hab ha hb
  let density (c : ∀ j : J, C j) (x : ∀ i, C i) :=
    if project J x = c then (p x).toReal / mass p (project J) c else 0
  have hcond (c : ∀ j : J, C j) (g : (∀ i : I, C i) → ℝ) :
      cond p (project J) c (g ∘ project I) = ∑ x, density c x * g (project I x) := by
    unfold cond fiberSum
    rw [Finset.sum_div, Finset.sum_filter]
    apply sum_congr rfl
    intro x _
    by_cases hx : project J x = c <;> simp [density, hx, div_mul_eq_mul_div, Function.comp_apply]
  let responseMass (c : ∀ j : J, C j) (y : ∀ i : I, C i) :=
    fiberSum (project I) y (density c)
  have hmean (c : ∀ j : J, C j) (g : (∀ i : I, C i) → ℝ) :
      cond p (project J) c (g ∘ project I) = ∑ y, responseMass c y * g y := by
    rw [hcond c g]
    exact (sum_by_fibers (project I) (density c) g).symm
  have hnonneg (c : ∀ j : J, C j) (hc : 0 < mass p (project J) c) (y : ∀ i : I, C i) :
      0 ≤ responseMass c y := by
    apply sum_nonneg
    intro x _
    by_cases hx : project J x = c
    · simp [density, hx, div_nonneg ENNReal.toReal_nonneg hc.le]
    · simp [density, hx]
  have htotal (c : ∀ j : J, C j) (hc : 0 < mass p (project J) c) :
      ∑ y, responseMass c y = 1 := by
    have he := hmean c (fun _ => 1)
    simp only [cond, Function.comp_apply, mul_one] at he
    change mass p (project J) c / mass p (project J) c = _ at he
    rwa [div_self hc.ne', eq_comm] at he
  have hupper (U : Finset (∀ i : I, C i))
      (hU : ∀ ⦃x y⦄, x ∈ U → x ≤ y → y ∈ U) :
      ∑ y ∈ U, responseMass b y ≤ ∑ y ∈ U, responseMass a y := by
    have hSet : IsUpperSet (↑U : Set (∀ i : I, C i)) :=
      fun _ _ hxy hx => hU hx hxy
    have htest := h I J hd (↑U) hSet a b hab ha hb
    have he (c : ∀ j : J, C j) :
        cond p (project J) c (event (↑U) ∘ project I) = ∑ y ∈ U, responseMass c y := by
      have hfilter : univ.filter (fun y => y ∈ U) = U := by ext y; simp
      rw [hmean c (event (↑U))]
      simp only [event, Finset.mem_coe, mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter, hfilter]
    simpa only [he] using htest
  obtain ⟨π, hπ, hrow, hcol, hsupp⟩ :=
    (FiniteOrderedStrassen.forall_isUpperSet_sum_le_iff_exists_coupling
      (responseMass b) (responseMass a) (hnonneg b hb) (hnonneg a ha)
      ((htotal b hb).trans (htotal a ha).symm)).mp hupper
  rw [hmean b f, hmean a f]
  calc
    ∑ x, responseMass b x * f x = ∑ x, ∑ y, π x y * f x := by
      simp only [← sum_mul, hrow]
    _ ≤ ∑ x, ∑ y, π x y * f y := by
      apply sum_le_sum
      intro x _
      apply sum_le_sum
      intro y _
      by_cases hxy : x ≤ y
      · exact mul_le_mul_of_nonneg_left (hf hxy) (hπ x y)
      · simp [hsupp x y hxy]
    _ = ∑ y, responseMass a y * f y := by
      rw [Finset.sum_comm]
      simp only [← sum_mul, hcol]

omit [Fintype ι] [∀ i, Fintype (C i)] [∀ i, LinearOrder (C i)] in
private theorem map_weight (p : PMF α) (q : α → β) (b : β) :
    (p.map q b).toReal = mass p q b := by
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
  · simp only [mass, fiberSum, sum_filter]
    apply sum_congr rfl
    intro x _
    by_cases hx : q x = b <;> simp [hx, show (b = q x) ↔ (q x = b) from eq_comm]
  · intro x _
    split_ifs
    · exact p.apply_ne_top x
    · exact ENNReal.zero_ne_top

omit [Fintype ι] [∀ i, Fintype (C i)] [∀ i, LinearOrder (C i)] in
private theorem mass_nonneg (p : PMF α) (q : α → β) (a : β) : 0 ≤ mass p q a :=
  sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)

omit [Fintype ι] [∀ i, Fintype (C i)] [∀ i, LinearOrder (C i)] in
private theorem mass_mul_cond (p : PMF α) (q : α → β) (a : β) (f : α → ℝ) :
    mass p q a * cond p q a f = fiberSum q a (fun x => (p x).toReal * f x) := by
  by_cases h : mass p q a = 0
  · have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)).mp h
    rw [h, zero_mul, fiberSum, sum_eq_zero (fun x hx => by rw [hz x hx, zero_mul])]
  · unfold cond
    rw [mul_comm, div_mul_cancel₀ _ h]

omit [Fintype ι] [∀ i, Fintype (C i)] [∀ i, LinearOrder (C i)] in
private theorem expect_map [Fintype β] (p : PMF α) (q : α → β) (g : β → ℝ) :
    expect (p.map q) g = expect p (g ∘ q) := by
  simp only [expect, map_weight]
  exact sum_by_fibers q _ g

omit [Fintype ι] [∀ i, Fintype (C i)] [∀ i, LinearOrder (C i)] in
private theorem tower_mul [Fintype β] (p : PMF α) (q : α → β) (f : α → ℝ) (g : β → ℝ) :
    expect (p.map q) (fun y => cond p q y f * g y) =
      expect p (fun x => f x * g (q x)) := by
  simp only [expect, map_weight, ← mul_assoc, mass_mul_cond]
  exact sum_by_fibers q _ g

omit [Fintype ι] [∀ i, Fintype (C i)] [∀ i, LinearOrder (C i)] in
private theorem tower [Fintype β] (p : PMF α) (q : α → β) (r : β → γ)
    (a : γ) (f : α → ℝ) :
    cond (p.map q) r a (fun y => cond p q y f) = cond p (r ∘ q) a f ∧
      mass (p.map q) r a = mass p (r ∘ q) a := by
  let g (y : β) : ℝ := if r y = a then 1 else 0
  have hmass : mass (p.map q) r a = mass p (r ∘ q) a := by
    simpa only [expect, mass, fiberSum, sum_filter, g, mul_ite, mul_one, mul_zero,
      Function.comp_apply] using expect_map p q g
  refine ⟨?_, hmass⟩
  change fiberSum r a (fun y => (p.map q y).toReal * cond p q y f) / mass (p.map q) r a =
    fiberSum (r ∘ q) a (fun x => (p x).toReal * f x) / mass p (r ∘ q) a
  rw [hmass]
  apply congrArg (· / mass p (r ∘ q) a)
  simpa only [expect, fiberSum, sum_filter, g, mul_ite, mul_one, mul_zero, mul_assoc,
    Function.comp_apply] using tower_mul p q f g

omit [Fintype ι] [∀ i, Fintype (C i)] [∀ i, LinearOrder (C i)] in
private theorem weight_total (p : PMF α) : ∑ x, (p x).toReal = 1 := by
  have h : ∑ x, p x = 1 := (tsum_fintype p).symm.trans p.tsum_coe
  rw [← ENNReal.toReal_sum (fun x _ => p.apply_ne_top x), h]
  simp

omit [Fintype ι] [∀ i, Fintype (C i)] [∀ i, LinearOrder (C i)] in
private theorem centered_total (p : PMF α) (f : α → ℝ) :
    ∑ x, (p x).toReal * (f x - expect p f) = 0 := by
  simp only [mul_sub, sum_sub_distrib, ← sum_mul, weight_total, one_mul, expect, sub_self]

omit [Fintype ι] [∀ i, Fintype (C i)] [∀ i, LinearOrder (C i)] in
private theorem centered_cov [Preorder α] (p : PMF α) (f g : α → ℝ)
    (hg : Monotone g)
    (h : ∀ U : Set α, IsUpperSet U →
      ∑ x ∈ U.toFinset, (p x).toReal * (f x - expect p f) ≤ 0) : cov p f g ≤ 0 := by
  have hsign := upper_test_induction (fun x => (p x).toReal * (f x - expect p f))
    (centered_total p f) (fun U hU => ?_) g hg
  · have he (x : α) : (p x).toReal * (f x - expect p f) * g x =
        (p x).toReal * (f x * g x) - (p x).toReal * g x * expect p f := by ring
    simp only [he, sum_sub_distrib, ← sum_mul] at hsign
    change expect p (fun x => f x * g x) - expect p g * expect p f ≤ 0 at hsign
    simpa only [cov, mul_comm (expect p f)] using hsign
  · convert h U hU using 1
    rw [show U.toFinset = univ.filter (fun x => x ∈ U) by ext x; simp, sum_filter]
    apply sum_congr rfl
    intro x _
    by_cases hx : x ∈ U <;> simp [event, hx]

omit [Fintype ι] [∀ i, Fintype (C i)] [∀ i, LinearOrder (C i)] in
private theorem cov_marginal [Fintype β] (p : PMF α) (q : α → β) (f : α → ℝ) (g : β → ℝ) :
    cov p f (g ∘ q) = cov (p.map q) (fun y => cond p q y f) g := by
  have hm := tower_mul p q f (fun _ => 1)
  simp only [mul_one] at hm
  rw [cov, cov, tower_mul, hm, expect_map]
  rfl

open ThreeBitCubeConditionalMeans in
omit [Fintype ι] [∀ i, Fintype (C i)] [∀ i, LinearOrder (C i)] in
/-- A cube-valued projection has nonpositive covariance with an increasing test
when the score has antitone conditional means on all its positive subfibers. -/
private theorem cube_cov_nonpos (p : PMF α) (q : α → Fin 3 → Fin 2) (f : α → ℝ)
    (g : (Fin 3 → Fin 2) → ℝ) (hg : Monotone g)
    (hr : ∀ (T : Finset (Fin 3)) (a b : T → Fin 2), a ≤ b →
      0 < mass p (project T ∘ q) a → 0 < mass p (project T ∘ q) b →
        cond p (project T ∘ q) b f ≤ cond p (project T ∘ q) a f) :
    cov p f (g ∘ q) ≤ 0 := by
  rw [cov_marginal]
  apply centered_cov _ _ _ hg
  apply centered_sum_nonpos_of_antitone_fiber_means
  intro T a b hab ha hb
  have hfiber (c : T → Fin 2) :
      (fiber T c).toFinset = univ.filter (fun x => project T x = c) := by
    ext x
    rw [Set.mem_toFinset]
    simp only [mem_filter, mem_univ, true_and]
    rfl
  have hm (c : T → Fin 2) : fiberMass (p.map q) T c = mass p (project T ∘ q) c := by
    rw [← (tower p q (project T) c f).2]
    rw [fiberMass, hfiber, mass, fiberSum]
    exact Finset.sum_congr (by ext x; simp) (fun _ _ => rfl)
  have hc (c : T → Fin 2) :
      fiberMean (p.map q) (fun y => cond p q y f) T c = cond p (project T ∘ q) c f := by
    rw [← (tower p q (project T) c f).1]
    rw [fiberMean, hfiber, cond, hm, ← (tower p q (project T) c f).2, fiberSum]
    apply congrArg (· / mass (p.map q) (project T) c)
    exact Finset.sum_congr (by ext x; simp) (fun _ _ => rfl)
  rw [hc, hc]
  exact hr T a b hab (hm a ▸ ha) (hm b ▸ hb)

section SmallBlocks

variable {X Y : Type*} [Fintype X] [Fintype Y]

private def center (p : PMF X) (f : X → ℝ) (x : X) :=
  (p x).toReal * (f x - expect p f)

/-- Conditional score decreases between every pair of comparable positive fibers. -/
private def AntitoneConditionalMeans [Preorder Y] (p : PMF X) (q : X → Y) (f : X → ℝ) : Prop :=
  ∀ a b, a ≤ b → 0 < mass p q a → 0 < mass p q b → cond p q b f ≤ cond p q a f

private theorem descending_marginal [Preorder γ] (p : PMF X) (q : X → Y) (r : Y → γ)
    (f : X → ℝ) (h : AntitoneConditionalMeans p (r ∘ q) f) :
    AntitoneConditionalMeans (p.map q) r (fun y => cond p q y f) := by
  intro a b hab ha hb
  rw [(tower p q r a f).2] at ha
  rw [(tower p q r b f).2] at hb
  rw [(tower p q r a f).1, (tower p q r b f).1]
  exact h a b hab ha hb

private theorem no_reverse [Preorder Y] {p : PMF X} {q : X → Y} {f : X → ℝ}
    (h : AntitoneConditionalMeans p q f) {a b : Y} (hab : a ≤ b)
    (ha : fiberSum q a (center p f) < 0) (hb : 0 < fiberSum q b (center p f)) : False := by
  have heq (y : Y) :
      fiberSum q y (center p f) = mass p q y * (cond p q y f - expect p f) := by
    rw [mul_sub, mass_mul_cond]
    simp only [mass, fiberSum, sum_mul, center, mul_sub, sum_sub_distrib]
  rw [heq] at ha hb
  have hp (y : Y) : 0 ≤ mass p q y := mass_nonneg p q y
  have hpa : 0 < mass p q a := by
    by_contra! hn
    rw [le_antisymm hn (hp a), zero_mul] at ha
    exact (lt_irrefl _ ha)
  have hpb : 0 < mass p q b := by
    by_contra! hn
    rw [le_antisymm hn (hp b), zero_mul] at hb
    exact (lt_irrefl _ hb)
  have hneg := neg_of_mul_neg_right ha hpa.le
  have hpos := pos_of_mul_pos_right hb (hp b)
  linarith only [hneg, hpos, h a b hab hpa hpb]

private theorem fiber_id (w : X → ℝ) (x : X) : fiberSum id x w = w x := by
  rw [fiberSum, show (univ.filter (fun y => id y = x)) = {x} by ext y; simp, sum_singleton]

private theorem tail_nonpos {L : Type*} [Fintype L] [LinearOrder L] (w : L → ℝ)
    (h : ∀ a b, a ≤ b → w a < 0 → 0 < w b → False) (ht : ∑ a, w a ≤ 0)
    (U : Set L) (hU : IsUpperSet U) : ∑ a ∈ U.toFinset, w a ≤ 0 := by
  by_contra! hpos
  obtain ⟨b, hb, hwb⟩ : ∃ b ∈ U.toFinset, 0 < w b := by
    by_contra! hn
    exact hpos.not_ge (sum_nonpos hn)
  have hsub := Finset.sum_sdiff (s₁ := U.toFinset) (s₂ := univ) (f := w) (subset_univ _)
  have hcomp : 0 ≤ ∑ a ∈ univ \ U.toFinset, w a := by
    apply sum_nonneg
    intro a ha
    by_contra! hwa
    have hle : a ≤ b := le_of_not_ge (fun hba => (mem_sdiff.mp ha).2
      (Set.mem_toFinset.mpr (hU hba (Set.mem_toFinset.mp hb))))
    exact h a b hle hwa hwb
  linarith only [hpos, hcomp, hsub, ht]

/-- A chain-valued projection has nonpositive covariance with an increasing test
if the conditional score is antitone on comparable positive fibers. -/
private theorem chain_cov_nonpos {L : Type*} [LinearOrder L] [Fintype L]
    (p : PMF X) (q : X → L) (f : X → ℝ) (g : L → ℝ) (hg : Monotone g)
    (h : AntitoneConditionalMeans p q f) : cov p f (g ∘ q) ≤ 0 := by
  rw [cov_marginal]
  apply centered_cov _ _ _ hg
  intro U hU
  let r := p.map q
  let s := fun y => cond p q y f
  have hd : AntitoneConditionalMeans r id s := descending_marginal p q id f h
  refine tail_nonpos (center r s) (fun a b hab ha hb => ?_) (centered_total r s).le U hU
  exact no_reverse hd hab (by rwa [fiber_id]) (by rwa [fiber_id])

private theorem row_fiber {L : Type*} [Fintype L] (w : Fin 2 × L → ℝ) (b : Fin 2) :
    fiberSum Prod.fst b w = ∑ x, w (b, x) := by
  have hb : b = 0 ∨ b = 1 := by decide +revert
  rw [fiberSum, sum_filter, Fintype.sum_prod_type, Fin.sum_univ_two]
  rcases hb with rfl | rfl <;> simp

private theorem col_fiber {L : Type*} [Fintype L] (w : Fin 2 × L → ℝ) (x : L) :
    fiberSum Prod.snd x w = w (0, x) + w (1, x) := by
  rw [fiberSum, sum_filter, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp

private theorem pair_event {L : Type*} [Fintype L] (w : Fin 2 × L → ℝ)
    (U : Set (Fin 2 × L)) :
    ∑ z ∈ U.toFinset, w z =
      (∑ x ∈ {x | (0, x) ∈ U}.toFinset, w (0, x)) +
      (∑ x ∈ {x | (1, x) ∈ U}.toFinset, w (1, x)) := by
  have hs : ∀ (V : Set (Fin 2 × L)), V.toFinset = univ.filter (· ∈ V) := by
    intro V
    ext z
    rw [Set.mem_toFinset, mem_filter_univ]
  have hs' : ∀ (V : Set L), V.toFinset = univ.filter (· ∈ V) := by
    intro V
    ext z
    rw [Set.mem_toFinset, mem_filter_univ]
  rw [hs, hs', hs', sum_filter, sum_filter, sum_filter, Fintype.sum_prod_type, Fin.sum_univ_two]
  rfl

private theorem pair_centered {L : Type*} [LinearOrder L] [Fintype L] (p : PMF (Fin 2 × L))
    (f : Fin 2 × L → ℝ) (hrow : AntitoneConditionalMeans p Prod.fst f) (hcol : AntitoneConditionalMeans p Prod.snd f)
    (hpoint : AntitoneConditionalMeans p id f) {U : Set (Fin 2 × L)} (hU : IsUpperSet U) :
    ∑ z ∈ U.toFinset, center p f z ≤ 0 := by
  let w := center p f
  have htot : (∑ x, w (0, x)) + (∑ x, w (1, x)) = 0 := by
    have h := centered_total p f
    rwa [Fintype.sum_prod_type, Fin.sum_univ_two] at h
  have hrow1 : ∑ x, w (1, x) ≤ 0 := by
    by_contra! hp
    have hn : ∑ x, w (0, x) < 0 := by linarith only [htot, hp]
    exact no_reverse hrow (show (0 : Fin 2) ≤ 1 by decide)
      (by rwa [row_fiber]) (by rwa [row_fiber])
  let U0 : Set L := {x | (0, x) ∈ U}
  let U1 : Set L := {x | (1, x) ∈ U}
  have hu1 : IsUpperSet U1 := fun a b hab hx =>
    hU (show ((1 : Fin 2), a) ≤ (1, b) from ⟨le_rfl, hab⟩) hx
  have hsub : U0.toFinset ⊆ U1.toFinset := by
    intro x hx
    have hm : x ∈ U0 := Set.mem_toFinset.mp hx
    have h01 : (0 : Fin 2) ≤ 1 := by decide
    exact Set.mem_toFinset.mpr (hU (show ((0 : Fin 2), x) ≤ (1, x) from ⟨h01, le_rfl⟩) hm)
  have htail1 : ∑ x ∈ U1.toFinset, w (1, x) ≤ 0 :=
    tail_nonpos (fun x => w (1, x)) (fun a b hab ha hb =>
      no_reverse hpoint (show ((1 : Fin 2), a) ≤ (1, b) from ⟨le_rfl, hab⟩)
        (by rwa [fiber_id]) (by rwa [fiber_id])) hrow1 U1 hu1
  have htotCol : ∑ x, (w (0, x) + w (1, x)) ≤ 0 := by rw [sum_add_distrib, htot]
  have htailCol : ∑ x ∈ U1.toFinset, (w (0, x) + w (1, x)) ≤ 0 :=
    tail_nonpos (fun x => w (0, x) + w (1, x)) (fun a b hab ha hb =>
      no_reverse hcol hab (by rwa [col_fiber]) (by rwa [col_fiber])) htotCol U1 hu1
  by_contra! hpos
  rw [pair_event] at hpos
  have h0 : 0 < ∑ x ∈ U0.toFinset, w (0, x) := by linarith only [hpos, htail1]
  obtain ⟨b, hb, hwb⟩ : ∃ b ∈ U0.toFinset, 0 < w (0, b) := by
    by_contra! hn
    exact h0.not_ge (sum_nonpos hn)
  have hgap : 0 ≤ ∑ a ∈ U1.toFinset \ U0.toFinset, w (0, a) := by
    apply sum_nonneg
    intro a ha
    have hmem : b ∈ U0 := Set.mem_toFinset.mp hb
    have hab : a ≤ b := le_of_not_ge (fun hba => (mem_sdiff.mp ha).2
      (Set.mem_toFinset.mpr (hU (show ((0 : Fin 2), b) ≤ (0, a) from ⟨le_rfl, hba⟩) hmem)))
    by_contra! hwa
    exact no_reverse hpoint (show ((0 : Fin 2), a) ≤ (0, b) from ⟨le_rfl, hab⟩)
      (by rwa [fiber_id]) (by rwa [fiber_id])
  have hsplit := Finset.sum_sdiff (f := fun x => w (0, x)) hsub
  rw [sum_add_distrib] at htailCol
  linarith only [hpos, htailCol, hgap, hsplit]

/-- A binary-by-chain marginal has nonpositive covariance with an increasing test
under antitone conditional scores on rows, columns, and points. -/
private theorem binary_chain_cov_nonpos {L : Type*} [LinearOrder L] [Fintype L]
    (p : PMF X) (q : X → Fin 2 × L) (f : X → ℝ) (g : Fin 2 × L → ℝ) (hg : Monotone g)
    (hrow : AntitoneConditionalMeans p (Prod.fst ∘ q) f) (hcol : AntitoneConditionalMeans p (Prod.snd ∘ q) f)
    (hpoint : AntitoneConditionalMeans p q f) : cov p f (g ∘ q) ≤ 0 := by
  rw [cov_marginal]
  apply centered_cov _ _ _ hg
  intro U hU
  exact pair_centered _ _ (descending_marginal p q Prod.fst f hrow)
    (descending_marginal p q Prod.snd f hcol) (descending_marginal p q id f hpoint) hU

end SmallBlocks

section MarginalSupport

private abbrev CoordinateSupport (p : PMF (∀ i, C i)) (i : ι) :=
  ((p.map (fun x => x i)).support : Set (C i))

private theorem coordinate_mem (p : PMF (∀ i, C i)) {x : ∀ i, C i}
    (hx : x ∈ p.support) (i : ι) : x i ∈ CoordinateSupport p i :=
  (PMF.mem_support_map_iff _ _ _).mpr ⟨x, hx, rfl⟩

private def supportDefault (p : PMF (∀ i, C i)) (i : ι) : CoordinateSupport p i :=
  ⟨p.support_nonempty.choose i, coordinate_mem p p.support_nonempty.choose_spec i⟩

private def encodeSupport (p : PMF (∀ i, C i)) (x : ∀ i, C i) (i : ι) :
    CoordinateSupport p i :=
  if h : x i ∈ CoordinateSupport p i then ⟨x i, h⟩ else supportDefault p i

private theorem encodeSupport_val (p : PMF (∀ i, C i)) {x : ∀ i, C i}
    (hx : x ∈ p.support) (i : ι) : (encodeSupport p x i).val = x i := by
  unfold encodeSupport
  rw [dite_eq_left (coordinate_mem p hx i)]

private theorem fiber_congr_support (p : PMF α) (q : α → β) (r : α → γ) (b : β) (c : γ)
    (h : ∀ x ∈ p.support, q x = b ↔ r x = c) (f : α → ℝ) :
    fiberSum q b (fun x => (p x).toReal * f x) = fiberSum r c (fun x => (p x).toReal * f x) := by
  simp only [fiberSum, sum_filter]
  apply sum_congr rfl
  intro x _
  by_cases hx : x ∈ p.support
  · by_cases hb : q x = b
    · rw [ite_eq_left hb, ite_eq_left ((h x hx).mp hb)]
    · rw [ite_eq_right hb, ite_eq_right (fun hc => hb ((h x hx).mpr hc))]
  · have hz : p x = 0 := Classical.not_not.mp hx
    simp [hz]

private theorem cond_congr_support (p : PMF α) (q : α → β) (r : α → γ) (b : β) (c : γ)
    (h : ∀ x ∈ p.support, q x = b ↔ r x = c) (f : α → ℝ) :
    mass p q b = mass p r c ∧ cond p q b f = cond p r c f := by
  have hm : mass p q b = mass p r c := by
    simpa only [mul_one, mass] using fiber_congr_support p q r b c h (fun _ => 1)
  exact ⟨hm, by rw [cond, cond, hm, fiber_congr_support p q r b c h]⟩

private theorem cond_congr_score (p : PMF α) (q : α → β) (b : β) {f g : α → ℝ}
    (h : ∀ x ∈ p.support, f x = g x) : cond p q b f = cond p q b g := by
  unfold cond fiberSum
  apply congrArg (· / mass p q b)
  apply sum_congr rfl
  intro x _
  by_cases hx : x ∈ p.support
  · exact congrArg ((p x).toReal * ·) (h x hx)
  · have hz : p x = 0 := Classical.not_not.mp hx
    simp [hz]

private theorem supported_fiber (p : PMF (∀ i, C i)) (J : Finset ι)
    (a : ∀ i : J, CoordinateSupport p i) (x : ∀ i, C i) (hx : x ∈ p.support) :
    (project J (encodeSupport p x) = a) ↔
      project J x = (fun i => (a i).val) := by
  simp only [funext_iff, project]
  exact forall_congr' (fun i => by
    constructor
    · intro h
      simpa only [encodeSupport_val p hx i] using congrArg Subtype.val h
    · intro h
      exact Subtype.ext ((encodeSupport_val p hx i).trans h))

private theorem support_nrd (p : PMF (∀ i, C i)) (hp : FullNRD p) :
    FullNRD (p.map (encodeSupport p)) := by
  intro I J hd f hf a b hab ha hb
  let extend (x : ∀ i : I, C i) : ℝ :=
    sSup (Set.insert (sInf (Set.range f))
      {v | ∃ y : ∀ i : I, CoordinateSupport p i, (∀ i, (y i).val ≤ x i) ∧ f y = v})
  have hfinite (x : ∀ i : I, C i) :
      (Set.insert (sInf (Set.range f))
        {v | ∃ y : ∀ i : I, CoordinateSupport p i, (∀ i, (y i).val ≤ x i) ∧ f y = v}).Finite := by
    refine ((Set.finite_range f).subset ?_).insert _
    rintro v ⟨y, _, rfl⟩
    exact ⟨y, rfl⟩
  have hext : Monotone extend := by
    intro x y hxy
    apply csSup_le_csSup (hfinite y).bddAbove (Set.insert_nonempty _ _)
    intro v hv
    rcases hv with hv | ⟨z, hz, rfl⟩
    · exact Or.inl hv
    · exact Or.inr ⟨z, fun i => (hz i).trans (hxy i), rfl⟩
  have heq (y : ∀ i : I, CoordinateSupport p i) : extend (fun i => (y i).val) = f y := by
    apply le_antisymm
    · apply csSup_le (Set.insert_nonempty _ _)
      intro v hv
      rcases hv with hv | ⟨z, hz, rfl⟩
      · exact hv ▸ csInf_le (Set.finite_range f).bddBelow ⟨y, rfl⟩
      · exact hf hz
    · apply le_csSup (hfinite _).bddAbove
      exact Or.inr ⟨y, fun _ => le_rfl, rfl⟩
  let read (c : ∀ i : J, CoordinateSupport p i) : ∀ i : J, C i := fun i => (c i).val
  let r := project J ∘ encodeSupport p
  let score := (f ∘ project I) ∘ encodeSupport p
  have hagree (x : ∀ i, C i) (hx : x ∈ p.support) : score x = (extend ∘ project I) x := by
    have h : (fun i : I => (encodeSupport p x i).val) = project I x :=
      funext (fun i => encodeSupport_val p hx i)
    calc
      score x = extend (fun i : I => (encodeSupport p x i).val) :=
        (heq (project I (encodeSupport p x))).symm
      _ = (extend ∘ project I) x := congrArg extend h
  have htransport (c : ∀ i : J, CoordinateSupport p i) :
      mass (p.map (encodeSupport p)) (project J) c = mass p (project J) (read c) ∧
      cond (p.map (encodeSupport p)) (project J) c (f ∘ project I) =
        cond p (project J) (read c) (extend ∘ project I) := by
    have hm := (tower p (encodeSupport p) (project J) c score).2
    have hnum :
        fiberSum (project J) c (fun y => (p.map (encodeSupport p) y).toReal *
          (f ∘ project I) y) = fiberSum r c (fun x => (p x).toReal * score x) := by
      let g (y : ∀ i, CoordinateSupport p i) : ℝ :=
        if project J y = c then (f ∘ project I) y else 0
      have H := expect_map p (encodeSupport p) g
      calc
        _ = expect (p.map (encodeSupport p)) g := by
          simp only [fiberSum, sum_filter, expect]
          apply sum_congr rfl
          intro x _
          by_cases hx : project J x = c <;> simp [g, hx]
        _ = expect p (g ∘ encodeSupport p) := H
        _ = _ := by
          simp only [fiberSum, sum_filter, expect]
          apply sum_congr rfl
          intro x _
          by_cases hx : project J (encodeSupport p x) = c <;> simp [r, score, g, hx]
    have hc :
        cond (p.map (encodeSupport p)) (project J) c (f ∘ project I) = cond p r c score := by
      rw [cond, cond, hm, hnum]
    have hfib := cond_congr_support p r (project J) c (read c) (supported_fiber p J c) score
    exact ⟨hm.trans hfib.1, hc.trans (hfib.2.trans
      (cond_congr_score p (project J) (read c) hagree))⟩
  rw [(htransport a).1] at ha
  rw [(htransport b).1] at hb
  rw [(htransport a).2, (htransport b).2]
  exact hp I J hd extend hext (read a) (read b) hab ha hb

private theorem support_na (p : PMF (∀ i, C i)) (hp : NA (p.map (encodeSupport p))) : NA p := by
  intro I J hd f g hf hg
  let f' (x : ∀ i : I, CoordinateSupport p i) := f (fun i => (x i).val)
  let g' (x : ∀ i : J, CoordinateSupport p i) := g (fun i => (x i).val)
  have h := hp I J hd f' g' (fun _ _ hab => hf hab) (fun _ _ hab => hg hab)
  have heq (K : Finset ι) (x : ∀ i, C i) (hx : x ∈ p.support) :
      (fun i : K => (encodeSupport p x i).val) = project K x :=
    funext (fun i => encodeSupport_val p hx i)
  unfold cov at h ⊢
  rw [expect_map, expect_map, expect_map] at h
  have he {s t : (∀ i, C i) → ℝ} (h : ∀ x ∈ p.support, s x = t x) : expect p s = expect p t := by
    apply sum_congr rfl
    intro x _
    by_cases hx : x ∈ p.support
    · rw [h x hx]
    · have hz : p x = 0 := Classical.not_not.mp hx
      simp [hz]
  rw [← he (t := f ∘ project I) (fun x hx => congrArg f (heq I x hx)),
    ← he (t := g ∘ project J) (fun x hx => congrArg g (heq J x hx)),
    ← he (t := fun x => (f ∘ project I) x * (g ∘ project J) x)
      (fun x hx => congrArg₂ (· * ·) (congrArg f (heq I x hx)) (congrArg g (heq J x hx)))]
  exact h

private theorem transport_desc {X Y Z : Type*} [Fintype X] [Preorder Y] [Preorder Z]
    {p : PMF X} {q : X → Y} {r : X → Z} {f : X → ℝ} (d : Z → Y) (hd : Monotone d)
    (he : ∀ x z, r x = z ↔ q x = d z)
    (h : AntitoneConditionalMeans p q f) : AntitoneConditionalMeans p r f := by
  intro a b hab ha hb
  have htransport (z : Z) := cond_congr_support p r q z (d z) (fun x _ => he x z) f
  rw [(htransport a).1] at ha
  rw [(htransport b).1] at hb
  rw [(htransport a).2, (htransport b).2]
  exact h _ _ (hd hab) ha hb

private theorem reindexed_subblock {κ : Type*} {D : κ → Type*} [∀ k, Preorder (D k)]
    (p : PMF (∀ i, C i)) (I S : Finset ι) (e : κ ≃ S)
    (o : ∀ k, D k ≃o C (e k : ι)) (hIS : Disjoint I S)
    {f : (∀ i : I, C i) → ℝ} (hf : Monotone f) (hp : FullNRD p) (T : Finset κ) :
    AntitoneConditionalMeans p (project T ∘ fun x k => (o k).symm (x (e k))) (f ∘ project I) := by
  let E : κ ↪ ι := e.toEmbedding.trans (Function.Embedding.subtype _)
  let U := T.map E
  let ET : T ≃ U := T.equivMap E
  let row (a : ∀ k : T, D k) (k : T) : C (ET k : U) := o k (a k)
  let decode (a : ∀ k : T, D k) : ∀ j : U, C j :=
    (ET.piCongrLeft fun j : U => C j) (row a)
  have hdecode (a : ∀ k : T, D k) (k : T) : decode a (ET k) = o k (a k) := by
    exact Equiv.piCongrLeft_apply_apply (fun j : U => C j) ET (row a) k
  have hmon : Monotone decode := by
    intro a b hab j
    obtain ⟨k, rfl⟩ := ET.surjective j
    simp only [hdecode]
    exact (o k).monotone (hab k)
  refine transport_desc (q := project U) decode hmon (fun x a => ?_) ?_
  · constructor
    · intro h
      funext j
      obtain ⟨k, rfl⟩ := ET.surjective j
      change x (e k) = decode a (ET k)
      rw [hdecode, ← congrFun h k]
      exact ((o k).apply_symm_apply _).symm
    · intro h
      funext k
      change (o k).symm (x (e k)) = a k
      have hh : x (e k) = decode a (ET k) := congrFun h (ET k)
      rw [hh, hdecode, OrderIso.symm_apply_apply]
  · intro a b hab ha hb
    apply hp I U (Disjoint.mono_right ?_ hIS) f hf a b hab ha hb
    intro i hi
    obtain ⟨k, _, rfl⟩ := mem_map.mp hi
    exact (e k).property

private theorem reindexed_test {κ : Type*} {D : κ → Type*} [∀ k, Preorder (D k)]
    (base : ∀ i, C i) (J S : Finset ι) (hs : S ⊆ J) (e : κ ≃ S)
    (o : ∀ k, D k ≃o C (e k : ι))
    (h1 : ∀ i ∈ J, i ∉ S → Subsingleton (C i))
    {g : (∀ j : J, C j) → ℝ} (hg : Monotone g) :
    ∃ g' : (∀ k, D k) → ℝ, Monotone g' ∧
      g ∘ project J = g' ∘ (fun x k => (o k).symm (x (e k))) := by
  let decodeS : (∀ k, D k) ≃ (∀ j : S, C j) :=
    (Equiv.piCongrRight fun k => (o k).toEquiv).trans (e.piCongrLeft fun j : S => C j)
  have hdecode (a : ∀ k, D k) (k : κ) : decodeS a (e k) = o k (a k) := by
    unfold decodeS
    rw [Equiv.trans_apply, Equiv.piCongrLeft_apply_apply]
    rfl
  have hds (a b : ∀ k, D k) (hab : a ≤ b) (j : S) : decodeS a j ≤ decodeS b j := by
    obtain ⟨k, rfl⟩ := e.surjective j
    rw [hdecode, hdecode]
    exact (o k).monotone (hab k)
  have hx (x : ∀ i, C i) (j : S) :
      decodeS (fun k => (o k).symm (x (e k))) j = x j := by
    obtain ⟨k, rfl⟩ := e.surjective j
    rw [hdecode, OrderIso.apply_symm_apply]
  let decode (a : ∀ k, D k) (j : J) : C j :=
    if hj : (j : ι) ∈ S then decodeS a ⟨j, hj⟩ else base j
  refine ⟨g ∘ decode, hg.comp ?_, ?_⟩
  · intro a b hab j
    unfold decode
    split
    · rename_i hj
      exact hds a b hab ⟨j, hj⟩
    · exact le_rfl
  · funext x
    apply congrArg g
    funext j
    symm
    unfold decode
    split
    · rename_i hj
      exact hx x ⟨j, hj⟩
    · rename_i hj
      haveI := h1 j j.property hj
      exact Subsingleton.elim _ _

private theorem desc_point {X κ : Type*} [Fintype X] {D : κ → Type*} [∀ i, Preorder (D i)]
    {p : PMF X} {q : X → ∀ k, D k} {f : X → ℝ}
    (h : ∀ T : Finset κ, AntitoneConditionalMeans p (project T ∘ q) f)
    [Fintype κ] : AntitoneConditionalMeans p q f := by
  let d (a : ∀ k, D k) (k : (univ : Finset κ)) := a k
  have hd : Monotone d := fun _ _ hab i => hab i
  apply transport_desc (q := project (univ : Finset κ) ∘ q) d hd ?_ (h univ)
  intro x a
  exact ⟨fun he => congrArg (project univ) he,
    fun he => funext (fun i => congrFun he ⟨i, mem_univ _⟩)⟩

private theorem desc_coordinate {X κ : Type*} [Fintype X] {D : κ → Type*} [∀ i, Preorder (D i)]
    {p : PMF X} {q : X → ∀ k, D k} {f : X → ℝ}
    (h : ∀ T : Finset κ, AntitoneConditionalMeans p (project T ∘ q) f)
    (k : κ) : AntitoneConditionalMeans p (fun x => q x k) f := by
  let d (a : D k) (i : ({k} : Finset κ)) : D i :=
    cast (congrArg D (mem_singleton.mp i.property).symm) a
  have hd (a : D k) : d a ⟨k, mem_singleton_self k⟩ = a := rfl
  refine transport_desc (q := project {k} ∘ q) d ?_ (fun x a => ?_) (h {k})
  · intro a b hab i
    rcases i with ⟨i, hi⟩
    change i ∈ ({k} : Finset κ) at hi
    obtain rfl := mem_singleton.mp hi
    exact hab
  · constructor
    · intro he
      funext i
      rcases i with ⟨i, hi⟩
      change i ∈ ({k} : Finset κ) at hi
      obtain rfl := mem_singleton.mp hi
      exact he
    · intro he
      exact (congrFun he ⟨k, mem_singleton_self k⟩).trans (hd a)

private theorem cov_comm (p : PMF α) (f g : α → ℝ) : cov p f g = cov p g f := by
  unfold cov
  rw [mul_comm (expect p f), show (fun x => f x * g x) = (fun x => g x * f x)
    from funext (fun x => mul_comm _ _)]

private theorem cov_const (p : PMF α) (f : α → ℝ) (r : ℝ) :
    cov p f (fun _ => r) = 0 := by
  have h (x : α) : (p x).toReal * (f x * r) = ((p x).toReal * f x) * r := by ring
  simp only [cov, expect, h, ← sum_mul, weight_total, one_mul, sub_self]

private theorem small_block (p : PMF (∀ i, C i)) (hp : FullNRD p) (I J : Finset ι)
    (hd : Disjoint I J) (hsize : (∏ i ∈ J, Fintype.card (C i)) ≤ 8)
    (f : (∀ i : I, C i) → ℝ) (g : (∀ j : J, C j) → ℝ) (hf : Monotone f) (hg : Monotone g) :
    cov p (f ∘ project I) (g ∘ project J) ≤ 0 := by
  let base := p.support_nonempty.choose
  let d (i : ι) := Fintype.card (C i)
  have hpos (i : ι) : 1 ≤ d i := Fintype.card_pos_iff.mpr ⟨base i⟩
  let S := J.filter (fun i => 2 ≤ d i)
  have hs : S ⊆ J := filter_subset _ _
  have h1 (i : ι) (hi : i ∈ J) (hn : i ∉ S) : Subsingleton (C i) := by
    apply Fintype.card_le_one_iff_subsingleton.mp
    by_contra! h
    exact hn (mem_filter.mpr ⟨hi, h⟩)
  have h2 (i : ι) (hi : i ∈ S) : 2 ≤ d i := (mem_filter.mp hi).2
  have hsSize : ∏ i ∈ S, d i ≤ 8 :=
    (prod_le_prod_of_subset_of_one_le hs (fun i _ _ => hpos i)).trans hsize
  have hpow (U : Finset ι) (hU : U ⊆ S) : 2 ^ U.card ≤ ∏ i ∈ U, d i := by
    rw [← prod_const]
    exact prod_le_prod (fun i hi => h2 i (hU hi))
  have hcard : S.card ≤ 3 := by
    by_contra! hc
    have hh : 2 ^ 4 ≤ 2 ^ S.card := Nat.pow_le_pow_right (by decide) hc
    have H := hh.trans ((hpow S (Subset.refl _)).trans hsSize)
    omega
  let score := f ∘ project I
  have hdS := Disjoint.mono_right hs hd
  interval_cases cardS : S.card
  · have hempty : S = ∅ := card_eq_zero.mp cardS
    have hab (x : ∀ i, C i) : project J x = project J base := by
      funext j
      haveI := h1 j j.property (by simp [hempty])
      exact Subsingleton.elim _ _
    have H : g ∘ project J = fun _ => g (project J base) :=
      funext (fun x => congrArg g (hab x))
    rw [H, cov_const]
  · let e : Fin 1 ≃ S := (S.equivFinOfCardEq cardS).symm
    let o (k : Fin 1) : C (e k : ι) ≃o C (e k : ι) := OrderIso.refl _
    obtain ⟨g', hg', he⟩ := reindexed_test base J S hs e o h1 hg
    let q (x : ∀ i, C i) (k : Fin 1) := x (e k)
    have hr (T : Finset (Fin 1)) : AntitoneConditionalMeans p (project T ∘ q) score :=
      reindexed_subblock p I S e o hdS hf hp T
    let r (x : ∀ i, C i) := q x 0
    let decode (a : C (e 0 : ι)) (k : Fin 1) : C (e k : ι) := Fin.cases a (fun i => (Nat.not_lt_zero i.val i.isLt).elim) k
    have hdecode : Monotone decode := by
      intro a b h k
      fin_cases k
      exact h
    have hrec (x : ∀ i, C i) : decode (r x) = q x := by
      funext k
      fin_cases k
      rfl
    rw [he]
    change cov p score (g' ∘ q) ≤ 0
    rw [show g' ∘ q = (g' ∘ decode) ∘ r from
      funext (fun x => congrArg g' (hrec x).symm)]
    exact chain_cov_nonpos p r score _ (hg'.comp hdecode) (desc_coordinate hr 0)
  · have ht : ∃ i ∈ S, d i = 2 := by
      by_contra! h
      have H : 3 ^ S.card ≤ ∏ i ∈ S, d i := by
        rw [← prod_const]
        exact prod_le_prod (fun i hi => by have := h2 i hi; have := h i hi; omega)
      rw [cardS] at H
      omega
    obtain ⟨i, hi, hi2⟩ := ht
    let e0 : Fin 2 ≃ S := (S.equivFinOfCardEq cardS).symm
    let e := (Equiv.swap (0 : Fin 2) (e0.symm ⟨i, hi⟩)).trans e0
    have he0 : e 0 = ⟨i, hi⟩ := by simp [e]
    let D (k : Fin 2) := Fin (Fin.cases 2 (fun _ => d (e 1)) k)
    letI (k : Fin 2) : LinearOrder (D k) := inferInstanceAs (LinearOrder (Fin _))
    let o (k : Fin 2) : D k ≃o C (e k : ι) :=
      Fintype.orderIsoFinOfCardEq _ (by
        fin_cases k
        · change d (e 0) = 2
          rw [he0]
          exact hi2
        · rfl)
    obtain ⟨g', hg', he⟩ := reindexed_test base J S hs e o h1 hg
    let q (x : ∀ i, C i) (k : Fin 2) := (o k).symm (x (e k))
    let E := OrderIso.piFinTwoIso D
    let r := E ∘ q
    have hr (T : Finset (Fin 2)) : AntitoneConditionalMeans p (project T ∘ q) score :=
      reindexed_subblock p I S e o hdS hf hp T
    have hpair : AntitoneConditionalMeans p r score := by
      apply transport_desc (q := q) E.symm E.symm.monotone (fun x a => ?_) (desc_point hr)
      exact E.toEquiv.apply_eq_iff_eq_symm_apply
    rw [he]
    change cov p score (g' ∘ q) ≤ 0
    rw [show g' ∘ q = (g' ∘ E.symm) ∘ r from
      funext (fun x => congrArg g' (E.symm_apply_apply (q x)).symm)]
    exact binary_chain_cov_nonpos p r score _ (hg'.comp E.symm.monotone)
      (desc_coordinate hr 0) (desc_coordinate hr 1) hpair
  · have hd2 (i : ι) (hi : i ∈ S) : d i = 2 := by
      have hm := hpow (S.erase i) (erase_subset _ _)
      rw [card_erase_of_mem hi, cardS] at hm
      have hm' := Nat.mul_le_mul_right (d i) hm
      rw [prod_erase_mul S d hi] at hm'
      have := h2 i hi
      omega
    let e : Fin 3 ≃ S := (S.equivFinOfCardEq cardS).symm
    let o (k : Fin 3) : Fin 2 ≃o C (e k : ι) :=
      Fintype.orderIsoFinOfCardEq _ (hd2 _ (e k).property)
    obtain ⟨g', hg', he⟩ := reindexed_test base J S hs e o h1 hg
    rw [he]
    apply cube_cov_nonpos p _ score g' hg'
    exact fun T => reindexed_subblock p I S e o hdS hf hp T

private theorem na_of_product_lt (p : PMF (∀ i, C i)) (hn : FullNRD p)
    (hsize : (∏ i, Fintype.card (C i)) < 81) : NA p := by
  intro I J hd f g hf hg
  let d (i : ι) := Fintype.card (C i)
  have hprod : (∏ i ∈ I, d i) * (∏ i ∈ J, d i) < 81 := by
    rw [← prod_union hd]
    exact ((prod_le_prod_of_subset_of_one_le (subset_univ (I ∪ J)) (fun i _ _ =>
      Fintype.card_pos_iff.mpr ⟨p.support_nonempty.choose i⟩)).trans_lt hsize)
  by_cases hj : (∏ i ∈ J, d i) ≤ 8
  · exact small_block p hn I J hd hj f g hf hg
  · have hi : (∏ i ∈ I, d i) ≤ 8 := by
      by_contra! hh
      have H := Nat.mul_le_mul (show 9 ≤ ∏ i ∈ I, d i by omega)
        (show 9 ≤ ∏ i ∈ J, d i by omega)
      omega
    rw [cov_comm]
    exact small_block p hn J I hd.symm hi g f hg hf

/-- Every full-NRD finite law with actual marginal-support product below 81
is negatively associated. -/
theorem na_of_fullNRD_of_marginalProduct_lt_81 (p : PMF (∀ i, C i))
    (hn : FullNRD p) (hsize : marginalProduct p < 81) :
    ∀ (I J : Finset ι), Disjoint I J → ∀ (f : (∀ i : I, C i) → ℝ)
    (g : (∀ j : J, C j) → ℝ), Monotone f → Monotone g →
      cov p (f ∘ project I) (g ∘ project J) ≤ 0 := by
  show NA p
  apply support_na
  exact na_of_product_lt (p.map (encodeSupport p)) (support_nrd p hn) hsize

end MarginalSupport

end
end D5.S3.Analytic.Probability.FiniteNegativeRegression
