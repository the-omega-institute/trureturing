/- GID: D5/S3/Quantum/Fibers/FiniteRectangleTransport
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/FiniteRectangleTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rectangular controls realize exact phase sums on the positive five-mode fiber. -/

import D5.S3.Quantum.Fibers.InteriorProbabilityPhaseFiber
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

noncomputable section

namespace D5.S3.Quantum.Fibers.FiniteRectangleTransport

open Set Filter Topology AffineMap MeasureTheory
open D5.S3.Quantum.Fibers.InteriorProbabilityPhaseFiber

set_option autoImplicit false
set_option relaxedAutoImplicit false

abbrev Vec := Fin 5 → ℝ
abbrev State := ℝ × ℝ × Vec
abbrev Base := ℝ × ℝ × ℝ

def ValidBase (b : Base) : Prop :=
  0 < b.2.2 ∧ b.2.2 < 1 ∧ 0 < b.1 ∧ b.1 < 1-b.2.2 ∧
  0 < b.2.1 ∧ b.2.1 < 1-b.2.2

def lower (b : Base) : ℝ := max 0 (b.1+b.2.1-(1-b.2.2))
def upper (b : Base) : ℝ := min b.1 b.2.1

def probability (b : Base) (k : ℝ) : Vec :=
  ![1-b.2.2-b.1-b.2.1+k, b.1-k, b.2.2, b.2.1-k, k]

def direction : Vec := ![1,-1,0,-1,1]

def information (b : Base) (k : ℝ) : ℝ :=
  1/probability b k 0 + 1/probability b k 1 +
  1/probability b k 3 + 1/probability b k 4

def phaseWeight (b : Base) (k : ℝ) : Vec :=
  fun i => direction i / (probability b k i * information b k)

/-- The five affine probabilities form the existing strict simplex carrier. -/
def fiberProbability (b : Base) (k : ℝ) (hb : ValidBase b)
    (hk : k ∈ Ioo (lower b) (upper b)) : InteriorProbability 4 where
  weight := probability b k
  positive := by
    obtain ⟨hZ, _, _, _, _, _⟩ := hb
    have hlo := (max_lt_iff.mp hk.1)
    have hhi := (lt_min_iff.mp hk.2)
    intro i
    fin_cases i <;> simp [probability] <;> dsimp [lower, upper] at * <;> linarith
  total := by simp [probability, Fin.sum_univ_succ]; ring

/-- A leg's lifted phase slope obeys the transport law along its entire affine chart. -/
def LawfulLeg (w : ℝ → Vec) (L U : ℝ) (x y : State) : Prop :=
  x.1 ∈ Ioo L U ∧ y.1 ∈ Ioo L U ∧
  ∀ t ∈ Icc (0 : ℝ) 1, ∀ i,
    y.2.2 i-x.2.2 i = w ((lineMap x y t).1) i * (y.2.1-x.2.1)

/-- The actual real-time interpolation of a finite vertex list, with unit-time legs. -/
def polygon : List State → ℝ → State
  | [] => fun _ => 0
  | [x] => fun _ => x
  | x :: y :: rest => fun t =>
      if t ≤ 1 then lineMap x y t else polygon (y :: rest) (t-1)

private theorem polygon_zero (x : State) (xs : List State) :
    polygon (x :: xs) 0 = x := by
  cases xs <;> simp [polygon]

private theorem polygon_continuous (x : State) (xs : List State) :
    Continuous (polygon (x :: xs)) := by
  induction xs generalizing x with
  | nil => exact continuous_const
  | cons y ys ih =>
    apply Continuous.if_le (lipschitzWith_lineMap x y).continuous
      ((ih y).comp (continuous_id.sub continuous_const)) continuous_id continuous_const
    intro t ht
    change t = 1 at ht
    subst t
    simp [polygon_zero]

private theorem polygon_end (x : State) (xs : List State) :
    polygon (x :: xs) xs.length = (x :: xs).getLast (by simp) := by
  induction xs generalizing x with
  | nil => simp [polygon]
  | cons y ys ih =>
    cases ys with
    | nil => simp [polygon]
    | cons z zs =>
      have ht : ¬ ((y :: z :: zs).length : ℝ) ≤ 1 := by
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        have hn : 0 ≤ (zs.length : ℝ) := Nat.cast_nonneg _
        linarith
      change (if ((y :: z :: zs).length : ℝ) ≤ 1 then
        lineMap x y ((y :: z :: zs).length : ℝ) else
        polygon (y :: z :: zs) (((y :: z :: zs).length : ℝ)-1)) =
          (y :: z :: zs).getLast (by simp)
      rw [if_neg ht]
      rw [show ((y :: z :: zs).length : ℝ)-1 = (z :: zs).length by simp]
      simpa only [List.getLast_cons_cons] using ih y

/-- A continuous history with finite phase variation and affine transport charts. -/
def Admissible (b : Base) (N : ℕ) (q : ℝ → State) : Prop :=
  Continuous q ∧
  (∀ t ∈ Icc (0 : ℝ) N, (q t).1 ∈ Ioo (lower b) (upper b)) ∧
  BoundedVariationOn (fun t => (q t).2.1) (Icc (0 : ℝ) N) ∧
  (∀ j : ℕ, j < N → ∃ x y : State,
    EqOn q (fun t => lineMap x y (t-j)) (Icc (j : ℝ) (j+1)) ∧
    ∀ t ∈ Ioo (j : ℝ) (j+1), ∀ i,
      HasDerivAt (fun s => (q s).2.2 i)
        (phaseWeight b (q t).1 i * deriv (fun s => (q s).2.1) t) t) ∧
  (∀ i, IntervalIntegrable
    (fun t => phaseWeight b (q t).1 i * deriv (fun s => (q s).2.1) t) volume 0 N ∧
    (∫ t in (0 : ℝ)..N, phaseWeight b (q t).1 i * deriv (fun s => (q s).2.1) t) =
      (q N).2.2 i-(q 0).2.2 i) ∧
  (∀ j : ℕ, j < N → ∀ t ∈ Ioo (j : ℝ) (j+1), ∀ i,
    HasDerivAt (fun s => probability b (q s).1 i)
      (direction i * deriv (fun s => (q s).1) t) t)

private theorem polygon_tail (x y : State) (xs : List State) (t : ℝ) (ht : 1 ≤ t) :
    polygon (x :: y :: xs) t = polygon (y :: xs) (t-1) := by
  by_cases h : t ≤ 1
  · have he : t = 1 := le_antisymm h ht
    simp [polygon, he, polygon_zero]
  · simp [polygon, h]

private theorem polygon_charts (w : ℝ → Vec) (L U : ℝ) (x : State)
    (xs : List State) (h : List.IsChain (LawfulLeg w L U) (x :: xs)) :
    ∀ j : ℕ, j < xs.length → ∃ a c : State,
      LawfulLeg w L U a c ∧
      EqOn (polygon (x :: xs)) (fun t => lineMap a c (t-j)) (Icc (j : ℝ) (j+1)) := by
  induction xs generalizing x with
  | nil => simp
  | cons y ys ih =>
    obtain ⟨hxy, hys⟩ := List.isChain_cons_cons.mp h
    intro j hj
    cases j with
    | zero =>
      refine ⟨x, y, hxy, ?_⟩
      intro t ht
      have hle : t ≤ 1 := by simpa using ht.2
      simp [polygon, hle]
    | succ j =>
      obtain ⟨a, c, hac, he⟩ := ih y hys j (by simpa using hj)
      refine ⟨a, c, hac, ?_⟩
      intro t ht
      simp only [mem_Icc, Nat.cast_add, Nat.cast_one] at ht
      rw [polygon_tail x y ys t (by linarith)]
      have hh := he (by constructor <;> linarith :
        t-1 ∈ Icc (j : ℝ) (j+1))
      convert hh using 1 <;> push_cast <;> congr 1 <;> ring

private theorem polygon_inside (w : ℝ → Vec) (L U : ℝ) (x : State)
    (xs : List State) (hx : x.1 ∈ Ioo L U)
    (h : List.IsChain (LawfulLeg w L U) (x :: xs)) :
    ∀ t ∈ Icc (0 : ℝ) xs.length, (polygon (x :: xs) t).1 ∈ Ioo L U := by
  induction xs generalizing x with
  | nil => intro t ht; simpa [polygon] using hx
  | cons y ys ih =>
    obtain ⟨hxy, hys⟩ := List.isChain_cons_cons.mp h
    intro t ht
    by_cases hle : t ≤ 1
    · simp only [polygon, if_pos hle]
      have he : (lineMap x y t).1 = (1-t)*x.1+t*y.1 := by
        simp [lineMap_apply]; ring
      rw [he]
      exact (convex_Ioo (𝕜 := ℝ) L U) hxy.1 hxy.2.1
        (by linarith) ht.1 (by ring)
    · rw [polygon_tail x y ys t (by linarith)]
      exact ih y hxy.2.1 hys (t-1) (by
        simp only [mem_Icc, List.length_cons, Nat.cast_add, Nat.cast_one] at ht
        constructor <;> linarith)

private theorem coordinate_derivative (x y : State) (j : ℕ) (t : ℝ) (i : Fin 5) :
    HasDerivAt (fun s : ℝ => (lineMap x y (s-j)).2.2 i) (y.2.2 i-x.2.2 i) t := by
  have hf : (fun s : ℝ => (lineMap x y (s-j)).2.2 i) =
      (fun s : ℝ => (s-j)*(y.2.2 i-x.2.2 i)+x.2.2 i) := by
    funext s; simp [lineMap_apply, Pi.smul_apply, smul_eq_mul]
  rw [hf]
  simpa using (((hasDerivAt_id t).sub_const (j : ℝ)).mul_const
    (y.2.2 i-x.2.2 i)).add_const (x.2.2 i)

private theorem phase_derivative (x y : State) (j : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (lineMap x y (s-j)).2.1) (y.2.1-x.2.1) t := by
  have hf : (fun s : ℝ => (lineMap x y (s-j)).2.1) =
      (fun s : ℝ => (s-j)*(y.2.1-x.2.1)+x.2.1) := by
    funext s; simp [lineMap_apply, smul_eq_mul]
  rw [hf]
  simpa using (((hasDerivAt_id t).sub_const (j : ℝ)).mul_const
    (y.2.1-x.2.1)).add_const (x.2.1)

private theorem charts_variation (N : ℕ) (q : ℝ → State)
    (h : ∀ j : ℕ, j < N → ∃ x y : State,
      EqOn q (fun t => lineMap x y (t-j)) (Icc (j : ℝ) (j+1))) :
    BoundedVariationOn (fun t => (q t).2.1) (Icc (0 : ℝ) N) := by
  let f : ℝ → ℝ := fun t => (q t).2.1
  have hs := eVariationOn.sum' f
    (show Monotone (fun j : ℕ => (j : ℝ)) from
      fun i j hij => Nat.cast_le.mpr hij) (n := N)
  simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one] at hs
  change eVariationOn f (Icc 0 (N : ℝ)) ≠ ⊤
  rw [← hs]
  apply ENNReal.sum_ne_top.mpr
  intro j hj
  obtain ⟨x, y, he⟩ := h j (Finset.mem_range.mp hj)
  let g : ℝ → ℝ := fun t => lineMap x.2.1 y.2.1 (t-(j : ℝ))
  have ht : LipschitzWith 1 (fun t : ℝ => t-(j : ℝ)) :=
    LipschitzWith.of_dist_le_mul (fun x y => by
      simp only [Real.dist_eq, NNReal.coe_one, one_mul]
      rw [show x-(j : ℝ)-(y-j) = x-y by ring])
  have hg : LipschitzWith (nndist x.2.1 y.2.1 * 1) g :=
    (lipschitzWith_lineMap x.2.1 y.2.1).comp ht
  have hv : BoundedVariationOn g (Icc (j : ℝ) (j+1)) := by
    simpa only [Function.comp_id] using hg.comp_boundedVariationOn
      (BoundedVariationOn.id_Icc (j : ℝ) (j+1))
  have heq : EqOn f g (Icc (j : ℝ) (j+1)) := by
    intro t hti
    change (q t).2.1 = lineMap x.2.1 y.2.1 (t-(j : ℝ))
    have he' : q t = lineMap x y (t-(j : ℝ)) := he hti
    rw [he']
    simp [lineMap_apply, smul_eq_mul]
  exact (eVariationOn.congr heq).trans_ne hv

private theorem charts_integral (b : Base) (N : ℕ) (q : ℝ → State)
    (hq : Continuous q)
    (h : ∀ j : ℕ, j < N → ∃ x y : State,
      EqOn q (fun t => lineMap x y (t-j)) (Icc (j : ℝ) (j+1)) ∧
      ∀ t ∈ Ioo (j : ℝ) (j+1), ∀ i,
        HasDerivAt (fun s => (q s).2.2 i)
          (phaseWeight b (q t).1 i * deriv (fun s => (q s).2.1) t) t) :
    ∀ i, IntervalIntegrable
      (fun t => phaseWeight b (q t).1 i * deriv (fun s => (q s).2.1) t) volume 0 N ∧
      (∫ t in (0 : ℝ)..N, phaseWeight b (q t).1 i * deriv (fun s => (q s).2.1) t) =
        (q N).2.2 i-(q 0).2.2 i := by
  intro i
  let f : ℝ → ℝ := fun t => phaseWeight b (q t).1 i * deriv (fun s => (q s).2.1) t
  have hint : ∀ j : ℕ, j < N → IntervalIntegrable f volume (j : ℝ) ((j+1 : ℕ) : ℝ) := by
    intro j hj
    obtain ⟨x,y,he,hd⟩ := h j hj
    apply (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => y.2.2 i-x.2.2 i) volume (j : ℝ) ((j+1 : ℕ) : ℝ)).congr_uIoo
    intro t ht
    have ht' : t ∈ Ioo (j : ℝ) (j+1) := by
      rw [uIoo_of_le (by exact_mod_cast Nat.le_succ j)] at ht
      simpa only [Nat.cast_add, Nat.cast_one] using ht
    have hevent : q =ᶠ[𝓝 t] (fun s => lineMap x y (s-j)) := by
      filter_upwards [Ioo_mem_nhds ht'.1 ht'.2] with s hs
      exact he (Ioo_subset_Icc_self hs)
    exact ((coordinate_derivative x y j t i).congr_of_eventuallyEq
      (hevent.fun_comp (fun z : State => z.2.2 i))).unique (hd t ht' i)
  constructor
  · simpa only [Nat.cast_zero] using IntervalIntegrable.trans_iterate hint
  · have hs := intervalIntegral.sum_integral_adjacent_intervals hint
    simp only [Nat.cast_zero] at hs
    change (∫ t in (0 : ℝ)..N, f t) = _
    rw [← hs]
    calc
      ∑ j ∈ Finset.range N, ∫ t in (j : ℝ)..((j+1 : ℕ) : ℝ), f t =
          ∑ j ∈ Finset.range N, ((q ((j+1 : ℕ) : ℝ)).2.2 i-(q j).2.2 i) := by
        apply Finset.sum_congr rfl
        intro j hj
        obtain ⟨_,_,_,hd⟩ := h j (Finset.mem_range.mp hj)
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
          (by exact_mod_cast Nat.le_succ j)
          ((continuous_apply i).comp (continuous_snd.comp (continuous_snd.comp hq))).continuousOn
        · intro t ht
          apply hd t (by simpa only [Nat.cast_add, Nat.cast_one] using ht) i
        · exact hint j (Finset.mem_range.mp hj)
      _ = (q N).2.2 i-(q 0).2.2 i := by
        simpa only [Nat.cast_zero] using
          Finset.sum_range_sub (fun j : ℕ => (q j).2.2 i) N

theorem probability_derivative (b : Base) (k : ℝ → ℝ) (v t : ℝ)
    (hk : HasDerivAt k v t) (i : Fin 5) :
    HasDerivAt (fun s => probability b (k s) i) (direction i * v) t := by
  fin_cases i
  · change HasDerivAt (fun s => 1-b.2.2-b.1-b.2.1+k s) (1*v) t
    simpa only [one_mul] using hk.const_add (1-b.2.2-b.1-b.2.1)
  · change HasDerivAt (fun s => b.1-k s) (-1*v) t
    simpa only [neg_mul, one_mul] using hk.const_sub b.1
  · change HasDerivAt (fun _ => b.2.2) (0*v) t
    simpa only [zero_mul] using hasDerivAt_const t b.2.2
  · change HasDerivAt (fun s => b.2.1-k s) (-1*v) t
    simpa only [neg_mul, one_mul] using hk.const_sub b.2.1
  · change HasDerivAt k (1*v) t
    simpa only [one_mul] using hk

private theorem charts_probability (b : Base) (N : ℕ) (q : ℝ → State)
    (h : ∀ j : ℕ, j < N → ∃ x y : State,
      EqOn q (fun t => lineMap x y (t-j)) (Icc (j : ℝ) (j+1))) :
    ∀ j : ℕ, j < N → ∀ t ∈ Ioo (j : ℝ) (j+1), ∀ i,
      HasDerivAt (fun s => probability b (q s).1 i)
        (direction i * deriv (fun s => (q s).1) t) t := by
  intro j hj t ht i
  obtain ⟨x, y, he⟩ := h j hj
  have hf : (fun s : ℝ => (lineMap x y (s-j)).1) =
      (fun s : ℝ => (s-j)*(y.1-x.1)+x.1) := by
    funext s
    simp [lineMap_apply, smul_eq_mul]
  have hk : HasDerivAt (fun s : ℝ => (lineMap x y (s-j)).1) (y.1-x.1) t := by
    rw [hf]
    simpa using (((hasDerivAt_id t).sub_const (j : ℝ)).mul_const
      (y.1-x.1)).add_const x.1
  have hevent : q =ᶠ[𝓝 t] (fun s => lineMap x y (s-j)) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact he (Ioo_subset_Icc_self hs)
  have hd := hk.congr_of_eventuallyEq (hevent.fun_comp Prod.fst)
  change HasDerivAt (fun s => (q s).1) (y.1-x.1) t at hd
  rw [hd.deriv]
  exact probability_derivative b (fun s => (q s).1) (y.1-x.1) t hd i

theorem polygon_admissible (b : Base) (x : State) (xs : List State)
    (hx : x.1 ∈ Ioo (lower b) (upper b))
    (h : List.IsChain (LawfulLeg (phaseWeight b) (lower b) (upper b)) (x :: xs)) :
    Admissible b xs.length (polygon (x :: xs)) := by
  have charts := polygon_charts (phaseWeight b) (lower b) (upper b) x xs h
  have hcharts : ∀ j : ℕ, j < xs.length → ∃ a c : State,
      EqOn (polygon (x :: xs)) (fun t => lineMap a c (t-j)) (Icc (j : ℝ) (j+1)) ∧
      ∀ t ∈ Ioo (j : ℝ) (j+1), ∀ i,
        HasDerivAt (fun s => (polygon (x :: xs) s).2.2 i)
          (phaseWeight b (polygon (x :: xs) t).1 i *
            deriv (fun s => (polygon (x :: xs) s).2.1) t) t := by
    intro j hj
    obtain ⟨a, c, hac, he⟩ := charts j hj
    refine ⟨a, c, he, ?_⟩
    intro t ht i
    have hevent : polygon (x :: xs) =ᶠ[𝓝 t] (fun s => lineMap a c (s-j)) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact he (Ioo_subset_Icc_self hs)
    have hc := (coordinate_derivative a c j t i).congr_of_eventuallyEq
      (hevent.fun_comp (fun z : State => z.2.2 i))
    have hp := (phase_derivative a c j t).congr_of_eventuallyEq
      (hevent.fun_comp (fun z : State => z.2.1))
    change HasDerivAt (fun s => (polygon (x :: xs) s).2.1) (c.2.1-a.2.1) t at hp
    rw [hp.deriv]
    have hw := hac.2.2 (t-j) (by
      simp only [mem_Ioo] at ht
      constructor <;> linarith : t-j ∈ Icc (0 : ℝ) 1) i
    have heq : polygon (x :: xs) t = lineMap a c (t-j) := he (Ioo_subset_Icc_self ht)
    rw [← heq] at hw
    exact hc.congr_deriv hw
  exact ⟨polygon_continuous x xs, polygon_inside _ _ _ x xs hx h,
    charts_variation xs.length _ (fun j hj => by
      obtain ⟨a, c, _, he⟩ := charts j hj; exact ⟨a, c, he⟩),
    hcharts, charts_integral b xs.length _ (polygon_continuous x xs) hcharts,
    charts_probability b xs.length _ (fun j hj => by
      obtain ⟨a, c, _, he⟩ := charts j hj
      exact ⟨a, c, he⟩)⟩

/-- The exact lifted phase sum of a finite rectangle menu. -/
def residual (w : ℝ → Vec) (k0 : ℝ) (data : List (ℝ × ℝ)) : Vec :=
  (data.map (fun ka => ka.2 • (w ka.1-w k0))).sum

private def rectangleTail (w : ℝ → Vec) (k0 : ℝ) : List (ℝ × ℝ) → Vec → List State
  | [], _ => []
  | (k,a) :: rest, h =>
    (k,0,h) :: (k,a,h+a • w k) :: (k0,a,h+a • w k) ::
      (k0,0,h+a • (w k-w k0)) ::
      rectangleTail w k0 rest (h+a • (w k-w k0))

private theorem rectangle_length (w : ℝ → Vec) (k0 : ℝ) (data : List (ℝ × ℝ)) (h : Vec) :
    (rectangleTail w k0 data h).length = 4*data.length := by
  induction data generalizing h with
  | nil => simp [rectangleTail]
  | cons ka rest ih =>
    rcases ka with ⟨k,a⟩
    simp [rectangleTail, ih]; omega

private theorem horizontal_leg (w : ℝ → Vec) (L U k l c : ℝ) (h : Vec)
    (hk : k ∈ Ioo L U) (hl : l ∈ Ioo L U) :
    LawfulLeg w L U (k,c,h) (l,c,h) := by
  refine ⟨hk,hl,?_⟩
  intro t ht i
  simp

private theorem vertical_leg (w : ℝ → Vec) (L U k c a : ℝ) (h : Vec)
    (hk : k ∈ Ioo L U) :
    LawfulLeg w L U (k,c,h) (k,c+a,h+a • w k) := by
  refine ⟨hk,hk,?_⟩
  intro t ht i
  simp [lineMap_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem rectangle_chain (w : ℝ → Vec) (L U k0 : ℝ)
    (data : List (ℝ × ℝ)) (h : Vec) (hk0 : k0 ∈ Ioo L U)
    (hdata : ∀ ka ∈ data, ka.1 ∈ Ioo L U) :
    List.IsChain (LawfulLeg w L U) ((k0,0,h) :: rectangleTail w k0 data h) := by
  induction data generalizing h with
  | nil => exact List.isChain_singleton _
  | cons ka rest ih =>
    rcases ka with ⟨k,a⟩
    have hk := hdata (k,a) (by simp)
    have hr := ih (h+a • (w k-w k0)) (fun ka hka => hdata ka (by simp [hka]))
    simp only [rectangleTail, List.isChain_cons_cons]
    refine ⟨horizontal_leg w L U k0 k 0 h hk0 hk, ?_,
      horizontal_leg w L U k k0 a (h+a • w k) hk hk0, ?_, hr⟩
    · simpa using vertical_leg w L U k 0 a h hk
    · convert vertical_leg w L U k0 a (-a) (h+a • w k) hk0 using 1 <;>
        ext i <;> simp [Pi.smul_apply, smul_eq_mul] <;> ring

private theorem rectangle_last (w : ℝ → Vec) (k0 : ℝ)
    (data : List (ℝ × ℝ)) (h : Vec) :
    ((k0,0,h) :: rectangleTail w k0 data h).getLast (by simp) =
      (k0,0,h+residual w k0 data) := by
  induction data generalizing h with
  | nil => simp [rectangleTail, residual]
  | cons ka rest ih =>
    rcases ka with ⟨k,a⟩
    simp only [rectangleTail, List.getLast_cons_cons]
    rw [ih]
    simp only [residual, List.map_cons, List.sum_cons]
    congr 2
    exact add_assoc _ _ _

/-- The middle-fixed gauge and the real relation phase of the state lift. -/
def Compatible (x : State) : Prop :=
  x.2.2 2 = 0 ∧ x.2.2 0-x.2.2 1-x.2.2 3+x.2.2 4 = x.2.1

theorem weight_compatible (b : Base) (hb : ValidBase b) (k : ℝ)
    (hk : k ∈ Ioo (lower b) (upper b)) :
    phaseWeight b k 2 = 0 ∧
      phaseWeight b k 0-phaseWeight b k 1-phaseWeight b k 3+phaseWeight b k 4 = 1 := by
  have h0 := (fiberProbability b k hb hk).positive 0
  have h1 := (fiberProbability b k hb hk).positive 1
  have h3 := (fiberProbability b k hb hk).positive 3
  have h4 := (fiberProbability b k hb hk).positive 4
  change 0 < probability b k 0 at h0
  change 0 < probability b k 1 at h1
  change 0 < probability b k 3 at h3
  change 0 < probability b k 4 at h4
  have hI : information b k ≠ 0 := by
    apply ne_of_gt
    unfold information
    positivity
  constructor
  · simp [phaseWeight,direction]
  · simp only [phaseWeight, direction, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]
    field_simp [hI,h0.ne',h1.ne',h3.ne',h4.ne']
    dsimp [information]
    field_simp [h0.ne',h1.ne',h3.ne',h4.ne']
    ring

private theorem compatible_line (x y : State) (hx : Compatible x) (hy : Compatible y)
    (t : ℝ) : Compatible (lineMap x y t) := by
  constructor
  · simp [lineMap_apply,Pi.smul_apply,smul_eq_mul,hx.1,hy.1]
  · change (lineMap x y t).2.2 0-(lineMap x y t).2.2 1-
      (lineMap x y t).2.2 3+(lineMap x y t).2.2 4 = (lineMap x y t).2.1
    simp [lineMap_apply,Pi.smul_apply,smul_eq_mul]
    linear_combination (1-t)*hx.2+t*hy.2

private theorem polygon_compatible (x : State) (xs : List State)
    (h : ∀ y ∈ x :: xs, Compatible y) : ∀ t : ℝ, Compatible (polygon (x :: xs) t) := by
  induction xs generalizing x with
  | nil => intro t; exact h x (by simp)
  | cons y ys ih =>
    intro t
    by_cases ht : t ≤ 1
    · simp only [polygon,if_pos ht]
      exact compatible_line x y (h x (by simp)) (h y (by simp)) t
    · rw [polygon_tail x y ys t (by linarith)]
      exact ih y (fun z hz => h z (by simp only [List.mem_cons] at hz ⊢; tauto)) (t-1)

private theorem rectangle_compatible (b : Base) (hb : ValidBase b) (k0 : ℝ)
    (hk0 : k0 ∈ Ioo (lower b) (upper b)) (data : List (ℝ × ℝ))
    (hdata : ∀ ka ∈ data, ka.1 ∈ Ioo (lower b) (upper b)) (h : Vec)
    (hh : Compatible (k0, 0, h)) :
    ∀ x ∈ (k0,0,h) :: rectangleTail (phaseWeight b) k0 data h, Compatible x := by
  induction data generalizing h with
  | nil => simpa [rectangleTail] using hh
  | cons ka rest ih =>
    rcases ka with ⟨k,a⟩
    have hh2 : h 2 = 0 := hh.1
    have hhc : h 0-h 1-h 3+h 4 = 0 := hh.2
    have hk := hdata (k,a) (by simp)
    obtain ⟨hw2,hw⟩ := weight_compatible b hb k hk
    obtain ⟨h02,h0⟩ := weight_compatible b hb k0 hk0
    have hf : Compatible (k0,0,h+a • (phaseWeight b k-phaseWeight b k0)) := by
      constructor
      · simp [Pi.smul_apply,smul_eq_mul,hh2,hw2,h02]
      · dsimp [Compatible]
        linear_combination hhc+a*hw-a*h0
    have hr := ih (fun ka hka => hdata ka (by simp [hka])) _ hf
    intro x hx
    simp only [rectangleTail,List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | hx
    · exact hh
    · simpa [Compatible] using hh
    · constructor
      · simp [Pi.smul_apply,smul_eq_mul,hh2,hw2]
      · dsimp [Compatible]
        linear_combination hhc+a*hw
    · constructor
      · simp [Pi.smul_apply,smul_eq_mul,hh2,hw2]
      · dsimp [Compatible]
        linear_combination hhc+a*hw
    · exact hf
    · exact hr x (by simp [hx])

/-- Arbitrary finite rectangles are realized by an actual continuous transport path.
The time interval has four unit affine legs per supplied height; coefficients may
be positive, negative or zero, and no distinctness of heights is imposed. -/
theorem finite_rectangles_realize (b : Base) (hb : ValidBase b) (k0 : ℝ)
    (hk0 : k0 ∈ Ioo (lower b) (upper b)) (data : List (ℝ × ℝ))
    (hdata : ∀ ka ∈ data, ka.1 ∈ Ioo (lower b) (upper b)) :
    ∃ q : ℝ → State,
      Admissible b (4*data.length) q ∧
      q 0 = (k0,0,0) ∧
      (q (4*data.length)).1 = k0 ∧ (q (4*data.length)).2.1 = 0 ∧
      (∀ t ∈ Icc (0 : ℝ) (4*data.length),
        ∃ p : InteriorProbability 4, p.weight = probability b (q t).1) ∧
      (∀ t ∈ Icc (0 : ℝ) (4*data.length), Compatible (q t)) ∧
      (q (4*data.length)).2.2 = residual (phaseWeight b) k0 data := by
  let tail := rectangleTail (phaseWeight b) k0 data 0
  let q := polygon ((k0,0,0) :: tail)
  have hlen : tail.length = 4*data.length := rectangle_length _ _ _ _
  have hc := rectangle_chain (phaseWeight b) (lower b) (upper b) k0 data 0 hk0 hdata
  have ha : Admissible b (4*data.length) q := by
    rw [← hlen]
    exact polygon_admissible b (k0,0,0) tail hk0 hc
  have he : q (4*data.length) = (k0,0,residual (phaseWeight b) k0 data) := by
    rw [show 4*(data.length : ℝ) = (tail.length : ℝ) by exact_mod_cast hlen.symm]
    simpa only [q, tail, rectangle_last, zero_add] using polygon_end (k0,0,(0 : Vec)) tail
  refine ⟨q,ha,polygon_zero _ _,congrArg Prod.fst he,
    congrArg (fun x : State => x.2.1) he,?_,?_,congrArg (fun x : State => x.2.2) he⟩
  · intro t ht
    exact ⟨fiberProbability b (q t).1 hb
      (ha.2.1 t (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using ht)), rfl⟩
  · intro t ht
    exact polygon_compatible (k0,0,0) tail
      (rectangle_compatible b hb k0 hk0 data hdata 0 (by simp [Compatible])) t

#print axioms finite_rectangles_realize

end D5.S3.Quantum.Fibers.FiniteRectangleTransport
