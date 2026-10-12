/- GID: D5/S3/Geometry/Hyperideal/FourCycleExistence
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/FourCycleExistence
   mirror-E: none(waiver:unbounded-finite-incidence-real-existence)
   anchors: []
   utility: none
   digest: One shared interior zero-curvature vector for every four-cycle incidence system. -/

import D5.S3.Geometry.Hyperideal.FourCycleCurvature
import D5.S3.Geometry.FixedPoint.Brouwer
import Mathlib.Tactic

/-!
Classical finite-dimensional fixed-point transport is support for the actual
FourCycle consumer below, not a novelty claim. Every coordinate is a shared
global edge variable and every star counts occurrences with multiplicity.
No continuity, finite-edge, zero-curvature, or geometric-realization premise
is added to the existing FourCycle incidence hypotheses.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.Geometry.Hyperideal.FourCycleExistence

open D5.S3.Geometry.Hyperideal.FourCycleCurvature
open D5.S3.Geometry.Hyperideal.FourCycleEnvelopes

private abbrev Cube (n : ℕ) := {x : Fin n → ℝ // ∀ i, x i ∈ Set.Icc 0 1}

-- A cube is a retract of a containing simplex; no affine equivalence is claimed.
private theorem cube_fixed_point (n : ℕ) (f : Cube n → Cube n)
    (hf : Continuous f) : ∃ x, f x = x := by
  let m : ℝ := (n : ℝ) + 1
  have hm : 0 < m := by dsimp [m]; positivity
  let up : Cube n → stdSimplex ℝ (Fin (n+1)) := fun x =>
    ⟨Fin.cons (1 - ∑ i, x.1 i / m) (fun i => x.1 i / m), by
      constructor
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Fin.cons_zero]
          have hsum : ∑ i, x.1 i ≤ (n : ℝ) := by
            calc
              ∑ i, x.1 i ≤ ∑ _i : Fin n, (1 : ℝ) :=
                Finset.sum_le_sum (fun i _ => (x.2 i).2)
              _ = (n : ℝ) := by simp
          rw [← Finset.sum_div]
          have hdiv : (∑ i, x.1 i) / m ≤ 1 :=
            (div_le_one hm).2 (by dsimp [m]; linarith)
          linarith
        · simpa only [Fin.cons_succ] using div_nonneg (x.2 j).1 hm.le
      · rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        ring⟩
  let down : stdSimplex ℝ (Fin (n+1)) → Cube n := fun y =>
    ⟨fun i => max 0 (min 1 (m * y.1 i.succ)), fun i =>
      ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩⟩
  have hdownup : ∀ x, down (up x) = x := by
    intro x
    apply Subtype.ext
    funext i
    change max 0 (min 1 (m * (x.1 i / m))) = x.1 i
    have heq : m * (x.1 i / m) = x.1 i  := by field_simp [hm.ne']
    rw [heq, min_eq_right (x.2 i).2, max_eq_right (x.2 i).1]
  have hcoord : ∀ i, Continuous (fun x : Cube n => x.1 i) := by
    intro i
    exact (continuous_apply i).comp continuous_subtype_val
  have hup : Continuous up := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Continuous (fun x : Cube n => 1 - ∑ i, x.1 i / m)
      exact continuous_const.sub (continuous_finsetSum _
        (fun i _ => (hcoord i).div_const m))
    · change Continuous (fun x : Cube n => x.1 j / m)
      exact (hcoord j).div_const m
  have hdown : Continuous down := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    change Continuous (fun y : stdSimplex ℝ (Fin (n+1)) =>
      max 0 (min 1 (m * y.1 i.succ)))
    exact continuous_const.max (continuous_const.min
      (continuous_const.mul ((continuous_apply i.succ).comp continuous_subtype_val)))
  obtain ⟨y, hy⟩ := D5.S3.Geometry.FixedPoint.Brouwer
    ⟨n+1, Nat.succ_pos n⟩ (up ∘ f ∘ down) (hup.comp (hf.comp hdown))
  refine ⟨down y, ?_⟩
  have h := congrArg down hy
  change down (up (f (down y))) = down y at h
  rwa [hdownup] at h

-- Boundary signs exclude both clamp-active cases before cancellation.
private theorem clamp_fixed_zero (t v : ℝ) (ht : t ∈ Set.Icc 0 1)
    (hfix : max 0 (min 1 (t + v)) = t)
    (hlo : t = 0 → 0 < v) (hhi : t = 1 → v < 0) :
    0 < t ∧ t < 1 ∧ v = 0 := by
  have ht0 : 0 < t := by
    by_contra h
    have heq : t = 0 := le_antisymm (le_of_not_gt h) ht.1
    have hv := hlo heq
    have hp : 0 < min 1 (t + v) := lt_min (by norm_num) (by linarith)
    have hp' := hp.trans_le (le_max_right 0 (min 1 (t + v)))
    rw [hfix] at hp'
    linarith
  have ht1 : t < 1 := by
    by_contra h
    have heq : t = 1 := le_antisymm ht.2 (le_of_not_gt h)
    have hv := hhi heq
    have hp : max 0 (min 1 (t + v)) < 1 :=
      max_lt (by norm_num) ((min_le_right _ _).trans_lt (by linarith))
    rw [hfix] at hp
    linarith
  have hmin : min 1 (t + v) = t := by
    by_cases h : 0 ≤ min 1 (t + v)
    · rwa [max_eq_right h] at hfix
    · rw [max_eq_left (le_of_not_ge h)] at hfix
      linarith
  have hsum : t + v = t := by
    by_cases h : t + v ≤ 1
    · rwa [min_eq_right h] at hmin
    · rw [min_eq_left (le_of_not_ge h)] at hmin
      linarith
  exact ⟨ht0, ht1, by linarith⟩

variable {T E : Type*} [Fintype T] [DecidableEq E]

theorem fourcycle_zero_curvature (s : Incidence T E) (hs : FourCycle s) :
    ∃ x : E → ℝ,
      (∀ e, lower s e < x e ∧ x e < upper s e) ∧
      (∀ o : T × Fin 6, -1 < localCosine s x o ∧ localCosine s x o < 1) ∧
      (∀ e, curvature s x e = 0) := by
  classical
  have hsource : Function.Surjective (source s) := by
    intro e
    have hpos : 0 < degree s e := by
      cases h : s.low e with
      | false => have hd := hs.2.2 e h; omega
      | true => rw [hs.2.1 e h]; norm_num
    obtain ⟨o, ho⟩ := Finset.card_pos.mp hpos
    exact ⟨o, (Finset.mem_filter.mp ho).2⟩
  let : Fintype E := Fintype.ofSurjective (source s) hsource
  obtain ⟨hd, hd8, hm, hbase, hfaces⟩ := fourcycle_curvature_box s hs
  have hwidth : ∀ e, lower s e < upper s e := by
    intro e
    unfold lower upper
    split_ifs <;> linarith
  have hlower : ∀ e, 1 < lower s e := by
    intro e
    unfold lower
    split_ifs <;> linarith
  let n := Fintype.card E
  let q : E ≃ Fin n := Fintype.equivFin E
  let X : Cube n → E → ℝ := fun u e =>
    lower s e + (upper s e - lower s e) * u.1 (q e)
  have hX : ∀ u, Box s (X u) := by
    intro u e
    have hu := u.2 (q e)
    have hw := hwidth e
    change lower s e ≤ lower s e + (upper s e-lower s e)*u.1 (q e) ∧
      lower s e + (upper s e-lower s e)*u.1 (q e) ≤ upper s e
    have hp := mul_nonneg (sub_nonneg.mpr hw.le) hu.1
    have hq := mul_nonneg (sub_nonneg.mpr hw.le) (sub_nonneg.mpr hu.2)
    constructor <;> nlinarith
  have hc : ∀ e, Continuous (fun u : Cube n => X u e) := by
    intro e
    exact continuous_const.add (continuous_const.mul
      ((continuous_apply (q e)).comp continuous_subtype_val))
  have hrad : ∀ u : Cube n, ∀ i j k : E,
      0 < rad (X u i) (X u j) (X u k) := by
    intro u i j k
    have hi := (hlower i).trans_le (hX u i).1
    have hj := (hlower j).trans_le (hX u j).1
    have hk := (hlower k).trans_le (hX u k).1
    have hp : 0 ≤ 2 * X u i * X u j * X u k := by positivity
    unfold rad
    nlinarith [sq_nonneg (X u i-1), sq_nonneg (X u j-1),
      sq_nonneg (X u k-1)]
  have hcos : ∀ o, Continuous (fun u : Cube n => localCosine s (X u) o) := by
    intro o
    have hr : ∀ i j k : E, Continuous (fun u : Cube n =>
        Real.sqrt (rad (X u i) (X u j) (X u k))) := by
      intro i j k
      apply Real.continuous_sqrt.comp
      unfold rad
      fun_prop
    have hn : Continuous (fun u : Cube n =>
        numerator (X u (coordinate s o 0)) (X u (coordinate s o 1))
          (X u (coordinate s o 2)) (X u (coordinate s o 3))
          (X u (coordinate s o 4)) (X u (coordinate s o 5))) := by
      unfold numerator
      fun_prop
    unfold localCosine cosine
    exact (hn.div (hr _ _ _) (fun u => (Real.sqrt_pos.2 (hrad u _ _ _)).ne')).div
      (hr _ _ _) (fun u => (Real.sqrt_pos.2 (hrad u _ _ _)).ne')
  have hK : ∀ e, Continuous (fun u : Cube n => curvature s (X u) e) := by
    intro e
    apply continuous_const.sub
    exact continuous_finsetSum _ (fun o _ => Real.continuous_arccos.comp (hcos o))
  let G : Cube n → Cube n := fun u =>
    ⟨fun i => max 0 (min 1 (u.1 i + curvature s (X u) (q.symm i))),
      fun i => ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩⟩
  have hG : Continuous G := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact continuous_const.max (continuous_const.min
      (((continuous_apply i).comp continuous_subtype_val).add (hK (q.symm i))))
  obtain ⟨u, hu⟩ := cube_fixed_point n G hG
  have hsol : ∀ e, 0 < u.1 (q e) ∧ u.1 (q e) < 1 ∧ curvature s (X u) e = 0 := by
    intro e
    have hfix := congrArg (fun z : Cube n => z.1 (q e)) hu
    change max 0 (min 1 (u.1 (q e) + curvature s (X u) (q.symm (q e)))) =
      u.1 (q e) at hfix
    simp only [Equiv.symm_apply_apply] at hfix
    apply clamp_fixed_zero _ _ (u.2 (q e)) hfix
    · intro heq
      have hface : X u e = lower s e := by dsimp [X]; rw [heq]; ring
      exact hm.trans_le (((hfaces (X u) (hX u)).2 e).1 hface)
    · intro heq
      have hface : X u e = upper s e := by dsimp [X]; rw [heq]; ring
      have h := ((hfaces (X u) (hX u)).2 e).2 hface
      linarith
  refine ⟨X u, ?_, (hfaces (X u) (hX u)).1, fun e => (hsol e).2.2⟩
  intro e
  have hw := hwidth e
  obtain ⟨h0, h1, _⟩ := hsol e
  have hp := mul_pos (sub_pos.mpr hw) h0
  have hq := mul_pos (sub_pos.mpr hw) (sub_pos.mpr h1)
  dsimp [X]
  constructor <;> nlinarith

end D5.S3.Geometry.Hyperideal.FourCycleExistence
