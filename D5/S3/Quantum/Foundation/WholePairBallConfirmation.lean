/- GID: D5/S3/Quantum/Foundation/WholePairBallConfirmation
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/WholePairBallConfirmation
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Whole minimal-face balls and common positive supports construct least confirmation. -/

import D5.S3.Quantum.Foundation.CircuitBalancedConfirmation
import Mathlib.Geometry.Convex.Cone.Face.Lattice
import Mathlib.Analysis.Convex.Strict.Extreme
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.LinearAlgebra.AffineSpace.Midpoint

/-!
The base, pure points, proper interval and least-confirmation predicate are the
original CircuitBalancedConfirmation objects. Pair bases use every cone face,
not a selected patch. Ball dimensions may vary and include one.
-/

noncomputable section
open scoped RealInnerProductSpace

namespace D5.S3.Quantum.Foundation.WholePairBallConfirmation

open CircuitBalancedConfirmation

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The entire base of the smallest original cone face containing both points. -/
def pairBase (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (p q : V) : Set V :=
  {x | x ∈ base C u ∧ ∀ F : C.Face, p ∈ F → q ∈ F → x ∈ F}

/-- An injective affine parametrization of the entire pair base by a closed ball. -/
structure BallChart (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (p q : V) where
  dim : ℕ
  dim_pos : 0 < dim
  param : EuclideanSpace ℝ (Fin dim) →ᵃ[ℝ] V
  injective : Function.Injective param
  whole : param '' Metric.closedBall 0 1 = pairBase C u p q

/-- All distinct global pure pairs have entire finite ball bases. -/
def wholePairBalls (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) : Prop :=
  ∀ p q : pure C u, p ≠ q → Nonempty (BallChart C u p q)

/-- One positive functional per pure point vanishes at every chart antipode.
No proper upper bound or leastness is assumed. -/
def commonSupport (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) : Prop :=
  ∀ p : pure C u, ∃ g : V →ₗ[ℝ] ℝ,
    (∀ x ∈ C, 0 ≤ g x) ∧ 0 < g p ∧
    ∀ (q : pure C u), p ≠ q → ∀ b : BallChart C u p q,
      ∀ n, ‖n‖ = 1 → b.param n = p → g (b.param (-n)) = 0

omit [FiniteDimensional ℝ V] in
theorem affine_extreme_preimage {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : E →ᵃ[ℝ] V) (hf : Function.Injective f) (S : Set E) (x : E) :
    f x ∈ (f '' S).extremePoints ℝ → x ∈ S.extremePoints ℝ := by
  rintro ⟨hx, he⟩
  refine ⟨(hf.mem_set_image).mp hx, ?_⟩
  intro a ha b hb hab
  apply hf
  exact he ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    ((image_openSegment ℝ f a b) ▸ Set.mem_image_of_mem f hab)

omit [FiniteDimensional ℝ V] in
private theorem chart_mem {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ} {p q : V}
    (b : BallChart C u p q) {s} (hs : ‖s‖ ≤ 1) : b.param s ∈ pairBase C u p q := by
  rw [← b.whole]
  exact ⟨s, by simpa using hs, rfl⟩

private theorem chart_pure_norm {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ} {p q : V}
    (b : BallChart C u p q) {s} (hs : ‖s‖ ≤ 1)
    (hp : b.param s ∈ pure C u) : ‖s‖ = 1 := by
  have : Nonempty (Fin b.dim) := ⟨⟨0, b.dim_pos⟩⟩
  have he : b.param s ∈ (b.param '' Metric.closedBall 0 1).extremePoints ℝ := by
    refine ⟨⟨s, by simpa using hs, rfl⟩, ?_⟩
    intro x hx y hy hxy
    exact hp.2 ((b.whole ▸ hx).1) ((b.whole ▸ hy).1) hxy
  have hh := affine_extreme_preimage b.param b.injective _ s he
  rw [StrictConvexSpace.extremePoints_closedBall_eq_sphere] at hh
  simpa using hh

private theorem affine_riesz {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E →ᵃ[ℝ] ℝ) :
    ∃ v : E, ∀ s, f s = f 0 + ⟪v, s⟫ := by
  let L := f.linear.toContinuousLinearMap
  refine ⟨(InnerProductSpace.toDual ℝ E).symm L, fun s => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  simpa [L, add_comm] using congrFun f.decomp s

private theorem affine_nonneg_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {a : ℝ} {v : E}
    (h : ∀ s : E, ‖s‖ ≤ 1 → 0 ≤ a + ⟪v, s⟫) : ‖v‖ ≤ a := by
  by_cases hv : v = 0
  · simpa [hv] using h 0 (by simp)
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hs : ‖-(‖v‖⁻¹ • v)‖ ≤ 1 := by
    simp [norm_smul, hvpos.ne']
  have hh := h (-(‖v‖⁻¹ • v)) hs
  simp only [inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq] at hh
  have he : ‖v‖⁻¹ * ‖v‖ ^ 2 = ‖v‖ := by field_simp
  rw [he] at hh
  linarith

private theorem affine_zero_antipode {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E →ᵃ[ℝ] ℝ) {n : E} (hn : ‖n‖ = 1)
    (hpos : ∀ s, ‖s‖ ≤ 1 → 0 ≤ f s) (hz : f (-n) = 0) :
    ∀ s, f s = f n / 2 * (1 + ⟪n, s⟫) := by
  obtain ⟨v, hv⟩ := affine_riesz f
  have hbound := affine_nonneg_bound (fun s hs => by rw [← hv]; exact hpos s hs)
  have hzero : f 0 = ⟪v, n⟫ := by rw [hv, inner_neg_right] at hz; linarith
  have hcs : ⟪v, n⟫ ≤ ‖v‖ := by simpa [hn] using real_inner_le_norm v n
  have heq : f 0 = ‖v‖ := le_antisymm (hzero.trans_le hcs) hbound
  have halign : v = ‖v‖ • n := by
    have hh := inner_eq_norm_mul_iff_real.mp
      (show ⟪v, n⟫ = ‖v‖ * ‖n‖ by rw [hn, mul_one, ← heq, hzero])
    simpa [hn] using hh
  have hfn : f n = 2 * f 0 := by rw [hv, ← hzero]; ring
  intro s
  rw [hv, halign, real_inner_smul_left, ← heq, hfn]
  ring

private abbrev swapChart {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ} {p q : V}
    (b : BallChart C u p q) : BallChart C u q p where
  dim := b.dim
  dim_pos := b.dim_pos
  param := b.param
  injective := b.injective
  whole := b.whole.trans (by ext x; simp only [pairBase, Set.mem_ofPred_eq]; aesop)

private theorem endpoint_coordinates {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (p q : pure C u) (b : BallChart C u p q) :
    ∃ n, ‖n‖ = 1 ∧ b.param n = p := by
  have hp : (p : V) ∈ pairBase C u p q := ⟨p.property.1, fun _ hp _ => hp⟩
  rw [← b.whole] at hp
  obtain ⟨n, hn, he⟩ := hp
  refine ⟨n, chart_pure_norm b (by simpa using hn) (by rw [he]; exact p.property), he⟩

private theorem support_formula {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    {p q : pure C u} (b : BallChart C u p q) (g : V →ₗ[ℝ] ℝ)
    (hpos : ∀ x ∈ C, 0 ≤ g x) (hgp : 0 < g p)
    {n} (hn : ‖n‖ = 1) (hp : b.param n = p) (hz : g (b.param (-n)) = 0) :
    ∀ s, ((g p)⁻¹ • g) (b.param s) = (1 + ⟪n, s⟫) / 2 := by
  have hh := affine_zero_antipode (g.toAffineMap.comp b.param) hn
    (fun s hs => hpos _ (chart_mem b hs).1.1) hz
  intro s
  have he := hh s
  change g (b.param s) = g (b.param n) / 2 * (1 + ⟪n, s⟫) at he
  rw [hp] at he
  simp only [LinearMap.smul_apply, smul_eq_mul, he]
  field_simp

private theorem confirming_dominates_ball {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    {p q : pure C u} (b : BallChart C u p q)
    {n} (hn : ‖n‖ = 1) (hp : b.param n = p)
    (h : V →ₗ[ℝ] ℝ) (hh : confirms C u p h) :
    ∀ s, ‖s‖ ≤ 1 → (1 + ⟪n, s⟫) / 2 ≤ h (b.param s) := by
  let f := (AffineMap.const ℝ (EuclideanSpace ℝ (Fin b.dim)) (1 : ℝ)) -
    h.toAffineMap.comp b.param
  have hnon (s) (hs : ‖s‖ ≤ 1) : 0 ≤ f s := by
    have hx := chart_mem b hs
    have hb := (hh.1 _ hx.1.1).2
    change 0 ≤ 1 - h (b.param s)
    rw [hx.1.2] at hb
    linarith
  have hzero : f (-(-n)) = 0 := by simp [f, hp, hh.2]
  have hf := affine_zero_antipode f (by simpa using hn : ‖-n‖ = 1) hnon hzero
  intro s hs
  have he := hf s
  have hc := (hh.1 _ (chart_mem b (by simp [hn] : ‖-n‖ ≤ 1)).1.1).1
  have hi : ⟪n, s⟫ ≤ 1 :=
    (real_inner_le_norm n s).trans (by simpa [hn] using hs)
  change 1 - h (b.param s) = (1 - h (b.param (-n))) / 2 * (1 + ⟪-n, s⟫) at he
  rw [inner_neg_left] at he
  nlinarith

/-- Original global binary exclusion, with one proper confirmer as its witness. -/
def excludes (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (p x : V) : Prop :=
  ∃ h : V →ₗ[ℝ] ℝ, confirms C u p h ∧ h x = 0

/-- The zero midpoint condition on all original mixed states. -/
def zeroMidpoint (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) : Prop :=
  ∀ (p : pure C u) (x y : V), x ∈ base C u → y ∈ base C u →
    excludes C u p x → excludes C u p y → excludes C u p ((1 / 2 : ℝ) • (x + y))

/-- Antipodal exclusion for every pure point of every entire pair ball. -/
def allAntipodes (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) : Prop :=
  ∀ (p q : pure C u), p ≠ q → ∀ b : BallChart C u p q,
    ∀ n, ‖n‖ = 1 → b.param n ∈ pure C u →
      excludes C u (b.param n) (b.param (-n))

/-- The globally normalized common support; its properness is a conclusion. -/
def supportEffect {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hH : commonSupport C u) (p : pure C u) : V →ₗ[ℝ] ℝ :=
  ((Classical.choose (hH p)) p)⁻¹ • Classical.choose (hH p)

omit [FiniteDimensional ℝ V] in
theorem pair_extreme (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (p q : V) :
    IsExtreme ℝ (base C u) (pairBase C u p q) := by
  refine ⟨fun _ hx => hx.1, ?_⟩
  intro x hx y hy z hz hseg
  refine ⟨hx, fun F hp hq => ?_⟩
  exact F.isFaceOf.isExtreme.left_mem_of_mem_openSegment hx.1 hy.1 (hz.2 F hp hq) hseg

private theorem chart_sphere_pure {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ} {p q : V}
    (b : BallChart C u p q) {n} (hn : ‖n‖ = 1) : b.param n ∈ pure C u := by
  have : Nonempty (Fin b.dim) := ⟨⟨0, b.dim_pos⟩⟩
  have hh : n ∈ (Metric.closedBall 0 1).extremePoints ℝ := by
    rw [StrictConvexSpace.extremePoints_closedBall_eq_sphere]
    simpa using hn
  have hi := D5.S3.Quantum.Foundation.CircuitBalancedConfirmation.affine_extreme_image
    (Metric.closedBall (0 : EuclideanSpace ℝ (Fin b.dim)) 1)
    (convex_closedBall 0 1) b.param (fun _ _ _ _ h => b.injective h) hh
  rw [b.whole] at hi
  exact (pair_extreme C u p q).extremePoints_subset_extremePoints hi

omit [FiniteDimensional ℝ V] in
private theorem chart_midpoint {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ} {p q : V}
    (b : BallChart C u p q) (s) :
    (1 / 2 : ℝ) • (b.param s + b.param (-s)) = b.param 0 := by
  have hh := b.param.map_midpoint s (-s)
  simpa [midpoint_eq_smul_add] using hh.symm

private theorem antipode_pair_base {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ} {p q : V}
    (b : BallChart C u p q) {n} (hn : ‖n‖ = 1) :
    pairBase C u (b.param n) (b.param (-n)) = pairBase C u p q := by
  ext x
  constructor
  · rintro ⟨hx, hF⟩
    refine ⟨hx, fun F hp hq => hF F ?_ ?_⟩
    · exact (chart_mem b hn.le).2 F hp hq
    · exact (chart_mem b (by simp [hn] : ‖-n‖ ≤ 1)).2 F hp hq
  · rintro ⟨hx, hF⟩
    refine ⟨hx, fun F ha hr => ?_⟩
    have hc : b.param 0 ∈ F := by
      rw [← chart_midpoint b n]
      exact F.toPointedCone.smul_mem (by norm_num) (F.toPointedCone.add_mem ha hr)
    have hxball : x ∈ b.param '' Metric.closedBall 0 1 := b.whole.symm ▸ ⟨hx, hF⟩
    obtain ⟨s, hs, rfl⟩ := hxball
    have hss : ‖s‖ ≤ 1 := by simpa using hs
    have hxC := (chart_mem b hss).1.1
    have hyC := (chart_mem b (by simpa using hss : ‖-s‖ ≤ 1)).1.1
    apply F.isFaceOf.mem_of_smul_add_smul_mem_left hxC hyC
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    change (1 / 2 : ℝ) • b.param s + (1 / 2 : ℝ) • b.param (-s) ∈ F
    rw [← smul_add, chart_midpoint]
    exact hc

private abbrev rebaseChart {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ} {p q : V}
    (b : BallChart C u p q) {n} (hn : ‖n‖ = 1) :
    BallChart C u (b.param n) (b.param (-n)) where
  dim := b.dim
  dim_pos := b.dim_pos
  param := b.param
  injective := b.injective
  whole := b.whole.trans (antipode_pair_base b hn).symm

private theorem support_effects {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hclosed : IsClosed (C : Set V)) (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hB : wholePairBalls C u) (hH : commonSupport C u) :
    (∀ p : pure C u, confirms C u p (supportEffect hH p)) ∧
    (∀ (p : pure C u) h, confirms C u p h → ∀ x ∈ C, supportEffect hH p x ≤ h x) ∧
    (∀ p q : pure C u, supportEffect hH p q = supportEffect hH q p) := by
  have hg (p : pure C u) := Classical.choose_spec (hH p)
  have he (p : pure C u) : supportEffect hH p p = 1 := by
    change ((Classical.choose (hH p)) p)⁻¹ * (Classical.choose (hH p)) p = 1
    exact inv_mul_cancel₀ (hg p).2.1.ne'
  have hformula (p q : pure C u) (hpq : p ≠ q) (b : BallChart C u p q)
      {n} (hn : ‖n‖ = 1) (hpn : b.param n = p) :
      ∀ s, supportEffect hH p (b.param s) = (1 + ⟪n, s⟫) / 2 :=
    support_formula b _ (hg p).1 (hg p).2.1 hn hpn ((hg p).2.2 q hpq b n hn hpn)
  have hK := base_compact hclosed hstrict
  have hconf (p : pure C u) : confirms C u p (supportEffect hH p) := by
    refine ⟨cone_bound hK hstrict (fun q => ?_), he p⟩
    by_cases hpq : p = q
    · subst q; rw [he]; exact ⟨by norm_num, le_rfl⟩
    obtain ⟨b⟩ := hB p q hpq
    obtain ⟨n, hn, hpn⟩ := endpoint_coordinates p q b
    obtain ⟨m, hm, hqm⟩ := endpoint_coordinates q p (swapChart b)
    have hv := hformula p q hpq b hn hpn m
    change supportEffect hH p (b.param m) = _ at hv
    change b.param m = q at hqm
    rw [hqm] at hv
    have hi : |⟪n, m⟫| ≤ 1 := by simpa [hn, hm] using abs_real_inner_le_norm n m
    rw [hv]
    constructor <;> linarith [(abs_le.mp hi).1, (abs_le.mp hi).2]
  have hleast (p : pure C u) (h : V →ₗ[ℝ] ℝ) (hh : confirms C u p h) :
      ∀ x ∈ C, supportEffect hH p x ≤ h x := by
    have hnon (q : pure C u) : 0 ≤ (h - supportEffect hH p) q := by
      simp only [LinearMap.sub_apply, sub_nonneg]
      by_cases hpq : p = q
      · subst q; rw [he, hh.2]
      obtain ⟨b⟩ := hB p q hpq
      obtain ⟨n, hn, hpn⟩ := endpoint_coordinates p q b
      obtain ⟨m, hm, hqm⟩ := endpoint_coordinates q p (swapChart b)
      change b.param m = q at hqm
      rw [← hqm, hformula p q hpq b hn hpn]
      exact confirming_dominates_ball b hn hpn h hh m hm.le
    intro x hx
    exact sub_nonneg.mp (nonneg_on_cone hK hstrict hnon x hx)
  refine ⟨hconf, hleast, ?_⟩
  intro p q
  by_cases hpq : p = q
  · subst q; rfl
  obtain ⟨b⟩ := hB p q hpq
  obtain ⟨n, hn, hpn⟩ := endpoint_coordinates p q b
  obtain ⟨m, hm, hqm⟩ := endpoint_coordinates q p (swapChart b)
  have hleft := hformula p q hpq b hn hpn m
  have hright := hformula q p (Ne.symm hpq) (swapChart b) hm hqm n
  change b.param m = q at hqm
  change supportEffect hH q (b.param n) = _ at hright
  rw [hqm] at hleft
  rw [hpn] at hright
  rw [hleft, hright, real_inner_comm]

/-- The forward whole-face construction on the original carrier, including all
mixed-state zeros, zero-weight mixtures and every pure antipode in every pair ball. -/
theorem whole_pair_ball_confirmation
    (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ)
    (hclosed : IsClosed (C : Set V)) (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hspan : Submodule.span ℝ (C : Set V) = ⊤)
    (hB : wholePairBalls C u) (hH : commonSupport C u) :
    reciprocalLeast C u ∧ fullMixture C u ∧
    (∀ (p : pure C u) x, x ∈ base C u →
      (excludes C u p x ↔ supportEffect hH p x = 0)) ∧
    zeroMidpoint C u ∧ allAntipodes C u ∧
    (∀ (p : pure C u) (n : ℕ) (x : Fin n → V) (w : Fin n → ℝ),
      (∀ i, x i ∈ base C u) → (∀ i, 0 ≤ w i) → (∑ i, w i) = 1 →
      (excludes C u p (∑ i, w i • x i) ↔
        ∀ i, 0 < w i → excludes C u p (x i))) := by
  obtain ⟨hconf, hleast, hrecip⟩ := support_effects hclosed hstrict hB hH
  have hl : reciprocalLeast C u := ⟨supportEffect hH, hconf, hleast, hrecip⟩
  have hzero (p : pure C u) (x : V) (hx : x ∈ C) :
      excludes C u p x ↔ supportEffect hH p x = 0 := by
    constructor
    · rintro ⟨h, hh, hz⟩
      exact le_antisymm ((hleast p h hh x hx).trans_eq hz) ((hconf p).1 x hx).1
    · intro hz
      exact ⟨supportEffect hH p, hconf p, hz⟩
  have hS := full_mixture_iff_circuit_balance C u hclosed hstrict hspan
  refine ⟨hl, hS.1.mpr (hS.2.2.mpr hl), fun p x hx => hzero p x hx.1, ?_, ?_, ?_⟩
  · intro p x y hx hy hpx hpy
    apply (hzero p _ (C.smul_mem (by norm_num) (C.add_mem hx.1 hy.1))).mpr
    simp only [map_smul, map_add, (hzero p x hx.1).mp hpx, (hzero p y hy.1).mp hpy,
      add_zero, smul_zero]
  · intro p q _ b n hn _
    have ha := chart_sphere_pure b hn
    have hr := chart_sphere_pure b (by simp [hn] : ‖-n‖ = 1)
    let a : pure C u := ⟨b.param n, ha⟩
    let r : pure C u := ⟨b.param (-n), hr⟩
    have hne : a ≠ r := by
      intro heq
      have he := b.injective (congrArg Subtype.val heq)
      have hz : n = 0 := by
        have hh : (2 : ℝ) • n = 0 := by simpa [two_smul] using congrArg (fun z => z + n) he
        exact (smul_eq_zero.mp hh).resolve_left (by norm_num)
      simp [hz] at hn
    have hg := Classical.choose_spec (hH a)
    have hz := hg.2.2 r hne (rebaseChart b hn) n hn rfl
    apply (hzero a _ hr.1.1).mpr
    simp only [supportEffect, LinearMap.smul_apply, hz, smul_zero]
  · intro p n x w hx hw _
    have hxC : (∑ i, w i • x i) ∈ C :=
      C.sum_mem (fun i _ => C.smul_mem (hw i) (hx i).1)
    rw [hzero p _ hxC]
    simp only [map_sum, map_smul, smul_eq_mul]
    constructor
    · intro hz i hi
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => mul_nonneg (hw i) ((hconf p).1 _ (hx i).1).1)).mp hz i (Finset.mem_univ i)
      exact (hzero p _ (hx i).1).mpr ((mul_eq_zero.mp hterm).resolve_left hi.ne')
    · intro hz
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : w i = 0
      · rw [hi, zero_mul]
      · rw [(hzero p _ (hx i).1).mp (hz i (lt_of_le_of_ne (hw i) (Ne.symm hi))), mul_zero]

end D5.S3.Quantum.Foundation.WholePairBallConfirmation
