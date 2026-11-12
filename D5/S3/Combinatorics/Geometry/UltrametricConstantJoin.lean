/- GID: D5/S3/Combinatorics/Geometry/UltrametricConstantJoin
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:non-computational)
   anchors: []
   utility: none
   digest: Constant-distance joins preserve ultrametricity and give exact sphere and center formulas. -/

import D5.S3.Combinatorics.Geometry.DovgosheyRovenskaCentralEdges
import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
Constant cross-distance joins, the reusable construction in the pinned proof of
#29039 (ac989b58cffd1522c9c4301bb693800029516078,
ULTRAMETRIC_CENTER_SPHERE_COUNTS.md, Theorem 1.2).
The underlying set is a dependent disjoint union. No finiteness, nonemptiness,
or multiplicity hypothesis is needed for the metric construction.
-/

noncomputable section

namespace ConstantCrossDistance

variable {ι : Type} (X : ι → Type) [∀ i, MetricSpace (X i)]

/-- Distances within a component are retained; all other distances equal `a`. -/
def crossDist (a : ℝ) (p q : Sigma X) : ℝ :=
  @dite ℝ (p.1 = q.1) (Classical.propDecidable _)
    (fun h => dist (h ▸ p.2) q.2) (fun _ => a)

@[simp] theorem crossDist_same (a : ℝ) (i : ι) (x y : X i) :
    crossDist X a ⟨i, x⟩ ⟨i, y⟩ = dist x y := by
  simp [crossDist]

@[simp] theorem crossDist_cross (a : ℝ) {i j : ι} (h : i ≠ j)
    (x : X i) (y : X j) : crossDist X a ⟨i, x⟩ ⟨j, y⟩ = a := by
  simp [crossDist, h]

theorem crossDist_nonneg {a : ℝ} (ha : 0 ≤ a) (p q : Sigma X) :
    0 ≤ crossDist X a p q := by
  unfold crossDist
  split
  · exact dist_nonneg
  · exact ha

theorem crossDist_comm (a : ℝ) (p q : Sigma X) :
    crossDist X a p q = crossDist X a q p := by
  rcases p with ⟨i, x⟩
  rcases q with ⟨j, y⟩
  by_cases h : i = j
  · subst j
    simp [dist_comm]
  · simp [crossDist, h, Ne.symm h]

/-- A dependent disjoint union recording the chosen join metric parameters. -/
structure Join (a : ℝ) (_ha : 0 < a)
    (_hb : ∀ i (x y : X i), dist x y ≤ a) where
  fst : ι
  snd : X fst

variable [∀ i, IsUltrametricDist (X i)]

/-- A non-strict component diameter bound already suffices for ultrametricity. -/
theorem crossDist_triangle_max (a : ℝ)
    (hb : ∀ i (x y : X i), dist x y ≤ a) (p q r : Sigma X) :
    crossDist X a p r ≤ max (crossDist X a p q) (crossDist X a q r) := by
  rcases p with ⟨i, x⟩
  rcases q with ⟨j, y⟩
  rcases r with ⟨k, z⟩
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      simpa using IsUltrametricDist.dist_triangle_max x y z
    · simp [crossDist, hik]
  · by_cases hjk : j = k
    · subst k
      simp [crossDist, hij]
    · by_cases hik : i = k
      · subst k
        simpa [crossDist, hij, Ne.symm hij] using hb i x z
      · simp [crossDist, hij, hjk, hik]

/-- Install explicitly with `letI := metricSpace X a ha hb`.
This avoids imposing a competing global metric on `Sigma X`. -/
@[instance_reducible] def metricSpace (a : ℝ) (ha : 0 < a)
    (hb : ∀ i (x y : X i), dist x y ≤ a) : MetricSpace (Sigma X) where
  dist := crossDist X a
  dist_self := by rintro ⟨i, x⟩; simp
  dist_comm := crossDist_comm X a
  dist_triangle := by
    intro p q r
    exact (crossDist_triangle_max X a hb p q r).trans
      (max_le (le_add_of_nonneg_right (crossDist_nonneg X ha.le q r))
        (le_add_of_nonneg_left (crossDist_nonneg X ha.le p q)))
  eq_of_dist_eq_zero := by
    rintro ⟨i, x⟩ ⟨j, y⟩ h
    by_cases hij : i = j
    · subst j
      simp only [crossDist_same] at h
      exact congrArg (Sigma.mk i) (dist_eq_zero.mp h)
    · have : a = 0 := by simpa [crossDist, hij] using h
      exact (ha.ne' this).elim

variable (a : ℝ) (ha : 0 < a) (hb : ∀ i (x y : X i), dist x y ≤ a)

instance joinMetric : MetricSpace (Join X a ha hb) :=
  @MetricSpace.induced _ _ (fun p => (⟨p.fst, p.snd⟩ : Sigma X))
    (by intro p q h; cases p; cases q; cases h; rfl) (metricSpace X a ha hb)

/-- The join uses Mathlib's ultrametric mixin. -/
@[instance] theorem isUltrametricDist : IsUltrametricDist (Join X a ha hb) :=
  ⟨fun p q r => crossDist_triangle_max X a hb
    ⟨p.fst, p.snd⟩ ⟨q.fst, q.snd⟩ ⟨r.fst, r.snd⟩⟩

@[simp] theorem dist_same (i : ι) (x y : X i) :
    dist (⟨i, x⟩ : Join X a ha hb) ⟨i, y⟩ = dist x y := crossDist_same X a i x y

@[simp] theorem dist_cross {i j : ι} (h : i ≠ j) (x : X i) (y : X j) :
    dist (⟨i, x⟩ : Join X a ha hb) ⟨j, y⟩ = a := crossDist_cross X a h x y

/-- At any radius other than the cross-distance, witnesses stay in their component. -/
theorem sphere_witness_iff (i : ι) (x : X i) {t : ℝ} (ht : t ≠ a) :
    (∃ q : Join X a ha hb, dist q ⟨i, x⟩ = t) ↔ ∃ y : X i, dist y x = t := by
  constructor
  · rintro ⟨⟨j, y⟩, hy⟩
    by_cases h : j = i
    · subst j
      exact ⟨y, by simpa only [dist_same] using hy⟩
    · have : a = t := by simpa [dist_cross X a ha hb h] using hy
      exact (ht this.symm).elim
  · rintro ⟨y, hy⟩
    exact ⟨⟨i, y⟩, by simpa only [dist_same] using hy⟩

/-- Below the join level the whole sphere is the image of the old sphere. -/
theorem sphere_eq_image (i : ι) (x : X i) {t : ℝ} (ht : t ≠ a) :
    Metric.sphere (⟨i, x⟩ : Join X a ha hb) t =
      (fun y : X i => (⟨i, y⟩ : Join X a ha hb)) '' Metric.sphere x t := by
  ext q
  rcases q with ⟨j, y⟩
  by_cases h : j = i
  · subst j
    simp [Metric.mem_sphere]
  · have hne : (⟨j, y⟩ : Join X a ha hb) ∉ (fun y : X i => (⟨i, y⟩ : Join X a ha hb)) '' Metric.sphere x t := by
      rintro ⟨z, _, hz⟩
      exact h (congrArg Join.fst hz).symm
    simp [Metric.mem_sphere, dist_cross X a ha hb h, Ne.symm ht, hne]

/-- Strict component bounds identify the top sphere with the outside components. -/
theorem sphere_top (hs : ∀ i (x y : X i), dist x y < a) (p : Join X a ha hb) :
    Metric.sphere p a = {q | q.1 ≠ p.1} := by
  rcases p with ⟨i, x⟩
  ext q
  rcases q with ⟨j, y⟩
  by_cases h : j = i
  · subst j
    simp [Metric.mem_sphere, (hs i y x).ne]
  · simp [Metric.mem_sphere, dist_cross X a ha hb h, h]

/-- Sphere counts at every radius different from `a` are retained exactly. -/
theorem sphere_card (i : ι) (x : X i) {t : ℝ} (ht : t ≠ a) :
    Nat.card (Metric.sphere (⟨i, x⟩ : Join X a ha hb) t) =
      Nat.card (Metric.sphere x t) := by
  simp only [Nat.card_coe_set_eq]
  rw [sphere_eq_image X a ha hb i x ht]
  exact Set.ncard_image_of_injective _ (by intro x y h; cases h; rfl)

/-- Forgetting the metric identifies the join with its dependent disjoint union. -/
def equivSigma : Join X a ha hb ≃ Sigma X where
  toFun p := ⟨p.fst, p.snd⟩
  invFun p := ⟨p.fst, p.snd⟩
  left_inv := by rintro ⟨i, x⟩; rfl
  right_inv := by rintro ⟨i, x⟩; rfl

omit [∀ i, IsUltrametricDist (X i)] in
theorem card_join : Nat.card (Join X a ha hb) = Nat.card (Sigma X) :=
  Nat.card_congr (equivSigma X a ha hb)

instance finiteJoin [Finite ι] [∀ i, Finite (X i)] : Finite (Join X a ha hb) :=
  Finite.of_equiv (Sigma X) (equivSigma X a ha hb).symm

omit [∀ i, IsUltrametricDist (X i)] in
/-- The order of a finite join is the sum of its component orders. -/
theorem card_join_sum [Fintype ι] [∀ i, Finite (X i)] :
    Nat.card (Join X a ha hb) = ∑ i, Nat.card (X i) := by
  rw [card_join X a ha hb, Nat.card_sigma]

/-- The sphere at the join level has total order minus the component order. -/
theorem sphere_top_card [Finite ι] [∀ i, Finite (X i)]
    (hs : ∀ i (x y : X i), dist x y < a) (i : ι) (x : X i) :
    Nat.card (Metric.sphere (⟨i, x⟩ : Join X a ha hb) a) =
      Nat.card (Join X a ha hb) - Nat.card (X i) := by
  rw [Nat.card_coe_set_eq, sphere_top X a ha hb hs]
  have he : {q : Join X a ha hb | q.fst ≠ i} =
      ((fun y : X i => (⟨i, y⟩ : Join X a ha hb)) '' Set.univ)ᶜ := by
    ext q
    rcases q with ⟨j, y⟩
    by_cases h : j = i
    · subst j
      simp
    · simp [h, Ne.symm h]
  rw [he, Set.ncard_compl, Set.ncard_image_of_injective _
    (by intro x y h; cases h; rfl), Set.ncard_univ]

open D5.S3.Combinatorics.Geometry.DovgosheyRovenskaCentralEdges

/-- The existing distance-center predicate is preserved componentwise away from `a`.
The explicit sign condition also covers an empty index type. -/
theorem mem_center_iff {t : ℝ} (ht : t ≠ a) :
    t ∈ center (Join X a ha hb) ↔ 0 ≤ t ∧ ∀ i, t ∈ center (X i) := by
  constructor
  · rintro ⟨ht0, htall⟩
    exact ⟨ht0, fun i => ⟨ht0, fun x =>
      (sphere_witness_iff X a ha hb i x ht).mp (htall ⟨i, x⟩)⟩⟩
  · rintro ⟨ht0, h⟩
    refine ⟨ht0, ?_⟩
    rintro ⟨i, x⟩
    exact (sphere_witness_iff X a ha hb i x ht).mpr ((h i).2 x)

/-- The top radius is central exactly when every point has an occupied
component different from its own. This includes empty and singleton joins. -/
theorem top_mem_center_iff (hs : ∀ i (x y : X i), dist x y < a) :
    a ∈ center (Join X a ha hb) ↔
      ∀ i, X i → ∃ j, Nonempty (X j) ∧ j ≠ i := by
  constructor
  · rintro ⟨_, h⟩ i x
    obtain ⟨q, hq⟩ := h ⟨i, x⟩
    have hm : q ∈ Metric.sphere (⟨i, x⟩ : Join X a ha hb) a := hq
    rw [sphere_top X a ha hb hs] at hm
    exact ⟨q.fst, ⟨q.snd⟩, hm⟩
  · intro h
    refine ⟨ha.le, ?_⟩
    rintro ⟨i, x⟩
    obtain ⟨j, ⟨y⟩, hji⟩ := h i x
    exact ⟨⟨j, y⟩, dist_cross X a ha hb hji y x⟩

/-- Exact center formula under strict component bounds, retaining the original
project definition rather than introducing a replacement center predicate. -/
theorem center_eq (hs : ∀ i (x y : X i), dist x y < a) :
    center (Join X a ha hb) =
      {t | 0 ≤ t ∧ t ≠ a ∧ ∀ i, t ∈ center (X i)} ∪
      {t | t = a ∧ ∀ i, X i → ∃ j, Nonempty (X j) ∧ j ≠ i} := by
  ext t
  by_cases ht : t = a
  · subst t
    simp [top_mem_center_iff X a ha hb hs]
  · simp [ht, mem_center_iff X a ha hb ht]

end ConstantCrossDistance
