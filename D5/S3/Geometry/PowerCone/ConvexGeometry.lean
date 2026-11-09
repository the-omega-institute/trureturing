/- GID: D5/S3/Geometry/PowerCone/ConvexGeometry
   generality: I
   mirror-B: D5/B/S3/Geometry/PowerCone/ConvexGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Formalized power-cone geometry and analytic support module. -/

import D5.S3.Geometry.PowerCone.PrimalDikin
import D5.S3.Analytic.ConvexBarrier.OriginalConeRecession
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.Topology

/-!
Geometry of the actual closedCone definition. Weighted geometric mean
superadditivity is derived from Mathlib's weighted two-term AM--GM;
neither convexity nor interior-plus-cone stability is an assumption.
Zero coordinates are treated explicitly before normalizing positive sums.

The normed-space geometry is standard; the chord theorem in
OriginalConeChords specializes to V=R and makes no vector optimality claim.
SOURCE ONLY, UNCOMPILED; immutable ScalarSection/Topology are not edited.
-/

open Set
open D5.S3.Analytic.ConvexBarrier

namespace D5.S3.Geometry.PowerCone

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Weighted geometric mean superadditivity, including all zero faces.
The positive-sum case is AM--GM on x/(x+u), y/(y+v), and the
complementary pair; the two arithmetic right sides add to one. -/
theorem weight_superadditive {c x y u v : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    weight c x y+weight c u v ≤ weight c (x+u) (y+v) := by
  have hc' : 0 < 1-c := sub_pos.mpr hc1
  by_cases hX0 : x+u = 0
  · have hx0 : x = 0 := by linarith
    have hu0 : u = 0 := by linarith
    simp [weight, hx0, hu0, Real.zero_rpow hc.ne']
  by_cases hY0 : y+v = 0
  · have hy0 : y = 0 := by linarith
    have hv0 : v = 0 := by linarith
    simp [weight, hy0, hv0, Real.zero_rpow hc'.ne']
  have hX : 0 < x+u := lt_of_le_of_ne (add_nonneg hx hu) (Ne.symm hX0)
  have hY : 0 < y+v := lt_of_le_of_ne (add_nonneg hy hv) (Ne.symm hY0)
  have hw : 0 < weight c (x+u) (y+v) :=
    mul_pos (Real.rpow_pos_of_pos hX _) (Real.rpow_pos_of_pos hY _)
  have hnormalize {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
      weight c (a/(x+u)) (b/(y+v)) =
        weight c a b/weight c (x+u) (y+v) := by
    unfold weight
    rw [Real.div_rpow ha hX.le, Real.div_rpow hb hY.le]
    exact div_mul_div_comm _ _ _ _
  have h1 := Real.geom_mean_le_arith_mean2_weighted hc.le hc'.le
    (div_nonneg hx hX.le) (div_nonneg hy hY.le) (by ring : c+(1-c) = 1)
  have h2 := Real.geom_mean_le_arith_mean2_weighted hc.le hc'.le
    (div_nonneg hu hX.le) (div_nonneg hv hY.le) (by ring : c+(1-c) = 1)
  change weight c (x/(x+u)) (y/(y+v)) ≤ _ at h1
  change weight c (u/(x+u)) (v/(y+v)) ≤ _ at h2
  rw [hnormalize hx hy] at h1
  rw [hnormalize hu hv] at h2
  have hrhs : c*(x/(x+u))+(1-c)*(y/(y+v))+
      (c*(u/(x+u))+(1-c)*(v/(y+v))) = 1 := by
    field_simp [hX.ne', hY.ne']
    <;> ring
  have hh : (weight c x y+weight c u v)/weight c (x+u) (y+v) ≤ 1 := by
    rw [add_div]
    linarith
  exact (div_le_one hw).mp hh

/-- Nonnegative scaling of the actual closed cone, including t=0. -/
theorem closedCone_nonnegScale {c t : ℝ} (hc : 0 < c) (hc1 : c < 1)
    (ht : 0 ≤ t) {p : Point V} (hp : p ∈ closedCone c) :
    t • p ∈ closedCone c := by
  rcases eq_or_lt_of_le ht with he | ht'
  · have ht0 : t = 0 := he.symm
    simp [ht0, closedCone, weight, Real.zero_rpow hc.ne']
  · change 0 ≤ t*p.1.1 ∧ 0 ≤ t*p.1.2 ∧
      ‖t • p.2‖ ≤ weight c (t*p.1.1) (t*p.1.2)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht', weight_posScale ht' hp.1 hp.2.1]
    exact ⟨mul_nonneg ht hp.1, mul_nonneg ht hp.2.1,
      mul_le_mul_of_nonneg_left hp.2.2 ht⟩

theorem closedCone_add {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    {p r : Point V} (hp : p ∈ closedCone c) (hr : r ∈ closedCone c) :
    p+r ∈ closedCone c := by
  change 0 ≤ p.1.1+r.1.1 ∧ 0 ≤ p.1.2+r.1.2 ∧
    ‖p.2+r.2‖ ≤ weight c (p.1.1+r.1.1) (p.1.2+r.1.2)
  refine ⟨add_nonneg hp.1 hr.1, add_nonneg hp.2.1 hr.2.1, ?_⟩
  calc
    ‖p.2+r.2‖ ≤ ‖p.2‖+‖r.2‖ := norm_add_le _ _
    _ ≤ weight c p.1.1 p.1.2+weight c r.1.1 r.1.2 := add_le_add hp.2.2 hr.2.2
    _ ≤ _ := weight_superadditive hc hc1 hp.1 hp.2.1 hr.1 hr.2.1

theorem closedCone_convex {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    Convex ℝ (closedCone c : Set (Point V)) := by
  intro p hp r hr a b ha hb hab
  exact closedCone_add hc hc1 (closedCone_nonnegScale hc hc1 ha hp)
    (closedCone_nonnegScale hc hc1 hb hr)

theorem coneInterior_convex {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    Convex ℝ (coneInterior c : Set (Point V)) := by
  rw [coneInterior_eq_interior hc.le hc1.le]
  exact (closedCone_convex hc hc1).interior

/-- Positive scaling on the actual strict inequalities. -/
theorem coneInterior_posScale {c t : ℝ} (ht : 0 < t)
    {p : Point V} (hp : p ∈ coneInterior c) : t • p ∈ coneInterior c := by
  change 0 < t*p.1.1 ∧ 0 < t*p.1.2 ∧
    ‖t • p.2‖ < weight c (t*p.1.1) (t*p.1.2)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, weight_posScale ht hp.1.le hp.2.1.le]
  exact ⟨mul_pos ht hp.1, mul_pos ht hp.2.1,
    mul_lt_mul_of_pos_left hp.2.2 ht⟩

/-- The actual interior-plus-closed-cone inclusion. In particular the
second point may be on a coordinate-zero face or at the origin. -/
theorem coneInterior_add_closedCone {c : ℝ} (hc : 0 < c) (hc1 : c < 1)
    {p r : Point V} (hp : p ∈ coneInterior c) (hr : r ∈ closedCone c) :
    p+r ∈ coneInterior c := by
  change 0 < p.1.1+r.1.1 ∧ 0 < p.1.2+r.1.2 ∧
    ‖p.2+r.2‖ < weight c (p.1.1+r.1.1) (p.1.2+r.1.2)
  refine ⟨add_pos_of_pos_of_nonneg hp.1 hr.1,
    add_pos_of_pos_of_nonneg hp.2.1 hr.2.1, ?_⟩
  calc
    ‖p.2+r.2‖ ≤ ‖p.2‖+‖r.2‖ := norm_add_le _ _
    _ < weight c p.1.1 p.1.2+weight c r.1.1 r.1.2 :=
      add_lt_add_of_lt_of_le hp.2.2 hr.2.2
    _ ≤ _ := weight_superadditive hc hc1 hp.1.le hp.2.1.le hr.1 hr.2.1

/-- All geometric inputs of the analytic recession theorem are discharged
from 0<c<1 and the existing closedCone/coneInterior definitions. -/
theorem actual_powerCone_rayGeometry {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    ConeRayGeometry (coneInterior c : Set (Point V)) (closedCone c) := by
  refine ⟨coneInterior_convex hc hc1, ?_, ?_, ?_⟩
  · exact fun p hp t ht => coneInterior_posScale ht hp
  · exact fun p hp t ht => closedCone_nonnegScale hc hc1 ht hp
  · exact fun p hp r hr => coneInterior_add_closedCone hc hc1 hp hr

/-- Closedness and convexity concern precisely the same actual cone. -/
theorem actual_powerCone_closed_convex {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    IsClosed (closedCone c : Set (Point V)) ∧ Convex ℝ (closedCone c : Set (Point V)) :=
  ⟨closedCone_isClosed hc.le hc1.le, closedCone_convex hc hc1⟩

end D5.S3.Geometry.PowerCone
