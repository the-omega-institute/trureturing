/- GID: D5/S3/Observer/MetricGeometry/OrbitConnesDistance
   generality: G
   mirror-B: D5/B/S3/Observer/MetricGeometry/OrbitConnesDistance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Update-defect observables recover distance on the integer shift orbit. -/

import D5.S3.Observer.ObserverMetric
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Instances.Int
import Mathlib.Order.ConditionallyCompleteLattice.Basic

namespace D5.S3.Observer.MetricGeometry.OrbitConnesDistance

open Set
open D5.S3.Observer.ObserverMetric

/-- Bounded real observables whose one-step update defects have norm at most one. -/
def orbitLipBall : Set (Int → Real) :=
  {f | Bornology.IsBounded (Set.range f) ∧
    ∀ k, ‖updateDefect (Equiv.addRight (1 : Int)) (fun i => (f i : Complex)) k‖ ≤ 1}

/-- Point gaps attained by bounded observables in the orbit Lipschitz ball. -/
def orbitGapSet (m n : Int) : Set Real :=
  {r | ∃ f ∈ orbitLipBall, r = dist (f m) (f n)}

/-- The supremum of observable gaps subject to the unit Lipschitz constraint. -/
noncomputable def orbitConnesDistance (m n : Int) : Real :=
  sSup (orbitGapSet m n)

/-- A bounded distance coordinate clipped at the distance between the selected points. -/
def clippedDistanceObservable (m n k : Int) : Real :=
  min (dist k m) (dist m n)

/-- Every observable in the ball has unit-bounded defect under one shift step. -/
theorem orbitLipBall_unit_update_defect {f : Int → Real} (hf : f ∈ orbitLipBall) (k : Int) :
    dist (f (k + 1)) (f k) ≤ 1 := by
  simpa [updateDefect, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, Real.dist_eq, abs_sub_comm] using hf.2 (k + 1)

private theorem dist_le_natCast_of_add_nat {f : Int → Real}
    (hstep : ∀ k, dist (f (k + 1)) (f k) ≤ 1) (m : Int) (d : Nat) :
    dist (f m) (f (m + d)) ≤ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      calc
        dist (f m) (f (m + (d.succ : Int))) ≤
            dist (f m) (f (m + d)) +
              dist (f (m + d)) (f (m + (d.succ : Int))) := dist_triangle _ _ _
        _ ≤ (d : Real) + 1 := by
          gcongr
          simpa [Nat.cast_succ, dist_comm, add_assoc] using hstep (m + d)
        _ = (d.succ : Real) := by simp

private theorem orbitLipBall_dist_le_of_le {f : Int → Real} (hf : f ∈ orbitLipBall)
    {m n : Int} (hmn : m ≤ n) : dist (f m) (f n) ≤ dist m n := by
  let d := (n - m).toNat
  have hd : (d : Int) = n - m := Int.toNat_of_nonneg (sub_nonneg.mpr hmn)
  have hn : n = m + (d : Int) := by omega
  rw [hn]
  simpa [Int.dist_eq] using
    dist_le_natCast_of_add_nat (orbitLipBall_unit_update_defect hf) m d

private theorem orbitLipBall_dist_le {f : Int → Real} (hf : f ∈ orbitLipBall) (m n : Int) :
    dist (f m) (f n) ≤ dist m n := by
  rcases le_total m n with hmn | hnm
  · exact orbitLipBall_dist_le_of_le hf hmn
  · rw [dist_comm (f m), dist_comm m]
    exact orbitLipBall_dist_le_of_le hf hnm

/-- The clipped distance coordinate is a bounded member of the orbit Lipschitz ball. -/
private theorem clippedDistanceObservable_mem (m n : Int) :
    clippedDistanceObservable m n ∈ orbitLipBall := by
  constructor
  · apply (Metric.isBounded_Icc (0 : Real) (dist m n)).subset
    rintro _ ⟨k, rfl⟩
    exact ⟨le_min dist_nonneg dist_nonneg, min_le_right _ _⟩
  · intro k
    have hdist :
        dist (clippedDistanceObservable m n (k - 1))
            (clippedDistanceObservable m n k) ≤ 1 := by
      simpa [clippedDistanceObservable] using
        ((LipschitzWith.dist_left m).min_const (dist m n)).dist_le_mul (k - 1) k
    change ‖((clippedDistanceObservable m n (k - 1) : Real) : Complex) -
      (clippedDistanceObservable m n k : Complex)‖ ≤ 1
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    simpa [Real.dist_eq] using hdist

/-- The clipped distance coordinate attains the full distance between its selected endpoints. -/
private theorem clippedDistanceObservable_attains (m n : Int) :
    dist (clippedDistanceObservable m n m) (clippedDistanceObservable m n n) =
      dist m n := by
  simp [clippedDistanceObservable, dist_comm, abs_of_nonneg dist_nonneg]

private theorem orbitGapSet_nonempty (m n : Int) : (orbitGapSet m n).Nonempty := by
  refine ⟨0, fun _ => 0, ?_, by simp⟩
  constructor
  · rw [Metric.isBounded_range_iff]
    exact ⟨0, by simp⟩
  · simp [updateDefect]

private theorem orbitGapSet_le (m n : Int) {r : Real} (hr : r ∈ orbitGapSet m n) :
    r ≤ dist m n := by
  rcases hr with ⟨f, hf, rfl⟩
  exact orbitLipBall_dist_le hf m n

private theorem orbitGapSet_bddAbove (m n : Int) : BddAbove (orbitGapSet m n) :=
  ⟨dist m n, fun _ => orbitGapSet_le m n⟩

private theorem orbitGapSet_attains (m n : Int) : dist m n ∈ orbitGapSet m n := by
  refine ⟨clippedDistanceObservable m n, clippedDistanceObservable_mem m n, ?_⟩
  exact (clippedDistanceObservable_attains m n).symm

/-- The supremal bounded-observable gap on the free integer orbit equals its metric distance. -/
theorem orbit_connes_distance_eq (m n : Int) :
    orbitConnesDistance m n = dist m n := by
  apply le_antisymm
  · exact csSup_le (orbitGapSet_nonempty m n) fun r hr => orbitGapSet_le m n hr
  · exact le_csSup (orbitGapSet_bddAbove m n) (orbitGapSet_attains m n)

/-- From the orbit origin, the distance is the absolute value of the integer displacement. -/
theorem orbit_distance_from_zero (n : Int) :
    orbitConnesDistance 0 n = |(n : Real)| := by
  rw [orbit_connes_distance_eq, Int.dist_eq]
  simp

/-- A nonconstant admissible observable explicitly attains distance three. -/
theorem orbit_distance_three_witness :
    ∃ f ∈ orbitLipBall,
      f 0 ≠ f 3 ∧ dist (f 0) (f 3) = 3 := by
  have hgap :
      dist (clippedDistanceObservable 0 3 0) (clippedDistanceObservable 0 3 3) = 3 := by
    rw [clippedDistanceObservable_attains]
    norm_num [Int.dist_eq]
  refine ⟨clippedDistanceObservable 0 3, clippedDistanceObservable_mem 0 3, ?_, hgap⟩
  intro h
  rw [h, dist_self] at hgap
  norm_num at hgap

/-- The orbit points zero and three have supremal observable gap three. -/
theorem orbit_distance_three : orbitConnesDistance 0 3 = 3 := by
  rw [orbit_connes_distance_eq]
  norm_num [Int.dist_eq]

end D5.S3.Observer.MetricGeometry.OrbitConnesDistance
