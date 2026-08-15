/- GID: D5/S3/Observer/Separation/InvariantObservableInfinity
   generality: G
   mirror-B: D5/B/S3/Observer/Separation/InvariantObservableInfinity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A bounded invariant observable separating two points forces infinite distance. -/

import D5.S3.Observer.ObserverMetric
import Mathlib.Data.ENNReal.Real
import Mathlib.Topology.MetricSpace.Bounded

/- Library-search audit trail (2026-08-15):
   * Loogle query `iSup_eq_top` found the exact supremum criterion used below.
   * Loogle queries `exists_nat_gt`, `Metric.isBounded_range_iff`, and
     `dist_smul_pair` found the exact Archimedean, bounded-range, and scalar-distance
     support lemmas used below.
   * LeanSearch query `If a bounded observable is invariant under a permutation and
     separates two points, then the supremum of all unit update-defect observable gaps
     is infinite.` returned permutation-sum lemmas but no matching distance theorem.
   * Repository shape searches found only the concrete solenoid instance
     `visible_phase_separation_distance_eq_top`; no general invariant-separation theorem
     or formalization receipt matched this statement.
-/

namespace D5.S3.Observer.Separation.InvariantObservableInfinity

open D5.S3.Observer.ObserverMetric

/-- Bounded complex observables whose pointwise update defect is at most one. -/
def admissibleObservable {index : Type*} (tau : Equiv.Perm index) :
    Set (index -> Complex) :=
  {f | Bornology.IsBounded (Set.range f) ∧
    ∀ i, ‖updateDefect tau f i‖ ≤ 1}

/-- The extended observer distance obtained by maximizing admissible endpoint gaps. -/
noncomputable def invariantObserverDistance {index : Type*}
    (tau : Equiv.Perm index) (x y : index) : ENNReal :=
  ⨆ f : admissibleObservable tau, ENNReal.ofReal ‖f.1 x - f.1 y‖

/-- A bounded update-invariant observable that separates two points can be scaled
without increasing its update defect, forcing their observer distance to be infinite. -/
theorem invariant_separation_distance_eq_top {index : Type*}
    (tau : Equiv.Perm index) (f : index -> Complex) (x y : index)
    (hbounded : Bornology.IsBounded (Set.range f))
    (hinvariant : updateDefect tau f = 0)
    (hseparates : f x ≠ f y) :
    invariantObserverDistance tau x y = ⊤ := by
  apply iSup_eq_top.mpr
  intro b hb
  let gap : Real := ‖f x - f y‖
  have hgap : 0 < gap := norm_pos_iff.mpr (sub_ne_zero.mpr hseparates)
  obtain ⟨m, hm⟩ := exists_nat_gt (b.toReal / gap)
  have hscaled_bounded :
      Bornology.IsBounded (Set.range ((m : Complex) • f)) := by
    rw [Metric.isBounded_range_iff] at hbounded ⊢
    rcases hbounded with ⟨C, hC⟩
    refine ⟨‖(m : Complex)‖ * C, fun i j => ?_⟩
    calc
      dist (((m : Complex) • f) i) (((m : Complex) • f) j) ≤
          dist (m : Complex) 0 * dist (f i) (f j) := by
        simpa only [Pi.smul_apply] using
          dist_smul_pair (m : Complex) (f i) (f j)
      _ ≤ ‖(m : Complex)‖ * C := by
        simpa only [dist_zero_right] using
          mul_le_mul_of_nonneg_left (hC i j) (norm_nonneg (m : Complex))
  refine ⟨⟨(m : Complex) • f, hscaled_bounded, ?_⟩, ?_⟩
  · intro i
    have hi : f (tau.symm i) - f i = 0 := by
      simpa [updateDefect] using congrFun hinvariant i
    simp only [updateDefect, Pi.smul_apply, smul_eq_mul]
    rw [← mul_sub, hi, mul_zero, norm_zero]
    norm_num
  · simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_sub]
    change b < ENNReal.ofReal (‖(m : Complex) * (f x - f y)‖)
    rw [norm_mul, Complex.norm_natCast]
    apply (ENNReal.lt_ofReal_iff_toReal_lt hb.ne).mpr
    simpa [gap] using (div_lt_iff₀ hgap).mp hm

/-- The hypotheses are jointly satisfiable on a two-point domain, and the conclusion
is nontrivial there. -/
example :
    let tau : Equiv.Perm Bool := Equiv.refl _
    let f : Bool -> Complex := fun b => if b then 1 else 0
    updateDefect tau f = 0 ∧
      f false ≠ f true ∧
      invariantObserverDistance tau false true = ⊤ := by
  dsimp
  have hbounded :
      Bornology.IsBounded
        (Set.range (fun b : Bool => if b then (1 : Complex) else 0)) := by
    rw [Metric.isBounded_range_iff]
    refine ⟨1, fun i j => ?_⟩
    cases i <;> cases j <;> norm_num
  have hinvariant :
      updateDefect (Equiv.refl Bool)
        (fun b : Bool => if b then (1 : Complex) else 0) = 0 := by
    funext i
    change (if i then (1 : Complex) else 0) - (if i then 1 else 0) = 0
    exact sub_self _
  refine ⟨hinvariant, by norm_num, ?_⟩
  exact invariant_separation_distance_eq_top
    (Equiv.refl Bool) (fun b : Bool => if b then (1 : Complex) else 0)
    false true hbounded hinvariant (by norm_num)

end D5.S3.Observer.Separation.InvariantObservableInfinity
