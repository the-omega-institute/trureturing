/- GID: D5/S1/Dynamics/PeriodicOrbits/SkewAdditiveReturn
   generality: G
   mirror-B: D5/B/S1/Dynamics/PeriodicOrbits/SkewAdditiveReturn
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Orbit holonomy determines exact returns and minimal periods of additive skew dynamics. -/

import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.GroupTheory.OrderOfElement

namespace D5.S1.Dynamics.PeriodicOrbits.SkewAdditiveReturn

open Function

variable {X A : Type*} [AddCommGroup A]

/-- The charge is evaluated at the current base state before the base advances. -/
def skewStep (f : X → X) (c : X → A) : X × A → X × A :=
  fun z => (f z.1, z.2 + c z.1)

/-- The actual skew orbit transports the fiber by the Birkhoff sum along its base orbit. -/
theorem skew_iterate (f : X → X) (c : X → A) (n : ℕ) (x : X) (a : A) :
    (skewStep f c)^[n] (x, a) = (f^[n] x, a + birkhoffSum f c n x) := by
  induction n with
  | zero => simp [birkhoffSum_zero]
  | succ n ih =>
    rw [iterate_succ_apply', ih, birkhoffSum_succ, iterate_succ_apply']
    simp [skewStep, add_assoc]

/-- Any returning base block repeats its same holonomy; the block need not be minimal. -/
theorem skew_iterate_block (f : X → X) (c : X → A) {p : ℕ} {x : X}
    (hp : IsPeriodicPt f p x) (k : ℕ) (a : A) :
    (skewStep f c)^[p * k] (x, a) = (x, a + k • birkhoffSum f c p x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Nat.add_comm (p * k) p, iterate_add_apply, ih,
      skew_iterate, hp.eq]
    simp [succ_nsmul, add_assoc]

/-- Every exact lifted return is a multiple of the base period times the holonomy order.
Order zero means that only time zero returns. No global invertibility is required. -/
theorem skew_return_iff (f : X → X) (c : X → A) (n : ℕ) (x : X) (a : A) :
    (skewStep f c)^[n] (x, a) = (x, a) ↔
      minimalPeriod f x * addOrderOf (birkhoffSum f c (minimalPeriod f x) x) ∣ n := by
  constructor
  · intro hr
    have hb : IsPeriodicPt f n x := by
      change f^[n] x = x
      have hfst := congrArg Prod.fst hr
      simpa only [skew_iterate] using hfst
    obtain ⟨k, hk⟩ := isPeriodicPt_iff_minimalPeriod_dvd.mp hb
    rw [hk, skew_iterate_block f c (isPeriodicPt_minimalPeriod f x)] at hr
    have hz : k • birkhoffSum f c (minimalPeriod f x) x = 0 := by
      have hsnd := congrArg Prod.snd hr
      exact (add_left_cancel (hsnd.trans (add_zero a).symm))
    obtain ⟨l, hl⟩ := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz
    refine ⟨l, ?_⟩
    rw [hk, hl, Nat.mul_assoc]
  · rintro ⟨k, rfl⟩
    rw [Nat.mul_assoc, skew_iterate_block f c (isPeriodicPt_minimalPeriod f x)]
    have hz := addOrderOf_dvd_iff_nsmul_eq_zero.mp
      (dvd_mul_right (addOrderOf (birkhoffSum f c (minimalPeriod f x) x)) k)
    simp only [hz, add_zero]

/-- Finite holonomy order multiplies the base period; infinite order gives period zero. -/
theorem skew_minimalPeriod (f : X → X) (c : X → A) (x : X) (a : A) :
    minimalPeriod (skewStep f c) (x, a) =
      minimalPeriod f x * addOrderOf (birkhoffSum f c (minimalPeriod f x) x) := by
  apply Nat.dvd_antisymm
  · apply IsPeriodicPt.minimalPeriod_dvd
    exact (skew_return_iff f c _ x a).mpr dvd_rfl
  · exact (skew_return_iff f c _ x a).mp (isPeriodicPt_minimalPeriod _ _).eq

#print axioms skew_iterate
#print axioms skew_iterate_block
#print axioms skew_return_iff
#print axioms skew_minimalPeriod

end D5.S1.Dynamics.PeriodicOrbits.SkewAdditiveReturn
