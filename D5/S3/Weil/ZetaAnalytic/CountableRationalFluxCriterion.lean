/- GID: D5/S3/Weil/ZetaAnalytic/CountableRationalFluxCriterion
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaAnalytic/CountableRationalFluxCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Rational rectangles detect every isolated zero in the open right half-plane. -/

import D5.S3.Weil.ZetaPntBase.Rectangle
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

/- Library-search audit trail (2026-08-31):
   * D5 searches for rational-rectangle flux criteria and zero-counting
     characterizations found the rectangle argument principle and analytic
     zero-isolation owners, but no countable rational criterion.
   * Body-shape searches found the canonical `Rectangle` and `RectangleBorder`
     primitives in `ZetaPntBase.Rectangle`; this module imports them and
     introduces no duplicate rectangle or flux definition.
   * Pinned Mathlib supplies `exists_rat_btwn`; searches for countable rational
     rectangle criteria and flux-zero characterizations found no exact theorem.
   * GitHub Lean-code searches for `rational rectangle`, for `RectangleBorder`
     with `exists_rat_btwn`, and for rectangle flux with analytic zero order all
     returned no results. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Complex Set

namespace D5.S3.Weil.ZetaAnalytic.CountableRationalFluxCriterion

/-- For an axis-isolated complex zero set, a flux that vanishes exactly on
zero-free rational rectangles detects whether the open right half-plane is
zero-free.  The boundary condition is public, as is the local flux-counting
law supplied by the argument principle. -/
theorem countable_rational_flux_criterion
    (zeros : Set Complex)
    (flux : Rat -> Rat -> Rat -> Rat -> Nat)
    (axisIsolated : forall z, z ∈ zeros -> 0 < z.re ->
      exists x0 x1 y0 y1 : Real,
        0 < x0 /\ x0 < z.re /\ z.re < x1 /\
        y0 < z.im /\ z.im < y1 /\
        forall w, w ∈ zeros ->
          w ∈ Rectangle (Complex.mk x0 y0) (Complex.mk x1 y1) -> w = z)
    (fluxZeroIff : forall (a b c d : Rat),
      0 < a -> a < b -> c < d ->
      (forall z, z ∈ RectangleBorder
        (Complex.mk (a : Real) (c : Real))
        (Complex.mk (b : Real) (d : Real)) -> z ∉ zeros) ->
      (flux a b c d = 0 <->
        forall z, z ∈ zeros -> z ∉ Rectangle
          (Complex.mk (a : Real) (c : Real))
          (Complex.mk (b : Real) (d : Real)))) :
    (forall z, z ∈ zeros -> ¬ (0 < z.re)) <->
      forall (a b c d : Rat),
        0 < a -> a < b -> c < d ->
        (forall z, z ∈ RectangleBorder
          (Complex.mk (a : Real) (c : Real))
          (Complex.mk (b : Real) (d : Real)) -> z ∉ zeros) ->
        flux a b c d = 0 := by
  constructor
  · intro noRightZero a b c d ha hab hcd boundaryFree
    apply (fluxZeroIff a b c d ha hab hcd boundaryFree).2
    intro z hz hrect
    have hcoords :=
      (mem_Rect (Rat.cast_le.2 hab.le) (Rat.cast_le.2 hcd.le) z).1 hrect
    exact noRightZero z hz ((Rat.cast_pos.2 ha).trans_le hcoords.1)
  · intro allFlux z hz hzRight
    obtain ⟨x0, x1, y0, y1, hx0, hx0z, hzx1, hy0z, hzy1, isolated⟩ :=
      axisIsolated z hz hzRight
    obtain ⟨a, hx0a, haz⟩ := exists_rat_btwn hx0z
    obtain ⟨b, hzb, hbx1⟩ := exists_rat_btwn hzx1
    obtain ⟨c, hy0c, hcz⟩ := exists_rat_btwn hy0z
    obtain ⟨d, hzd, hdy1⟩ := exists_rat_btwn hzy1
    have ha : 0 < a := Rat.cast_pos.1 (hx0.trans hx0a)
    have hab : a < b := Rat.cast_lt.1 (haz.trans hzb)
    have hcd : c < d := Rat.cast_lt.1 (hcz.trans hzd)
    have boundaryFree : forall w, w ∈ RectangleBorder
        (Complex.mk (a : Real) (c : Real))
        (Complex.mk (b : Real) (d : Real)) -> w ∉ zeros := by
      intro w hw hwz
      have hwinner := rectangleBorder_subset_rectangle _ _ hw
      have hwcoords :=
        (mem_Rect (Rat.cast_le.2 hab.le) (Rat.cast_le.2 hcd.le) w).1 hwinner
      have hwouter :
          w ∈ Rectangle (Complex.mk x0 y0) (Complex.mk x1 y1) := by
        apply (mem_Rect (hx0z.le.trans hzx1.le) (hy0z.le.trans hzy1.le) w).2
        exact ⟨hx0a.le.trans hwcoords.1,
          hwcoords.2.1.trans hbx1.le,
          hy0c.le.trans hwcoords.2.2.1,
          hwcoords.2.2.2.trans hdy1.le⟩
      have hwEq : w = z := isolated w hwz hwouter
      have zNotBoundary : z ∉ RectangleBorder
          (Complex.mk (a : Real) (c : Real))
          (Complex.mk (b : Real) (d : Real)) := by
        refine Set.disjoint_right.mp (rectangleBorder_disjoint_singleton ?_) rfl
        change z.re ≠ (a : Real) /\ z.re ≠ (b : Real) /\
          z.im ≠ (c : Real) /\ z.im ≠ (d : Real)
        exact ⟨ne_of_gt haz, ne_of_lt hzb, ne_of_gt hcz, ne_of_lt hzd⟩
      exact zNotBoundary (hwEq ▸ hw)
    have fluxZero := allFlux a b c d ha hab hcd boundaryFree
    have noZeroInside :=
      (fluxZeroIff a b c d ha hab hcd boundaryFree).1 fluxZero
    apply noZeroInside z hz
    apply (mem_Rect (Rat.cast_le.2 hab.le) (Rat.cast_le.2 hcd.le) z).2
    exact ⟨haz.le, hzb.le, hcz.le, hzd.le⟩

#print axioms countable_rational_flux_criterion

end D5.S3.Weil.ZetaAnalytic.CountableRationalFluxCriterion
