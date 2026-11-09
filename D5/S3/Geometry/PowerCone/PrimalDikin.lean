/- GID: D5/S3/Geometry/PowerCone/PrimalDikin
   generality: I
   mirror-B: D5/B/S3/Geometry/PowerCone/PrimalDikin
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Formalized power-cone geometry and analytic support module. -/

import D5.S3.Analytic.ConvexBarrier.PrimalDikin
import D5.S3.Analytic.ConvexBarrier.HomogeneousHessian
import D5.S3.Geometry.PowerCone.Topology

/-!
The primal Dikin theorem applied to the *same* concrete scalar power cone
as the completed scalar mechanism. Every positive multiple of either
actual chord endpoint is excluded by the proved containment theorem.
No larger cone and no scalar optimality premise is used.

The final normalization interface supplies the exact `ScalarAlgebra`
`primalQuadratic` inputs. The Hessian coordinate identities are derived
from homogeneity in `HomogeneousHessian`; they are not premises.
There is deliberately no conclusion about `dualQuadratic`, rho >= 1,
two-sided normalized chords, `Curve`, or the scalar optimum.

Attribution: Zhang--Fu--Dai, arXiv:2611.06404v1, (2.2) and Lemma 3.2.
SOURCE ONLY. No Lean elaboration or kernel execution has been performed.
-/

open Set
open D5.S3.Analytic.ConvexBarrier

namespace D5.S3.Geometry.PowerCone

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Exact positive scaling law, including coordinate-zero faces. -/
theorem weight_posScale {c x y t : ℝ} (ht : 0 < t)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    weight c (t*x) (t*y) = t * weight c x y := by
  unfold weight
  rw [Real.mul_rpow ht.le hx, Real.mul_rpow ht.le hy]
  calc
    t^c*x^c*(t^(1-c)*y^(1-c)) =
        (t^c*t^(1-c))*(x^c*y^(1-c)) := by ring
    _ = t*(x^c*y^(1-c)) := by
      rw [← Real.rpow_add ht, show c+(1-c) = (1 : ℝ) by ring, Real.rpow_one]

/-- A positive multiple of a point on the full explicit boundary stays
on that full boundary. The coordinate-zero faces are not discarded. -/
theorem coneBoundary_posScale {c t : ℝ} (ht : 0 < t)
    {y : Point V} (hy : y ∈ coneBoundary c) : t • y ∈ coneBoundary c := by
  have hweight := weight_posScale (c := c) ht hy.1.1 hy.1.2.1
  constructor
  · change 0 ≤ t*y.1.1 ∧ 0 ≤ t*y.1.2 ∧
      ‖t • y.2‖ ≤ weight c (t*y.1.1) (t*y.1.2)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, hweight]
    exact ⟨mul_nonneg ht.le hy.1.1, mul_nonneg ht.le hy.1.2.1,
      mul_le_mul_of_nonneg_left hy.1.2.2 ht.le⟩
  · intro hi
    change 0 < t*y.1.1 ∧ 0 < t*y.1.2 ∧
      ‖t • y.2‖ < weight c (t*y.1.1) (t*y.1.2) at hi
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, hweight] at hi
    apply hy.2
    exact ⟨(mul_pos_iff_of_pos_left ht).mp hi.1,
      (mul_pos_iff_of_pos_left ht).mp hi.2.1,
      lt_of_mul_lt_mul_left hi.2.2 ht.le⟩

theorem coneInterior_frontier_subset {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    frontier (coneInterior c : Set (Point V)) ⊆ coneBoundary c := by
  rw [coneInterior_eq_interior hc hc1, coneBoundary_eq_frontier hc hc1]
  exact frontier_interior_subset

/-- Arbitrary displacement, strict radius, and the exact original cone.
The ambient V need not be finite dimensional for this primal result. -/
theorem primal_dikin_actual_powerCone {c ν : ℝ} {F : Point V → ℝ}
    (hF : IsLHSCB ν (interior (closedCone c)) (frontier (closedCone c)) F)
    {x : Point V} (hx : x ∈ interior (closedCone c)) (h : Point V)
    (hradius : diagonal 2 (interior (closedCone c)) F x h < 1) :
    x+h ∈ interior (closedCone c) :=
  hF.primal_dikin_interior hx h hradius

/-- Both actual primal chord exclusions, with no Dikin/exclusion premise.
`ScalarMechanism` consumes scalar chords; V=R is therefore fixed here.
The endpoint signs match Zhang--Fu--Dai Lemma 3.2 exactly. -/
theorem scalar_primal_chord_exclusions {c ν : ℝ}
    (hc : 0 < c) (hc1 : c < 1) {F : Point ℝ → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)
    {x h : Point ℝ} (hx : x ∈ coneInterior c) (δminus δplus : ℝ)
    (hminus : x-δminus • h ∈ coneBoundary c)
    (hplus : x+δplus • h ∈ coneBoundary c) :
    (∀ t : ℝ, 0 < t → 1 ≤ diagonal 2 (coneInterior c) F x
      (t • (x-δminus • h)-x)) ∧
    (∀ t : ℝ, 0 < t → 1 ≤ diagonal 2 (coneInterior c) F x
      (t • (x+δplus • h)-x)) :=
  hF.primal_chord_exclusions (coneInterior_frontier_subset hc.le hc1.le)
    hx δminus δplus
    (fun _ ht => (coneBoundary_posScale ht hminus).2)
    (fun _ ht => (coneBoundary_posScale ht hplus).2)

/-- Exact connection to the two primal `ScalarAlgebra` inputs. The
normalizations are Aminus=1+a*deltaMinus, Qminus=q*deltaMinus^2,
Aplus=1-a*deltaPlus, Qplus=q*deltaPlus^2. Here a and q are the actual
normalized derivatives. Their metric polynomial identities have been
derived from differentiated homogeneity, not assumed in this interface.

This theorem is not a dual supplier. In particular it cannot by itself
be used to infer nu>=2 or rho=nu-1>=1.
-/
theorem scalar_primalQuadratic_inputs {c ν δminus δplus : ℝ}
    (hc : 0 < c) (hc1 : c < 1) {F : Point ℝ → ℝ}
    (hF : IsLHSCB ν (coneInterior c) (coneBoundary c) F)
    {x h : Point ℝ} (hx : x ∈ coneInterior c)
    (hminus : x-δminus • h ∈ coneBoundary c)
    (hplus : x+δplus • h ∈ coneBoundary c) :
    let a := normalizedFirst ν F x h
    let q := projectiveHessian ν (coneInterior c) F x h
    (∀ t : ℝ, 0 < t →
      1 ≤ primalQuadratic ν (1+a*δminus) (q*δminus^2) t) ∧
    (∀ t : ℝ, 0 < t →
      1 ≤ primalQuadratic ν (1-a*δplus) (q*δplus^2) t) := by
  dsimp only
  obtain ⟨hm, hp⟩ := scalar_primal_chord_exclusions hc hc1 hF hx
    δminus δplus hminus hplus
  constructor
  · intro t ht
    have heq := hF.primal_chord_polynomial hx h (-δminus) t
    simp only [neg_smul, mul_neg, sub_neg_eq_add, neg_sq] at heq
    rw [← heq]
    exact hm t ht
  · intro t ht
    rw [← hF.primal_chord_polynomial hx h δplus t]
    exact hp t ht

end D5.S3.Geometry.PowerCone
