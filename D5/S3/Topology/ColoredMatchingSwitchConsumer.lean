/- GID: D5/S3/Topology/ColoredMatchingSwitchConsumer
   generality: G
   mirror-B: D5/B/S3/Topology/ColoredMatchingSwitchConsumer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Logic.Relation]
   utility: none
   digest: Actual weaving crossing insertion changes mixed circles by at most one. -/

import D5.S3.Topology.ColoredMatchingSwitch
import D5.S3.Topology.WeavingMixedComponents

/-! Colored matching surgery at an actual crossing, with exact merging certified
by the actual spanning-component descent. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Topology.WeavingMixedComponents
noncomputable section
open D5.S3.Topology.WeavingDiagramPorts

private def matchingCircleEquiv (P : Parameters) (p : ℕ) (S : Finset (Crossing P)) :
    MixedCircle P p S ≃
      ColoredMatchingSwitch.Circle (externalPerm P) (mixedPerm P p S) :=
  Quotient.congr (Equiv.refl _) (fun x y =>
    (mixedReach_iff_matchingConnected P p S x y).trans
      (ColoredMatchingSwitch.reach_iff_matchingConnected
        (externalPerm P) (mixedPerm P p S) (external_involutive P)
        (mixedMate_involutive P p S) x y).symm)

/-- Actual crossing insertion has the universal circle-change bound. If its
two reference ends occupy distinct spanning components, the two actual mixed
circles merge exactly, by the previously constructed component-map descent.
The premise refers to that real graph quotient, not a supplied circle count. -/
theorem mixed_insert_circle_count (P : Parameters) (p : ℕ) (hp : p < 2)
    (S : Finset (Crossing P)) (z : Crossing P) (hz : z ∉ S) :
    |(Nat.card (MixedCircle P p (insert z S)) : ℤ) -
      (Nat.card (MixedCircle P p S) : ℤ)| ≤ 1 ∧
    (dartComponent P p hp S (z.1, z.2, .tl) ≠
      dartComponent P p hp S
        (z.1, z.2, if cup p z.2 then .bl else .tr) →
      (Nat.card (MixedCircle P p (insert z S)) : ℤ) =
        (Nat.card (MixedCircle P p S) : ℤ) - 1) := by
  classical
  rcases z with ⟨u, i⟩
  let a : Dart P := (u, i, .tl)
  let b : Dart P := (u, i, if cup p i then .tr else .bl)
  let c : Dart P := (u, i, if cup p i then .bl else .tr)
  let d : Dart P := (u, i, .br)
  have hcomp : cup (1 - p) i ↔ ¬ cup p i := by
    unfold cup
    have hmod := Nat.mod_lt i.val (by decide : 0 < 2)
    omega
  have hdist : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
    by_cases hc : cup p i <;> simp [a, b, c, d, hc]
  have htab : mixedPerm P p S a = b := by
    change mixedMate P p S a = b
    by_cases hc : cup p i <;> simp [mixedPerm, mixedMate, localMate, hz, a, b, hc]
  have htcd : mixedPerm P p S c = d := by
    change mixedMate P p S c = d
    by_cases hc : cup p i <;> simp [mixedPerm, mixedMate, localMate, hz, c, d, hc]
  have htPac : mixedPerm P p (insert (u, i) S) a = c := by
    change mixedMate P p (insert (u, i) S) a = c
    by_cases hc : cup p i <;>
      simp [mixedPerm, mixedMate, localMate, a, c, hcomp, hc]
  have htPbd : mixedPerm P p (insert (u, i) S) b = d := by
    change mixedMate P p (insert (u, i) S) b = d
    by_cases hc : cup p i <;>
      simp [mixedPerm, mixedMate, localMate, b, d, hcomp, hc]
  have hports (j : Port) :
      (u, i, j) = a ∨ (u, i, j) = b ∨ (u, i, j) = c ∨ (u, i, j) = d := by
    cases j <;> by_cases hc : cup p i <;> simp [a, b, c, d, hc]
  have houtside : ∀ x, x ≠ a → x ≠ b → x ≠ c → x ≠ d →
      mixedPerm P p (insert (u, i) S) x = mixedPerm P p S x := by
    rintro ⟨v, j, k⟩ hxa hxb hxc hxd
    have hpair : (v, j) ≠ (u, i) := by
      intro he
      have hx : (v, j, k) = (u, i, k) := by cases he; rfl
      rcases hports k with ha | hb | hc | hd
      · exact hxa (hx.trans ha)
      · exact hxb (hx.trans hb)
      · exact hxc (hx.trans hc)
      · exact hxd (hx.trans hd)
    change mixedMate P p (insert (u,i) S) (v,j,k) = mixedMate P p S (v,j,k)
    simp [mixedMate, hpair]
  have h := ColoredMatchingSwitch.colored_switch_circle_count
    (externalPerm P) (mixedPerm P p S) (mixedPerm P p (insert (u, i) S))
    (external_involutive P) (mixedMate_involutive P p S)
    (mixedMate_involutive P p (insert (u, i) S))
    (external_ne_self P) (mixedMate_ne_self P p S)
    (mixedMate_ne_self P p (insert (u, i) S)) a b c d
    hdist.1 hdist.2.1 hdist.2.2.1 hdist.2.2.2.1 hdist.2.2.2.2.1 hdist.2.2.2.2.2
    htab htcd htPac htPbd houtside
  have hold := Nat.card_congr (matchingCircleEquiv P p S)
  have hnew := Nat.card_congr (matchingCircleEquiv P p (insert (u, i) S))
  rw [← hold, ← hnew] at h
  refine ⟨h.1, ?_⟩
  intro href
  apply h.2
  intro hreach
  have hne := distinct_reference_components_force_distinct_mixed_circles
    P p hp S a c href
  apply hne
  apply Quotient.sound
  apply (mixedReach_iff_matchingConnected P p S a c).mpr
  exact (ColoredMatchingSwitch.reach_iff_matchingConnected
    (externalPerm P) (mixedPerm P p S) (external_involutive P)
    (mixedMate_involutive P p S) a c).mp hreach

#print axioms mixed_insert_circle_count

end
end D5.S3.Topology.WeavingMixedComponents
