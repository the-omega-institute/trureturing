import Reg.Support.FibonacciL22Low
import Mathlib.Tactic.IntervalCases

namespace Reg.Support.FibonacciL22
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry
open Reg.Support.FibonacciQuadratic
open _root_.Set
open scoped Topology
noncomputable section

theorem competing_membership : b ∈ CompetingT ownership theta .G0 Q Q h W := by
  have bounds := t_bounds
  refine ⟨?_, ?_, ?_⟩
  · norm_num [InSupport, supportUpper, b, eval, phi]
    constructor <;> linarith [bounds.1,bounds.2]
  · intro r hr
    have hc := numeric_low false r (by simpa [W] using hr)
    apply (owned_color_interval ownership theta theta_bounds.1.le _ _).mpr
    exact ⟨hc.1, hc.2.1.le, hc.2.2.le,
      fun he => (ne_of_lt hc.2.1 he.symm).elim,
      fun he => (ne_of_lt hc.2.2 he).elim⟩
  · intro i r hr
    have hc := numeric_low i r hr
    apply (owned_color_interval ownership theta theta_bounds.1.le _ _).mpr
    exact ⟨hc.1, hc.2.1.le, hc.2.2.le,
      fun he => (ne_of_lt hc.2.1 he.symm).elim,
      fun he => (ne_of_lt hc.2.2 he).elim⟩

private theorem costs_le {a z : ℝ} {w : List Label} {cs : List Color}
    (hc : EndpointCertificate theta a z w cs) :
    ∀ x ∈ endpointCosts a z w cs, x ≤ theta := by
  intro x hx
  obtain ⟨r,rfl⟩ := List.mem_ofFn.mp hx
  exact max_le (hc r r.isLt).1.2 (hc r r.isLt).2.2

private theorem low_certificate (i : Bool) : EndpointCertificate theta b b Q (W i) := by
  intro r hr
  have hc := numeric_low i r hr
  have pair := (expanded_distance_formula theta theta_bounds.1.le (W i)[r] _).mp
    ⟨hc.1,hc.2.1.le,hc.2.2.le⟩
  exact ⟨pair,pair⟩

private theorem fold_le (xs : List ℝ) (hc : ∀ x ∈ xs, x ≤ theta) :
    xs.foldr max 0 ≤ theta := by
  induction xs with
  | nil => exact theta_bounds.1.le
  | cons x xs ih =>
    exact max_le (hc x (by simp)) (ih (fun z hz => hc z (by simp [hz])))

theorem budget_le : familyEndpointBudget P Q h U V W 22 ≤ theta := by
  unfold familyEndpointBudget
  apply fold_le
  rw [familyEndpointCosts, endpoints.1, endpoints.2.1, endpoints.2.2.1, endpoints.2.2.2]
  intro x hx
  simp only [List.mem_append] at hx
  rcases hx with ((((hx | hx) | hx) | hx) | hx) | hx
  · exact costs_le numeric_high_P x hx
  · exact costs_le (low_certificate false) x hx
  · exact costs_le numeric_high_P x hx
  · exact costs_le numeric_high_R x hx
  · exact costs_le (low_certificate false) x hx
  · exact costs_le (low_certificate true) x hx

theorem budget_eq : familyEndpointBudget P Q h U V W 22 = theta := by
  apply le_antisymm budget_le
  let x := max (max (cut h[17].val-compose (P.drop 17) lo)
    (max 0 (compose (P.drop 17) lo-cut (h[17].val+1))))
    (max (cut h[17].val-compose (P.drop 17) hi)
      (max 0 (compose (P.drop 17) hi-cut (h[17].val+1))))
  have hx : x ∈ familyEndpointCosts P Q h U V W 22 := by
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    rw [endpoints.1,endpoints.2.1]
    exact List.mem_ofFn.mpr ⟨⟨17,by decide⟩,rfl⟩
  have he : cut h[17].val-compose (P.drop 17) hi = theta := by
    simp only [hi,compose_eval]
    norm_num [h,P,composePair,step,shiftPair,eval,theta,cut,g,T2,lam]
    ring
  have hle : theta ≤ x := by
    rw [← he]
    exact (le_max_left _ _).trans (le_max_right _ _)
  exact List.le_max_of_le' 0 hx hle

theorem feasibility :
    if 0 < (-g)^22 then
      (CompetingT ownership theta .G0 Q (V false) h W).Nonempty ∧
      canonicalReturnLo V 22 ∈ closure (CompetingT ownership theta .G0 Q (V false) h W)
    else canonicalReturnLo V 22 ∈ CompetingT ownership theta .G0 Q (V false) h W := by
  rw [if_pos positive_slope, endpoints.2.2.1]
  exact ⟨⟨b,competing_membership⟩,subset_closure competing_membership⟩

#print axioms budget_eq
#print axioms feasibility
end
end Reg.Support.FibonacciL22
