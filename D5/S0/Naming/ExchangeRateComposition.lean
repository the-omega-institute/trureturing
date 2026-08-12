/- GID: D5/S0/Naming/ExchangeRateComposition
   generality: G
   mirror-B: D5/B/S0/Naming/ExchangeRateComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exchange rates multiply when normal translations compose. -/

import Mathlib.Topology.Instances.Real.Lemmas

namespace D5.S0.Naming.ExchangeRateComposition

open Filter

/-- Suppose a translation sends the source high-resource filter to the intermediate one, the
intermediate height tends to infinity, and both component height ratios have limits. Then the
height ratio along the composite translation tends to the product of the component limits. -/
theorem exchange_rate_composition
    {A B C : Type*} {lA : Filter A} {lB : Filter B} {lC : Filter C}
    (tau1 : A -> B) (tau2 : B -> C)
    (h0 : A -> Real) (h1 : B -> Real) (h2 : C -> Real)
    (rho1 rho2 : Real)
    (tau1_normal : Tendsto tau1 lA lB)
    (_tau2_normal : Tendsto tau2 lB lC)
    (h1_high_resource : Tendsto h1 lB atTop)
    (rate1 : Tendsto (fun a => h0 a / h1 (tau1 a)) lA (nhds rho1))
    (rate2 : Tendsto (fun b => h1 b / h2 (tau2 b)) lB (nhds rho2)) :
    Tendsto (fun a => h0 a / h2 (tau2 (tau1 a))) lA (nhds (rho1 * rho2)) := by
  have second_rate_along_tau1 :
      Tendsto (fun a => h1 (tau1 a) / h2 (tau2 (tau1 a))) lA (nhds rho2) :=
    rate2.comp tau1_normal
  have product_rate := rate1.mul second_rate_along_tau1
  have h1_eventually_nonzero : Filter.Eventually (fun b => h1 b ≠ 0) lB :=
    (h1_high_resource.eventually_gt_atTop 0).mono fun _ hb => ne_of_gt hb
  apply product_rate.congr'
  filter_upwards [tau1_normal.eventually h1_eventually_nonzero] with a ha
  exact div_mul_div_cancel₀ ha

/-- The source, intermediate, and target name domains can all be inhabited. -/
example : Nonempty (Unit × Unit × Unit) := inferInstance

/-- Constant translations and positive growing height make all hypotheses simultaneously
satisfiable, with both component rates and the composite rate equal to one. -/
example :
    let tau1 : Nat -> Nat := fun n => n
    let tau2 : Nat -> Nat := fun n => n
    let height : Nat -> Real := fun n => n + 1
    Tendsto tau1 atTop atTop /\
      Tendsto tau2 atTop atTop /\
      Tendsto height atTop atTop /\
      Tendsto (fun n => height n / height (tau1 n)) atTop (nhds 1) /\
      Tendsto (fun n => height n / height (tau2 n)) atTop (nhds 1) := by
  dsimp
  refine ⟨tendsto_id, tendsto_id, ?_, ?_, ?_⟩
  · exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  · convert tendsto_const_nhds using 1
    funext n
    rw [div_self]
    positivity
  · convert tendsto_const_nhds using 1
    funext n
    rw [div_self]
    positivity

end D5.S0.Naming.ExchangeRateComposition
