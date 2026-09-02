/- GID: D5/S3/Weil/CofinalSupport/GoldenCofinalPositivity
   generality: I
   mirror-B: D5/B/S3/Weil/CofinalSupport/GoldenCofinalPositivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Cofinal golden support layers transfer positivity to every compact Weil test. -/

import D5.S3.Weil.TestFunctions
import D5.S3.Weil.ZetaCore.ExplicitFormulaBridge
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Order.Filter.AtTopBot.Tendsto

namespace D5.S3.Weil.CofinalSupport.GoldenCofinalPositivity

open Filter Set
open D5.S3.Weil.TestFunctions

/-- The source schedule `L n = L0 * phi^(2n)`. -/
noncomputable def goldenSupportRadius (initialRadius : Real) (n : Nat) : Real :=
  initialRadius * Real.goldenRatio ^ (2 * n)

/-- Weil tests whose support is contained in the symmetric radius window. -/
def supportLayer (radius : Real) : Set WeilTestFunction :=
  {f | Function.support (f : Real -> Complex) ⊆ Icc (-radius) radius}

/-- Positive initial radii make the source's golden schedule cofinal. -/
theorem goldenSupportRadius_tendsto {initialRadius : Real} (hInitial : 0 < initialRadius) :
    Tendsto (goldenSupportRadius initialRadius) atTop atTop := by
  change Tendsto (fun n : Nat => initialRadius * Real.goldenRatio ^ (2 * n)) atTop atTop
  have hDouble : Tendsto (fun n : Nat => 2 * n) atTop atTop := by
    refine tendsto_atTop.2 fun bound => ?_
    filter_upwards [eventually_ge_atTop bound] with n hn
    omega
  simpa only [Function.comp_apply] using
    Tendsto.const_mul_atTop hInitial
      ((tendsto_pow_atTop_atTop_of_one_lt Real.one_lt_goldenRatio).comp hDouble)

/-- Positivity on every level of a cofinal golden support schedule is positivity
on every compactly supported Weil test. -/
theorem golden_cofinal_positivity
    (initialRadius : Real) (Q : WeilTestFunction -> Real)
    (hCofinal : Tendsto (goldenSupportRadius initialRadius) atTop atTop)
    (hLayer : forall n f,
      f ∈ supportLayer (goldenSupportRadius initialRadius n) -> 0 <= Q f) :
    forall f : WeilTestFunction, 0 <= Q f := by
  intro f
  obtain ⟨radius, supportBound⟩ :=
    Zeta23.EF.exists_abs_le_of_hasCompactSupport f.hasCompactSupport
  obtain ⟨n, radiusLe⟩ := (hCofinal.eventually_ge_atTop radius).exists
  apply hLayer n f
  intro x hx
  exact abs_le.mp ((supportBound x hx).trans radiusLe)

example
    (initialRadius : Real) (Q : WeilTestFunction -> Real)
    (hCofinal : Tendsto (goldenSupportRadius initialRadius) atTop atTop)
    (hLayer : forall n f,
      f ∈ supportLayer (goldenSupportRadius initialRadius n) -> 0 <= Q f) :
    0 <= Q standardTestFunction :=
  golden_cofinal_positivity initialRadius Q hCofinal hLayer standardTestFunction

example :
    ¬ forall f : WeilTestFunction,
      0 <= (fun _ : WeilTestFunction => (-1 : Real)) f := by
  intro h
  have hFalse := h standardTestFunction
  norm_num at hFalse

example :
    Tendsto (goldenSupportRadius 1) atTop atTop ∧
      (forall n f,
        f ∈ supportLayer (goldenSupportRadius 1 n) ->
          0 <= (fun _ : WeilTestFunction => (0 : Real)) f) := by
  exact ⟨goldenSupportRadius_tendsto one_pos, by simp⟩

#print axioms golden_cofinal_positivity

end D5.S3.Weil.CofinalSupport.GoldenCofinalPositivity
