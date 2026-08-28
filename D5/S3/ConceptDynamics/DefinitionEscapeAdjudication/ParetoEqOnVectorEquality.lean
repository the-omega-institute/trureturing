/- GID: D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ParetoEqOnVectorEquality
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeAdjudication/ParetoEqOnVectorEquality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Partial orders identify the symmetric Pareto kernel with vector equality. -/

import D5.S3.ConceptDynamics.DefinitionEscapeAdjudication.ParetoEqOnDecidableEquivalence

/- Library-search audit trail (2026-08-28):
   * `rg -n 'ParetoEqOn.*value.*=|sameVectorClass|GainVector.ext|le_antisymm'
     D5 --glob '*.lean'` found no theorem identifying the symmetric Pareto
     kernel with gain-vector equality.
   * The imported frozen `ParetoEqOn` and `ParetoWeak` definitions supply the
     two independent dominance directions.  The coordinate `PartialOrder`
     instances supply antisymmetry in each field; no new relation is defined.
   * No matching theorem was found in pinned Mathlib; generic extensionality
     is used only for the existing `GainVector` structure.
 -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.Adjudication

universe u

/- The symmetric weak-dominance kernel coincides with equality of all five
   coordinates when each coordinate order is antisymmetric. -/
theorem pareto_eq_on_iff_vector_eq
    {Action Information Residual Transfer Cost Risk : Type u}
    [DecidableEq Action]
    [PartialOrder Information] [PartialOrder Residual]
    [PartialOrder Transfer] [PartialOrder Cost] [PartialOrder Risk]
    (value : Action → GainVector Information Residual Transfer Cost Risk)
    (F : Finset Action) (x y : ParetoCarrier F) :
    ParetoEqOn value F x y ↔ value x.1 = value y.1 := by
  constructor
  · rintro ⟨hxy, hyx⟩
    cases hx : value x.1 with
    | mk xi xr xt xc xk =>
      cases hy : value y.1 with
      | mk yi yr yt yc yk =>
        simp only [ParetoWeakOn, ParetoWeak] at hxy hyx
        have hi : xi = yi := le_antisymm
          (by simpa [hx, hy] using hyx.1)
          (by simpa [hx, hy] using hxy.1)
        have hr : xr = yr := le_antisymm
          (by simpa [hx, hy] using hyx.2.1)
          (by simpa [hx, hy] using hxy.2.1)
        have ht : xt = yt := le_antisymm
          (by simpa [hx, hy] using hyx.2.2.1)
          (by simpa [hx, hy] using hxy.2.2.1)
        have hc : xc = yc := le_antisymm
          (by simpa [hx, hy] using hxy.2.2.2.1)
          (by simpa [hx, hy] using hyx.2.2.2.1)
        have hk : xk = yk := le_antisymm
          (by simpa [hx, hy] using hxy.2.2.2.2)
          (by simpa [hx, hy] using hyx.2.2.2.2)
        simp [hi, hr, ht, hc, hk]
  · intro h
    refine ⟨?_, ?_⟩
    · unfold ParetoWeakOn ParetoWeak
      rw [h]
      exact ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩
    · unfold ParetoWeakOn ParetoWeak
      rw [h]
      exact ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩

/- A concrete inhabited carrier and coordinate instance witness the theorem's
   hypotheses without making the general result depend on that instance. -/
example :
    let F : Finset Bool := {false, true}
    let value : Bool → GainVector Nat Nat Nat Nat Nat := fun action =>
      if action then
        { information := 1
          residualCapture := 1
          transfer := 1
          lifecycleCost := 0
          risk := 0 }
      else
        { information := 0
          residualCapture := 0
          transfer := 0
          lifecycleCost := 1
          risk := 1 }
    ∀ x y : ParetoCarrier F,
      ParetoEqOn value F x y ↔ value x.1 = value y.1 := by
  dsimp
  intro x y
  exact pareto_eq_on_iff_vector_eq _ _ _ _

example : ParetoCarrier ({false, true} : Finset Bool) :=
  ⟨false, by simp⟩

#print axioms pareto_eq_on_iff_vector_eq

end D5.S3.ConceptDynamics.DefinitionEscape.Adjudication
