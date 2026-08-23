/- GID: D5/S3/ConceptDynamics/Factor/FactorInvariantObservables
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Factor/FactorInvariantObservables
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Factor dynamics are exactly the dynamics preserving every pulled-back observable. -/

import Mathlib.Logic.Function.Conjugate

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'factor_iff_observable_invariance' D5 Golden/Frozen/accepted`
     returned no matches.
   * The requested repository search for `Function.Semiconj`, semiconjugacy, composition
     equations, and factors found uses of generic factorization and semiconjugacy, but no
     theorem equating factor dynamics with invariance of every observable family.
   * Pinned Mathlib provides `Function.semiconj_iff_comp_eq` and
     `Function.Semiconj.comp_eq`; they identify the factor equation with semiconjugacy and
     are reused below. Searches around `Function.FactorsThrough` found only adjacent
     fiberwise factorization criteria, not the quantified observable-invariance statement. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

namespace D5.S3.ConceptDynamics.Factor.FactorInvariantObservables

/-- Pullback of a value-valued function along a state self-map. -/
def pullback {Y : Type u} {V : Type v} (tau : Y -> Y) (f : Y -> V) : Y -> V :=
  f ∘ tau

/-- Every observable through `phi` remains observable after pullback along `tau`.
The value type is quantified so that the identity observable on `Z` is available. -/
def ObservableInvariant {Y : Type u} {Z : Type v} (phi : Y -> Z) (tau : Y -> Y) : Prop :=
  forall (V : Type v) (g : Z -> V),
    Exists fun h : Z -> V => pullback tau (g ∘ phi) = h ∘ phi

/-- A factor dynamics transports pullback of every observable through the factor map. -/
theorem factor_pullback_formula
    {Y : Type u} {Z : Type v} {V : Type w}
    (phi : Y -> Z) (tau : Y -> Y) (sigma : Z -> Z)
    (factor : Function.Semiconj phi tau sigma) :
    forall g : Z -> V, pullback tau (g ∘ phi) = (g ∘ sigma) ∘ phi := by
  intro g
  funext y
  exact congrArg g (factor y)

/-- A factor dynamics exists exactly when pullback preserves all observable families. -/
theorem factor_iff_observable_invariance
    {Y : Type u} {Z : Type v} (phi : Y -> Z) (tau : Y -> Y) :
    (Exists fun sigma : Z -> Z => Function.Semiconj phi tau sigma) <->
      ObservableInvariant phi tau := by
  constructor
  · rintro ⟨sigma, factor⟩ V g
    exact ⟨g ∘ sigma, factor_pullback_formula phi tau sigma factor g⟩
  · intro invariant
    obtain ⟨sigma, factor⟩ := invariant Z id
    refine ⟨sigma, Function.semiconj_iff_comp_eq.mpr ?_⟩
    funext y
    exact congrFun factor y

/-- A surjective readout makes the induced factor dynamics unique. -/
theorem factor_unique_of_surjective
    {Y : Type u} {Z : Type v} (phi : Y -> Z) (tau : Y -> Y)
    (surjective : Function.Surjective phi) {sigma1 sigma2 : Z -> Z}
    (factor1 : Function.Semiconj phi tau sigma1)
    (factor2 : Function.Semiconj phi tau sigma2) :
    sigma1 = sigma2 := by
  funext z
  obtain ⟨y, rfl⟩ := surjective z
  exact (factor1 y).symm.trans (factor2 y)

example : ObservableInvariant (id : Bool -> Bool) Bool.not := by
  apply (factor_iff_observable_invariance (id : Bool -> Bool) Bool.not).mp
  exact ⟨Bool.not, Function.Semiconj.id_left⟩

#print axioms factor_iff_observable_invariance

end D5.S3.ConceptDynamics.Factor.FactorInvariantObservables
