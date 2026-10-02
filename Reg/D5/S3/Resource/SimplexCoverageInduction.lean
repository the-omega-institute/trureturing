import D5.S3.Resource.SimplexCoverageInduction
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Module.ULift

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Resource.SimplexCoverageInduction

open _root_.D5.S3.Resource.SimplexCoveragePolynomial
open _root_.D5.S3.Resource.SimplexCoverageInduction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped BigOperators

universe u v w

private abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ _ value => value ^ 2) (fun impossible => nomatch impossible)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun impossible => nomatch impossible)

private abbrev arena : Arena where
  signature := signature
  Law observation := ∀ {K : Type u} {V : Type v} {Index : Type w}
    [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Fintype Index] [DecidableEq Index]
    (columns : Index → V) (U : Submodule K V) (degree : ℕ) (x y : Index → ℝ)
    (_positive : ∀ index, 0 < x index),
    (degree : ℝ) * evaluateAt x (spanningPolynomial columns U degree) *
        (y ⬝ᵥ (spanningHessian columns U degree x *ᵥ y)) ≤
      ((degree : ℝ) - 1) * observation.readout () ()
        ((fun index => evaluateAt x (MvPolynomial.pderiv index
          (spanningPolynomial columns U degree))) ⬝ᵥ y)

private theorem actualLaw : arena.{u,v,w}.Law actual := @spanningPolynomial_reverse

private theorem rejectedLaw : ¬ arena.{u,v,w}.Law rejected := by
  let basis : Module.Basis (Fin 0) (ULift.{u} ℚ) (ULift.{v} (Fin 0 → ℚ)) :=
    ((Pi.basisFun ℚ (Fin 0)).mapCoeffs ULift.ringEquiv.symm
      (by intro scalar vector; rfl)).map ULift.moduleEquiv.symm
  let : FiniteDimensional (ULift.{u} ℚ) (ULift.{v} (Fin 0 → ℚ)) :=
    Module.Finite.of_basis basis
  intro law
  have contradiction := law (K := ULift.{u} ℚ) (V := ULift.{v} (Fin 0 → ℚ))
    (Index := ULift.{w} Unit) (fun _ => 0) ⊤ 0 (fun _ => 1) (fun _ => 0)
    (fun _ => zero_lt_one)
  norm_num [rejected, realize] at contradiction

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

private def registration : Registration arena.{u,v,w} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actualLaw, rejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejectedLaw⟩
      intro other different
      exact (different (Subsingleton.elim other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := dependence

register_information_theorem spanningPolynomial_reverse in arena
  readout via (realize signature (fun _ _ value => value ^ 2)
    (fun impossible => nomatch impossible))
  realizes registration
  escape from source ({
    owner := `D5.S3.Resource.SimplexCoverageInduction
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateOperand := some #["fn", "arg"] }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.Resource.SimplexCoverageInduction
