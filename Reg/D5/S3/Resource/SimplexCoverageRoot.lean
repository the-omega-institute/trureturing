import D5.S3.Resource.SimplexCoverageRoot
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Module.ULift

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Resource.SimplexCoverageRoot

open _root_.D5.S3.Resource.SimplexCoveragePolynomial
open _root_.D5.S3.Resource.SimplexCoverageRoot
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

universe w u v

namespace Line

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
  realize signature (fun _ _ value => value) (fun impossible => nomatch impossible)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun impossible => nomatch impossible)

private abbrev arena : Arena where
  signature := signature
  Law observation := ∀ {Index : Type w} [Fintype Index]
    (polynomial : MvPolynomial Index ℚ) (x y : Index → ℝ) (time : ℝ),
    HasDerivAt (fun parameter => evaluateAt (fun index => x index + parameter * y index)
      polynomial)
      (observation.readout () () (∑ index, y index *
        evaluateAt (fun index => x index + time * y index) (MvPolynomial.pderiv index polynomial)))
      time

private theorem actualLaw : arena.{w}.Law actual := @evaluateAt_line_hasDerivAt

private theorem rejectedLaw : ¬ arena.{w}.Law rejected := by
  intro law
  have derivative := law (Index := ULift.{w} Unit) 0 (fun _ => 0) (fun _ => 0) 0
  have zero_derivative : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 1 0 := by
    simpa [rejected, realize, evaluateAt] using derivative
  have contradiction := zero_derivative.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  norm_num at contradiction

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

private def registration : Registration arena.{w} (arena.Law actual) where
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

register_information_theorem evaluateAt_line_hasDerivAt in arena
  readout via (realize signature (fun _ _ value => value)
    (fun impossible => nomatch impossible))
  realizes registration
  escape from source ({
    owner := `D5.S3.Resource.SimplexCoverageRoot
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateOperand := some #[] }] })
  escape continues (open)

#print axioms registration

end Line

namespace Root

private abbrev signature : Signature where
  Params := ℕ
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ degree value => value ^ (1 / (degree : ℝ)))
    (fun impossible => nomatch impossible)

private def rejected : Realization signature :=
  realize signature (fun _ _ value => value ^ 2) (fun impossible => nomatch impossible)

private abbrev arena : Arena where
  signature := signature
  Law observation := ∀ {Index : Type w} [Fintype Index] [DecidableEq Index]
    {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (columns : Index → V) (U : Submodule K V) [FiniteDimensional K (V ⧸ U)]
    (degree : ℕ) (_positive_degree : 1 ≤ degree),
    ConcaveOn ℝ {x : Index → ℝ | ∀ index, 0 ≤ x index}
      (fun x => observation.readout () degree (evaluateAt x (spanningPolynomial columns U degree)))

private theorem actualLaw : arena.{w,u,v}.Law actual := @spanningPolynomial_root_concaveOn

private theorem rejectedLaw : ¬ arena.{w,u,v}.Law rejected := by
  classical
  let basis : Module.Basis (Fin 0) (ULift.{u} ℚ) (ULift.{v} (Fin 0 → ℚ)) :=
    ((Pi.basisFun ℚ (Fin 0)).mapCoeffs ULift.ringEquiv.symm
      (by intro scalar vector; rfl)).map ULift.moduleEquiv.symm
  let : FiniteDimensional (ULift.{u} ℚ) (ULift.{v} (Fin 0 → ℚ)) :=
    Module.Finite.of_basis basis
  let columns : ULift.{w} Unit → ULift.{v} (Fin 0 → ℚ) := fun _ => 0
  have polynomial_identity : spanningPolynomial (K := ULift.{u} ℚ) columns ⊤ 1 =
      MvPolynomial.X (default : ULift.{w} Unit) := by
    apply MvPolynomial.ext
    intro alpha
    have singleton : Finsupp.single (default : ULift.{w} Unit) 1 = alpha ↔
        alpha default = 1 := by
      constructor
      · intro equality
        rw [← equality]
        simp
      · intro equality
        apply Finsupp.ext
        intro index
        have index_eq : index = default := Subsingleton.elim _ _
        subst index
        simpa using equality.symm
    rw [spanningPolynomial_coeff, MvPolynomial.coeff_X]
    simp only [singleton, representedSpan, top_sup_eq, Fintype.sum_unique, and_true]
    split_ifs with equality
    · simp [reciprocalFactorial, equality]
    · rfl
  intro law
  have concavity := law (K := ULift.{u} ℚ) (V := ULift.{v} (Fin 0 → ℚ))
    (Index := ULift.{w} Unit) columns ⊤ 1 (by norm_num)
  have jensen := concavity.2
  have contradiction := jensen (x := fun _ => 0) (y := fun _ => 2)
    (by intro index; norm_num) (by intro index; norm_num)
    (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  norm_num [rejected, realize, polynomial_identity, evaluateAt, Pi.smul_apply,
    Pi.add_apply, smul_eq_mul] at contradiction

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨1, 0, 1, ?_⟩
  norm_num [actual, realize]

private def registration : Registration arena.{w,u,v} (arena.Law actual) where
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

register_information_theorem spanningPolynomial_root_concaveOn in arena
  readout via (realize signature (fun _ degree value => value ^ (1 / (degree : ℝ)))
    (fun impossible => nomatch impossible))
  realizes registration
  escape from source ({
    owner := `D5.S3.Resource.SimplexCoverageRoot
    coordinates := #[11]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "arg", "body"]
      stateOperand := some #["fn", "arg"] }] })
  escape continues (open)

#print axioms registration

end Root

end Reg.D5.S3.Resource.SimplexCoverageRoot
