import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
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

noncomputable def registration_1.{u_1, u_2, u_3} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Resource.SimplexCoverageInduction.spanningPolynomial_reverse.{u_1, u_2, u_3}) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ value => value ^ 2)
    (fun impossible => nomatch impossible))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Resource") "SimplexCoverageInduction") "spanningPolynomial_reverse") "Reg.D5.S3.Resource.SimplexCoverageInduction/_private.Reg.D5.S3.Resource.SimplexCoverageInduction.0.Reg.D5.S3.Resource.SimplexCoverageInduction.arena/[anonymous]") "__information_unit"),
  realizationName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "_private") "Reg") "D5") "S3") "Resource") "SimplexCoverageInduction") 0) "Reg") "D5") "S3") "Resource") "SimplexCoverageInduction") "registration"),
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  objectArena := .source ⟨(arena.{u_1, u_2, u_3})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1, u_2, u_3}) ⟨(registration.{u_1, u_2, u_3})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ value => value ^ 2)
    (fun impossible => nomatch impossible)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Resource.SimplexCoverageInduction, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Resource.SimplexCoverageInduction, declaration := `D5.S3.Resource.SimplexCoverageInduction.spanningPolynomial_reverse, part := .type, path := [], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Resource.SimplexCoverageInduction, declaration := `Reg.D5.S3.Resource.SimplexCoverageInduction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Resource.SimplexCoverageInduction, declaration := `Reg.D5.S3.Resource.SimplexCoverageInduction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Resource.SimplexCoverageInduction, declaration := `Reg.D5.S3.Resource.SimplexCoverageInduction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] },
    { owner := `Reg.D5.S3.Resource.SimplexCoverageInduction, declaration := `Reg.D5.S3.Resource.SimplexCoverageInduction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2, .param `u_3] }], facts := [`Reg.D5.S3.Resource.SimplexCoverageInduction.registration_1.canonicalArenaFact, `Reg.D5.S3.Resource.SimplexCoverageInduction.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Resource.SimplexCoverageInduction.registration_1.sourceBridgeFact, `Reg.D5.S3.Resource.SimplexCoverageInduction.registration_1.observationFact0, `Reg.D5.S3.Resource.SimplexCoverageInduction.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Resource.SimplexCoverageInduction.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Resource.SimplexCoverageInduction.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Resource.SimplexCoverageInduction.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.Resource.SimplexCoverageInduction


noncomputable def Reg.D5.S3.Resource.SimplexCoverageInduction.registration_1.canonicalArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  _private.Reg.D5.S3.Resource.SimplexCoverageInduction.0.Reg.D5.S3.Resource.SimplexCoverageInduction.arena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Resource.SimplexCoverageInduction.registration_1.canonicalArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"SimplexCoverageInduction\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"SimplexCoverageInduction\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Resource.SimplexCoverageInduction, declaration := `Reg.D5.S3.Resource.SimplexCoverageInduction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Resource.SimplexCoverageInduction, declaration := `Reg.D5.S3.Resource.SimplexCoverageInduction.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence
noncomputable def Reg.D5.S3.Resource.SimplexCoverageInduction.registration_1.canonicalObjectArenaOperand.{u_1, u_2, u_3} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  _private.Reg.D5.S3.Resource.SimplexCoverageInduction.0.Reg.D5.S3.Resource.SimplexCoverageInduction.arena.{u_1, u_2, u_3}
noncomputable def Reg.D5.S3.Resource.SimplexCoverageInduction.registration_1.canonicalObjectArenaFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"SimplexCoverageInduction\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"SimplexCoverageInduction\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Resource.SimplexCoverageInduction, declaration := `Reg.D5.S3.Resource.SimplexCoverageInduction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Resource.SimplexCoverageInduction, declaration := `Reg.D5.S3.Resource.SimplexCoverageInduction.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  .evidence


noncomputable def Reg.D5.S3.Resource.SimplexCoverageInduction.registration_1.sourceLaw.{u_1, u_2, u_3} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (_private.Reg.D5.S3.Resource.SimplexCoverageInduction.0.Reg.D5.S3.Resource.SimplexCoverageInduction.arena.) (_private.Reg.D5.S3.Resource.SimplexCoverageInduction.0.Reg.D5.S3.Resource.SimplexCoverageInduction.registration.{u_1,
  u_2, u_3}).actual

noncomputable def Reg.D5.S3.Resource.SimplexCoverageInduction.registration_1.sourceBridgeFact.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Resource\",\"SimplexCoverageInduction\",\"spanningPolynomial_reverse\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"SimplexCoverageInduction\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Resource.SimplexCoverageInduction, declaration := `D5.S3.Resource.SimplexCoverageInduction.spanningPolynomial_reverse, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Resource.SimplexCoverageInduction, declaration := `Reg.D5.S3.Resource.SimplexCoverageInduction.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (_private.Reg.D5.S3.Resource.SimplexCoverageInduction.0.Reg.D5.S3.Resource.SimplexCoverageInduction.registration.{u_1,
  u_2, u_3}).bridge

noncomputable def Reg.D5.S3.Resource.SimplexCoverageInduction.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Resource.SimplexCoverageInduction.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Resource.SimplexCoverageInduction.registration_1.observation0.{u_1, u_2, u_3} : {K : Type u_1} →
  {V : Type u_2} →
    {Index : Type u_3} →
      [inst : Field.{u_1} K] →
        [inst_1 : AddCommGroup.{u_2} V] →
          [inst_2 :
              @Module.{u_1, u_2} K V
                (@DivisionSemiring.toSemiring.{u_1} K
                  (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1)] →
            [@FiniteDimensional.{u_1, u_2} K V (@Field.toDivisionRing.{u_1} K inst) inst_1 inst_2] →
              [Fintype.{u_3} Index] →
                [DecidableEq.{u_3 + 1} Index] →
                  (columns : Index → V) →
                    (U :
                        @Submodule.{u_1, u_2} K V
                          (@DivisionSemiring.toSemiring.{u_1} K
                            (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
                          (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2) →
                      (degree : Nat) →
                        (x y : Index → Real) →
                          (positive :
                              ∀ (index : Index),
                                @LT.lt.{0} Real Real.instLT
                                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                  (x index)) →
                            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                              _private.Reg.D5.S3.Resource.SimplexCoverageInduction.0.Reg.D5.S3.Resource.SimplexCoverageInduction.signature
                              PUnit.unit.{1} PUnit.unit.{1} :=
  fun {K : Type u_1} {V : Type u_2} {Index : Type u_3} [inst : Field.{u_1} K] [inst_1 : AddCommGroup.{u_2} V]
    [inst_2 :
      @Module.{u_1, u_2} K V
        (@DivisionSemiring.toSemiring.{u_1} K (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
        (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1)]
    [@FiniteDimensional.{u_1, u_2} K V (@Field.toDivisionRing.{u_1} K inst) inst_1 inst_2]
    [inst_4 : Fintype.{u_3} Index] [inst_5 : DecidableEq.{u_3 + 1} Index] (columns : Index → V)
    (U :
      @Submodule.{u_1, u_2} K V
        (@DivisionSemiring.toSemiring.{u_1} K (@Semifield.toDivisionSemiring.{u_1} K (@Field.toSemifield.{u_1} K inst)))
        (@AddCommGroup.toAddCommMonoid.{u_2} V inst_1) inst_2)
    (degree : Nat) (x y : Index → Real)
    (positive :
      ∀ (index : Index),
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (x index)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    _private.Reg.D5.S3.Resource.SimplexCoverageInduction.0.Reg.D5.S3.Resource.SimplexCoverageInduction.signature
    _private.Reg.D5.S3.Resource.SimplexCoverageInduction.0.Reg.D5.S3.Resource.SimplexCoverageInduction.actual
    PUnit.unit.{1} PUnit.unit.{1}
    (@dotProduct.{0, u_3} Index Real inst_4 Real.instMul Real.instAddCommMonoid
      (fun (index : Index) =>
        @D5.S3.Resource.SimplexCoveragePolynomial.evaluateAt.{u_3} Index x
          (@DFunLike.coe.{max (u_3 + 1) 1, max (u_3 + 1) 1, max (u_3 + 1) 1}
            (@Derivation.{0, u_3, u_3} Rat (@MvPolynomial.{u_3, 0} Index Rat Rat.commSemiring)
              (@MvPolynomial.{u_3, 0} Index Rat Rat.commSemiring) Rat.commSemiring
              (@AddMonoidAlgebra.commSemiring.{0, u_3} Rat
                (@Finsupp.{u_3, 0} Index Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) Rat.commSemiring
                (@Finsupp.instAddCommMonoid.{u_3, 0} Index Nat Nat.instAddCommMonoid))
              (@AddMonoidAlgebra.instAddCommMonoid.{0, u_3} Rat
                (@Finsupp.{u_3, 0} Index Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                (@CommSemiring.toSemiring.{0} Rat Rat.commSemiring))
              (@AddMonoidAlgebra.algebra.{0, 0, u_3} Rat Rat
                (@Finsupp.{u_3, 0} Index Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) Rat.commSemiring
                (@CommSemiring.toSemiring.{0} Rat Rat.commSemiring) (@Algebra.id.{0} Rat Rat.commSemiring)
                (@AddCommMonoid.toAddMonoid.{u_3}
                  (@Finsupp.{u_3, 0} Index Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                  (@Finsupp.instAddCommMonoid.{u_3, 0} Index Nat Nat.instAddCommMonoid)))
              (@Semiring.toModule.{u_3} (@MvPolynomial.{u_3, 0} Index Rat Rat.commSemiring)
                (@CommSemiring.toSemiring.{u_3} (@MvPolynomial.{u_3, 0} Index Rat Rat.commSemiring)
                  (@AddMonoidAlgebra.commSemiring.{0, u_3} Rat
                    (@Finsupp.{u_3, 0} Index Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) Rat.commSemiring
                    (@Finsupp.instAddCommMonoid.{u_3, 0} Index Nat Nat.instAddCommMonoid))))
              (@AddMonoidAlgebra.instModule.{0, 0, u_3} Rat Rat
                (@Finsupp.{u_3, 0} Index Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                (@CommSemiring.toSemiring.{0} Rat Rat.commSemiring) (@CommSemiring.toSemiring.{0} Rat Rat.commSemiring)
                (@Semiring.toModule.{0} Rat (@CommSemiring.toSemiring.{0} Rat Rat.commSemiring))))
            (@MvPolynomial.{u_3, 0} Index Rat Rat.commSemiring)
            (fun (x : @MvPolynomial.{u_3, 0} Index Rat Rat.commSemiring) =>
              @MvPolynomial.{u_3, 0} Index Rat Rat.commSemiring)
            (@Derivation.instFunLike.{0, u_3, u_3} Rat (@MvPolynomial.{u_3, 0} Index Rat Rat.commSemiring)
              (@MvPolynomial.{u_3, 0} Index Rat Rat.commSemiring) Rat.commSemiring
              (@AddMonoidAlgebra.commSemiring.{0, u_3} Rat
                (@Finsupp.{u_3, 0} Index Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) Rat.commSemiring
                (@Finsupp.instAddCommMonoid.{u_3, 0} Index Nat Nat.instAddCommMonoid))
              (@AddMonoidAlgebra.instAddCommMonoid.{0, u_3} Rat
                (@Finsupp.{u_3, 0} Index Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                (@CommSemiring.toSemiring.{0} Rat Rat.commSemiring))
              (@AddMonoidAlgebra.algebra.{0, 0, u_3} Rat Rat
                (@Finsupp.{u_3, 0} Index Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) Rat.commSemiring
                (@CommSemiring.toSemiring.{0} Rat Rat.commSemiring) (@Algebra.id.{0} Rat Rat.commSemiring)
                (@AddCommMonoid.toAddMonoid.{u_3}
                  (@Finsupp.{u_3, 0} Index Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                  (@Finsupp.instAddCommMonoid.{u_3, 0} Index Nat Nat.instAddCommMonoid)))
              (@Semiring.toModule.{u_3} (@MvPolynomial.{u_3, 0} Index Rat Rat.commSemiring)
                (@CommSemiring.toSemiring.{u_3} (@MvPolynomial.{u_3, 0} Index Rat Rat.commSemiring)
                  (@AddMonoidAlgebra.commSemiring.{0, u_3} Rat
                    (@Finsupp.{u_3, 0} Index Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)) Rat.commSemiring
                    (@Finsupp.instAddCommMonoid.{u_3, 0} Index Nat Nat.instAddCommMonoid))))
              (@AddMonoidAlgebra.instModule.{0, 0, u_3} Rat Rat
                (@Finsupp.{u_3, 0} Index Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass))
                (@CommSemiring.toSemiring.{0} Rat Rat.commSemiring) (@CommSemiring.toSemiring.{0} Rat Rat.commSemiring)
                (@Semiring.toModule.{0} Rat (@CommSemiring.toSemiring.{0} Rat Rat.commSemiring))))
            (@MvPolynomial.pderiv.{0, u_3} Rat Index Rat.commSemiring index)
            (@D5.S3.Resource.SimplexCoveragePolynomial.spanningPolynomial.{u_1, u_2, u_3} K V Index inst inst_1 inst_2
              inst_4 inst_5 columns U degree)))
      y)

noncomputable def Reg.D5.S3.Resource.SimplexCoverageInduction.registration_1.observationFact0.{u_1, u_2, u_3} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Resource\",\"SimplexCoverageInduction\",\"spanningPolynomial_reverse\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"SimplexCoverageInduction\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `D5.S3.Resource.SimplexCoverageInduction, declaration := `D5.S3.Resource.SimplexCoverageInduction.spanningPolynomial_reverse, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .body, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Resource.SimplexCoverageInduction, declaration := `Reg.D5.S3.Resource.SimplexCoverageInduction.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Resource.SimplexCoverageInduction.registration_1.varyingLawInput.{u_1, u_2, u_3} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Resource.SimplexCoverageInduction.registration_1.canonicalArenaOperand.{u_1, u_2, u_3})
noncomputable def Reg.D5.S3.Resource.SimplexCoverageInduction.registration_1.varyingLaw.{u_1, u_2, u_3}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"SimplexCoverageInduction\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"

noncomputable def Reg.D5.S3.Resource.SimplexCoverageInduction.registration_1.statementExclusion.{u_1, u_2, u_3} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"SimplexCoverageInduction\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Resource\",\"SimplexCoverageInduction\",\"spanningPolynomial_reverse\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Resource.SimplexCoverageInduction, declaration := `Reg.D5.S3.Resource.SimplexCoverageInduction.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  statementLocation := { owner := `D5.S3.Resource.SimplexCoverageInduction, declaration := `D5.S3.Resource.SimplexCoverageInduction.spanningPolynomial_reverse, part := .type, path := [], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (_private.Reg.D5.S3.Resource.SimplexCoverageInduction.0.Reg.D5.S3.Resource.SimplexCoverageInduction.registration.{u_1,
  u_2, u_3}).actual (_private.Reg.D5.S3.Resource.SimplexCoverageInduction.0.Reg.D5.S3.Resource.SimplexCoverageInduction.registration.{u_1,
  u_2, u_3}).variation.2.choose (_private.Reg.D5.S3.Resource.SimplexCoverageInduction.0.Reg.D5.S3.Resource.SimplexCoverageInduction.registration.{u_1,
  u_2, u_3}).variation.1 (_private.Reg.D5.S3.Resource.SimplexCoverageInduction.0.Reg.D5.S3.Resource.SimplexCoverageInduction.registration.{u_1,
  u_2, u_3}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Resource.SimplexCoverageInduction.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Resource\",\"SimplexCoverageInduction\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}")) (@(compiled_node% "{\"declaration\":[\"_private\",\"Reg\",\"D5\",\"S3\",\"Resource\",\"SimplexCoverageInduction\",0,\"Reg\",\"D5\",\"S3\",\"Resource\",\"SimplexCoverageInduction\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]],[\"param\",[\"u_2\"]],[\"param\",[\"u_3\"]]]}"))
  { owner := `Reg.D5.S3.Resource.SimplexCoverageInduction, declaration := `Reg.D5.S3.Resource.SimplexCoverageInduction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  { owner := `Reg.D5.S3.Resource.SimplexCoverageInduction, declaration := `_private.Reg.D5.S3.Resource.SimplexCoverageInduction.0.Reg.D5.S3.Resource.SimplexCoverageInduction.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1), (.param `u_2), (.param `u_3)] }
  (by first | rfl | (ext <;> rfl))
