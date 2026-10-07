import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity

open Module LeanInformationAudit
open _root_.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity
open _root_.D5.S3.Observer.Hankel.HankelMinimalStateDimension
open _root_.D5.S3.Observer.Hankel.SequenceHankelRealization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := FiniteLinearRealization ℚ ℚ ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ r => r.stateDimension) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ N : ℕ,
    ∃ f g : FiniteLinearRealization ℚ ℚ ℚ,
      FiniteDimensional ℚ (tailSpace f.behavior) ∧
      FiniteDimensional ℚ (tailSpace g.behavior) ∧
      (∀ w : List Unit, w.length ≤ N → f.behavior w.length = g.behavior w.length) ∧
      f.behavior 0 1 = 1 ∧ g.behavior 0 1 = 1 ∧
      dataHankel f.behavior 1 1 ≠ 0 ∧ dataHankel g.behavior 1 1 ≠ 0 ∧
      R.readout () () f = 1 ∧ g.stateDimension = N + 3 ∧
      (∀ r : FiniteLinearRealization ℚ ℚ ℚ,
        r.behavior = f.behavior → f.stateDimension ≤ r.stateDimension) ∧
      (∀ r : FiniteLinearRealization ℚ ℚ ℚ,
        r.behavior = g.behavior → g.stateDimension ≤ r.stateDimension)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨f, g, hf, hg, hw, hf0, hg0, hbf, hbg, hdim, hrest⟩ := h 0
  change (0 : ℕ) = 1 at hdim
  cases hdim

def registration : Registration arena (∀ N : ℕ,
    ∃ f g : FiniteLinearRealization ℚ ℚ ℚ,
      FiniteDimensional ℚ (tailSpace f.behavior) ∧
      FiniteDimensional ℚ (tailSpace g.behavior) ∧
      (∀ w : List Unit, w.length ≤ N → f.behavior w.length = g.behavior w.length) ∧
      f.behavior 0 1 = 1 ∧ g.behavior 0 1 = 1 ∧
      dataHankel f.behavior 1 1 ≠ 0 ∧ dataHankel g.behavior 1 1 ≠ 0 ∧
      f.stateDimension = 1 ∧ g.stateDimension = N + 3 ∧
      (∀ r : FiniteLinearRealization ℚ ℚ ℚ,
        r.behavior = f.behavior → f.stateDimension ≤ r.stateDimension) ∧
      (∀ r : FiniteLinearRealization ℚ ℚ ℚ,
        r.behavior = g.behavior → g.stateDimension ≤ r.stateDimension)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finite_sample_rank_ambiguity, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (@Subsingleton.elim Unit _ j i))
    · intro i
      exact nomatch i
  dependence := by
    intro i
    obtain ⟨f, g, hf, hg, hw, hf0, hg0, hbf, hbg, hfd, hgd, hmin⟩ :=
      finite_sample_rank_ambiguity 0
    refine ⟨(), f, g, ?_⟩
    change f.stateDimension ≠ g.stateDimension
    omega

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.finite_sample_rank_ambiguity) (type_of% (realize.{0, 1, 0, 0, 0} signature (fun _ _ r => r.stateDimension) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Observer") "Hankel") "FiniteSampleRankAmbiguity") "finite_sample_rank_ambiguity") "Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity/Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 1, 0, 0, 0} signature (fun _ _ r => r.stateDimension) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity, definition := none, coordinates := #[], readouts := #[{ path := #["body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity, declaration := `D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.finite_sample_rank_ambiguity, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity, declaration := `Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity, declaration := `Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity, declaration := `Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity, declaration := `Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration_1.canonicalArenaFact, `Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration_1.sourceBridgeFact, `Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration_1.observationFact0, `Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration_1.anchorEnumeration }


#print axioms registration

end

end Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity


noncomputable def Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 1, 0, 0, 0} :=
  Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.arena
noncomputable def Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Hankel\",\"FiniteSampleRankAmbiguity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Hankel\",\"FiniteSampleRankAmbiguity\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity, declaration := `Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity, declaration := `Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 1, 0, 0, 0} :=
  Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.arena
noncomputable def Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Hankel\",\"FiniteSampleRankAmbiguity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Hankel\",\"FiniteSampleRankAmbiguity\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity, declaration := `Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity, declaration := `Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 1, 0, 0, 0}
  Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 1, 0, 0, 0}
    Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.arena
    (∀ (N : Nat),
      @Exists.{2}
        (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.{0} Rat Rat Rat Rat.instField
          Rat.addCommGroup
          (@Semiring.toModule.{0} Rat
            (@DivisionSemiring.toSemiring.{0} Rat
              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
          Rat.addCommGroup
          (@Semiring.toModule.{0} Rat
            (@DivisionSemiring.toSemiring.{0} Rat
              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
        fun
          (f :
            @D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.{0} Rat Rat Rat Rat.instField
              Rat.addCommGroup
              (@Semiring.toModule.{0} Rat
                (@DivisionSemiring.toSemiring.{0} Rat
                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
              Rat.addCommGroup
              (@Semiring.toModule.{0} Rat
                (@DivisionSemiring.toSemiring.{0} Rat
                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))) =>
        @Exists.{2}
          (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.{0} Rat Rat Rat Rat.instField
            Rat.addCommGroup
            (@Semiring.toModule.{0} Rat
              (@DivisionSemiring.toSemiring.{0} Rat
                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
            Rat.addCommGroup
            (@Semiring.toModule.{0} Rat
              (@DivisionSemiring.toSemiring.{0} Rat
                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
          fun
            (g :
              @D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.{0} Rat Rat Rat Rat.instField
                Rat.addCommGroup
                (@Semiring.toModule.{0} Rat
                  (@DivisionSemiring.toSemiring.{0} Rat
                    (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                Rat.addCommGroup
                (@Semiring.toModule.{0} Rat
                  (@DivisionSemiring.toSemiring.{0} Rat
                    (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))) =>
          And
            (@FiniteDimensional.{0, 0} Rat
              (@Subtype.{1} (Nat → Rat) fun (x : Nat → Rat) =>
                @Membership.mem.{0, 0} (Nat → Rat)
                  (@Submodule.{0, 0} Rat (Nat → Rat)
                    (@DivisionSemiring.toSemiring.{0} Rat
                      (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                    (@Pi.addCommMonoid.{0, 0} Nat (fun (a : Nat) => Rat) fun (i : Nat) =>
                      @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                    (@Pi.Function.module.{0, 0, 0} Nat Rat Rat
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                      (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                      (@Semiring.toModule.{0} Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))))
                  (@SetLike.instMembership.{0, 0}
                    (@Submodule.{0, 0} Rat (Nat → Rat)
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                      (@Pi.addCommMonoid.{0, 0} Nat (fun (a : Nat) => Rat) fun (i : Nat) =>
                        @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                      (@Pi.Function.module.{0, 0, 0} Nat Rat Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                        (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                        (@Semiring.toModule.{0} Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))))
                    (Nat → Rat)
                    (@Submodule.setLike.{0, 0} Rat (Nat → Rat)
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                      (@Pi.addCommMonoid.{0, 0} Nat (fun (a : Nat) => Rat) fun (i : Nat) =>
                        @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                      (@Pi.Function.module.{0, 0, 0} Nat Rat Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                        (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                        (@Semiring.toModule.{0} Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))))
                  (@D5.S3.Observer.Hankel.SequenceHankelRealization.tailSpace.{0} Rat Rat Rat Rat.instField
                    Rat.addCommGroup
                    (@Semiring.toModule.{0} Rat
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                    Rat.addCommGroup
                    (@Semiring.toModule.{0} Rat
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                    (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.behavior.{0} Rat Rat Rat
                      Rat.instField Rat.addCommGroup
                      (@Semiring.toModule.{0} Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                      Rat.addCommGroup
                      (@Semiring.toModule.{0} Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                      f))
                  x)
              Rat.instDivisionRing
              (@Submodule.addCommGroup.{0, 0} Rat (Nat → Rat) (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing)
                (@Pi.addCommGroup.{0, 0} Nat (fun (a : Nat) => Rat) fun (i : Nat) => Rat.addCommGroup)
                (@Pi.Function.module.{0, 0, 0} Nat Rat Rat
                  (@DivisionSemiring.toSemiring.{0} Rat
                    (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                  (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                  (@Semiring.toModule.{0} Rat
                    (@DivisionSemiring.toSemiring.{0} Rat
                      (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                (@D5.S3.Observer.Hankel.SequenceHankelRealization.tailSpace.{0} Rat Rat Rat Rat.instField
                  Rat.addCommGroup
                  (@Semiring.toModule.{0} Rat
                    (@DivisionSemiring.toSemiring.{0} Rat
                      (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                  Rat.addCommGroup
                  (@Semiring.toModule.{0} Rat
                    (@DivisionSemiring.toSemiring.{0} Rat
                      (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                  (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.behavior.{0} Rat Rat Rat
                    Rat.instField Rat.addCommGroup
                    (@Semiring.toModule.{0} Rat
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                    Rat.addCommGroup
                    (@Semiring.toModule.{0} Rat
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                    f)))
              (@Submodule.module.{0, 0} Rat (Nat → Rat)
                (@DivisionSemiring.toSemiring.{0} Rat
                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                (@Pi.addCommMonoid.{0, 0} Nat (fun (a : Nat) => Rat) fun (i : Nat) =>
                  @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                (@Pi.Function.module.{0, 0, 0} Nat Rat Rat
                  (@DivisionSemiring.toSemiring.{0} Rat
                    (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                  (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                  (@Semiring.toModule.{0} Rat
                    (@DivisionSemiring.toSemiring.{0} Rat
                      (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                (@D5.S3.Observer.Hankel.SequenceHankelRealization.tailSpace.{0} Rat Rat Rat Rat.instField
                  Rat.addCommGroup
                  (@Semiring.toModule.{0} Rat
                    (@DivisionSemiring.toSemiring.{0} Rat
                      (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                  Rat.addCommGroup
                  (@Semiring.toModule.{0} Rat
                    (@DivisionSemiring.toSemiring.{0} Rat
                      (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                  (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.behavior.{0} Rat Rat Rat
                    Rat.instField Rat.addCommGroup
                    (@Semiring.toModule.{0} Rat
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                    Rat.addCommGroup
                    (@Semiring.toModule.{0} Rat
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                    f))))
            (And
              (@FiniteDimensional.{0, 0} Rat
                (@Subtype.{1} (Nat → Rat) fun (x : Nat → Rat) =>
                  @Membership.mem.{0, 0} (Nat → Rat)
                    (@Submodule.{0, 0} Rat (Nat → Rat)
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                      (@Pi.addCommMonoid.{0, 0} Nat (fun (a : Nat) => Rat) fun (i : Nat) =>
                        @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                      (@Pi.Function.module.{0, 0, 0} Nat Rat Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                        (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                        (@Semiring.toModule.{0} Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))))
                    (@SetLike.instMembership.{0, 0}
                      (@Submodule.{0, 0} Rat (Nat → Rat)
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                        (@Pi.addCommMonoid.{0, 0} Nat (fun (a : Nat) => Rat) fun (i : Nat) =>
                          @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                        (@Pi.Function.module.{0, 0, 0} Nat Rat Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                          (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                          (@Semiring.toModule.{0} Rat
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))))
                      (Nat → Rat)
                      (@Submodule.setLike.{0, 0} Rat (Nat → Rat)
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                        (@Pi.addCommMonoid.{0, 0} Nat (fun (a : Nat) => Rat) fun (i : Nat) =>
                          @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                        (@Pi.Function.module.{0, 0, 0} Nat Rat Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                          (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                          (@Semiring.toModule.{0} Rat
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))))
                    (@D5.S3.Observer.Hankel.SequenceHankelRealization.tailSpace.{0} Rat Rat Rat Rat.instField
                      Rat.addCommGroup
                      (@Semiring.toModule.{0} Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                      Rat.addCommGroup
                      (@Semiring.toModule.{0} Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                      (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.behavior.{0} Rat Rat
                        Rat Rat.instField Rat.addCommGroup
                        (@Semiring.toModule.{0} Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                        Rat.addCommGroup
                        (@Semiring.toModule.{0} Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                        g))
                    x)
                Rat.instDivisionRing
                (@Submodule.addCommGroup.{0, 0} Rat (Nat → Rat) (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing)
                  (@Pi.addCommGroup.{0, 0} Nat (fun (a : Nat) => Rat) fun (i : Nat) => Rat.addCommGroup)
                  (@Pi.Function.module.{0, 0, 0} Nat Rat Rat
                    (@DivisionSemiring.toSemiring.{0} Rat
                      (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                    (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                    (@Semiring.toModule.{0} Rat
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                  (@D5.S3.Observer.Hankel.SequenceHankelRealization.tailSpace.{0} Rat Rat Rat Rat.instField
                    Rat.addCommGroup
                    (@Semiring.toModule.{0} Rat
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                    Rat.addCommGroup
                    (@Semiring.toModule.{0} Rat
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                    (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.behavior.{0} Rat Rat Rat
                      Rat.instField Rat.addCommGroup
                      (@Semiring.toModule.{0} Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                      Rat.addCommGroup
                      (@Semiring.toModule.{0} Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                      g)))
                (@Submodule.module.{0, 0} Rat (Nat → Rat)
                  (@DivisionSemiring.toSemiring.{0} Rat
                    (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                  (@Pi.addCommMonoid.{0, 0} Nat (fun (a : Nat) => Rat) fun (i : Nat) =>
                    @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                  (@Pi.Function.module.{0, 0, 0} Nat Rat Rat
                    (@DivisionSemiring.toSemiring.{0} Rat
                      (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                    (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                    (@Semiring.toModule.{0} Rat
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                  (@D5.S3.Observer.Hankel.SequenceHankelRealization.tailSpace.{0} Rat Rat Rat Rat.instField
                    Rat.addCommGroup
                    (@Semiring.toModule.{0} Rat
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                    Rat.addCommGroup
                    (@Semiring.toModule.{0} Rat
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                    (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.behavior.{0} Rat Rat Rat
                      Rat.instField Rat.addCommGroup
                      (@Semiring.toModule.{0} Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                      Rat.addCommGroup
                      (@Semiring.toModule.{0} Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                      g))))
              (And
                (∀ (w : List.{0} Unit),
                  @LE.le.{0} Nat instLENat (@List.length.{0} Unit w) N →
                    @Eq.{1}
                      (@LinearMap.{0, 0, 0, 0} Rat Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                        (@RingHom.id.{0} Rat
                          (@Semiring.toNonAssocSemiring.{0} Rat
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                        Rat Rat (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                        (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                        (@Semiring.toModule.{0} Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                        (@Semiring.toModule.{0} Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                      (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.behavior.{0} Rat Rat
                        Rat Rat.instField Rat.addCommGroup
                        (@Semiring.toModule.{0} Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                        Rat.addCommGroup
                        (@Semiring.toModule.{0} Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                        f (@List.length.{0} Unit w))
                      (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.behavior.{0} Rat Rat
                        Rat Rat.instField Rat.addCommGroup
                        (@Semiring.toModule.{0} Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                        Rat.addCommGroup
                        (@Semiring.toModule.{0} Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                        g (@List.length.{0} Unit w)))
                (And
                  (@Eq.{1} Rat
                    (@DFunLike.coe.{1, 1, 1}
                      (@LinearMap.{0, 0, 0, 0} Rat Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                        (@RingHom.id.{0} Rat
                          (@Semiring.toNonAssocSemiring.{0} Rat
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                        Rat Rat (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                        (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                        (@Semiring.toModule.{0} Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                        (@Semiring.toModule.{0} Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                      Rat (fun (x : Rat) => Rat)
                      (@LinearMap.instFunLike.{0, 0, 0, 0} Rat Rat Rat Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                        (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                        (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                        (@Semiring.toModule.{0} Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                        (@Semiring.toModule.{0} Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                        (@RingHom.id.{0} Rat
                          (@Semiring.toNonAssocSemiring.{0} Rat
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))))
                      (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.behavior.{0} Rat Rat
                        Rat Rat.instField Rat.addCommGroup
                        (@Semiring.toModule.{0} Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                        Rat.addCommGroup
                        (@Semiring.toModule.{0} Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                        f (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
                    (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
                  (And
                    (@Eq.{1} Rat
                      (@DFunLike.coe.{1, 1, 1}
                        (@LinearMap.{0, 0, 0, 0} Rat Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                          (@RingHom.id.{0} Rat
                            (@Semiring.toNonAssocSemiring.{0} Rat
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                          Rat Rat (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                          (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                          (@Semiring.toModule.{0} Rat
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                          (@Semiring.toModule.{0} Rat
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                        Rat (fun (x : Rat) => Rat)
                        (@LinearMap.instFunLike.{0, 0, 0, 0} Rat Rat Rat Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                          (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                          (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                          (@Semiring.toModule.{0} Rat
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                          (@Semiring.toModule.{0} Rat
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                          (@RingHom.id.{0} Rat
                            (@Semiring.toNonAssocSemiring.{0} Rat
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))))
                        (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.behavior.{0} Rat Rat
                          Rat Rat.instField Rat.addCommGroup
                          (@Semiring.toModule.{0} Rat
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                          Rat.addCommGroup
                          (@Semiring.toModule.{0} Rat
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                          g (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
                      (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
                    (And
                      (@Ne.{1}
                        (@LinearMap.{0, 0, 0, 0} Rat Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                          (@RingHom.id.{0} Rat
                            (@Semiring.toNonAssocSemiring.{0} Rat
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Rat)
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Rat)
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) => Rat)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                            @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) => Rat)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                            @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                          (@Pi.Function.module.{0, 0, 0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) Rat Rat
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                            (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                            (@Semiring.toModule.{0} Rat
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                          (@Pi.Function.module.{0, 0, 0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) Rat Rat
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                            (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                            (@Semiring.toModule.{0} Rat
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))))
                        (@D5.S3.Observer.Hankel.SequenceHankelRealization.dataHankel.{0} Rat Rat Rat Rat.instField
                          Rat.addCommGroup
                          (@Semiring.toModule.{0} Rat
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                          Rat.addCommGroup
                          (@Semiring.toModule.{0} Rat
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                          (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.behavior.{0} Rat
                            Rat Rat Rat.instField Rat.addCommGroup
                            (@Semiring.toModule.{0} Rat
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                            Rat.addCommGroup
                            (@Semiring.toModule.{0} Rat
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                            f)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (@OfNat.ofNat.{0}
                          (@LinearMap.{0, 0, 0, 0} Rat Rat
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                            (@RingHom.id.{0} Rat
                              (@Semiring.toNonAssocSemiring.{0} Rat
                                (@DivisionSemiring.toSemiring.{0} Rat
                                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Rat)
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Rat)
                            (@Pi.addCommMonoid.{0, 0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) => Rat)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                              @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                            (@Pi.addCommMonoid.{0, 0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) => Rat)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                              @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                            (@Pi.Function.module.{0, 0, 0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) Rat Rat
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                              (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                              (@Semiring.toModule.{0} Rat
                                (@DivisionSemiring.toSemiring.{0} Rat
                                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                            (@Pi.Function.module.{0, 0, 0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) Rat Rat
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                              (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                              (@Semiring.toModule.{0} Rat
                                (@DivisionSemiring.toSemiring.{0} Rat
                                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))))
                          (nat_lit 0)
                          (@Zero.toOfNat0.{0}
                            (@LinearMap.{0, 0, 0, 0} Rat Rat
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                              (@RingHom.id.{0} Rat
                                (@Semiring.toNonAssocSemiring.{0} Rat
                                  (@DivisionSemiring.toSemiring.{0} Rat
                                    (@Semifield.toDivisionSemiring.{0} Rat
                                      (@Field.toSemifield.{0} Rat Rat.instField)))))
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Rat)
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Rat)
                              (@Pi.addCommMonoid.{0, 0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) => Rat)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                                @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                              (@Pi.addCommMonoid.{0, 0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) => Rat)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                                @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                              (@Pi.Function.module.{0, 0, 0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) Rat Rat
                                (@DivisionSemiring.toSemiring.{0} Rat
                                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                                (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                                (@Semiring.toModule.{0} Rat
                                  (@DivisionSemiring.toSemiring.{0} Rat
                                    (@Semifield.toDivisionSemiring.{0} Rat
                                      (@Field.toSemifield.{0} Rat Rat.instField)))))
                              (@Pi.Function.module.{0, 0, 0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) Rat Rat
                                (@DivisionSemiring.toSemiring.{0} Rat
                                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                                (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                                (@Semiring.toModule.{0} Rat
                                  (@DivisionSemiring.toSemiring.{0} Rat
                                    (@Semifield.toDivisionSemiring.{0} Rat
                                      (@Field.toSemifield.{0} Rat Rat.instField))))))
                            (@LinearMap.instZero.{0, 0, 0, 0} Rat Rat
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Rat)
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Rat)
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                              (@Pi.addCommMonoid.{0, 0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) => Rat)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                                @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                              (@Pi.addCommMonoid.{0, 0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) => Rat)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                                @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                              (@Pi.Function.module.{0, 0, 0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) Rat Rat
                                (@DivisionSemiring.toSemiring.{0} Rat
                                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                                (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                                (@Semiring.toModule.{0} Rat
                                  (@DivisionSemiring.toSemiring.{0} Rat
                                    (@Semifield.toDivisionSemiring.{0} Rat
                                      (@Field.toSemifield.{0} Rat Rat.instField)))))
                              (@Pi.Function.module.{0, 0, 0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) Rat Rat
                                (@DivisionSemiring.toSemiring.{0} Rat
                                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                                (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                                (@Semiring.toModule.{0} Rat
                                  (@DivisionSemiring.toSemiring.{0} Rat
                                    (@Semifield.toDivisionSemiring.{0} Rat
                                      (@Field.toSemifield.{0} Rat Rat.instField)))))
                              (@RingHom.id.{0} Rat
                                (@Semiring.toNonAssocSemiring.{0} Rat
                                  (@DivisionSemiring.toSemiring.{0} Rat
                                    (@Semifield.toDivisionSemiring.{0} Rat
                                      (@Field.toSemifield.{0} Rat Rat.instField)))))))))
                      (And
                        (@Ne.{1}
                          (@LinearMap.{0, 0, 0, 0} Rat Rat
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                            (@RingHom.id.{0} Rat
                              (@Semiring.toNonAssocSemiring.{0} Rat
                                (@DivisionSemiring.toSemiring.{0} Rat
                                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Rat)
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Rat)
                            (@Pi.addCommMonoid.{0, 0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) => Rat)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                              @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                            (@Pi.addCommMonoid.{0, 0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) => Rat)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                              @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                            (@Pi.Function.module.{0, 0, 0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) Rat Rat
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                              (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                              (@Semiring.toModule.{0} Rat
                                (@DivisionSemiring.toSemiring.{0} Rat
                                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                            (@Pi.Function.module.{0, 0, 0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) Rat Rat
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                              (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                              (@Semiring.toModule.{0} Rat
                                (@DivisionSemiring.toSemiring.{0} Rat
                                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))))
                          (@D5.S3.Observer.Hankel.SequenceHankelRealization.dataHankel.{0} Rat Rat Rat Rat.instField
                            Rat.addCommGroup
                            (@Semiring.toModule.{0} Rat
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                            Rat.addCommGroup
                            (@Semiring.toModule.{0} Rat
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                            (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.behavior.{0} Rat
                              Rat Rat Rat.instField Rat.addCommGroup
                              (@Semiring.toModule.{0} Rat
                                (@DivisionSemiring.toSemiring.{0} Rat
                                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                              Rat.addCommGroup
                              (@Semiring.toModule.{0} Rat
                                (@DivisionSemiring.toSemiring.{0} Rat
                                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                              g)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (@OfNat.ofNat.{0}
                            (@LinearMap.{0, 0, 0, 0} Rat Rat
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                              (@RingHom.id.{0} Rat
                                (@Semiring.toNonAssocSemiring.{0} Rat
                                  (@DivisionSemiring.toSemiring.{0} Rat
                                    (@Semifield.toDivisionSemiring.{0} Rat
                                      (@Field.toSemifield.{0} Rat Rat.instField)))))
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Rat)
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Rat)
                              (@Pi.addCommMonoid.{0, 0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) => Rat)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                                @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                              (@Pi.addCommMonoid.{0, 0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) => Rat)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                                @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                              (@Pi.Function.module.{0, 0, 0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) Rat Rat
                                (@DivisionSemiring.toSemiring.{0} Rat
                                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                                (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                                (@Semiring.toModule.{0} Rat
                                  (@DivisionSemiring.toSemiring.{0} Rat
                                    (@Semifield.toDivisionSemiring.{0} Rat
                                      (@Field.toSemifield.{0} Rat Rat.instField)))))
                              (@Pi.Function.module.{0, 0, 0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) Rat Rat
                                (@DivisionSemiring.toSemiring.{0} Rat
                                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                                (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                                (@Semiring.toModule.{0} Rat
                                  (@DivisionSemiring.toSemiring.{0} Rat
                                    (@Semifield.toDivisionSemiring.{0} Rat
                                      (@Field.toSemifield.{0} Rat Rat.instField))))))
                            (nat_lit 0)
                            (@Zero.toOfNat0.{0}
                              (@LinearMap.{0, 0, 0, 0} Rat Rat
                                (@DivisionSemiring.toSemiring.{0} Rat
                                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                                (@DivisionSemiring.toSemiring.{0} Rat
                                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                                (@RingHom.id.{0} Rat
                                  (@Semiring.toNonAssocSemiring.{0} Rat
                                    (@DivisionSemiring.toSemiring.{0} Rat
                                      (@Semifield.toDivisionSemiring.{0} Rat
                                        (@Field.toSemifield.{0} Rat Rat.instField)))))
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Rat)
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Rat)
                                (@Pi.addCommMonoid.{0, 0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                  (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) => Rat)
                                  fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                                  @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                                (@Pi.addCommMonoid.{0, 0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                  (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) => Rat)
                                  fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                                  @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                                (@Pi.Function.module.{0, 0, 0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) Rat Rat
                                  (@DivisionSemiring.toSemiring.{0} Rat
                                    (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                                  (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                                  (@Semiring.toModule.{0} Rat
                                    (@DivisionSemiring.toSemiring.{0} Rat
                                      (@Semifield.toDivisionSemiring.{0} Rat
                                        (@Field.toSemifield.{0} Rat Rat.instField)))))
                                (@Pi.Function.module.{0, 0, 0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) Rat Rat
                                  (@DivisionSemiring.toSemiring.{0} Rat
                                    (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                                  (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                                  (@Semiring.toModule.{0} Rat
                                    (@DivisionSemiring.toSemiring.{0} Rat
                                      (@Semifield.toDivisionSemiring.{0} Rat
                                        (@Field.toSemifield.{0} Rat Rat.instField))))))
                              (@LinearMap.instZero.{0, 0, 0, 0} Rat Rat
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Rat)
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Rat)
                                (@DivisionSemiring.toSemiring.{0} Rat
                                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                                (@DivisionSemiring.toSemiring.{0} Rat
                                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                                (@Pi.addCommMonoid.{0, 0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                  (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) => Rat)
                                  fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                                  @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                                (@Pi.addCommMonoid.{0, 0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                  (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) => Rat)
                                  fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                                  @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                                (@Pi.Function.module.{0, 0, 0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) Rat Rat
                                  (@DivisionSemiring.toSemiring.{0} Rat
                                    (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                                  (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                                  (@Semiring.toModule.{0} Rat
                                    (@DivisionSemiring.toSemiring.{0} Rat
                                      (@Semifield.toDivisionSemiring.{0} Rat
                                        (@Field.toSemifield.{0} Rat Rat.instField)))))
                                (@Pi.Function.module.{0, 0, 0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) Rat Rat
                                  (@DivisionSemiring.toSemiring.{0} Rat
                                    (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                                  (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                                  (@Semiring.toModule.{0} Rat
                                    (@DivisionSemiring.toSemiring.{0} Rat
                                      (@Semifield.toDivisionSemiring.{0} Rat
                                        (@Field.toSemifield.{0} Rat Rat.instField)))))
                                (@RingHom.id.{0} Rat
                                  (@Semiring.toNonAssocSemiring.{0} Rat
                                    (@DivisionSemiring.toSemiring.{0} Rat
                                      (@Semifield.toDivisionSemiring.{0} Rat
                                        (@Field.toSemifield.{0} Rat Rat.instField)))))))))
                        (And
                          (@Eq.{1} Nat
                            (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.stateDimension.{0}
                              Rat Rat Rat Rat.instField Rat.addCommGroup
                              (@Semiring.toModule.{0} Rat
                                (@DivisionSemiring.toSemiring.{0} Rat
                                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                              Rat.addCommGroup
                              (@Semiring.toModule.{0} Rat
                                (@DivisionSemiring.toSemiring.{0} Rat
                                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                              f)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (And
                            (@Eq.{1} Nat
                              (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.stateDimension.{0}
                                Rat Rat Rat Rat.instField Rat.addCommGroup
                                (@Semiring.toModule.{0} Rat
                                  (@DivisionSemiring.toSemiring.{0} Rat
                                    (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                                Rat.addCommGroup
                                (@Semiring.toModule.{0} Rat
                                  (@DivisionSemiring.toSemiring.{0} Rat
                                    (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                                g)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                            (And
                              (∀
                                (r :
                                  @D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.{0} Rat Rat
                                    Rat Rat.instField Rat.addCommGroup
                                    (@Semiring.toModule.{0} Rat
                                      (@DivisionSemiring.toSemiring.{0} Rat
                                        (@Semifield.toDivisionSemiring.{0} Rat
                                          (@Field.toSemifield.{0} Rat Rat.instField))))
                                    Rat.addCommGroup
                                    (@Semiring.toModule.{0} Rat
                                      (@DivisionSemiring.toSemiring.{0} Rat
                                        (@Semifield.toDivisionSemiring.{0} Rat
                                          (@Field.toSemifield.{0} Rat Rat.instField))))),
                                @Eq.{1}
                                    (Nat →
                                      @LinearMap.{0, 0, 0, 0} Rat Rat
                                        (@DivisionSemiring.toSemiring.{0} Rat
                                          (@Semifield.toDivisionSemiring.{0} Rat
                                            (@Field.toSemifield.{0} Rat Rat.instField)))
                                        (@DivisionSemiring.toSemiring.{0} Rat
                                          (@Semifield.toDivisionSemiring.{0} Rat
                                            (@Field.toSemifield.{0} Rat Rat.instField)))
                                        (@RingHom.id.{0} Rat
                                          (@Semiring.toNonAssocSemiring.{0} Rat
                                            (@DivisionSemiring.toSemiring.{0} Rat
                                              (@Semifield.toDivisionSemiring.{0} Rat
                                                (@Field.toSemifield.{0} Rat Rat.instField)))))
                                        Rat Rat (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                                        (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                                        (@Semiring.toModule.{0} Rat
                                          (@DivisionSemiring.toSemiring.{0} Rat
                                            (@Semifield.toDivisionSemiring.{0} Rat
                                              (@Field.toSemifield.{0} Rat Rat.instField))))
                                        (@Semiring.toModule.{0} Rat
                                          (@DivisionSemiring.toSemiring.{0} Rat
                                            (@Semifield.toDivisionSemiring.{0} Rat
                                              (@Field.toSemifield.{0} Rat Rat.instField)))))
                                    (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.behavior.{0}
                                      Rat Rat Rat Rat.instField Rat.addCommGroup
                                      (@Semiring.toModule.{0} Rat
                                        (@DivisionSemiring.toSemiring.{0} Rat
                                          (@Semifield.toDivisionSemiring.{0} Rat
                                            (@Field.toSemifield.{0} Rat Rat.instField))))
                                      Rat.addCommGroup
                                      (@Semiring.toModule.{0} Rat
                                        (@DivisionSemiring.toSemiring.{0} Rat
                                          (@Semifield.toDivisionSemiring.{0} Rat
                                            (@Field.toSemifield.{0} Rat Rat.instField))))
                                      r)
                                    (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.behavior.{0}
                                      Rat Rat Rat Rat.instField Rat.addCommGroup
                                      (@Semiring.toModule.{0} Rat
                                        (@DivisionSemiring.toSemiring.{0} Rat
                                          (@Semifield.toDivisionSemiring.{0} Rat
                                            (@Field.toSemifield.{0} Rat Rat.instField))))
                                      Rat.addCommGroup
                                      (@Semiring.toModule.{0} Rat
                                        (@DivisionSemiring.toSemiring.{0} Rat
                                          (@Semifield.toDivisionSemiring.{0} Rat
                                            (@Field.toSemifield.{0} Rat Rat.instField))))
                                      f) →
                                  @LE.le.{0} Nat instLENat
                                    (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.stateDimension.{0}
                                      Rat Rat Rat Rat.instField Rat.addCommGroup
                                      (@Semiring.toModule.{0} Rat
                                        (@DivisionSemiring.toSemiring.{0} Rat
                                          (@Semifield.toDivisionSemiring.{0} Rat
                                            (@Field.toSemifield.{0} Rat Rat.instField))))
                                      Rat.addCommGroup
                                      (@Semiring.toModule.{0} Rat
                                        (@DivisionSemiring.toSemiring.{0} Rat
                                          (@Semifield.toDivisionSemiring.{0} Rat
                                            (@Field.toSemifield.{0} Rat Rat.instField))))
                                      f)
                                    (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.stateDimension.{0}
                                      Rat Rat Rat Rat.instField Rat.addCommGroup
                                      (@Semiring.toModule.{0} Rat
                                        (@DivisionSemiring.toSemiring.{0} Rat
                                          (@Semifield.toDivisionSemiring.{0} Rat
                                            (@Field.toSemifield.{0} Rat Rat.instField))))
                                      Rat.addCommGroup
                                      (@Semiring.toModule.{0} Rat
                                        (@DivisionSemiring.toSemiring.{0} Rat
                                          (@Semifield.toDivisionSemiring.{0} Rat
                                            (@Field.toSemifield.{0} Rat Rat.instField))))
                                      r))
                              (∀
                                (r :
                                  @D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.{0} Rat Rat
                                    Rat Rat.instField Rat.addCommGroup
                                    (@Semiring.toModule.{0} Rat
                                      (@DivisionSemiring.toSemiring.{0} Rat
                                        (@Semifield.toDivisionSemiring.{0} Rat
                                          (@Field.toSemifield.{0} Rat Rat.instField))))
                                    Rat.addCommGroup
                                    (@Semiring.toModule.{0} Rat
                                      (@DivisionSemiring.toSemiring.{0} Rat
                                        (@Semifield.toDivisionSemiring.{0} Rat
                                          (@Field.toSemifield.{0} Rat Rat.instField))))),
                                @Eq.{1}
                                    (Nat →
                                      @LinearMap.{0, 0, 0, 0} Rat Rat
                                        (@DivisionSemiring.toSemiring.{0} Rat
                                          (@Semifield.toDivisionSemiring.{0} Rat
                                            (@Field.toSemifield.{0} Rat Rat.instField)))
                                        (@DivisionSemiring.toSemiring.{0} Rat
                                          (@Semifield.toDivisionSemiring.{0} Rat
                                            (@Field.toSemifield.{0} Rat Rat.instField)))
                                        (@RingHom.id.{0} Rat
                                          (@Semiring.toNonAssocSemiring.{0} Rat
                                            (@DivisionSemiring.toSemiring.{0} Rat
                                              (@Semifield.toDivisionSemiring.{0} Rat
                                                (@Field.toSemifield.{0} Rat Rat.instField)))))
                                        Rat Rat (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                                        (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                                        (@Semiring.toModule.{0} Rat
                                          (@DivisionSemiring.toSemiring.{0} Rat
                                            (@Semifield.toDivisionSemiring.{0} Rat
                                              (@Field.toSemifield.{0} Rat Rat.instField))))
                                        (@Semiring.toModule.{0} Rat
                                          (@DivisionSemiring.toSemiring.{0} Rat
                                            (@Semifield.toDivisionSemiring.{0} Rat
                                              (@Field.toSemifield.{0} Rat Rat.instField)))))
                                    (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.behavior.{0}
                                      Rat Rat Rat Rat.instField Rat.addCommGroup
                                      (@Semiring.toModule.{0} Rat
                                        (@DivisionSemiring.toSemiring.{0} Rat
                                          (@Semifield.toDivisionSemiring.{0} Rat
                                            (@Field.toSemifield.{0} Rat Rat.instField))))
                                      Rat.addCommGroup
                                      (@Semiring.toModule.{0} Rat
                                        (@DivisionSemiring.toSemiring.{0} Rat
                                          (@Semifield.toDivisionSemiring.{0} Rat
                                            (@Field.toSemifield.{0} Rat Rat.instField))))
                                      r)
                                    (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.behavior.{0}
                                      Rat Rat Rat Rat.instField Rat.addCommGroup
                                      (@Semiring.toModule.{0} Rat
                                        (@DivisionSemiring.toSemiring.{0} Rat
                                          (@Semifield.toDivisionSemiring.{0} Rat
                                            (@Field.toSemifield.{0} Rat Rat.instField))))
                                      Rat.addCommGroup
                                      (@Semiring.toModule.{0} Rat
                                        (@DivisionSemiring.toSemiring.{0} Rat
                                          (@Semifield.toDivisionSemiring.{0} Rat
                                            (@Field.toSemifield.{0} Rat Rat.instField))))
                                      g) →
                                  @LE.le.{0} Nat instLENat
                                    (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.stateDimension.{0}
                                      Rat Rat Rat Rat.instField Rat.addCommGroup
                                      (@Semiring.toModule.{0} Rat
                                        (@DivisionSemiring.toSemiring.{0} Rat
                                          (@Semifield.toDivisionSemiring.{0} Rat
                                            (@Field.toSemifield.{0} Rat Rat.instField))))
                                      Rat.addCommGroup
                                      (@Semiring.toModule.{0} Rat
                                        (@DivisionSemiring.toSemiring.{0} Rat
                                          (@Semifield.toDivisionSemiring.{0} Rat
                                            (@Field.toSemifield.{0} Rat Rat.instField))))
                                      g)
                                    (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.stateDimension.{0}
                                      Rat Rat Rat Rat.instField Rat.addCommGroup
                                      (@Semiring.toModule.{0} Rat
                                        (@DivisionSemiring.toSemiring.{0} Rat
                                          (@Semifield.toDivisionSemiring.{0} Rat
                                            (@Field.toSemifield.{0} Rat Rat.instField))))
                                      Rat.addCommGroup
                                      (@Semiring.toModule.{0} Rat
                                        (@DivisionSemiring.toSemiring.{0} Rat
                                          (@Semifield.toDivisionSemiring.{0} Rat
                                            (@Field.toSemifield.{0} Rat Rat.instField))))
                                      r))))))))))))
    Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration)

noncomputable def Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Hankel\",\"FiniteSampleRankAmbiguity\",\"finite_sample_rank_ambiguity\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Hankel\",\"FiniteSampleRankAmbiguity\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity, declaration := `D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.finite_sample_rank_ambiguity, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity, declaration := `Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 1, 0, 0, 0}
  Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.arena
  (∀ (N : Nat),
    @Exists.{2}
      (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.{0} Rat Rat Rat Rat.instField
        Rat.addCommGroup
        (@Semiring.toModule.{0} Rat
          (@DivisionSemiring.toSemiring.{0} Rat
            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
        Rat.addCommGroup
        (@Semiring.toModule.{0} Rat
          (@DivisionSemiring.toSemiring.{0} Rat
            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
      fun
        (f :
          @D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.{0} Rat Rat Rat Rat.instField
            Rat.addCommGroup
            (@Semiring.toModule.{0} Rat
              (@DivisionSemiring.toSemiring.{0} Rat
                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
            Rat.addCommGroup
            (@Semiring.toModule.{0} Rat
              (@DivisionSemiring.toSemiring.{0} Rat
                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))) =>
      @Exists.{2}
        (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.{0} Rat Rat Rat Rat.instField
          Rat.addCommGroup
          (@Semiring.toModule.{0} Rat
            (@DivisionSemiring.toSemiring.{0} Rat
              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
          Rat.addCommGroup
          (@Semiring.toModule.{0} Rat
            (@DivisionSemiring.toSemiring.{0} Rat
              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
        fun
          (g :
            @D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.{0} Rat Rat Rat Rat.instField
              Rat.addCommGroup
              (@Semiring.toModule.{0} Rat
                (@DivisionSemiring.toSemiring.{0} Rat
                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
              Rat.addCommGroup
              (@Semiring.toModule.{0} Rat
                (@DivisionSemiring.toSemiring.{0} Rat
                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))) =>
        And
          (@FiniteDimensional.{0, 0} Rat
            (@Subtype.{1} (Nat → Rat) fun (x : Nat → Rat) =>
              @Membership.mem.{0, 0} (Nat → Rat)
                (@Submodule.{0, 0} Rat (Nat → Rat)
                  (@DivisionSemiring.toSemiring.{0} Rat
                    (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                  (@Pi.addCommMonoid.{0, 0} Nat (fun (a : Nat) => Rat) fun (i : Nat) =>
                    @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                  (@Pi.Function.module.{0, 0, 0} Nat Rat Rat
                    (@DivisionSemiring.toSemiring.{0} Rat
                      (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                    (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                    (@Semiring.toModule.{0} Rat
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))))
                (@SetLike.instMembership.{0, 0}
                  (@Submodule.{0, 0} Rat (Nat → Rat)
                    (@DivisionSemiring.toSemiring.{0} Rat
                      (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                    (@Pi.addCommMonoid.{0, 0} Nat (fun (a : Nat) => Rat) fun (i : Nat) =>
                      @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                    (@Pi.Function.module.{0, 0, 0} Nat Rat Rat
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                      (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                      (@Semiring.toModule.{0} Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))))
                  (Nat → Rat)
                  (@Submodule.setLike.{0, 0} Rat (Nat → Rat)
                    (@DivisionSemiring.toSemiring.{0} Rat
                      (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                    (@Pi.addCommMonoid.{0, 0} Nat (fun (a : Nat) => Rat) fun (i : Nat) =>
                      @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                    (@Pi.Function.module.{0, 0, 0} Nat Rat Rat
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                      (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                      (@Semiring.toModule.{0} Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))))
                (@D5.S3.Observer.Hankel.SequenceHankelRealization.tailSpace.{0} Rat Rat Rat Rat.instField
                  Rat.addCommGroup
                  (@Semiring.toModule.{0} Rat
                    (@DivisionSemiring.toSemiring.{0} Rat
                      (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                  Rat.addCommGroup
                  (@Semiring.toModule.{0} Rat
                    (@DivisionSemiring.toSemiring.{0} Rat
                      (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                  (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.behavior.{0} Rat Rat Rat
                    Rat.instField Rat.addCommGroup
                    (@Semiring.toModule.{0} Rat
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                    Rat.addCommGroup
                    (@Semiring.toModule.{0} Rat
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                    f))
                x)
            Rat.instDivisionRing
            (@Submodule.addCommGroup.{0, 0} Rat (Nat → Rat) (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing)
              (@Pi.addCommGroup.{0, 0} Nat (fun (a : Nat) => Rat) fun (i : Nat) => Rat.addCommGroup)
              (@Pi.Function.module.{0, 0, 0} Nat Rat Rat
                (@DivisionSemiring.toSemiring.{0} Rat
                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                (@Semiring.toModule.{0} Rat
                  (@DivisionSemiring.toSemiring.{0} Rat
                    (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
              (@D5.S3.Observer.Hankel.SequenceHankelRealization.tailSpace.{0} Rat Rat Rat Rat.instField Rat.addCommGroup
                (@Semiring.toModule.{0} Rat
                  (@DivisionSemiring.toSemiring.{0} Rat
                    (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                Rat.addCommGroup
                (@Semiring.toModule.{0} Rat
                  (@DivisionSemiring.toSemiring.{0} Rat
                    (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.behavior.{0} Rat Rat Rat
                  Rat.instField Rat.addCommGroup
                  (@Semiring.toModule.{0} Rat
                    (@DivisionSemiring.toSemiring.{0} Rat
                      (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                  Rat.addCommGroup
                  (@Semiring.toModule.{0} Rat
                    (@DivisionSemiring.toSemiring.{0} Rat
                      (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                  f)))
            (@Submodule.module.{0, 0} Rat (Nat → Rat)
              (@DivisionSemiring.toSemiring.{0} Rat
                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
              (@Pi.addCommMonoid.{0, 0} Nat (fun (a : Nat) => Rat) fun (i : Nat) =>
                @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
              (@Pi.Function.module.{0, 0, 0} Nat Rat Rat
                (@DivisionSemiring.toSemiring.{0} Rat
                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                (@Semiring.toModule.{0} Rat
                  (@DivisionSemiring.toSemiring.{0} Rat
                    (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
              (@D5.S3.Observer.Hankel.SequenceHankelRealization.tailSpace.{0} Rat Rat Rat Rat.instField Rat.addCommGroup
                (@Semiring.toModule.{0} Rat
                  (@DivisionSemiring.toSemiring.{0} Rat
                    (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                Rat.addCommGroup
                (@Semiring.toModule.{0} Rat
                  (@DivisionSemiring.toSemiring.{0} Rat
                    (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.behavior.{0} Rat Rat Rat
                  Rat.instField Rat.addCommGroup
                  (@Semiring.toModule.{0} Rat
                    (@DivisionSemiring.toSemiring.{0} Rat
                      (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                  Rat.addCommGroup
                  (@Semiring.toModule.{0} Rat
                    (@DivisionSemiring.toSemiring.{0} Rat
                      (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                  f))))
          (And
            (@FiniteDimensional.{0, 0} Rat
              (@Subtype.{1} (Nat → Rat) fun (x : Nat → Rat) =>
                @Membership.mem.{0, 0} (Nat → Rat)
                  (@Submodule.{0, 0} Rat (Nat → Rat)
                    (@DivisionSemiring.toSemiring.{0} Rat
                      (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                    (@Pi.addCommMonoid.{0, 0} Nat (fun (a : Nat) => Rat) fun (i : Nat) =>
                      @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                    (@Pi.Function.module.{0, 0, 0} Nat Rat Rat
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                      (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                      (@Semiring.toModule.{0} Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))))
                  (@SetLike.instMembership.{0, 0}
                    (@Submodule.{0, 0} Rat (Nat → Rat)
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                      (@Pi.addCommMonoid.{0, 0} Nat (fun (a : Nat) => Rat) fun (i : Nat) =>
                        @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                      (@Pi.Function.module.{0, 0, 0} Nat Rat Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                        (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                        (@Semiring.toModule.{0} Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))))
                    (Nat → Rat)
                    (@Submodule.setLike.{0, 0} Rat (Nat → Rat)
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                      (@Pi.addCommMonoid.{0, 0} Nat (fun (a : Nat) => Rat) fun (i : Nat) =>
                        @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                      (@Pi.Function.module.{0, 0, 0} Nat Rat Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                        (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                        (@Semiring.toModule.{0} Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))))
                  (@D5.S3.Observer.Hankel.SequenceHankelRealization.tailSpace.{0} Rat Rat Rat Rat.instField
                    Rat.addCommGroup
                    (@Semiring.toModule.{0} Rat
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                    Rat.addCommGroup
                    (@Semiring.toModule.{0} Rat
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                    (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.behavior.{0} Rat Rat Rat
                      Rat.instField Rat.addCommGroup
                      (@Semiring.toModule.{0} Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                      Rat.addCommGroup
                      (@Semiring.toModule.{0} Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                      g))
                  x)
              Rat.instDivisionRing
              (@Submodule.addCommGroup.{0, 0} Rat (Nat → Rat) (@DivisionRing.toRing.{0} Rat Rat.instDivisionRing)
                (@Pi.addCommGroup.{0, 0} Nat (fun (a : Nat) => Rat) fun (i : Nat) => Rat.addCommGroup)
                (@Pi.Function.module.{0, 0, 0} Nat Rat Rat
                  (@DivisionSemiring.toSemiring.{0} Rat
                    (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                  (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                  (@Semiring.toModule.{0} Rat
                    (@DivisionSemiring.toSemiring.{0} Rat
                      (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                (@D5.S3.Observer.Hankel.SequenceHankelRealization.tailSpace.{0} Rat Rat Rat Rat.instField
                  Rat.addCommGroup
                  (@Semiring.toModule.{0} Rat
                    (@DivisionSemiring.toSemiring.{0} Rat
                      (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                  Rat.addCommGroup
                  (@Semiring.toModule.{0} Rat
                    (@DivisionSemiring.toSemiring.{0} Rat
                      (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                  (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.behavior.{0} Rat Rat Rat
                    Rat.instField Rat.addCommGroup
                    (@Semiring.toModule.{0} Rat
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                    Rat.addCommGroup
                    (@Semiring.toModule.{0} Rat
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                    g)))
              (@Submodule.module.{0, 0} Rat (Nat → Rat)
                (@DivisionSemiring.toSemiring.{0} Rat
                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                (@Pi.addCommMonoid.{0, 0} Nat (fun (a : Nat) => Rat) fun (i : Nat) =>
                  @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                (@Pi.Function.module.{0, 0, 0} Nat Rat Rat
                  (@DivisionSemiring.toSemiring.{0} Rat
                    (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                  (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                  (@Semiring.toModule.{0} Rat
                    (@DivisionSemiring.toSemiring.{0} Rat
                      (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                (@D5.S3.Observer.Hankel.SequenceHankelRealization.tailSpace.{0} Rat Rat Rat Rat.instField
                  Rat.addCommGroup
                  (@Semiring.toModule.{0} Rat
                    (@DivisionSemiring.toSemiring.{0} Rat
                      (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                  Rat.addCommGroup
                  (@Semiring.toModule.{0} Rat
                    (@DivisionSemiring.toSemiring.{0} Rat
                      (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                  (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.behavior.{0} Rat Rat Rat
                    Rat.instField Rat.addCommGroup
                    (@Semiring.toModule.{0} Rat
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                    Rat.addCommGroup
                    (@Semiring.toModule.{0} Rat
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                    g))))
            (And
              (∀ (w : List.{0} Unit),
                @LE.le.{0} Nat instLENat (@List.length.{0} Unit w) N →
                  @Eq.{1}
                    (@LinearMap.{0, 0, 0, 0} Rat Rat
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                      (@RingHom.id.{0} Rat
                        (@Semiring.toNonAssocSemiring.{0} Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                      Rat Rat (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                      (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                      (@Semiring.toModule.{0} Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                      (@Semiring.toModule.{0} Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                    (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.behavior.{0} Rat Rat Rat
                      Rat.instField Rat.addCommGroup
                      (@Semiring.toModule.{0} Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                      Rat.addCommGroup
                      (@Semiring.toModule.{0} Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                      f (@List.length.{0} Unit w))
                    (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.behavior.{0} Rat Rat Rat
                      Rat.instField Rat.addCommGroup
                      (@Semiring.toModule.{0} Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                      Rat.addCommGroup
                      (@Semiring.toModule.{0} Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                      g (@List.length.{0} Unit w)))
              (And
                (@Eq.{1} Rat
                  (@DFunLike.coe.{1, 1, 1}
                    (@LinearMap.{0, 0, 0, 0} Rat Rat
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                      (@RingHom.id.{0} Rat
                        (@Semiring.toNonAssocSemiring.{0} Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                      Rat Rat (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                      (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                      (@Semiring.toModule.{0} Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                      (@Semiring.toModule.{0} Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                    Rat (fun (x : Rat) => Rat)
                    (@LinearMap.instFunLike.{0, 0, 0, 0} Rat Rat Rat Rat
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                      (@DivisionSemiring.toSemiring.{0} Rat
                        (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                      (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                      (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                      (@Semiring.toModule.{0} Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                      (@Semiring.toModule.{0} Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                      (@RingHom.id.{0} Rat
                        (@Semiring.toNonAssocSemiring.{0} Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))))
                    (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.behavior.{0} Rat Rat Rat
                      Rat.instField Rat.addCommGroup
                      (@Semiring.toModule.{0} Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                      Rat.addCommGroup
                      (@Semiring.toModule.{0} Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                      f (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
                  (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
                (And
                  (@Eq.{1} Rat
                    (@DFunLike.coe.{1, 1, 1}
                      (@LinearMap.{0, 0, 0, 0} Rat Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                        (@RingHom.id.{0} Rat
                          (@Semiring.toNonAssocSemiring.{0} Rat
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                        Rat Rat (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                        (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                        (@Semiring.toModule.{0} Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                        (@Semiring.toModule.{0} Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                      Rat (fun (x : Rat) => Rat)
                      (@LinearMap.instFunLike.{0, 0, 0, 0} Rat Rat Rat Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                        (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                        (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                        (@Semiring.toModule.{0} Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                        (@Semiring.toModule.{0} Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                        (@RingHom.id.{0} Rat
                          (@Semiring.toNonAssocSemiring.{0} Rat
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))))
                      (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.behavior.{0} Rat Rat
                        Rat Rat.instField Rat.addCommGroup
                        (@Semiring.toModule.{0} Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                        Rat.addCommGroup
                        (@Semiring.toModule.{0} Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                        g (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
                    (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1))))
                  (And
                    (@Ne.{1}
                      (@LinearMap.{0, 0, 0, 0} Rat Rat
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                        (@DivisionSemiring.toSemiring.{0} Rat
                          (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                        (@RingHom.id.{0} Rat
                          (@Semiring.toNonAssocSemiring.{0} Rat
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Rat)
                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Rat)
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) => Rat)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                          @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                        (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) => Rat)
                          fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                          @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                        (@Pi.Function.module.{0, 0, 0}
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) Rat Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                          (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                          (@Semiring.toModule.{0} Rat
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                        (@Pi.Function.module.{0, 0, 0}
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) Rat Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                          (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                          (@Semiring.toModule.{0} Rat
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))))
                      (@D5.S3.Observer.Hankel.SequenceHankelRealization.dataHankel.{0} Rat Rat Rat Rat.instField
                        Rat.addCommGroup
                        (@Semiring.toModule.{0} Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                        Rat.addCommGroup
                        (@Semiring.toModule.{0} Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                        (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.behavior.{0} Rat Rat
                          Rat Rat.instField Rat.addCommGroup
                          (@Semiring.toModule.{0} Rat
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                          Rat.addCommGroup
                          (@Semiring.toModule.{0} Rat
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                          f)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (@OfNat.ofNat.{0}
                        (@LinearMap.{0, 0, 0, 0} Rat Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                          (@RingHom.id.{0} Rat
                            (@Semiring.toNonAssocSemiring.{0} Rat
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Rat)
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Rat)
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) => Rat)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                            @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) => Rat)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                            @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                          (@Pi.Function.module.{0, 0, 0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) Rat Rat
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                            (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                            (@Semiring.toModule.{0} Rat
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                          (@Pi.Function.module.{0, 0, 0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) Rat Rat
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                            (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                            (@Semiring.toModule.{0} Rat
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))))
                        (nat_lit 0)
                        (@Zero.toOfNat0.{0}
                          (@LinearMap.{0, 0, 0, 0} Rat Rat
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                            (@RingHom.id.{0} Rat
                              (@Semiring.toNonAssocSemiring.{0} Rat
                                (@DivisionSemiring.toSemiring.{0} Rat
                                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Rat)
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Rat)
                            (@Pi.addCommMonoid.{0, 0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) => Rat)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                              @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                            (@Pi.addCommMonoid.{0, 0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) => Rat)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                              @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                            (@Pi.Function.module.{0, 0, 0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) Rat Rat
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                              (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                              (@Semiring.toModule.{0} Rat
                                (@DivisionSemiring.toSemiring.{0} Rat
                                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                            (@Pi.Function.module.{0, 0, 0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) Rat Rat
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                              (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                              (@Semiring.toModule.{0} Rat
                                (@DivisionSemiring.toSemiring.{0} Rat
                                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))))
                          (@LinearMap.instZero.{0, 0, 0, 0} Rat Rat
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Rat)
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Rat)
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                            (@Pi.addCommMonoid.{0, 0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) => Rat)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                              @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                            (@Pi.addCommMonoid.{0, 0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) => Rat)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                              @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                            (@Pi.Function.module.{0, 0, 0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) Rat Rat
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                              (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                              (@Semiring.toModule.{0} Rat
                                (@DivisionSemiring.toSemiring.{0} Rat
                                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                            (@Pi.Function.module.{0, 0, 0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) Rat Rat
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                              (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                              (@Semiring.toModule.{0} Rat
                                (@DivisionSemiring.toSemiring.{0} Rat
                                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                            (@RingHom.id.{0} Rat
                              (@Semiring.toNonAssocSemiring.{0} Rat
                                (@DivisionSemiring.toSemiring.{0} Rat
                                  (@Semifield.toDivisionSemiring.{0} Rat
                                    (@Field.toSemifield.{0} Rat Rat.instField)))))))))
                    (And
                      (@Ne.{1}
                        (@LinearMap.{0, 0, 0, 0} Rat Rat
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                          (@DivisionSemiring.toSemiring.{0} Rat
                            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                          (@RingHom.id.{0} Rat
                            (@Semiring.toNonAssocSemiring.{0} Rat
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Rat)
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Rat)
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) => Rat)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                            @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                          (@Pi.addCommMonoid.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) => Rat)
                            fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                            @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                          (@Pi.Function.module.{0, 0, 0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) Rat Rat
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                            (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                            (@Semiring.toModule.{0} Rat
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                          (@Pi.Function.module.{0, 0, 0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) Rat Rat
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                            (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                            (@Semiring.toModule.{0} Rat
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))))
                        (@D5.S3.Observer.Hankel.SequenceHankelRealization.dataHankel.{0} Rat Rat Rat Rat.instField
                          Rat.addCommGroup
                          (@Semiring.toModule.{0} Rat
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                          Rat.addCommGroup
                          (@Semiring.toModule.{0} Rat
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                          (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.behavior.{0} Rat
                            Rat Rat Rat.instField Rat.addCommGroup
                            (@Semiring.toModule.{0} Rat
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                            Rat.addCommGroup
                            (@Semiring.toModule.{0} Rat
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                            g)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (@OfNat.ofNat.{0}
                          (@LinearMap.{0, 0, 0, 0} Rat Rat
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                            (@DivisionSemiring.toSemiring.{0} Rat
                              (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                            (@RingHom.id.{0} Rat
                              (@Semiring.toNonAssocSemiring.{0} Rat
                                (@DivisionSemiring.toSemiring.{0} Rat
                                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Rat)
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Rat)
                            (@Pi.addCommMonoid.{0, 0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) => Rat)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                              @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                            (@Pi.addCommMonoid.{0, 0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) => Rat)
                              fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                              @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                            (@Pi.Function.module.{0, 0, 0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) Rat Rat
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                              (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                              (@Semiring.toModule.{0} Rat
                                (@DivisionSemiring.toSemiring.{0} Rat
                                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))))
                            (@Pi.Function.module.{0, 0, 0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) Rat Rat
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                              (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                              (@Semiring.toModule.{0} Rat
                                (@DivisionSemiring.toSemiring.{0} Rat
                                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))))
                          (nat_lit 0)
                          (@Zero.toOfNat0.{0}
                            (@LinearMap.{0, 0, 0, 0} Rat Rat
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                              (@RingHom.id.{0} Rat
                                (@Semiring.toNonAssocSemiring.{0} Rat
                                  (@DivisionSemiring.toSemiring.{0} Rat
                                    (@Semifield.toDivisionSemiring.{0} Rat
                                      (@Field.toSemifield.{0} Rat Rat.instField)))))
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Rat)
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Rat)
                              (@Pi.addCommMonoid.{0, 0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) => Rat)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                                @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                              (@Pi.addCommMonoid.{0, 0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) => Rat)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                                @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                              (@Pi.Function.module.{0, 0, 0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) Rat Rat
                                (@DivisionSemiring.toSemiring.{0} Rat
                                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                                (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                                (@Semiring.toModule.{0} Rat
                                  (@DivisionSemiring.toSemiring.{0} Rat
                                    (@Semifield.toDivisionSemiring.{0} Rat
                                      (@Field.toSemifield.{0} Rat Rat.instField)))))
                              (@Pi.Function.module.{0, 0, 0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) Rat Rat
                                (@DivisionSemiring.toSemiring.{0} Rat
                                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                                (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                                (@Semiring.toModule.{0} Rat
                                  (@DivisionSemiring.toSemiring.{0} Rat
                                    (@Semifield.toDivisionSemiring.{0} Rat
                                      (@Field.toSemifield.{0} Rat Rat.instField))))))
                            (@LinearMap.instZero.{0, 0, 0, 0} Rat Rat
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Rat)
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) → Rat)
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                              (@Pi.addCommMonoid.{0, 0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) => Rat)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                                @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                              (@Pi.addCommMonoid.{0, 0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) => Rat)
                                fun (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) =>
                                @AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                              (@Pi.Function.module.{0, 0, 0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) Rat Rat
                                (@DivisionSemiring.toSemiring.{0} Rat
                                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                                (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                                (@Semiring.toModule.{0} Rat
                                  (@DivisionSemiring.toSemiring.{0} Rat
                                    (@Semifield.toDivisionSemiring.{0} Rat
                                      (@Field.toSemifield.{0} Rat Rat.instField)))))
                              (@Pi.Function.module.{0, 0, 0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) Rat Rat
                                (@DivisionSemiring.toSemiring.{0} Rat
                                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField)))
                                (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                                (@Semiring.toModule.{0} Rat
                                  (@DivisionSemiring.toSemiring.{0} Rat
                                    (@Semifield.toDivisionSemiring.{0} Rat
                                      (@Field.toSemifield.{0} Rat Rat.instField)))))
                              (@RingHom.id.{0} Rat
                                (@Semiring.toNonAssocSemiring.{0} Rat
                                  (@DivisionSemiring.toSemiring.{0} Rat
                                    (@Semifield.toDivisionSemiring.{0} Rat
                                      (@Field.toSemifield.{0} Rat Rat.instField)))))))))
                      (And
                        (@Eq.{1} Nat
                          (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.stateDimension.{0}
                            Rat Rat Rat Rat.instField Rat.addCommGroup
                            (@Semiring.toModule.{0} Rat
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                            Rat.addCommGroup
                            (@Semiring.toModule.{0} Rat
                              (@DivisionSemiring.toSemiring.{0} Rat
                                (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                            f)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (And
                          (@Eq.{1} Nat
                            (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.stateDimension.{0}
                              Rat Rat Rat Rat.instField Rat.addCommGroup
                              (@Semiring.toModule.{0} Rat
                                (@DivisionSemiring.toSemiring.{0} Rat
                                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                              Rat.addCommGroup
                              (@Semiring.toModule.{0} Rat
                                (@DivisionSemiring.toSemiring.{0} Rat
                                  (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
                              g)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                          (And
                            (∀
                              (r :
                                @D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.{0} Rat Rat
                                  Rat Rat.instField Rat.addCommGroup
                                  (@Semiring.toModule.{0} Rat
                                    (@DivisionSemiring.toSemiring.{0} Rat
                                      (@Semifield.toDivisionSemiring.{0} Rat
                                        (@Field.toSemifield.{0} Rat Rat.instField))))
                                  Rat.addCommGroup
                                  (@Semiring.toModule.{0} Rat
                                    (@DivisionSemiring.toSemiring.{0} Rat
                                      (@Semifield.toDivisionSemiring.{0} Rat
                                        (@Field.toSemifield.{0} Rat Rat.instField))))),
                              @Eq.{1}
                                  (Nat →
                                    @LinearMap.{0, 0, 0, 0} Rat Rat
                                      (@DivisionSemiring.toSemiring.{0} Rat
                                        (@Semifield.toDivisionSemiring.{0} Rat
                                          (@Field.toSemifield.{0} Rat Rat.instField)))
                                      (@DivisionSemiring.toSemiring.{0} Rat
                                        (@Semifield.toDivisionSemiring.{0} Rat
                                          (@Field.toSemifield.{0} Rat Rat.instField)))
                                      (@RingHom.id.{0} Rat
                                        (@Semiring.toNonAssocSemiring.{0} Rat
                                          (@DivisionSemiring.toSemiring.{0} Rat
                                            (@Semifield.toDivisionSemiring.{0} Rat
                                              (@Field.toSemifield.{0} Rat Rat.instField)))))
                                      Rat Rat (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                                      (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                                      (@Semiring.toModule.{0} Rat
                                        (@DivisionSemiring.toSemiring.{0} Rat
                                          (@Semifield.toDivisionSemiring.{0} Rat
                                            (@Field.toSemifield.{0} Rat Rat.instField))))
                                      (@Semiring.toModule.{0} Rat
                                        (@DivisionSemiring.toSemiring.{0} Rat
                                          (@Semifield.toDivisionSemiring.{0} Rat
                                            (@Field.toSemifield.{0} Rat Rat.instField)))))
                                  (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.behavior.{0}
                                    Rat Rat Rat Rat.instField Rat.addCommGroup
                                    (@Semiring.toModule.{0} Rat
                                      (@DivisionSemiring.toSemiring.{0} Rat
                                        (@Semifield.toDivisionSemiring.{0} Rat
                                          (@Field.toSemifield.{0} Rat Rat.instField))))
                                    Rat.addCommGroup
                                    (@Semiring.toModule.{0} Rat
                                      (@DivisionSemiring.toSemiring.{0} Rat
                                        (@Semifield.toDivisionSemiring.{0} Rat
                                          (@Field.toSemifield.{0} Rat Rat.instField))))
                                    r)
                                  (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.behavior.{0}
                                    Rat Rat Rat Rat.instField Rat.addCommGroup
                                    (@Semiring.toModule.{0} Rat
                                      (@DivisionSemiring.toSemiring.{0} Rat
                                        (@Semifield.toDivisionSemiring.{0} Rat
                                          (@Field.toSemifield.{0} Rat Rat.instField))))
                                    Rat.addCommGroup
                                    (@Semiring.toModule.{0} Rat
                                      (@DivisionSemiring.toSemiring.{0} Rat
                                        (@Semifield.toDivisionSemiring.{0} Rat
                                          (@Field.toSemifield.{0} Rat Rat.instField))))
                                    f) →
                                @LE.le.{0} Nat instLENat
                                  (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.stateDimension.{0}
                                    Rat Rat Rat Rat.instField Rat.addCommGroup
                                    (@Semiring.toModule.{0} Rat
                                      (@DivisionSemiring.toSemiring.{0} Rat
                                        (@Semifield.toDivisionSemiring.{0} Rat
                                          (@Field.toSemifield.{0} Rat Rat.instField))))
                                    Rat.addCommGroup
                                    (@Semiring.toModule.{0} Rat
                                      (@DivisionSemiring.toSemiring.{0} Rat
                                        (@Semifield.toDivisionSemiring.{0} Rat
                                          (@Field.toSemifield.{0} Rat Rat.instField))))
                                    f)
                                  (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.stateDimension.{0}
                                    Rat Rat Rat Rat.instField Rat.addCommGroup
                                    (@Semiring.toModule.{0} Rat
                                      (@DivisionSemiring.toSemiring.{0} Rat
                                        (@Semifield.toDivisionSemiring.{0} Rat
                                          (@Field.toSemifield.{0} Rat Rat.instField))))
                                    Rat.addCommGroup
                                    (@Semiring.toModule.{0} Rat
                                      (@DivisionSemiring.toSemiring.{0} Rat
                                        (@Semifield.toDivisionSemiring.{0} Rat
                                          (@Field.toSemifield.{0} Rat Rat.instField))))
                                    r))
                            (∀
                              (r :
                                @D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.{0} Rat Rat
                                  Rat Rat.instField Rat.addCommGroup
                                  (@Semiring.toModule.{0} Rat
                                    (@DivisionSemiring.toSemiring.{0} Rat
                                      (@Semifield.toDivisionSemiring.{0} Rat
                                        (@Field.toSemifield.{0} Rat Rat.instField))))
                                  Rat.addCommGroup
                                  (@Semiring.toModule.{0} Rat
                                    (@DivisionSemiring.toSemiring.{0} Rat
                                      (@Semifield.toDivisionSemiring.{0} Rat
                                        (@Field.toSemifield.{0} Rat Rat.instField))))),
                              @Eq.{1}
                                  (Nat →
                                    @LinearMap.{0, 0, 0, 0} Rat Rat
                                      (@DivisionSemiring.toSemiring.{0} Rat
                                        (@Semifield.toDivisionSemiring.{0} Rat
                                          (@Field.toSemifield.{0} Rat Rat.instField)))
                                      (@DivisionSemiring.toSemiring.{0} Rat
                                        (@Semifield.toDivisionSemiring.{0} Rat
                                          (@Field.toSemifield.{0} Rat Rat.instField)))
                                      (@RingHom.id.{0} Rat
                                        (@Semiring.toNonAssocSemiring.{0} Rat
                                          (@DivisionSemiring.toSemiring.{0} Rat
                                            (@Semifield.toDivisionSemiring.{0} Rat
                                              (@Field.toSemifield.{0} Rat Rat.instField)))))
                                      Rat Rat (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                                      (@AddCommGroup.toAddCommMonoid.{0} Rat Rat.addCommGroup)
                                      (@Semiring.toModule.{0} Rat
                                        (@DivisionSemiring.toSemiring.{0} Rat
                                          (@Semifield.toDivisionSemiring.{0} Rat
                                            (@Field.toSemifield.{0} Rat Rat.instField))))
                                      (@Semiring.toModule.{0} Rat
                                        (@DivisionSemiring.toSemiring.{0} Rat
                                          (@Semifield.toDivisionSemiring.{0} Rat
                                            (@Field.toSemifield.{0} Rat Rat.instField)))))
                                  (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.behavior.{0}
                                    Rat Rat Rat Rat.instField Rat.addCommGroup
                                    (@Semiring.toModule.{0} Rat
                                      (@DivisionSemiring.toSemiring.{0} Rat
                                        (@Semifield.toDivisionSemiring.{0} Rat
                                          (@Field.toSemifield.{0} Rat Rat.instField))))
                                    Rat.addCommGroup
                                    (@Semiring.toModule.{0} Rat
                                      (@DivisionSemiring.toSemiring.{0} Rat
                                        (@Semifield.toDivisionSemiring.{0} Rat
                                          (@Field.toSemifield.{0} Rat Rat.instField))))
                                    r)
                                  (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.behavior.{0}
                                    Rat Rat Rat Rat.instField Rat.addCommGroup
                                    (@Semiring.toModule.{0} Rat
                                      (@DivisionSemiring.toSemiring.{0} Rat
                                        (@Semifield.toDivisionSemiring.{0} Rat
                                          (@Field.toSemifield.{0} Rat Rat.instField))))
                                    Rat.addCommGroup
                                    (@Semiring.toModule.{0} Rat
                                      (@DivisionSemiring.toSemiring.{0} Rat
                                        (@Semifield.toDivisionSemiring.{0} Rat
                                          (@Field.toSemifield.{0} Rat Rat.instField))))
                                    g) →
                                @LE.le.{0} Nat instLENat
                                  (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.stateDimension.{0}
                                    Rat Rat Rat Rat.instField Rat.addCommGroup
                                    (@Semiring.toModule.{0} Rat
                                      (@DivisionSemiring.toSemiring.{0} Rat
                                        (@Semifield.toDivisionSemiring.{0} Rat
                                          (@Field.toSemifield.{0} Rat Rat.instField))))
                                    Rat.addCommGroup
                                    (@Semiring.toModule.{0} Rat
                                      (@DivisionSemiring.toSemiring.{0} Rat
                                        (@Semifield.toDivisionSemiring.{0} Rat
                                          (@Field.toSemifield.{0} Rat Rat.instField))))
                                    g)
                                  (@D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.stateDimension.{0}
                                    Rat Rat Rat Rat.instField Rat.addCommGroup
                                    (@Semiring.toModule.{0} Rat
                                      (@DivisionSemiring.toSemiring.{0} Rat
                                        (@Semifield.toDivisionSemiring.{0} Rat
                                          (@Field.toSemifield.{0} Rat Rat.instField))))
                                    Rat.addCommGroup
                                    (@Semiring.toModule.{0} Rat
                                      (@DivisionSemiring.toSemiring.{0} Rat
                                        (@Semifield.toDivisionSemiring.{0} Rat
                                          (@Field.toSemifield.{0} Rat Rat.instField))))
                                    r))))))))))))
  Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration)

noncomputable def Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration_1.observation0 : (N : Nat) →
  (f g :
      @D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.{0} Rat Rat Rat Rat.instField
        Rat.addCommGroup
        (@Semiring.toModule.{0} Rat
          (@DivisionSemiring.toSemiring.{0} Rat
            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
        Rat.addCommGroup
        (@Semiring.toModule.{0} Rat
          (@DivisionSemiring.toSemiring.{0} Rat
            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))) →
    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 1, 0, 0, 0}
      Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (N : Nat)
    (f g :
      @D5.S3.Observer.Hankel.HankelMinimalStateDimension.FiniteLinearRealization.{0} Rat Rat Rat Rat.instField
        Rat.addCommGroup
        (@Semiring.toModule.{0} Rat
          (@DivisionSemiring.toSemiring.{0} Rat
            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))
        Rat.addCommGroup
        (@Semiring.toModule.{0} Rat
          (@DivisionSemiring.toSemiring.{0} Rat
            (@Semifield.toDivisionSemiring.{0} Rat (@Field.toSemifield.{0} Rat Rat.instField))))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 1, 0, 0, 0}
    Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.signature
    Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.actual PUnit.unit.{1} PUnit.unit.{1} f

noncomputable def Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Hankel\",\"FiniteSampleRankAmbiguity\",\"finite_sample_rank_ambiguity\"],\"part\":\"type\",\"path\":[\"body\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"function\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Hankel\",\"FiniteSampleRankAmbiguity\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity, declaration := `D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.finite_sample_rank_ambiguity, part := .type, path := [.body, .argument, .body, .argument, .body, .argument, .argument, .argument, .argument, .argument, .argument, .argument, .function, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity, declaration := `Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Hankel\",\"FiniteSampleRankAmbiguity\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Hankel\",\"FiniteSampleRankAmbiguity\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Observer\",\"Hankel\",\"FiniteSampleRankAmbiguity\",\"finite_sample_rank_ambiguity\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity, declaration := `Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity, declaration := `D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.finite_sample_rank_ambiguity, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration).actual (Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration).variation.2.choose (Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration).variation.1 (Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Hankel\",\"FiniteSampleRankAmbiguity\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Observer\",\"Hankel\",\"FiniteSampleRankAmbiguity\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity, declaration := `Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity, declaration := `Reg.D5.S3.Observer.Hankel.FiniteSampleRankAmbiguity.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
