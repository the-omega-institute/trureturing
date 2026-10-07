import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer
import Reg.Support.DependentFamily
import Mathlib.Data.Fintype.EquivFin

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer
open _root_.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ d => d ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- The complete original negative statement; only its cardinality readout varies. -/
abbrev arena : Arena where
  signature := signature
  Law r := ¬ ∀ (d : ℕ) (G : Type) [Group G] [Fintype G]
    (π : G → Matrix (Fin d) (Fin d) ℂ)
    (W : Submodule ℂ (EuclideanSpace ℂ (Fin d))),
    IsPEM π → Fintype.card G = r.readout () () d →
    (logicalOps π W).ncard * (stabilizers π W).ncard = Fintype.card G →
    ∀ g : G, ∀ s ∈ stabilizers π W, g * s * g⁻¹ ∈ stabilizers π W

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  apply h
  intro d G group finite π W pem cardinality balance g s hs
  change Fintype.card G = 1 at cardinality
  obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.mp cardinality
  have equal : g * s * g⁻¹ = s := (hx _).trans (hx _).symm
  simpa only [equal] using hs

def registration : Registration arena
    (¬ _root_.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.claim) where
  actual := actual
  bridge := by rfl
  variation := ⟨_root_.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := by
    intro ⟨⟩
    exact ⟨(), 1, 2, by decide⟩

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.result) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ d => d ^ 2) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Information") "NiceErrorBasisNonNormalStabilizer") "result") "Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer/Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ d => d ^ 2) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer, definition := some { owner := `D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer, name := `D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.claim, path := #["arg"] }, coordinates := #[], readouts := #[{ path := #["arg", "body", "body", "body", "body", "body", "body", "body", "domain", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer, declaration := `D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.result, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer, declaration := `Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer, declaration := `Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer, declaration := `Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer, declaration := `Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] },
    { owner := `D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer, declaration := `D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.claim, part := .value, path := [], levels := [] }], facts := [`Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration_1.observationFact0, `Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration_1.anchorEnumeration }


#print axioms registration

end Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer


noncomputable def Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.arena
noncomputable def Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"NiceErrorBasisNonNormalStabilizer\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"NiceErrorBasisNonNormalStabilizer\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer, declaration := `Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer, declaration := `Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.arena
noncomputable def Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"NiceErrorBasisNonNormalStabilizer\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"NiceErrorBasisNonNormalStabilizer\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer, declaration := `Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer, declaration := `Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.arena) (Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration).actual

noncomputable def Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Information\",\"NiceErrorBasisNonNormalStabilizer\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"NiceErrorBasisNonNormalStabilizer\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer, declaration := `D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.result, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer, declaration := `Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration).bridge

noncomputable def Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration_1.observation0 : (d : Nat) →
  (G : Type) →
    [inst : Group.{0} G] →
      [Fintype.{0} G] →
        (π : G → Matrix.{0, 0, 0} (Fin d) (Fin d) Complex) →
          (W :
              @Submodule.{0, 0} Complex (EuclideanSpace.{0, 0} Complex (Fin d)) Complex.instSemiring
                (@AddCommGroup.toAddCommMonoid.{0} (EuclideanSpace.{0, 0} Complex (Fin d))
                  (@WithLp.instAddCommGroup.{0}
                    (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                        (@AddMonoidWithOne.toNatCast.{0} ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                        PiLp.innerProductSpace._proof_1))
                    ((i : Fin d) → (fun (x : Fin d) => Complex) i)
                    (@Pi.addCommGroup.{0, 0} (Fin d) (fun (x : Fin d) => Complex) fun (i : Fin d) =>
                      Complex.addCommGroup)))
                (@WithLp.instModule.{0, 0}
                  (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                      PiLp.innerProductSpace._proof_1))
                  Complex ((i : Fin d) → (fun (x : Fin d) => Complex) i) Complex.instSemiring
                  (@Pi.addCommGroup.{0, 0} (Fin d) (fun (x : Fin d) => Complex) fun (i : Fin d) => Complex.addCommGroup)
                  (@Pi.Function.module.{0, 0, 0} (Fin d) Complex Complex Complex.instSemiring Complex.instAddCommMonoid
                    (@Semiring.toModule.{0} Complex Complex.instSemiring)))) →
            @D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.IsPEM G inst d π →
              D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.signature PUnit.unit.{1} PUnit.unit.{1} :=
  fun (d : Nat) (G : Type) [Group.{0} G] [Fintype.{0} G] (π : G → Matrix.{0, 0, 0} (Fin d) (Fin d) Complex)
    (W :
      @Submodule.{0, 0} Complex (EuclideanSpace.{0, 0} Complex (Fin d)) Complex.instSemiring
        (@AddCommGroup.toAddCommMonoid.{0} (EuclideanSpace.{0, 0} Complex (Fin d))
          (@WithLp.instAddCommGroup.{0}
            (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                PiLp.innerProductSpace._proof_1))
            ((i : Fin d) → (fun (x : Fin d) => Complex) i)
            (@Pi.addCommGroup.{0, 0} (Fin d) (fun (x : Fin d) => Complex) fun (i : Fin d) => Complex.addCommGroup)))
        (@WithLp.instModule.{0, 0}
          (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
              (@AddMonoidWithOne.toNatCast.{0} ENNReal
                (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
              PiLp.innerProductSpace._proof_1))
          Complex ((i : Fin d) → (fun (x : Fin d) => Complex) i) Complex.instSemiring
          (@Pi.addCommGroup.{0, 0} (Fin d) (fun (x : Fin d) => Complex) fun (i : Fin d) => Complex.addCommGroup)
          (@Pi.Function.module.{0, 0, 0} (Fin d) Complex Complex Complex.instSemiring Complex.instAddCommMonoid
            (@Semiring.toModule.{0} Complex Complex.instSemiring))))
    (a : @D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.IsPEM G inst d π) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.signature
    Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.actual PUnit.unit.{1} PUnit.unit.{1} d

noncomputable def Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Information\",\"NiceErrorBasisNonNormalStabilizer\",\"claim\"],\"part\":\"value\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"domain\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"NiceErrorBasisNonNormalStabilizer\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer, declaration := `D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.claim, part := .value, path := [.body, .body, .body, .body, .body, .body, .body, .domain, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer, declaration := `Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"NiceErrorBasisNonNormalStabilizer\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"NiceErrorBasisNonNormalStabilizer\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Information\",\"NiceErrorBasisNonNormalStabilizer\",\"result\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer, declaration := `Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer, declaration := `D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.result, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration).actual (Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration).variation.2.choose (Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration).variation.1 (Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"NiceErrorBasisNonNormalStabilizer\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Information\",\"NiceErrorBasisNonNormalStabilizer\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer, declaration := `Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer, declaration := `Reg.D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
