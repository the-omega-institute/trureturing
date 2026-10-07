import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.NonProjectiveDarkEffect
import Reg.Support.DependentFamily
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics
open _root_.D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure
open _root_.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect
open LeanInformationAudit
open Lean Elab Command
open Matrix Filter Topology
open scoped ComplexOrder MatrixOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect

@[reducible] def signature : Signature where
  Params := ℝ
  State _ := Matrix (Fin 2) (Fin 2) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Matrix (Fin 2) (Fin 2) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ F => F) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (a : ℝ), 0 < a → a < 1 →
    ∃ (Q : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ)
      (L : Fin 1 → Matrix (Fin 2) (Fin 2) ℂ)
      (F : Matrix (Fin 2) (Fin 2) ℂ),
      Q 0 = basisProjector (0 : Fin 2) ∧
      Q 1 = Matrix.single 0 1 (Real.sqrt a : ℂ) ∧
      L 0 = (Real.sqrt (1 - a) : ℂ) • basisProjector (1 : Fin 2) ∧
      (∑ i, (Q i)ᴴ * Q i) + ∑ i, (L i)ᴴ * L i = 1 ∧
      (∀ X, noClickDual Q X = X 0 0 • F) ∧
      (∀ N, 1 ≤ N → survival Q N = F) ∧
      Tendsto (survival Q) atTop (𝓝 F) ∧
      R.readout () a F =
        basisProjector (0 : Fin 2) + (a : ℂ) • basisProjector (1 : Fin 2) ∧
      F * F ≠ F ∧
      (∀ v : Fin 2 → ℂ, star v ⬝ᵥ v = 1 →
        (star v ⬝ᵥ (F *ᵥ v) = 1 ↔ v 1 = 0)) ∧
      (basisProjector (1 : Fin 2) * F).trace = (a : ℂ) ∧
      (basisProjector (1 : Fin 2) * ((L 0)ᴴ * L 0)).trace = ((1 - a : ℝ) : ℂ) ∧
      (basisProjector (1 : Fin 2) * basisProjector (0 : Fin 2)).trace = 0



theorem actual_law : arena.Law actual := by
  simpa only [arena, actual, realize] using non_projective_dark_effect

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨Q, L, F, _hQ0, _hQ1, _hL0, _hcomp, _hdual, _hstable, _hlimit,
    hF, _hnotIdempotent, _hunitDirections, _htrace, _hclick, _hweight⟩ :=
      h (1 / 2 : ℝ) (by norm_num) (by norm_num)
  have hentry := congrFun (congrFun hF (0 : Fin 2)) (0 : Fin 2)
  simp only [rejected, realize, signature, basisProjector, Matrix.add_apply,
    Matrix.smul_apply, Matrix.single_apply] at hentry
  have hzero : (0 : Matrix (Fin 2) (Fin 2) ℂ) (0 : Fin 2) (0 : Fin 2) = 0 := rfl
  rw [hzero] at hentry
  norm_num at hentry

theorem sensitivity_proof : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    cases i
    cases j
    exact (hji rfl).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(0 : ℝ), (0 : Matrix (Fin 2) (Fin 2) ℂ),
    (1 : Matrix (Fin 2) (Fin 2) ℂ), ?_⟩
  intro h
  have hentry := congrFun (congrFun h (0 : Fin 2)) (0 : Fin 2)
  norm_num [actual, realize] at hentry

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.non_projective_dark_effect) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ F => F) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Measurement") "NonProjectiveDarkEffect") "non_projective_dark_effect") "Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect/Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ F => F) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Measurement.NonProjectiveDarkEffect, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "fn", "arg"], stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Measurement.NonProjectiveDarkEffect, declaration := `D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.non_projective_dark_effect, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect, declaration := `Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect, declaration := `Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect, declaration := `Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect, declaration := `Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration_1.observationFact0, `Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration_1.anchorEnumeration }


#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof


end Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect


noncomputable def Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.arena
noncomputable def Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"NonProjectiveDarkEffect\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"NonProjectiveDarkEffect\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect, declaration := `Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect, declaration := `Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.arena
noncomputable def Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"NonProjectiveDarkEffect\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"NonProjectiveDarkEffect\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect, declaration := `Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect, declaration := `Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.arena
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
      Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.arena
      Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.actual)
    Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration)

noncomputable def Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"NonProjectiveDarkEffect\",\"non_projective_dark_effect\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"NonProjectiveDarkEffect\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Measurement.NonProjectiveDarkEffect, declaration := `D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.non_projective_dark_effect, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect, declaration := `Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.arena
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.arena
    Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.actual)
  Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration)

noncomputable def Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration_1.observation0 : (a : Real) →
  (ha0 : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) a) →
    (ha1 : @LT.lt.{0} Real Real.instLT a (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
      (Q :
          Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
            Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex) →
        (L :
            Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
              Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex) →
          (F :
              Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex) →
            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.signature PUnit.unit.{1} a :=
  fun (a : Real)
    (ha0 : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) a)
    (ha1 : @LT.lt.{0} Real Real.instLT a (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
    (Q :
      Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
        Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
    (L :
      Fin (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
    (F :
      Matrix.{0, 0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.signature
    Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.actual PUnit.unit.{1} a F

noncomputable def Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"NonProjectiveDarkEffect\",\"non_projective_dark_effect\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"function\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"NonProjectiveDarkEffect\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Measurement.NonProjectiveDarkEffect, declaration := `D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.non_projective_dark_effect, part := .type, path := [.body, .body, .body, .argument, .body, .argument, .body, .argument, .body, .argument, .argument, .argument, .argument, .argument, .argument, .argument, .function, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect, declaration := `Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"NonProjectiveDarkEffect\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"NonProjectiveDarkEffect\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"NonProjectiveDarkEffect\",\"non_projective_dark_effect\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect, declaration := `Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Quantum.Measurement.NonProjectiveDarkEffect, declaration := `D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.non_projective_dark_effect, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration).actual (Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration).variation.2.choose (Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration).variation.1 (Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"NonProjectiveDarkEffect\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"NonProjectiveDarkEffect\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect, declaration := `Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect, declaration := `Reg.D5.S3.Quantum.Measurement.NonProjectiveDarkEffect.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
