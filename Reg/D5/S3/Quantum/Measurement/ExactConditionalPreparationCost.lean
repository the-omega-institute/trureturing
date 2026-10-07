import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.ExactConditionalPreparationCost
import Reg.Support.DependentFamily
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost
open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel
open LeanInformationAudit
open Lean Elab Command
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder


noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost

universe u

@[reducible] def effectSignature : Signature where
  Params := Type u
  State ι := Matrix ι ι ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ ι := Matrix ι ι ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization effectSignature.{u} :=
  realize effectSignature.{u} (fun _ _ R => R) (fun e => nomatch e)

def rejected : Realization effectSignature.{u} :=
  realize effectSignature.{u}
    (fun _ ι _ => (0 : Matrix ι ι ℂ)) (fun e => nomatch e)

def arena : Arena where
  signature := effectSignature.{u}
  Law Q := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (R : Matrix ι ι ℂ) (hR : R.PosDef),
    (∀ {m : ℕ} (K : Fin m → Matrix ι ι ℂ), ExactPreparationContract R K →
      ∃ c : ℝ, 0 < c ∧ ∀ X : Matrix ι ι ℂ,
        (fun K X => PhyslibLeaf.MatrixMap.of_kraus K K X) K X = (c : ℂ) • (CFC.sqrt R * X * CFC.sqrt R)) ∧
    (∀ c : ℝ, 0 < c →
      let Kc : Fin 1 → Matrix ι ι ℂ := fun _ =>
        (Real.sqrt c) • CFC.sqrt R;
      (∀ ρ : Matrix ι ι ℂ, ρ.PosSemidef → ρ.trace = 1 →
        0 < ((fun K X => PhyslibLeaf.MatrixMap.of_kraus K K X) Kc ρ).trace.re ∧
        (fun K X => PhyslibLeaf.MatrixMap.of_kraus K K X) Kc ρ = (((fun K X => PhyslibLeaf.MatrixMap.of_kraus K K X) Kc ρ).trace / (R * ρ).trace) •
          (CFC.sqrt R * ρ * CFC.sqrt R)) ∧
      (TraceNonincreasing Kc ↔ (1 - c • R).PosSemidef)) ∧
    (∀ {m : ℕ} (K : Fin m → Matrix ι ι ℂ) (c : ℝ), 0 < c →
      (∀ X : Matrix ι ι ℂ,
        (fun K X => PhyslibLeaf.MatrixMap.of_kraus K K X) K X = (c : ℂ) • (CFC.sqrt R * X * CFC.sqrt R)) →
      (TraceNonincreasing K ↔ (1 - (c : ℂ) • R).PosSemidef)) ∧
    (∀ {m : ℕ} (K : Fin m → Matrix ι ι ℂ), ExactPreparationContract R K →
      TraceNonincreasing K → ∃ ρ : Matrix ι ι ℂ,
        ρ.PosSemidef ∧ ρ.trace = 1 ∧
        ((fun K X => PhyslibLeaf.MatrixMap.of_kraus K K X) K ρ).trace.re ≤
          leastEigenvalue R hR / greatestEigenvalue R hR) ∧
    (let Kopt : Fin 1 → Matrix ι ι ℂ := fun _ =>
        (((1 / Real.sqrt (greatestEigenvalue R hR) : ℝ) : ℂ) • CFC.sqrt R);
      let Kfail : Matrix ι ι ℂ :=
        CFC.sqrt (1 - ((1 / greatestEigenvalue R hR : ℝ) : ℂ) • R);
      ExactPreparationContract R Kopt ∧ TraceNonincreasing Kopt ∧
        (Kopt 0)ᴴ * Kopt 0 + Kfailᴴ * Kfail = 1 ∧
        ∀ ρ : Matrix ι ι ℂ, ρ.PosSemidef → ρ.trace = 1 →
          leastEigenvalue R hR / greatestEigenvalue R hR ≤
            ((fun K X => PhyslibLeaf.MatrixMap.of_kraus K K X) Kopt ρ).trace.re) ∧
    ((∃ (m : ℕ) (K : Fin m → Matrix ι ι ℂ),
        ExactPreparationContract R K ∧ TraceNonincreasing K ∧
        ∀ ρ : Matrix ι ι ℂ, ρ.PosSemidef → ρ.trace = 1 →
          ((fun K X => PhyslibLeaf.MatrixMap.of_kraus K K X) K ρ).trace = 1) ↔
      ∃ scalar : ℝ, 0 < scalar ∧
        Q.readout () ι R = (scalar : ℂ) • 1)



theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hLaw := h
    (R := (1 : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℂ))
    Matrix.PosDef.one
  have hDeterministic :
      ∃ (m : ℕ) (K : Fin m →
        Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℂ),
        ExactPreparationContract 1 K ∧ TraceNonincreasing K ∧
        ∀ ρ : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℂ,
          ρ.PosSemidef → ρ.trace = 1 →
          ((fun K X => PhyslibLeaf.MatrixMap.of_kraus K K X) K ρ).trace = 1 := by
    exact (exact_conditional_preparation_cost
      (R := (1 : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℂ))
        Matrix.PosDef.one).2.2.2.2.2.mpr
        ⟨1, by norm_num, by simp⟩
  obtain ⟨scalar, hscalar, hzero⟩ := hLaw.2.2.2.2.2.mp hDeterministic
  have hentry := congrFun (congrFun hzero (ULift.up 0)) (ULift.up 0)
  change (0 : ℂ) = (scalar : ℂ) *
    (1 : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℂ)
      (ULift.up 0) (ULift.up 0) at hentry
  have hscalarComplex : (scalar : ℂ) = 0 := by
    simpa only [Matrix.one_apply_eq, mul_one] using hentry.symm
  exact hscalar.ne' (Complex.ofReal_injective hscalarComplex)

theorem actual_law : arena.{u}.Law actual := by
  intro ι _ _ _ R hR
  simpa only [actual, realize] using exact_conditional_preparation_cost R hR

theorem sensitivity_proof : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    cases i
    cases j
    exact (hji rfl).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence effectSignature.{u} actual := by
  intro i
  cases i
  refine ⟨ULift.{u} (Fin 1),
    (0 : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℂ),
    (1 : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1)) ℂ), ?_⟩
  intro h
  have hentry := congrFun (congrFun h (ULift.up 0)) (ULift.up 0)
  norm_num [actual, realize] at hentry

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_1.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.exact_conditional_preparation_cost.{u_1}) (type_of% (realize.{u_1 + 1, u_1, 0, u_1, 0} effectSignature.{u_1} (fun _ _ R => R) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Measurement") "ExactConditionalPreparationCost") "exact_conditional_preparation_cost") "Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost/Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1})⟩,
  objectArena := .source ⟨(arena.{u_1})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨(registration.{u_1})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_1 + 1, u_1, 0, u_1, 0} effectSignature.{u_1} (fun _ _ R => R) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Measurement.ExactConditionalPreparationCost, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "arg", "arg", "body", "arg", "fn", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Measurement.ExactConditionalPreparationCost, declaration := `D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.exact_conditional_preparation_cost, part := .type, path := [], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost, declaration := `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost, declaration := `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost, declaration := `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost, declaration := `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1] }], facts := [`Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration_1.observationFact0, `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration_1.anchorEnumeration }


#print axioms rejected_law
#print axioms actual_law
#print axioms sensitivity_proof
#print axioms dependence_proof


end Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost


noncomputable def Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration_1.canonicalArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, u_1, 0} :=
  Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.arena.{u_1}
noncomputable def Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration_1.canonicalArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ExactConditionalPreparationCost\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ExactConditionalPreparationCost\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost, declaration := `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost, declaration := `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration_1.canonicalObjectArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, u_1, 0} :=
  Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.arena.{u_1}
noncomputable def Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration_1.canonicalObjectArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ExactConditionalPreparationCost\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ExactConditionalPreparationCost\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost, declaration := `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost, declaration := `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration_1.sourceLaw.{u_1} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_1 + 1, u_1, 0, u_1, 0}
  Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.arena.{u_1}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{u_1 + 1, u_1, 0, u_1, 0}
    Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.arena.{u_1}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_1 + 1, u_1, 0, u_1, 0}
      Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.arena.{u_1}
      Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.actual.{u_1})
    Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration.{u_1})

noncomputable def Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration_1.sourceBridgeFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ExactConditionalPreparationCost\",\"exact_conditional_preparation_cost\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ExactConditionalPreparationCost\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Quantum.Measurement.ExactConditionalPreparationCost, declaration := `D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.exact_conditional_preparation_cost, part := .type, path := [], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost, declaration := `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{u_1 + 1, u_1, 0, u_1, 0}
  Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.arena.{u_1}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_1 + 1, u_1, 0, u_1, 0}
    Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.arena.{u_1}
    Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.actual.{u_1})
  Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration.{u_1})

noncomputable def Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration_1.observation0.{u_1} : {ι : Type u_1} →
  [Fintype.{u_1} ι] →
    [DecidableEq.{u_1 + 1} ι] →
      [Nonempty.{u_1 + 1} ι] →
        (R : Matrix.{u_1, u_1, 0} ι ι Complex) →
          (hR : @Matrix.PosDef.{u_1, 0} ι Complex Complex.instRing Complex.partialOrder Complex.instStarRing R) →
            (scalar : Real) →
              D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u_1 + 1, u_1, 0, u_1, 0}
                Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.effectSignature.{u_1} PUnit.unit.{1} ι :=
  fun {ι : Type u_1} [Fintype.{u_1} ι] [DecidableEq.{u_1 + 1} ι] [Nonempty.{u_1 + 1} ι]
    (R : Matrix.{u_1, u_1, 0} ι ι Complex)
    (hR : @Matrix.PosDef.{u_1, 0} ι Complex Complex.instRing Complex.partialOrder Complex.instStarRing R)
    (scalar : Real) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u_1 + 1, u_1, 0, u_1, 0}
    Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.effectSignature.{u_1}
    Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.actual.{u_1} PUnit.unit.{1} ι R

noncomputable def Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration_1.observationFact0.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ExactConditionalPreparationCost\",\"exact_conditional_preparation_cost\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"argument\",\"body\",\"argument\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ExactConditionalPreparationCost\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Quantum.Measurement.ExactConditionalPreparationCost, declaration := `D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.exact_conditional_preparation_cost, part := .type, path := [.body, .body, .body, .body, .body, .body, .argument, .argument, .argument, .argument, .argument, .argument, .argument, .body, .argument, .function, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost, declaration := `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration_1.varyingLawInput.{u_1} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration_1.canonicalArenaOperand.{u_1})
noncomputable def Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration_1.varyingLaw.{u_1}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ExactConditionalPreparationCost\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration_1.statementExclusion.{u_1} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ExactConditionalPreparationCost\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ExactConditionalPreparationCost\",\"exact_conditional_preparation_cost\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost, declaration := `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1)] }
  statementLocation := { owner := `D5.S3.Quantum.Measurement.ExactConditionalPreparationCost, declaration := `D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.exact_conditional_preparation_cost, part := .type, path := [], levels := [(.param `u_1)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration.{u_1}).actual (Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration.{u_1}).variation.2.choose (Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration.{u_1}).variation.1 (Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration.{u_1}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration_1.descriptorFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ExactConditionalPreparationCost\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Measurement\",\"ExactConditionalPreparationCost\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost, declaration := `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost, declaration := `Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))
