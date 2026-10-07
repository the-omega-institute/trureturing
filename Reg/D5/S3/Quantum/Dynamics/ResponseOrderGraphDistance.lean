import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance
import Reg.Support.DependentFamily
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance
open LeanInformationAudit
open Lean Elab Command
open scoped Matrix

noncomputable section
namespace Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance

@[reducible] def graphDistanceSignature : Signature where
  Params := Σ d : ℕ, Σ _ : Matrix (Fin d) (Fin d) ℝ, Σ _ : Fin d, Fin d
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization graphDistanceSignature :=
  realize graphDistanceSignature
    (fun _ p n => (p.2.1 ^ n) p.2.2.2 p.2.2.1)
    (fun e => nomatch e)

def rejected : Realization graphDistanceSignature :=
  realize graphDistanceSignature
    (fun _ _ _ => (1 : ℝ))
    (fun e => nomatch e)

def arena : Arena where
  signature := graphDistanceSignature
  Law R := ∀ {d : ℕ}
    (H : Matrix (Fin d) (Fin d) ℝ)
    (_hsym : ∀ i j, H i j = H j i)
    (_hoff : ∀ i j, i ≠ j → 0 ≤ H i j)
    {i j : Fin d} (_hne : i ≠ j)
    (_hreach : (couplingGraph H).Reachable i j),
    (∀ n < (couplingGraph H).dist i j, R.readout () ⟨d, H, i, j⟩ n = 0) ∧
      0 < (H ^ (couplingGraph H).dist i j) j i



theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let H : Matrix (Fin 2) (Fin 2) ℝ := fun _ _ => 1
  have hadj : (couplingGraph H).Adj (0 : Fin 2) 1 := by
    simp [couplingGraph, H]
  have hdist : (couplingGraph H).dist (0 : Fin 2) 1 = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr hadj
  have htest := (h H (by simp [H]) (by simp [H])
    (i := 0) (j := 1) (by decide) hadj.reachable).1 0 (by omega)
  norm_num [rejected, realize, graphDistanceSignature] at htest

theorem actual_law : arena.Law actual := by
  intro d H hsym hoff i j hne hreach
  exact first_nonzero_power_eq_graph_distance H hsym hoff hne hreach

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

theorem dependence_proof : ObservationalDependence graphDistanceSignature actual := by
  intro i
  cases i
  let H : Matrix (Fin 2) (Fin 2) ℝ := fun _ _ => 1
  let p : graphDistanceSignature.Params := ⟨2, H, 0, 1⟩
  refine ⟨p, (0 : ℕ), (1 : ℕ), ?_⟩
  change (H ^ (0 : ℕ)) (1 : Fin 2) (0 : Fin 2) ≠ (H ^ (1 : ℕ)) 1 0
  rw [pow_zero, pow_one]
  norm_num [Matrix.one_apply, H]

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.first_nonzero_power_eq_graph_distance) (type_of% (realize.{0, 0, 0, 0, 0} graphDistanceSignature
    (fun _ p n => (p.2.1 ^ n) p.2.2.2 p.2.2.1)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Dynamics") "ResponseOrderGraphDistance") "first_nonzero_power_eq_graph_distance") "Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance/Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} graphDistanceSignature
    (fun _ p n => (p.2.1 ^ n) p.2.2.2 p.2.2.1)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance, definition := none, coordinates := #[0, 1, 4, 5], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "body", "fn", "arg"], stateBinder := 8, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance, declaration := `D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.first_nonzero_power_eq_graph_distance, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance, declaration := `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance, declaration := `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance, declaration := `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance, declaration := `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration_1.observationFact0, `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration_1.anchorEnumeration }


#print axioms rejected_law
#print axioms actual_law
#print axioms sensitivity_proof
#print axioms dependence_proof


end Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance


noncomputable def Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.arena
noncomputable def Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Dynamics\",\"ResponseOrderGraphDistance\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Dynamics\",\"ResponseOrderGraphDistance\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance, declaration := `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance, declaration := `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.arena
noncomputable def Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Dynamics\",\"ResponseOrderGraphDistance\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Dynamics\",\"ResponseOrderGraphDistance\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance, declaration := `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance, declaration := `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0} (Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.arena) (Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration).actual

noncomputable def Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Dynamics\",\"ResponseOrderGraphDistance\",\"first_nonzero_power_eq_graph_distance\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Dynamics\",\"ResponseOrderGraphDistance\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance, declaration := `D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.first_nonzero_power_eq_graph_distance, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance, declaration := `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration).bridge

noncomputable def Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration_1.observation0 : {d : Nat} →
  (H : Matrix.{0, 0, 0} (Fin d) (Fin d) Real) →
    (hsym : ∀ (i j : Fin d), @Eq.{1} Real (H i j) (H j i)) →
      (hoff :
          ∀ (i j : Fin d),
            @Ne.{1} (Fin d) i j →
              @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                (H i j)) →
        {i j : Fin d} →
          (hne : @Ne.{1} (Fin d) i j) →
            (hreach :
                @SimpleGraph.Reachable.{0} (Fin d)
                  (@D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.couplingGraph d H) i j) →
              (n : Nat) →
                @LT.lt.{0} Nat instLTNat n
                    (@SimpleGraph.dist.{0} (Fin d)
                      (@D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.couplingGraph d H) i j) →
                  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                    Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.graphDistanceSignature PUnit.unit.{1}
                    (@Sigma.mk.{0, 0} Nat
                      (fun (d : Nat) =>
                        @Sigma.{0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Real)
                          fun (x : Matrix.{0, 0, 0} (Fin d) (Fin d) Real) =>
                          @Sigma.{0, 0} (Fin d) fun (x : Fin d) => Fin d)
                      d
                      (@Sigma.mk.{0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Real)
                        (fun (x : Matrix.{0, 0, 0} (Fin d) (Fin d) Real) =>
                          @Sigma.{0, 0} (Fin d) fun (x : Fin d) => Fin d)
                        H (@Sigma.mk.{0, 0} (Fin d) (fun (x : Fin d) => Fin d) i j))) :=
  fun {d : Nat} (H : Matrix.{0, 0, 0} (Fin d) (Fin d) Real) (hsym : ∀ (i j : Fin d), @Eq.{1} Real (H i j) (H j i))
    (hoff :
      ∀ (i j : Fin d),
        @Ne.{1} (Fin d) i j →
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (H i j))
    {i j : Fin d} (hne : @Ne.{1} (Fin d) i j)
    (hreach :
      @SimpleGraph.Reachable.{0} (Fin d) (@D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.couplingGraph d H) i j)
    (n : Nat)
    (a :
      @LT.lt.{0} Nat instLTNat n
        (@SimpleGraph.dist.{0} (Fin d) (@D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.couplingGraph d H) i j)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.graphDistanceSignature
    Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.actual PUnit.unit.{1}
    (@Sigma.mk.{0, 0} Nat
      (fun (d : Nat) =>
        @Sigma.{0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Real) fun (x : Matrix.{0, 0, 0} (Fin d) (Fin d) Real) =>
          @Sigma.{0, 0} (Fin d) fun (x : Fin d) => Fin d)
      d
      (@Sigma.mk.{0, 0} (Matrix.{0, 0, 0} (Fin d) (Fin d) Real)
        (fun (x : Matrix.{0, 0, 0} (Fin d) (Fin d) Real) => @Sigma.{0, 0} (Fin d) fun (x : Fin d) => Fin d) H
        (@Sigma.mk.{0, 0} (Fin d) (fun (x : Fin d) => Fin d) i j)))
    n

noncomputable def Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Dynamics\",\"ResponseOrderGraphDistance\",\"first_nonzero_power_eq_graph_distance\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"function\",\"argument\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Dynamics\",\"ResponseOrderGraphDistance\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance, declaration := `D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.first_nonzero_power_eq_graph_distance, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .body, .function, .argument, .body, .body, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance, declaration := `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Dynamics\",\"ResponseOrderGraphDistance\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Dynamics\",\"ResponseOrderGraphDistance\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Dynamics\",\"ResponseOrderGraphDistance\",\"first_nonzero_power_eq_graph_distance\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance, declaration := `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance, declaration := `D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.first_nonzero_power_eq_graph_distance, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration).actual (Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration).variation.2.choose (Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration).variation.1 (Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Dynamics\",\"ResponseOrderGraphDistance\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Dynamics\",\"ResponseOrderGraphDistance\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance, declaration := `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance, declaration := `Reg.D5.S3.Quantum.Dynamics.ResponseOrderGraphDistance.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
