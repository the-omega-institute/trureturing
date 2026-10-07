import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight
import Reg.Support.GraphCutRegistrationTemplates
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.GraphCutRegistrationTemplates
open _root_.D5.S3.Fourier.CharacterSelection.SimpleGraphCycleSpace
open _root_.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight
open LeanInformationAudit
open Lean Elab Command
open SimpleGraph

noncomputable section
namespace Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight

universe u

def actual : Realization graphGradientSignature.{u} :=
  realize graphGradientSignature.{u}
    (fun _ p x => edgeDifferential p.2 x) (fun e => nomatch e)

def rejected : Realization graphGradientSignature.{u} :=
  realize graphGradientSignature.{u}
    (fun _ p _ => (0 : p.2.edgeSet → ZMod 2)) (fun e => nomatch e)

def arena : Arena where
  signature := graphGradientSignature.{u}
  Law r := ∀ {V : Type u} (G : SimpleGraph V) [Fintype G.edgeSet] (k : Nat),
    G.IsEdgeConnected k ↔
      ∀ x : V → ZMod 2,
        (∃ a b : V, x a ≠ x b) →
          k ≤ hammingNorm (r.readout () ⟨V, G⟩ x)



theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  let G : SimpleGraph (ULift.{u} Bool) := completeGraph _
  have hc : G.IsEdgeConnected 1 := isEdgeConnected_one.mpr (connected_top.preconnected)
  have hw := (h (V := ULift.{u} Bool) G 1).mp hc
  let x : ULift.{u} Bool → ZMod 2 := fun b => if b.down then 1 else 0
  have hx : ∃ a b : ULift.{u} Bool, x a ≠ x b :=
    ⟨⟨false⟩, ⟨true⟩, by norm_num [x]⟩
  have hbad := hw x hx
  change 1 ≤ hammingNorm (0 : G.edgeSet → ZMod 2) at hbad
  simp at hbad

theorem sensitivity_proof : Sensitivity arena.{u} actual.{u} := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hj
    have hji : j = i := by
      cases j
      cases i
      rfl
    exact (hj hji).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence graphGradientSignature.{u} actual.{u} := by
  intro i
  let G : SimpleGraph (ULift.{u} Bool) := completeGraph _
  let x : ULift.{u} Bool → ZMod 2 := fun b => if b.down then 1 else 0
  refine ⟨⟨ULift.{u} Bool, G⟩, (fun _ => 0), x, ?_⟩
  intro h
  have he : s((⟨false⟩ : ULift.{u} Bool), ⟨true⟩) ∈ G.edgeSet := by simp [G]
  have hp := congrArg (fun f : G.edgeSet → ZMod 2 =>
    f ⟨s((⟨false⟩ : ULift.{u} Bool), ⟨true⟩), he⟩) h
  change (0 : ZMod 2) = 0 + 1 at hp
  norm_num at hp

def registration : Registration arena.{u} (arena.{u}.Law actual.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨edge_connected_iff_gradient_weight, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

noncomputable def registration_1.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.edge_connected_iff_gradient_weight.{u_1}) (type_of% (realize.{u_1 + 1, u_1, 0, u_1, 0} graphGradientSignature.{u_1}
    (fun _ p x => edgeDifferential.{u_1} p.2 x) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Fourier") "CharacterSelection") "EdgeConnectivityGradientWeight") "edge_connected_iff_gradient_weight") "Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight/Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u_1})⟩,
  objectArena := .source ⟨(arena.{u_1})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u_1}) ⟨(registration.{u_1})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u_1 + 1, u_1, 0, u_1, 0} graphGradientSignature.{u_1}
    (fun _ p x => edgeDifferential.{u_1} p.2 x) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight, definition := none, coordinates := #[0, 1], readouts := #[{ path := #["body", "body", "body", "body", "arg", "body", "body", "arg", "arg"], stateBinder := 4, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight, declaration := `D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.edge_connected_iff_gradient_weight, part := .type, path := [], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight, declaration := `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight, declaration := `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight, declaration := `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight, declaration := `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1] }], facts := [`Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration_1.canonicalArenaFact, `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration_1.sourceBridgeFact, `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration_1.observationFact0, `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration_1.anchorEnumeration }


#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof


end Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight


noncomputable def Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration_1.canonicalArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, u_1, 0} :=
  Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.arena.{u_1}
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration_1.canonicalArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"EdgeConnectivityGradientWeight\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"EdgeConnectivityGradientWeight\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight, declaration := `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight, declaration := `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration_1.canonicalObjectArenaOperand.{u_1} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u_1 + 1, u_1, 0, u_1, 0} :=
  Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.arena.{u_1}
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration_1.canonicalObjectArenaFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"EdgeConnectivityGradientWeight\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"EdgeConnectivityGradientWeight\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight, declaration := `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight, declaration := `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u_1)] }
  .evidence


noncomputable def Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration_1.sourceLaw.{u_1} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u_1 + 1, u_1, 0, u_1, 0} (Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.arena.) (Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration.{u_1}).actual

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration_1.sourceBridgeFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"EdgeConnectivityGradientWeight\",\"edge_connected_iff_gradient_weight\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"EdgeConnectivityGradientWeight\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight, declaration := `D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.edge_connected_iff_gradient_weight, part := .type, path := [], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight, declaration := `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u_1)] }
  (Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration.{u_1}).bridge

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration_1.observation0.{u_1} : {V : Type u_1} →
  (G : SimpleGraph.{u_1} V) →
    [Fintype.{u_1} (@Set.Elem.{u_1} (Sym2.{u_1} V) (@SimpleGraph.edgeSet.{u_1} V G))] →
      (k : Nat) →
        (x : V → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
          (@Exists.{u_1 + 1} V fun (u : V) =>
              @Exists.{u_1 + 1} V fun (v : V) =>
                @Ne.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (x u) (x v)) →
            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u_1 + 1, u_1, 0, u_1, 0}
              D5.S3.ConceptDynamics.InformationEscape.GraphCutRegistrationTemplates.graphGradientSignature.{u_1}
              PUnit.unit.{1} (@Sigma.mk.{u_1 + 1, u_1} (Type u_1) (fun (V : Type u_1) => SimpleGraph.{u_1} V) V G) :=
  fun {V : Type u_1} (G : SimpleGraph.{u_1} V)
    [Fintype.{u_1} (@Set.Elem.{u_1} (Sym2.{u_1} V) (@SimpleGraph.edgeSet.{u_1} V G))] (k : Nat)
    (x : V → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (a :
      @Exists.{u_1 + 1} V fun (u : V) =>
        @Exists.{u_1 + 1} V fun (v : V) =>
          @Ne.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (x u) (x v)) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u_1 + 1, u_1, 0, u_1, 0}
    D5.S3.ConceptDynamics.InformationEscape.GraphCutRegistrationTemplates.graphGradientSignature.{u_1}
    Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.actual.{u_1} PUnit.unit.{1}
    (@Sigma.mk.{u_1 + 1, u_1} (Type u_1) (fun (V : Type u_1) => SimpleGraph.{u_1} V) V G) x

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration_1.observationFact0.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"EdgeConnectivityGradientWeight\",\"edge_connected_iff_gradient_weight\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"body\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"EdgeConnectivityGradientWeight\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight, declaration := `D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.edge_connected_iff_gradient_weight, part := .type, path := [.body, .body, .body, .body, .argument, .body, .body, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight, declaration := `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration_1.observation0, part := .value, path := [], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration_1.varyingLawInput.{u_1} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration_1.canonicalArenaOperand.{u_1})
noncomputable def Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration_1.varyingLaw.{u_1}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"EdgeConnectivityGradientWeight\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}"

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration_1.statementExclusion.{u_1} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"EdgeConnectivityGradientWeight\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"EdgeConnectivityGradientWeight\",\"edge_connected_iff_gradient_weight\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u_1\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight, declaration := `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u_1)] }
  statementLocation := { owner := `D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight, declaration := `D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.edge_connected_iff_gradient_weight, part := .type, path := [], levels := [(.param `u_1)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration.{u_1}).actual (Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration.{u_1}).variation.2.choose (Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration.{u_1}).variation.1 (Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration.{u_1}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration_1.descriptorFact.{u_1} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"EdgeConnectivityGradientWeight\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Fourier\",\"CharacterSelection\",\"EdgeConnectivityGradientWeight\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u_1\"]]]}"))
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight, declaration := `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u_1)] }
  { owner := `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight, declaration := `Reg.D5.S3.Fourier.CharacterSelection.EdgeConnectivityGradientWeight.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u_1)] }
  (by first | rfl | (ext <;> rfl))
