import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction
import Reg.Support.DependentFamily
import Reg.Support.FiniteSectorSingleton

open _root_.D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality
open _root_.D5.S3.Quantum.Entanglement.SectorSchmidtEncoding
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Matrix Kronecker InnerProductSpace

noncomputable section
namespace Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction
universe u
namespace Kraus

abbrev signature : Signature where
  Params := Type u
  State := fun b => CStarMatrix b b ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ b => Matrix b b ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ X => CStarMatrix.ofMatrix.symm X) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => fun _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law R :=
    (∀ {a b : Type u} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
      (channel : QuantumChannel a b),
      ∃ K : (b × a) → Matrix b a ℂ,
        (∑ k, (K k).conjTranspose * K k) = 1 ∧
        ∀ rho : Matrix a a ℂ,
          R.readout () b
            (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix rho)) =
            ∑ k, K k * rho * (K k).conjTranspose) ∧
    (∀ {a b : Type u} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
      (channel : QuantumChannel a b),
      ∃ V : Matrix ((b × a) × b) a ℂ,
        V.conjTranspose * V = 1 ∧
        ∀ rho : Matrix a a ℂ,
          partialTraceLeft (V * rho * V.conjTranspose) =
            CStarMatrix.ofMatrix.symm
              (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix rho)))

theorem actual_law : arena.{u}.Law actual := channel_kraus_stinespring

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let K : Unit → Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ := fun _ => 1
  have hK : (∑ i, (K i).conjTranspose * K i) = 1 := by simp [K]
  obtain ⟨channel, _⟩ := finite_kraus_quantum_channel K hK
  obtain ⟨L, _, hL⟩ := h.1 channel
  have hz := congrFun (congrFun (hL 0) (⟨()⟩ : ULift.{u} Unit)) ⟨()⟩
  simpa [rejected, realize] using hz

/-- The complementary Stinespring intervention excludes every dilation witness. -/
theorem rejected_stinespring_telescope : ¬
    (∀ {a b : Type u} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
      (_channel : QuantumChannel a b),
      ∃ V : Matrix ((b × a) × b) a ℂ,
        V.conjTranspose * V = 1 ∧
        ∀ rho : Matrix a a ℂ,
          partialTraceLeft (V * rho * V.conjTranspose) = fun _ _ => (1 : ℂ)) := by
  intro h
  let K : Unit → Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ := fun _ => 1
  have hK : (∑ i, (K i).conjTranspose * K i) = 1 := by simp [K]
  obtain ⟨channel, _⟩ := finite_kraus_quantum_channel K hK
  obtain ⟨V, _, hV⟩ := h channel
  have hz := congrFun (congrFun (hV 0) (⟨()⟩ : ULift.{u} Unit)) ⟨()⟩
  simpa [partialTraceLeft] using hz

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨ULift.{u} Unit, CStarMatrix.ofMatrix (fun _ _ => 0),
    CStarMatrix.ofMatrix (fun _ _ => 1), ?_⟩
  intro h
  have he := congrFun (congrFun h (⟨()⟩ : ULift.{u} Unit)) ⟨()⟩
  exact zero_ne_one he

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.channel_kraus_stinespring.{u}) (type_of% (realize.{u + 1, u, 0, u, 0} signature.{u}
    (fun _ _ X => CStarMatrix.ofMatrix.symm X) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Entanglement") "FiniteSectorChannelOptimality") "channel_kraus_stinespring") "Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction/Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u})⟩,
  objectArena := .source ⟨(arena.{u})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u}) ⟨(registration.{u})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{u + 1, u, 0, u, 0} signature.{u}
    (fun _ _ X => CStarMatrix.ofMatrix.symm X) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, definition := none, coordinates := #[1], readouts := #[{ path := #["fn", "arg", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, declaration := `D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.channel_kraus_stinespring, part := .type, path := [], levels := [.param `u] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u] }], facts := [`Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration_1.observationFact0, `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration_1.anchorEnumeration }


#print axioms registration
#print axioms rejected_stinespring_telescope
end Kraus

namespace Encoding
abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := ULift.{u} Unit
  finiteRole := Fintype.ofSubsingleton ⟨()⟩
  nonemptyRole := inferInstance
  Output := fun _ _ => ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ x => (x : ℂ)) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {Sector : Type u} [Fintype Sector] [DecidableEq Sector]
    {spectralSize : ℕ} [Nonempty Sector] (M : Model Sector spectralSize),
    ∃ encoding : EncodingChannels M,
    ∃ splitting : QuantumChannel (SourceLocal (Coord := Fin spectralSize) M.d) (TargetLocal M.d),
    ∃ splittingJoint : QuantumChannel
        (SourceLocal (Coord := Fin spectralSize) M.d × SourceLocal (Coord := Fin spectralSize) M.d)
        (TargetLocal M.d × TargetLocal M.d),
      (∀ left right : QuantumChannel (SourceLocal (Coord := Fin spectralSize) M.d) (TargetLocal M.d),
        ∃ joint : QuantumChannel
          (SourceLocal (Coord := Fin spectralSize) M.d × SourceLocal (Coord := Fin spectralSize) M.d)
          (TargetLocal M.d × TargetLocal M.d), TensorRealization left right joint) ∧
      (∀ (m : ℕ) (weight : Fin m → ℝ), weight ∈ stdSimplex ℝ (Fin m) →
        ∀ left right : Fin m → QuantumChannel
          (SourceLocal (Coord := Fin spectralSize) M.d) (TargetLocal M.d),
        ∃ joint : QuantumChannel
          (SourceLocal (Coord := Fin spectralSize) M.d × SourceLocal (Coord := Fin spectralSize) M.d)
          (TargetLocal M.d × TargetLocal M.d), MixtureRealization weight left right joint) ∧
      TensorRealization splitting splitting splittingJoint ∧
      (∀ X : Matrix (SourceLocal (Coord := Fin spectralSize) M.d)
          (SourceLocal (Coord := Fin spectralSize) M.d) ℂ,
        CStarMatrix.ofMatrix.symm
          (splitting.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
        fun b c => ∑ j : Fin spectralSize, X ⟨b.1, (b.2, j)⟩ ⟨c.1, (c.2, j)⟩) ∧
      (∀ X : Matrix Sector Sector ℂ,
        CStarMatrix.ofMatrix.symm
          ((splittingJoint.comp encoding.source).toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
        targetEncoding M.d * (Matrix.of fun s t => R.readout ⟨()⟩ () (kernel M s t) * X s t) *
          (targetEncoding M.d)ᴴ)

theorem actual_law : arena.{u}.Law actual := by
  intro Sector _ _ spectralSize _ M
  exact physical_encoding M

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let M := Reg.Support.FiniteSectorSingleton.model (ULift.{u} Unit)
  obtain ⟨encoding, splitting, splittingJoint, _, _, _, _, haction⟩ := h M
  let C := splittingJoint.comp encoding.source
  have hz := haction (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ)
  have ht := C.trace_preserving (CStarMatrix.ofMatrix (1 : Matrix (ULift.{u} Unit) _ ℂ))
  have he := congrArg Matrix.trace hz
  change Matrix.trace (C.toCompletelyPositiveMap (CStarMatrix.ofMatrix 1)) = _ at he
  rw [ht] at he
  norm_num [rejected, realize, Matrix.of_apply, Matrix.trace, Matrix.mul_apply,
    Matrix.diag_apply, CStarMatrix.ofMatrix_apply] at he
  change (1 : ℂ) = 0 at he
  exact one_ne_zero he

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def registration : Registration arena.{u} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim (ULift.{u} Unit) _ j i)).elim
    · intro i
      exact nomatch i
  dependence := dependence

noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.physical_encoding.{u}) (type_of% (realize.{0, 0, u, 0, 0} signature.{u} (fun _ _ x => (x : ℂ)) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Entanglement") "FiniteSectorChannelOptimality") "physical_encoding") "Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction/Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena.{u})⟩,
  objectArena := .source ⟨(arena.{u})⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{u}) ⟨(registration.{u})⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, u, 0, 0} signature.{u} (fun _ _ x => (x : ℂ)) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "body", "arg", "fn", "arg", "arg", "arg", "body", "body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, declaration := `D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.physical_encoding, part := .type, path := [], levels := [.param `u] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u] },
    { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u] }], facts := [`Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration_2.canonicalArenaFact, `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration_2.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration_2.sourceBridgeFact, `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration_2.observationFact0, `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration_2.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration_2.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration_2.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration_2.anchorEnumeration }


#print axioms registration
end Encoding
end Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction


noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration_2.canonicalArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, u, 0, 0} :=
  Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.arena.{u}
noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration_2.canonicalArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorPhysicalConstruction\",\"Encoding\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorPhysicalConstruction\",\"Encoding\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration_2.canonicalObjectArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, u, 0, 0} :=
  Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.arena.{u}
noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration_2.canonicalObjectArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorPhysicalConstruction\",\"Encoding\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorPhysicalConstruction\",\"Encoding\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration_1.canonicalArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u + 1, u, 0, u, 0} :=
  Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.arena.{u}
noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration_1.canonicalArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorPhysicalConstruction\",\"Kraus\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorPhysicalConstruction\",\"Kraus\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration_1.canonicalObjectArenaOperand.{u} : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{u + 1, u, 0, u, 0} :=
  Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.arena.{u}
noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration_1.canonicalObjectArenaFact.{u} : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorPhysicalConstruction\",\"Kraus\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorPhysicalConstruction\",\"Kraus\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [(.param `u)] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration_2.sourceLaw.{u} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, u, 0, 0}
  Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.arena.{u}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, u, 0, 0}
    Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.arena.{u}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, u, 0, 0}
      Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.arena.{u}
      Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.actual.{u})
    Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration.{u})

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration_2.sourceBridgeFact.{u} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorChannelOptimality\",\"physical_encoding\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorPhysicalConstruction\",\"Encoding\",\"registration_2\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, declaration := `D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.physical_encoding, part := .type, path := [], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration_2.sourceLaw, part := .value, path := [], levels := [(.param `u)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, u, 0, 0}
  Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.arena.{u}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, u, 0, 0}
    Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.arena.{u}
    Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.actual.{u})
  Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration.{u})

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration_2.roleEnumeration.{u} : LeanInformationAudit.Contract.FiniteEnumeration (ULift.{u, 0} Unit) where
  values := [@ULift.up.{u, 0} Unit Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration_2.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration_2.observation0.{u} : {Sector : Type u} →
  [inst : Fintype.{u} Sector] →
    [inst_1 : DecidableEq.{u + 1} Sector] →
      {spectralSize : Nat} →
        [Nonempty.{u + 1} Sector] →
          (M : @D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.{u} Sector inst spectralSize) →
            (encoding :
                @D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.EncodingChannels.{u} Sector inst inst_1
                  spectralSize M) →
              (splitting :
                  @D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.{u, u}
                    (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin spectralSize)
                      (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize
                        M))
                    (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                      (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize
                        M))
                    (@Sigma.instFintype.{u, 0} Sector
                      (fun (s : Sector) =>
                        Prod.{0, 0}
                          (Fin
                            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                              spectralSize M s))
                          (Fin spectralSize))
                      (fun (i : Sector) =>
                        @instFintypeProd.{0, 0}
                          (Fin
                            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                              spectralSize M i))
                          (Fin spectralSize)
                          (Fin.fintype
                            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                              spectralSize M i))
                          (Fin.fintype spectralSize))
                      inst)
                    (fun
                        (a b :
                          @D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin spectralSize)
                            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                              spectralSize M)) =>
                      @Sigma.instDecidableEqSigma.{u, 0} Sector
                        (fun (s : Sector) =>
                          Prod.{0, 0}
                            (Fin
                              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                spectralSize M s))
                            (Fin spectralSize))
                        inst_1
                        (fun (a : Sector)
                            (a_1 b :
                              Prod.{0, 0}
                                (Fin
                                  (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                    spectralSize M a))
                                (Fin spectralSize)) =>
                          @instDecidableEqProd.{0, 0}
                            (Fin
                              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                spectralSize M a))
                            (Fin spectralSize)
                            ((fun (a : Sector) =>
                                instDecidableEqFin
                                  (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                    spectralSize M a))
                              a)
                            (instDecidableEqFin spectralSize) a_1 b)
                        a b)
                    (@Sigma.instFintype.{u, 0} Sector
                      (fun (s : Sector) =>
                        Fin
                          (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                            spectralSize M s))
                      (fun (i : Sector) =>
                        Fin.fintype
                          (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                            spectralSize M i))
                      inst)
                    fun
                      (a b :
                        @D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                          (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                            spectralSize M)) =>
                    @Sigma.instDecidableEqSigma.{u, 0} Sector
                      (fun (s : Sector) =>
                        Fin
                          (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                            spectralSize M s))
                      inst_1
                      (fun (a : Sector) =>
                        instDecidableEqFin
                          (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                            spectralSize M a))
                      a b) →
                (splittingJoint :
                    @D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.{u, u}
                      (Prod.{u, u}
                        (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin spectralSize)
                          (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                            spectralSize M))
                        (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin spectralSize)
                          (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                            spectralSize M)))
                      (Prod.{u, u}
                        (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                          (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                            spectralSize M))
                        (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                          (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                            spectralSize M)))
                      (@instFintypeProd.{u, u}
                        (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin spectralSize)
                          (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                            spectralSize M))
                        (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin spectralSize)
                          (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                            spectralSize M))
                        (@Sigma.instFintype.{u, 0} Sector
                          (fun (s : Sector) =>
                            Prod.{0, 0}
                              (Fin
                                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                  spectralSize M s))
                              (Fin spectralSize))
                          (fun (i : Sector) =>
                            @instFintypeProd.{0, 0}
                              (Fin
                                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                  spectralSize M i))
                              (Fin spectralSize)
                              (Fin.fintype
                                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                  spectralSize M i))
                              (Fin.fintype spectralSize))
                          inst)
                        (@Sigma.instFintype.{u, 0} Sector
                          (fun (s : Sector) =>
                            Prod.{0, 0}
                              (Fin
                                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                  spectralSize M s))
                              (Fin spectralSize))
                          (fun (i : Sector) =>
                            @instFintypeProd.{0, 0}
                              (Fin
                                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                  spectralSize M i))
                              (Fin spectralSize)
                              (Fin.fintype
                                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                  spectralSize M i))
                              (Fin.fintype spectralSize))
                          inst))
                      (fun
                          (a b :
                            Prod.{u, u}
                              (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector
                                (Fin spectralSize)
                                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                  spectralSize M))
                              (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector
                                (Fin spectralSize)
                                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                  spectralSize M))) =>
                        @instDecidableEqProd.{u, u}
                          (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector
                            (Fin spectralSize)
                            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                              spectralSize M))
                          (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector
                            (Fin spectralSize)
                            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                              spectralSize M))
                          (fun
                              (a b :
                                @D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector
                                  (Fin spectralSize)
                                  (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                    spectralSize M)) =>
                            @Sigma.instDecidableEqSigma.{u, 0} Sector
                              (fun (s : Sector) =>
                                Prod.{0, 0}
                                  (Fin
                                    (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                      spectralSize M s))
                                  (Fin spectralSize))
                              inst_1
                              (fun (a : Sector)
                                  (a_1 b :
                                    Prod.{0, 0}
                                      (Fin
                                        (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector
                                          inst spectralSize M a))
                                      (Fin spectralSize)) =>
                                @instDecidableEqProd.{0, 0}
                                  (Fin
                                    (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                      spectralSize M a))
                                  (Fin spectralSize)
                                  ((fun (a : Sector) =>
                                      instDecidableEqFin
                                        (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector
                                          inst spectralSize M a))
                                    a)
                                  (instDecidableEqFin spectralSize) a_1 b)
                              a b)
                          (fun
                              (a b :
                                @D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector
                                  (Fin spectralSize)
                                  (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                    spectralSize M)) =>
                            @Sigma.instDecidableEqSigma.{u, 0} Sector
                              (fun (s : Sector) =>
                                Prod.{0, 0}
                                  (Fin
                                    (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                      spectralSize M s))
                                  (Fin spectralSize))
                              inst_1
                              (fun (a : Sector)
                                  (a_1 b :
                                    Prod.{0, 0}
                                      (Fin
                                        (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector
                                          inst spectralSize M a))
                                      (Fin spectralSize)) =>
                                @instDecidableEqProd.{0, 0}
                                  (Fin
                                    (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                      spectralSize M a))
                                  (Fin spectralSize)
                                  ((fun (a : Sector) =>
                                      instDecidableEqFin
                                        (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector
                                          inst spectralSize M a))
                                    a)
                                  (instDecidableEqFin spectralSize) a_1 b)
                              a b)
                          a b)
                      (@instFintypeProd.{u, u}
                        (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                          (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                            spectralSize M))
                        (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                          (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                            spectralSize M))
                        (@Sigma.instFintype.{u, 0} Sector
                          (fun (s : Sector) =>
                            Fin
                              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                spectralSize M s))
                          (fun (i : Sector) =>
                            Fin.fintype
                              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                spectralSize M i))
                          inst)
                        (@Sigma.instFintype.{u, 0} Sector
                          (fun (s : Sector) =>
                            Fin
                              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                spectralSize M s))
                          (fun (i : Sector) =>
                            Fin.fintype
                              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                spectralSize M i))
                          inst))
                      fun
                        (a b :
                          Prod.{u, u}
                            (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                spectralSize M))
                            (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                spectralSize M))) =>
                      @instDecidableEqProd.{u, u}
                        (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                          (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                            spectralSize M))
                        (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                          (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                            spectralSize M))
                        (fun
                            (a b :
                              @D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                  spectralSize M)) =>
                          @Sigma.instDecidableEqSigma.{u, 0} Sector
                            (fun (s : Sector) =>
                              Fin
                                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                  spectralSize M s))
                            inst_1
                            (fun (a : Sector) =>
                              instDecidableEqFin
                                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                  spectralSize M a))
                            a b)
                        (fun
                            (a b :
                              @D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                  spectralSize M)) =>
                          @Sigma.instDecidableEqSigma.{u, 0} Sector
                            (fun (s : Sector) =>
                              Fin
                                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                  spectralSize M s))
                            inst_1
                            (fun (a : Sector) =>
                              instDecidableEqFin
                                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                                  spectralSize M a))
                            a b)
                        a b) →
                  (X : Matrix.{u, u, 0} Sector Sector Complex) →
                    (s t : Sector) →
                      D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, u, 0, 0}
                        Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.signature.{u}
                        (@ULift.up.{u, 0} Unit Unit.unit) PUnit.unit.{1} :=
  fun {Sector : Type u} [inst : Fintype.{u} Sector] [DecidableEq.{u + 1} Sector] {spectralSize : Nat}
    [Nonempty.{u + 1} Sector]
    (M : @D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.{u} Sector inst spectralSize)
    (encoding :
      @D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.EncodingChannels.{u} Sector inst inst_1 spectralSize M)
    (splitting :
      @D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.{u, u}
        (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin spectralSize)
          (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M))
        (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
          (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M))
        (@Sigma.instFintype.{u, 0} Sector
          (fun (s : Sector) =>
            Prod.{0, 0}
              (Fin (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M s))
              (Fin spectralSize))
          (fun (i : Sector) =>
            @instFintypeProd.{0, 0}
              (Fin (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M i))
              (Fin spectralSize)
              (Fin.fintype
                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M i))
              (Fin.fintype spectralSize))
          inst)
        (fun
            (a b :
              @D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin spectralSize)
                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M)) =>
          @Sigma.instDecidableEqSigma.{u, 0} Sector
            (fun (s : Sector) =>
              Prod.{0, 0}
                (Fin
                  (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M s))
                (Fin spectralSize))
            inst_1
            (fun (a : Sector)
                (a_1 b :
                  Prod.{0, 0}
                    (Fin
                      (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M
                        a))
                    (Fin spectralSize)) =>
              @instDecidableEqProd.{0, 0}
                (Fin
                  (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M a))
                (Fin spectralSize)
                ((fun (a : Sector) =>
                    instDecidableEqFin
                      (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M
                        a))
                  a)
                (instDecidableEqFin spectralSize) a_1 b)
            a b)
        (@Sigma.instFintype.{u, 0} Sector
          (fun (s : Sector) =>
            Fin (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M s))
          (fun (i : Sector) =>
            Fin.fintype
              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M i))
          inst)
        fun
          (a b :
            @D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M)) =>
        @Sigma.instDecidableEqSigma.{u, 0} Sector
          (fun (s : Sector) =>
            Fin (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M s))
          inst_1
          (fun (a : Sector) =>
            instDecidableEqFin
              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M a))
          a b)
    (splittingJoint :
      @D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.{u, u}
        (Prod.{u, u}
          (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin spectralSize)
            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M))
          (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin spectralSize)
            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M)))
        (Prod.{u, u}
          (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M))
          (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M)))
        (@instFintypeProd.{u, u}
          (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin spectralSize)
            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M))
          (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin spectralSize)
            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M))
          (@Sigma.instFintype.{u, 0} Sector
            (fun (s : Sector) =>
              Prod.{0, 0}
                (Fin
                  (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M s))
                (Fin spectralSize))
            (fun (i : Sector) =>
              @instFintypeProd.{0, 0}
                (Fin
                  (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M i))
                (Fin spectralSize)
                (Fin.fintype
                  (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M i))
                (Fin.fintype spectralSize))
            inst)
          (@Sigma.instFintype.{u, 0} Sector
            (fun (s : Sector) =>
              Prod.{0, 0}
                (Fin
                  (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M s))
                (Fin spectralSize))
            (fun (i : Sector) =>
              @instFintypeProd.{0, 0}
                (Fin
                  (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M i))
                (Fin spectralSize)
                (Fin.fintype
                  (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M i))
                (Fin.fintype spectralSize))
            inst))
        (fun
            (a b :
              Prod.{u, u}
                (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin spectralSize)
                  (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M))
                (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin spectralSize)
                  (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize
                    M))) =>
          @instDecidableEqProd.{u, u}
            (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin spectralSize)
              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M))
            (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin spectralSize)
              (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M))
            (fun
                (a b :
                  @D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin spectralSize)
                    (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize
                      M)) =>
              @Sigma.instDecidableEqSigma.{u, 0} Sector
                (fun (s : Sector) =>
                  Prod.{0, 0}
                    (Fin
                      (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M
                        s))
                    (Fin spectralSize))
                inst_1
                (fun (a : Sector)
                    (a_1 b :
                      Prod.{0, 0}
                        (Fin
                          (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                            spectralSize M a))
                        (Fin spectralSize)) =>
                  @instDecidableEqProd.{0, 0}
                    (Fin
                      (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M
                        a))
                    (Fin spectralSize)
                    ((fun (a : Sector) =>
                        instDecidableEqFin
                          (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                            spectralSize M a))
                      a)
                    (instDecidableEqFin spectralSize) a_1 b)
                a b)
            (fun
                (a b :
                  @D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.SourceLocal.{u, 0} Sector (Fin spectralSize)
                    (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize
                      M)) =>
              @Sigma.instDecidableEqSigma.{u, 0} Sector
                (fun (s : Sector) =>
                  Prod.{0, 0}
                    (Fin
                      (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M
                        s))
                    (Fin spectralSize))
                inst_1
                (fun (a : Sector)
                    (a_1 b :
                      Prod.{0, 0}
                        (Fin
                          (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                            spectralSize M a))
                        (Fin spectralSize)) =>
                  @instDecidableEqProd.{0, 0}
                    (Fin
                      (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M
                        a))
                    (Fin spectralSize)
                    ((fun (a : Sector) =>
                        instDecidableEqFin
                          (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst
                            spectralSize M a))
                      a)
                    (instDecidableEqFin spectralSize) a_1 b)
                a b)
            a b)
        (@instFintypeProd.{u, u}
          (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M))
          (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M))
          (@Sigma.instFintype.{u, 0} Sector
            (fun (s : Sector) =>
              Fin (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M s))
            (fun (i : Sector) =>
              Fin.fintype
                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M i))
            inst)
          (@Sigma.instFintype.{u, 0} Sector
            (fun (s : Sector) =>
              Fin (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M s))
            (fun (i : Sector) =>
              Fin.fintype
                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M i))
            inst))
        fun
          (a b :
            Prod.{u, u}
              (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M))
              (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M))) =>
        @instDecidableEqProd.{u, u}
          (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M))
          (@D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
            (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M))
          (fun
              (a b :
                @D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                  (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M)) =>
            @Sigma.instDecidableEqSigma.{u, 0} Sector
              (fun (s : Sector) =>
                Fin
                  (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M s))
              inst_1
              (fun (a : Sector) =>
                instDecidableEqFin
                  (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M a))
              a b)
          (fun
              (a b :
                @D5.S3.Quantum.Entanglement.SectorSchmidtEncoding.TargetLocal.{u} Sector
                  (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M)) =>
            @Sigma.instDecidableEqSigma.{u, 0} Sector
              (fun (s : Sector) =>
                Fin
                  (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M s))
              inst_1
              (fun (a : Sector) =>
                instDecidableEqFin
                  (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.Model.d.{u} Sector inst spectralSize M a))
              a b)
          a b)
    (X : Matrix.{u, u, 0} Sector Sector Complex) (s t : Sector) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, u, 0, 0}
    Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.signature.{u}
    Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.actual.{u}
    (@ULift.up.{u, 0} Unit Unit.unit) PUnit.unit.{1}
    (@D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.kernel.{u} Sector inst spectralSize M s t)

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration_2.observationFact0.{u} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorChannelOptimality\",\"physical_encoding\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"argument\",\"argument\",\"argument\",\"body\",\"argument\",\"function\",\"argument\",\"argument\",\"argument\",\"body\",\"body\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorPhysicalConstruction\",\"Encoding\",\"registration_2\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, declaration := `D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.physical_encoding, part := .type, path := [.body, .body, .body, .body, .body, .body, .argument, .body, .argument, .body, .argument, .body, .argument, .argument, .argument, .argument, .body, .argument, .function, .argument, .argument, .argument, .body, .body, .function, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration_2.observation0, part := .value, path := [], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration_2.varyingLawInput.{u} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration_2.canonicalArenaOperand.{u})
noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration_2.varyingLaw.{u}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorPhysicalConstruction\",\"Encoding\",\"registration_2\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration_2.statementExclusion.{u} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorPhysicalConstruction\",\"Encoding\",\"registration_2\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorChannelOptimality\",\"physical_encoding\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration_2.varyingLaw, part := .value, path := [], levels := [(.param `u)] }
  statementLocation := { owner := `D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, declaration := `D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.physical_encoding, part := .type, path := [], levels := [(.param `u)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration.{u}).actual (Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration.{u}).variation.2.choose (Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration.{u}).variation.1 (Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration.{u}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration_2.descriptorFact.{u} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorPhysicalConstruction\",\"Encoding\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorPhysicalConstruction\",\"Encoding\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Encoding.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration_1.sourceLaw.{u} : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u + 1, u, 0, u, 0}
  Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.arena.{u}
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{u + 1, u, 0, u, 0}
    Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.arena.{u}
    (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u + 1, u, 0, u, 0}
      Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.arena.{u}
      Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.actual.{u})
    Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration.{u})

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration_1.sourceBridgeFact.{u} : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorChannelOptimality\",\"channel_kraus_stinespring\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorPhysicalConstruction\",\"Kraus\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, declaration := `D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.channel_kraus_stinespring, part := .type, path := [], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration_1.sourceLaw, part := .value, path := [], levels := [(.param `u)] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{u + 1, u, 0, u, 0}
  Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.arena.{u}
  (D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{u + 1, u, 0, u, 0}
    Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.arena.{u}
    Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.actual.{u})
  Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration.{u})

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration_1.observation0.{u} : {a b : Type u} →
  [inst : Fintype.{u} a] →
    [inst_1 : DecidableEq.{u + 1} a] →
      [inst_2 : Fintype.{u} b] →
        [inst_3 : DecidableEq.{u + 1} b] →
          (channel : @D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.{u, u} a b inst inst_1 inst_2 inst_3) →
            (K : Prod.{u, u} b a → Matrix.{u, u, 0} b a Complex) →
              (rho : Matrix.{u, u, 0} a a Complex) →
                D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{u + 1, u, 0, u, 0}
                  Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.signature.{u} PUnit.unit.{1} b :=
  fun {a b : Type u} [inst : Fintype.{u} a] [inst_1 : DecidableEq.{u + 1} a] [inst_2 : Fintype.{u} b]
    [inst_3 : DecidableEq.{u + 1} b]
    (channel : @D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.{u, u} a b inst inst_1 inst_2 inst_3)
    (K : Prod.{u, u} b a → Matrix.{u, u, 0} b a Complex) (rho : Matrix.{u, u, 0} a a Complex) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{u + 1, u, 0, u, 0}
    Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.signature.{u}
    Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.actual.{u} PUnit.unit.{1} b
    (@DFunLike.coe.{u + 1, u + 1, u + 1}
      (@CompletelyPositiveMap.{u, u} (CStarMatrix.{u, u, 0} a a Complex) (CStarMatrix.{u, u, 0} b b Complex)
        (@CStarMatrix.instNonUnitalCStarAlgebra.{0, u} Complex
          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
          Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) a inst)
        (@CStarMatrix.instNonUnitalCStarAlgebra.{0, u} Complex
          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
          Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) b inst_2)
        (@CStarMatrix.instPartialOrder.{0, u} Complex
          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
          Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) a inst)
        (@CStarMatrix.instPartialOrder.{0, u} Complex
          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
          Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) b inst_2)
        (@CStarMatrix.instStarOrderedRing.{0, u} Complex
          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
          Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) a inst)
        (@CStarMatrix.instStarOrderedRing.{0, u} Complex
          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
          Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) b inst_2))
      (CStarMatrix.{u, u, 0} a a Complex)
      (fun (x : CStarMatrix.{u, u, 0} a a Complex) => CStarMatrix.{u, u, 0} b b Complex)
      (@CompletelyPositiveMap.instFunLike.{u, u} (CStarMatrix.{u, u, 0} a a Complex) (CStarMatrix.{u, u, 0} b b Complex)
        (@CStarMatrix.instNonUnitalCStarAlgebra.{0, u} Complex
          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
          Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) a inst)
        (@CStarMatrix.instNonUnitalCStarAlgebra.{0, u} Complex
          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
          Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) b inst_2)
        (@CStarMatrix.instPartialOrder.{0, u} Complex
          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
          Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) a inst)
        (@CStarMatrix.instPartialOrder.{0, u} Complex
          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
          Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) b inst_2)
        (@CStarMatrix.instStarOrderedRing.{0, u} Complex
          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
          Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) a inst)
        (@CStarMatrix.instStarOrderedRing.{0, u} Complex
          (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra.{0} Complex
            (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra.{0} Complex instCommCStarAlgebraComplex))
          Complex.partialOrder (@RCLike.toStarOrderedRing.{0} Complex Complex.instRCLike) b inst_2))
      (@D5.S3.Quantum.Foundation.FiniteStateChannel.QuantumChannel.toCompletelyPositiveMap.{u, u} a b inst inst_1 inst_2
        inst_3 channel)
      (@DFunLike.coe.{max 1 (u + 1), max 1 (u + 1), max 1 (u + 1)}
        (Equiv.{max 1 (u + 1), max 1 (u + 1)} (Matrix.{u, u, 0} a a Complex) (CStarMatrix.{u, u, 0} a a Complex))
        (Matrix.{u, u, 0} a a Complex) (fun (x : Matrix.{u, u, 0} a a Complex) => CStarMatrix.{u, u, 0} a a Complex)
        (@EquivLike.toFunLike.{max 1 (u + 1), max 1 (u + 1), max 1 (u + 1)}
          (Equiv.{max 1 (u + 1), max 1 (u + 1)} (Matrix.{u, u, 0} a a Complex) (CStarMatrix.{u, u, 0} a a Complex))
          (Matrix.{u, u, 0} a a Complex) (CStarMatrix.{u, u, 0} a a Complex)
          (@Equiv.instEquivLike.{max 1 (u + 1), max 1 (u + 1)} (Matrix.{u, u, 0} a a Complex)
            (CStarMatrix.{u, u, 0} a a Complex)))
        (@CStarMatrix.ofMatrix.{u, u, 0} a a Complex) rho))

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration_1.observationFact0.{u} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorChannelOptimality\",\"channel_kraus_stinespring\"],\"part\":\"type\",\"path\":[\"function\",\"argument\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"argument\",\"body\",\"argument\",\"body\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorPhysicalConstruction\",\"Kraus\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, declaration := `D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.channel_kraus_stinespring, part := .type, path := [.function, .argument, .body, .body, .body, .body, .body, .body, .body, .argument, .body, .argument, .body, .function, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration_1.observation0, part := .value, path := [], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration_1.varyingLawInput.{u} :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration_1.canonicalArenaOperand.{u})
noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration_1.varyingLaw.{u}  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorPhysicalConstruction\",\"Kraus\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}"

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration_1.statementExclusion.{u} : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorPhysicalConstruction\",\"Kraus\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorChannelOptimality\",\"channel_kraus_stinespring\"],\"part\":\"type\",\"path\":[],\"levels\":[[\"param\",[\"u\"]]]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration_1.varyingLaw, part := .value, path := [], levels := [(.param `u)] }
  statementLocation := { owner := `D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, declaration := `D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality.channel_kraus_stinespring, part := .type, path := [], levels := [(.param `u)] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration.{u}).actual (Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration.{u}).variation.2.choose (Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration.{u}).variation.1 (Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration.{u}).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration_1.descriptorFact.{u} : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorPhysicalConstruction\",\"Kraus\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Entanglement\",\"FiniteSectorPhysicalConstruction\",\"Kraus\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[[\"param\",[\"u\"]]]}"))
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [(.param `u)] }
  { owner := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction, declaration := `Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction.Kraus.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [(.param `u)] }
  (by first | rfl | (ext <;> rfl))
