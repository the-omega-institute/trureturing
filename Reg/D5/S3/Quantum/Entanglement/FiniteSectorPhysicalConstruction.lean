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

register_information_theorem channel_kraus_stinespring in arena
  readout via (realize signature.{u}
    (fun _ _ X => CStarMatrix.ofMatrix.symm X) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction
    coordinates := #[1]
    readouts := #[{path := #["fn", "arg", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "fn", "arg"], stateOperand := some #["arg"]}] })
  escape continues (open)

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

register_information_theorem physical_encoding in arena
  readout via (realize signature.{u} (fun _ _ x => (x : ℂ)) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction
    coordinates := #[]
    readouts := #[{path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "body", "arg", "fn", "arg", "arg", "arg", "body", "body", "fn", "arg"], stateOperand := some #["arg"]}] })
  escape continues (open)

#print axioms registration
end Encoding
end Reg.D5.S3.Quantum.Entanglement.FiniteSectorPhysicalConstruction
