import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Divergence.CanonicalChannelDPIComposition
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u v w

open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
open _root_.D5.S3.Quantum.Divergence.CanonicalChannelDPIComposition
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped CStarAlgebra ComplexOrder MatrixOrder

namespace Reg.D5.S3.Quantum.Divergence.CanonicalChannelDPIComposition

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (WithTop ℝ × WithTop ℝ) (fun _ => Bool) (fun _ => Prop)

def actual : Realization signature :=
  realize signature (fun _ p state => state = true ∧ p.1 ≤ p.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {a : Type u} {b : Type v} {c : Type w}
    [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b]
    [Fintype c] [DecidableEq c] [Nonempty c]
    (second : QuantumChannel b c) (first : QuantumChannel a b)
    (rho sigma : DensityState a),
    R.readout ()
      (extendedQuantumRelativeEntropy ((second.comp first).mapState rho)
          ((second.comp first).mapState sigma),
        extendedQuantumRelativeEntropy rho sigma) true

private noncomputable def unitChannel {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Unique α] [Unique β] : QuantumChannel α β :=
  Classical.choose (D5.S3.Quantum.Foundation.FiniteKrausChannel.finite_kraus_quantum_channel
    (fun _ : Unit => (fun _ _ => (1 : ℂ))) (by
      ext i j
      have hij : i = j := Subsingleton.elim _ _
      subst j
      simp only [Matrix.sum_apply]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
      simp [Fintype.sum_unique]))

private noncomputable def unitState {α : Type*}
    [Fintype α] [DecidableEq α] [Unique α] : DensityState α := by
  refine ⟨CStarMatrix.ofMatrix (1 : Matrix α α ℂ), ?_, ?_⟩
  · exact (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      ((Matrix.PosSemidef.one : (1 : Matrix α α ℂ).PosSemidef).nonneg))
  · change Matrix.trace (1 : Matrix α α ℂ) = 1
    simp [Matrix.trace, Fintype.sum_unique]

theorem actual_law : arena.{u,v,w}.Law actual := by
  intro a b c ia da na ib db nb ic dc nc second first rho sigma
  simpa [actual, realize] using
    (extended_quantum_relative_entropy_comp_dpi second first rho sigma)

theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let a := ULift.{u} Unit
  let b := ULift.{v} Unit
  let c := ULift.{w} Unit
  have hf := h (a := a) (b := b) (c := c)
    (unitChannel (α := b) (β := c)) (unitChannel (α := a) (β := b))
      (unitState (α := a)) (unitState (α := a))
  exact hf

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(0, 1), false, true, ?_⟩
  simp [actual, realize]

def family : Registration arena.{u,v,w}
    (type_of% (@extended_quantum_relative_entropy_comp_dpi.{u,v,w})) where
  actual := actual
  bridge := by
    constructor
    · intro _
      exact actual_law
    · intro h
      intro a b c ia da na ib db nb ic dc nc second first rho sigma
      have hh := h (a := a) (b := b) (c := c) second first rho sigma
      simpa [actual, realize] using hh
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@extended_quantum_relative_entropy_comp_dpi.{u,v,w})
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.CanonicalChannelDPIComposition.unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.CanonicalChannelDPIComposition.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p state => state = true ∧ p.1 ≤ p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration

end Reg.D5.S3.Quantum.Divergence.CanonicalChannelDPIComposition
