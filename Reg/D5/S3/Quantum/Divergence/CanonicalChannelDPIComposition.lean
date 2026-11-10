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
  Law R :=
    (∀ {a : Type u} {b : Type v} {c : Type w}
      [Fintype a] [DecidableEq a] [Nonempty a]
      [Fintype b] [DecidableEq b] [Nonempty b]
      [Fintype c] [DecidableEq c] [Nonempty c]
      (second : QuantumChannel b c) (first : QuantumChannel a b)
      (rho sigma : DensityState a),
      R.readout ()
        (extendedQuantumRelativeEntropy ((second.comp first).mapState rho)
            ((second.comp first).mapState sigma),
          extendedQuantumRelativeEntropy rho sigma) true) ∧
    R.readout () (0, 1) true

theorem actual_law : arena.{u,v,w}.Law actual := by
  constructor
  · intro a b c ia da na ib db nb ic dc nc second first rho sigma
    simpa [actual, realize] using
      (extended_quantum_relative_entropy_comp_dpi second first rho sigma)
  · simp [actual, realize]

theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  simpa [rejected, realize] using h.2

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
      have hh := (And.left h) second first rho sigma
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
