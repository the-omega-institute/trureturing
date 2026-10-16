import D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCofactor
import Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/- The dependent-family construction mirrors the terminal cone equivalence with its
whole original telescope. The actual law, equivalence bridge, variation, sensitivity
and observational dependence are Lean proof terms. The sourceSelection descriptor
has unresolved native binding (IE-C050 ClosedTruthReadout, unclassified_form);
this registration is not declared_validated.
The unfinished audit for this equivalence, circuit_cofactor_complete,
circuit_deleted_cols_linearIndependent and kernel_cross_identity is disclosed at
https://github.com/the-omega-institute/trureturing/issues/17856.
The other three interfaces still lack complete faithful four-slot registrations.
-/

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCofactor

open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCofactor
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u
noncomputable section

namespace Hull

abbrev signature : Signature :=
  _root_.Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit.Hull.signature.{u}

def actual : Realization signature.{u} :=
  _root_.Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit.Hull.actual.{u}

def rejected : Realization signature.{u} :=
  _root_.Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit.Hull.rejected.{u}

abbrev arena : Arena where
  signature := signature
  Law O := ∀ {J : Type u} [Fintype J] {m : ℕ} (B : Matrix (Fin m) J ℝ) (x : J → ℝ),
    InKernel B x ↔ x ∈ O.readout () J (cofactorCandidates B)

abbrev sourceScope := type_of% (@nonnegKernel_iff_mem_hull_cofactorCandidates.{u})

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let x : ULift.{u} Unit → ℝ := fun _ => 1
  have hx : InKernel (fun (_ : Fin 0) (_ : ULift.{u} Unit) => (0 : ℝ)) x :=
    ⟨fun _ => zero_le_one, fun r => Fin.elim0 r⟩
  have he := (h (J := ULift.{u} Unit) (m := 0) _ x).mp hx
  change x ∈ (⊥ : PointedCone ℝ (ULift.{u} Unit → ℝ)) at he
  have hz : x = 0 := by simpa using he
  have he0 := congrFun hz (ULift.up ())
  norm_num [x] at he0

private theorem dependence : ObservationalDependence signature.{u} actual.{u} :=
  _root_.Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit.Hull.family.dependence

def family : Registration arena.{u} sourceScope.{u} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@nonnegKernel_iff_mem_hull_cofactorCandidates.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@nonnegKernel_iff_mem_hull_cofactorCandidates.{u})
      (Realization signature.{u}) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCofactor.nonnegKernel_iff_mem_hull_cofactorCandidates.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCofactor.Hull.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCofactor
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Hull
end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCofactor
