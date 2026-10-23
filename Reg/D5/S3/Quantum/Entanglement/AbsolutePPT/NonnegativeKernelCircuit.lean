import D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
universe u
noncomputable section

namespace Hull

abbrev signature : Signature where
  Params := Type u
  State J := Set (J → ℝ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ J := PointedCone ℝ (J → ℝ)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ s => PointedCone.hull ℝ s) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => ⊥) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law O := ∀ {J : Type u} [Fintype J] {m : ℕ} (B : Fin m → J → ℝ) (x : J → ℝ),
    InKernel B x → x ∈ O.readout () J {v | Circuit B v}

abbrev sourceScope := type_of% (@nonnegKernel_mem_hull_circuit.{u})

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let x : ULift.{u} Unit → ℝ := fun _ => 1
  have hx : InKernel (fun (_ : Fin 0) (_ : ULift.{u} Unit) => (0 : ℝ)) x :=
    ⟨fun _ => zero_le_one, fun r => Fin.elim0 r⟩
  have he := h (J := ULift.{u} Unit) (m := 0) _ x hx
  change x ∈ (⊥ : PointedCone ℝ (ULift.{u} Unit → ℝ)) at he
  have hz : x = 0 := by simpa using he
  have := congrFun hz (ULift.up ())
  norm_num [x] at this

private theorem dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro _
  let x : ULift.{u} Unit → ℝ := fun _ => 1
  refine ⟨ULift.{u} Unit, {x}, ∅, ?_⟩
  intro he
  have hx : x ∈ PointedCone.hull ℝ ({x} : Set (ULift.{u} Unit → ℝ)) :=
    PointedCone.subset_hull (Set.mem_singleton x)
  change PointedCone.hull ℝ ({x} : Set (ULift.{u} Unit → ℝ)) =
    PointedCone.hull ℝ ∅ at he
  rw [he] at hx
  have hz : x = 0 := by simpa [PointedCone.hull] using hx
  have := congrFun hz (ULift.up ())
  norm_num [x] at this

def family : Registration arena.{u} sourceScope.{u} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@nonnegKernel_mem_hull_circuit.{u}, rejected, rejected_law⟩
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
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0} (@nonnegKernel_mem_hull_circuit.{u})
      (Realization signature.{u}) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit.nonnegKernel_mem_hull_circuit.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit.Hull.family
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
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Hull

namespace Support

abbrev signature : Signature where
  Params := Type u
  State J := Finset J
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ s => s.card) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law O := ∀ {J : Type u} [Fintype J] {m : ℕ} {B : Fin m → J → ℝ} {v : J → ℝ},
    Circuit B v → O.readout () J (nzSupport v) ≤ m + 1

abbrev sourceScope := type_of% (@circuit_support_card_le.{u})

private theorem unit_circuit :
    Circuit (fun (_ : Fin 0) (_ : ULift.{u} (Fin 2)) => (0 : ℝ))
      (fun j => if j.down = 0 then (1 : ℝ) else 0) := by
  classical
  refine ⟨⟨fun j => by dsimp; split <;> norm_num, fun r => Fin.elim0 r⟩, ?_, ?_⟩
  · intro h
    have := congrFun h (ULift.up 0)
    norm_num at this
  · intro w hw hwn hsub
    have hs : nzSupport (fun j : ULift.{u} (Fin 2) => if j.down = 0 then (1 : ℝ) else 0) =
        {ULift.up 0} := by
      ext j
      rcases j with ⟨j⟩
      simp [nzSupport]
    rw [hs] at hsub ⊢
    simp only [Finset.card_singleton]
    apply Finset.card_pos.mpr
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hwn
    exact ⟨j, by simpa [nzSupport] using hj⟩

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have he := h unit_circuit
  change 2 ≤ 0 + 1 at he
  norm_num at he

private theorem dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro _
  refine ⟨ULift.{u} Unit, ∅, {ULift.up ()}, ?_⟩
  simp [actual, realize]

def family : Registration arena.{u} sourceScope.{u} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@circuit_support_card_le.{u}, rejected, rejected_law⟩
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
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0} (@circuit_support_card_le.{u}) (Realization signature.{u}) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit.circuit_support_card_le.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit.Support.family
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
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Support
end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit
