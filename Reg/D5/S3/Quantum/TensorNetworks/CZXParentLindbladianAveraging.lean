import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAveraging
import Reg.Support.DependentFamily

/-! Source-bound audits of coordinate averaging and its pointwise formulas. -/

namespace Reg.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAveraging
open _root_.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAveraging
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u_1 u_2

/-- Observe the source function at a binary configuration. -/
abbrev evaluationSignature : Signature where
  Params := Σ V : Type u_1, Σ n : ℕ, ((Fin n → Fin 2) → V)
  State p := Fin p.2.1 → Fin 2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def evaluationActual : Realization evaluationSignature :=
  realize evaluationSignature (fun _ p x => p.2.2 x) (fun e => Empty.elim e)

def evaluationRejected : Realization evaluationSignature :=
  realize evaluationSignature (fun _ p _ => p.2.2 (fun _ => 0)) (fun e => Empty.elim e)

theorem evaluationDependence :
    ObservationalDependence evaluationSignature.{u_1} evaluationActual := by
  intro i
  refine ⟨⟨ULift.{u_1} (Fin 2), ⟨1, fun x => ⟨x 0⟩⟩⟩,
    (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have he := congrArg (fun z : ULift.{u_1} (Fin 2) => z.down.val) h
  change (0 : ℕ) = 1 at he
  exact Nat.zero_ne_one he

/-- The operator-valued readout retains the source algebra dictionaries. -/
abbrev operatorSignature : Signature where
  Params := Σ V : Type u_1, Σ g : AddCommGroup V, Σ _ : @Module ℂ V _ g.toAddCommMonoid, ℕ
  State p := Finset (Fin p.2.2.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := by
    letI := p.2.1
    letI := p.2.2.1
    exact Module.End ℂ ((Fin p.2.2.2 → Fin 2) → p.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def operatorActual : Realization operatorSignature :=
  realize operatorSignature (fun _ p s => by
    letI := p.2.1
    letI := p.2.2.1
    exact avg p.2.2.2 s) (fun e => Empty.elim e)

def operatorRejected : Realization operatorSignature :=
  realize operatorSignature (fun _ p _ => by
    letI := p.2.1
    letI := p.2.2.1
    exact 0) (fun e => Empty.elim e)

private abbrev ProbeSpace := ULift.{u_1} Unit → ℂ

private def probe (x : Fin 2 → Fin 2) : ProbeSpace.{u_1} := fun _ => (x 0).val

theorem operatorDependence :
    ObservationalDependence operatorSignature.{u_1} operatorActual := by
  intro i
  refine ⟨⟨ProbeSpace.{u_1}, ⟨inferInstance, ⟨inferInstance, 2⟩⟩⟩,
    ∅, {0, 1}, ?_⟩
  intro h
  have he := congrArg (fun T => T probe (fun _ => 0) ⟨()⟩) h
  change (avg 2 ∅ probe (fun _ => 0)) ⟨()⟩ =
    (avg 2 {0, 1} probe (fun _ => 0)) ⟨()⟩ at he
  rw [avg_empty, avg_pair_apply 2 0 1 (by decide)] at he
  norm_num [probe, Fin.sum_univ_two, Function.update_apply] at he

private def spike {V : Type u_1} [AddCommGroup V] [Module ℂ V] (n : ℕ) :
    Module.End ℂ ((Fin n → Fin 2) → V) where
  toFun f x := if x = (fun _ => 0) then f x else 0
  map_add' := by
    intro f g
    funext x
    by_cases hx : x = (fun _ => 0) <;> simp [hx]
  map_smul' := by
    intro c f
    funext x
    by_cases hx : x = (fun _ => 0) <;> simp [hx]

def commutationRejected : Realization operatorSignature :=
  realize operatorSignature (fun _ p _ => by
    letI := p.2.1
    letI := p.2.2.1
    exact spike p.2.2.2) (fun e => Empty.elim e)

namespace Empty

abbrev arena : Arena where
  signature := operatorSignature.{u_1}
  Law r := ∀ {V : Type u_1} [AddCommGroup V] [Module ℂ V] (n : ℕ),
    r.readout () ⟨V, ⟨inferInstance, ⟨inferInstance, n⟩⟩⟩ ∅ = 1

theorem rejected_law : ¬ arena.{u_1}.Law operatorRejected := by
  intro h
  have he := h (V := ProbeSpace.{u_1}) 0
  have hz := congrArg (fun T => T (fun _ _ => 1) (fun i => Fin.elim0 i) ⟨()⟩) he
  change (0 : ℂ) = 1 at hz
  exact zero_ne_one hz

def source_registration : Registration arena.{u_1} (type_of% @avg_empty.{u_1}) where
  actual := operatorActual
  bridge := Iff.rfl
  variation := ⟨avg_empty, operatorRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨operatorRejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := operatorDependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@avg_empty.{u_1})
      (Realization operatorSignature.{u_1}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAveraging.Empty.unit
  realizationName :=
    `Reg.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAveraging.Empty.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize operatorSignature (fun _ p s => by
    letI := p.2.1
    letI := p.2.2.1
    exact avg p.2.2.2 s) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAveraging
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Empty

namespace Composition

/-- Observe the source union as its second coordinate varies. -/
abbrev signature : Signature where
  Params := Σ n : ℕ, Finset (Fin n)
  State p := Finset (Fin p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Finset (Fin p.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p t => p.2 ∪ t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {V : Type u_1} [AddCommGroup V] [Module ℂ V]
    (n : ℕ) (s t : Finset (Fin n)),
    avg (V := V) n s * avg n t = avg n (r.readout () ⟨n, s⟩ t)

theorem rejected_law : ¬ arena.{u_1}.Law rejected := by
  intro h
  have he := h (V := ProbeSpace.{u_1}) 2 {0, 1} ∅
  rw [avg_empty, mul_one] at he
  have hz := congrArg (fun T => T probe (fun _ => 0) ⟨()⟩) he
  change avg 2 {0, 1} probe (fun _ => 0) ⟨()⟩ = avg 2 ∅ probe (fun _ => 0) ⟨()⟩ at hz
  rw [avg_empty, avg_pair_apply 2 0 1 (by decide)] at hz
  norm_num [probe, Fin.sum_univ_two, Function.update_apply] at hz

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, ∅⟩, ∅, {0}, ?_⟩
  simp [actual, realize]

def source_registration : Registration arena.{u_1} (type_of% @avg_mul.{u_1}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨avg_mul, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@avg_mul.{u_1})
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAveraging.Composition.unit
  realizationName :=
    `Reg.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAveraging.Composition.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p t => p.2 ∪ t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAveraging
    definition := none
    coordinates := #[3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Composition

namespace Commutation

abbrev arena : Arena where
  signature := operatorSignature.{u_1}
  Law r := ∀ {V : Type u_1} [AddCommGroup V] [Module ℂ V]
    (n : ℕ) (s t : Finset (Fin n)),
    Commute (r.readout () ⟨V, ⟨inferInstance, ⟨inferInstance, n⟩⟩⟩ s) (avg n t)

theorem rejected_law : ¬ arena.{u_1}.Law commutationRejected := by
  intro h
  have he := h (V := ProbeSpace.{u_1}) 2 ∅ {0, 1}
  change spike 2 * avg 2 {0, 1} = avg 2 {0, 1} * spike 2 at he
  have hz := congrArg (fun T => T (fun _ _ => 1) (fun _ => 0) ⟨()⟩) he
  change spike 2 (avg 2 {0, 1} (fun _ => (1 : ProbeSpace.{u_1}))) (fun _ => 0) ⟨()⟩ =
    avg 2 {0, 1} (spike 2 (fun _ => (1 : ProbeSpace.{u_1}))) (fun _ => 0) ⟨()⟩ at hz
  simp only [spike, LinearMap.coe_mk, AddHom.coe_mk] at hz
  rw [avg_pair_apply 2 0 1 (by decide), avg_pair_apply 2 0 1 (by decide)] at hz
  norm_num [spike, Fin.sum_univ_two, Function.update_apply, funext_iff, Fin.forall_fin_two] at hz
  norm_num [Finset.filter_eq'] at hz

def source_registration : Registration arena.{u_1} (type_of% @avg_commute.{u_1}) where
  actual := operatorActual
  bridge := Iff.rfl
  variation := ⟨avg_commute, commutationRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨commutationRejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
        rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := operatorDependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@avg_commute.{u_1})
      (Realization operatorSignature.{u_1}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAveraging.Commutation.unit
  realizationName :=
    `Reg.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAveraging.Commutation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize operatorSignature (fun _ p s => by
    letI := p.2.1
    letI := p.2.2.1
    exact avg p.2.2.2 s) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAveraging
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Commutation

namespace Pair

abbrev arena : Arena where
  signature := evaluationSignature.{u_1}
  Law r := ∀ {V : Type u_1} [AddCommGroup V] [Module ℂ V]
    (n : ℕ) (k l : Fin n) (_h : k ≠ l)
    (f : (Fin n → Fin 2) → V) (x : Fin n → Fin 2),
    avg n {k, l} f x = (4 : ℂ)⁻¹ • ∑ b : Fin 2, ∑ c : Fin 2,
      r.readout () ⟨V, ⟨n, f⟩⟩ (Function.update (Function.update x k b) l c)

theorem rejected_law : ¬ arena.{u_1}.Law evaluationRejected := by
  intro h
  have he := h (V := ProbeSpace.{u_1}) 2 0 1 (by decide) probe (fun _ => 0)
  rw [avg_pair_apply 2 0 1 (by decide)] at he
  have hzero : probe (fun _ => 0) = (0 : ProbeSpace.{u_1}) := by
    funext z
    simp [probe]
  simp only [evaluationRejected, realize, hzero] at he
  have hz := congrFun he ⟨()⟩
  norm_num [probe, Fin.sum_univ_two, Function.update_apply] at hz

def source_registration : Registration arena.{u_1} (type_of% @avg_pair_apply.{u_1}) where
  actual := realize evaluationSignature
    (fun _ p x => p.2.2 x) (fun e => Empty.elim e)
  bridge := Iff.rfl
  variation := ⟨avg_pair_apply, evaluationRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨evaluationRejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
        rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := evaluationDependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@avg_pair_apply.{u_1})
      (Realization evaluationSignature.{u_1}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAveraging.Pair.unit
  realizationName :=
    `Reg.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAveraging.Pair.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize evaluationSignature
    (fun _ p x => p.2.2 x) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAveraging
    definition := none
    coordinates := #[0, 3, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg",
        "arg", "arg", "body", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Pair

namespace Naturality

abbrev arena : Arena where
  signature := evaluationSignature.{u_1}
  Law r := ∀ {V : Type u_1} {W : Type u_2} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (n : ℕ) (s : Finset (Fin n)) (l : V →ₗ[ℂ] W)
    (f : (Fin n → Fin 2) → V) (x : Fin n → Fin 2),
    l (avg n s f x) = avg n s (fun y => l (r.readout () ⟨V, ⟨n, f⟩⟩ y)) x

theorem rejected_law : ¬ arena.{u_1,u_2}.Law evaluationRejected := by
  intro h
  let f : (Fin 1 → Fin 2) → ProbeSpace.{u_1} := fun x _ => (x 0).val
  let l : ProbeSpace.{u_1} →ₗ[ℂ] ProbeSpace.{u_2} :=
    { toFun := fun z _ => z ⟨()⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have he := h 1 ∅ l f (fun _ => 1)
  rw [avg_empty, avg_empty] at he
  have hz := congrFun he ⟨()⟩
  norm_num [l, f, evaluationRejected, realize] at hz

def source_registration : Registration arena.{u_1,u_2} (type_of% @avg_map.{u_1,u_2}) where
  actual := realize evaluationSignature
    (fun _ p x => p.2.2 x) (fun e => Empty.elim e)
  bridge := Iff.rfl
  variation := ⟨avg_map, evaluationRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨evaluationRejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
        rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := evaluationDependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@avg_map.{u_1,u_2})
      (Realization evaluationSignature.{u_1}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAveraging.Naturality.unit
  realizationName :=
    `Reg.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAveraging.Naturality.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize evaluationSignature
    (fun _ p x => p.2.2 x) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAveraging
    definition := none
    coordinates := #[0, 6, 9]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg", "fn", "arg", "body", "arg"]
      stateBinder := 11
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Naturality

namespace Full

abbrev arena : Arena where
  signature := evaluationSignature.{u_1}
  Law r := ∀ {V : Type u_1} [AddCommGroup V] [Module ℂ V] (n : ℕ)
    (f : (Fin n → Fin 2) → V) (x : Fin n → Fin 2),
    avg n Finset.univ f x = ((2 : ℂ) ^ n)⁻¹ • ∑ y : Fin n → Fin 2,
      r.readout () ⟨V, ⟨n, f⟩⟩ y

theorem rejected_law : ¬ arena.{u_1}.Law evaluationRejected := by
  intro h
  have he := h (V := ProbeSpace.{u_1}) 2 probe (fun _ => 0)
  have hs : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  rw [hs, avg_pair_apply 2 0 1 (by decide)] at he
  have hzero : probe (fun _ => 0) = (0 : ProbeSpace.{u_1}) := by
    funext z
    simp [probe]
  simp only [evaluationRejected, realize, hzero] at he
  have hz := congrFun he ⟨()⟩
  norm_num [probe, Fin.sum_univ_two, Function.update_apply] at hz

def source_registration : Registration arena.{u_1} (type_of% @avg_univ.{u_1}) where
  actual := realize evaluationSignature
    (fun _ p x => p.2.2 x) (fun e => Empty.elim e)
  bridge := Iff.rfl
  variation := ⟨avg_univ, evaluationRejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨evaluationRejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
        rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := evaluationDependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@avg_univ.{u_1})
      (Realization evaluationSignature.{u_1}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAveraging.Full.unit
  realizationName :=
    `Reg.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAveraging.Full.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize evaluationSignature
    (fun _ p x => p.2.2 x) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAveraging
    definition := none
    coordinates := #[0, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "arg", "body"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Full

end
end Reg.D5.S3.Quantum.TensorNetworks.CZXParentLindbladianAveraging
