import D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift
import Mathlib.Order.ULift
import Mathlib.Algebra.Order.Ring.InjSurj

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

namespace Conformal

universe v
open scoped Matrix

private noncomputable instance liftedRealStrict : IsStrictOrderedRing (ULift.{u} ℝ) :=
  Function.Injective.isStrictOrderedRing
    ULift.down rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) .rfl .rfl

/-- All varying scalar, label and matrix parameters stay in the source family. -/
structure Parameters where
  F : Type u
  field : Field F
  order : LinearOrder F
  strict : @IsStrictOrderedRing F field.toSemiring order.toPartialOrder
  E : Type v
  finite : Fintype E
  m : ℕ
  A : Matrix (Fin m) E F

attribute [local instance] Parameters.field Parameters.order Parameters.strict Parameters.finite

abbrev signature : Signature where
  Params := Parameters.{u,v}
  State p := p.E → p.F
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin p.m → p.F
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ p c => p.A *ᵥ c) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law O := ∀ {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {E : Type v} [Fintype E] {m : ℕ}
    (A : Matrix (Fin m) E F) (x : E → F) (e : E),
    A *ᵥ x = 0 → x e ≠ 0 →
    ∃ c : E → F,
      O.readout () ⟨F, inferInstance, inferInstance, inferInstance, E, inferInstance, m, A⟩ c = 0 ∧
      c e ≠ 0 ∧
      (∀ i, c i = 0 ∨ SignType.sign (c i) = SignType.sign (x i)) ∧
      (∀ w : E → F, A *ᵥ w = 0 → w ≠ 0 →
        Function.support w ⊆ Function.support c →
        Function.support w = Function.support c)

abbrev sourceScope := type_of% (@OrderedField.signConformalGlobalKernelCircuit.{u,v})

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let A : Matrix (Fin 1) (ULift.{v} Unit) (ULift.{u} ℝ) := 0
  let x : ULift.{v} Unit → ULift.{u} ℝ := 1
  obtain ⟨c, hc, _⟩ := h A x (ULift.up ()) (by simp [A]) (by simp [x])
  have he := congrFun hc (0 : Fin 1)
  exact one_ne_zero he

private theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro _
  let A : Matrix (Fin 1) (ULift.{v} Unit) (ULift.{u} ℝ) := fun _ _ => 1
  let p : Parameters.{u,v} :=
    ⟨ULift.{u} ℝ, inferInstance, inferInstance, inferInstance,
      ULift.{v} Unit, inferInstance, 1, A⟩
  refine ⟨p, 0, 1, ?_⟩
  intro he
  have he' := congrFun he (0 : Fin 1)
  norm_num [actual, realize, p, A, Matrix.mulVec, dotProduct] at he'
  exact zero_ne_one he'

def family : Registration arena.{u,v} sourceScope.{u,v} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@OrderedField.signConformalGlobalKernelCircuit.{u,v}, rejected, rejected_law⟩
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
      (@OrderedField.signConformalGlobalKernelCircuit.{u,v})
      (Realization signature.{u,v}) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit.OrderedField.signConformalGlobalKernelCircuit.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit.Conformal.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p c => p.A *ᵥ c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit
    definition := none
    coordinates := #[0, 4, 6, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 12
      functionOperand := false
      stateOperand := some #["arg", "fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Conformal

namespace Decomposition

universe v
open scoped BigOperators Matrix
open _root_.D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit.OrderedField

private noncomputable instance liftedRealStrict : IsStrictOrderedRing (ULift.{u} ℝ) :=
  Function.Injective.isStrictOrderedRing
    ULift.down rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) .rfl .rfl

structure Parameters where
  F : Type u
  field : Field F
  order : LinearOrder F
  strict : @IsStrictOrderedRing F field.toSemiring order.toPartialOrder
  E : Type v
  finite : Fintype E
  m : ℕ
  A : Matrix (Fin m) E F
  n : ℕ
  j : Fin n

attribute [local instance] Parameters.field Parameters.order Parameters.strict Parameters.finite

abbrev signature : Signature where
  Params := Parameters.{u,v}
  State p := Fin p.n → p.E → p.F
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin p.m → p.F
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ p c => p.A *ᵥ c p.j) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law O := ∀ {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {E : Type v} [Fintype E] {m : ℕ}
    (A : Matrix (Fin m) E F) (x : E → F), A *ᵥ x = 0 →
    ∃ (n : ℕ) (c : Fin n → (E → F)),
      (∑ j, c j) = x ∧ LinearIndependent F c ∧ n ≤ (support x).card ∧
      n ≤ Module.finrank F (LinearMap.ker (Matrix.mulVecLin A)) ∧
      ∀ j, c j ≠ 0 ∧
        O.readout () ⟨F, inferInstance, inferInstance, inferInstance,
          E, inferInstance, m, A, n, j⟩ c = 0 ∧
        (∀ i, c j i = 0 ∨ SignType.sign (c j i) = SignType.sign (x i)) ∧
        (∀ w : E → F, A *ᵥ w = 0 → w ≠ 0 →
          Function.support w ⊆ Function.support (c j) →
          Function.support w = Function.support (c j))

abbrev sourceScope := type_of% (@signConformalGlobalKernelCircuitDecomposition.{u,v})

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let A : Matrix (Fin 1) (ULift.{v} Unit) (ULift.{u} ℝ) := 0
  let x : ULift.{v} Unit → ULift.{u} ℝ := 1
  obtain ⟨n, c, hs, _, _, _, hc⟩ := h A x (by simp [A])
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    have he := congrFun hs (ULift.up ())
    simp [x] at he
  have he := congrFun (hc ⟨0, hn⟩).2.1 (0 : Fin 1)
  exact one_ne_zero he

private theorem dependence : ObservationalDependence signature.{u,v} actual := by
  intro _
  let A : Matrix (Fin 1) (ULift.{v} Unit) (ULift.{u} ℝ) := fun _ _ => 1
  let p : Parameters.{u,v} :=
    ⟨ULift.{u} ℝ, inferInstance, inferInstance, inferInstance,
      ULift.{v} Unit, inferInstance, 1, A, 1, 0⟩
  refine ⟨p, 0, 1, ?_⟩
  intro he
  have he' := congrFun he (0 : Fin 1)
  norm_num [actual, realize, p, A, Matrix.mulVec, dotProduct] at he'
  exact zero_ne_one he'

def family : Registration arena.{u,v} sourceScope.{u,v} where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@signConformalGlobalKernelCircuitDecomposition.{u,v}, rejected, rejected_law⟩
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
      (@signConformalGlobalKernelCircuitDecomposition.{u,v})
      (Realization signature.{u,v}) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit.OrderedField.signConformalGlobalKernelCircuitDecomposition.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit.Decomposition.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p c => p.A *ᵥ c p.j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5, 6, 7, 10, 12]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "body",
        "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Decomposition
end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.NonnegativeKernelCircuit
