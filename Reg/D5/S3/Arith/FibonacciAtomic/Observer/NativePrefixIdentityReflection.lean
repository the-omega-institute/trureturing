import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns (Pattern Frontier fill)
open D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection

abbrev signature : Signature where
  Params := Σ m : Nat, Σ d : Fin m → Nat, (i : Fin m) → Pattern (d i)
  State p := Fin p.1 → Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := MixedExpr (Fin p.1) → Source
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => eval z) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : Nat) (d : Fin m → Nat) (p : (i : Fin m) → Pattern (d i))
    (_live : ∀ i, Nonempty (Frontier (p i))) (A B : MixedExpr (Fin m)),
    (∀ w : (i : Fin m) → Frontier (p i) → Source,
      R.readout () ⟨m,d,p⟩ (fun i => fill (p i) (w i)) A =
      R.readout () ⟨m,d,p⟩ (fun i => fill (p i) (w i)) B) →
    ∀ z : Fin m → Source, R.readout () ⟨m,d,p⟩ z A = R.readout () ⟨m,d,p⟩ z B

private theorem bridge : (type_of% (@prefix_identity_reflection)) ↔ arena.Law actual := Iff.rfl
private theorem actual_law : arena.Law actual := @prefix_identity_reflection

private def rootTag : Source → Source
  | .of b => .of b
  | .mul _ _ => .mul (.of true) (.of true)

def bad : Realization signature :=
  realize signature (fun _ _ z E => rootTag (eval z E)) (fun e => nomatch e)

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  let p : (i : Fin 1) → Pattern 1 := fun _ => Sum.inr ((),())
  let A : MixedExpr (Fin 1) := .residual 0 0
  let B : MixedExpr (Fin 1) := .ground (.mul (.of true) (.of true))
  have live : ∀ i, Nonempty (Frontier (p i)) := fun _ => ⟨Sum.inl ()⟩
  have cylinder : ∀ w : (i : Fin 1) → Frontier (p i) → Source,
      bad.readout () ⟨1,(fun _ => 1),p⟩ (fun i => fill (p i) (w i)) A =
      bad.readout () ⟨1,(fun _ => 1),p⟩ (fun i => fill (p i) (w i)) B := by
    intro w; rfl
  have no := h 1 (fun _ => 1) p live A B cylinder (fun _ => .of true)
  change FreeMagma.of true = FreeMagma.mul (.of true) (.of true) at no
  cases no

def proof : Registration arena (type_of% (@prefix_identity_reflection)) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨1,(fun _ => 0),(fun _ => ())⟩,
      (fun _ => .of true),(fun _ => .of false),?_⟩
    intro eq
    have no := congrFun eq (MixedExpr.residual 0 0)
    change FreeMagma.of true = FreeMagma.of false at no
    cases no

noncomputable def prefix_identity_reflection_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection.prefix_identity_reflection)
    (Realization signature) (Nat → Type) Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection.prefix_identity_reflection
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => eval z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","fn","arg","fn"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms prefix_identity_reflection_registration

namespace Suppliers

open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (substitution)

abbrev massSignature : Signature where
  Params := Unit
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def massActual : Realization massSignature := realize massSignature (fun _ _ => gamma) (fun e => nomatch e)
def clockActual : Realization massSignature := realize massSignature (fun _ _ => kappa) (fun e => nomatch e)
def zero : Realization massSignature := realize massSignature (fun _ _ _ => 0) (fun e => nomatch e)
def one : Realization massSignature := realize massSignature (fun _ _ _ => 1) (fun e => nomatch e)
def rootMass : Realization massSignature := realize massSignature
  (fun _ _ t => match t with | .of _ => 1 | .mul _ _ => 0) (fun e => nomatch e)
def leafClock : Realization massSignature := realize massSignature
  (fun _ _ t => match t with | .of true => 0 | _ => 1) (fun e => nomatch e)

private theorem massDependence : ObservationalDependence massSignature massActual := by
  intro i
  refine ⟨(),.of true,comb 1,?_⟩
  change gamma (.of true) ≠ gamma (comb 1)
  rw [gamma_comb]
  decide

private theorem clockDependence : ObservationalDependence massSignature clockActual := by
  intro i
  refine ⟨(),.of true,.of false,?_⟩
  change (0 : Nat) ≠ 1
  decide

abbrev gammaIterateArena : Arena where
  signature := massSignature
  Law R := ∀ (a : Nat) (t : Source),
    R.readout () () (substitution^[a] t) = R.readout () () t

private theorem gammaIterateBad : ¬ gammaIterateArena.Law leafClock := by
  intro h
  have no := h 1 (.of true)
  change (1 : Nat) = 0 at no
  exact Nat.one_ne_zero no

abbrev gammaPairArena : Arena where
  signature := massSignature
  Law R := ∀ (s t : Source),
    (0 < R.readout () () s ∨ 0 < R.readout () () t) →
    R.readout () () (.mul s t) = 1 + R.readout () () s + R.readout () () t

private theorem gammaPairBad : ¬ gammaPairArena.Law one := by
  intro h
  have no := h (.of true) (.of true) (Or.inl (by decide))
  change (1 : Nat) = 3 at no
  norm_num at no

abbrev gammaParentArena : Arena where
  signature := massSignature
  Law R := ∀ (s t : Source),
    R.readout () () s ≤ R.readout () () (.mul s t) ∧
      R.readout () () t ≤ R.readout () () (.mul s t)

private theorem gammaParentBad : ¬ gammaParentArena.Law rootMass := by
  intro h
  have no := (h (.of true) (.of true)).1
  change (1 : Nat) ≤ 0 at no
  exact Nat.not_succ_le_zero 0 no

abbrev kappaIterateArena : Arena where
  signature := massSignature
  Law R := ∀ (a : Nat) (t : Source),
    R.readout () () (substitution^[a] t) = R.readout () () t + a

private theorem kappaIterateBad : ¬ kappaIterateArena.Law zero := by
  intro h
  have no := h 1 (.of true)
  change (0 : Nat) = 1 at no
  exact Nat.zero_ne_one no

abbrev gammaCombArena : Arena where
  signature := massSignature
  Law R := ∀ r : Nat, R.readout () () (comb r) = r

private theorem gammaCombBad : ¬ gammaCombArena.Law zero := by
  intro h
  have no := h 1
  change (0 : Nat) = 1 at no
  exact Nat.zero_ne_one no

def gamma_iterate_proof : Registration gammaIterateArena (type_of% (@gamma_iterate)) where
  actual := massActual
  bridge := Iff.rfl
  variation := ⟨@gamma_iterate,leafClock,gammaIterateBad⟩
  sensitivity := ⟨fun i => ⟨leafClock,fun j h => (h (Subsingleton.elim j i)).elim,rfl,gammaIterateBad⟩,
    fun i => nomatch i⟩
  dependence := massDependence

noncomputable def gamma_iterate_registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection.gamma_iterate)
    (Realization massSignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection.Suppliers.gamma_iterate
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection.Suppliers.gamma_iterate_proof
  realizationSource := none
  generated := false
  arena := .source ⟨gammaIterateArena⟩
  objectArena := .source ⟨gammaIterateArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source gammaIterateArena ⟨gamma_iterate_proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize massSignature (fun _ _ => gamma) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","fn","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def gamma_pair_proof : Registration gammaPairArena (type_of% (@gamma_pair)) where
  actual := massActual
  bridge := Iff.rfl
  variation := ⟨@gamma_pair,one,gammaPairBad⟩
  sensitivity := ⟨fun i => ⟨one,fun j h => (h (Subsingleton.elim j i)).elim,rfl,gammaPairBad⟩,
    fun i => nomatch i⟩
  dependence := massDependence

noncomputable def gamma_pair_registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection.gamma_pair)
    (Realization massSignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection.Suppliers.gamma_pair
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection.Suppliers.gamma_pair_proof
  realizationSource := none
  generated := false
  arena := .source ⟨gammaPairArena⟩
  objectArena := .source ⟨gammaPairArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source gammaPairArena ⟨gamma_pair_proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize massSignature (fun _ _ => gamma) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","fn","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def gamma_parent_proof : Registration gammaParentArena (type_of% (@gamma_parent)) where
  actual := massActual
  bridge := Iff.rfl
  variation := ⟨@gamma_parent,rootMass,gammaParentBad⟩
  sensitivity := ⟨fun i => ⟨rootMass,fun j h => (h (Subsingleton.elim j i)).elim,rfl,gammaParentBad⟩,
    fun i => nomatch i⟩
  dependence := massDependence

noncomputable def gamma_parent_registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection.gamma_parent)
    (Realization massSignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection.Suppliers.gamma_parent
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection.Suppliers.gamma_parent_proof
  realizationSource := none
  generated := false
  arena := .source ⟨gammaParentArena⟩
  objectArena := .source ⟨gammaParentArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source gammaParentArena ⟨gamma_parent_proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize massSignature (fun _ _ => gamma) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","fn","arg","fn","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def kappa_iterate_proof : Registration kappaIterateArena (type_of% (@kappa_iterate)) where
  actual := clockActual
  bridge := Iff.rfl
  variation := ⟨@kappa_iterate,zero,kappaIterateBad⟩
  sensitivity := ⟨fun i => ⟨zero,fun j h => (h (Subsingleton.elim j i)).elim,rfl,kappaIterateBad⟩,
    fun i => nomatch i⟩
  dependence := clockDependence

noncomputable def kappa_iterate_registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection.kappa_iterate)
    (Realization massSignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection.Suppliers.kappa_iterate
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection.Suppliers.kappa_iterate_proof
  realizationSource := none
  generated := false
  arena := .source ⟨kappaIterateArena⟩
  objectArena := .source ⟨kappaIterateArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source kappaIterateArena ⟨kappa_iterate_proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize massSignature (fun _ _ => kappa) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","fn","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def gamma_comb_proof : Registration gammaCombArena (type_of% (@gamma_comb)) where
  actual := massActual
  bridge := Iff.rfl
  variation := ⟨@gamma_comb,zero,gammaCombBad⟩
  sensitivity := ⟨fun i => ⟨zero,fun j h => (h (Subsingleton.elim j i)).elim,rfl,gammaCombBad⟩,
    fun i => nomatch i⟩
  dependence := massDependence

noncomputable def gamma_comb_registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection.gamma_comb)
    (Realization massSignature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection.Suppliers.gamma_comb
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection.Suppliers.gamma_comb_proof
  realizationSource := none
  generated := false
  arena := .source ⟨gammaCombArena⟩
  objectArena := .source ⟨gammaCombArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source gammaCombArena ⟨gamma_comb_proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize massSignature (fun _ _ => gamma) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","fn","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev closedSignature : Signature where
  Params := Type
  State ι := ι → Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ ι := MixedExpr ι → Source
  Anchor := Empty
  finiteAnchor := inferInstance

def closedActual : Realization closedSignature := realize closedSignature
  (fun _ _ z => eval z) (fun e => nomatch e)

noncomputable def closedBad : Realization closedSignature := by
  classical
  exact realize closedSignature
    (fun _ ι z _ => if h : Nonempty ι then z (Classical.choice h) else .of true) (fun e => nomatch e)

abbrev closedArena : Arena where
  signature := closedSignature
  Law R := ∀ {ι : Type} (E : MixedExpr ι), active E = false →
    ∀ (z v : ι → Source), R.readout () ι z E = R.readout () ι v E

private theorem closedBadLaw : ¬ closedArena.Law closedBad := by
  intro h
  have no := @h Unit (.ground (.of true)) rfl (fun _ => .of true) (fun _ => .of false)
  simp only [closedBad,realize,dif_pos (inferInstance : Nonempty Unit)] at no
  cases no

def eval_closed_proof : Registration closedArena (type_of% (@eval_closed)) where
  actual := closedActual
  bridge := Iff.rfl
  variation := ⟨@eval_closed,closedBad,closedBadLaw⟩
  sensitivity := ⟨fun i => ⟨closedBad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,closedBadLaw⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨Unit,(fun _ => .of true),(fun _ => .of false),?_⟩
    intro eq
    have no := congrFun eq (.residual 0 ())
    cases no

noncomputable def eval_closed_registration : LeanInformationAudit.Contract.Registration.{1,1,1,0,0,0,1,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection.eval_closed)
    (Realization closedSignature) (Type → Type) Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection.Suppliers.eval_closed
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection.Suppliers.eval_closed_proof
  realizationSource := none
  generated := false
  arena := .source ⟨closedArena⟩
  objectArena := .source ⟨closedArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source closedArena ⟨eval_closed_proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize closedSignature (fun _ _ z => eval z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","fn","arg","fn"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Suppliers

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection
