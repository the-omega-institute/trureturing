import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeOriginalReconstructionBridge
import Reg.Support.DependentFamily

/-! The exact original-coordinate classification uses native finiteness as its readout. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.Observer
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeOriginalReconstructionBridge
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns (Pattern)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSymbolicFiniteForcing (canonicalSolution)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.CompletionHomogeneousFixedPoints
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedFreeExtension
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeAffineImageSaturation
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeEffectiveImageGuard
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeImageSaturationInterface
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeOriginalReconstructionBridge
noncomputable section


abbrev rigiditySignature : Signature where
  Params := Nat
  State q := CompletionTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ q := Pattern (q + 1)
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev rigidityActual : Realization rigiditySignature :=
  realize rigiditySignature (fun _ h X => cutoff (h + 1) X) (fun e => nomatch e)
abbrev rigidityRejected : Realization rigiditySignature :=
  realize rigiditySignature (fun _ _ _ => .inl true) (fun e => nomatch e)

abbrev rigidityArena : Arena where
  signature := rigiditySignature
  Law A := ∀ {n k m r : Nat} (I : EpochInput n k m)
    (s : Fin m → Nat) (valid : Potential I s) (mode : EffectiveMode (functionalInput I s))
    (R : Fin r → Expression k m) (p : Fin n → Nat)
    (passing : (originalImageGuard (functionalInput I s) mode).holds (environment p)),
    OriginalAdmissible I p (canonicalOriginal I s valid mode p passing) ∧
    ∀ i : Fin r,
      (IsFinite (evaluate (ranks I.base p) (canonicalOriginal I s valid mode p passing) (R i)) ↔
        i ∈ finiteReconstructions I s mode R) ∧
      (i ∈ finiteReconstructions I s mode R →
        ∃ g : Source,
          evaluate (ranks I.base p) (canonicalOriginal I s valid mode p passing) (R i) = embed g ∧
          ∀ v, OriginalAdmissible I p v →
            EffectiveInMode (functionalInput I s) mode p (imageValues s v) →
            evaluate (ranks I.base p) v (R i) = embed g) ∧
      (∀ h, originalPrefixProgram I s mode p R h i = A.readout () h
        (evaluate (ranks I.base p) (canonicalOriginal I s valid mode p passing) (R i)))

private theorem rigidity_actual : rigidityArena.Law rigidityActual := by
  simpa only [rigidityArena, rigidityActual, realize, decide_eq_true_eq] using (@original_classification_rigidity_prefix)

private theorem rigidity_rejected : ¬ rigidityArena.Law rigidityRejected := by
  intro law
  let I : EpochInput 0 0 0 := {
    base := {
      equations := Fin.elim0
      filters := []
      indices := Fin.elim0
      guard := .qf .truth }
    headPower := Fin.elim0 }
  let s : Fin 0 → Nat := Fin.elim0
  have valid : Potential I s := by intro i; exact Fin.elim0 i
  let mode : EffectiveMode (functionalInput I s) := fun i => Fin.elim0 i.val
  let p : Fin 0 → Nat := Fin.elim0
  have passing : (originalImageGuard (functionalInput I s) mode).holds (environment p) := by
    apply ((original_effective_image_guard (functionalInput I s) mode p).1).mpr
    constructor
    · exact ⟨rfl, fun j => Fin.elim0 j⟩
    · intro E r hr
      simp [functionalInput, I] at hr
  let R : Fin 1 → Expression 0 0 := fun _ => .ground (.of false)
  have correct := ((original_classification_rigidity_prefix I s valid mode R p passing).2 0).2.2 0
  have bad := ((law I s valid mode R p passing).2 0).2.2 0
  rw [correct] at bad
  change (Sum.inl false : Pattern 1) = Sum.inl true at bad
  cases bad

def rigidityEvidence : Registration rigidityArena (type_of% (@original_classification_rigidity_prefix)) where
  actual := rigidityActual
  bridge := by simp only [rigidityArena, rigidityActual, realize, decide_eq_true_eq]
  variation := ⟨rigidity_actual, rigidityRejected, rigidity_rejected⟩
  sensitivity := ⟨fun i => ⟨rigidityRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rigidity_rejected⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨0, leaf true, leaf false, ?_⟩
    intro h
    cases h

noncomputable def rigidityRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_classification_rigidity_prefix) (Realization rigiditySignature) (rigiditySignature.Params → Type) Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeOriginalReconstructionBridge.original_classification_rigidity_prefix.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeOriginalReconstructionBridge.rigidityEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨rigidityArena⟩
  objectArena := .source ⟨rigidityArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rigidityArena ⟨rigidityEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rigiditySignature (fun _ h X => cutoff (h + 1) X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeOriginalReconstructionBridge
    definition := none
    coordinates := #[12]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms rigidityEvidence

def emptyEpoch : EpochInput 0 0 0 where
  base := {
    equations := Fin.elim0
    filters := []
    indices := Fin.elim0
    guard := .qf .truth }
  headPower := Fin.elim0

def emptyPotential : Fin 0 → Nat := Fin.elim0

theorem empty_valid : Potential emptyEpoch emptyPotential := by
  intro i
  exact Fin.elim0 i

def emptyMode : EffectiveMode (functionalInput emptyEpoch emptyPotential) :=
  fun i => Fin.elim0 i.val

def emptyParameters : Fin 0 → Nat := Fin.elim0

theorem empty_passing :
    (originalImageGuard (functionalInput emptyEpoch emptyPotential) emptyMode).holds
      (environment emptyParameters) := by
  apply ((original_effective_image_guard _ emptyMode emptyParameters).1).mpr
  constructor
  · exact ⟨rfl, fun j => Fin.elim0 j⟩
  · intro E r hr
    simp [functionalInput, emptyEpoch] at hr

abbrev canonicalSignature : Signature where
  Params := Σ m : Nat, Fin m → Nat
  State _ := CompletionTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := CompletionTree
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev canonicalActual : Realization canonicalSignature :=
  realize canonicalSignature (fun _ q X => rho^[commonShift q.2] X) (fun e => nomatch e)
abbrev canonicalRejected : Realization canonicalSignature :=
  realize canonicalSignature (fun _ _ _ => leaf true) (fun e => nomatch e)

abbrev canonicalArena : Arena where
  signature := canonicalSignature
  Law A := ∀ {n k m r : Nat} (I : EpochInput n k m)
    (s : Fin m → Nat) (valid : Potential I s) (mode : EffectiveMode (functionalInput I s))
    (p : Fin n → Nat)
    (passing : (originalImageGuard (functionalInput I s) mode).holds (environment p))
    (R : Fin r → Expression k m) (i : Fin r),
    CompletionPositiveDriftRegion.value (tokenKind k) (tokenRank (ranks I.base p))
      (canonicalSolution (canonicalSystem I s mode) (tokenKind k) (tokenRank (ranks I.base p)))
      (reconstructionImages I s R i) =
      A.readout () ⟨m, s⟩ (evaluate (ranks I.base p)
        (canonicalOriginal I s valid mode p passing) (R i))

private theorem canonical_actual : canonicalArena.Law canonicalActual := by
  simpa only [canonicalArena, canonicalActual, realize, decide_eq_true_eq] using (@canonical_reconstruction_image)

private theorem canonical_rejected : ¬ canonicalArena.Law canonicalRejected := by
  intro law
  let R : Fin 1 → Expression 0 0 := fun _ => .ground (.of false)
  have bad := law emptyEpoch emptyPotential empty_valid emptyMode emptyParameters empty_passing R 0
  rw [canonical_reconstruction_image emptyEpoch emptyPotential empty_valid emptyMode
    emptyParameters empty_passing R 0] at bad
  change leaf false = leaf true at bad
  have tags := congrArg (fun X => (PFunctor.M.dest X).1) bad
  cases tags

def canonicalEvidence : Registration canonicalArena (type_of% (@canonical_reconstruction_image)) where
  actual := canonicalActual
  bridge := by simp only [canonicalArena, canonicalActual, realize, decide_eq_true_eq]
  variation := ⟨canonical_actual, canonicalRejected, canonical_rejected⟩
  sensitivity := ⟨fun i => ⟨canonicalRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, canonical_rejected⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨⟨0, Fin.elim0⟩, leaf true, leaf false, ?_⟩
    intro h
    have tags := congrArg (fun X => (PFunctor.M.dest X).1) h
    cases tags

noncomputable def canonicalRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@canonical_reconstruction_image) (Realization canonicalSignature) (canonicalSignature.Params → Type) Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeOriginalReconstructionBridge.canonical_reconstruction_image.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeOriginalReconstructionBridge.canonicalEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨canonicalArena⟩
  objectArena := .source ⟨canonicalArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source canonicalArena ⟨canonicalEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize canonicalSignature (fun _ q X => rho^[commonShift q.2] X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeOriginalReconstructionBridge
    definition := none
    coordinates := #[2, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms canonicalEvidence


abbrev transportSignature : Signature where
  Params := Σ k : Nat, Σ m : Nat, (Fin m → Nat) × (Fin k → Nat) × Expression k m
  State q := Fin q.2.1 → CompletionTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ q := CompletionTree
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev transportActual : Realization transportSignature :=
  realize transportSignature (fun _ q w => evaluate q.2.2.2.1 w (transport q.2.2.1 (commonShift q.2.2.1) q.2.2.2.2)) (fun e => nomatch e)
abbrev transportRejected : Realization transportSignature :=
  realize transportSignature (fun _ _ _ => leaf true) (fun e => nomatch e)

abbrev transportArena : Arena where
  signature := transportSignature
  Law A := ∀ {k m : Nat} (s : Fin m → Nat)
    (p : Fin k → Nat) (v : Fin m → CompletionTree) (E : Expression k m),
    A.readout () ⟨k, m, s, p, E⟩ (imageValues s v) =
      rho^[commonShift s] (evaluate p v E) ∧
    NativeImage (commonShift s)
      (evaluate p (imageValues s v) (transport s (commonShift s) E))

private theorem transport_actual : transportArena.Law transportActual := by
  simpa only [transportArena, transportActual, realize, decide_eq_true_eq] using (@reconstruction_transport)

private theorem transport_rejected : ¬ transportArena.Law transportRejected := by
  intro law
  let E : Expression 0 0 := .ground (.of false)
  have bad := (law Fin.elim0 Fin.elim0 Fin.elim0 E).1
  change leaf true = leaf false at bad
  have tags := congrArg (fun X => (PFunctor.M.dest X).1) bad
  cases tags

def transportEvidence : Registration transportArena (type_of% (@reconstruction_transport)) where
  actual := transportActual
  bridge := by simp only [transportArena, transportActual, realize, decide_eq_true_eq]
  variation := ⟨transport_actual, transportRejected, transport_rejected⟩
  sensitivity := ⟨fun i => ⟨transportRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, transport_rejected⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨⟨0, 1, (fun _ => 0), Fin.elim0, .var 0 0⟩,
      (fun _ => leaf true), (fun _ => leaf false), ?_⟩
    intro h
    have tags := congrArg (fun X => (PFunctor.M.dest X).1) h
    cases tags

noncomputable def transportRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@reconstruction_transport) (Realization transportSignature) (transportSignature.Params → Type) Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeOriginalReconstructionBridge.reconstruction_transport.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeOriginalReconstructionBridge.transportEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨transportArena⟩
  objectArena := .source ⟨transportArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source transportArena ⟨transportEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize transportSignature (fun _ q w => evaluate q.2.2.2.1 w (transport q.2.2.1 (commonShift q.2.2.1) q.2.2.2.2)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeOriginalReconstructionBridge
    definition := none
    coordinates := #[0, 1, 2, 3, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms transportEvidence


abbrev epochSignature : Signature where
  Params := Σ m : Nat, Fin m → Nat
  State q := Fin q.1 → CompletionTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ q := Fin q.1 → CompletionTree
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev epochActual : Realization epochSignature :=
  realize epochSignature (fun _ q v => imageValues q.2 v) (fun e => nomatch e)
abbrev epochRejected : Realization epochSignature :=
  realize epochSignature (fun _ _ _ _ => leaf true) (fun e => nomatch e)

abbrev epochArena : Arena where
  signature := epochSignature
  Law A := ∀ {n k m : Nat} (I : EpochInput n k m)
    (s : Fin m → Nat) (valid : Potential I s) (p : Fin n → Nat)
    (w : Fin m → CompletionTree),
    (Legal (functionalInput I s) p ∧ SourceSatisfies (functionalInput I s) p w ∧
      SourcePasses (functionalInput I s) p w) ↔
    ∃! v, OriginalAdmissible I p v ∧ A.readout () ⟨m, s⟩ v = w

private theorem epoch_actual : epochArena.Law epochActual := by
  simpa only [epochArena, epochActual, realize, decide_eq_true_eq] using (@epoch_solution_correspondence)

private theorem epoch_rejected : ¬ epochArena.Law epochRejected := by
  intro law
  let I : EpochInput 0 0 1 := {
    base := {
      equations := fun _ => none
      filters := []
      indices := Fin.elim0
      guard := .qf .truth }
    headPower := fun _ => 0 }
  let s : Fin 1 → Nat := fun _ => 0
  have valid : Potential I s := by
    intro i E he
    cases he
  let p : Fin 0 → Nat := Fin.elim0
  let w : Fin 1 → CompletionTree := fun _ => leaf false
  have admissible : OriginalAdmissible I p w := by
    refine ⟨⟨rfl, fun j => Fin.elim0 j⟩, ?_, ?_⟩
    · intro i E he
      cases he
    · intro E r hr
      cases hr
  have original : ∃! v, OriginalAdmissible I p v ∧ imageValues s v = w := by
    refine ⟨w, ⟨admissible, rfl⟩, ?_⟩
    intro u hu
    exact hu.2
  have lhs := (epoch_solution_correspondence I s valid p w).mpr original
  obtain ⟨v, hv, _⟩ := (law I s valid p w).mp lhs
  have bad := congrFun hv.2 0
  change leaf true = leaf false at bad
  have tags := congrArg (fun X => (PFunctor.M.dest X).1) bad
  cases tags

def epochEvidence : Registration epochArena (type_of% (@epoch_solution_correspondence)) where
  actual := epochActual
  bridge := by simp only [epochArena, epochActual, realize, decide_eq_true_eq]
  variation := ⟨epoch_actual, epochRejected, epoch_rejected⟩
  sensitivity := ⟨fun i => ⟨epochRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, epoch_rejected⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨⟨1, fun _ => 0⟩, (fun _ => leaf true), (fun _ => leaf false), ?_⟩
    intro h
    have bad := congrFun h 0
    have tags := congrArg (fun X => (PFunctor.M.dest X).1) bad
    cases tags

noncomputable def epochRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@epoch_solution_correspondence) (Realization epochSignature) (epochSignature.Params → Type) Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeOriginalReconstructionBridge.epoch_solution_correspondence.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeOriginalReconstructionBridge.epochEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨epochArena⟩
  objectArena := .source ⟨epochArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source epochArena ⟨epochEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize epochSignature (fun _ q v => imageValues q.2 v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeOriginalReconstructionBridge
    definition := none
    coordinates := #[2, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms epochEvidence

end
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeOriginalReconstructionBridge
