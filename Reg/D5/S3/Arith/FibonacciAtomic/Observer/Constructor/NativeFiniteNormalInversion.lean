import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFiniteNormalInversion
import Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeOriginalReconstructionBridge
import Reg.Support.DependentFamily

/-! Finite native inverses retain their exact source telescopes under observation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteNormalInversion
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeOriginalReconstructionBridge
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.CompletionHomogeneousFixedPoints
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedFreeExtension
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeAffineImageSaturation
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeEffectiveImageGuard
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeImageSaturationInterface
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSymbolicFiniteForcing (FiniteExpression)
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeOriginalReconstructionBridge
  (emptyEpoch emptyPotential empty_valid emptyMode emptyParameters empty_passing)
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFiniteNormalInversion
noncomputable section

abbrev codeSignature : Signature where
  Params := Nat
  State _ := Code
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option Code
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev codeActual : Realization codeSignature :=
  realize codeSignature (fun _ t C => inverseCode t C) (fun e => nomatch e)
abbrev codeRejected : Realization codeSignature :=
  realize codeSignature (fun _ _ _ => none) (fun e => nomatch e)

abbrev codeArena : Arena where
  signature := codeSignature
  Law A := ∀ (t : Nat) (g : Source)
    (image : NativeImage t (embed g)),
    Normal (encode g) ∧ expand (encode g) = g ∧
    ∃! D : Code, A.readout () t (encode g) = some D ∧ Normal D ∧
      substitution^[t] (expand D) = g

private theorem code_actual : codeArena.Law codeActual := by
  exact (@finite_normal_inverse)

private theorem code_rejected : ¬ codeArena.Law codeRejected := by
  intro law
  have h := law 0 (.of true) ⟨embed (.of true), rfl⟩
  obtain ⟨D, hd, _⟩ := h.2.2
  have impossible : (none : Option Code) = some D := hd.1
  cases impossible

def codeEvidence : Registration codeArena (type_of% (@finite_normal_inverse)) where
  actual := codeActual
  bridge := Iff.rfl
  variation := ⟨code_actual, codeRejected, code_rejected⟩
  sensitivity := ⟨fun i => ⟨codeRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, code_rejected⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨0, .of 0, .of 1, ?_⟩
    intro h
    cases h

noncomputable def codeRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_normal_inverse) (Realization codeSignature) (Nat → Type) Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteNormalInversion.finite_normal_inverse.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFiniteNormalInversion.codeEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨codeArena⟩
  objectArena := .source ⟨codeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source codeArena ⟨codeEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize codeSignature (fun _ t C => inverseCode t C) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFiniteNormalInversion
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms codeEvidence

abbrev rankSignature : Signature where
  Params := Nat
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option Nat
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev rankActual : Realization rankSignature :=
  realize rankSignature (fun _ t n => rankInverse t n) (fun e => nomatch e)
abbrev rankRejected : Realization rankSignature :=
  realize rankSignature (fun _ _ _ => none) (fun e => nomatch e)

abbrev rankArena : Arena where
  signature := rankSignature
  Law A := ∀ (t n : Nat),
    (∀ q, A.readout () t n = some q ↔ q + t = n) ∧
    ((∃ q, rankInverse t n = some q) ↔ t ≤ n) ∧
    (∀ q r, q + t = n → r + t = n → q = r)

private theorem rank_actual : rankArena.Law rankActual := by
  exact (@exact_natural_rank_inverse)

private theorem rank_rejected : ¬ rankArena.Law rankRejected := by
  intro law
  have h := ((law 0 0).1 0).mpr rfl
  have impossible : (none : Option Nat) = some 0 := h
  cases impossible

def rankEvidence : Registration rankArena (type_of% (@exact_natural_rank_inverse)) where
  actual := rankActual
  bridge := Iff.rfl
  variation := ⟨rank_actual, rankRejected, rank_rejected⟩
  sensitivity := ⟨fun i => ⟨rankRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rank_rejected⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    intro h
    cases h

noncomputable def rankRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exact_natural_rank_inverse) (Realization rankSignature) (Nat → Type) Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteNormalInversion.exact_natural_rank_inverse.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFiniteNormalInversion.rankEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨rankArena⟩
  objectArena := .source ⟨rankArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rankArena ⟨rankEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rankSignature (fun _ t n => rankInverse t n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFiniteNormalInversion
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms rankEvidence

abbrev symbolicSignature : Signature where
  Params := Nat
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Source
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev symbolicActual : Realization symbolicSignature :=
  realize symbolicSignature (fun _ t g => substitution^[t] g) (fun e => nomatch e)
abbrev symbolicRejected : Realization symbolicSignature :=
  realize symbolicSignature (fun _ _ _ => .of true) (fun e => nomatch e)

abbrev symbolicArena : Arena where
  signature := symbolicSignature
  Law A := ∀ (T : Template) (t : Nat) (xs : List Int)
    (positive : Nonnegative xs T) (image : NativeImage t (embed (expand (templateCode xs T)))),
    (∃! l : (normalPartition T).Leaf, ((normalPartition T).guard l).eval xs = true) ∧
    ∀ l : (normalPartition T).Leaf, ((normalPartition T).guard l).eval xs = true →
      Nonnegative xs (inverseTemplate t ((normalPartition T).output l)) ∧
      Normal (templateCode xs (inverseTemplate t ((normalPartition T).output l))) ∧
      A.readout () t (expand (templateCode xs (inverseTemplate t ((normalPartition T).output l)))) =
        expand (templateCode xs T) ∧
      ∀ n q, rankInverse t n = some q ↔ q + t = n

private theorem symbolic_actual : symbolicArena.Law symbolicActual := by
  exact (@symbolic_presburger_inverse)

private theorem symbolic_rejected : ¬ symbolicArena.Law symbolicRejected := by
  intro law
  let T : Template := .of (.const 1)
  have h := law T 0 [] (by change (0 : Int) ≤ 1; omega) ⟨_, rfl⟩
  obtain ⟨l, hl, _⟩ := h.1
  have bad := (h.2 l hl).2.2.1
  change (FreeMagma.of true : Source) = FreeMagma.of false at bad
  cases bad

def symbolicEvidence : Registration symbolicArena (type_of% (@symbolic_presburger_inverse)) where
  actual := symbolicActual
  bridge := Iff.rfl
  variation := ⟨symbolic_actual, symbolicRejected, symbolic_rejected⟩
  sensitivity := ⟨fun i => ⟨symbolicRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, symbolic_rejected⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨0, .of true, .of false, ?_⟩
    intro h
    cases h

noncomputable def symbolicRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@symbolic_presburger_inverse) (Realization symbolicSignature) (Nat → Type) Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteNormalInversion.symbolic_presburger_inverse.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFiniteNormalInversion.symbolicEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨symbolicArena⟩
  objectArena := .source ⟨symbolicArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source symbolicArena ⟨symbolicEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize symbolicSignature (fun _ t g => substitution^[t] g) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFiniteNormalInversion
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "body", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms symbolicEvidence

abbrev originalSignature : Signature where
  Params := Unit
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := CompletionTree
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev originalActual : Realization originalSignature :=
  realize originalSignature (fun _ _ g => embed g) (fun e => nomatch e)
abbrev originalRejected : Realization originalSignature :=
  realize originalSignature (fun _ _ _ => leaf true) (fun e => nomatch e)

abbrev originalArena : Arena where
  signature := originalSignature
  Law A := ∀ {n k m r : Nat} (I : EpochInput n k m)
    (s : Fin m → Nat) (valid : Potential I s) (mode : EffectiveMode (functionalInput I s))
    (R : Fin r → Expression k m) (i : Fin r) (f : FiniteExpression (k + 1))
    (finite : finiteImageExpressions I s mode R i = some f)
    (p : Fin n → Nat)
    (passing : (originalImageGuard (functionalInput I s) mode).holds (environment p)),
    let P := normalPartition (finiteTemplate I.base f)
    (∃! l : P.Leaf, (P.guard l).eval (environment p) = true) ∧
    ∀ l : P.Leaf, (P.guard l).eval (environment p) = true →
      Nonnegative (environment p) (inverseTemplate (commonShift s) (P.output l)) ∧
      Normal (templateCode (environment p) (inverseTemplate (commonShift s) (P.output l))) ∧
      evaluate (ranks I.base p) (canonicalOriginal I s valid mode p passing) (R i) =
        A.readout () () (expand (templateCode (environment p) (inverseTemplate (commonShift s) (P.output l)))) ∧
      (∀ v, OriginalAdmissible I p v →
        EffectiveInMode (functionalInput I s) mode p (imageValues s v) →
        evaluate (ranks I.base p) v (R i) =
          embed (expand (templateCode (environment p) (inverseTemplate (commonShift s) (P.output l))))) ∧
      (∀ n q, rankInverse (commonShift s) n = some q ↔ q + commonShift s = n)

private theorem original_actual : originalArena.Law originalActual := by
  simpa only [originalArena, originalActual, realize, decide_eq_true_eq] using (@original_symbolic_finite_value)

private theorem original_rejected : ¬ originalArena.Law originalRejected := by
  intro law
  let R : Fin 1 → Expression 0 0 := fun _ => .ground (.of false)
  let f : FiniteExpression 1 := .ground (.of false)
  have finite : finiteImageExpressions emptyEpoch emptyPotential emptyMode R 0 = some f := rfl
  have h := law emptyEpoch emptyPotential empty_valid emptyMode R 0 f finite
    emptyParameters empty_passing
  obtain ⟨l, hl, _⟩ := h.1
  have bad := (h.2 l hl).2.2.1
  change leaf false = leaf true at bad
  have tags := congrArg (fun X => (PFunctor.M.dest X).1) bad
  cases tags

def originalEvidence : Registration originalArena (type_of% (@original_symbolic_finite_value)) where
  actual := originalActual
  bridge := by simp only [originalArena, originalActual, realize, decide_eq_true_eq]
  variation := ⟨original_actual, originalRejected, original_rejected⟩
  sensitivity := ⟨fun i => ⟨originalRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, original_rejected⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(), .of true, .of false, ?_⟩
    intro h
    have tags := congrArg (fun X => (PFunctor.M.dest X).1) h
    cases tags

noncomputable def originalRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_symbolic_finite_value) (Realization originalSignature) (originalSignature.Params → Type) Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteNormalInversion.original_symbolic_finite_value.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFiniteNormalInversion.originalEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨originalArena⟩
  objectArena := .source ⟨originalArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source originalArena ⟨originalEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize originalSignature (fun _ _ g => embed g) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFiniteNormalInversion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms originalEvidence

end
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeFiniteNormalInversion
