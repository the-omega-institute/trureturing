import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.OriginalVector.InterleavedWordRecovery
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity (subtree)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.OriginalVector.InterleavedWordRecovery
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.OriginalVector.InterleavedWordRecovery

abbrev familySignature : Signature where
  Params := Σ h : Nat, Fin h → Address
  State p := {x : List Bool // x.length = p.1}
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Source
  Anchor := Empty
  finiteAnchor := inferInstance

def familyActual : Realization familySignature := realize familySignature
  (fun _ p x => original (Nat.clog 2 p.1) p.2 x.val) (fun e => nomatch e)
def familyBad : Realization familySignature := realize familySignature
  (fun _ _ _ => .of true) (fun e => nomatch e)
abbrev familyArena : Arena where
  signature := familySignature
  Law R := ∀ {h : Nat} (positive : 0 < h)
    (q : Fin h → Address) (injective : Function.Injective q)
    (lengths : ∀ i, (q i).length = Nat.clog 2 h),
    Function.Injective (fun x : {x : List Bool // x.length = h} =>
      R.readout () ⟨h,q⟩ x) ∧
    (∀ x a, a.length = Nat.clog 2 h → (∀ i, q i ≠ a) →
      subtree a (original (Nat.clog 2 h) q x) = some (.of true)) ∧
    (∀ x i, subtree (q i) (original (Nat.clog 2 h) q x) =
      some (.of (!(x.getD i.val false)))) ∧
    (∀ x, x.length = h →
      Run (program q) (initial h positive) 0 (original (Nat.clog 2 h) q x)
        (chronology q 0 x) x ∧
      Run (wordProgram q) (install (initial h positive)) 0 (original (Nat.clog 2 h) q x)
        (chronology q 0 x) x ∧
      (∀ t z, Run (wordProgram q) (install (initial h positive)) 0
          (original (Nat.clog 2 h) q x) t z → t = chronology q 0 x ∧ z = x) ∧
      (answers (chronology q 0 x)).length = h ∧
      (chronology q 0 x).length = 2*h-1 ∧
      (chronology q 0 x).countP (fun e => match e with | .update _ => true | _ => false) = h-1 ∧
      Event.localStep ∉ chronology q 0 x ∧
      Nat.card {v : Vertex h // ∃ r, Reached positive q (original (Nat.clog 2 h) q x) v r} = 2*h) ∧
    (∀ x, x.length = h → ∀ v r,
      Reached positive q (original (Nat.clog 2 h) q x) v r ↔
        Fits v x ∧ r = substitution^[epochOf v] (original (Nat.clog 2 h) q x)) ∧
    Fintype.card (Vertex h) = 3*2^h-3 ∧
    Fintype.card (Installed h) = 3*2^h-3 ∧
    (∀ w : Installed h,
      D5.S1.Words.AdmissibleWords.AdmissibleCount.Adm (5*h-3) w.val) ∧
    Function.Injective (encode : Vertex h → (Fin (5*h-3) → Bool)) ∧
    (∀ (s : List Bool) (hs : s.length < h) (b : Bool), hammingDist (encode (.q s hs)) (encode (child s hs b)) = 1) ∧
    (∀ (s : List Bool) (hs : 0 < s.length ∧ s.length < h), hammingDist (encode (.u s hs)) (encode (.q s hs.2)) = 1) ∧
    (∀ (s : List Bool) (hs : s.length < h) (r : Reply), decode s.length r = none →
      response s hs r = .q s hs ∧ hammingDist (encode (.q s hs)) (encode (response s hs r)) = 0) ∧
    (∀ w : Installed h, ∃ x : List Bool, x.length = h ∧ ∃ e r t,
      StateTransition.Reaches (nativeStep (wordProgram q))
        (install (initial h positive), 0, original (Nat.clog 2 h) q x, []) (w,e,r,t)) ∧
    (∀ s hs, wordProgram q (install (.q s hs)) =
      .read (literal q s.length) (fun r => install (response s hs r))) ∧
    (∀ s hs, wordProgram q (install (.u s hs)) = .applyRho (install (.q s hs.2))) ∧
    (∀ s hs, wordProgram q (install (.z s hs)) = .stop s) ∧
    (∀ w c, wordProgram q w ≠ .localStep c) ∧
    Function.Injective (fun x => answers (chronology q 0 x)) ∧
    (∀ x, x.length = h → ∀ w r,
      (∃ e t, StateTransition.Reaches (nativeStep (wordProgram q))
        (install (initial h positive),0,original (Nat.clog 2 h) q x,[]) (w,e,r,t)) ↔
        Fits (inverse w) x ∧
          r = substitution^[epochOf (inverse w)] (original (Nat.clog 2 h) q x)) ∧
    (∀ v e r t, nativeStep (wordProgram q) (install v,e,r,t) =
      (nativeStep (program q) (v,e,r,t)).map
        (fun a => (install a.1,a.2.1,a.2.2.1,a.2.2.2))) ∧
    (∀ x a, a.length = Nat.clog 2 h →
      subtree a (original (Nat.clog 2 h) q x) = some (leafValue q x a)) ∧
    (∀ u : Source, substitution u ≠ u)

private theorem family_bad : ¬ familyArena.Law familyBad := by
  intro law
  have hi := (law (h := 1) (by decide) (fun _ => [])
    (fun _ _ _ => Subsingleton.elim _ _) (by intro i; simp)).1
  have he := @hi (⟨[false],rfl⟩ : {x : List Bool // x.length = 1})
    (⟨[true],rfl⟩ : {x : List Bool // x.length = 1}) rfl
  have lists := congrArg Subtype.val he
  cases lists

def familyProof : Registration familyArena (type_of% (@interleaved_word_recovery)) where
  actual := familyActual
  bridge := Iff.rfl
  variation := ⟨@interleaved_word_recovery,familyBad,family_bad⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ family_bad
  dependence := by
    intro i
    refine ⟨⟨1,fun _ => []⟩,⟨[false],rfl⟩,⟨[true],rfl⟩,?_⟩
    intro same
    have hi := (interleaved_word_recovery (h := 1) (by decide) (fun _ => [])
      (fun _ _ _ => Subsingleton.elim _ _) (by intro i; simp)).1
    have he := hi same
    have lists := congrArg Subtype.val he
    cases lists

noncomputable def interleaved_word_recovery_registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@interleaved_word_recovery) (Realization familySignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.OriginalVector.InterleavedWordRecovery.interleaved_word_recovery.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.OriginalVector.InterleavedWordRecovery.familyProof
  realizationSource := none
  generated := false
  arena := .source ⟨familyArena⟩
  objectArena := .source ⟨familyArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source familyArena ⟨familyProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize familySignature familyActual.readout familyActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.OriginalVector.InterleavedWordRecovery
    definition := none
    coordinates := #[0,2]
    readouts := #[{
      path := #["body","body","body","body","body","fn","arg","arg","body"],
      stateBinder := 5, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.OriginalVector.InterleavedWordRecovery
