import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply readout)
open D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine
open D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialEffective
open D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth
open D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns (History Consistent)
open D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder (literalRecord)
open D5.S3.Arith.FibonacciAtomic.Observer.NativeHistoryCells (ActualFiber)
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev answersSignature : Signature where
  Params := Unit
  State _ := Trace
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := List Reply
  Anchor := Empty
  finiteAnchor := inferInstance

def answersActual : Realization answersSignature :=
  realize answersSignature (fun _ _ t => answers t) (fun e => nomatch e)

def answersBad : Realization answersSignature :=
  realize answersSignature (fun _ _ _ => []) (fun e => nomatch e)

abbrev supportArena : Arena where
  signature := answersSignature
  Law R := ∀ {C O : Type} (δ : C → Op C O) (c : C) (N K : Nat),
    ∃ D : Finset Descriptor, ∀ (u : Source) (t : Trace) (o : O),
      Run δ c N (substitution^[N] u) t o →
      (R.readout () () t).length ≤ K → ∀ n a y, Event.read n a y ∈ t → (n,a) ∈ D

private def spine : Nat → Source
  | 0 => .of true
  | n+1 => .mul (spine n) (.of false)

private theorem spine_read (n m : Nat) :
    readout (List.replicate n false) (spine (n+m)) =
      if m = 0 then .alpha else .branch := by
  induction n with
  | zero => cases m <;> simp [spine,readout]
  | succ n ih => simpa [Nat.succ_add,List.replicate_succ,spine,readout] using ih

private def walk : Option Nat → Op (Option Nat) Unit
  | none => .stop ()
  | some n => .read (List.replicate n false)
      (fun y => if y = .branch then some (n+1) else none)

private theorem spine_run (n m : Nat) :
    ∃ t, Run walk (some n) 0 (spine (n+m)) t () ∧
      Event.read 0 (List.replicate (n+m) false) .alpha ∈ t := by
  induction m generalizing n with
  | zero =>
      refine ⟨[.read 0 (List.replicate n false) .alpha],?_,by simp⟩
      apply Run.read rfl
      · simpa using spine_read n 0
      · exact Run.stop rfl
  | succ m ih =>
      obtain ⟨t,run,mem⟩ := ih (n+1)
      have eq : n+1+m = n+(m+1) := by omega
      rw [eq] at run mem
      refine ⟨.read 0 (List.replicate n false) .branch::t,?_,by simp [mem]⟩
      apply Run.read rfl
      · simpa using spine_read n (m+1)
      · exact run

private theorem support_bad : ¬ supportArena.Law answersBad := by
  intro h
  obtain ⟨D,cover⟩ := @h (Option Nat) Unit walk (some 0) 0 0
  let n := D.sup (fun d => d.2.length)+1
  obtain ⟨t,run,mem⟩ := spine_run 0 n
  have present : (0,List.replicate n false) ∈ D := cover (spine n) t ()
    (by simpa using run) (Nat.le_refl 0) 0 (List.replicate n false) .alpha (by simpa using mem)
  have bound : n ≤ D.sup (fun d => d.2.length) := by
    simpa using Finset.le_sup (f := fun d : Descriptor => d.2.length) present
  dsimp [n] at bound
  omega

def supportProof : Registration supportArena (type_of% (@bounded_read_support)) where
  actual := answersActual
  bridge := Iff.rfl
  variation := ⟨@bounded_read_support,answersBad,support_bad⟩
  sensitivity := ⟨fun i => ⟨answersBad,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,support_bad⟩,fun i => nomatch i⟩
  dependence := by
    intro i
    exact ⟨(),[],[.read 0 [] .alpha],by simp [answersActual,realize,answers,reads]⟩

abbrev outputSignature : Signature where
  Params := Σ O : Type, Source → O
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def outputActual : Realization outputSignature :=
  realize outputSignature (fun _ p u => p.2 u) (fun e => nomatch e)

def outputBad : Realization outputSignature :=
  realize outputSignature (fun _ p _ => p.2 (.of true)) (fun e => nomatch e)

abbrev depthArena : Arena where
  signature := outputSignature
  Law R := ∀ {C O : Type} (δ : C → Op C O) (c : C) (N K : Nat)
    (U : Set Source) (F : Source → O),
    (∀ u ∈ U, ∃ t, Run δ c N (substitution^[N] u) t (F u) ∧ (answers t).length ≤ K) →
    ∃ h : Nat, ∀ u ∈ U, ∀ v ∈ U, OriginalAgree h u v →
      R.readout () ⟨O,F⟩ u = F v ∧ ∃ t, Run δ c N (substitution^[N] u) t (F u) ∧
        Run δ c N (substitution^[N] v) t (F v)

def leafBit : Source → Bool
  | .of b => b
  | .mul _ _ => true

private theorem depth_bad : ¬ depthArena.Law outputBad := by
  intro law
  obtain ⟨h,depth⟩ := @law Unit Bool (fun _ => .stop false) () 0 0 {(.of false)} leafBit (by
    intro u hu
    simp only [Set.mem_singleton_iff] at hu
    subst u
    exact ⟨[],Run.stop rfl,by simp [answers,reads]⟩)
  have bad := (depth (.of false) (by simp) (.of false) (by simp) (fun _ _ => rfl)).1
  cases bad

def depthProof : Registration depthArena (type_of% (@bounded_serial_original_depth)) where
  actual := outputActual
  bridge := Iff.rfl
  variation := ⟨@bounded_serial_original_depth,outputBad,depth_bad⟩
  sensitivity := ⟨fun i => ⟨outputBad,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,depth_bad⟩,fun i => nomatch i⟩
  dependence := by
    intro i
    exact ⟨⟨Bool,leafBit⟩,.of true,.of false,by simp [outputActual,realize,leafBit]⟩

abbrev rowSignature : Signature where
  Params := CutSet
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := LiteralRow
  Anchor := Empty
  finiteAnchor := inferInstance

def rowActual : Realization rowSignature :=
  realize rowSignature (fun _ Q u => canonicalRow Q u) (fun e => nomatch e)

def rowBad : Realization rowSignature :=
  realize rowSignature (fun _ _ _ => .of (.inl true)) (fun e => nomatch e)

abbrev rowArena : Arena where
  signature := rowSignature
  Law R := ∀ {C : Type} (δ : C → Op C LiteralRow) (c : C)
    (P Q : CutSet), CutPrefixFree Q → ∀ (old : LiteralRow) (H : History) (N K : Nat),
    (∀ u : ActualFiber P old H, ∃ t, Run δ c N (substitution^[N] u.val) t
      (canonicalRow Q u.val) ∧ (answers t).length ≤ K) →
    ∃ h : Nat, ∀ u v : ActualFiber P old H, OriginalAgree h u.val v.val →
      R.readout () Q u.val = canonicalRow Q v.val ∧ literalRecord Q u.val = literalRecord Q v.val

private theorem row_bad : ¬ rowArena.Law rowBad := by
  intro law
  let old := canonicalRow (∅ : CutSet) (.of false)
  let u : ActualFiber ∅ old [] := ⟨.of false,rfl,by simp [Consistent]⟩
  obtain ⟨h,depth⟩ := @law Unit (fun _ => .stop old) () ∅ ∅ (by simp [CutPrefixFree,D5.S0.Computability.Coding.PrefixFreeCode.IsPrefixFree]) old [] 0 0 (by
    intro v
    refine ⟨[],?_,by simp [answers,reads]⟩
    rw [v.property.1]
    exact Run.stop rfl)
  have bad := (depth u u (fun _ _ => rfl)).1
  have eq : (FreeMagma.of (.inl true) : LiteralRow) = .of (.inl false) := by
    simpa [rowBad,realize,u,canonicalRow,literalRow] using bad
  cases eq

def rowProof : Registration rowArena (type_of% (@whole_row_serial_implies_depth)) where
  actual := rowActual
  bridge := Iff.rfl
  variation := ⟨@whole_row_serial_implies_depth,rowBad,row_bad⟩
  sensitivity := ⟨fun i => ⟨rowBad,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,row_bad⟩,fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨∅,.of true,.of false,?_⟩
    intro eq
    have eq' : (FreeMagma.of (.inl true) : LiteralRow) = .of (.inl false) := by
      simpa [rowActual,realize,canonicalRow,literalRow] using eq
    cases eq'

abbrev effectiveArena : Arena where
  signature := rowSignature
  Law R := ∀ (S : EffectiveService LiteralRow) (P Q : CutSet), CutPrefixFree Q →
    ∀ (old : LiteralRow) (H : History) (N K : Nat),
    (∀ u : ActualFiber P old H, ∃ t, ServiceRun S S.initial N (substitution^[N] u.val) t
      (canonicalRow Q u.val) ∧ (answers t).length ≤ K) →
    ∃ h : Nat, ∀ u v : ActualFiber P old H, OriginalAgree h u.val v.val →
      R.readout () Q u.val = canonicalRow Q v.val ∧ literalRecord Q u.val = literalRecord Q v.val

private theorem effective_bad : ¬ effectiveArena.Law rowBad := by
  intro law
  let old := canonicalRow (∅ : CutSet) (.of false)
  let u : ActualFiber ∅ old [] := ⟨.of false,rfl,by simp [Consistent]⟩
  let S : EffectiveService LiteralRow := ⟨fun _ => (3,0,[],(0,0,0,0)),Computable.const _,0,fun _ => old⟩
  obtain ⟨h,depth⟩ := law S ∅ ∅ (by simp [CutPrefixFree,D5.S0.Computability.Coding.PrefixFreeCode.IsPrefixFree]) old [] 0 0 (by
    intro v
    refine ⟨[],?_,by simp [answers,reads]⟩
    rw [v.property.1]
    exact ServiceRun.stop (by decide) (by decide) (by decide))
  have bad := (depth u u (fun _ _ => rfl)).1
  have eq : (FreeMagma.of (.inl true) : LiteralRow) = .of (.inl false) := by
    simpa [rowBad,realize,u,canonicalRow,literalRow] using bad
  cases eq

def effectiveProof : Registration effectiveArena (type_of% (@effective_whole_row_implies_depth)) where
  actual := rowActual
  bridge := Iff.rfl
  variation := ⟨effective_whole_row_implies_depth,rowBad,effective_bad⟩
  sensitivity := ⟨fun i => ⟨rowBad,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,effective_bad⟩,fun i => nomatch i⟩
  dependence := rowProof.dependence

noncomputable def bounded_read_support_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth.bounded_read_support)
    (Realization answersSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth.bounded_read_support
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth.supportProof
  realizationSource := none
  generated := false
  arena := .source ⟨supportArena⟩
  objectArena := .source ⟨supportArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source supportArena ⟨supportProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize answersSignature answersActual.readout answersActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body","body","body","body","body","body","arg","body","body","body","body","body","domain","fn","arg","arg"], stateBinder := 8, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def bounded_serial_original_depth_registration : LeanInformationAudit.Contract.Registration.{1,1,1,0,0,0,1,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth.bounded_serial_original_depth)
    (Realization outputSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth.bounded_serial_original_depth
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth.depthProof
  realizationSource := none
  generated := false
  arena := .source ⟨depthArena⟩
  objectArena := .source ⟨depthArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source depthArena ⟨depthProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize outputSignature outputActual.readout outputActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth
    definition := none
    coordinates := #[1,7]
    readouts := #[{ path := #["body","body","body","body","body","body","body","body","body","arg","body","body","body","body","body","body","fn","arg","fn","arg"], stateBinder := 10, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def whole_row_serial_implies_depth_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth.whole_row_serial_implies_depth)
    (Realization rowSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth.whole_row_serial_implies_depth
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth.rowProof
  realizationSource := none
  generated := false
  arena := .source ⟨rowArena⟩
  objectArena := .source ⟨rowArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rowArena ⟨rowProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rowSignature rowActual.readout rowActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth
    definition := none
    coordinates := #[4]
    readouts := #[{ path := #["body","body","body","body","body","body","body","body","body","body","body","arg","body","body","body","body","fn","arg","fn","arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def effective_whole_row_implies_depth_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth.effective_whole_row_implies_depth)
    (Realization rowSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth.effective_whole_row_implies_depth
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth.effectiveProof
  realizationSource := none
  generated := false
  arena := .source ⟨effectiveArena⟩
  objectArena := .source ⟨effectiveArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source effectiveArena ⟨effectiveProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rowSignature rowActual.readout rowActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth
    definition := none
    coordinates := #[2]
    readouts := #[{ path := #["body","body","body","body","body","body","body","body","body","arg","body","body","body","body","fn","arg","fn","arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev originalRowArena : Arena where
  signature := rowSignature
  Law R := ∀ (S : OriginalEffectiveService RowWord) (s : OriginalState)
    (P Q : CutSet), CutPrefixFree Q → ∀ (old : LiteralRow) (H : History)
    (N K : Nat), s.epoch = N → Nonempty (ActualFiber P old H) →
    (∀ u : ActualFiber P old H, ∃ t, OriginalRun S s (substitution^[N] u.val) t
      (rowWord (canonicalRow Q u.val)) ∧ (answers t).length ≤ K) →
    (∃ h : Nat, ∀ u v : ActualFiber P old H, OriginalAgree h u.val v.val →
      R.readout () Q u.val = canonicalRow Q v.val ∧ literalRecord Q u.val = literalRecord Q v.val) ∧
    (∃ labels : Finset LiteralRow, labels.card ≤ 4^K ∧
      ∀ u : ActualFiber P old H, canonicalRow Q u.val ∈ labels)

private theorem original_row_bad : ¬ originalRowArena.Law rowBad := by
  intro law
  let old := canonicalRow (∅ : CutSet) (.of false)
  let u : ActualFiber ∅ old [] := ⟨.of false,rfl,by simp [Consistent]⟩
  let S : OriginalEffectiveService RowWord := {
    select := fun _ => Part.some (originalStop (rowWord old))
    effective := Computable.const _ }
  obtain ⟨⟨h,depth⟩,_⟩ := law S (0, 0, 0, []) ∅ ∅
    (by simp [CutPrefixFree,D5.S0.Computability.Coding.PrefixFreeCode.IsPrefixFree])
    old [] 0 0 rfl ⟨u⟩ (by
      intro v
      refine ⟨[],?_,by simp [answers,reads]⟩
      rw [v.property.1]
      exact OriginalRun.stop (by simp [S]))
  have bad := (depth u u (fun _ _ => rfl)).1
  have eq : (FreeMagma.of (.inl true) : LiteralRow) = .of (.inl false) := by
    simpa [rowBad,realize,u,canonicalRow,literalRow] using bad
  cases eq

def originalRowProof : Registration originalRowArena
    (type_of% (@original_whole_row_implies_depth_and_image)) where
  actual := rowActual
  bridge := Iff.rfl
  variation := ⟨@original_whole_row_implies_depth_and_image,rowBad,original_row_bad⟩
  sensitivity := ⟨fun i => ⟨rowBad,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,original_row_bad⟩,fun i => nomatch i⟩
  dependence := rowProof.dependence

noncomputable def original_whole_row_implies_depth_and_image_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth.original_whole_row_implies_depth_and_image)
    (Realization rowSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth.original_whole_row_implies_depth_and_image
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth.originalRowProof
  realizationSource := none
  generated := false
  arena := .source ⟨originalRowArena⟩
  objectArena := .source ⟨originalRowArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source originalRowArena ⟨originalRowProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rowSignature rowActual.readout rowActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth
    definition := none
    coordinates := #[3]
    readouts := #[{ path := #["body","body","body","body","body","body","body","body","body","body","body","body","fn","arg","arg","body","body","body","body","fn","arg","fn","arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
abbrev uniqueSignature : Signature where
  Params := Unit
  State _ := Trace
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Trace
  Anchor := Empty
  finiteAnchor := inferInstance

def uniqueActual : Realization uniqueSignature :=
  realize uniqueSignature (fun _ _ t => t) (fun e => nomatch e)
def uniqueBad : Realization uniqueSignature :=
  realize uniqueSignature (fun _ _ _ => []) (fun e => nomatch e)
abbrev uniqueArena : Arena where
  signature := uniqueSignature
  Law R := ∀ {C : Type} {O : Type} {δ : C → Op C O}
    {c : C} {e : Nat} {r : Source} {t s : Trace} {o p : O}
    (_ : Run δ c e r t o) (_ : Run δ c e r s p),
    R.readout () () t = s ∧ o = p

private def uniqueProbe : Bool → Op Bool Unit
  | true => .read [] (fun _ => false)
  | false => .stop ()

private theorem unique_bad : ¬ uniqueArena.Law uniqueBad := by
  intro law
  have run : Run uniqueProbe true 0 (.of true) [.read 0 [] .alpha] () :=
    Run.read rfl rfl (Run.stop rfl)
  have eq := (law run run).1
  change ([] : Trace) = [.read 0 [] .alpha] at eq
  cases eq

def uniqueProof : Registration uniqueArena (type_of% (@run_unique)) where
  actual := uniqueActual
  bridge := Iff.rfl
  variation := ⟨@run_unique,uniqueBad,unique_bad⟩
  sensitivity := ⟨fun i => ⟨uniqueBad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,unique_bad⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    exact ⟨(),[],[.read 0 [] .alpha],by simp [uniqueActual,realize]⟩

noncomputable def run_unique_registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@run_unique) (Realization uniqueSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth.run_unique.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth.uniqueProof
  realizationSource := none
  generated := false
  arena := .source ⟨uniqueArena⟩
  objectArena := .source ⟨uniqueArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source uniqueArena ⟨uniqueProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize uniqueSignature uniqueActual.readout uniqueActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","fn","arg","fn","arg"],
      stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialDepth
