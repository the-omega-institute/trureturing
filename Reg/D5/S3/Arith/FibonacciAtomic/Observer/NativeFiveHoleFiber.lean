import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleJointChoice
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleFiber
open D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleCompiler
open D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleJointChoice
open D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionDecoder (literalRecord HoleExterior)
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address)
open D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity (subtree)
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleFiber

private def emptyHistory : History := ⟨[],by simp [Supported]⟩
private theorem present (side : Bool) : Stratum side emptyHistory (source side (.of true) (.of false)) :=
  (raw_stratum_iff side emptyHistory _).mpr ⟨.of true,.of false,rfl,
    by unfold Distinct F; decide +kernel,by simp [Protected,emptyHistory]⟩
private theorem absent (side : Bool) : ¬ Stratum side emptyHistory (.of true) := by
  intro h
  obtain ⟨x,y,z,h⟩ := (raw_fiber_iff _).mp h.1.1
  cases h

namespace RawFiber
abbrev signature : Signature where
  Params := Unit
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ u => Raw u) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ u : Source, R.readout () () u ↔ ∃ x y z : Source, u = V x y z
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  exact (h (V (.of true) (.of true) (.of true))).mpr ⟨_,_,_,rfl⟩
def proof : Registration arena (type_of% (@raw_fiber_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@raw_fiber_iff,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(),V (.of true) (.of true) (.of true),.of true,?_⟩
    intro eq
    have h := eq.mp ((raw_fiber_iff _).mpr ⟨_,_,_,rfl⟩)
    obtain ⟨x,y,z,he⟩ := (raw_fiber_iff _).mp h
    cases he

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@raw_fiber_iff) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleFiber.RawFiber.raw_fiber_iff
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleFiber.RawFiber.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ u => Raw u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleFiber
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms proof
end RawFiber

namespace EpochHole
abbrev signature : Signature where
  Params := Σ a : Nat, Σ y : Source, Σ z : Source, Fin 5
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option Source
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p x => subtree (position p.2.2.2) (substitution^[p.1] (V x p.2.1 p.2.2.1)))
  (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => none) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a : Nat) (x y z : Source) (i : Fin 5),
    R.readout () ⟨a,y,z,i⟩ x = some (substitution^[a] (hole x y z i))
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have no := h 0 (.of true) (.of true) (.of true) 0
  cases no
def proof : Registration arena (type_of% (@epoch_hole)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@epoch_hole,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨0,.of true,.of true,0⟩,.of true,.of false,?_⟩
    intro eq
    change some (FreeMagma.of true) = some (FreeMagma.of false) at eq
    cases eq

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@epoch_hole) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleFiber.EpochHole.epoch_hole
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleFiber.EpochHole.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
  (fun _ p x => subtree (position p.2.2.2) (substitution^[p.1] (V x p.2.1 p.2.2.1)))
  (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleFiber
    definition := none
    coordinates := #[0,2,3,4]
    readouts := #[{
      path := #["body","body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg","arg","fn","fn","arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms proof
end EpochHole

namespace CompleteLabel
abbrev signature : Signature where
  Params := Σ side : Bool, Σ y : Source, Source
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p x => literalRecord Q (V x p.2.1 p.2.2) = label p.1) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => True) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (side : Bool) (x y z : Source),
    R.readout () ⟨side,y,z⟩ x ↔ x = (if side then F y else y) ∧ Distinct y z
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have no := (h false (.of true) (.of true) (.of true)).mp trivial |>.2.1
  exact no rfl
def proof : Registration arena (type_of% (@complete_label_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@complete_label_iff,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨false,.of true,.of false⟩,.of true,F (.of true),?_⟩
    intro eq
    have yes := (complete_label_iff false (.of true) (.of true) (.of false)).mpr
      ⟨rfl,by unfold Distinct F; decide +kernel⟩
    have no := (complete_label_iff false (F (.of true)) (.of true) (.of false)).mp (eq.mp yes) |>.1
    cases no

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@complete_label_iff) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleFiber.CompleteLabel.complete_label_iff
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleFiber.CompleteLabel.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
  (fun _ p x => literalRecord Q (V x p.2.1 p.2.2) = label p.1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleFiber
    definition := none
    coordinates := #[0,2,3]
    readouts := #[{
      path := #["body","body","body","body","fn","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms proof
end CompleteLabel

namespace RawStratum
abbrev signature : Signature where
  Params := Σ side : Bool, History
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p u => Stratum p.1 p.2 u) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (side : Bool) (H : History) (u : Source),
    R.readout () ⟨side,H⟩ u ↔ ∃ y z : Source,
      u = source side y z ∧ Distinct y z ∧ Protected H (source side y z)
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  exact (h false emptyHistory _).mpr ((raw_stratum_iff false emptyHistory _).mp (present false))
def proof : Registration arena (type_of% (@raw_stratum_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@raw_stratum_iff,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨false,emptyHistory⟩,source false (.of true) (.of false),.of true,?_⟩
    intro eq
    exact absent false (eq.mp (present false))

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@raw_stratum_iff) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleFiber.RawStratum.raw_stratum_iff
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleFiber.RawStratum.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p u => Stratum p.1 p.2 u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleFiber
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","fn","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms proof
end RawStratum

abbrev rootSignature : Signature where
  Params := Unit
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := HoleExterior × Finset (Address × Address)
  Anchor := Empty
  finiteAnchor := inferInstance

def rootActual : Realization rootSignature :=
  realize rootSignature (fun _ _ u => literalRecord {[]} u) (fun i => nomatch i)

abbrev rootArena : Arena where
  signature := rootSignature
  Law R := ∀ u : Source, R.readout () () u = rootLabel

/-- The exact constant root readout cannot satisfy the observational dependence
required by this template, even though its row equality holds for all sources. -/
theorem root_registration_impossible :
    ¬ Nonempty (Registration rootArena (type_of% (@root_record))) := by
  rintro ⟨r⟩
  obtain ⟨p,x,y,hxy⟩ := r.dependence ()
  cases p
  exact hxy ((r.variation.1 x).trans (r.variation.1 y).symm)

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiveHoleFiber
