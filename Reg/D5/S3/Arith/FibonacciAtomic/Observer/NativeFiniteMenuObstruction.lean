import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuObstruction
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply readout)
open D5.S3.Arith.FibonacciAtomic.ActualImageAddressCertificate (height)
open D5.S3.Arith.FibonacciAtomic.Observer
open NativeFiniteMenuCode NativeFiniteMenuReconstruction NativeFiniteMenuObstruction
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuObstruction

abbrev signature : Signature where
  Params := Menu
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ S u => code S u) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ S _ => code S (.of false)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : Nat) (S : Menu)
    (bounded : ∀ q ∈ S, q.length + 1 ≤ D) (a r : Address)
    (proper : r ≠ []) (selected : a ++ r ∈ S) (missing : a ∉ S),
    let v := spine a (.of true)
    let v' := spine a (.of false)
    let k := NativeRankedNavigationCompiler.pathCost r + 1
    2 ≤ D ∧ height v = a.length ∧ height v' = a.length ∧ a.length ≤ D - 2 ∧
      Family D (outer v) ∧ Family D (outer v') ∧
      initial S v = initial S v' ∧ initial (publicMenu S) (outer v) = initial (publicMenu S) (outer v') ∧
      R.readout () S v ≠ code S v' ∧ k < 2 * D ∧
      readout (true :: (a ++ r)) (substitution^[k] (outer v)) = .beta ∧
      readout (true :: (a ++ r)) (substitution^[k] (outer v')) = .branch ∧
      future S v k ≠ future S v' k ∧
      future (publicMenu S) (outer v) k ≠ future (publicMenu S) (outer v') k

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have z := h 2 [[false]] (by intro q hq; simp at hq; subst q; decide) [] [false] (by decide) (by simp) (by simp)
  exact z.2.2.2.2.2.2.2.2.1 rfl

def family : Registration arena (type_of% (@every_missing_prefix_obstruction)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨every_missing_prefix_obstruction, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨[[]], .of true, .of false, ?_⟩
    exact original_code_context_separation [[]] [] [] (by simp)

noncomputable def every_missing_prefix_obstruction_registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@every_missing_prefix_obstruction) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuObstruction.every_missing_prefix_obstruction.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuObstruction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ S u => code S u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuObstruction
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","arg","arg","arg","arg","arg","arg","arg","arg","fn","arg","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms every_missing_prefix_obstruction_registration

abbrev separatorSignature : Signature where
  Params := Address
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Reply
  Anchor := Empty
  finiteAnchor := inferInstance

def separatorActual : Realization separatorSignature :=
  realize separatorSignature (fun _ q u => readout q u) (fun e => nomatch e)

def separatorBad : Realization separatorSignature :=
  realize separatorSignature (fun _ _ _ => .alpha) (fun e => nomatch e)

abbrev separatorArena : Arena where
  signature := separatorSignature
  Law R := ∀ r : Address,
    R.readout () r (substitution^[NativeRankedNavigationCompiler.pathCost r+1] (.of true)) = .beta ∧
    R.readout () r (substitution^[NativeRankedNavigationCompiler.pathCost r+1] (.of false)) = .branch

private theorem separator_bad : ¬ separatorArena.Law separatorBad := by
  intro h
  have he := (h []).1
  cases he

def separatorFamily : Registration separatorArena (type_of% (@atomic_separator)) where
  actual := separatorActual
  bridge := Iff.rfl
  variation := ⟨atomic_separator, separatorBad, separator_bad⟩
  sensitivity := ⟨fun i => ⟨separatorBad,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, separator_bad⟩, fun i => nomatch i⟩
  dependence := by
    intro _
    refine ⟨[], .of true, .of false, ?_⟩
    change Reply.alpha ≠ .beta
    decide

noncomputable def atomic_separator_registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@atomic_separator) (Realization separatorSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuObstruction.atomic_separator.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuObstruction.separatorFamily
  realizationSource := none
  generated := false
  arena := .source ⟨separatorArena⟩
  objectArena := .source ⟨separatorArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source separatorArena ⟨separatorFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize separatorSignature (fun _ q u => readout q u) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuObstruction
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","fn","arg","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms separatorFamily
#print axioms atomic_separator_registration

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuObstruction
