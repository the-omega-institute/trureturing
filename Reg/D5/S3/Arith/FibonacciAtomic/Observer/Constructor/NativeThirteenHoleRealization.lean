import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeThirteenHoleRealization
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.Arith.FibonacciAtomic.Observer
open NativeThirteenHoleRealization
open NativePayloadHistoryInstallation
open D5.S3.Arith.FibonacciAtomic.FiniteHereditaryPatternRealization (B_T)
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeThirteenHoleRealization

abbrev signature : Signature where
  Params := Unit
  State _ := Nat
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Source
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun side _ h => theta side h) (fun e => nomatch e)
def bad : Realization signature := realize signature (fun _ _ _ => .of true) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ h, SignedJoint h (R.readout false () h) (R.readout true () h)

private theorem no_acquired : ¬ Acquired (.of true) := by
  intro h
  have lit := h.2.1 (.literal 0 [] .branch) (by simp [literals])
  cases lit

private theorem bad_law : ¬ arena.Law bad := fun h => no_acquired (h 0).1

def changed (side : Bool) : Realization signature := realize signature
  (fun i _ h => if i = side then .of true else theta i h) (fun e => nomatch e)

private theorem changed_law (side : Bool) : ¬ arena.Law (changed side) := by
  intro h
  cases side
  · exact no_acquired (h 0).1
  · exact no_acquired (h 0).2.1

def proof : Registration arena (type_of% (@actual_joint_realization)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_joint_realization,bad,bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨changed i,?_,rfl,changed_law i⟩
      intro j hj
      funext p h
      simp [actual,changed,realize,hj]
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨(),0,1,?_⟩
    intro eq
    have clocks := congrArg (fun t : Source =>
      NativePrefixIdentityReflection.kappa (match t with | .of _ => t | .mul l _ => l)) eq
    cases i <;> change NativePrefixIdentityReflection.kappa (x 0) =
      NativePrefixIdentityReflection.kappa (x 1) at clocks
    all_goals
      unfold x at clocks
      rw [NativePrefixIdentityReflection.kappa_iterate,
        NativePrefixIdentityReflection.kappa_iterate] at clocks
      omega

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@actual_joint_realization) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeThirteenHoleRealization.actual_joint_realization
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeThirteenHoleRealization.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun side _ h => theta side h) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeThirteenHoleRealization
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body","fn","arg"], stateBinder := 0,
        functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["body","arg"], stateBinder := 0,
        functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms proof
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeThirteenHoleRealization
