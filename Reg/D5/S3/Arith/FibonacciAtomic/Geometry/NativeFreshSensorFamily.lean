import D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorFamily
import Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorGrowth
import Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorSector
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorFamily
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address readout leaves)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity (subtree)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeMaterialRootRecognition (D material terminals)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeGuardedLeafRepair (Value RawMap nativeRun zeroExtend)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorGrowth (calls grown sensors)
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorSector (vector half adjacency basis)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorFamily
open NativeFreshSensorSector (signature actual bad dependence)
noncomputable section
@[reducible] def supportArena : Arena where
  signature := signature
  Law R := ∀ (t : Source) (p : Address), subtree p t = some (.mul (.of false) (.of false)) →
    (∀ q ∈ terminals (grown t), half p q = 0) ∧
    (∀ q ∈ sensors t, half p q = 0) ∧
    (∀ q ∈ sensors t, R.readout () t (half p) q = 0)
@[reducible] def familyArena : Arena where
  signature := signature
  Law R := ∀ {t : Source} {k : ℕ} (ch : Cherries t k),
    Function.Injective (H ch) ∧
    (∀ theta, R.readout () t (R.readout () t (H ch theta)) = H ch theta) ∧
    (∀ theta (j : ℕ) q, q ∈ sensors t → (R.readout () t)^[j] (H ch theta) q = 0) ∧
    (∀ theta q, q ∈ terminals (grown t) → H ch theta q = 0)
def supportBad : Realization signature := realize signature (fun _ _ _ _ => 1) (fun e => nomatch e)
private theorem support_bad : ¬ supportArena.Law supportBad := by
  intro h
  have hh := (h (.mul (.of false) (.of false)) [] rfl).2.2 [false,false,true]
    (by simp [sensors])
  change (1 : ℚ) = 0 at hh
  norm_num at hh
private def oneCherry : Cherries (.mul (.of false) (.of false)) 1 where
  root _ := []
  native _ := rfl
  disjoint i j hij := False.elim (hij (Subsingleton.elim i j))
private theorem family_bad : ¬ familyArena.Law bad := by
  intro h
  have hh := congrFun ((h oneCherry).2.1 (fun _ => 1)) [false]
  norm_num [bad,realize,H,oneCherry,half,vector,basis] at hh

def supportFamilyRegistration : Registration supportArena (type_of% designated_support) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨designated_support,supportBad,support_bad⟩
  sensitivity := ⟨fun i => ⟨supportBad,
    fun j hj => False.elim (hj (Subsingleton.elim j i)), rfl,support_bad⟩,
    fun e => nomatch e⟩
  dependence := dependence }

noncomputable def supportRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@designated_support) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str `D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorFamily.designated_support "__information_unit"
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorFamily.supportFamilyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨supportArena⟩
  objectArena := .source ⟨supportArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source supportArena ⟨supportFamilyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorFamily
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg", "fn"]
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def familyFamilyRegistration : Registration familyArena (type_of% @persistent_family) := {
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@persistent_family,bad,family_bad⟩
  sensitivity := ⟨fun i => ⟨bad,
    fun j hj => False.elim (hj (Subsingleton.elim j i)), rfl,family_bad⟩,
    fun e => nomatch e⟩
  dependence := dependence }

noncomputable def familyRegistration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@persistent_family) (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := Lean.Name.str `D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorFamily.persistent_family "__information_unit"
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorFamily.familyFamilyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨familyArena⟩
  objectArena := .source ⟨familyArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source familyArena ⟨familyFamilyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorFamily
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg", "fn"]
      stateBinder := 0, functionOperand := false, stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.NativeFreshSensorFamily
