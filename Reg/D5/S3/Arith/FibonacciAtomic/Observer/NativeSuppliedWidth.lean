import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Arith.FibonacciAtomic.Observer.NativeSuppliedWidth

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSuppliedWidth
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSuppliedWidth
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

private def small : Source := .mul (.of true) (.of true)
private def big : Source := Nat.rec (.of true) (fun _ z => .mul z z) 8
private theorem small_even : small.length%2=0 := by decide
private theorem big_even : big.length%2=0 := by decide
private theorem large_capacity (n : Nat) (bound : 258 ≤ n) : 11 ≤ capacity n := by
  have cap := (_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciActiveTable.native_fibonacci_active_table
    (n-1) (fun _ => []) 0).1
  change n-1+1 ≤ Nat.fib (capacity n+2) at cap
  by_contra h
  have mono := Nat.fib_mono (show capacity n+2 ≤ 12 by omega)
  norm_num at mono
  omega

private theorem dimension_small :
    _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciActiveTable.dimension 1=1 ∧
    _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciActiveTable.dimension 2=2 := by
  have c1 := _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciActiveTable.native_fibonacci_active_table 1 (fun _ => []) 0
  have c2 := _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciActiveTable.native_fibonacci_active_table 2 (fun _ => []) 0
  have a : _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciActiveTable.dimension 1 ≤ 1 := by
    by_contra h
    have no := c1.2.1 1 (by omega)
    norm_num at no
  have b : _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciActiveTable.dimension 2 ≤ 2 := by
    by_contra h
    have no := c2.2.1 2 (by omega)
    norm_num at no
  have cap1 := c1.1
  have cap2 := c2.1
  clear c1 c2
  constructor
  · have lower : 1 ≤ _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciActiveTable.dimension 1 := by
      by_contra low
      have zero : _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciActiveTable.dimension 1=0 := by omega
      rw [zero] at cap1
      norm_num at cap1
    omega
  · have lower : 2 ≤ _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciActiveTable.dimension 2 := by
      by_contra low
      have mono := Nat.fib_mono (show _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciActiveTable.dimension 2+2 ≤ 3 by omega)
      norm_num at mono
      omega
    omega

abbrev upperSignature := Reg.Support.SingleDependentReadout.signature Source (fun _ => Nat) (fun _ => Nat)
def upperActual : Realization upperSignature := realize upperSignature
  (fun _ S T => _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciActiveTable.dimension
    (S.length*((T+1)/2+1))+7) (fun e => nomatch e)
def upperBad : Realization upperSignature := realize upperSignature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev upperArena : Arena where
  signature := upperSignature
  Law R := ∀ (S : Source) (T : Nat), S.length%2=0 →
    Feasible S T (_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciActiveTable.dimension S.length+7) ∧
      StaticFeasible S T (R.readout () S T)
private theorem upper_negative : ¬ upperArena.Law upperBad := by
  intro law
  obtain ⟨I,_,_⟩ := (law small 0 small_even).2
  exact (by omega : ¬ (0 < 0)) I.positive
def upperEvidence : Registration upperArena (type_of% (@native_upper_members)) where
  actual := upperActual
  bridge := Iff.rfl
  variation := ⟨native_upper_members,upperBad,upper_negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ upper_negative
  dependence := by
    intro i
    cases i
    refine ⟨.of true,0,2,?_⟩
    change _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciActiveTable.dimension 1+7 ≠
      _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciActiveTable.dimension 2+7
    rw [dimension_small.1,dimension_small.2]
    omega

abbrev minSignature := Reg.Support.SingleDependentReadout.signature Unit (fun _ => Source) (fun _ => Nat)
def minActual : Realization minSignature := realize minSignature
  (fun _ _ S => capacity (S.length+2)) (fun e => nomatch e)
def minBad : Realization minSignature := realize minSignature (fun _ _ _ => 100) (fun e => nomatch e)
abbrev minArena : Arena where
  signature := minSignature
  Law R := ∀ (S : Source) (T : Nat) (even : S.length%2=0),
    let a := activeMinimum S T even
    let s := staticMinimum S T even
    let K := (T+1)/2
    let M := S.length*(K+1)
    let r := (T+3)/3
    Feasible S T a ∧ (∀ w, Feasible S T w → a ≤ w) ∧
    StaticFeasible S T s ∧ (∀ w, StaticFeasible S T w → s ≤ w) ∧
    R.readout () () S ≤ a ∧ a ≤ capacity (S.length+1)+7 ∧
    capacity (S.length+1)+7 ≤ capacity (S.length+2)+7 ∧
    capacity (S.length*r+2) ≤ s ∧ s ≤ capacity (M+1)+7 ∧
    capacity (M+1)+7 ≤ capacity (S.length*r+2)+9
private theorem min_negative : ¬ minArena.Law minBad := by
  intro law
  have lower := (law small 0 small_even).2.2.2.2.1
  have upper := (minimum_width_bounds small 0 small_even).2.2.2.2.2.1
  change 100 ≤ activeMinimum small 0 small_even at lower
  change activeMinimum small 0 small_even ≤
    _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciActiveTable.dimension 2+7 at upper
  rw [dimension_small.2] at upper
  omega
def minEvidence : Registration minArena (type_of% (@minimum_width_bounds)) where
  actual := minActual
  bridge := Iff.rfl
  variation := ⟨minimum_width_bounds,minBad,min_negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ min_negative
  dependence := by
    intro i
    cases i
    refine ⟨(),.of true,big,?_⟩
    change capacity 3 ≠ capacity (big.length+2)
    have lo := large_capacity (big.length+2) (by decide)
    change _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeFibonacciActiveTable.dimension 2 ≠ _
    rw [dimension_small.2]
    omega

abbrev logSignature := Reg.Support.SingleDependentReadout.signature Unit (fun _ => Source) (fun _ => ℝ)
def logActual : Realization logSignature := realize logSignature
  (fun _ _ S => Real.logb Real.goldenRatio S.length) (fun e => nomatch e)
def logBad : Realization logSignature := realize logSignature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev logArena : Arena where
  signature := logSignature
  Law R := ∀ (S : Source) (T : Nat) (even : S.length%2=0),
    |(activeMinimum S T even : ℝ)-R.readout () () S| ≤ 10 ∧
    |(staticMinimum S T even : ℝ)-Real.logb Real.goldenRatio (S.length*(T+1) : Nat)| ≤ 10
private theorem log_negative : ¬ logArena.Law logBad := by
  intro law
  have bad := (law big 0 big_even).1
  change |(activeMinimum big 0 big_even : ℝ)-0| ≤ 10 at bad
  have lower := (minimum_width_bounds big 0 big_even).2.2.2.2.1
  have len : big.length = 256 := by decide
  rw [len] at lower
  have cap := large_capacity 258 le_rfl
  have high : 11 ≤ activeMinimum big 0 big_even := cap.trans lower
  have cast : (11 : ℝ) ≤ activeMinimum big 0 big_even := by exact_mod_cast high
  rw [sub_zero,abs_of_nonneg (by positivity)] at bad
  linarith
def logEvidence : Registration logArena (type_of% (@uniform_logarithmic_width)) where
  actual := logActual
  bridge := Iff.rfl
  variation := ⟨uniform_logarithmic_width,logBad,log_negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ log_negative
  dependence := by
    intro i
    cases i
    refine ⟨(),.of true,small,?_⟩
    intro eq
    have same : (0 : ℝ) = Real.logb Real.goldenRatio 2 := by
      simpa [logActual,realize,small] using eq
    have pos := Real.logb_pos Real.one_lt_goldenRatio (by norm_num : (1 : ℝ) < 2)
    linarith

def upperRegistration : Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0} (@native_upper_members) (Realization upperSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSuppliedWidth.native_upper_members.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSuppliedWidth.upperEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨upperArena⟩
  objectArena := .source ⟨upperArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source upperArena ⟨upperEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize upperSignature upperActual.readout upperActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSuppliedWidth
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","arg","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms upperEvidence
#print axioms upperRegistration

def minRegistration : Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0} (@minimum_width_bounds) (Realization minSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSuppliedWidth.minimum_width_bounds.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSuppliedWidth.minEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨minArena⟩
  objectArena := .source ⟨minArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source minArena ⟨minEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize minSignature minActual.readout minActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSuppliedWidth
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","arg","arg","arg","arg","fn","arg","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms minEvidence
#print axioms minRegistration

def logRegistration : Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0} (@uniform_logarithmic_width) (Realization logSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSuppliedWidth.uniform_logarithmic_width.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSuppliedWidth.logEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨logArena⟩
  objectArena := .source ⟨logArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source logArena ⟨logEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize logSignature logActual.readout logActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSuppliedWidth
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","fn","arg","fn","arg","arg","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms logEvidence
#print axioms logRegistration

end
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSuppliedWidth
