import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import Reg.D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds
import D5.S3.Arith.FibonacciAtomic.Observer.NativeSuppliedWidth

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSuppliedComparison
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply readout)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds (Controller Run literal queries halts)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeActiveParityExecution (chartOf source labels bit)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSuppliedComparison
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

private theorem small_correct : Correct CombLiteralInstallationBounds.small (.of true) 0 := by
  intro x t ht
  have tz : t = 0 := by omega
  subst t
  have src : source (chartOf (.of true)) x = .of (!(x ⟨0,by decide⟩)) := by
    change _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeActiveParityExecution.atom (bit (x (0 : Fin 1))) = .of (!(x (0 : Fin 1)))
    cases h : x (0 : Fin 1) <;>
      simp [_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeActiveParityExecution.atom,bit,h,
        _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport.substitution]

  have target : _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeActiveParityExecution.parity
      (labels x) 1 = x ⟨0,by decide⟩ := by
    simp [_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeActiveParityExecution.parity,labels]
  have c := CombLiteralInstallationBounds.small_correct (.of (!(x ⟨0,by decide⟩))) rfl 0 le_rfl
  rw [src]
  refine ⟨c.1,?_⟩
  intro qs updates f b run
  have out := c.2 qs updates f b run
  change b = _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeActiveParityExecution.parity (labels x) 1
  rw [target]
  simpa [_root_.D5.S3.Arith.FibonacciAtomic.Observer.CombLiteralInstallationBounds.parity] using out

abbrev countSignature := Reg.Support.SingleDependentReadout.signature Unit (fun _ => Source) (fun _ => Nat)
def countActual : Realization countSignature := realize countSignature (fun _ _ S => S.length) (fun e => nomatch e)
def countBad : Realization countSignature := realize countSignature (fun _ _ _ => 2) (fun e => nomatch e)
abbrev installedArena : Arena where
  signature := countSignature
  Law R := ∀ {E : Type} [Fintype E] {M : Controller E} {S : Source} {T : Nat},
    Correct M S T → R.readout () () S ≤ (queries M).card ∧
      2 ≤ (halts M).card ∧ S.length+2 ≤ Fintype.card E
private theorem installed_negative : ¬ installedArena.Law countBad := by
  intro law
  have bad := (law small_correct).1
  change 2 ≤ (queries CombLiteralInstallationBounds.small).card at bad
  rw [CombLiteralInstallationBounds.small_queries] at bad
  omega
def installedEvidence : Registration installedArena (type_of% (@installed_lower_bound)) where
  actual := countActual
  bridge := Iff.rfl
  variation := ⟨@installed_lower_bound,countBad,installed_negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ installed_negative
  dependence := by intro i; cases i; exact ⟨(),.of true,.mul (.of true) (.of true),by change (1 : Nat) ≠ 2; omega⟩

abbrev staticArena : Arena where
  signature := countSignature
  Law R := ∀ {E : Type} [Fintype E] {M : Controller E} {S : Source} {T : Nat},
    Correct M S T → Static M S T → R.readout () () S*((T+3)/3) ≤ (queries M).card ∧
      S.length*((T+3)/3)+2 ≤ Fintype.card E
private theorem small_static : Static CombLiteralInstallationBounds.small (.of true) 0 := by
  intro x t ht qs updates f b run
  have tz : t = 0 := by omega
  subst t
  apply CombLiteralInstallationBounds.small_static _ _ 0 le_rfl qs updates f b run
  change (_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeActiveParityExecution.atom (bit (x (0 : Fin 1)))).length = 1
  cases h : x (0 : Fin 1) <;>
    simp [_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeActiveParityExecution.atom,bit,h,
      _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport.substitution]

private theorem static_negative : ¬ staticArena.Law countBad := by
  intro law
  have bad := (law small_correct small_static).1
  change 2*((0+3)/3) ≤ (queries CombLiteralInstallationBounds.small).card at bad
  rw [CombLiteralInstallationBounds.small_queries] at bad
  omega
def staticEvidence : Registration staticArena (type_of% (@static_installed_lower_bound)) where
  actual := countActual
  bridge := Iff.rfl
  variation := ⟨@static_installed_lower_bound,countBad,static_negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ static_negative
  dependence := by intro i; cases i; exact ⟨(),.of true,.mul (.of true) (.of true),by change (1 : Nat) ≠ 2; omega⟩

abbrev rawParams := Σ E : Type, Controller E
abbrev rawSignature : Signature where
  Params := rawParams
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Address
  Anchor := Empty
  finiteAnchor := inferInstance
def rawActual : Realization rawSignature := realize rawSignature
  (fun _ p e => literal p.2 e) (fun e => nomatch e)
def rawBad : Realization rawSignature := realize rawSignature (fun _ _ _ => []) (fun e => nomatch e)
abbrev rawArena : Arena where
  signature := rawSignature
  Law R := ∀ {E : Type} {M : Controller E} {S : Source} {T : Nat}, Correct M S T →
    ∀ (x : Fin S.length → Bool) {t : Nat}, t ≤ T →
    ∀ {qs : List (E × Nat)} {updates : Nat} {f : E} {b : Bool},
    Run M (source (chartOf S) x) M.initial t qs updates f b →
    ∃ pick : Fin S.length → E, Function.Injective pick ∧
      ∀ i, ∃ epoch, (pick i,epoch) ∈ qs ∧
        ((chartOf S).address i).IsPrefix (R.readout () ⟨E,M⟩ (pick i)) ∧
        readout (literal M (pick i)) (substitution^[epoch] (source (chartOf S) x)) ≠
          readout (literal M (pick i)) (substitution^[epoch]
            (source (chartOf S) (Function.update x i (!(x i)))))
private theorem raw_negative : ¬ rawArena.Law rawBad := by
  intro law
  let S : Source := .mul (.of true) (.of true)
  obtain ⟨I,correct⟩ := (_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSuppliedWidth.native_upper_members S 0 (by decide)).1
  obtain ⟨qs,updates,f,b,run⟩ := (correct (fun _ => false) 0 le_rfl).1
  obtain ⟨pick,_,sep⟩ := law correct (fun _ => false) le_rfl run
  obtain ⟨epoch,_,pre,_⟩ := sep ⟨0,by decide⟩
  change [false].IsPrefix [] at pre
  simpa using pre
def rawEvidence : Registration rawArena (type_of% (@same_run_distinct_queries)) where
  actual := rawActual
  bridge := Iff.rfl
  variation := ⟨@same_run_distinct_queries,rawBad,raw_negative⟩
  sensitivity := ⟨fun i => ⟨rawBad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,raw_negative⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    cases i
    let M : Controller Bool := ⟨false,fun b => .read [b] (fun _ => b)⟩
    refine ⟨⟨Bool,M⟩,false,true,?_⟩
    change [false] ≠ [true]
    decide

def installedRegistration : Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0} (@installed_lower_bound) (Realization countSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSuppliedComparison.installed_lower_bound.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSuppliedComparison.installedEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨installedArena⟩
  objectArena := .source ⟨installedArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source installedArena ⟨installedEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize countSignature countActual.readout countActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSuppliedComparison
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","fn","arg","fn","arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms installedEvidence
#print axioms installedRegistration

def staticRegistration : Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0} (@static_installed_lower_bound) (Realization countSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSuppliedComparison.static_installed_lower_bound.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSuppliedComparison.staticEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨staticArena⟩
  objectArena := .source ⟨staticArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source staticArena ⟨staticEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize countSignature countActual.readout countActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSuppliedComparison
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","fn","arg","fn","arg","fn","arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms staticEvidence
#print axioms staticRegistration

def rawRegistration : Contract.Registration.{1,0,1,0,0,0,1,0,0,0,0,0} (@same_run_distinct_queries) (Realization rawSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSuppliedComparison.same_run_distinct_queries.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSuppliedComparison.rawEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨rawArena⟩
  objectArena := .source ⟨rawArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rawArena ⟨rawEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rawSignature rawActual.readout rawActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSuppliedComparison
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","body","arg","body","arg","body","arg","body","arg","fn","arg","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms rawEvidence
#print axioms rawRegistration

end
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSuppliedComparison
