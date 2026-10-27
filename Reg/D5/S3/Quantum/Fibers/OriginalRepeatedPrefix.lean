import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fibers.OriginalRepeatedPrefix
import Reg.Support.DependentFamily

/-! Source-bound registration attempt for the actual all-n survival construction. -/
noncomputable section
open D5.S3.Quantum.Fibers
open D5.S3.Quantum.Fibers.OriginalControlComposition
open D5.S3.Quantum.Fibers.OriginalMarkedConcatenation
open D5.S3.Quantum.Fibers.OriginalRepeatedPrefix
open D5.S3.Quantum.Fibers.OriginalRepeatedPrefix.Band
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set
namespace Reg.D5.S3.Quantum.Fibers.OriginalRepeatedPrefix
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option relaxedAutoImplicit false

structure Input where
  band : Band
  count : ℕ
  positive : 1 ≤ count

abbrev signature : Signature where
  Params := Unit
  State := fun _ => Input
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def value (i : Fin 2) (d : Input) : ℝ := if i=0 then
  survival d.band.c (d.band.early d.count d.positive) 2 else
  survival d.band.c (d.band.late d.count d.positive) 2
def actual : Realization signature := realize signature
  (fun i _ d => value i d) (fun e => nomatch e)
def changed (i : Fin 2) : Realization signature := realize signature
  (fun j _ d => if j=i then 0 else value j d) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law obs := ∀ (B : Band) (n : ℕ) (hn : 1 ≤ n) (chi : ℝ),
    0 < B.q ∧ B.q < 1 ∧
    OriginalControl (B.c,B.c,1-2*B.c) 2 (B.early n hn) (fun _ => chi) ∧
    OriginalControl (B.c,B.c,1-2*B.c) 2 (B.late n hn) (fun _ => chi) ∧
    AbsolutelyContinuousOnInterval (B.early n hn) 0 2 ∧
    AbsolutelyContinuousOnInterval (B.late n hn) 0 2 ∧
    (∀ t ∈ Icc (0:ℝ) 1,
      B.early n hn t=B.repeated (halfStep n) (by unfold halfStep; positivity) n t ∧
      B.late n hn t=B.repeated (halfStep n) (by unfold halfStep; positivity) n t) ∧
    B.early n hn 2=B.a ∧ B.late n hn 2=B.a ∧
    obs.readout 0 () ⟨B,n,hn⟩=B.q^(n+1) ∧
    obs.readout 1 () ⟨B,n,hn⟩=B.q^(n+1) ∧
    B.early n hn (5/4)=B.b ∧ B.late n hn (5/4)=B.a

private theorem actual_law : arena.Law actual := by
  intro B n hn chi
  simpa only [actual,realize,value,ite_eq_left rfl,ite_eq_right (by decide : (1:Fin 2)≠0)]
    using early_late_native_survival B n hn chi

private def sample : Band :=
  ⟨1/8,1/4,3/8,by norm_num,by norm_num,by norm_num,by norm_num⟩

private theorem value_pow (i : Fin 2) (B : Band) (n : ℕ) (hn : 1 ≤ n) :
    value i ⟨B,n,hn⟩=B.q^(n+1) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,he,hl,_,_⟩ := early_late_native_survival B n hn 0
  fin_cases i
  · simpa only [value,ite_eq_left rfl] using he
  · simpa only [value,ite_eq_right (by decide : (1:Fin 2)≠0)] using hl

private theorem changed_fails (i : Fin 2) : ¬ arena.Law (changed i) := by
  intro h
  obtain ⟨hq,_,_,_,_,_,_,_,_,he,hl,_,_⟩ := h sample 1 (by omega) 0
  fin_cases i
  · change 0=sample.q^(1+1) at he
    exact (ne_of_gt (pow_pos hq 2)) he.symm
  · change 0=sample.q^(1+1) at hl
    exact (ne_of_gt (pow_pos hq 2)) hl.symm

private theorem changed_other (i j : Fin 2) (hj : j≠i) (param : Unit) (d : Input) :
    actual.readout j param d=(changed i).readout j param d := by
  simp [actual,changed,realize,hj]

def registration : Registration arena (type_of% (@early_late_native_survival)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law,changed 0,changed_fails 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨changed i,?_,rfl,changed_fails i⟩
      intro j hj
      funext param d
      exact changed_other i j hj param d
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨(),⟨sample,1,by omega⟩,⟨sample,2,by omega⟩,?_⟩
    intro he
    change value i ⟨sample,1,by omega⟩=value i ⟨sample,2,by omega⟩ at he
    rw [value_pow,value_pow] at he
    obtain ⟨hq0,hq1,_⟩ := early_late_native_survival sample 1 (by omega) 0
    have hlt : sample.q^3 < sample.q^2 := by
      simpa only [pow_succ,mul_one] using
        mul_lt_mul_of_pos_left hq1 (pow_pos hq0 2)
    exact (ne_of_lt hlt) he.symm

noncomputable def registration_1 : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@early_late_native_survival)
    (type_of% (realize signature (fun i _ d => value i d) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Fibers.OriginalRepeatedPrefix.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.OriginalRepeatedPrefix.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun i _ d => value i d) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fibers.OriginalRepeatedPrefix
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","arg","arg","arg","arg",
        "arg","arg","arg","arg","arg","fn","arg","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false },{
      path := #["body","body","body","body","arg","arg","arg","arg",
        "arg","arg","arg","arg","arg","arg","fn","arg","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Quantum.Fibers.OriginalRepeatedPrefix
