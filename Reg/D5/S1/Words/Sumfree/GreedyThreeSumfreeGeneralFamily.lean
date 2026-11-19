import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Sumfree.GreedyThreeSumfreeGeneralFamily
import Reg.Support.DependentFamily
namespace Reg.D5.S1.Words.Sumfree.GreedyThreeSumfreeGeneralFamily
open _root_.D5.S1.Words.Sumfree.GreedyThreeSumfreeGeneralFamily
open _root_.D5.S1.Words.Sumfree.GreedyThreeSumfreeTwoParameter (RestrictedThreeSum)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section

namespace sum
abbrev signature : Signature where
  Params := Nat × Nat × Nat × Nat
  State _ := Nat → Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {f g d z : Nat} (hf : 1 ≤ f) (hg : f < g) (hd : 2 ≤ d) (ha : d+1 ≤ f+g)
    (hex : f ≠ 1 ∨ g ≠ 2 ∨ d ≠ 2) , R.readout () (f,g,d,z) (A f g d) ↔ g+d < z ∧ z ∉ A f g d
def rejected : Realization signature := realize signature (fun _ _ _ => True) (fun e => Empty.elim e)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h := h (f:=3) (g:=7) (d:=6) (z:=0) (by omega) (by omega) (by omega) (by omega) (by omega)
  exact (Nat.not_lt_zero _ (h.mp trivial).1)
def source_registration : Registration arena (type_of% (@_root_.D5.S1.Words.Sumfree.GreedyThreeSumfreeGeneralFamily.restricted_three_sum_eq_complement)) where
  actual := realize signature (fun _ p P => RestrictedThreeSum P p.2.2.2) (fun e => Empty.elim e)
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.Sumfree.GreedyThreeSumfreeGeneralFamily.restricted_three_sum_eq_complement,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(3,7,6,6), (fun n => n=1 ∨ n=2 ∨ n=3), (fun _ => False), ?_⟩
    intro he
    change RestrictedThreeSum (fun n => n=1 ∨ n=2 ∨ n=3) 6 = RestrictedThreeSum (fun _ => False) 6 at he
    have hx : RestrictedThreeSum (fun n => n=1 ∨ n=2 ∨ n=3) 6 :=
      ⟨1,2,3,by omega,by omega,by simp,by simp,by simp,rfl⟩
    have hn : RestrictedThreeSum (fun _ => False) 6 := he ▸ hx
    obtain ⟨x,y,w,hxy,hyw,hx,hy,hw,hs⟩ := hn
    exact hx
def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.Sumfree.GreedyThreeSumfreeGeneralFamily.restricted_three_sum_eq_complement) (Realization signature) Unit Unit := {
  unitName := `D5.S1.Words.Sumfree.GreedyThreeSumfreeGeneralFamily.restricted_three_sum_eq_complement.__information_unit
  realizationName := `Reg.D5.S1.Words.Sumfree.GreedyThreeSumfreeGeneralFamily.sum.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p P => RestrictedThreeSum P p.2.2.2) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Sumfree.GreedyThreeSumfreeGeneralFamily
    definition := none
    coordinates := #[0,1,2,3]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","arg"]
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms source_registration
#print axioms audit
end sum

namespace range
abbrev signature : Signature where
  Params := Nat × Nat × Nat
  State _ := Nat → Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {f g d : Nat} (hf : 1 ≤ f) (hg : f < g) (hd : 2 ≤ d) (ha : d+1 ≤ f+g)
    (hex : f ≠ 1 ∨ g ≠ 2 ∨ d ≠ 2) , R.readout () (f,g,d) (S f g d)
def rejected : Realization signature := realize signature (fun _ _ _ => False) (fun e => Empty.elim e)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h := h (f:=3) (g:=7) (d:=6) (by omega) (by omega) (by omega) (by omega) (by omega)
  exact h
def source_registration : Registration arena (type_of% (@_root_.D5.S1.Words.Sumfree.GreedyThreeSumfreeGeneralFamily.s_eq_A)) where
  actual := realize signature (fun _ p P => P = A p.1 p.2.1 p.2.2) (fun e => Empty.elim e)
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.Sumfree.GreedyThreeSumfreeGeneralFamily.s_eq_A,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(3,7,6), A 3 7 6, (fun _ => False), ?_⟩
    intro he
    change (A 3 7 6 = A 3 7 6) = ((fun _ : Nat => False) = A 3 7 6) at he
    have hn : (fun _ : Nat => False) = A 3 7 6 := he ▸ rfl
    have ha : A 3 7 6 3 := Or.inl (Or.inl (Or.inl rfl))
    rw [← hn] at ha
    exact ha
def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.Sumfree.GreedyThreeSumfreeGeneralFamily.s_eq_A) (Realization signature) Unit Unit := {
  unitName := `D5.S1.Words.Sumfree.GreedyThreeSumfreeGeneralFamily.s_eq_A.__information_unit
  realizationName := `Reg.D5.S1.Words.Sumfree.GreedyThreeSumfreeGeneralFamily.range.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p P => P = A p.1 p.2.1 p.2.2) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Sumfree.GreedyThreeSumfreeGeneralFamily
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","arg"]
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms source_registration
#print axioms audit
end range

namespace period
abbrev signature : Signature where
  Params := Nat × Nat × Nat × Nat × Nat
  State _ := Nat → Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {f g d : Nat} (hf : 1 ≤ f) (hg : f < g) (hd : 2 ≤ d) (ha : d+1 ≤ f+g)
    (hex : f ≠ 1 ∨ g ≠ 2 ∨ d ≠ 2) (q N : Nat) (hq : 0 < q), R.readout () (f,g,d,q,N) (S f g d) ↔ (3*f+5*g+2*d-3) ∣ q ∧ f+2*g+d-1 ≤ N
def rejected : Realization signature := realize signature (fun _ _ _ => True) (fun e => Empty.elim e)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h := h (f:=3) (g:=7) (d:=6) (by omega) (by omega) (by omega) (by omega) (by omega) 1 0 (by omega)
  have hh := (h.mp trivial).2
  omega
def source_registration : Registration arena (type_of% (@_root_.D5.S1.Words.Sumfree.GreedyThreeSumfreeGeneralFamily.characteristic_periods)) where
  actual := realize signature (fun _ p P => PeriodFrom P p.2.2.2.1 (p.2.2.2.2+1)) (fun e => Empty.elim e)
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Words.Sumfree.GreedyThreeSumfreeGeneralFamily.characteristic_periods,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(3,7,6,1,0), (fun _ => True), (fun n => n=1), ?_⟩
    intro he
    change PeriodFrom (fun _ => True) 1 1 = PeriodFrom (fun n => n=1) 1 1 at he
    have ht : PeriodFrom (fun _ => True) 1 1 := by intro n hn; trivial
    have hn : PeriodFrom (fun n => n=1) 1 1 := he ▸ ht
    have hc := (hn 1 (by omega)).mpr rfl
    omega
def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Words.Sumfree.GreedyThreeSumfreeGeneralFamily.characteristic_periods) (Realization signature) Unit Unit := {
  unitName := `D5.S1.Words.Sumfree.GreedyThreeSumfreeGeneralFamily.characteristic_periods.__information_unit
  realizationName := `Reg.D5.S1.Words.Sumfree.GreedyThreeSumfreeGeneralFamily.period.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p P => PeriodFrom P p.2.2.2.1 (p.2.2.2.2+1)) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Sumfree.GreedyThreeSumfreeGeneralFamily
    definition := none
    coordinates := #[0,1,2,8,9]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","fn","arg"]
      booleanPredicate := false}] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms source_registration
#print axioms audit
end period

end
end Reg.D5.S1.Words.Sumfree.GreedyThreeSumfreeGeneralFamily
