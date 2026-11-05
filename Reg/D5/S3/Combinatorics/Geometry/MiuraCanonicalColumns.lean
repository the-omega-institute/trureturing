import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Geometry.MiuraCanonicalColumns
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

/-! Exact signed column maps as complete dependent readout families. -/
namespace Reg.D5.S3.Combinatorics.Geometry.MiuraCanonicalColumns
open _root_.D5.S3.Combinatorics.Geometry
open MiuraHeightEnvelope MiuraCoreColumns MiuraCoreContract MiuraCanonicalColumns
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

structure Parameter where
  m : ℕ
  n : ℕ
  hm : 0 < m
  j : Fin n
  k : Fin n

def line (n : ℕ) (c : ℤ) (v : Cell 1 n) : ℤ := (v.2.val : ℤ) + c

theorem line_height (n : ℕ) (c : ℤ) : IsHeight (line n c) := by
  intro p q hpq
  have hp : p.1.val = 0 := by have := p.1.isLt; omega
  have hq : q.1.val = 0 := by have := q.1.isLt; omega
  unfold adj gdist at hpq
  dsimp [line]
  rw [add_sub_add_right_eq_sub]
  simpa only [hp, hq, Int.cast_zero, Int.sub_self, Int.natAbs_zero,
    zero_add, Int.natCast_natAbs] using hpq

theorem line_frozen (c : ℤ) (j : Fin 5) (hj0 : 0 < j.val) (hj1 : j.val + 1 < 5) :
    frozenColumn (line 5 c) j := by
  refine ⟨hj0, hj1, ?_⟩
  intro i
  dsimp [line]
  rw [Int.ofNat_sub (by omega)]
  push_cast
  ring

namespace Left
abbrev State (p : Parameter) := {h : Cell p.m p.n → ℤ //
  IsHeight h ∧ frozenColumn h p.j ∧ frozenColumn h p.k ∧ p.j.val < p.k.val}

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Parameter State (fun p => Cell p.m (p.n - 1) → ℤ)

def actual : Realization signature :=
  realize signature (fun (_ : Unit) p x => contractAt x.val p.hm p.j x.property.2.1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ p (x : State p), frozenColumn (R.readout () p x) ⟨p.k.val - 1, by have := p.k.isLt; have := x.property.2.2.2; omega⟩

def rejected : Realization signature :=
  realize signature (fun (_ : Unit) p _ => fun v => (v.2.val : ℤ) ^ 2) (fun e => nomatch e)

abbrev lineParameter : Parameter := ⟨1, 5, by decide, ⟨1, by decide⟩, ⟨2, by decide⟩⟩

def lineState (c : ℤ) : State lineParameter :=
  ⟨line 5 c, line_height 5 c, line_frozen c _ (by decide) (by decide),
    line_frozen c _ (by decide) (by decide), by decide⟩

theorem actual_law : arena.Law actual := by
  intro p x
  exact frozen_after_left_deletion x.val x.property.1 p.hm p.j p.k
    x.property.2.1 x.property.2.2.1 x.property.2.2.2

theorem bridge : (type_of% (@frozen_after_left_deletion)) ↔ arena.Law actual := by
  constructor
  · intro h p x
    exact h x.val x.property.1 p.hm p.j p.k
      x.property.2.1 x.property.2.2.1 x.property.2.2.2
  · intro h m n src hh hm j k hj hk hrel
    exact h ⟨m, n, hm, j, k⟩ ⟨src, hh, hj, hk, hrel⟩

theorem rejected_not_law : ¬ arena.Law rejected := by
  intro h
  have he := h lineParameter (lineState 0)
  have hs := he.2.2 (0 : Fin 1)
  norm_num [rejected, realize, lineParameter] at hs

theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨lineParameter, lineState 0, lineState 1, ?_⟩
  intro he
  have hv := congrFun he ((0 : Fin 1), (0 : Fin 4))
  norm_num [actual, realize, lineState, lineParameter, contractAt, line] at hv

def registration : Registration arena (type_of% (@frozen_after_left_deletion)) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law, rejected, rejected_not_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_not_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@frozen_after_left_deletion)
    (type_of% (realize signature (fun (_ : Unit) p x => contractAt x.val p.hm p.j x.property.2.1)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Combinatorics.Geometry.MiuraCanonicalColumns.frozen_after_left_deletion.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Geometry.MiuraCanonicalColumns.Left.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun (_ : Unit) p x => contractAt x.val p.hm p.j x.property.2.1)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

end Left

namespace Right
abbrev State (p : Parameter) := {h : Cell p.m p.n → ℤ //
  IsHeight h ∧ frozenColumn h p.j ∧ frozenColumn h p.k ∧ p.k.val < p.j.val}

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Parameter State (fun p => Cell p.m (p.n - 1) → ℤ)

def actual : Realization signature :=
  realize signature (fun (_ : Unit) p x => contractAt x.val p.hm p.j x.property.2.1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ p (x : State p), frozenColumn (R.readout () p x) ⟨p.k.val, by have := x.property.2.1.2.1; have := x.property.2.2.2; omega⟩

def rejected : Realization signature :=
  realize signature (fun (_ : Unit) p _ => fun v => (v.2.val : ℤ) ^ 2) (fun e => nomatch e)

abbrev lineParameter : Parameter := ⟨1, 5, by decide, ⟨2, by decide⟩, ⟨1, by decide⟩⟩

def lineState (c : ℤ) : State lineParameter :=
  ⟨line 5 c, line_height 5 c, line_frozen c _ (by decide) (by decide),
    line_frozen c _ (by decide) (by decide), by decide⟩

theorem actual_law : arena.Law actual := by
  intro p x
  exact frozen_after_right_deletion x.val x.property.1 p.hm p.j p.k
    x.property.2.1 x.property.2.2.1 x.property.2.2.2

theorem bridge : (type_of% (@frozen_after_right_deletion)) ↔ arena.Law actual := by
  constructor
  · intro h p x
    exact h x.val x.property.1 p.hm p.j p.k
      x.property.2.1 x.property.2.2.1 x.property.2.2.2
  · intro h m n src hh hm j k hj hk hrel
    exact h ⟨m, n, hm, j, k⟩ ⟨src, hh, hj, hk, hrel⟩

theorem rejected_not_law : ¬ arena.Law rejected := by
  intro h
  have he := h lineParameter (lineState 0)
  have hs := he.2.2 (0 : Fin 1)
  norm_num [rejected, realize, lineParameter] at hs

theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨lineParameter, lineState 0, lineState 1, ?_⟩
  intro he
  have hv := congrFun he ((0 : Fin 1), (0 : Fin 4))
  norm_num [actual, realize, lineState, lineParameter, contractAt, line] at hv

def registration : Registration arena (type_of% (@frozen_after_right_deletion)) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law, rejected, rejected_not_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_not_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@frozen_after_right_deletion)
    (type_of% (realize signature (fun (_ : Unit) p x => contractAt x.val p.hm p.j x.property.2.1)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Combinatorics.Geometry.MiuraCanonicalColumns.frozen_after_right_deletion.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Geometry.MiuraCanonicalColumns.Right.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun (_ : Unit) p x => contractAt x.val p.hm p.j x.property.2.1)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

end Right

namespace Adjacent
abbrev State (p : Parameter) := {h : Cell p.m p.n → ℤ //
  IsHeight h ∧ frozenColumn h p.j ∧ frozenColumn h p.k ∧ p.j.val + 1 = p.k.val}

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Parameter State (fun p => (Cell p.m (p.n - 1) → ℤ) × (Cell p.m (p.n - 1) → ℤ))

def actual : Realization signature :=
  realize signature (fun (_ : Unit) p x => (contractAt x.val p.hm p.j x.property.2.1, contractAt x.val p.hm p.k x.property.2.2.1)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ p (x : State p), (R.readout () p x).1 = (R.readout () p x).2

def rejected : Realization signature :=
  realize signature (fun (_ : Unit) p _ => (fun _ => (0 : ℤ), fun _ => (1 : ℤ))) (fun e => nomatch e)

abbrev lineParameter : Parameter := ⟨1, 5, by decide, ⟨1, by decide⟩, ⟨2, by decide⟩⟩

def lineState (c : ℤ) : State lineParameter :=
  ⟨line 5 c, line_height 5 c, line_frozen c _ (by decide) (by decide),
    line_frozen c _ (by decide) (by decide), by decide⟩

theorem actual_law : arena.Law actual := by
  intro p x
  exact adjacent_deletions_equal x.val x.property.1 p.hm p.j p.k
    x.property.2.1 x.property.2.2.1 x.property.2.2.2

theorem bridge : (type_of% (@adjacent_deletions_equal)) ↔ arena.Law actual := by
  constructor
  · intro h p x
    exact h x.val x.property.1 p.hm p.j p.k
      x.property.2.1 x.property.2.2.1 x.property.2.2.2
  · intro h m n src hh hm j k hj hk hrel
    exact h ⟨m, n, hm, j, k⟩ ⟨src, hh, hj, hk, hrel⟩

theorem rejected_not_law : ¬ arena.Law rejected := by
  intro h
  have he := h lineParameter (lineState 0)
  have hv := congrFun he ((0 : Fin 1), (0 : Fin 4))
  norm_num [rejected, realize] at hv

theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨lineParameter, lineState 0, lineState 1, ?_⟩
  intro he
  have hv := congrFun (congrArg Prod.fst he) ((0 : Fin 1), (0 : Fin 4))
  norm_num [actual, realize, lineState, lineParameter, contractAt, line] at hv

def registration : Registration arena (type_of% (@adjacent_deletions_equal)) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law, rejected, rejected_not_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_not_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@adjacent_deletions_equal)
    (type_of% (realize signature (fun (_ : Unit) p x => (contractAt x.val p.hm p.j x.property.2.1, contractAt x.val p.hm p.k x.property.2.2.1))
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Combinatorics.Geometry.MiuraCanonicalColumns.adjacent_deletions_equal.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Geometry.MiuraCanonicalColumns.Adjacent.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun (_ : Unit) p x => (contractAt x.val p.hm p.j x.property.2.1, contractAt x.val p.hm p.k x.property.2.2.1))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

end Adjacent

namespace Commute
abbrev State (p : Parameter) := {h : Cell p.m p.n → ℤ //
  IsHeight h ∧ frozenColumn h p.j ∧ frozenColumn h p.k ∧ p.j.val < p.k.val}

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Parameter State (fun p => (Cell p.m (p.n - 1 - 1) → ℤ) × (Cell p.m (p.n - 1 - 1) → ℤ))

def actual : Realization signature :=
  realize signature (fun (_ : Unit) p x => (contractAt (contractAt x.val p.hm p.j x.property.2.1) p.hm
      ⟨p.k.val - 1, by have := p.k.isLt; have := x.property.2.2.2; omega⟩
      (frozen_after_left_deletion x.val x.property.1 p.hm p.j p.k
        x.property.2.1 x.property.2.2.1 x.property.2.2.2), contractAt (contractAt x.val p.hm p.k x.property.2.2.1) p.hm
      ⟨p.j.val, by have := x.property.2.2.1.2.1; have := x.property.2.2.2; omega⟩
      (frozen_after_right_deletion x.val x.property.1 p.hm p.k p.j
        x.property.2.2.1 x.property.2.1 x.property.2.2.2))) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ p (x : State p), (R.readout () p x).1 = (R.readout () p x).2

def rejected : Realization signature :=
  realize signature (fun (_ : Unit) p _ => (fun _ => (0 : ℤ), fun _ => (1 : ℤ))) (fun e => nomatch e)

abbrev lineParameter : Parameter := ⟨1, 5, by decide, ⟨1, by decide⟩, ⟨3, by decide⟩⟩

def lineState (c : ℤ) : State lineParameter :=
  ⟨line 5 c, line_height 5 c, line_frozen c _ (by decide) (by decide),
    line_frozen c _ (by decide) (by decide), by decide⟩

theorem actual_law : arena.Law actual := by
  intro p x
  exact separated_deletions_commute x.val x.property.1 p.hm p.j p.k
    x.property.2.1 x.property.2.2.1 x.property.2.2.2

theorem bridge : (type_of% (@separated_deletions_commute)) ↔ arena.Law actual := by
  constructor
  · intro h p x
    exact h x.val x.property.1 p.hm p.j p.k
      x.property.2.1 x.property.2.2.1 x.property.2.2.2
  · intro h m n src hh hm j k hj hk hrel
    exact h ⟨m, n, hm, j, k⟩ ⟨src, hh, hj, hk, hrel⟩

theorem rejected_not_law : ¬ arena.Law rejected := by
  intro h
  have he := h lineParameter (lineState 0)
  have hv := congrFun he ((0 : Fin 1), (0 : Fin 3))
  norm_num [rejected, realize] at hv

theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨lineParameter, lineState 0, lineState 1, ?_⟩
  intro he
  have hv := congrFun (congrArg Prod.fst he) ((0 : Fin 1), (0 : Fin 3))
  norm_num [actual, realize, lineState, lineParameter, contractAt, line] at hv

def registration : Registration arena (type_of% (@separated_deletions_commute)) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law, rejected, rejected_not_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_not_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@separated_deletions_commute)
    (type_of% (realize signature (fun (_ : Unit) p x => (contractAt (contractAt x.val p.hm p.j x.property.2.1) p.hm
      ⟨p.k.val - 1, by have := p.k.isLt; have := x.property.2.2.2; omega⟩
      (frozen_after_left_deletion x.val x.property.1 p.hm p.j p.k
        x.property.2.1 x.property.2.2.1 x.property.2.2.2), contractAt (contractAt x.val p.hm p.k x.property.2.2.1) p.hm
      ⟨p.j.val, by have := x.property.2.2.1.2.1; have := x.property.2.2.2; omega⟩
      (frozen_after_right_deletion x.val x.property.1 p.hm p.k p.j
        x.property.2.2.1 x.property.2.1 x.property.2.2.2)))
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Combinatorics.Geometry.MiuraCanonicalColumns.separated_deletions_commute.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Geometry.MiuraCanonicalColumns.Commute.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun (_ : Unit) p x => (contractAt (contractAt x.val p.hm p.j x.property.2.1) p.hm
      ⟨p.k.val - 1, by have := p.k.isLt; have := x.property.2.2.2; omega⟩
      (frozen_after_left_deletion x.val x.property.1 p.hm p.j p.k
        x.property.2.1 x.property.2.2.1 x.property.2.2.2), contractAt (contractAt x.val p.hm p.k x.property.2.2.1) p.hm
      ⟨p.j.val, by have := x.property.2.2.1.2.1; have := x.property.2.2.2; omega⟩
      (frozen_after_right_deletion x.val x.property.1 p.hm p.k p.j
        x.property.2.2.1 x.property.2.1 x.property.2.2.2)))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

end Commute

end
end Reg.D5.S3.Combinatorics.Geometry.MiuraCanonicalColumns
