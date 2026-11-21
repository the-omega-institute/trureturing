import D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635State
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Observations of state counts, relabelling and remaining-budget laws. -/

namespace Reg.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635State

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635State
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229584StripData (Row)
open scoped BigOperators

noncomputable section

set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace CountClasses

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Row → Option State) (fun _ => State) (fun _ => ℤ)

private def observation : ∀ role p, signature.State p → signature.Output role p :=
  (fun _ f s => (((List.ofFn rowEquiv).filterMap f).count s : ℤ))

private def actual : Realization signature :=
  realize signature observation (fun e => nomatch e)

private def altered : Realization signature :=
  realize signature (fun _ p k => observation () p k + 1) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (f : Row → Option State) (s : State),
    R.readout () f s = ∑ r : Row, if f r = some s then (1 : ℤ) else 0

private theorem rejected : ¬ arena.Law altered := by
  intro h
  have wrong := h (fun _ => some 0) 0
  have right := count_classes (fun _ => some 0) 0
  dsimp only [altered, realize, observation] at wrong
  omega

def family : Registration arena (type_of% @count_classes) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨count_classes, altered, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual altered rejected
  dependence := by
    intro role
    refine ⟨(fun _ => some 0), 0, 1, ?_⟩
    change observation () (fun _ => some 0) 0 ≠ observation () (fun _ => some 0) 1
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@count_classes) (Realization signature) Type Unit where
  unitName := `Reg.HardinA229635State.count_classes.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature observation (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635State
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CountClasses

namespace HRelabel

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Row) (fun _ => ℕ)

private def observation : ∀ role p, signature.State p → signature.Output role p :=
  (fun _ _ p => h p)

private def actual : Realization signature :=
  realize signature observation (fun e => nomatch e)

private def altered : Realization signature :=
  realize signature (fun _ p k => observation () p k + 1) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (e : Equiv.Perm (Fin 3)) (p : Row), h (e ∘ p) = R.readout () () p

private theorem rejected : ¬ arena.Law altered := by
  intro h
  have wrong := h (Equiv.refl _) (![0, 1, 0, 1, 0, 1] : Row)
  have right := h_relabel (Equiv.refl _) (![0, 1, 0, 1, 0, 1] : Row)
  dsimp only [altered, realize, observation] at wrong
  omega

def family : Registration arena (type_of% @h_relabel) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨h_relabel, altered, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual altered rejected
  dependence := by
    intro role
    refine ⟨(), (![0, 1, 0, 1, 0, 1] : Row), (![0, 0, 0, 0, 0, 0] : Row), ?_⟩
    change observation () () (![0, 1, 0, 1, 0, 1] : Row) ≠ observation () () (![0, 0, 0, 0, 0, 0] : Row)
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@h_relabel) (Realization signature) Type Unit where
  unitName := `Reg.HardinA229635State.h_relabel.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature observation (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635State
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end HRelabel

namespace CostRelabel

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Row (fun _ => Row) (fun _ => ℕ)

private def observation : ∀ role p, signature.State p → signature.Output role p :=
  (fun _ p r => cost p r)

private def actual : Realization signature :=
  realize signature observation (fun e => nomatch e)

private def altered : Realization signature :=
  realize signature (fun _ p k => observation () p k + 1) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (e : Equiv.Perm (Fin 3)) (p r : Row),
    cost (e ∘ p) (e ∘ r) = R.readout () p r

private theorem rejected : ¬ arena.Law altered := by
  intro h
  have wrong := h (Equiv.refl _) (![0, 1, 0, 1, 0, 1] : Row) (![0, 1, 0, 1, 0, 1] : Row)
  have right := cost_relabel (Equiv.refl _) (![0, 1, 0, 1, 0, 1] : Row) (![0, 1, 0, 1, 0, 1] : Row)
  dsimp only [altered, realize, observation] at wrong
  omega

def family : Registration arena (type_of% @cost_relabel) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cost_relabel, altered, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual altered rejected
  dependence := by
    intro role
    refine ⟨(![0, 1, 0, 1, 0, 1] : Row), (![0, 1, 0, 1, 0, 1] : Row), (![0, 0, 0, 0, 0, 0] : Row), ?_⟩
    change observation () (![0, 1, 0, 1, 0, 1] : Row) (![0, 1, 0, 1, 0, 1] : Row) ≠ observation () (![0, 1, 0, 1, 0, 1] : Row) (![0, 0, 0, 0, 0, 0] : Row)
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@cost_relabel) (Realization signature) Type Unit where
  unitName := `Reg.HardinA229635State.cost_relabel.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature observation (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635State
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CostRelabel

namespace ClRelabel

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Row (fun _ => ℕ) (fun _ => State)

private def observation : ∀ role p, signature.State p → signature.Output role p :=
  (fun _ p d => cl p d)

private def actual : Realization signature :=
  realize signature observation (fun e => nomatch e)

private def altered : Realization signature :=
  realize signature (fun _ p _ => cl p 2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (e : Equiv.Perm (Fin 3)) (p : Row) (d : ℕ),
    cl (e ∘ p) d = R.readout () p d

private theorem rejected : ¬ arena.Law altered := by
  intro h
  have wrong := h (Equiv.refl _) (![0, 1, 0, 1, 0, 1] : Row) 0
  change cl (![0, 1, 0, 1, 0, 1] : Row) 0 = cl (![0, 1, 0, 1, 0, 1] : Row) 2 at wrong
  exact (by decide +kernel : cl (![0, 1, 0, 1, 0, 1] : Row) 0 ≠ cl (![0, 1, 0, 1, 0, 1] : Row) 2) wrong

def family : Registration arena (type_of% @cl_relabel) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cl_relabel, altered, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual altered rejected
  dependence := by
    intro role
    refine ⟨(![0, 1, 0, 1, 0, 1] : Row), 0, 2, ?_⟩
    change cl (![0, 1, 0, 1, 0, 1] : Row) 0 ≠ cl (![0, 1, 0, 1, 0, 1] : Row) 2
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@cl_relabel) (Realization signature) Type Unit where
  unitName := `Reg.HardinA229635State.cl_relabel.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature observation (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635State
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ClRelabel

namespace Legal

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Row (fun _ => Row) (fun _ => ℕ)

private def observation : ∀ role p, signature.State p → signature.Output role p :=
  (fun _ p r => cost p r)

private def actual : Realization signature :=
  realize signature observation (fun e => nomatch e)

private def altered : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Row) (d : ℕ), Valid p d → ∀ (r : Row), cost p r ≤ d →
    Valid r (d - R.readout () p r)

private theorem rejected : ¬ arena.Law altered := by
  intro h
  have wrong := h (![0, 1, 0, 1, 0, 1] : Row) 2 (by unfold Valid; decide +kernel)
    (![1, 1, 0, 1, 0, 1] : Row) (by decide +kernel)
  exact (by unfold Valid; decide +kernel : ¬ Valid (![1, 1, 0, 1, 0, 1] : Row) 2) wrong

def family : Registration arena (type_of% @legal) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨legal, altered, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual altered rejected
  dependence := by
    intro role
    refine ⟨(![0, 1, 0, 1, 0, 1] : Row), (![0, 1, 0, 1, 0, 1] : Row), (![1, 1, 0, 1, 0, 1] : Row), ?_⟩
    change cost (![0, 1, 0, 1, 0, 1] : Row) (![0, 1, 0, 1, 0, 1] : Row) ≠ cost (![0, 1, 0, 1, 0, 1] : Row) (![1, 1, 0, 1, 0, 1] : Row)
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@legal) (Realization signature) Type Unit where
  unitName := `Reg.HardinA229635State.legal.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature observation (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635State
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Legal

namespace Closed

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Row) (fun _ => ℕ)

private def observation : ∀ role p, signature.State p → signature.Output role p :=
  (fun _ _ r => h r)

private def actual : Realization signature :=
  realize signature observation (fun e => nomatch e)

private def altered : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p r : Row) (d : ℕ), h p + d ≤ 1 → cost p r ≤ d →
    R.readout () () r + (d - cost p r) ≤ 1

private theorem rejected : ¬ arena.Law altered := by
  intro hfalse
  have wrong := hfalse (![0, 1, 0, 1, 0, 1] : Row) (![0, 1, 0, 1, 0, 1] : Row) 0 (by decide +kernel) (by decide +kernel)
  change 2 + (0 - cost (![0, 1, 0, 1, 0, 1] : Row) (![0, 1, 0, 1, 0, 1] : Row)) ≤ 1 at wrong
  omega

def family : Registration arena (type_of% @closed) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨closed, altered, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual altered rejected
  dependence := by
    intro role
    refine ⟨(), (![0, 1, 0, 1, 0, 1] : Row), (![1, 1, 0, 1, 0, 1] : Row), ?_⟩
    change h (![0, 1, 0, 1, 0, 1] : Row) ≠ h (![1, 1, 0, 1, 0, 1] : Row)
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@closed) (Realization signature) Type Unit where
  unitName := `Reg.HardinA229635State.closed.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature observation (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635State
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Closed

namespace LegalStart

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Row) (fun _ => ℕ)

private def observation : ∀ role p, signature.State p → signature.Output role p :=
  (fun _ _ r => h r)

private def actual : Realization signature :=
  realize signature observation (fun e => nomatch e)

private def altered : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (r : Row), h r ≤ 2 → Valid r (2 - R.readout () () r)

private theorem rejected : ¬ arena.Law altered := by
  intro hfalse
  have wrong := hfalse (![0, 0, 0, 1, 0, 1] : Row) (by decide +kernel)
  exact (by unfold Valid; decide +kernel : ¬ Valid (![0, 0, 0, 1, 0, 1] : Row) 2) wrong

def family : Registration arena (type_of% @legal_start) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨legal_start, altered, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual altered rejected
  dependence := by
    intro role
    refine ⟨(), (![0, 1, 0, 1, 0, 1] : Row), (![1, 1, 0, 1, 0, 1] : Row), ?_⟩
    change h (![0, 1, 0, 1, 0, 1] : Row) ≠ h (![1, 1, 0, 1, 0, 1] : Row)
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@legal_start) (Realization signature) Type Unit where
  unitName := `Reg.HardinA229635State.legal_start.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature observation (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635State
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LegalStart


end

end Reg.D5.S3.StatisticalMechanics.Potts.CrossedStripDefectsWide.P5b.HardinA229635State
