import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Observer.Separation.BooleanRankThreeK4
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Registrations for the shared word scanner and the pair-label bond criterion. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStripReadouts

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
open _root_.D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace FinishFirst

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℕ × Seen)
    (fun p => Fin p.1 → Fin 6) (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ p f => (finish p.2 f).1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (s : Seen) (f : Fin n → Fin 6),
    R.readout () (n, s) f = true ↔ s.1 = true ∨ ∃ i, f i = 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 (true, true) (fun i => Fin.elim0 i)
  simpa [rejected, realize] using hh

def family : Registration arena (type_of% @finish_fst) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finish_fst, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(1, (false, false)), (fun _ => 0), (fun _ => 1), ?_⟩
    change (finish (false, false) (fun _ : Fin 1 => (0 : Fin 6))).1 ≠
      (finish (false, false) (fun _ : Fin 1 => (1 : Fin 6))).1
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@finish_fst) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStripReadouts.FinishFirst.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStripReadouts.FinishFirst.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p f => (finish p.2 f).1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end FinishFirst

namespace FinishSecond

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℕ × Seen)
    (fun p => Fin p.1 → Fin 6) (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ p f => (finish p.2 f).2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (s : Seen) (f : Fin n → Fin 6),
    R.readout () (n, s) f = true ↔ s.2 = true ∨ ∃ i, f i = 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 (true, true) (fun i => Fin.elim0 i)
  simpa [rejected, realize] using hh

def family : Registration arena (type_of% @finish_snd) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finish_snd, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(1, (false, false)), (fun _ => 0), (fun _ => 2), ?_⟩
    change (finish (false, false) (fun _ : Fin 1 => (0 : Fin 6))).2 ≠
      (finish (false, false) (fun _ : Fin 1 => (2 : Fin 6))).2
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@finish_snd) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStripReadouts.FinishSecond.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStripReadouts.FinishSecond.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p f => (finish p.2 f).2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end FinishSecond

namespace GoodCriterion

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℕ × Seen)
    (fun p => Fin p.1 → Fin 6) (fun _ => Prop)

def actual : Realization signature :=
  realize signature (fun _ p f => good p.2 f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (s : Seen) (f : Fin n → Fin 6),
    R.readout () (n, s) f ↔ ∀ i,
      ((f i = 2 ∨ f i = 3 ∨ f i = 4) → s.1 = true ∨ ∃ j, j < i ∧ f j = 1) ∧
      (f i = 3 → s.2 = true ∨ ∃ j, j < i ∧ f j = 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 (false, false) (fun i => Fin.elim0 i)
  simpa [rejected, realize] using hh

def family : Registration arena (type_of% @good_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@good_iff, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(1, (false, false)), (fun _ => 0), (fun _ => 2), ?_⟩
    simp [actual, realize, good, allowed]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@good_iff) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStripReadouts.GoodCriterion.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStripReadouts.GoodCriterion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p f => good p.2 f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end GoodCriterion

namespace PairBonds

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Col (fun _ => Col) (fun _ => Prop)

def actual : Realization signature :=
  realize signature (fun _ c d => ∀ r, beta (d r) ≠ beta (c 0) ∧ beta (d r) ≠ beta (c 1))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => True) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ c d : Col,
    (∀ r s, c r ≠ d s ∧ (c r).val + (d s).val ≠ 5) ↔ R.readout () c d

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (fun _ => 0) (fun _ => 0)
  simpa [rejected, realize] using hh

def family : Registration arena (type_of% @edge_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨edge_iff, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(fun _ => 0), (fun _ => 0), (fun _ => 1), ?_⟩
    simp [actual, realize, beta]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@edge_iff) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStripReadouts.PairBonds.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStripReadouts.PairBonds.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ c d => ∀ r, beta (d r) ≠ beta (c 0) ∧ beta (d r) ≠ beta (c 1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end PairBonds

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStripReadouts
