import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Readout registrations for the ladder generating function, initial coefficients and shared scanner. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
  (Seen allowed advance good finish)
open _root_.D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)
open LeanInformationAudit PowerSeries

noncomputable section

attribute [local irreducible] a

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => a n + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (1 - 8 * X) * (1 - 24 * X - 256 * X ^ 2 + 1024 * X ^ 3) *
      (PowerSeries.mk fun n => (R.readout () () n : ℤ)) =
        X * (11 - 272 * X - 576 * X ^ 2 + 20992 * X ^ 3 - 53248 * X ^ 4)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change (1 - 8 * X) * (1 - 24 * X - 256 * X ^ 2 + 1024 * X ^ 3) *
    (PowerSeries.mk fun n => ((a n + 1 : ℕ) : ℤ)) =
      X * (11 - 272 * X - 576 * X ^ 2 + 20992 * X ^ 3 - 53248 * X ^ 4) at h
  have h0 := finite_certificate.1
  have hb := congrArg (PowerSeries.coeff 0) h
  simpa [PowerSeries.coeff_mul, Nat.cast_add, h0] using hb

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change a 0 ≠ a 1
    intro h
    have hh := congrArg (fun n : ℕ => (n : ℤ)) h
    linarith [finite_certificate.1, finite_certificate.2.1]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "arg", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

namespace InitialCoefficients

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => a n + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (R.readout () () 0 : ℤ) = 0 ∧
    (R.readout () () 1 : ℤ) = 11 ∧
    (R.readout () () 2 : ℤ) = 80 ∧
    (R.readout () () 3 : ℤ) = 2688 ∧
    (R.readout () () 4 : ℤ) = 78336 ∧
    (R.readout () () 5 : ℤ) = 2469888 ∧
    (R.readout () () 6 : ℤ) = 76447744 ∧
    (R.readout () () 7 : ℤ) = 2385772544 ∧
    (R.readout () () 8 : ℤ) = 74291609600 ∧
    (R.readout () () 9 : ℤ) = 2315406802944 ∧
    (R.readout () () 10 : ℤ) = 72144847372288 ∧
    (R.readout () () 11 : ℤ) = 2248141575290880

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h.1
  change ((a 0 + 1 : ℕ) : ℤ) = 0 at hb
  have ha := finite_certificate.1
  simp only [Nat.cast_add, Nat.cast_one] at hb
  linarith

def family : Registration arena (type_of% @finite_certificate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finite_certificate, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change a 0 ≠ a 1
    intro h
    have hh := congrArg (fun n : ℕ => (n : ℤ)) h
    linarith [finite_certificate.1, finite_certificate.2.1]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@finite_certificate) (Realization signature) Type Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder.InitialCoefficients.auditUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder.InitialCoefficients.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end InitialCoefficients

namespace AdvanceSeen

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 3)
    (fun _ => Fin 6) (fun _ => Seen)

def actual : Realization signature :=
  realize signature (fun _ s x => advance (seen s) x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (true, true)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (s : Fin 3) (x : Fin 6), allowed (seen s) x →
    R.readout () s x = seen (next s x)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 0 (by decide +kernel)
  change (true, true) = seen (next 0 0) at hh
  revert hh
  decide +kernel

def family : Registration arena (type_of% @advance_seen) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@advance_seen, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, 1, ?_⟩
    change advance (seen 0) 0 ≠ advance (seen 0) 1
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@advance_seen) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder.AdvanceSeen.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder.AdvanceSeen.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ s x => advance (seen s) x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end AdvanceSeen

namespace NextMono

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 3)
    (fun _ => Fin 6) (fun _ => Fin 3)

def actual : Realization signature :=
  realize signature (fun _ s x => next s x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (s : Fin 3) (x : Fin 6), s ≤ R.readout () s x

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 0
  change (1 : Fin 3) ≤ 0 at hh
  revert hh
  decide +kernel

def family : Registration arena (type_of% @next_mono) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@next_mono, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, 2, ?_⟩
    change next 0 0 ≠ next 0 2
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@next_mono) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder.NextMono.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder.NextMono.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ s x => next s x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end NextMono

namespace LabelNext

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 3)
    (fun _ => Fin 6) (fun _ => Fin 3)

def actual : Realization signature :=
  realize signature (fun _ s x => next s x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (s : Fin 3) (x : Fin 6), allowed (seen s) x →
    beta x ≤ R.readout () s x

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 1 (by decide +kernel)
  change beta 1 ≤ (0 : Fin 3) at hh
  revert hh
  decide +kernel

def family : Registration arena (type_of% @label_next) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@label_next, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, 2, ?_⟩
    change next 0 0 ≠ next 0 2
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@label_next) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder.LabelNext.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder.LabelNext.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ s x => next s x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end LabelNext

namespace EndLevelMono

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Sigma (fun {n : ℕ} => Fin 3))
    (fun p => Fin p.1 → Fin 6) (fun _ => Fin 3)

def actual : Realization signature :=
  realize signature (fun _ p f => endLevel p.2 f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (s : Fin 3) (f : Fin n → Fin 6),
    s ≤ R.readout () ⟨n, s⟩ f

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (n := 0) 1 (fun i => Fin.elim0 i)
  change (1 : Fin 3) ≤ 0 at hh
  revert hh
  decide +kernel

def family : Registration arena (type_of% @endLevel_mono) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@endLevel_mono, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨⟨1, 0⟩, (fun _ => 0), (fun _ => 2), ?_⟩
    change endLevel 0 (fun _ : Fin 1 => (0 : Fin 6)) ≠
      endLevel 0 (fun _ : Fin 1 => (2 : Fin 6))
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@endLevel_mono) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder.EndLevelMono.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder.EndLevelMono.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p f => endLevel p.2 f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end EndLevelMono

namespace FinishSeen

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Sigma (fun {n : ℕ} => Fin 3))
    (fun p => Fin p.1 → Fin 6) (fun _ => Seen)

def actual : Realization signature :=
  realize signature (fun _ p f => finish (seen p.2) f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (true, true)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (s : Fin 3) (f : Fin n → Fin 6)
    (_h : good (seen s) f), R.readout () ⟨n, s⟩ f = seen (endLevel s f)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (n := 0) 0 (fun i => Fin.elim0 i) (by trivial)
  change (true, true) = seen (endLevel 0 (fun i : Fin 0 => Fin.elim0 i)) at hh
  revert hh
  decide +kernel

def family : Registration arena (type_of% @finish_seen) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finish_seen, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨⟨1, 0⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    change finish (seen 0) (fun _ : Fin 1 => (0 : Fin 6)) ≠
      finish (seen 0) (fun _ : Fin 1 => (1 : Fin 6))
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@finish_seen) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder.FinishSeen.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder.FinishSeen.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p f => finish (seen p.2) f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end FinishSeen

namespace WeightedSum

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (List ℕ)
    (fun _ => ℕ → ℤ) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ es g => ((es.flatMap fun e => List.replicate (e % 9) (e / 9)).map g).sum) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (es : List ℕ) (g : ℕ → ℤ), R.readout () es g =
    (es.map fun e => ((e % 9 : ℕ) : ℤ) * g (e / 9)).sum

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h [10] (fun _ => 1)
  change (0 : ℤ) = 1 at hh
  exact (by decide : (0 : ℤ) ≠ 1) hh

def family : Registration arena (type_of% @weighted_sum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weighted_sum, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨[10], (fun _ => 0), (fun _ => 1), ?_⟩
    change (0 : ℤ) ≠ 1
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@weighted_sum) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder.WeightedSum.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder.WeightedSum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ es g => ((es.flatMap fun e => List.replicate (e % 9) (e / 9)).map g).sum) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder
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

#print axioms audit

end WeightedSum

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder
