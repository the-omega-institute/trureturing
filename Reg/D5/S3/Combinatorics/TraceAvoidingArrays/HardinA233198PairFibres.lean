import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198PairFibres
import Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198LiteralModel
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Whole-family readouts of the literal complementary-pair fibre counts. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198PairFibres

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198PairFibres
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

attribute [local irreducible] a fibreCount

namespace TwoColours

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => ordinaryCount 2 n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => ordinaryCount 2 n + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n, 0 < n → R.readout () () n = if n = 1 then 2 else 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 1 (by decide)
  have ha := ordinary_two_count 1 (by decide)
  change ordinaryCount 2 1 + 1 = (if (1 : ℕ) = 1 then 2 else 0) at hb
  norm_num at hb ha
  omega

def family : Registration arena (type_of% @ordinary_two_count) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@ordinary_two_count, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    change ordinaryCount 2 1 ≠ ordinaryCount 2 2
    rw [ordinary_two_count 1 (by decide), ordinary_two_count 2 (by decide)]
    decide

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@ordinary_two_count) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198PairFibres.TwoColours.unit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198PairFibres.TwoColours.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => ordinaryCount 2 n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198PairFibres
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TwoColours

namespace ThreeColours

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => ordinaryCount 3 n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => ordinaryCount 3 n + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n, 0 < n → R.readout () () n = if n = 1 then 24 else 6

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 1 (by decide)
  have ha := ordinary_three_count 1 (by decide)
  change ordinaryCount 3 1 + 1 = (if (1 : ℕ) = 1 then 24 else 6) at hb
  norm_num at hb ha
  omega

def family : Registration arena (type_of% @ordinary_three_count) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@ordinary_three_count, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 1, 2, ?_⟩
    change ordinaryCount 3 1 ≠ ordinaryCount 3 2
    rw [ordinary_three_count 1 (by decide), ordinary_three_count 2 (by decide)]
    decide

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@ordinary_three_count) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198PairFibres.ThreeColours.unit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198PairFibres.ThreeColours.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => ordinaryCount 3 n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198PairFibres
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ThreeColours

namespace FourSeries

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ)
    (fun _ => PowerSeries ℚ)

def actual : Realization signature :=
  realize signature (fun _ _ q => ordinarySeries q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ q => ordinarySeries q + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () 4 =
    (108 * PowerSeries.X ^ 1 - 528 * PowerSeries.X ^ 2 +
      960 * PowerSeries.X ^ 3 - 1200 * PowerSeries.X ^ 4) *
    (1 - 12 * PowerSeries.X ^ 1 + 40 * PowerSeries.X ^ 2 -
      68 * PowerSeries.X ^ 3 + 64 * PowerSeries.X ^ 4)⁻¹

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := congrArg (PowerSeries.coeff 0) h
  have ha := congrArg (PowerSeries.coeff 0) ordinary_series_four
  change PowerSeries.coeff 0 (ordinarySeries 4 + 1) = _ at hb
  have hm : PowerSeries.coeff 0 (ordinarySeries 4 + 1) =
      PowerSeries.coeff 0 (ordinarySeries 4) + 1 := by simp
  rw [hm] at hb
  linarith

def family : Registration arena (type_of% @ordinary_series_four) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨ordinary_series_four, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 2, 3, ?_⟩
    change ordinarySeries 2 ≠ ordinarySeries 3
    intro he
    have hh := congrArg (PowerSeries.coeff 1) he
    simp only [ordinarySeries, PowerSeries.coeff_mk, if_neg (by decide : ¬ (1 : ℕ) = 0)] at hh
    rw [ordinary_two_count 1 (by decide), ordinary_three_count 1 (by decide)] at hh
    norm_num at hh

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@ordinary_series_four) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198PairFibres.FourSeries.unit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198PairFibres.FourSeries.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ q => ordinarySeries q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198PairFibres
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FourSeries





namespace LiteralSeries

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Unit →₀ ℕ)
    (fun _ => ℚ)

def actual : Realization signature :=
  realize signature (fun _ _ d => A d) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ d => A d + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := (fun d => R.readout () () d : PowerSeries ℚ) = numerator * denominator⁻¹

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := congrArg (PowerSeries.coeff 0) h
  have ha := congrArg (PowerSeries.coeff 0) generating_function
  change A (Finsupp.single () 0) + 1 = _ at hb
  change A (Finsupp.single () 0) = _ at ha
  linarith

def family : Registration arena (type_of% @generating_function) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨generating_function, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    cases i
    refine ⟨(), 0, Finsupp.single () 1, ?_⟩
    change A 0 ≠ A (Finsupp.single () 1)
    rw [show (0 : Unit →₀ ℕ) = Finsupp.single () 0 by simp]
    change PowerSeries.coeff 0 A ≠ PowerSeries.coeff 1 A
    simp only [A, PowerSeries.coeff_mk]
    norm_num only [ite_true, ite_false, Nat.cast_zero, ne_eq]
    exact_mod_cast LiteralCount.positive_one.ne

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@generating_function) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198PairFibres.LiteralSeries.unit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198PairFibres.LiteralSeries.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ d => A d) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198PairFibres
    definition := some {
      owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198PairFibres
      name := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198PairFibres.GeneratingFunction
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LiteralSeries

end

end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233198PairFibres
