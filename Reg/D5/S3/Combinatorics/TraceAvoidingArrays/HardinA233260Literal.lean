import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
attribute [local irreducible] a L
namespace Bridge
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ n => (32 : ℤ)^n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => (32 : ℤ)^n + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ}, 2 ≤ n → 48 * (a n : ℤ) =
    R.readout () () n * ((L n : ℤ) + 6)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := counting_bridge (n := 2) (by decide)
  have hb := h (n := 2) (by decide)
  change 48 * (a 2 : ℤ) = ((32 : ℤ)^2+1) * ((L 2 : ℤ)+6) at hb
  have hL : (0 : ℤ) ≤ (L 2 : ℤ) := Int.natCast_nonneg _
  norm_num only [show (32 : ℤ)^2 = 1024 from rfl] at ha hb
  nlinarith only [ha, hb, hL]
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 2, 3, ?_⟩
  norm_num [actual, realize]
def family : Registration arena (type_of% @counting_bridge) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@counting_bridge, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@counting_bridge) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal.Bridge.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal.Bridge.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (32 : ℤ)^n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Bridge

namespace Result
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℤ) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ n => (a n.toNat : ℤ)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => (a n.toNat : ℤ)+1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℤ), 11 < n →
    R.readout () () n = 512*(a (n-1).toNat : ℤ) - 65536*(a (n-2).toNat : ℤ) +
    2490368*(a (n-3).toNat : ℤ) + 17825792*(a (n-4).toNat : ℤ) -
    2818572288*(a (n-5).toNat : ℤ) + 51539607552*(a (n-6).toNat : ℤ) -
    274877906944*(a (n-7).toNat : ℤ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := result 12 (by decide)
  have hb := h 12 (by decide)
  change (a 12 : ℤ)+1 = _ at hb
  norm_num only [Int.reduceSub, Int.reduceToNat] at ha hb
  linarith only [ha,hb]
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), -1, 1, ?_⟩
  have hzero : a 0 = 0 := by unfold a; decide +kernel
  have hpos : 0 < a 1 := by
    unfold a
    apply Finset.card_pos.mpr
    refine ⟨(fun _ => 0), ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    decide +kernel
  change (a 0 : ℤ) ≠ (a 1 : ℤ)
  exact_mod_cast (by omega : a 0 ≠ a 1)
def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal.Result.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal.Result.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (a n.toNat : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Result

end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
