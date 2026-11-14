import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233261Literal
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Literal six-row array counts as exact dependent-family laws. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233261Literal
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233261Literal
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
attribute [local irreducible] a L
namespace Bridge
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℤ)
def actual : Realization signature :=
  realize signature (fun _ _ n => (64 : ℤ)^n) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ n => (64 : ℤ)^n + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ}, 2 ≤ n → 48 * (a n : ℤ) =
    R.readout () () n * ((L n : ℤ) + 6)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := counting_bridge (n := 2) (by decide)
  have hb := h (n := 2) (by decide)
  change 48 * (a 2 : ℤ) = ((64 : ℤ)^2+1) * ((L 2 : ℤ)+6) at hb
  have hL : (0 : ℤ) ≤ (L 2 : ℤ) := Int.natCast_nonneg _
  norm_num only [show (64 : ℤ)^2 = 4096 from rfl] at ha hb
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
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233261Literal.Bridge.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233261Literal.Bridge.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => (64 : ℤ)^n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233261Literal
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
  Law R := ∀ (n : ℤ), 16 < n →
    R.readout () () n = 1984*(a (n-1).toNat : ℤ) -
    1282048*(a (n-2).toNat : ℤ) +
    346292224*(a (n-3).toNat : ℤ) -
    27028094976*(a (n-4).toNat : ℤ) -
    6584184864768*(a (n-5).toNat : ℤ) +
    1907721393668096*(a (n-6).toNat : ℤ) -
    214149680718675968*(a (n-7).toNat : ℤ) +
    12624715655426342912*(a (n-8).toNat : ℤ) -
    384499321786383466496*(a (n-9).toNat : ℤ) +
    4759259971017064316928*(a (n-10).toNat : ℤ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ha := result 17 (by decide)
  have hb := h 17 (by decide)
  change (a 17 : ℤ)+1 = _ at hb
  norm_num at ha hb
  linarith only [ha,hb]
private theorem count_bound (n : ℕ) : a n ≤ 6 ^ (6 * n) := by
  unfold a
  calc
    _ ≤ (Finset.univ : Finset (Fin 6 × Fin n → Fin 6)).card := Finset.card_filter_le _ _
    _ = 6 ^ (6 * n) := by simp
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 4, ?_⟩
  have hsmall : a 1 ≤ 46656 := count_bound 1
  have hs : (a 1 : ℤ) ≤ 46656 := by exact_mod_cast hsmall
  have hb := counting_bridge (n := 4) (by decide)
  have hL : (0 : ℤ) ≤ (L 4 : ℤ) := Int.natCast_nonneg _
  change (a 1 : ℤ) ≠ (a 4 : ℤ)
  norm_num only [show (64 : ℤ)^4 = 16777216 from rfl] at hb
  intro he
  rw [he] at hs
  linarith only [hs, hb, hL]

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233261Literal.Result.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233261Literal.Result.family
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
  escapeFrom := some ℤ
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233261Literal
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

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233261Literal
