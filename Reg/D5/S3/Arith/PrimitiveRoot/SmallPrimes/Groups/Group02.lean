import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Groups.Group02
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! The source readout is the exact order target at each odd-slot index. -/
noncomputable section
open _root_.D5.S3.Arith.PrimitiveRoot.SmallPrimes
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Arith.PrimitiveRoot.SmallPrimes.Groups.Group02

abbrev signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℕ) (fun _ => ℕ)
def actual : Realization signature :=
  realize signature (fun _ _ k => 1310723 + 2 * k - 1) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ k : ℕ, k < 327680 → (1310723 + 2 * k).Prime →
    ∃ q : ℕ, q.Prime ∧ q < 1310723 + 2 * k ∧
      orderOf (q : ZMod (1310723 + 2 * k)) = R.readout () () k
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp : (1310723 : ℕ).Prime := by norm_num
  let : Fact (1310723 : ℕ).Prime := ⟨hp⟩
  obtain ⟨q, hq, hlt, ho⟩ := h 0 (by decide) hp
  have hz : (q : ZMod 1310723) ≠ 0 := by
    intro hz
    have hd : 1310723 ∣ q := (CharP.cast_eq_zero_iff (ZMod 1310723) 1310723 q).mp hz
    exact Nat.not_dvd_of_pos_of_lt hq.pos hlt hd
  have hd := ZMod.orderOf_dvd_card_sub_one hz
  have hn := Nat.pos_of_dvd_of_pos hd (by decide : 0 < 1310723 - 1)
  have he : orderOf (q : ZMod 1310723) = 0 := ho
  omega
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩
def family : Registration arena (type_of% @group02_sound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@group02_sound, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@group02_sound) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.PrimitiveRoot.SmallPrimes.group02_sound.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.SmallPrimes.Groups.Group02.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ k => 1310723 + 2 * k - 1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.SmallPrimes.Groups.Group02
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end Reg.D5.S3.Arith.PrimitiveRoot.SmallPrimes.Groups.Group02
