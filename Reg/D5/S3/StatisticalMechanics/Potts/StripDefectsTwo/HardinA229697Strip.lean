import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripData
import D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripData
import D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697Strip
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697Strip
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697Strip
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697StripData
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229589StripData (Row horizontal between)
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
attribute [local irreducible] T initial terminal W cl
namespace Recurrence
/- signature: proof_shape=bind-only; consumers=readout,rejected,arena,family,audit -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)
/- readout: proof_shape=bind-only; consumers=family,audit -/
def readout : Realization signature := realize signature (fun _ _ n => a n) (fun e => nomatch e)
/- rejected: proof_shape=bind-only; consumers=rejected_law,family -/
def rejected : Realization signature := realize signature (fun _ _ n => a n + 1) (fun e => nomatch e)
/- arena: proof_shape=bind-only; consumers=rejected_law,family,audit -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ),
    (R.readout () () (n + 18) : ℤ) = 27 * R.readout () () (n + 17) - 288 * R.readout () () (n + 16) + 1557 * R.readout () () (n + 15) - 4644 * R.readout () () (n + 14) + 8073 * R.readout () () (n + 13) - 8343 * R.readout () () (n + 12) + 5022 * R.readout () () (n + 11) - 1620 * R.readout () () (n + 10) + 216 * R.readout () () (n + 9)
/- rejected_at: proof_shape=bind-only; consumers=rejected_law -/
private theorem rejected_at (h : arena.Law rejected) (n : ℕ) : False := by
  have hb := h n
  have ha := result n
  simp only [rejected, realize, Nat.cast_add, Nat.cast_one] at hb
  linarith
/- rejected_law: proof_shape=bind-only; consumers=family -/
private theorem rejected_law : ¬ arena.Law rejected := fun h => rejected_at h 0
/- count_zero: proof_shape=bind-only; consumers=family -/
private theorem count_zero : a 0 = 0 := by
  unfold a
  decide +kernel
/- count_two_pos: proof_shape=bind-only; consumers=family -/
private theorem count_two_pos : 0 < a 2 := by
  unfold a
  unfold _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical.Canonical
  apply Finset.card_pos.mpr
  refine ⟨(fun x => ![![0, 0], ![0, 1], ![0, 1], ![0, 1]] x.1 x.2), ?_⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, by decide +kernel⟩
/- family: proof_shape=bind-only; consumers=audit -/
def family : Registration arena (type_of% @result) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 2, ?_⟩
    change a 0 ≠ a 2
    rw [count_zero]
    exact Nat.ne_of_lt count_two_pos

/- audit: proof_shape=bind-only; consumers=LeanInformationAudit registration extraction -/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229697Strip.Recurrence.auditUnit
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
  readout := some (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697Strip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Recurrence

namespace FiniteCertificate
/- signature: proof_shape=bind-only; consumers=readout,rejected,arena,family,audit -/
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 42) (fun _ => Fin 42 → ℤ)
/- readout: proof_shape=bind-only; consumers=family,audit -/
def readout : Realization signature := realize signature (fun _ _ r s => T r s) (fun e => nomatch e)
/- rejected: proof_shape=bind-only; consumers=rejected_law,family -/
def rejected : Realization signature := realize signature (fun _ _ r s => T r s + 1) (fun e => nomatch e)
/- arena: proof_shape=bind-only; consumers=rejected_law,family,audit -/
abbrev arena : Arena where
  signature := signature
  Law R :=     (∀ p (d : Fin 3), Valid p d.val →
      terminal (cl p d.val) = (if d.val = 0 then 1 else 0)) ∧
    (∀ p (d : Fin 3), Valid p d.val → ∀ r : Row,
      bondDefects between p r + bondDefects horizontal r r ≤ d.val →
      Valid r (d.val - (bondDefects between p r + bondDefects horizontal r r))) ∧
    (∀ p (d : Fin 3), Valid p d.val → ∀ s : Fin 42,
      (∑ r : Row, if bondDefects between p r + bondDefects horizontal r r ≤ d.val ∧
        cl r (d.val - (bondDefects between p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = (fun r s => R.readout () () r s) (cl p d.val) s) ∧
    (∀ r : Row, bondDefects horizontal r r ≤ 2 → Valid r (2 - bondDefects horizontal r r)) ∧
    (∀ s : Fin 42, (∑ r : Row, if bondDefects horizontal r r ≤ 2 ∧
      cl r (2 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s) ∧
    (W 0 = initial ∧ ∀ i : Fin 17, W i.succ = Matrix.vecMul (W i.castSucc) (fun r s => R.readout () () r s)) ∧
    W 17 = ∑ j : Fin 9, (![216, -1620, 5022, -8343, 8073, -4644, 1557, -288, 27] j : ℤ) • W ⟨8 + j.val, by omega⟩
/- rejected_law: proof_shape=bind-only; consumers=family -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h.2.2.1 ![0, 0, 0, 0] ⟨2, by decide⟩ (by decide +kernel) 0
  have ha := finite_certificate.2.2.1 ![0, 0, 0, 0] ⟨2, by decide⟩ (by decide +kernel) 0
  change _ = T (cl ![0, 0, 0, 0] 2) 0 + 1 at hb
  try simp only [Fin.val_zero] at ha hb
  linarith
/- family: proof_shape=bind-only; consumers=audit -/
def family : Registration arena (type_of% @finite_certificate) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨finite_certificate, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have he := congrFun h 0
    exact (by decide +kernel : T 0 0 ≠ T 1 0) he
/- audit: proof_shape=bind-only; consumers=LeanInformationAudit registration extraction -/
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@finite_certificate) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229697Strip.finite_certificate.auditUnit
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
  readout := some (realize signature (fun _ _ r s => T r s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697Strip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "fn", "arg", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end FiniteCertificate

end
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsTwo.HardinA229697Strip
