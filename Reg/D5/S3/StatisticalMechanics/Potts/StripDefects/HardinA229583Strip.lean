import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583Strip
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583StripData
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Readout registrations for exact defective-strip counts and finite transfer data. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583Strip
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583Strip
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583StripData
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
attribute [local irreducible] a T initial terminal W cl

namespace Recurrence
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)
def readout : Realization signature := realize signature (fun _ _ n => a n) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ n => a n + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ),
    (R.readout () () (n + 5) : ℤ) =  30 * R.readout () () (n + 4) - 261 * R.readout () () (n + 3) + 540 * R.readout () () (n + 2) - 324 * R.readout () () (n + 1)
private theorem rejected_at (h : arena.Law rejected) (n : ℕ) : False := by
  have hb := h n
  have ha := result n
  simp only [rejected, realize, Nat.cast_add, Nat.cast_one] at hb
  linarith
private theorem rejected_law : ¬ arena.Law rejected := fun h => rejected_at h 0
private theorem count_zero : a 0 = 0 := by
  unfold a
  decide +kernel
private theorem count_one_pos : 0 < a 1 := by
  unfold a
  apply Finset.card_pos.mpr
  refine ⟨(fun x => ![0, 0, 1, 0, 1] x.2), ?_⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, by decide +kernel⟩
def family : Registration arena (type_of% @result) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change a 0 ≠ a 1
    rw [count_zero]
    exact Nat.ne_of_lt count_one_pos

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229583Strip.Recurrence.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583Strip
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

namespace Certificate
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 14) (fun _ => Fin 14) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ x y => T x y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ x y => T x y + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R :=     (∀ p (d : Fin 2), Valid p d.val →
      terminal (cl p d.val) = (if d.val = 0 then 1 else 0)) ∧
    (∀ p (d : Fin 2), Valid p d.val → ∀ r : Row,
      cross p r + bondDefects horizontal r r ≤ d.val →
      Valid (boundary r) (d.val - (cross p r + bondDefects horizontal r r))) ∧
    (∀ p (d : Fin 2), Valid p d.val → ∀ s : Fin 14,
      (∑ r : Row, if cross p r + bondDefects horizontal r r ≤ d.val ∧
        cl (boundary r) (d.val - (cross p r + bondDefects horizontal r r)) = s
        then (1 : ℤ) else 0) = (fun x y => R.readout () x y) (cl p d.val) s) ∧
    (∀ r : Row, bondDefects horizontal r r ≤ 1 →
      Valid (boundary r) (1 - bondDefects horizontal r r)) ∧
    (∀ s : Fin 14, (∑ r : Row, if bondDefects horizontal r r ≤ 1 ∧
      cl (boundary r) (1 - bondDefects horizontal r r) = s then (1 : ℤ) else 0) = initial s) ∧
    (W 0 = initial ∧ ∀ i : Fin 5, W i.succ = Matrix.vecMul (W i.castSucc) (fun x y => R.readout () x y)) ∧
    W 5 = ∑ j : Fin 4, (![-324, 540, -261, 30] j : ℤ) • W ⟨1 + j.val, by omega⟩
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h.2.2.1 ![0, 1, 0, 1] ⟨1, by decide⟩ (by decide +kernel) 0
  have ha := finite_certificate.2.2.1 ![0, 1, 0, 1] ⟨1, by decide⟩ (by decide +kernel) 0
  change _ = T (cl ![0, 1, 0, 1] 1) 0 + 1 at hb
  linarith
def family : Registration arena (type_of% @finite_certificate) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨finite_certificate, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨0, 0, 2, ?_⟩
    change T 0 0 ≠ T 0 2
    unfold T
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@finite_certificate) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229583Strip.Certificate.auditUnit
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
  readout := some (realize signature (fun _ x y => T x y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583Strip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "fn", "arg", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Certificate

namespace Edge
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Row (fun _ => Row) (fun _ => ℕ)
def readout : Realization signature :=
  realize signature (fun _ r t => cross (boundary r) t) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ r t => cross (boundary r) t + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ r t : Row, bondDefects antidiagonal r t = R.readout () r t
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (fun _ => 0) (fun _ => 0)
  have ha := edge (fun _ => 0) (fun _ => 0)
  change _ = cross (boundary (fun _ => 0)) (fun _ => 0) + 1 at hb
  omega
def family : Registration arena (type_of% @edge) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨edge, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro ⟨⟩
    refine ⟨(fun _ => 0), (fun _ => 0), (fun _ => 1), ?_⟩
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@edge) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229583Strip.Edge.auditUnit
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
  readout := some (realize signature (fun _ r t => cross (boundary r) t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583Strip
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

end Edge
end
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229583Strip
