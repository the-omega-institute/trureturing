import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Geometry.MiuraSlabExtrema
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

/-! Actual dependent-array audit evidence for matching rectangle minima. -/

namespace Reg.D5.S3.Combinatorics.Geometry.MiuraSlabExtrema

open _root_.D5.S3.Combinatorics.Geometry.MiuraHeightEnvelope
open _root_.D5.S3.Combinatorics.Geometry.MiuraSlabExtrema
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev Parameter := Σ m : ℕ, Σ n : ℕ, Cell m n → ℤ

def signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Parameter (fun p => Cell p.1 p.2.1) (fun _ => ℤ)

def actual : Realization signature := realize signature
  (fun (_ : Unit) (p : Parameter) v => p.2.2 v) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun (_ : Unit) (_p : Parameter) _v => (0 : ℤ)) (fun e => nomatch e)

/-- Retain the actual geometric premises and vary the ambient height readout
in the extremum conclusion over the complete original dependent family. -/
def arena : Arena where
  signature := signature
  Law R := ∀ {m n : ℕ} {h : Cell m n → ℤ}, IsHeight h →
    ∀ I : Interval m, ∀ J : Interval n,
    RowOutward h I 1 → ColOutward h J 1 →
    ∃ v ∈ rectangle I J, IsStrictLocalMin (R.readout () ⟨m, n, h⟩) v

private def corner : Interval 2 := ⟨0, 0, le_rfl⟩
private def ramp (v : Cell 2 2) : ℤ := v.1.val + v.2.val

private theorem ramp_height : IsHeight ramp := by
  intro v u hu
  simp only [adj, gdist] at hu
  dsimp [ramp]
  rw [abs_eq (by norm_num : (0 : ℤ) ≤ 1)]
  omega

private theorem ramp_row : RowOutward ramp corner 1 := by
  intro v u hv hu hadj
  change (0 : Fin 2) ≤ v.1 ∧ v.1 ≤ 0 at hv
  change ¬ ((0 : Fin 2) ≤ u.1 ∧ u.1 ≤ 0) at hu
  simp only [adj, gdist] at hadj
  have := v.1.isLt
  have := u.1.isLt
  dsimp [ramp]
  omega

private theorem ramp_col : ColOutward ramp corner 1 := by
  intro v u hv hu hadj
  change (0 : Fin 2) ≤ v.2 ∧ v.2 ≤ 0 at hv
  change ¬ ((0 : Fin 2) ≤ u.2 ∧ u.2 ≤ 0) at hu
  simp only [adj, gdist] at hadj
  have := v.2.isLt
  have := u.2.isLt
  dsimp [ramp]
  omega

def registration : Registration arena (type_of% (@matching_minimum)) := by
  classical
  have hbad : ¬ arena.Law rejected := by
    intro h
    obtain ⟨v, hv, hmin⟩ := h ramp_height corner corner ramp_row ramp_col
    have hv' : corner.Contains v.1 ∧ corner.Contains v.2 := by
      simpa only [rectangle, Finset.mem_product, Interval.mem_rows] using hv
    have hzero : v = ((0, 0) : Cell 2 2) := by
      apply Prod.ext <;> apply Fin.ext
      · exact Nat.eq_zero_of_le_zero hv'.1.2
      · exact Nat.eq_zero_of_le_zero hv'.2.2
    subst v
    have he := hmin ((1, 0) : Cell 2 2) (by norm_num [adj, gdist])
    change (0 : ℤ) = 0 + 1 at he
    omega
  refine {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨matching_minimum, rejected, hbad⟩
    sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ hbad
    dependence := ?_ }
  intro i
  refine ⟨⟨2, 2, ramp⟩, (0, 0), (1, 0), ?_⟩
  change ramp (0, 0) ≠ ramp (1, 0)
  norm_num [ramp]

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@matching_minimum)
    (type_of% (realize signature
      (fun (_ : Unit) (p : Parameter) v => p.2.2 v) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Combinatorics.Geometry.MiuraSlabExtrema.matching_minimum.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Geometry.MiuraSlabExtrema.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun (_ : Unit) (p : Parameter) v => p.2.2 v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Geometry.MiuraSlabExtrema
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

end
end Reg.D5.S3.Combinatorics.Geometry.MiuraSlabExtrema
