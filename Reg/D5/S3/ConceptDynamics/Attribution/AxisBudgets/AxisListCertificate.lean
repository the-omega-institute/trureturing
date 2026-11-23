import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.AxisBudgets.AxisListCertificate
import Reg.Support.DependentFamily

/-! Source-bound observations for the mask transport and its exact list incidence. -/

set_option autoImplicit false

namespace Reg.D5.S3.ConceptDynamics.Attribution.AxisBudgets.AxisListCertificate

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.ErdosUlam.SublatticeDefs
open _root_.D5.S3.ConceptDynamics.Attribution.AxisBudgets.AxisListCertificate
open _root_.D5.S3.ConceptDynamics.Attribution.AxisBudgets.AxisListCertificate.AxisMaskTransport
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedAxisFactor
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

namespace MaskRank

private abbrev signature : Signature where
  Params := ℕ
  State n := Fin (2 ^ n)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ n m => weight n m.val) (fun a => nomatch a)

private def zero : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun a => nomatch a)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ n m, (maskEquiv n m).val.card = R.readout () n m

private theorem zero_fails : ¬ arena.Law zero := by
  intro h
  let m : Fin (2 ^ 1) := ⟨1, by decide⟩
  have hr := mask_rank 1 m
  have hz := h 1 m
  change (maskEquiv 1 m).val.card = 0 at hz
  rw [hr] at hz
  exact (show weight 1 m.val ≠ 0 by decide) hz

def family : Registration arena (type_of% @mask_rank) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨mask_rank, zero, zero_fails⟩
  sensitivity := ⟨fun i => ⟨zero, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, zero_fails⟩, fun a => nomatch a⟩
  dependence := by
    rintro ⟨⟩
    exact ⟨1, ⟨0, by decide⟩, ⟨1, by decide⟩, by decide⟩

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@mask_rank) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.ConceptDynamics.Attribution.AxisBudgets.AxisListCertificate.mask_rank.audit
  realizationName :=
    `Reg.D5.S3.ConceptDynamics.Attribution.AxisBudgets.AxisListCertificate.MaskRank.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n m => weight n m.val) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.AxisBudgets.AxisListCertificate
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

end MaskRank

namespace MaskTop

private abbrev signature : Signature where
  Params := ℕ
  State n := Fin (2 ^ n)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := AxisSubset (n + 1) 0
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ n m => maskEquiv n m) (fun a => nomatch a)

private def emptyMask : Realization signature :=
  realize signature (fun _ n _ => maskEquiv n ⟨0, Nat.two_pow_pos n⟩) (fun a => nomatch a)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (m : Fin (2 ^ n)), m.val = 2 ^ n - 1 →
    R.readout () n m = axisTop 0

private theorem empty_fails : ¬ arena.Law emptyMask := by
  intro h
  let m : Fin (2 ^ 1) := ⟨1, by decide⟩
  have bad := h 1 m (by decide)
  rw [← mask_top 1 m (by decide)] at bad
  change maskEquiv 1 ⟨0, by decide⟩ = maskEquiv 1 m at bad
  exact (by decide : (⟨0, by decide⟩ : Fin (2 ^ 1)) ≠ m) ((maskEquiv 1).injective bad)

def family : Registration arena (type_of% @mask_top) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨mask_top, emptyMask, empty_fails⟩
  sensitivity := ⟨fun i => ⟨emptyMask, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, empty_fails⟩, fun a => nomatch a⟩
  dependence := by
    rintro ⟨⟩
    refine ⟨1, ⟨0, by decide⟩, ⟨1, by decide⟩, ?_⟩
    intro eq
    exact (by decide : (⟨0, by decide⟩ : Fin (2 ^ 1)) ≠ ⟨1, by decide⟩)
      ((maskEquiv 1).injective eq)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@mask_top) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.ConceptDynamics.Attribution.AxisBudgets.AxisListCertificate.mask_top.audit
  realizationName :=
    `Reg.D5.S3.ConceptDynamics.Attribution.AxisBudgets.AxisListCertificate.MaskTop.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n m => maskEquiv n m) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.AxisBudgets.AxisListCertificate
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

end MaskTop

namespace ListIncidence

open Finset
open _root_.D5.S3.ConceptDynamics.Attribution.AxisBudgets.AxisListCertificate.ListBridge
open _root_.D5.S3.ConceptDynamics.Attribution.ParitySeedFactor

private abbrev Parameters :=
  Σ n : ℕ, (Fin (2 ^ n) → List ℕ) × AxisSubset (n + 1) 0

private abbrev signature : Signature where
  Params := Parameters
  State p := AxisSubset (p.1 + 1) 0
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature
    (fun _ p b => ((maskEquiv p.1).symm b).val ∈ p.2.1 ((maskEquiv p.1).symm p.2.2))
    (fun a => nomatch a)

private def noEdge : Realization signature :=
  realize signature (fun _ _ _ => False) (fun a => nomatch a)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (row col : Fin (2 ^ n) → List ℕ) (budget : ℕ)
    (top : Fin (2 ^ n)), top.val = 2 ^ n - 1 → top.val ∉ row top →
    (∀ a w, w ∈ row a → w < 2 ^ n) →
    (∀ b w, w ∈ col b → w < 2 ^ n) →
    (∀ a, (row a).Nodup) →
    (∀ b, (col b).Nodup) →
    (∀ a b, b.val ∈ row a ↔ a.val ∈ col b) →
    (∀ a, residualDegree 3 true (decide (a = top)) (row a).length) →
    (∀ b, residualDegree 3 true (decide (b = top)) (col b).length) →
    (∀ a ≠ top, ∀ w ∈ row a, a.val &&& w = a.val) →
    (4 * (1 + ∑ a, if a ≠ top ∧ weight n a % 2 = 1 then
      (row a).countP (fun w => weight n w % 2 == 1) else 0) ≤ budget) →
    MaskedFactorWithRows 3 (0 : Fin (n + 1)) budget
      (fun a b => R.readout () ⟨n, row, a⟩ b)

private def diagonal (a : Fin (2 ^ 1)) : List ℕ := if a = 1 then [] else [a.val]

private theorem diagonal_bound : ∀ a w, w ∈ diagonal a → w < 2 ^ 1 := by
  intro a w h
  by_cases htop : a = 1
  · simp [diagonal, htop] at h
  · have eq : w = a.val := by simpa [diagonal, htop] using h
    exact eq.symm ▸ a.isLt

private theorem diagonal_support :
    ∀ a ≠ (1 : Fin (2 ^ 1)), ∀ w ∈ diagonal a, a.val &&& w = a.val := by
  intro a ha w hw
  have eq : w = a.val := by simpa [diagonal, ha] using hw
  simp [eq]

private theorem noEdge_fails : ¬ arena.Law noEdge := by
  intro h
  have diagonal_degree :
      ∀ a : Fin (2 ^ 1), residualDegree 3 true (decide (a = 1)) (diagonal a).length := by
    unfold residualDegree
    decide
  obtain ⟨f, selected, _, _, rows, _, _, _, read⟩ :=
    h 1 diagonal diagonal 4 1 (by decide) (by decide) diagonal_bound diagonal_bound
      (by decide) (by decide) (by decide) diagonal_degree diagonal_degree diagonal_support (by decide)
  have off (a b : AxisSubset 2 (0 : Fin 2)) : f a b = false := by
    cases hEntry : f a b
    · rfl
    · exact ((read a b).mp hEntry).elim
  let E := maskEquiv 1
  have hOrdinary : E 0 ≠ axisTop 0 := by
    rw [← mask_top 1 1 (by decide)]
    exact fun eq => (by decide : (0 : Fin (2 ^ 1)) ≠ 1) (E.injective eq)
  have rowDegree := rows (E 0)
  simp [residualDegree, hOrdinary, off] at rowDegree

private def family : Registration arena (type_of% @list_axis_factor) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@list_axis_factor, noEdge, noEdge_fails⟩
  sensitivity := ⟨fun i => ⟨noEdge, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, noEdge_fails⟩, fun a => nomatch a⟩
  dependence := by
    rintro ⟨⟩
    let E := maskEquiv 1
    refine ⟨⟨1, diagonal, E 0⟩, E 0, E 1, ?_⟩
    change (((E.symm (E 0)).val ∈ diagonal (E.symm (E 0))) ≠
      ((E.symm (E 1)).val ∈ diagonal (E.symm (E 0))))
    simp only [Equiv.symm_apply_apply]
    exact fun eq => (by decide : (1 : ℕ) ∉ diagonal 0) (eq.mp (by decide))

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@list_axis_factor) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.ConceptDynamics.Attribution.AxisBudgets.AxisListCertificate.list_axis_factor.audit
  realizationName :=
    `Reg.D5.S3.ConceptDynamics.Attribution.AxisBudgets.AxisListCertificate.ListIncidence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p b => ((maskEquiv p.1).symm b).val ∈ p.2.1 ((maskEquiv p.1).symm p.2.2))
    (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.AxisBudgets.AxisListCertificate
    definition := none
    coordinates := #[0, 1, 16]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "body"]
      stateBinder := 17
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ListIncidence

end
end Reg.D5.S3.ConceptDynamics.Attribution.AxisBudgets.AxisListCertificate
