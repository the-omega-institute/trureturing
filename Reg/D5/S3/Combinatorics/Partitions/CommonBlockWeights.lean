import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Partitions.CommonBlockWeights
import Reg.Support.SingleDependentReadout

/-! The universal grouped allocation law observes the digit capacity. -/

namespace Reg.D5.S3.Combinatorics.Partitions.CommonBlockWeights
open _root_.D5.S3.Combinatorics.Partitions.CommonBlockWeights
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ k n => (k + 1)^n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k n q : ℕ}, 0 < k → k*q+1 ≤ R.readout () k n →
    ∃ w : Fin n → ℕ, (∑ j, w j = q) ∧ CoversAllocations k q w

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨w, total, _⟩ := h (k := 1) (n := 0) (q := 1) (by decide) (by decide)
  simpa using total

def family : Registration arena (type_of% (@common_weights_for_allocations)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨common_weights_for_allocations, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    exact (by decide : (1 : ℕ) ≠ 2)

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
    (@common_weights_for_allocations) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Partitions.CommonBlockWeights.information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.CommonBlockWeights.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ k n => (k + 1)^n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.CommonBlockWeights
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "domain", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev fractionalSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def fractionalActual : Realization fractionalSignature :=
  realize fractionalSignature (fun _ _ K => K) (fun e => nomatch e)

def fractionalRejected : Realization fractionalSignature :=
  realize fractionalSignature (fun _ _ _ => 3) (fun e => nomatch e)

abbrev fractionalArena : Arena where
  signature := fractionalSignature
  Law R := ∀ {k n A b K : ℕ}, 0 < k → K * b = k →
    K * A + 1 ≤ (R.readout () () K * b.gcd A + 1) * (k + 1)^n →
    ∃ w : Fin (n + 1) → ℕ, (∑ j, w j = A) ∧
      ∀ t U : ℕ, (0 < t ∨ U = 0) → k * (t - 1) ≤ U → ∀ x : Fin t → ℕ,
        b * (∑ i, x i) = U * A →
        ∃ a : Fin (n + 1) → Fin t → ℕ, (∀ j, ∑ i, a j i = U) ∧
          (∀ i, ∑ j, a j i * w j = b * x i)

private theorem fractional_rejected_law : ¬ fractionalArena.Law fractionalRejected := by
  intro h
  obtain ⟨w, total, cover⟩ := h (k := 2) (n := 0) (A := 3) (b := 2) (K := 1)
    (by decide) (by decide) (by decide)
  let demand (i : Fin 2) : ℕ := i.val + 1
  obtain ⟨a, _, mass⟩ := cover 2 2 (by decide) (by decide) demand (by decide)
  change (∑ j : Fin 1, w j) = 3 at total
  have w0 : w 0 = 3 := by simpa only [Fin.sum_univ_one] using total
  have impossible := mass 0
  change (∑ j : Fin 1, a j 0 * w j) = 2 at impossible
  simp only [Fin.sum_univ_one, w0] at impossible
  omega

def fractionalFamily :
    Registration fractionalArena (type_of% (@common_fractional_allocations)) where
  actual := fractionalActual
  bridge := Iff.rfl
  variation := ⟨common_fractional_allocations, fractionalRejected, fractional_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity fractionalArena.Law
    fractionalActual fractionalRejected fractional_rejected_law
  dependence := by
    intro role
    exact ⟨(), 1, 2, (by decide : (1 : ℕ) ≠ 2)⟩

def fractionalRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
    (@common_fractional_allocations) (Realization fractionalSignature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.Partitions.CommonBlockWeights.fractional_information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Partitions.CommonBlockWeights.fractionalFamily
  realizationSource := none
  generated := false
  arena := .source ⟨fractionalArena⟩
  objectArena := .source ⟨fractionalArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source fractionalArena ⟨fractionalFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize fractionalSignature (fun _ _ K => K) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Partitions.CommonBlockWeights
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "domain", "arg", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Partitions.CommonBlockWeights
