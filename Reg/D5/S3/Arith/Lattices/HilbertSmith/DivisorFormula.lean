import D5.S3.Arith.Lattices.HilbertSmith.DivisorFormula
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source observations for the residue minimum and interval LCM formula. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.Lattices.HilbertSmith.DivisorFormula

open _root_.D5.S3.Arith.Lattices.HilbertSmith.DivisorFormula
open _root_.D5.S3.Arith.Lattices.HilbertSmith.NestedResidueMatching
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset
open scoped BigOperators

abbrev natSignature := Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℕ)
abbrev pairSignature :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, ℕ) (fun _ => ℕ) (fun _ => ℕ)
abbrev tripleSignature :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : ℕ, Σ _ : ℕ, ℕ)
    (fun _ => ℕ) (fun _ => ℕ)

namespace ResidueMinimum

def actual : Realization tripleSignature :=
  realize tripleSignature (fun _ p e => 2 * (∑ a ∈ Icc 1 e, (p.2.2 - commonCapacity p.2.1 (p.1 ^ a)))) (fun e => nomatch e)

def rejected : Realization tripleSignature :=
  realize tripleSignature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := tripleSignature
  Law R := ∀ {p n k : ℕ}, 0 < p → k ≤ n → ∀ e : ℕ,
    (∀ {I J : Finset ℕ}, I ⊆ range n → J ⊆ range n → I.card = k → J.card = k →
      R.readout () ⟨p, n, k⟩ e ≤ ∑ a ∈ Icc 1 e, residueLoss (p ^ a) I J) ∧
    (∃ I ⊆ range n, ∃ J ⊆ range n, I.card = k ∧ J.card = k ∧
      (∑ a ∈ Icc 1 e, residueLoss (p ^ a) I J) =
        2 * (∑ a ∈ Icc 1 e, (k - commonCapacity n (p ^ a))))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hlower := (h (p := 2) (n := 0) (k := 0) (by decide) (by decide) 0).1
    (I := ∅) (J := ∅) (by decide) (by decide) (by decide) (by decide)
  exact (by decide : ¬ 2 ≤ ∑ a ∈ Icc 1 0, residueLoss (2 ^ a) ∅ ∅) hlower

private theorem dependence : ObservationalDependence tripleSignature actual := by
  intro role
  refine ⟨⟨2, 1, 1⟩, 0, 1, ?_⟩
  change (2 * (∑ a ∈ Icc 1 0, (1 - commonCapacity 1 (2 ^ a)))) ≠
    (2 * (∑ a ∈ Icc 1 1, (1 - commonCapacity 1 (2 ^ a))))
  decide

def family : Registration arena (type_of% @residueLoss_sum_minimum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@residueLoss_sum_minimum, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@residueLoss_sum_minimum) (Realization tripleSignature) Unit Unit where
  unitName := `D5.S3.Arith.Lattices.HilbertSmith.DivisorFormula.residueLoss_sum_minimum.__information_unit
  realizationName := `Reg.D5.S3.Arith.Lattices.HilbertSmith.DivisorFormula.ResidueMinimum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize tripleSignature (fun _ p e => 2 * (∑ a ∈ Icc 1 e, (p.2.2 - commonCapacity p.2.1 (p.1 ^ a)))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Lattices.HilbertSmith.DivisorFormula
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ResidueMinimum

namespace LcmNonzero

def actual : Realization natSignature :=
  realize natSignature (fun _ n k => intervalLCM n k) (fun e => nomatch e)

def rejected : Realization natSignature :=
  realize natSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := natSignature
  Law R := ∀ {n k : ℕ}, 0 < k → R.readout () n k ≠ 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (n := 1) (k := 1) (by decide) rfl

private theorem dependence : ObservationalDependence natSignature actual := by
  intro role
  refine ⟨1, 0, 1, ?_⟩
  change intervalLCM 1 0 ≠ intervalLCM 1 1
  decide

def family : Registration arena (type_of% @intervalLCM_ne_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@intervalLCM_ne_zero, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@intervalLCM_ne_zero) (Realization natSignature) Unit Unit where
  unitName := `D5.S3.Arith.Lattices.HilbertSmith.DivisorFormula.intervalLCM_ne_zero.__information_unit
  realizationName := `Reg.D5.S3.Arith.Lattices.HilbertSmith.DivisorFormula.LcmNonzero.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ n k => intervalLCM n k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Lattices.HilbertSmith.DivisorFormula
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

end LcmNonzero

namespace LcmDivisibility

def actual : Realization natSignature :=
  realize natSignature (fun _ n k => intervalLCM n k) (fun e => nomatch e)

def rejected : Realization natSignature :=
  realize natSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := natSignature
  Law R := ∀ {n k l : ℕ}, k ≤ l → R.readout () n l ∣ intervalLCM n k

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (n := 1) (k := 1) (l := 1) (by decide)
  exact (by decide : ¬ 0 ∣ intervalLCM 1 1) hbad

private theorem dependence : ObservationalDependence natSignature actual := by
  intro role
  refine ⟨1, 0, 1, ?_⟩
  change intervalLCM 1 0 ≠ intervalLCM 1 1
  decide

def family : Registration arena (type_of% @intervalLCM_dvd_of_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@intervalLCM_dvd_of_le, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@intervalLCM_dvd_of_le) (Realization natSignature) Unit Unit where
  unitName := `D5.S3.Arith.Lattices.HilbertSmith.DivisorFormula.intervalLCM_dvd_of_le.__information_unit
  realizationName := `Reg.D5.S3.Arith.Lattices.HilbertSmith.DivisorFormula.LcmDivisibility.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ n k => intervalLCM n k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Lattices.HilbertSmith.DivisorFormula
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LcmDivisibility

namespace ClearingHeight

def actual : Realization natSignature :=
  realize natSignature (fun _ p n => Nat.log p (2 * n - 1)) (fun e => nomatch e)

def rejected : Realization natSignature :=
  realize natSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := natSignature
  Law R := ∀ {p n L : ℕ}, p.Prime → L ≠ 0 → intervalLCM n 1 ∣ L →
    R.readout () p n ≤ L.factorization p

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (p := 2) (n := 0) (L := 1) (by decide) (by decide) (by decide)
  change 1 ≤ (1 : ℕ).factorization 2 at hbad
  rw [Nat.factorization_one, Finsupp.zero_apply] at hbad
  omega

private theorem dependence : ObservationalDependence natSignature actual := by
  intro role
  refine ⟨2, 1, 2, ?_⟩
  change Nat.log 2 1 ≠ Nat.log 2 3
  decide

def family : Registration arena (type_of% @height_le_factorization) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@height_le_factorization, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@height_le_factorization) (Realization natSignature) Unit Unit where
  unitName := `D5.S3.Arith.Lattices.HilbertSmith.DivisorFormula.height_le_factorization.__information_unit
  realizationName := `Reg.D5.S3.Arith.Lattices.HilbertSmith.DivisorFormula.ClearingHeight.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ p n => Nat.log p (2 * n - 1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Lattices.HilbertSmith.DivisorFormula
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ClearingHeight

namespace CapacityDivisibility

def actual : Realization natSignature :=
  realize natSignature (fun _ n q => commonCapacity n q) (fun e => nomatch e)

def rejected : Realization natSignature :=
  realize natSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := natSignature
  Law R := ∀ {n k q : ℕ}, k ≤ n → 0 < q →
    (k ≤ R.readout () n q ↔ ∃ t ∈ Icc k (2 * n - k), q ∣ t)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h (n := 1) (k := 1) (q := 1) (by decide) (by decide)).mpr
    ⟨1, by decide, by decide⟩
  exact (by decide : ¬ (1 : ℕ) ≤ 0) hbad

private theorem dependence : ObservationalDependence natSignature actual := by
  intro role
  refine ⟨1, 1, 2, ?_⟩
  change commonCapacity 1 1 ≠ commonCapacity 1 2
  decide

def family : Registration arena (type_of% @le_capacity_iff_exists_dvd) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@le_capacity_iff_exists_dvd, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@le_capacity_iff_exists_dvd) (Realization natSignature) Unit Unit where
  unitName := `D5.S3.Arith.Lattices.HilbertSmith.DivisorFormula.le_capacity_iff_exists_dvd.__information_unit
  realizationName := `Reg.D5.S3.Arith.Lattices.HilbertSmith.DivisorFormula.CapacityDivisibility.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ n q => commonCapacity n q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Lattices.HilbertSmith.DivisorFormula
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CapacityDivisibility

namespace LcmValuation

def actual : Realization pairSignature :=
  realize pairSignature (fun _ p k => (intervalLCM p.2 k).factorization p.1) (fun e => nomatch e)

def rejected : Realization pairSignature :=
  realize pairSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := pairSignature
  Law R := ∀ {p n k : ℕ}, p.Prime → 0 < k → k ≤ n →
    R.readout () ⟨p, n⟩ k =
      (capacityLayers p n k).card

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (p := 2) (n := 1) (k := 1) (by decide) (by decide) (by decide)
  exact (by decide :
    (1 : ℕ) ≠ (capacityLayers 2 1 1).card) hbad

private theorem dependence : ObservationalDependence pairSignature actual := by
  intro role
  refine ⟨⟨2, 2⟩, 2, 3, ?_⟩
  change (intervalLCM 2 2).factorization 2 ≠ (intervalLCM 2 3).factorization 2
  have hlcm : intervalLCM 2 2 = 2 := by decide
  have hempty : intervalLCM 2 3 = 1 := by decide
  simp [hlcm, hempty, Nat.factorization_one,
    Nat.Prime.factorization_self (by decide : Nat.Prime 2)]

def family : Registration arena (type_of% @intervalLCM_factorization) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@intervalLCM_factorization, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@intervalLCM_factorization) (Realization pairSignature) Unit Unit where
  unitName := `D5.S3.Arith.Lattices.HilbertSmith.DivisorFormula.intervalLCM_factorization.__information_unit
  realizationName := `Reg.D5.S3.Arith.Lattices.HilbertSmith.DivisorFormula.LcmValuation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize pairSignature (fun _ p k => (intervalLCM p.2 k).factorization p.1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Lattices.HilbertSmith.DivisorFormula
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LcmValuation

namespace Increment

def actual : Realization tripleSignature :=
  realize tripleSignature (fun _ p L => (L / intervalLCM p.2.1 (p.2.2 + 1)).factorization p.1) (fun e => nomatch e)

def rejected : Realization tripleSignature :=
  realize tripleSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := tripleSignature
  Law R := ∀ {p n k L : ℕ}, p.Prime → L ≠ 0 → intervalLCM n 1 ∣ L → k + 1 ≤ n →
    divisorExponent p n L (k + 1) =
      divisorExponent p n L k + R.readout () ⟨p, n, k⟩ L

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (p := 2) (n := 1) (k := 0) (L := 1)
    (by decide) (by decide) (by decide) (by decide)
  change divisorExponent 2 1 1 1 = divisorExponent 2 1 1 0 + 1 at hbad
  have hempty : Icc (1 : ℕ) 0 = ∅ := by decide
  simp [divisorExponent, Nat.factorization_one, Nat.log_one_right, hempty] at hbad

private theorem dependence : ObservationalDependence tripleSignature actual := by
  intro role
  refine ⟨⟨2, 1, 0⟩, 1, 2, ?_⟩
  change ((1 : ℕ) / intervalLCM 1 1).factorization 2 ≠
    ((2 : ℕ) / intervalLCM 1 1).factorization 2
  have hlcm : intervalLCM 1 1 = 1 := by decide
  simp [hlcm, Nat.factorization_one,
    Nat.Prime.factorization_self (by decide : Nat.Prime 2)]

def family : Registration arena (type_of% @divisorExponent_succ_eq_intervalLCM) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@divisorExponent_succ_eq_intervalLCM, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@divisorExponent_succ_eq_intervalLCM) (Realization tripleSignature) Unit Unit where
  unitName := `D5.S3.Arith.Lattices.HilbertSmith.DivisorFormula.divisorExponent_succ_eq_intervalLCM.__information_unit
  realizationName := `Reg.D5.S3.Arith.Lattices.HilbertSmith.DivisorFormula.Increment.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize tripleSignature (fun _ p L => (L / intervalLCM p.2.1 (p.2.2 + 1)).factorization p.1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Lattices.HilbertSmith.DivisorFormula
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Increment

end Reg.D5.S3.Arith.Lattices.HilbertSmith.DivisorFormula
