import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.JacobiEndpointResolvent
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Field.ULift
import Reg.Support.UniverseSingleReadout

/-! Source-bound readouts of the Green-column transfer, its zeros and its supported action. -/

noncomputable section

open LeanInformationAudit
open _root_.D5.S3.Quantum.Matrix.JacobiEndpointResolvent
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators Matrix

namespace Reg.D5.S3.Quantum.Matrix.JacobiEndpointResolvent

universe u v

private abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature (Type u) (fun K => K) (fun K => K → Prop)

private def actual : Realization signature.{u} :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  refine ⟨ULift.{u} ℚ, 0, 1, ?_⟩
  intro h
  exact one_ne_zero ((congrFun h 0).mp rfl)

private theorem unit_tail {K : Type u} [Field K] {n : ℕ} (i : Fin n) :
    IsUnit (tail (1 : Matrix (Fin n) (Fin n) K) i).det := by
  rw [tail, Matrix.submatrix_one _ Subtype.val_injective, Matrix.det_one]
  exact isUnit_one

private theorem zero_tridiagonal {K : Type u} [Field K] {n : ℕ} :
    IsTridiagonal (0 : Matrix (Fin n) (Fin n) K) :=
  fun _ _ _ => rfl

private theorem zero_shift_unit_tail {K : Type u} [Field K] {n : ℕ} (i : Fin n) :
    IsUnit (tail (spectralShift (0 : Matrix (Fin n) (Fin n) K) 1) i).det := by
  simpa only [spectralShift, one_smul, sub_zero] using (unit_tail (K := K) i)

namespace TransferStep

private abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {K : Type u} [Field K] {n : ℕ} [NeZero n]
    (H : Matrix (Fin n) (Fin n) K) (z : K)
    (_hH : IsTridiagonal H) (_hInv : ∀ j : Fin n, IsUnit (tail (spectralShift H z) j).det)
    (p i : Fin n) (_hpi : p.val + 1 = i.val),
    R.readout () K (firstColumn (spectralShift H z) i)
      ((bond H p * firstColumn (spectralShift H z) p) * tailDiagonal (spectralShift H z) i)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (0 : Matrix (Fin 2) (Fin 2) (ULift.{u} ℚ)) 1
    zero_tridiagonal zero_shift_unit_tail 0 1 rfl

def family : Registration arena.{u} (type_of% @firstColumn_step.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@firstColumn_step.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@firstColumn_step.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.JacobiEndpointResolvent.firstColumn_step.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.JacobiEndpointResolvent.TransferStep.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.JacobiEndpointResolvent
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TransferStep

namespace ColumnProduct

private abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {K : Type u} [Field K] {n : ℕ} [NeZero n]
    (H : Matrix (Fin n) (Fin n) K) (z : K)
    (_hH : IsTridiagonal H) (_hInv : ∀ j : Fin n, IsUnit (tail (spectralShift H z) j).det)
    (i : Fin n),
    R.readout () K (firstColumn (spectralShift H z) i)
      (bondProduct H i * tailDiagonalProduct (spectralShift H z) i)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (0 : Matrix (Fin 1) (Fin 1) (ULift.{u} ℚ)) 1
    zero_tridiagonal zero_shift_unit_tail 0

def family : Registration arena.{u} (type_of% @firstColumn_eq.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@firstColumn_eq.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@firstColumn_eq.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.JacobiEndpointResolvent.firstColumn_eq.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.JacobiEndpointResolvent.ColumnProduct.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.JacobiEndpointResolvent
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ColumnProduct

namespace TailNonvanishing

private def nonvanishing : Realization signature.{u} :=
  realize signature (fun _ _ x y => x ≠ y) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {K : Type u} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K)
    (_hInv : ∀ j : Fin n, IsUnit (tail A j).det) (i : Fin n),
    R.readout () K (tailDiagonal A i) 0

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (1 : Matrix (Fin 1) (Fin 1) (ULift.{u} ℚ)) unit_tail 0

def family : Registration arena.{u} (type_of% @tailDiagonal_ne_zero.{u}) where
  actual := nonvanishing
  bridge := Iff.rfl
  variation := ⟨@tailDiagonal_ne_zero.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law nonvanishing rejected rejected_law
  dependence := by
    intro role
    refine ⟨ULift.{u} ℚ, 0, 1, ?_⟩
    intro h
    exact ((congrFun h 0).mpr one_ne_zero) rfl

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@tailDiagonal_ne_zero.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.JacobiEndpointResolvent.tailDiagonal_ne_zero.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.JacobiEndpointResolvent.TailNonvanishing.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ x y => x ≠ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.JacobiEndpointResolvent
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn",
        "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TailNonvanishing

namespace ColumnVanishing

private def alwaysEqual : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => True) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {K : Type u} [Field K] {n : ℕ} [NeZero n]
    (H : Matrix (Fin n) (Fin n) K) (z : K)
    (_hH : IsTridiagonal H) (_hInv : ∀ j : Fin n, IsUnit (tail (spectralShift H z) j).det)
    (i : Fin n),
    R.readout () K (firstColumn (spectralShift H z) i) 0 ↔
      ∃ j : Fin n, j < i ∧ bond H j = 0

private theorem rejected_law : ¬ arena.{u}.Law alwaysEqual := by
  intro h
  obtain ⟨j, hj, _⟩ := (h (0 : Matrix (Fin 1) (Fin 1) (ULift.{u} ℚ)) 1
    zero_tridiagonal zero_shift_unit_tail 0).mp trivial
  exact (not_lt_of_ge (Fin.zero_le j)) hj

def family : Registration arena.{u} (type_of% @firstColumn_eq_zero_iff.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@firstColumn_eq_zero_iff.{u}, alwaysEqual, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual alwaysEqual rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@firstColumn_eq_zero_iff.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.JacobiEndpointResolvent.firstColumn_eq_zero_iff.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.JacobiEndpointResolvent.ColumnVanishing.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.JacobiEndpointResolvent
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ColumnVanishing

namespace SupportedAction

private abbrev vectorSignature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature ((_ : Type u) × Type v)
    (fun p => p.2 → p.1) (fun p => (p.2 → p.1) → Prop)

private def vectorEquality : Realization vectorSignature.{u, v} :=
  realize vectorSignature (fun _ _ x y => x = y) (fun e => nomatch e)

private def vectorRejected : Realization vectorSignature.{u, v} :=
  realize vectorSignature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- Boolean comparison for the collar filter, using only Lean's natural number recursion. -/
private def collarLe : @& ℕ → @& ℕ → Bool
  | .zero, _ => true
  | .succ _, .zero => false
  | .succ j, .succ k => collarLe j k

private theorem collarLe_eq_ble (j k : ℕ) : collarLe j k = Nat.ble j k := by
  induction j generalizing k with
  | zero => rfl
  | succ j ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih k

private def collarLt (j k : ℕ) : Decidable (j < k) where
  decide := collarLe j.succ k
  reflects_decide := by
    rw [collarLe_eq_ble]
    exact (Nat.decLt j k).reflects_decide

private abbrev arena : Arena where
  signature := vectorSignature.{u, v}
  Law R := ∀ {K : Type u} [Field K] {n : ℕ} [NeZero n] {ι : Type v}
    (H : Matrix (Fin n) (Fin n) K) (z : K)
    (_hH : IsTridiagonal H) (_hInv : ∀ j : Fin n, IsUnit (tail (spectralShift H z) j).det)
    (W : Matrix ι (Fin n) K) (k : ℕ) (_hW : ∀ j : Fin n, k ≤ j.val → W.col j = 0),
    R.readout () ⟨K, ι⟩ (W *ᵥ firstColumn (spectralShift H z))
      (∑ j ∈ @Finset.filter (Fin n) (fun j => j.val < k) (fun j => collarLt j.val k) Finset.univ,
        tailDiagonalProduct (spectralShift H z) j • (bondProduct H j • W.col j))

private theorem rejected_law : ¬ arena.{u, v}.Law vectorRejected := by
  intro h
  exact h (ι := ULift.{v} Unit) (0 : Matrix (Fin 1) (Fin 1) (ULift.{u} ℚ)) 1
    zero_tridiagonal zero_shift_unit_tail 0 0 (fun _ _ => rfl)

private theorem source_bridge :
    (type_of% @supported_mulVec_firstColumn.{u, v}) ↔ arena.{u, v}.Law vectorEquality := by
  constructor <;> intro h K inst n hn ι H z hH hInv W k hW
  · have hfilter := Finset.filter_congr_decidable (Finset.univ : Finset (Fin n))
      (fun j => j.val < k) (fun j => collarLt j.val k)
    have hh := h H z hH hInv W k hW
    change W *ᵥ firstColumn (spectralShift H z) =
      ∑ j ∈ @Finset.filter (Fin n) (fun j => j.val < k) (fun j => collarLt j.val k) Finset.univ,
        tailDiagonalProduct (spectralShift H z) j • (bondProduct H j • W.col j)
    rwa [hfilter]
  · have hfilter := Finset.filter_congr_decidable (Finset.univ : Finset (Fin n))
      (fun j => j.val < k) (fun j => collarLt j.val k)
    have hh := h H z hH hInv W k hW
    change W *ᵥ firstColumn (spectralShift H z) =
      ∑ j ∈ @Finset.filter (Fin n) (fun j => j.val < k) (fun j => collarLt j.val k) Finset.univ,
        tailDiagonalProduct (spectralShift H z) j • (bondProduct H j • W.col j) at hh
    rwa [hfilter] at hh

def family : Registration arena.{u, v} (type_of% @supported_mulVec_firstColumn.{u, v}) where
  actual := vectorEquality
  bridge := source_bridge
  variation := ⟨source_bridge.mp @supported_mulVec_firstColumn.{u, v}, vectorRejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law vectorEquality vectorRejected rejected_law
  dependence := by
    intro role
    let K := ULift.{u} ℚ
    let rows := ULift.{v} Unit
    let zeroVector : rows → K := fun _ => 0
    let oneVector : rows → K := fun _ => 1
    refine ⟨⟨K, rows⟩, zeroVector, oneVector, ?_⟩
    intro h
    exact one_ne_zero (congrFun ((congrFun h zeroVector).mp rfl) ⟨()⟩)

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@supported_mulVec_firstColumn.{u, v}) (Realization vectorSignature.{u, v}) Unit Unit where
  unitName := `D5.S3.Quantum.Matrix.JacobiEndpointResolvent.supported_mulVec_firstColumn.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.JacobiEndpointResolvent.SupportedAction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v}⟩
  objectArena := .source ⟨arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u, v} ⟨family.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize vectorSignature.{u, v} (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.JacobiEndpointResolvent
    definition := none
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SupportedAction

end Reg.D5.S3.Quantum.Matrix.JacobiEndpointResolvent
