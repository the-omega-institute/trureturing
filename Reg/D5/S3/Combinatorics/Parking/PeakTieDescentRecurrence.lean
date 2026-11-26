import D5.S3.Combinatorics.Parking.PeakTieDescentRecurrence
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source-bound registrations for the literal observations. -/

open _root_.D5.S3.Combinatorics.Parking.DescentRefinement
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Combinatorics.Parking.PeakTieDescentRecurrence

noncomputable section

namespace boundedWords

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Nat)
    (fun _ => Nat) (fun _ => Finset (List Nat))

private def actual : Realization signature :=
  realize signature (fun _ n m => literalParking n m) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law f := ∀ n m (w : List Nat), w ∈ f.readout () n m ↔ BoundedParking n m w

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have valid : BoundedParking 0 0 [] := by simp [BoundedParking, RankBound]
  have he := (h 0 0 []).mpr valid
  simp [rejected, realize] at he

def family : Registration arena (type_of% @mem_literalParking) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@mem_literalParking, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨1, 0, 1, ?_⟩
    change literalParking 1 0 ≠ literalParking 1 1
    intro h
    have valid : BoundedParking 1 1 [1] := by simp [BoundedParking, RankBound]
    have he := (mem_literalParking 1 1 [1]).mpr valid
    rw [← h, mem_literalParking] at he
    exact (by decide : ¬ (1 ≤ 0)) (he.2.1 1 (by simp)).2

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@mem_literalParking) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Parking.PeakTieDescentRecurrence.boundedWords.unit
  realizationName := `Reg.D5.S3.Combinatorics.Parking.PeakTieDescentRecurrence.boundedWords.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Parking.PeakTieDescentRecurrence
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end boundedWords

namespace polynomialRecurrence

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Nat)
    (fun _ => Nat) (fun _ => ParkingPolynomial)

private def actual : Realization signature :=
  realize signature (fun _ n m => parkingPolynomial n m) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law f := ∀ {n m : Nat}, 2 ≤ m → m ≤ n →
    f.readout () n m = parkingPolynomial n (m - 1) +
      ∑ r ∈ Finset.Icc 1 (n - m + 1),
        insertionOperator (n - r) r (parkingPolynomial (n - r) (m - 1))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (n := 2) (m := 2) (by decide) (by decide)
  change 0 = parkingPolynomial 2 1 + _ at he
  have hb : parkingPolynomial 2 1 = MvPolynomial.X 1 := by
    rw [parkingPolynomial, parking_base]
    simp
  rw [hb] at he
  have hv := congrArg (MvPolynomial.eval (fun _ => 1)) he
  simp at hv
  omega

def family : Registration arena (type_of% @parkingPolynomial_operator_recurrence) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@parkingPolynomial_operator_recurrence, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨1, 0, 1, ?_⟩
    change parkingPolynomial 1 0 ≠ parkingPolynomial 1 1
    have hEmpty : literalParking 1 0 = ∅ := by
      ext w
      simp only [mem_literalParking, Finset.notMem_empty, iff_false]
      rintro ⟨hl, hm, _⟩
      cases w with
      | nil => simp at hl
      | cons a w =>
        obtain ⟨ha, hz⟩ := hm a (by simp)
        omega
    have h0 : parkingPolynomial 1 0 = 0 := by simp [parkingPolynomial, G, hEmpty]
    have h1 : parkingPolynomial 1 1 = 1 := by rw [parkingPolynomial, parking_base, pow_zero]
    rw [h0, h1]
    exact zero_ne_one

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@parkingPolynomial_operator_recurrence) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Parking.PeakTieDescentRecurrence.polynomialRecurrence.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Parking.PeakTieDescentRecurrence.polynomialRecurrence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Parking.PeakTieDescentRecurrence
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end polynomialRecurrence

end
end Reg.D5.S3.Combinatorics.Parking.PeakTieDescentRecurrence
