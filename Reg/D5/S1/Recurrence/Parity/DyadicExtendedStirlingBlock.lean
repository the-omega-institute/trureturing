import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

/-! A source-bound audit of the rational dyadic block law. -/

noncomputable section
namespace Reg.D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock
open _root_.D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ n k => T n k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

/-- The full source law, with the left array observation variable and the right operands fixed. -/
def arena : Arena where
  signature := signature
  Law R := ∀ (n k : ℕ), 1 ≤ n → 2 ≤ k →
    R.readout () n k = ((k : ℚ) - 1) ^ g n * T (h n) (k - 1) +
      (k : ℚ) ^ (g n + 1) * T (h n) k

private theorem rejected_bad : ¬ arena.Law rejected := by
  intro hh
  have hh12 := hh 1 2 (by omega) (by omega)
  norm_num [rejected, realize, g, h, T] at hh12

def family : Registration arena (type_of% dyadic_extended_stirling_block) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨dyadic_extended_stirling_block, rejected, rejected_bad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_bad⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(1 : ℕ), (2 : ℕ), (3 : ℕ), ?_⟩
    change T 1 2 ≠ T 1 3
    norm_num [T]

def registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@dyadic_extended_stirling_block) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock.blockUnit
  realizationName := `Reg.D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n k => T n k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock
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

#print axioms registration
private theorem columns_zero_one (n : ℕ) : T n 0 ≠ T n 1 := by
  have hz : T n 0 = 0 := by rw [T]; simp
  rw [hz, T_one]
  norm_num

def firstColumnRejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev firstColumnArena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, R.readout () n 1 = 1

private theorem firstColumnRejectedLaw : ¬ firstColumnArena.Law firstColumnRejected := by
  intro law
  have h := law 0
  change (0 : ℚ) = 1 at h
  norm_num at h

def firstColumnSource : Registration firstColumnArena (type_of% T_one) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨T_one, firstColumnRejected, firstColumnRejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity firstColumnArena.Law
    actual firstColumnRejected firstColumnRejectedLaw
  dependence := by
    intro role
    exact ⟨0, 0, 1, columns_zero_one 0⟩


def oddArrayActual : Realization signature :=
  realize signature (fun _ m k => T (2 * m + 1) k) (fun e => nomatch e)

def oddArrayRejected : Realization signature :=
  realize signature (fun _ m k => T (2 * m + 1) k + 1) (fun e => nomatch e)

abbrev oddArrayArena : Arena where
  signature := signature
  Law R := ∀ m k : ℕ, 2 ≤ k →
    R.readout () m k = (k : ℚ) * T m k + T m (k - 1)

private theorem oddArrayRejectedLaw : ¬ oddArrayArena.Law oddArrayRejected := by
  intro law
  have h := law 0 2 (by decide)
  change T (2 * 0 + 1) 2 + 1 = _ at h
  rw [← T_odd 0 2 (by decide)] at h
  linarith only [h]

def oddArraySource : Registration oddArrayArena (type_of% T_odd) where
  actual := oddArrayActual
  bridge := Iff.rfl
  variation := ⟨T_odd, oddArrayRejected, oddArrayRejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity oddArrayArena.Law
    oddArrayActual oddArrayRejected oddArrayRejectedLaw
  dependence := by
    intro role
    exact ⟨0, 0, 1, columns_zero_one (2 * 0 + 1)⟩


def evenArrayActual : Realization signature :=
  realize signature (fun _ m k => T (2 * m) k) (fun e => nomatch e)

def evenArrayRejected : Realization signature :=
  realize signature (fun _ m k => T (2 * m) k + 1) (fun e => nomatch e)

abbrev evenArrayArena : Arena where
  signature := signature
  Law R := ∀ m k : ℕ, 0 < m → 2 ≤ k →
    R.readout () m k = (k : ℚ) * T m k + T m (k - 1) -
      (T (2 * m) (k - 1) + T m (k - 1)) / ((k : ℚ) - 1)

private theorem evenArrayRejectedLaw : ¬ evenArrayArena.Law evenArrayRejected := by
  intro law
  have h := law 1 2 (by decide) (by decide)
  change T (2 * 1) 2 + 1 = _ at h
  rw [← T_even 1 2 (by decide) (by decide)] at h
  linarith only [h]

def evenArraySource : Registration evenArrayArena (type_of% T_even) where
  actual := evenArrayActual
  bridge := Iff.rfl
  variation := ⟨T_even, evenArrayRejected, evenArrayRejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity evenArrayArena.Law
    evenArrayActual evenArrayRejected evenArrayRejectedLaw
  dependence := by
    intro role
    exact ⟨1, 0, 1, columns_zero_one (2 * 1)⟩


def firstColumnRegistration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@T_one) (Realization signature) Unit Unit where
  unitName := `D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock.T_one.__information_unit
  realizationName := `Reg.D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock.firstColumnSource
  realizationSource := none
  generated := false
  arena := .source ⟨firstColumnArena⟩
  objectArena := .source ⟨firstColumnArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source firstColumnArena ⟨firstColumnSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n k => T n k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


def oddArrayRegistration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@T_odd) (Realization signature) Unit Unit where
  unitName := `D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock.T_odd.__information_unit
  realizationName := `Reg.D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock.oddArraySource
  realizationSource := none
  generated := false
  arena := .source ⟨oddArrayArena⟩
  objectArena := .source ⟨oddArrayArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source oddArrayArena ⟨oddArraySource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ m k => T (2 * m + 1) k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock
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


def evenArrayRegistration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@T_even) (Realization signature) Unit Unit where
  unitName := `D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock.T_even.__information_unit
  realizationName := `Reg.D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock.evenArraySource
  realizationSource := none
  generated := false
  arena := .source ⟨evenArrayArena⟩
  objectArena := .source ⟨evenArrayArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source evenArrayArena ⟨evenArraySource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ m k => T (2 * m) k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock
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

end Reg.D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock
