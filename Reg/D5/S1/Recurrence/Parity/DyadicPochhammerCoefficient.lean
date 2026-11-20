import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Parity.DyadicPochhammerCoefficient
import D5.S1.Recurrence.Parity.DyadicPowerRowClosedForm
import Reg.Support.SingleDependentReadout

/-! Source-bound registrations for the dyadic Pochhammer lemmas. -/

namespace Reg.D5.S1.Recurrence.Parity.DyadicPochhammerCoefficient

open Polynomial
open _root_.D5.S1.Digit.DyadicRowPolynomialRecurrence (R_zero wt wt_zero)
open _root_.D5.S1.Recurrence.Parity.DyadicExtendedStirlingBlock (T T_one)
open _root_.D5.S1.Recurrence.Parity.DyadicPochhammerCoefficient
open _root_.D5.S1.Recurrence.Parity.DyadicPowerRowClosedForm (b b_two_pow)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

private theorem eval_rational_row (n k : ℕ) (hn : n = 2 ^ k) :
    (rationalRow n).eval 1 = (2 : ℚ) ^ (k + 1) - 1 := by
  have he : (rationalRow n).eval 1 = (b n : ℚ) := by simp [rationalRow, b]
  rw [he, hn, b_two_pow]
  push_cast
  rfl


abbrev basis_signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℚ)

def basis_actual : Realization basis_signature :=
  realize basis_signature (fun _ i j => pochhammerBasis.coord i (ascPochhammer ℚ j))
    (fun e => nomatch e)

def basis_rejected : Realization basis_signature :=
  realize basis_signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev basis_arena : Arena where
  signature := basis_signature
  Law R := ∀ i j : ℕ, R.readout () i j = if j = i then 1 else 0

private theorem basis_rejected_law : ¬ basis_arena.Law basis_rejected := by
  intro law
  have h := law 0 0
  change (0 : ℚ) = (if (0 : ℕ) = 0 then 1 else 0) at h
  norm_num at h

private theorem basis_dependence :
    ObservationalDependence basis_signature basis_actual := by
  intro role
  refine ⟨0, 0, 1, ?_⟩
  change pochhammerBasis.coord 0 (ascPochhammer ℚ 0) ≠
    pochhammerBasis.coord 0 (ascPochhammer ℚ 1)
  rw [coord_basis, coord_basis]
  norm_num

def basis_source : Registration basis_arena (type_of% (@coord_basis)) where
  actual := basis_actual
  bridge := Iff.rfl
  variation := ⟨@coord_basis, basis_rejected, basis_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity basis_arena.Law
    basis_actual basis_rejected basis_rejected_law
  dependence := basis_dependence

def basis_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@coord_basis) (Realization basis_signature) Unit Unit := {
  unitName := `D5.S1.Recurrence.Parity.DyadicPochhammerCoefficient.coord_basis.__information_unit
  realizationName := `Reg.D5.S1.Recurrence.Parity.DyadicPochhammerCoefficient.basis_source
  realizationSource := none
  generated := false
  arena := .source ⟨basis_arena⟩
  objectArena := .source ⟨basis_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source basis_arena ⟨basis_source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize basis_signature
    (fun _ i j => pochhammerBasis.coord i (ascPochhammer ℚ j)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Parity.DyadicPochhammerCoefficient
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev odd_signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => Polynomial ℚ)

def odd_actual : Realization odd_signature :=
  realize odd_signature (fun _ _ n => rationalRow (2 * n + 1)) (fun e => nomatch e)

def odd_rejected : Realization odd_signature :=
  realize odd_signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev odd_arena : Arena where
  signature := odd_signature
  Law R := ∀ n : ℕ, R.readout () () n = X * rationalRow n

private theorem odd_rejected_law : ¬ odd_arena.Law odd_rejected := by
  intro law
  have h := congrArg (Polynomial.eval (1 : ℚ)) (law 0)
  change (0 : Polynomial ℚ).eval 1 = (X * rationalRow 0).eval 1 at h
  norm_num [rationalRow, R_zero] at h

private theorem odd_dependence : ObservationalDependence odd_signature odd_actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  change rationalRow (2 * 0 + 1) ≠ rationalRow (2 * 1 + 1)
  intro he
  rw [rationalRow_odd 0, rationalRow_odd 1, show 1 = 2 * 0 + 1 by rfl,
    rationalRow_odd 0] at he
  have h := congrArg (Polynomial.eval (2 : ℚ)) he
  norm_num [rationalRow, R_zero] at h

def odd_source : Registration odd_arena (type_of% (@rationalRow_odd)) where
  actual := odd_actual
  bridge := Iff.rfl
  variation := ⟨@rationalRow_odd, odd_rejected, odd_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity odd_arena.Law
    odd_actual odd_rejected odd_rejected_law
  dependence := odd_dependence

def odd_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@rationalRow_odd) (Realization odd_signature) Unit Unit := {
  unitName :=
    `D5.S1.Recurrence.Parity.DyadicPochhammerCoefficient.rationalRow_odd.__information_unit
  realizationName := `Reg.D5.S1.Recurrence.Parity.DyadicPochhammerCoefficient.odd_source
  realizationSource := none
  generated := false
  arena := .source ⟨odd_arena⟩
  objectArena := .source ⟨odd_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source odd_arena ⟨odd_source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize odd_signature
    (fun _ _ n => rationalRow (2 * n + 1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Parity.DyadicPochhammerCoefficient
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev even_signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => Polynomial ℚ)

def even_actual : Realization even_signature :=
  realize even_signature (fun _ _ n => rationalRow (2 * n)) (fun e => nomatch e)

def even_rejected : Realization even_signature :=
  realize even_signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev even_arena : Arena where
  signature := even_signature
  Law R := ∀ n : ℕ, 0 < n → R.readout () () n = difference (rationalRow n)

private theorem even_rejected_law : ¬ even_arena.Law even_rejected := by
  intro law
  have h := (law 1 (by decide)).trans (rationalRow_even 1 (by decide)).symm
  have h' := congrArg (Polynomial.eval (1 : ℚ)) h
  change (0 : Polynomial ℚ).eval 1 = (rationalRow 2).eval 1 at h'
  rw [eval_rational_row 2 1 (by decide)] at h'
  norm_num at h'

private theorem even_dependence : ObservationalDependence even_signature even_actual := by
  intro role
  refine ⟨(), 1, 2, ?_⟩
  change rationalRow 2 ≠ rationalRow 4
  intro he
  have h := congrArg (Polynomial.eval (1 : ℚ)) he
  rw [eval_rational_row 2 1 (by decide), eval_rational_row 4 2 (by decide)] at h
  norm_num at h

def even_source : Registration even_arena (type_of% (@rationalRow_even)) where
  actual := even_actual
  bridge := Iff.rfl
  variation := ⟨@rationalRow_even, even_rejected, even_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity even_arena.Law
    even_actual even_rejected even_rejected_law
  dependence := even_dependence

def even_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@rationalRow_even) (Realization even_signature) Unit Unit := {
  unitName :=
    `D5.S1.Recurrence.Parity.DyadicPochhammerCoefficient.rationalRow_even.__information_unit
  realizationName := `Reg.D5.S1.Recurrence.Parity.DyadicPochhammerCoefficient.even_source
  realizationSource := none
  generated := false
  arena := .source ⟨even_arena⟩
  objectArena := .source ⟨even_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source even_arena ⟨even_source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize even_signature (fun _ _ n => rationalRow (2 * n)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Parity.DyadicPochhammerCoefficient
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev eigenvalue_signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => Polynomial ℚ)

def eigenvalue_actual : Realization eigenvalue_signature :=
  realize eigenvalue_signature (fun _ _ j => difference (ascPochhammer ℚ j)) (fun e => nomatch e)

def eigenvalue_rejected : Realization eigenvalue_signature :=
  realize eigenvalue_signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev eigenvalue_arena : Arena where
  signature := eigenvalue_signature
  Law R := ∀ j : ℕ, R.readout () () j = (j : ℚ) • ascPochhammer ℚ j

private theorem eigenvalue_rejected_law : ¬ eigenvalue_arena.Law eigenvalue_rejected := by
  intro law
  have h := congrArg (Polynomial.eval (1 : ℚ)) (law 1)
  change (0 : Polynomial ℚ).eval 1 = ((1 : ℚ) • ascPochhammer ℚ 1).eval 1 at h
  norm_num [ascPochhammer_one] at h

private theorem eigenvalue_dependence :
    ObservationalDependence eigenvalue_signature eigenvalue_actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  change difference (ascPochhammer ℚ 0) ≠ difference (ascPochhammer ℚ 1)
  intro he
  rw [difference_pochhammer, difference_pochhammer] at he
  have h := congrArg (Polynomial.eval (1 : ℚ)) he
  norm_num [ascPochhammer_one] at h

def eigenvalue_source : Registration eigenvalue_arena (type_of% (@difference_pochhammer)) where
  actual := eigenvalue_actual
  bridge := Iff.rfl
  variation := ⟨@difference_pochhammer, eigenvalue_rejected, eigenvalue_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity eigenvalue_arena.Law
    eigenvalue_actual eigenvalue_rejected eigenvalue_rejected_law
  dependence := eigenvalue_dependence

def eigenvalue_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@difference_pochhammer) (Realization eigenvalue_signature) Unit Unit := {
  unitName :=
    `D5.S1.Recurrence.Parity.DyadicPochhammerCoefficient.difference_pochhammer.__information_unit
  realizationName := `Reg.D5.S1.Recurrence.Parity.DyadicPochhammerCoefficient.eigenvalue_source
  realizationSource := none
  generated := false
  arena := .source ⟨eigenvalue_arena⟩
  objectArena := .source ⟨eigenvalue_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source eigenvalue_arena ⟨eigenvalue_source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize eigenvalue_signature
    (fun _ _ j => difference (ascPochhammer ℚ j)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Parity.DyadicPochhammerCoefficient
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev coordinate_signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℚ)

def coordinate_actual : Realization coordinate_signature :=
  realize coordinate_signature (fun _ n j => pochhammerBasis.coord j (rowPolynomial n))
    (fun e => nomatch e)

def coordinate_rejected : Realization coordinate_signature :=
  realize coordinate_signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev coordinate_arena : Arena where
  signature := coordinate_signature
  Law R := ∀ n j : ℕ, R.readout () n j = (-1 : ℚ) ^ (wt n + 2 - j) * T n j

private theorem coordinate_rejected_law : ¬ coordinate_arena.Law coordinate_rejected := by
  intro law
  have h := law 0 1
  change (0 : ℚ) = (-1 : ℚ) ^ (wt 0 + 2 - 1) * T 0 1 at h
  norm_num [wt_zero, T_one] at h

private theorem coordinate_dependence :
    ObservationalDependence coordinate_signature coordinate_actual := by
  intro role
  refine ⟨0, 0, 1, ?_⟩
  change pochhammerBasis.coord 0 (rowPolynomial 0) ≠
    pochhammerBasis.coord 1 (rowPolynomial 0)
  rw [source_coordinate, source_coordinate]
  have h : T 0 0 = 0 := by rw [T]; decide
  norm_num [wt_zero, T_one, h]

def coordinate_source : Registration coordinate_arena (type_of% (@source_coordinate)) where
  actual := coordinate_actual
  bridge := Iff.rfl
  variation := ⟨@source_coordinate, coordinate_rejected, coordinate_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity coordinate_arena.Law
    coordinate_actual coordinate_rejected coordinate_rejected_law
  dependence := coordinate_dependence

def coordinate_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@source_coordinate) (Realization coordinate_signature) Unit Unit := {
  unitName :=
    `D5.S1.Recurrence.Parity.DyadicPochhammerCoefficient.source_coordinate.__information_unit
  realizationName := `Reg.D5.S1.Recurrence.Parity.DyadicPochhammerCoefficient.coordinate_source
  realizationSource := none
  generated := false
  arena := .source ⟨coordinate_arena⟩
  objectArena := .source ⟨coordinate_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source coordinate_arena ⟨coordinate_source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize coordinate_signature
    (fun _ n j => pochhammerBasis.coord j (rowPolynomial n)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Parity.DyadicPochhammerCoefficient
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev cleared_signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℚ)

def cleared_actual : Realization cleared_signature :=
  realize cleared_signature (fun _ n i => signedCoefficient (2 * n) i) (fun e => nomatch e)

def cleared_rejected : Realization cleared_signature :=
  realize cleared_signature (fun _ n i => signedCoefficient (2 * n) i + 1)
    (fun e => nomatch e)

abbrev cleared_arena : Arena where
  signature := cleared_signature
  Law R := ∀ n i : ℕ, 0 < n → 2 ≤ i →
    (((i : ℚ) - 1) * R.readout () n i + signedCoefficient (2 * n) (i - 1) =
      (i : ℚ) * ((i : ℚ) - 1) * signedCoefficient n i +
        ((i : ℚ) - 2) * signedCoefficient n (i - 1)) ∧
    (∀ j : ℕ,
      pochhammerBasis.coord j (rowPolynomial (2 * n)) =
        (-1 : ℚ) ^ (wt (2 * n) + 2 - j) * T (2 * n) j ∧
      pochhammerBasis.coord j (rowPolynomial n) =
        (-1 : ℚ) ^ (wt n + 2 - j) * T n j)

private theorem cleared_rejected_law : ¬ cleared_arena.Law cleared_rejected := by
  intro law
  have h := (law 1 2 (by decide) (by decide)).1
  have hactual := (positiveEvenCoefficient 1 2 (by decide) (by decide)).1
  simp only [cleared_rejected, realize] at h
  rw [← hactual] at h
  norm_num at h

private theorem cleared_dependence : ObservationalDependence cleared_signature cleared_actual := by
  intro role
  refine ⟨0, 0, 1, ?_⟩
  change signedCoefficient 0 0 ≠ signedCoefficient 0 1
  have h0 : T 0 0 = 0 := by rw [T]; simp
  rw [signedCoefficient, signedCoefficient, source_coordinate, source_coordinate]
  norm_num [wt_zero, h0, T_one]

def cleared_source : Registration cleared_arena (type_of% (@positiveEvenCoefficient)) where
  actual := cleared_actual
  bridge := Iff.rfl
  variation := ⟨@positiveEvenCoefficient, cleared_rejected, cleared_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity cleared_arena.Law
    cleared_actual cleared_rejected cleared_rejected_law
  dependence := cleared_dependence

def cleared_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@positiveEvenCoefficient) (Realization cleared_signature) Unit Unit := {
  unitName := `D5.S1.Recurrence.Parity.DyadicPochhammerCoefficient.positiveEvenCoefficient.__information_unit
  realizationName := `Reg.D5.S1.Recurrence.Parity.DyadicPochhammerCoefficient.cleared_source
  realizationSource := none
  generated := false
  arena := .source ⟨cleared_arena⟩
  objectArena := .source ⟨cleared_arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source cleared_arena ⟨cleared_source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize cleared_signature
    (fun _ n i => signedCoefficient (2 * n) i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Parity.DyadicPochhammerCoefficient
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S1.Recurrence.Parity.DyadicPochhammerCoefficient
