import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment
import Reg.Support.DependentFamily

/-! Faithful four-slot audit evidence for the dimension-general contraction family.
All finite systems and matrices remain in scope, including empty systems and
singular contractions. -/

set_option autoImplicit false
set_option Elab.async false
open Matrix LeanInformationAudit
open scoped ComplexOrder
open D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment
open D5.S3.Quantum.Entanglement.AbsolutePPT.QutritPerturbationAttainment (APPT)
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment
noncomputable section

universe t s o

/-- The exact packed source coordinates A and B; dictionaries stay in each Law. -/
abbrev Params : Type 1 := Sigma (fun _ : Type => Type)

abbrev Mat (p : Params) := Matrix (p.1 × p.2) (p.1 × p.2) ℂ

abbrev owningSignature (P : Type t) (X : P → Type s) (Y : P → Type o) : Signature where
  Params := P
  State := X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ => Y
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev matrixSignature : Signature :=
  owningSignature Params Mat Mat

private theorem owningSensitivity {P : Type t} {X : P → Type s} {Y : P → Type o}
    (law : Realization (owningSignature P X Y) → Prop)
    (actual bad : Realization (owningSignature P X Y)) (hbad : ¬ law bad) :
    Sensitivity ⟨owningSignature P X Y, law⟩ actual := by
  constructor
  · intro i
    refine ⟨bad, ?_, ?_, hbad⟩
    · intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e

/-- A concrete carrier for existential audit witnesses. -/
private abbrev WitnessMat := Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ

namespace Identity
/-- The RHS operand already present in the original identity is dictionary independent. -/
def actual : Realization matrixSignature :=
  realize matrixSignature (fun _ _ X => firstTranspose X) (fun e => nomatch e)
def bad : Realization matrixSignature :=
  realize matrixSignature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := matrixSignature
  Law O := ∀ {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (X : Matrix (A × B) (A × B) ℂ),
    krausSum X = ((Fintype.card A : ℂ)-1) • 1 +
      (2 : ℂ) • O.readout () ⟨A, B⟩ X
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have he : krausSum (1 : WitnessMat) =
      ((Fintype.card (Fin 1) : ℂ)-1) • (1 : WitnessMat) +
        (2 : ℂ) • (0 : WitnessMat) :=
    h (A := Fin 1) (B := Fin 1) (1 : WitnessMat)
  rw [kraus_identity] at he
  have he' := congrArg (fun Z : WitnessMat =>
    Z ((0, 0) : Fin 1 × Fin 1) ((0, 0) : Fin 1 × Fin 1)) he
  norm_num [firstTranspose, partialTranspose, Matrix.transpose_apply,
    Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply] at he'
private theorem dependence : ObservationalDependence matrixSignature actual := by
  intro i
  refine ⟨⟨Fin 1, Fin 1⟩, (0 : WitnessMat), (1 : WitnessMat), ?_⟩
  intro h
  change firstTranspose (0 : WitnessMat) = firstTranspose (1 : WitnessMat) at h
  have he := congrArg (fun Z : WitnessMat =>
    Z ((0, 0) : Fin 1 × Fin 1) ((0, 0) : Fin 1 × Fin 1)) h
  norm_num [firstTranspose, partialTranspose, Matrix.transpose_apply,
    Matrix.one_apply] at he
def family : Registration arena (type_of% @kraus_identity) where
  actual := actual
  bridge := ⟨fun h => h, fun h => h⟩
  variation := ⟨@kraus_identity, bad, bad_law⟩
  sensitivity := owningSensitivity arena.Law actual bad bad_law
  dependence := dependence
def audit : Contract.Registration (@kraus_identity) (Realization matrixSignature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment.Identity.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment.Identity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize matrixSignature
    (fun _ _ X => firstTranspose X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "arg", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Identity

namespace Positivity
def actual : Realization matrixSignature :=
  realize matrixSignature (fun _ _ X => partialTranspose X) (fun e => nomatch e)
/-- A constant negative entry needs no equality or finiteness dictionary. -/
def bad : Realization matrixSignature :=
  realize matrixSignature (fun _ _ _ => fun _ _ => (-1 : ℂ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := matrixSignature
  Law O := ∀ {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (X : Matrix (A × B) (A × B) ℂ), X.PosSemidef → (1-X).PosSemidef →
    (((Fintype.card A : ℂ)-1) • 1 + (2 : ℂ) • O.readout () ⟨A, B⟩ X).PosSemidef
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  let N : WitnessMat := fun _ _ => (-1 : ℂ)
  have hp : (((Fintype.card (Fin 1) : ℂ)-1) • (1 : WitnessMat) +
      (2 : ℂ) • N).PosSemidef :=
    h (A := Fin 1) (B := Fin 1) (0 : WitnessMat) Matrix.PosSemidef.zero
      (by simpa only [sub_zero] using
        (Matrix.PosSemidef.one : (1 : WitnessMat).PosSemidef))
  have hd := hp.diag_nonneg (i := ((0, 0) : Fin 1 × Fin 1))
  have hr := (Complex.nonneg_iff.mp hd).1
  change 0 ≤
    (((Fintype.card (Fin 1) : ℂ) - 1) * (1 : ℂ) +
      (2 : ℂ) * (-1 : ℂ)).re at hr
  norm_num [Complex.mul_re] at hr
private theorem dependence : ObservationalDependence matrixSignature actual := by
  intro i
  refine ⟨⟨Fin 1, Fin 1⟩, (0 : WitnessMat), (1 : WitnessMat), ?_⟩
  intro h
  change partialTranspose (0 : WitnessMat) = partialTranspose (1 : WitnessMat) at h
  have he := congrArg (fun Z : WitnessMat =>
    Z ((0, 0) : Fin 1 × Fin 1) ((0, 0) : Fin 1 × Fin 1)) h
  norm_num [partialTranspose, Matrix.one_apply] at he
def family : Registration arena (type_of% @partial_transpose_posSemidef) where
  actual := actual
  bridge := ⟨fun h => h, fun h => h⟩
  variation := ⟨@partial_transpose_posSemidef, bad, bad_law⟩
  sensitivity := owningSensitivity arena.Law actual bad bad_law
  dependence := dependence
def audit : Contract.Registration (@partial_transpose_posSemidef) (Realization matrixSignature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment.Positivity.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment.Positivity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize matrixSignature
    (fun _ _ X => partialTranspose X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Positivity

namespace Absolute
def actual : Realization matrixSignature :=
  realize matrixSignature (fun _ _ X => X) (fun e => nomatch e)
def bad : Realization matrixSignature :=
  realize matrixSignature (fun _ _ _ => fun _ _ => (-1 : ℂ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := matrixSignature
  Law O := ∀ {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (X : Matrix (A × B) (A × B) ℂ), X.PosSemidef → (1-X).PosSemidef →
    APPT (((Fintype.card A : ℂ)-1) • 1 + (2 : ℂ) • O.readout () ⟨A, B⟩ X)
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  let N : WitnessMat := fun _ _ => (-1 : ℂ)
  have hp : APPT (((Fintype.card (Fin 1) : ℂ)-1) • (1 : WitnessMat) +
      (2 : ℂ) • N) :=
    h (A := Fin 1) (B := Fin 1) (0 : WitnessMat) Matrix.PosSemidef.zero
      (by simpa only [sub_zero] using
        (Matrix.PosSemidef.one : (1 : WitnessMat).PosSemidef))
  have hp1 : (partialTranspose ((1 : WitnessMat) *
      (((Fintype.card (Fin 1) : ℂ)-1) • (1 : WitnessMat) +
        (2 : ℂ) • N) *
      (1 : WitnessMat)ᴴ)).PosSemidef :=
    hp (1 : unitaryGroup (Fin 1 × Fin 1) ℂ)
  simp only [one_mul, Matrix.conjTranspose_one, mul_one] at hp1
  have hd := hp1.diag_nonneg (i := ((0, 0) : Fin 1 × Fin 1))
  have hr := (Complex.nonneg_iff.mp hd).1
  change 0 ≤
    (((Fintype.card (Fin 1) : ℂ) - 1) * (1 : ℂ) +
      (2 : ℂ) * (-1 : ℂ)).re at hr
  norm_num [Complex.mul_re] at hr
private theorem dependence : ObservationalDependence matrixSignature actual := by
  intro i
  refine ⟨⟨Fin 1, Fin 1⟩, (0 : WitnessMat), (1 : WitnessMat), ?_⟩
  intro h
  change (0 : WitnessMat) = (1 : WitnessMat) at h
  have he := congrArg (fun Z : WitnessMat =>
    Z ((0, 0) : Fin 1 × Fin 1) ((0, 0) : Fin 1 × Fin 1)) h
  norm_num [Matrix.one_apply] at he
def family : Registration arena (type_of% @contraction_appt) where
  actual := actual
  bridge := ⟨fun h => h, fun h => h⟩
  variation := ⟨@contraction_appt, bad, bad_law⟩
  sensitivity := owningSensitivity arena.Law actual bad bad_law
  dependence := dependence
def audit : Contract.Registration (@contraction_appt) (Realization matrixSignature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment.Absolute.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment.Absolute.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize matrixSignature
    (fun _ _ X => X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Absolute

namespace FiveRow
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature :=
  realize signature (fun _ _ n => (fiveRowDensity n * fiveRowDensity n).trace.re) (fun e => nomatch e)
def bad : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law O := ∀ (n : ℕ), 0 < n → (fiveRowProjector n).rank = 2*n ∧
    (fiveRowDensity n).PosSemidef ∧ (fiveRowDensity n).trace = 1 ∧
    APPT (fiveRowDensity n) ∧ O.readout () () n = 5/(24*(n : ℝ))
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hp := (h 1 (by decide)).2.2.2.2
  norm_num [bad, realize] at hp
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  change (fiveRowDensity 1 * fiveRowDensity 1).trace.re ≠
    (fiveRowDensity 2 * fiveRowDensity 2).trace.re
  rw [(five_row_attainment 1 (by decide)).2.2.2.2,
    (five_row_attainment 2 (by decide)).2.2.2.2]
  norm_num
private theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    refine ⟨bad, ?_, ?_, bad_law⟩
    · intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro e
    exact nomatch e
def family : Registration arena (type_of% @five_row_attainment) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@five_row_attainment, bad, bad_law⟩
  sensitivity := sensitivity
  dependence := dependence
def audit : Contract.Registration (@five_row_attainment) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment.FiveRow.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment.FiveRow.family
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
    (fun _ _ n => (fiveRowDensity n * fiveRowDensity n).trace.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some { owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "arg", "arg", "arg", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end FiveRow

#print axioms Identity.family
#print axioms Positivity.family
#print axioms Absolute.family
#print axioms FiveRow.family
end
end Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment
