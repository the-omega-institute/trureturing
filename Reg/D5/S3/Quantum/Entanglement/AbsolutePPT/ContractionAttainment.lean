import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

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

structure Systems where
  A : Type
  B : Type
  fA : Fintype A
  fB : Fintype B
  dA : DecidableEq A
  dB : DecidableEq B
attribute [instance] Systems.fA Systems.fB Systems.dA Systems.dB

def system (A B : Type) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] :
    Systems := ⟨A, B, inferInstance, inferInstance, inferInstance, inferInstance⟩
abbrev Mat (p : Systems) := Matrix (p.A × p.B) (p.A × p.B) ℂ

abbrev matrixSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Systems
    (fun p => Mat p) (fun p => Mat p)

namespace Identity
def actual : Realization matrixSignature :=
  realize matrixSignature (fun _ _ X => krausSum X) (fun e => nomatch e)
def bad : Realization matrixSignature :=
  realize matrixSignature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := matrixSignature
  Law O := ∀ {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (X : Mat (system A B)),
    O.readout () (system A B) X =
      ((Fintype.card A : ℂ)-1) • 1 + (2 : ℂ) • firstTranspose X
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have he := congrFun (congrFun
    (h (A := Fin 2) (B := Fin 1)
      (0 : Mat (system (Fin 2) (Fin 1))))
    ((0, 0) : Fin 2 × Fin 1)) ((0, 0) : Fin 2 × Fin 1)
  have hz : (partialTranspose
      (0 : Mat (system (Fin 2) (Fin 1)))).transpose = 0 := by
    ext p q
    rfl
  simp only [firstTranspose] at he
  rw [hz] at he
  simp only [bad, realize, system] at he
  let M : Mat (system (Fin 2) (Fin 1)) := 0
  let i : Fin 2 × Fin 1 := (0, 0)
  have hzero : M i i = 0 := by simp [M, i]
  have hconst : ((1 : ℂ) • (1 : Mat (system (Fin 2) (Fin 1))) +
      (2 : ℂ) • M) i i = 1 := by
    simp [M, i, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply]
  rw [hzero, hconst] at he
  norm_num at he
private theorem dependence : ObservationalDependence matrixSignature actual := by
  intro i
  refine ⟨system (Fin 1) (Fin 1), 0, 1, ?_⟩
  change krausSum (0 : Mat (system (Fin 1) (Fin 1))) ≠
    krausSum (1 : Mat (system (Fin 1) (Fin 1)))
  rw [kraus_identity, kraus_identity]
  intro h
  have he := congrFun (congrFun h ((0, 0) : Fin 1 × Fin 1))
    ((0, 0) : Fin 1 × Fin 1)
  have hz : (partialTranspose
      (0 : Mat (system (Fin 1) (Fin 1)))).transpose = 0 := by
    ext p q
    rfl
  have ho : (partialTranspose
      (1 : Mat (system (Fin 1) (Fin 1)))).transpose = 1 := by
    ext p q
    by_cases hpq : p = q
    · subst q
      simp [partialTranspose, Matrix.one_apply]
    · have hcoords : ¬ (q.1 = p.1 ∧ p.2 = q.2) := by
        intro h
        exact hpq (Prod.ext h.1.symm h.2.symm)
      simp [partialTranspose, Matrix.one_apply, hpq, hcoords]
  simp only [firstTranspose] at he
  rw [hz, ho] at he
  let M : Mat (system (Fin 1) (Fin 1)) := 0
  let N : Mat (system (Fin 1) (Fin 1)) := 1
  let i : Fin 1 × Fin 1 := (0, 0)
  have hL : (((Fintype.card (Fin 1) : ℂ) - 1) •
      (1 : Mat (system (Fin 1) (Fin 1))) + (2 : ℂ) • M) i i = 0 := by
    simp [M, i, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply]
  have hR : (((Fintype.card (Fin 1) : ℂ) - 1) •
      (1 : Mat (system (Fin 1) (Fin 1))) + (2 : ℂ) • N) i i = 2 := by
    simp [N, i, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply]
  rw [hL, hR] at he
  norm_num at he
def family : Registration arena (type_of% @kraus_identity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@kraus_identity, bad, bad_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual bad bad_law
  dependence := dependence
def audit : Contract.Registration (@kraus_identity) (Realization matrixSignature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment.Identity.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment.Identity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize matrixSignature (fun _ _ X => krausSum X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some { owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment, definition := none, coordinates := #[0,1], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "arg"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Identity

namespace Positivity
def actual : Realization matrixSignature :=
  realize matrixSignature (fun _ _ X => partialTranspose X) (fun e => nomatch e)
def bad : Realization matrixSignature :=
  realize matrixSignature (fun _ _ _ => -1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := matrixSignature
  Law O := ∀ {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (X : Mat (system A B)), X.PosSemidef → (1-X).PosSemidef →
    (((Fintype.card A : ℂ)-1) • 1 + (2 : ℂ) • O.readout () (system A B) X).PosSemidef
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hp := h (A := Fin 1) (B := Fin 1)
    (0 : Mat (system (Fin 1) (Fin 1))) Matrix.PosSemidef.zero
    (by simpa using (Matrix.PosSemidef.one :
      (1 : Mat (system (Fin 1) (Fin 1))).PosSemidef))
  have hd := hp.diag_nonneg (i := ((0,0) : Fin 1 × Fin 1))
  have hr := (Complex.nonneg_iff.mp hd).1
  simp only [bad, realize] at hr
  let M : Mat (system (Fin 1) (Fin 1)) := 1
  let i : Fin 1 × Fin 1 := (0, 0)
  have hneg : (-(2 : ℂ) • M) i i = -2 := by
    simp [M, i, Matrix.smul_apply, Matrix.one_apply]
  rw [hneg] at hr
  norm_num at hr
private theorem dependence : ObservationalDependence matrixSignature actual := by
  intro i
  refine ⟨system (Fin 1) (Fin 1), 0, 1, ?_⟩
  intro h
  let M : Mat (system (Fin 1) (Fin 1)) := 0
  let N : Mat (system (Fin 1) (Fin 1)) := 1
  have h' : partialTranspose M = partialTranspose N := by
    simpa [actual, realize, M, N] using h
  have he := congrArg (fun Z : Mat (system (Fin 1) (Fin 1)) =>
      Z ((0, 0) : Fin 1 × Fin 1) ((0, 0) : Fin 1 × Fin 1)) h'
  have hz : partialTranspose M (0, 0) (0, 0) = 0 := by rfl
  have ho : partialTranspose N (0, 0) (0, 0) = 1 := by
    simp [partialTranspose, N, Matrix.one_apply]
  rw [hz, ho] at he
  norm_num at he
def family : Registration arena (type_of% @partial_transpose_posSemidef) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@partial_transpose_posSemidef, bad, bad_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual bad bad_law
  dependence := dependence
def audit : Contract.Registration (@partial_transpose_posSemidef) (Realization matrixSignature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment.Positivity.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment.Positivity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize matrixSignature (fun _ _ X => partialTranspose X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some { owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment, definition := none, coordinates := #[0,1], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Positivity

namespace Absolute
def actual : Realization matrixSignature :=
  realize matrixSignature (fun _ _ X => X) (fun e => nomatch e)
def bad : Realization matrixSignature :=
  realize matrixSignature (fun _ _ _ => -1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := matrixSignature
  Law O := ∀ {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (X : Mat (system A B)), X.PosSemidef → (1-X).PosSemidef →
    APPT (((Fintype.card A : ℂ)-1) • 1 + (2 : ℂ) • O.readout () (system A B) X)
private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hp := h (A := Fin 1) (B := Fin 1)
    (0 : Mat (system (Fin 1) (Fin 1))) Matrix.PosSemidef.zero
    (by simpa using (Matrix.PosSemidef.one :
      (1 : Mat (system (Fin 1) (Fin 1))).PosSemidef))
    (1 : unitaryGroup (Fin 1 × Fin 1) ℂ)
  have hd := hp.diag_nonneg (i := ((0,0) : Fin 1 × Fin 1))
  have hr := (Complex.nonneg_iff.mp hd).1
  simp only [bad, realize, system] at hr
  let M : Mat (system (Fin 1) (Fin 1)) := 1
  let i : Fin 1 × Fin 1 := (0, 0)
  have hneg : (1 * (0 • (1 : Mat (system (Fin 1) (Fin 1))) +
      (2 : ℂ) • (-M)) * 1) i i = -2 := by
    simp [M, i, Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply,
      Matrix.one_apply, Fintype.sum_unique]
  rw [hneg] at hr
  norm_num at hr
private theorem dependence : ObservationalDependence matrixSignature actual := by
  intro i
  refine ⟨system (Fin 1) (Fin 1), 0, 1, ?_⟩
  intro h
  let M : Mat (system (Fin 1) (Fin 1)) := 0
  let N : Mat (system (Fin 1) (Fin 1)) := 1
  have h' : M = N := by simpa [actual, realize, M, N] using h
  have he := congrArg (fun Z : Mat (system (Fin 1) (Fin 1)) =>
      Z ((0, 0) : Fin 1 × Fin 1) ((0, 0) : Fin 1 × Fin 1)) h'
  change (0 : ℂ) = 1 at he
  norm_num at he
def family : Registration arena (type_of% @contraction_appt) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@contraction_appt, bad, bad_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual bad bad_law
  dependence := dependence
def audit : Contract.Registration (@contraction_appt) (Realization matrixSignature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment.Absolute.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment.Absolute.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize matrixSignature (fun _ _ X => X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some { owner := `D5.S3.Quantum.Entanglement.AbsolutePPT.ContractionAttainment, definition := none, coordinates := #[0,1], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "arg"], stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
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
