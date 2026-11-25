import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.Auric.UnequalBlockBoundary
import Reg.Support.SingleDependentReadout
import Mathlib.Data.Matrix.Basis

/-! Readouts of the matrix identities, spectral agreement and two exact boundary values. -/

namespace Reg.D5.S3.Quantum.Measurement.Auric.UnequalBlockBoundary

open _root_.D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects
open _root_.D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects.Boundary
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped BigOperators ComplexOrder MatrixOrder

universe u t s o

set_option autoImplicit false

noncomputable section

private theorem oneReadoutSensitivity
    {S : Signature.{t,s,0,o,0}} [Subsingleton S.Role] [IsEmpty S.Anchor]
    (law : Realization S → Prop) (actual bad : Realization S) (hbad : ¬ law bad) :
    Sensitivity ⟨S, law⟩ actual := by
  constructor
  · intro i
    refine ⟨bad, fun j hj => (hj (Subsingleton.elim j i)).elim, ?_, hbad⟩
    funext e
    exact isEmptyElim e
  · intro e
    exact isEmptyElim e

private abbrev EmptyCarrier := ULift.{u} (Fin 0)

private theorem emptyFeasible :
    Feasible (fun _ => 0) (fun _ => 0) (fun _ : Fin 3 => (0 : Matrix EmptyCarrier.{u} EmptyCarrier.{u} ℂ)) := by
  refine ⟨fun _ => Matrix.PosSemidef.zero, Subsingleton.elim _ _, ?_, ?_⟩
  · intro j
    simp
  · intro j
    simp [Matrix.rank_zero]

namespace MatrixEquality

abbrev signature : Signature where
  Params := Type u
  State n := Matrix n n ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Matrix n n ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ X => Eq X) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  refine ⟨ULift.{u} Unit, 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  change ((0 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) = 0) = (1 = 0) at he
  exact one_ne_zero (Eq.mp he rfl)

private abbrev zeroArena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (_ : A.PosSemidef) (_ : A.trace.re = 0), R.readout () n A 0

private theorem zeroRejected : ¬ zeroArena.{u}.Law rejected := by
  intro h
  exact @h EmptyCarrier.{u} inferInstance inferInstance 0 Matrix.PosSemidef.zero (by simp)

private abbrev capArena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} {m : ℕ}
    (_ : A.PosSemidef) (_ : A ≤ 1) (_ : A.rank ≤ m)
    (_ : A.trace.re = (cap (Fintype.card n) m : ℝ)), R.readout () n (A * A) A

private theorem capRejected : ¬ capArena.{u}.Law rejected := by
  intro h
  exact @h EmptyCarrier.{u} inferInstance inferInstance 0 0 Matrix.PosSemidef.zero
    (le_of_eq (Subsingleton.elim _ _)) (by simp [Matrix.rank_zero]) (by simp [cap])

private abbrev annihilationArena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] {P B C : Matrix n n ℂ}
    (_ : P.IsHermitian) (_ : P * P = P) (_ : B.PosSemidef) (_ : C.PosSemidef)
    (_ : B + C = 1 - P), R.readout () n (P * B) 0 ∧ B * P = 0

private theorem annihilationRejected : ¬ annihilationArena.{u}.Law rejected := by
  intro h
  exact (@h EmptyCarrier.{u} inferInstance inferInstance 0 0 0
    Matrix.PosSemidef.zero.isHermitian (by simp) Matrix.PosSemidef.zero Matrix.PosSemidef.zero
    (Subsingleton.elim _ _)).1

private abbrev reductionArena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] {A : Fin 3 → Matrix n n ℂ}
    (_ : ∀ r, (A r).PosSemidef) (_ : ∑ r, A r = 1) {j i k : Fin 3}
    (_ : j ≠ i) (_ : j ≠ k) (_ : i ≠ k) (_ : A j * A j = A j),
    R.readout () n (A i + A k) (1 - A j) ∧ A j * A i = 0 ∧ A i * A j = 0 ∧
      A j * A k = 0 ∧ A k * A j = 0 ∧ Commute (A i) (A k)

private theorem reductionRejected : ¬ reductionArena.{u}.Law rejected := by
  intro h
  exact (@h EmptyCarrier.{u} inferInstance inferInstance (fun _ => 0)
    emptyFeasible.1 emptyFeasible.2.1 0 1 2 (by decide) (by decide) (by decide) (by simp)).1

def zeroRegistration : Registration zeroArena.{u} (type_of% @effect_eq_zero_of_trace_zero.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@effect_eq_zero_of_trace_zero.{u}, rejected, zeroRejected⟩
  sensitivity := oneReadoutSensitivity zeroArena.{u}.Law actual rejected zeroRejected
  dependence := dependence

def zeroAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@effect_eq_zero_of_trace_zero.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects.Boundary.effect_eq_zero_of_trace_zero.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.Auric.UnequalBlockBoundary.MatrixEquality.zeroRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨zeroArena.{u}⟩
  objectArena := .source ⟨zeroArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source zeroArena.{u} ⟨zeroRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ X => Eq X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.Auric.UnequalBlockBoundary
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def capRegistration : Registration capArena.{u} (type_of% @effect_sq_eq_self_of_trace_cap.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@effect_sq_eq_self_of_trace_cap.{u}, rejected, capRejected⟩
  sensitivity := oneReadoutSensitivity capArena.{u}.Law actual rejected capRejected
  dependence := dependence

def capAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@effect_sq_eq_self_of_trace_cap.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects.Boundary.effect_sq_eq_self_of_trace_cap.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.Auric.UnequalBlockBoundary.MatrixEquality.capRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨capArena.{u}⟩
  objectArena := .source ⟨capArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source capArena.{u} ⟨capRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ X => Eq X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.Auric.UnequalBlockBoundary
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def annihilationRegistration : Registration annihilationArena.{u} (type_of% @projection_mul_effect_eq_zero.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@projection_mul_effect_eq_zero.{u}, rejected, annihilationRejected⟩
  sensitivity := oneReadoutSensitivity annihilationArena.{u}.Law actual rejected annihilationRejected
  dependence := dependence

def annihilationAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@projection_mul_effect_eq_zero.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects.Boundary.projection_mul_effect_eq_zero.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.Auric.UnequalBlockBoundary.MatrixEquality.annihilationRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨annihilationArena.{u}⟩
  objectArena := .source ⟨annihilationArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source annihilationArena.{u} ⟨annihilationRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ X => Eq X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.Auric.UnequalBlockBoundary
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def reductionRegistration : Registration reductionArena.{u} (type_of% @projection_row_reduces.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@projection_row_reduces.{u}, rejected, reductionRejected⟩
  sensitivity := oneReadoutSensitivity reductionArena.{u}.Law actual rejected reductionRejected
  dependence := dependence

def reductionAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@projection_row_reduces.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects.Boundary.projection_row_reduces.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.Auric.UnequalBlockBoundary.MatrixEquality.reductionRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨reductionArena.{u}⟩
  objectArena := .source ⟨reductionArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source reductionArena.{u} ⟨reductionRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ X => Eq X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.Auric.UnequalBlockBoundary
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn", "arg", "fn",
        "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MatrixEquality

namespace Commutation

abbrev signature : Signature where
  Params := Σ n : Type u, Fintype n
  State p := Matrix p.1 p.1 ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix p.1 p.1 ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p X => by
    letI := p.2
    exact Commute X) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev commuteArena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [hn : Fintype n] [DecidableEq n]
    {m : Fin 3 → ℕ} {τ : Fin 3 → ℝ} {A : Fin 3 → Matrix n n ℂ}
    (_ : Feasible m τ A) {j : Fin 3}
    (_ : τ j = 0 ∨ τ j = (cap (Fintype.card n) (m j) : ℝ)),
    ∀ r s : Fin 3, R.readout () ⟨n, hn⟩ (A r) (A s)

private theorem commuteArenaRejected : ¬ commuteArena.{u}.Law rejected := by
  intro h
  exact @h EmptyCarrier.{u} inferInstance inferInstance (fun _ => 0) (fun _ => 0)
    (fun _ => 0) emptyFeasible 0 (Or.inl rfl) 0 1

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  let a : ULift.{u} Bool := ⟨false⟩
  let b : ULift.{u} Bool := ⟨true⟩
  let X := Matrix.single a b (1 : ℂ)
  let Y := Matrix.single b a (1 : ℂ)
  refine ⟨⟨ULift.{u} Bool, inferInstance⟩, 0, X, ?_⟩
  intro h
  have he := congrFun h Y
  change Commute (0 : Matrix (ULift.{u} Bool) (ULift.{u} Bool) ℂ) Y = Commute X Y at he
  have hXY : Commute X Y := Eq.mp he (Commute.zero_left Y)
  have entry := congrArg (fun Z : Matrix (ULift.{u} Bool) (ULift.{u} Bool) ℂ => Z a a) hXY.eq
  have hprod : X * Y = Matrix.single a a (1 : ℂ) := by
    simp [X, Y, Matrix.single_mul_single_same]
  have hrev : Y * X = Matrix.single b b (1 : ℂ) := by
    simp [X, Y, Matrix.single_mul_single_same]
  have hne : b ≠ a := by decide
  rw [hprod, hrev] at entry
  simpa [Matrix.single, hne] using entry

def commuteRegistration : Registration commuteArena.{u} (type_of% @commute_on_boundary.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@commute_on_boundary.{u}, rejected, commuteArenaRejected⟩
  sensitivity := oneReadoutSensitivity commuteArena.{u}.Law actual rejected commuteArenaRejected
  dependence := dependence

def commuteAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@commute_on_boundary.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects.Boundary.commute_on_boundary.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.Auric.UnequalBlockBoundary.Commutation.commuteRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨commuteArena.{u}⟩
  objectArena := .source ⟨commuteArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source commuteArena.{u} ⟨commuteRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ p X => by
    letI := p.2
    exact Commute X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.Auric.UnequalBlockBoundary
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Commutation

namespace SpectralEquality

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x => Eq x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev spectralArena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    {m : Fin 3 → ℕ} {τ : Fin 3 → ℝ} {A : Fin 3 → Matrix n n ℂ}
    (hA : Feasible m τ A) {j i k : Fin 3} (_ : j ≠ i) (_ : j ≠ k) (_ : i ≠ k)
    (_ : τ j = 0 ∨ τ j = (cap (Fintype.card n) (m j) : ℝ)),
    R.readout () () (spectralSum Real.negMulLog A hA.1)
      (spectralSum (fun x => Real.negMulLog (1 - x)) A hA.1)

private theorem spectralArenaRejected : ¬ spectralArena.{u}.Law rejected := by
  intro h
  exact @h EmptyCarrier.{u} inferInstance inferInstance (fun _ => 0) (fun _ => 0)
    (fun _ => 0) emptyFeasible 0 1 2 (by decide) (by decide) (by decide) (Or.inl rfl)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  change ((0 : ℝ) = 0) = (1 = 0) at he
  exact one_ne_zero (Eq.mp he rfl)

def spectralRegistration : Registration spectralArena.{u} (type_of% @spectralSum_eq_complement_on_boundary.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@spectralSum_eq_complement_on_boundary.{u}, rejected, spectralArenaRejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    spectralArena.{u}.Law actual rejected spectralArenaRejected
  dependence := dependence

def spectralAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@spectralSum_eq_complement_on_boundary.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects.Boundary.spectralSum_eq_complement_on_boundary.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.Auric.UnequalBlockBoundary.SpectralEquality.spectralRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨spectralArena.{u}⟩
  objectArena := .source ⟨spectralArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source spectralArena.{u} ⟨spectralRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Eq x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.Auric.UnequalBlockBoundary
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SpectralEquality

namespace BoundaryValue

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ count => boundaryValue count) (fun e => nomatch e)

/-- Replacing the entropy readout by a negative value contradicts attainment. -/
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => -1) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 2, ?_⟩
  intro h
  have he := congrFun h 1
  change boundaryValue 0 1 = boundaryValue 2 1 at he
  have hp : 0 < boundaryValue 2 1 := by
    unfold boundaryValue
    refine mul_pos (by norm_num) (Real.binEntropy_pos ?_ ?_)
    · norm_num
    · norm_num
  have hz : boundaryValue 0 1 = 0 := by simp [boundaryValue]
  exact hp.ne' (he.symm.trans hz)

private theorem noNegativeMaximumOnEmpty {m : Fin 3 → ℕ} {τ : Fin 3 → ℝ} :
    ¬ CommonMaximum (n := EmptyCarrier.{u}) m τ (-1) := by
  rintro ⟨⟨A, hA, hvalue, _⟩, _⟩
  norm_num [spectralSum, Finset.univ_eq_empty] at hvalue

private abbrev saturatedArena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (m : Fin 3 → ℕ) (τ : Fin 3 → ℝ) {j i k : Fin 3}
    (_ : j ≠ i) (_ : j ≠ k) (_ : i ≠ k)
    (_ : ∑ r, missing (Fintype.card n) (m r) ≤ Fintype.card n)
    (_ : ∀ r, 0 ≤ τ r) (_ : ∑ r, τ r = Fintype.card n)
    (_ : τ j = (cap (Fintype.card n) (m j) : ℝ)),
    CommonMaximum (n := n) m τ (R.readout () () (missing (Fintype.card n) (m j)) (τ i))

private theorem saturatedArenaRejected : ¬ saturatedArena.{u}.Law rejected := by
  intro h
  apply noNegativeMaximumOnEmpty (m := fun _ => 0) (τ := fun _ => 0)
  exact @h EmptyCarrier.{u} inferInstance inferInstance (fun _ => 0) (fun _ => 0)
    0 1 2 (by decide) (by decide) (by decide)
    (by simp [missing]) (fun _ => le_rfl) (by simp) (by simp [cap])

private abbrev zeroRowArena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (m : Fin 3 → ℕ) (τ : Fin 3 → ℝ) {j i k : Fin 3}
    (_ : j ≠ i) (_ : j ≠ k) (_ : i ≠ k)
    (_ : ∑ r, missing (Fintype.card n) (m r) ≤ Fintype.card n)
    (_ : ∀ r, 0 ≤ τ r) (_ : ∀ r, τ r ≤ (cap (Fintype.card n) (m r) : ℝ))
    (_ : ∑ r, τ r = Fintype.card n) (_ : τ j = 0),
    CommonMaximum (n := n) m τ
      (R.readout () ()
        (Fintype.card n - missing (Fintype.card n) (m i) - missing (Fintype.card n) (m k))
        (τ i - missing (Fintype.card n) (m k)))

private theorem zeroRowArenaRejected : ¬ zeroRowArena.{u}.Law rejected := by
  intro h
  apply noNegativeMaximumOnEmpty (m := fun _ => 0) (τ := fun _ => 0)
  exact @h EmptyCarrier.{u} inferInstance inferInstance (fun _ => 0) (fun _ => 0)
    0 1 2 (by decide) (by decide) (by decide)
    (by simp [missing]) (fun _ => le_rfl) (fun _ => by simp) (by simp) rfl

def saturatedRegistration : Registration saturatedArena.{u} (type_of% @saturated_face_maximum.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@saturated_face_maximum.{u}, rejected, saturatedArenaRejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    saturatedArena.{u}.Law actual rejected saturatedArenaRejected
  dependence := dependence

def saturatedAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@saturated_face_maximum.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects.Boundary.saturated_face_maximum.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.Auric.UnequalBlockBoundary.BoundaryValue.saturatedRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨saturatedArena.{u}⟩
  objectArena := .source ⟨saturatedArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source saturatedArena.{u} ⟨saturatedRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ count => boundaryValue count) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.Auric.UnequalBlockBoundary
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "arg",
        "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def zeroRowRegistration : Registration zeroRowArena.{u} (type_of% @zero_row_face_maximum.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@zero_row_face_maximum.{u}, rejected, zeroRowArenaRejected⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    zeroRowArena.{u}.Law actual rejected zeroRowArenaRejected
  dependence := dependence

def zeroRowAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@zero_row_face_maximum.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects.Boundary.zero_row_face_maximum.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.Auric.UnequalBlockBoundary.BoundaryValue.zeroRowRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨zeroRowArena.{u}⟩
  objectArena := .source ⟨zeroRowArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source zeroRowArena.{u} ⟨zeroRowRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ count => boundaryValue count) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.Auric.UnequalBlockBoundary
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end BoundaryValue

end

end Reg.D5.S3.Quantum.Measurement.Auric.UnequalBlockBoundary
