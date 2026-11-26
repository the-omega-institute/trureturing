import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.CompleteHockeyStickChoiSupport

/-! Source-bound registration of the complete coefficient saturation theorem. -/

set_option autoImplicit false

noncomputable section

open Matrix LeanInformationAudit
open scoped CStarAlgebra ComplexOrder MatrixOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Divergence.CompleteHockeyStickRefutation (completeCoefficient)
open _root_.D5.S3.Quantum.Foundation.FiniteDiamondDistance (pureState)
open _root_.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (act)
open _root_.D5.S3.Quantum.Divergence.CompleteHockeyStickChoiSupport
  (result coefficient_le_of_replacement)
open UnitaryReconstruction.LiuWildChoiObstruction
  (bell diagonalVector normalizedChoi pairMatrix)

namespace Reg.D5.S3.Quantum.Divergence.CompleteHockeyStickChoiSupport

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private def identity : QuantumChannel (Fin 2) (Fin 2) where
  toCompletelyPositiveMap :=
    { toLinearMap := LinearMap.id
      map_cstarMatrix_nonneg' := fun _ _ h => h }
  trace_preserving _ := rfl

private theorem identity_support (v : Fin 2 → ℂ)
    (hv : ∀ i : Fin 2, (fun p : Fin 2 × Fin 2 => if p.1 = i then v p.2 else 0) ∈
      (pairMatrix (normalizedChoi identity)).mulVecLin.range) : v = 0 := by
  have hid : pairMatrix (normalizedChoi identity) =
      vecMulVec (bell (Fin 2)) (star (bell (Fin 2))) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    rfl
  ext x
  obtain ⟨i, hi⟩ := exists_ne x
  obtain ⟨w, hw⟩ := hv i
  change (pairMatrix (normalizedChoi identity) *ᵥ w) =
    (fun p => if p.1 = i then v p.2 else 0) at hw
  have h := congrFun hw (i, x)
  change (pairMatrix (normalizedChoi identity) *ᵥ w) (i, x) =
    (if i = i then v x else 0) at h
  rw [hid] at h
  simpa [Matrix.mulVec, dotProduct, vecMulVec_apply, bell, diagonalVector, hi] using h.symm

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Nonempty A] (N : QuantumChannel A B) (γ : ℝ), 1 < γ →
    (∀ v : B → ℂ, (∀ i : A, (fun p : A × B => if p.1 = i then v p.2 else 0) ∈
      (pairMatrix (normalizedChoi N)).mulVecLin.range) → v = 0) →
    R.readout () () (completeCoefficient N γ false) 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h identity 2 (by norm_num) identity_support

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h := congrFun he 1
  change ((0 : ℝ) = 1) = ((1 : ℝ) = 1) at h
  exact zero_ne_one (h.mpr rfl)

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@result) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.CompleteHockeyStickChoiSupport.result.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.CompleteHockeyStickChoiSupport.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.CompleteHockeyStickChoiSupport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

namespace ReplacementBound

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (N M : QuantumChannel A B) (τ : DensityState B) {p γ : ℝ},
    0 ≤ p → p ≤ 1 → 1 ≤ γ →
    (∀ Z, act N Z = (1 - p) • act M Z + p • (Z.trace • pairMatrix τ)) →
    R.readout () () (completeCoefficient N γ false) (1 - p)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let τ := pureState (Pi.single (0 : Fin 2) (1 : ℂ)) (by simp [dotProduct, Pi.single_apply])
  exact h identity identity τ (p := 0) (γ := 1) le_rfl zero_le_one le_rfl (by simp)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have h := congrFun he 0
  change ((0 : ℝ) ≤ 0) = ((1 : ℝ) ≤ 0) at h
  exact (not_le.mpr zero_lt_one) (h.mp le_rfl)

def family : Registration arena (type_of% @coefficient_le_of_replacement) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@coefficient_le_of_replacement, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@coefficient_le_of_replacement) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Divergence.CompleteHockeyStickChoiSupport.coefficient_le_of_replacement.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Divergence.CompleteHockeyStickChoiSupport.ReplacementBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.CompleteHockeyStickChoiSupport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end ReplacementBound

end Reg.D5.S3.Quantum.Divergence.CompleteHockeyStickChoiSupport
