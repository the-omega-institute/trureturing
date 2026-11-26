import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.ConditionalExpansion.HeraldedRecoveryLowerBound
import D5.S3.Quantum.Foundation.FinitePreparationChannel

/-! Source-equivalence registrations for the two main comparison statements. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

noncomputable section

open Matrix LeanInformationAudit
open scoped BigOperators CStarAlgebra ComplexOrder Kronecker MatrixOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Divergence.ConditionalExpansion
open _root_.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
  (act amp posTrace ptr ratios)
open _root_.D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open _root_.D5.S3.Quantum.Foundation.FinitePreparationChannel
  (finite_preparation_quantum_channel)
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState QuantumChannel)
open _root_.D5.S3.Quantum.Foundation.FiniteDiamondDistance (pureState)

namespace Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.HeraldedRecoveryLowerBound

open _root_.Reg.Support.SingleDependentReadout (signature sensitivity)

universe u v w z

namespace Contrast

private abbrev observation := signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization observation :=
  realize observation (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization observation :=
  realize observation (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := observation
  Law R := ∀ {A : Type u} {B : Type v} {Ref : Type w} {J : Type z}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype Ref] [DecidableEq Ref] [Fintype J]
    (N : QuantumChannel A B) (K : J → Matrix A B ℂ) (p : ℝ) (hp : 0 ≤ p) (hp₁ : p ≤ 1)
    (heffect : (∑ j, (K j)ᴴ * K j) ≤ (1 : Matrix B B ℂ))
    (hrec : ∀ X : Matrix A A ℂ,
      MatrixMap.of_kraus K K (act N X) = (p : ℂ) • X)
    (H : Matrix (Ref × A) (Ref × A) ℂ) (hH : H.IsHermitian),
    R.readout () () (p * (posTrace H - posTrace (ptr H)))
      (posTrace (amp N H) - posTrace (ptr H))

private theorem rejected_law : ¬ arena.{u,v,w,z}.Law rejected := by
  intro h
  let A := ULift.{u} (Fin 2)
  let B := ULift.{v} Unit
  let Ref := ULift.{w} Unit
  let J := ULift.{z} Unit
  let ω : DensityState B :=
    pureState (Pi.single (default : B) (1 : ℂ)) (by simp [dotProduct, Pi.single_apply])
  obtain ⟨N, _⟩ := finite_preparation_quantum_channel (fun _ : A => ω)
  have hrec : ∀ X : Matrix A A ℂ,
      MatrixMap.of_kraus (fun _ : J => (0 : Matrix A B ℂ))
        (fun _ : J => (0 : Matrix A B ℂ)) (act N X) = (0 : ℂ) • X := by
    intro X
    simp [MatrixMap.of_kraus, LinearMap.coe_mk, AddHom.coe_mk]
  have hbad := h (A := A) (B := B) (Ref := Ref) (J := J) N
    (fun _ : J => (0 : Matrix A B ℂ)) 0 (by norm_num) (by norm_num)
    (by simp) hrec (0 : Matrix (Ref × A) (Ref × A) ℂ) Matrix.isHermitian_zero
  simpa [rejected, realize] using hbad

private theorem dependence : ObservationalDependence observation actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  norm_num [actual, realize] at he

def family : Registration arena.{u,v,w,z}
    (type_of% @heralded_recovery_contrast_lower_bound.{u,v,w,z}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@heralded_recovery_contrast_lower_bound.{u,v,w,z}, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@heralded_recovery_contrast_lower_bound.{u,v,w,z})
      (Realization observation) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Divergence.ConditionalExpansion.heralded_recovery_contrast_lower_bound.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.HeraldedRecoveryLowerBound.Contrast.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w,z}⟩
  objectArena := .source ⟨arena.{u,v,w,z}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w,z} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize observation (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.ConditionalExpansion.HeraldedRecoveryLowerBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Contrast

namespace CoefficientComparison

private abbrev observation := signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization observation :=
  realize observation (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization observation :=
  realize observation (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := observation
  Law R := ∀ {A B : Type}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (N : QuantumChannel A B) (hd : 2 ≤ Fintype.card A)
    (γ : ℝ) (hγ : 1 ≤ γ) (orth : Bool),
    let pRec := sSup (heraldedRecoveryProbabilities N)
    let η := sInf (ratios N γ orth)
    R.readout () () pRec η ∧ η ≤ (Fintype.card A : ℝ) ^ 2 * pRec ∧
      (0 < η ↔ ∃ q ∈ heraldedRecoveryProbabilities N, 0 < q)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let A := Fin 2
  let B := Unit
  let ω : DensityState B :=
    pureState (Pi.single (default : B) (1 : ℂ)) (by simp [dotProduct, Pi.single_apply])
  obtain ⟨N, _⟩ := finite_preparation_quantum_channel (fun _ : A => ω)
  exact (h N (by simp [A]) 1 (by norm_num) false).1

private theorem dependence : ObservationalDependence observation actual := by
  intro _
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  norm_num [actual, realize] at he

def family : Registration arena
    (type_of% @heralded_recovery_coefficient_comparison) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@heralded_recovery_coefficient_comparison, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@heralded_recovery_coefficient_comparison)
      (Realization observation) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Divergence.ConditionalExpansion.heralded_recovery_coefficient_comparison.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.HeraldedRecoveryLowerBound.CoefficientComparison.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize observation (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.ConditionalExpansion.HeraldedRecoveryLowerBound
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CoefficientComparison

end Reg.D5.S3.Quantum.Divergence.ConditionalExpansion.HeraldedRecoveryLowerBound
