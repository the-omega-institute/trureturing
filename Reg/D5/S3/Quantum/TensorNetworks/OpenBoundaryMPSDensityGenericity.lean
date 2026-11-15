import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity
import Reg.Support.SingleDependentReadout

/-! Source-bound observations of the real polynomial and the actual-image locus. -/

set_option autoImplicit false
noncomputable section

namespace Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity

open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityRecovery
open _root_.D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection (Bond Word)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MvPolynomial

namespace Genericity

abbrev signature : Signature where
  Params := ℕ
  State _ := ∀ m : ℕ, Set (openBoundaryMPS (3 + m))
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ m := Set (openBoundaryMPS (3 + m))
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ m family => family m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ m : ℕ,
    (R.readout () m goodStates).Nonempty ∧ IsOpen (goodStates m) ∧ Dense (goodStates m) ∧
      ∀ ψ ∈ goodStates m, ∀ φ : Word (3 + m) → ℂ,
        φ ∈ openBoundaryMPS (3 + m) →
        (rawPrefix 3 m φ = rawPrefix 3 m (ψ : Word (3 + m) → ℂ) ↔
          ∃ z : ℂ, ‖z‖ = 1 ∧ φ = z • (ψ : Word (3 + m) → ℂ))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact Set.not_nonempty_empty (h 0).1

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, (fun _ => ∅), (fun _ => Set.univ), ?_⟩
  intro he
  let ψ : openBoundaryMPS 3 := ⟨mpsState 3 0 0 0 0, ⟨0, 0, 0, 0, rfl⟩⟩
  have hbad := congrArg (fun S : Set (openBoundaryMPS 3) => ψ ∈ S) he
  exact (show ψ ∉ (∅ : Set (openBoundaryMPS 3)) from Set.notMem_empty ψ)
    (Eq.mpr hbad (Set.mem_univ ψ))

def family : Registration arena (type_of% (@intrinsic_recovery_genericity)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨intrinsic_recovery_genericity, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@intrinsic_recovery_genericity) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity.Genericity.unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity.Genericity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ m family => family m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Genericity

namespace Polynomial

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => Word 3 → ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ t => eval (realCoordinates t) recoveryPolynomial) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ t : Word 3 → ℂ,
    R.readout () () t ≠ 0 ↔
      eval t chartPoly ≠ 0 ∧ Function.Injective (transfer (canonicalCore t))

private theorem nonzero_witness : ∃ t : Word 3 → ℂ,
    eval (realCoordinates t) recoveryPolynomial ≠ 0 := by
  obtain ⟨ψ, hψ⟩ := (intrinsic_recovery_genericity 0).1
  refine ⟨fixedTensor (rawPrefix 3 0 ψ), ?_⟩
  change eval (realCoordinates (fun ij => rawPrefix 3 0
    (ψ : Word 3 → ℂ) ij.1 ij.2)) observedPolynomial ≠ 0 at hψ
  rw [observedPolynomial, eval_rename] at hψ
  have hc : (realCoordinates (fun ij => rawPrefix 3 0 (ψ : Word 3 → ℂ) ij.1 ij.2) ∘
      Sum.map (fun u => (u, fun _ => 0)) (fun u => (u, fun _ => 0))) =
        realCoordinates (fixedTensor (rawPrefix 3 0 ψ)) := by
    funext v
    cases v <;> rfl
  rwa [hc] at hψ

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨t, ht⟩ := nonzero_witness
  exact ((h t).mpr ((recoveryPolynomial_ne_zero t).mp ht)) rfl

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨t, ht⟩ := nonzero_witness
  have hz : eval (realCoordinates (0 : Word 3 → ℂ)) recoveryPolynomial = 0 := by
    by_contra hn
    have hg := ((recoveryPolynomial_ne_zero _).mp hn).1
    have hd : eval (0 : Word 3 → ℂ) minorPoly = 0 := by
      norm_num [minorPoly, kernelMinor, kernelMatrix, coordinate, Matrix.det_fin_three]
    exact hg (by simp only [chartPoly, map_mul, hd, zero_mul])
  refine ⟨(), 0, t, ?_⟩
  intro he
  change eval (realCoordinates (0 : Word 3 → ℂ)) recoveryPolynomial =
    eval (realCoordinates t) recoveryPolynomial at he
  exact ht (he.symm.trans hz)

def family : Registration arena (type_of% (@recoveryPolynomial_ne_zero)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨recoveryPolynomial_ne_zero, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@recoveryPolynomial_ne_zero) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity.Polynomial.unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity.Polynomial.family
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
    (fun _ _ t => eval (realCoordinates t) recoveryPolynomial) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Polynomial

#print axioms Genericity.registration
#print axioms Polynomial.registration

end Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityGenericity
