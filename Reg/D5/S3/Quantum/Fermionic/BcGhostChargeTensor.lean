import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Fermionic.BcGhostChargeTensor
import Mathlib.LinearAlgebra.TensorProduct.Unitors

/-! Source-family candidate retaining arbitrary complex matter and all mode premises. -/

noncomputable section
namespace Reg.D5.S3.Quantum.Fermionic.BcGhostChargeTensor

open scoped TensorProduct
open _root_.D5.S3.Quantum.Fermionic.CountableOccupationFock
open _root_.D5.S3.Quantum.Fermionic.BcGhostChargeTensor
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

structure Matter where
  Carrier : Type
  group : AddCommGroup Carrier
  complexModule : @Module ℂ Carrier _ group.toAddCommMonoid

attribute [instance] Matter.group Matter.complexModule

abbrev joint (P : Matter) := P.Carrier ⊗[ℂ] Fock
abbrev jointEnd (P : Matter) := Module.End ℂ (joint P)

abbrev signature : Signature where
  Params := Matter
  State P := jointEnd P
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := jointEnd P
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ E => E)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (P : Matter) (E : jointEnd P),
    (∀ m : ℤ, E * B m = B m * E) →
    (∀ m : ℤ, E * C m = C m * E) →
    ∀ (d : ℂ), d ≠ 0 → number * E - E * number = d • E → R.readout () P E = 0

def rejected : Realization signature := realize signature (fun _ _ _ => 1)
  (fun e => nomatch e)

private def scalarMatter : Matter := ⟨ℂ, inferInstance, inferInstance⟩

private theorem identity_ne_zero : (1 : jointEnd scalarMatter) ≠ 0 := by
  intro h
  have hz := LinearMap.congr_fun h ((1 : ℂ) ⊗ₜ[ℂ] vacuum)
  have hv := congrArg (TensorProduct.lid ℂ Fock) hz
  simpa [vacuum, ket] using hv

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h scalarMatter 0 (by intro m; simp) (by intro m; simp)
    1 one_ne_zero (by simp)
  exact identity_ne_zero hz

def family : Registration arena (type_of% @charged_commutant_vanishes.{0}) where
  actual := actual
  bridge := by
    constructor
    · intro h M iM mM E hb hc d hd hdegree
      exact h ⟨M, iM, mM⟩ E hb hc d hd hdegree
    · intro h P E hb hc d hd hdegree
      exact h E hb hc d hd hdegree
  variation := ⟨by
    intro P E hb hc d hd hdegree
    exact charged_commutant_vanishes E hb hc d hd hdegree,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro role
    refine ⟨scalarMatter, 0, 1, ?_⟩
    exact Ne.symm identity_ne_zero

def charged_commutant_audit : Contract.Registration
    (@charged_commutant_vanishes.{0}) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostChargeTensor.chargedCommutantUnit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostChargeTensor.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ E => E) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (jointEnd scalarMatter)
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostChargeTensor
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Fermionic.BcGhostChargeTensor
