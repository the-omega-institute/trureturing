import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Fermionic.BcGhostChargeTensor
import Mathlib.LinearAlgebra.TensorProduct.Associator

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
  simp only [Module.End.one_apply, LinearMap.zero_apply, TensorProduct.lid_tmul,
    one_smul, map_zero] at hv
  exact (by simp [vacuum, ket] : vacuum ≠ 0) hv

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h scalarMatter 0 (by intro m; simp) (by intro m; simp)
    1 one_ne_zero (by simp)
  exact identity_ne_zero hz

def family : Registration arena (type_of% @charged_commutant_vanishes.{0}) where
  actual := actual
  bridge := by
    constructor
    · intro h P E hb hc d hd hdegree
      exact h E hb hc d hd hdegree
    · intro h M iM mM E hb hc d hd hdegree
      exact h ⟨M, iM, mM⟩ E hb hc d hd hdegree
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


private def vacuumState : joint scalarMatter := (1 : ℂ) ⊗ₜ[ℂ] vacuum
private def chargedState : joint scalarMatter := (1 : ℂ) ⊗ₜ[ℂ] ket {1}

private theorem vacuumState_ne_zero : vacuumState ≠ 0 := by
  intro h
  have hv := congrArg (TensorProduct.lid ℂ Fock) h
  simp only [vacuumState, TensorProduct.lid_tmul, one_smul, map_zero] at hv
  exact (by simp [vacuum, ket] : vacuum ≠ 0) hv

private theorem chargedState_ne_zero : chargedState ≠ 0 := by
  intro h
  have hv := congrArg (TensorProduct.lid ℂ Fock) h
  simp only [chargedState, TensorProduct.lid_tmul, one_smul, map_zero] at hv
  exact (by simp [ket] : ket {1} ≠ 0) hv

private theorem number_vacuumState : number vacuumState = 0 := by
  simp only [number, liftGhost, vacuumState, TensorProduct.map_tmul, LinearMap.id_apply,
    _root_.D5.S3.Quantum.Fermionic.BcGhostCharge.ghost_number_relations.1,
    TensorProduct.tmul_zero]

private theorem number_chargedState : number chargedState = chargedState := by
  have h : _root_.D5.S3.Quantum.Fermionic.BcGhostCharge.ghostNumber (ket {1}) = ket {1} := by
    have hcharge : _root_.D5.S3.Quantum.Fermionic.BcGhostCharge.charge ({1} : Finset ℕ) = 1 := by
      norm_num [_root_.D5.S3.Quantum.Fermionic.BcGhostCharge.charge, Finset.filter_singleton]
    simp only [_root_.D5.S3.Quantum.Fermionic.BcGhostCharge.ghostNumber,
      ket, Finsupp.lsum_single, LinearMap.smulRight_apply, LinearMap.id_apply, one_smul,
      hcharge, Int.cast_one]
  simp only [number, liftGhost, chargedState, TensorProduct.map_tmul, LinearMap.id_apply, h]

namespace Capture

abbrev signature : Signature where
  Params := Matter
  State P := joint P
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ P := Finset ℤ → joint P
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ x L => partialNumber L x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (P : Matter) (x : joint P), ∃ K : Finset ℤ,
    ∀ L : Finset ℤ, K ⊆ L → R.readout () P x L = number x

def rejected : Realization signature := realize signature (fun _ _ x _ => x)
  (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨K, hK⟩ := h scalarMatter vacuumState
  have hz := hK K (fun _ hi => hi)
  change vacuumState = number vacuumState at hz
  rw [number_vacuumState] at hz
  exact vacuumState_ne_zero hz

def family : Registration arena (type_of% @tensor_finite_capture.{0}) where
  actual := actual
  bridge := by
    constructor
    · intro h P x
      exact h x
    · intro h M iM mM x
      exact h ⟨M, iM, mM⟩ x
  variation := ⟨fun P x => tensor_finite_capture x, rejected, rejected_law⟩
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
    refine ⟨scalarMatter, 0, chargedState, ?_⟩
    intro he
    obtain ⟨K, hK⟩ := tensor_finite_capture chargedState
    have hz := congrFun he K
    change partialNumber K 0 = partialNumber K chargedState at hz
    rw [map_zero, hK K (fun _ hi => hi), number_chargedState] at hz
    exact chargedState_ne_zero hz.symm

def audit : Contract.Registration (@tensor_finite_capture.{0})
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostChargeTensor.captureUnit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostChargeTensor.Capture.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x L => partialNumber L x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (joint scalarMatter)
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostChargeTensor
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Capture

private theorem tensor_c_degree :
    (number : jointEnd scalarMatter) * C 1 - C 1 * number = C 1 := by
  apply TensorProduct.ext'
  intro m v
  simp only [number, C, liftGhost, LinearMap.sub_apply, Module.End.mul_apply,
    TensorProduct.map_tmul, LinearMap.id_apply]
  rw [← TensorProduct.tmul_sub]
  exact congrArg (fun w : Fock => m ⊗ₜ[ℂ] w)
    (LinearMap.congr_fun
      (_root_.D5.S3.Quantum.Fermionic.BcGhostCharge.ghost_number_relations.2.2 1) v)

private theorem tensor_c_ne_zero : (C 1 : jointEnd scalarMatter) ≠ 0 := by
  intro h
  have hv := LinearMap.congr_fun h vacuumState
  have hz := congrArg (TensorProduct.lid ℂ Fock) hv
  simp only [C, liftGhost, vacuumState, TensorProduct.map_tmul, LinearMap.id_apply,
    _root_.D5.S3.Quantum.Fermionic.BcGhostFock.ghost_vacuum.2.2.1,
    LinearMap.zero_apply, TensorProduct.lid_tmul, one_smul, map_zero] at hz
  exact (by simp [ket] : ket {1} ≠ 0) hz

namespace SignedModes

abbrev arena : Arena where
  signature := _root_.Reg.D5.S3.Quantum.Fermionic.BcGhostChargeTensor.signature
  Law R := ∀ (P : Matter) (E : jointEnd P) (ε : ℂ), ε * ε = 1 →
    (∀ m : ℤ, E * B m = ε • (B m * E)) →
    (∀ m : ℤ, E * C m = ε • (C m * E)) → R.readout () P E = 0

def actual : Realization signature := realize signature
  (fun _ _ E => number * E - E * number) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h scalarMatter 0 1 (by simp) (by intro m; simp) (by intro m; simp)
  exact identity_ne_zero hz

def family : Registration arena (type_of% @number_commutes_of_signed_modes.{0}) where
  actual := actual
  bridge := by
    constructor
    · intro h P E ε hε hb hc
      exact h E ε hε hb hc
    · intro h M iM mM E ε hε hb hc
      exact h ⟨M, iM, mM⟩ E ε hε hb hc
  variation := ⟨fun P E ε hε hb hc => number_commutes_of_signed_modes E ε hε hb hc,
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
    refine ⟨scalarMatter, 0, C 1, ?_⟩
    change number * 0 - 0 * number ≠ number * C 1 - C 1 * number
    rw [tensor_c_degree]
    simpa using Ne.symm tensor_c_ne_zero

def audit : Contract.Registration (@number_commutes_of_signed_modes.{0})
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostChargeTensor.signedModesUnit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostChargeTensor.SignedModes.family
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
    (fun _ _ E => number * E - E * number) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (jointEnd scalarMatter)
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostChargeTensor
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SignedModes

end Reg.D5.S3.Quantum.Fermionic.BcGhostChargeTensor
