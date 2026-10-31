import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Observer.LinearMemory.MixedCycleRecovery

/-! A dependent-family audit of the complete mixed-cycle recovery statement. -/

noncomputable section

namespace Reg.D5.S3.Observer.LinearMemory.MixedCycleRecovery

open LeanInformationAudit
open _root_.D5.S3.Observer.LinearMemory.MixedCycleRecovery
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

/-- All source carriers, structures, dimensions, bases and bound choices. -/
structure Parameters where
  k : ℕ
  V : Type u
  normed : NormedAddCommGroup V
  inner : letI := normed; InnerProductSpace ℝ V
  finite : letI := normed; letI := inner; FiniteDimensional ℝ V
  basis : letI := normed; letI := inner; OrthonormalBasis (Axis k) ℝ V
  r : ℕ
  bound : r ≤ k

attribute [instance] Parameters.normed Parameters.inner Parameters.finite

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := p.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := generated p.basis p.r p.bound → visible p.basis
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p x => observations p.basis p.r p.bound x) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- One selected readout occurrence varies, with the entire original telescope retained. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {k : ℕ} {V : Type u} [n : NormedAddCommGroup V]
    [i : InnerProductSpace ℝ V] [f : FiniteDimensional ℝ V]
    (b : OrthonormalBasis (Axis k) ℝ V) (r : ℕ) (hr : r ≤ k),
    mixedCycle b 0 (Nat.zero_le k) = 1 ∧
        rowSpace b r hr = window b r ∧
        Module.finrank ℝ (rowSpace b r hr) = 3 + r ∧
        Module.finrank ℝ (LinearMap.id : visible b →ₗ[ℝ] visible b).range = 3 ∧
        (∀ x : visible b, observations b r hr x ⟨1, (generated b r hr).one_mem⟩ = x) ∧
        Module.finrank ℝ (visible b).orthogonalProjectionOnto.toLinearMap.range = 3 ∧
        LinearlyRecoverable b r hr (visible b).orthogonalProjectionOnto.toLinearMap ∧
        (∀ (h : r < k) (x : V) (a : ℝ),
          observations b r hr (x + a • b (.inr ⟨r, h⟩)) =
            R.readout () ⟨k, V, n, i, f, b, r, hr⟩ x ∧
          (a ≠ 0 → x + a • b (.inr ⟨r, h⟩) ≠ x)) ∧
        (LinearlyRecoverable b r hr (LinearMap.id : V →ₗ[ℝ] V) ↔ r = k) ∧
        Module.finrank ℝ (window b r).orthogonalProjectionOnto.toLinearMap.range = 3 + r ∧
        LinearlyRecoverable b r hr (window b r).orthogonalProjectionOnto.toLinearMap ∧
        ((∃ recover : (generated b r hr → visible b) → V,
          (id : V → V) = recover ∘ (observations b r hr)) ↔ r = k)

private def testBasis : OrthonormalBasis (Axis 1) ℝ
    (EuclideanSpace ℝ (ULift.{u} (Axis 1))) :=
  (EuclideanSpace.basisFun (ULift.{u} (Axis 1)) ℝ).reindex Equiv.ulift

private def testParameters : Parameters.{u} :=
  ⟨1, EuclideanSpace ℝ (ULift.{u} (Axis 1)), inferInstance, inferInstance,
    inferInstance, testBasis, 0, Nat.zero_le _⟩

private theorem test_visible : testBasis.{u} (.inl 0) ∈ visible testBasis :=
  Submodule.subset_span ⟨.inl 0, trivial, rfl⟩

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hs := (h testBasis 0 (Nat.zero_le 1)).2.2.2.2.2.2.2.1
    (by decide : 0 < 1) (testBasis (.inl 0)) 0
  have hh := congrFun hs.1 ⟨1, (generated testBasis 0 (Nat.zero_le 1)).one_mem⟩
  have hid := (mixed_cycle_recovery testBasis 0 (Nat.zero_le 1)).2.2.2.2.1
    ⟨testBasis (.inl 0), test_visible⟩
  have hobs : observations testBasis 0 (Nat.zero_le 1) (testBasis (.inl 0))
      ⟨1, (generated testBasis 0 (Nat.zero_le 1)).one_mem⟩ = 0 := by
    change observations testBasis 0 (Nat.zero_le 1)
      (testBasis (.inl 0) + 0 • testBasis (.inr ⟨0, by decide⟩)) _ = 0 at hh
    simpa only [zero_smul, add_zero] using hh
  have hz : (⟨testBasis (.inl 0), test_visible⟩ : visible testBasis) = 0 :=
    hid.symm.trans hobs
  exact testBasis.toBasis.ne_zero (.inl 0) (congrArg Subtype.val hz)

def source_registration : Registration arena.{u} (type_of% (@mixed_cycle_recovery.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@mixed_cycle_recovery, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro role
    refine ⟨testParameters, 0, testBasis (.inl 0), ?_⟩
    intro he
    have hh := congrFun he ⟨1, (generated testBasis 0 (Nat.zero_le 1)).one_mem⟩
    have hid := (mixed_cycle_recovery testBasis 0 (Nat.zero_le 1)).2.2.2.2.1
      ⟨testBasis (.inl 0), test_visible⟩
    change observations testBasis 0 (Nat.zero_le 1) 0 _ =
      observations testBasis 0 (Nat.zero_le 1) (testBasis (.inl 0)) _ at hh
    have hzero : observations testBasis 0 (Nat.zero_le 1) 0
        ⟨1, (generated testBasis 0 (Nat.zero_le 1)).one_mem⟩ = 0 := by
      rw [map_zero]
      rfl
    have hz : (0 : visible testBasis) = ⟨testBasis (.inl 0), test_visible⟩ :=
      hzero.symm.trans (hh.trans hid)
    exact testBasis.toBasis.ne_zero (.inl 0) (congrArg Subtype.val hz.symm)

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@mixed_cycle_recovery.{u})
    (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S3.Observer.LinearMemory.MixedCycleRecovery.mixed_cycle_recovery.information_unit
  realizationName := `Reg.D5.S3.Observer.LinearMemory.MixedCycleRecovery.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ p x => observations p.basis p.r p.bound x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.LinearMemory.MixedCycleRecovery
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5, 6, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg",
        "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Reg.D5.S3.Observer.LinearMemory.MixedCycleRecovery
