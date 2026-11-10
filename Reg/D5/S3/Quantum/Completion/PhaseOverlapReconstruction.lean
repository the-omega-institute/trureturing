import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Completion.PhaseOverlapReconstruction
import Reg.Support.SingleDependentReadout

/-! Source-bound audits for the phase-overlap reconstruction and its Born bound. -/

namespace Reg.D5.S3.Quantum.Completion.PhaseOverlapReconstruction

open _root_.D5.S3.Quantum.Completion.PhaseOverlapReconstruction
open _root_.D5.S3.QuadraticForms.ThreeWayPositiveKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

structure HilbertParam where
  Carrier : Type u
  normed : NormedAddCommGroup Carrier
  inner : InnerProductSpace ℂ Carrier

private instance uliftInnerProductSpace : InnerProductSpace ℂ (ULift.{u} ℂ) where
  inner x y := inner ℂ x.down y.down
  norm_sq_eq_re_inner := by
    intro x
    rw [inner_self_eq_norm_sq]
    simp
  conj_inner_symm := by
    intro x y
    simp [inner_conj_symm]
    ring
  add_left := by
    intro x y z
    simp [inner_add_left]
    ring
  smul_left := by
    intro a x y
    simp [inner_smul_left]
    ring

abbrev overlapSignature : Signature where
  Params := HilbertParam.{u}
  State p := (p.Carrier × p.Carrier) × Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def overlapActual : Realization overlapSignature.{u} :=
  realize overlapSignature (fun _ p q =>
    letI : NormedAddCommGroup p.Carrier := p.normed
    letI : InnerProductSpace ℂ p.Carrier := p.inner
    if q.2 then phaseOverlap q.1.1 q.1.2 = inner ℂ q.1.1 q.1.2 else False)
    (fun e => nomatch e)

def overlapRejected : Realization overlapSignature.{u} :=
  realize overlapSignature (fun _ _ _ => False) (fun e => nomatch e)

abbrev overlapArena : Arena where
  signature := overlapSignature.{u}
  Law R := ∀ (p : HilbertParam.{u}) (x y : p.Carrier),
    letI : NormedAddCommGroup p.Carrier := p.normed
    letI : InnerProductSpace ℂ p.Carrier := p.inner
    ‖x‖ = 1 → ‖y‖ = 1 → R.readout () p ((x, y), true)

private theorem overlapActualLaw : overlapArena.{u}.Law overlapActual := by
  intro p x y hx hy
  letI : NormedAddCommGroup p.Carrier := p.normed
  letI : InnerProductSpace ℂ p.Carrier := p.inner
  simpa [overlapActual, realize] using phaseOverlap_eq_inner x y hx hy

private theorem overlapRejectedLaw : ¬ overlapArena.{u}.Law overlapRejected := by
  intro h
  let p : HilbertParam :=
    { Carrier := ULift.{u} ℂ, normed := inferInstance, inner := inferInstance }
  have hunit : ‖(ULift.up (1 : ℂ) : ULift.{u} ℂ)‖ = 1 := by
    change ‖(1 : ℂ)‖ = 1
    norm_num
  have hb := h p (ULift.up (1 : ℂ)) (ULift.up 1) hunit hunit
  exact hb

private theorem overlapBridge :
    (type_of% @phaseOverlap_eq_inner.{u}) ↔ overlapArena.{u}.Law overlapActual := by
  constructor
  · intro h p x y hx hy
    letI : NormedAddCommGroup p.Carrier := p.normed
    letI : InnerProductSpace ℂ p.Carrier := p.inner
    simpa [overlapActual, realize] using h x y hx hy
  · intro h H instN instI x y hx hy
    let p : HilbertParam := { Carrier := H, normed := instN, inner := instI }
    have hp := h p x y hx hy
    simpa [overlapActual, realize] using hp

private theorem overlapDependence :
    ObservationalDependence overlapSignature.{u} overlapActual := by
  intro i
  let p : HilbertParam :=
    { Carrier := ULift.{u} ℂ, normed := inferInstance, inner := inferInstance }
  have hunit : ‖(ULift.up (1 : ℂ) : ULift.{u} ℂ)‖ = 1 := by
    change ‖(1 : ℂ)‖ = 1
    norm_num
  have ht : overlapActual.readout () p
      (((ULift.up (1 : ℂ)), ULift.up 1), true) := by
    simpa [overlapActual, realize, inner_self_eq_norm_sq, hunit] using
      phaseOverlap_eq_inner (ULift.up (1 : ℂ)) (ULift.up 1) hunit hunit
  have hf : ¬ overlapActual.readout () p
      (((ULift.up (1 : ℂ)), ULift.up 1), false) := by
    simp [overlapActual, realize]
  refine ⟨p, (((ULift.up (1 : ℂ)), ULift.up 1), true),
    (((ULift.up (1 : ℂ)), ULift.up 1), false), ?_⟩
  intro he
  exact hf (Eq.mp he ht)

def overlapSource :
    Registration overlapArena.{u} (type_of% @phaseOverlap_eq_inner.{u}) where
  actual := overlapActual
  bridge := overlapBridge
  variation := ⟨overlapActualLaw, overlapRejected, overlapRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨overlapRejected, ?_, ?_, overlapRejectedLaw⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := overlapDependence

def overlapRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@phaseOverlap_eq_inner.{u}) (Realization overlapSignature.{u}) Unit Unit := {
  unitName := `D5.S3.Quantum.Completion.PhaseOverlapReconstruction.phaseOverlap_eq_inner.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Completion.PhaseOverlapReconstruction.overlapSource
  realizationSource := none
  generated := false
  arena := .source ⟨overlapArena⟩
  objectArena := .source ⟨overlapArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source overlapArena.{u} ⟨overlapSource.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize overlapSignature (fun _ p q =>
    letI : NormedAddCommGroup p.Carrier := p.normed
    letI : InnerProductSpace ℂ p.Carrier := p.inner
    if q.2 then q.1.1 = q.1.2 else False) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev bornSignature : Signature where
  Params := HilbertParam.{u}
  State p := (p.Carrier × p.Carrier) × Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def bornActual : Realization bornSignature.{u} :=
  realize bornSignature (fun _ p q =>
    letI : NormedAddCommGroup p.Carrier := p.normed
    letI : InnerProductSpace ℂ p.Carrier := p.inner
    if q.2 then Complex.normSq (phaseOverlap q.1.1 q.1.2) ≤ 1 else False)
    (fun e => nomatch e)

def bornRejected : Realization bornSignature.{u} :=
  realize bornSignature (fun _ _ _ => False) (fun e => nomatch e)

abbrev bornArena : Arena where
  signature := bornSignature.{u}
  Law R := ∀ (p : HilbertParam.{u}) (x y : p.Carrier),
    letI : NormedAddCommGroup p.Carrier := p.normed
    letI : InnerProductSpace ℂ p.Carrier := p.inner
    ‖x‖ = 1 → ‖y‖ = 1 → R.readout () p ((x, y), true)

private theorem bornActualLaw : bornArena.{u}.Law bornActual := by
  intro p x y hx hy
  letI : NormedAddCommGroup p.Carrier := p.normed
  letI : InnerProductSpace ℂ p.Carrier := p.inner
  simpa [bornActual, realize] using phaseOverlap_normSq_le_one x y hx hy

private theorem bornRejectedLaw : ¬ bornArena.{u}.Law bornRejected := by
  intro h
  let p : HilbertParam :=
    { Carrier := ULift.{u} ℂ, normed := inferInstance, inner := inferInstance }
  have hunit : ‖(ULift.up (1 : ℂ) : ULift.{u} ℂ)‖ = 1 := by
    change ‖(1 : ℂ)‖ = 1
    norm_num
  have hb := h p (ULift.up (1 : ℂ)) (ULift.up 1) hunit hunit
  exact hb

private theorem bornBridge :
    (type_of% @phaseOverlap_normSq_le_one.{u}) ↔ bornArena.{u}.Law bornActual := by
  constructor
  · intro h p x y hx hy
    letI : NormedAddCommGroup p.Carrier := p.normed
    letI : InnerProductSpace ℂ p.Carrier := p.inner
    simpa [bornActual, realize] using h x y hx hy
  · intro h H instN instI x y hx hy
    let p : HilbertParam := { Carrier := H, normed := instN, inner := instI }
    have hp := h p x y hx hy
    simpa [bornActual, realize] using hp

private theorem bornDependence :
    ObservationalDependence bornSignature.{u} bornActual := by
  intro i
  let p : HilbertParam :=
    { Carrier := ULift.{u} ℂ, normed := inferInstance, inner := inferInstance }
  have hunit : ‖(ULift.up (1 : ℂ) : ULift.{u} ℂ)‖ = 1 := by
    change ‖(1 : ℂ)‖ = 1
    norm_num
  have ht : bornActual.readout () p
      (((ULift.up (1 : ℂ)), ULift.up 1), true) := by
    simpa [bornActual, realize, hunit] using
      phaseOverlap_normSq_le_one (ULift.up (1 : ℂ)) (ULift.up 1) hunit hunit
  have hf : ¬ bornActual.readout () p
      (((ULift.up (1 : ℂ)), ULift.up 1), false) := by
    simp [bornActual, realize]
  refine ⟨p, (((ULift.up (1 : ℂ)), ULift.up 1), true),
    (((ULift.up (1 : ℂ)), ULift.up 1), false), ?_⟩
  intro he
  exact hf (Eq.mp he ht)

def bornSource :
    Registration bornArena.{u} (type_of% @phaseOverlap_normSq_le_one.{u}) where
  actual := bornActual
  bridge := bornBridge
  variation := ⟨bornActualLaw, bornRejected, bornRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bornRejected, ?_, ?_, bornRejectedLaw⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := bornDependence

def bornRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@phaseOverlap_normSq_le_one.{u}) (Realization bornSignature.{u}) Unit Unit := {
  unitName := `D5.S3.Quantum.Completion.PhaseOverlapReconstruction.phaseOverlap_normSq_le_one.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Completion.PhaseOverlapReconstruction.bornSource
  realizationSource := none
  generated := false
  arena := .source ⟨bornArena⟩
  objectArena := .source ⟨bornArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source bornArena.{u} ⟨bornSource.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize bornSignature (fun _ p q =>
    letI : NormedAddCommGroup p.Carrier := p.normed
    letI : InnerProductSpace ℂ p.Carrier := p.inner
    if q.2 then Complex.normSq (phaseOverlap q.1.1 q.1.2) ≤ 1 else False)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms overlapRegistration
#print axioms bornRegistration

end
end Reg.D5.S3.Quantum.Completion.PhaseOverlapReconstruction
