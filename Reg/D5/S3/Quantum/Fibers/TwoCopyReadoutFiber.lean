import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Fibers.TwoCopyReadoutFiber
import Reg.Support.SingleDependentReadout

/-! Registration for the exact two-copy Bell readout fiber. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Quantum.Fibers.TwoCopyReadoutFiber
open _root_.D5.S3.Quantum.Fibers.TwoCopyReadoutFiber
open _root_.D5.S3.Quantum.Fibers.FiveModeTwoCopyPhase
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev fiberSignature : Signature := {
  Params := Unit
  State _ := Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
}

def actualFiber : Realization fiberSignature := realize fiberSignature
  (fun _ _ qr => twoCopyProbability qr.1 = twoCopyProbability qr.2)
  (fun e => nomatch e)

def rejectedFiber : Realization fiberSignature := realize fiberSignature
  (fun _ _ _ => True)
  (fun e => nomatch e)

abbrev fiberArena : Arena where
  signature := fiberSignature
  Law R := ∀ qr : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) 1,
    R.readout () () qr ↔
      ((qr.1 : ℝ) = (qr.2 : ℝ) ∨ (qr.1 : ℝ) + (qr.2 : ℝ) = 1)

private theorem actual_fiber_law : fiberArena.Law actualFiber := by
  intro qr
  exact two_copy_bell_readout_fiber qr.1 qr.2

private theorem rejected_fiber_law : ¬ fiberArena.Law rejectedFiber := by
  intro h
  have he := h ((⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1),
    (⟨1 / 2, by norm_num⟩ : Set.Icc (0 : ℝ) 1))
  norm_num [rejectedFiber, realize] at he

private theorem dependenceFiber : ObservationalDependence fiberSignature actualFiber := by
  intro i
  let q : Set.Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
  let r : Set.Icc (0 : ℝ) 1 := ⟨1 / 2, by norm_num⟩
  refine ⟨(), (q, q), (q, r), ?_⟩
  change (twoCopyProbability q = twoCopyProbability q) ≠
    (twoCopyProbability q = twoCopyProbability r)
  rw [(two_copy_bell_readout q).2.2.2, (two_copy_bell_readout r).2.2.2]
  norm_num

def familyFiber : Registration fiberArena (type_of% (@two_copy_bell_readout_fiber)) where
  actual := actualFiber
  bridge := by
    constructor
    · intro _
      exact actual_fiber_law
    · intro h
      intro q r
      exact h (q, r)
  variation := ⟨actual_fiber_law, ⟨rejectedFiber, rejected_fiber_law⟩⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity fiberArena.Law actualFiber
    rejectedFiber rejected_fiber_law
  dependence := dependenceFiber

def registrationFiber : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Fibers.TwoCopyReadoutFiber.two_copy_bell_readout_fiber)
    (Realization fiberSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Fibers.TwoCopyReadoutFiber.unit
  realizationName := `Reg.D5.S3.Quantum.Fibers.TwoCopyReadoutFiber.familyFiber
  realizationSource := none
  generated := false
  arena := .source ⟨fiberArena⟩
  objectArena := .source ⟨fiberArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source fiberArena ⟨familyFiber⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize fiberSignature
    (fun _ _ qr => twoCopyProbability qr.1 = twoCopyProbability qr.2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms familyFiber
#print axioms registrationFiber
end Reg.D5.S3.Quantum.Fibers.TwoCopyReadoutFiber
