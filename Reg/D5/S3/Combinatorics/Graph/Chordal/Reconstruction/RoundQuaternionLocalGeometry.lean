import D5.S3.Combinatorics.Graph.Chordal.Reconstruction.RoundQuaternionLocalGeometry
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! The exact defect is the observation entering the trace and score comparison. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Real
open scoped Quaternion InnerProductSpace

noncomputable section

namespace Reg.D5.S3.Combinatorics.Graph.Chordal.Reconstruction.RoundQuaternionLocalGeometry

open _root_.RoundQuaternionLocalSharpness _root_.RoundQuaternionK4Bounds
open _root_.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel (unitI inner_eq_components)

local notation "U" => unitary ℍ[ℝ]

abbrev signature := _root_.Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => Fin 3 → U) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ A => hubMaxDefect A) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law observer := ∀ (A : Fin 3 → U) (p q : ℂ) (η γ : Fin 3 → ℝ),
    (∀ j, (A j : ℍ[ℝ]) = quatPair ⟨-η j, γ j⟩ (transverse p q j)) →
    (∀ j, 0 < γ j) → ‖p‖ ≤ localR → ‖q‖ ≤ localR → etaMax η ≤ localR →
    LocalDefectEstimates A η p q (observer.readout () () A)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let A : Fin 3 → U := fun _ => unitI
  have hA (j : Fin 3) :
      (A j : ℍ[ℝ]) = quatPair ⟨-(0 : ℝ), 1⟩ (transverse 0 0 j) := by
    simp [A, transverse, quatPair, unitI]
  have hbound := law A 0 0 0 (fun _ => 1) (by simpa using hA)
    (by intro j; norm_num) (by norm_num [localR]) (by norm_num [localR])
    (by norm_num [etaMax, localR])
  have h := hbound.exact_defect
  change (-1 : ℝ) = π / 2 + arcsin (localDefectParam A 0) at h
  have hzero : 0 ≤ localDefectParam A 0 := by
    unfold localDefectParam
    exact le_max_of_le_left (by simp)
  have hs := arcsin_le_arcsin hzero
  rw [arcsin_zero] at hs
  linarith [pi_pos]

private theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), fun _ => 1, fun _ => unitI, ?_⟩
  change hubMaxDefect (fun _ => 1) ≠ hubMaxDefect (fun _ => unitI)
  have hzero : roundDist (1 : U) 1 = 0 := by simp [roundDist, real_inner_self_eq_norm_sq]
  have hfirst : hubMaxDefect (fun _ => 1) = 0 := by simp [hubMaxDefect, hzero]
  have hquarter : roundDist (1 : U) unitI = π / 2 := by
    simp [roundDist, inner_eq_components, unitI]
  have hlower : roundDist (1 : U) unitI ≤ hubMaxDefect (fun _ => unitI) :=
    (le_max_left _ _).trans (le_max_left _ _)
  rw [hfirst, hquarter] at *
  exact ne_of_lt (pi_div_two_pos.trans_le hlower)

def family : Registration arena (type_of% @local_defect_estimates) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@local_defect_estimates, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@local_defect_estimates) (Realization signature) Unit Unit where
  unitName := `RoundQuaternionLocalSharpness.local_defect_estimates.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.Chordal.Reconstruction.RoundQuaternionLocalGeometry.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.Reconstruction.RoundQuaternionLocalGeometry
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Structural

private def arena : Arena where
  signature := signature
  Law observer := LocalGeometryLaws (observer.readout () ())

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := (law.hub_faces (fun _ => 1)).1.2.2 0 1 2 (by decide) (by decide) (by decide)
  change roundDist _ _ ≤ -1 at h
  exact (by norm_num : ¬ 0 ≤ (-1 : ℝ)) ((arccos_nonneg _).trans h)

def family : Registration arena (type_of% @local_geometry) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@local_geometry, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@local_geometry) (Realization signature) Unit Unit where
  unitName := `RoundQuaternionLocalSharpness.local_geometry.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.Chordal.Reconstruction.RoundQuaternionLocalGeometry.Structural.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.Reconstruction.RoundQuaternionLocalGeometry
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Structural

end Reg.D5.S3.Combinatorics.Graph.Chordal.Reconstruction.RoundQuaternionLocalGeometry
