import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.SpinChains.TokenBlockLocalDefect
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.SpinChains.TokenBlockLocalDefect
open _root_.D5.S3.Quantum.SpinChains.TokenBlockLocalDefect
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators InnerProductSpace
noncomputable section

structure Parameters where
  m : ℕ
  s : ℕ
  r : ℕ
  i : Fin m

abbrev energySignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Parameters
    (fun p => Space p.m p.s p.r) (fun _ => ℝ)

def actualEnergy : Realization energySignature :=
  realize energySignature (fun _ p f => (inner ℂ f (defect p.m p.s p.r p.i f)).re)
    (fun e => nomatch e)

def rejectedEnergy : Realization energySignature :=
  realize energySignature (fun _ _ _ => -1) (fun e => nomatch e)

def coercivityArena : Arena where
  signature := energySignature
  Law R := ∀ (m s r : ℕ) (i : Fin m) (f : Space m s r),
    (s : ℝ) * ‖f-projection m s r i f‖^2 ≤ R.readout () ⟨m,s,r,i⟩ f

theorem rejected_coercivity : ¬ coercivityArena.Law rejectedEnergy := by
  intro h
  have hh := h 1 1 0 0 0
  norm_num [rejectedEnergy, realize] at hh

private theorem energy_dependence : ObservationalDependence energySignature actualEnergy := by
  intro role
  let f : Space 1 2 1 := WithLp.toLp 2 fun S => if (0,0) ∈ S.val then 1 else 0
  let A : Rank 1 2 1 := ⟨{(0,0)}, by simp⟩
  let B : Rank 1 2 1 := ⟨{(0,1)}, by simp⟩
  let π : Equiv.Perm (Fin 2) := Equiv.swap 0 1
  have hab : rankPermutation 1 2 1 0 π A = B := by
    apply Subtype.ext
    simp [rankPermutation, π, A, B]
  have hres : f-projection 1 2 1 0 f ≠ 0 := by
    intro hz
    have he := sub_eq_zero.mp hz
    have hf : f ∈ invariantSubspace 1 2 1 0 := by
      rw [he]
      exact (invariantSubspace 1 2 1 0).starProjection_apply_mem f
    have hh := congrArg (fun g : Space 1 2 1 => g B) (hf π)
    change f ((rankPermutation 1 2 1 0 π).symm B) = f B at hh
    rw [← hab, Equiv.symm_apply_apply] at hh
    norm_num [f, A, B] at hh
  have hpos : 0 < (inner ℂ f (defect 1 2 1 0 f)).re := by
    have hh := result 1 2 1 0 f
    have hn := sq_pos_of_pos (norm_pos_iff.mpr hres)
    norm_num at hh
    linarith
  refine ⟨⟨1,2,1,0⟩, 0, f, ?_⟩
  change (inner ℂ (0 : Space 1 2 1) (defect 1 2 1 0 0)).re ≠
    (inner ℂ f (defect 1 2 1 0 f)).re
  simpa using (ne_of_gt hpos).symm

def coercivitySource : Registration coercivityArena
    (∀ (m s r : ℕ) (i : Fin m) (f : Space m s r),
      (s : ℝ) * ‖f-projection m s r i f‖^2 ≤ (inner ℂ f (defect m s r i f)).re) where
  actual := actualEnergy
  bridge := Iff.rfl
  variation := ⟨result, rejectedEnergy, rejected_coercivity⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    coercivityArena.Law actualEnergy rejectedEnergy rejected_coercivity
  dependence := energy_dependence

def energyArena : Arena where
  signature := energySignature
  Law R := ∀ (m s r : ℕ) (i : Fin m) (f : Space m s r),
    R.readout () ⟨m,s,r,i⟩ f =
      (∑ T : Finset (Outside m s i),
        ((r-T.card : ℕ) : ℝ) * ((s : ℝ)+1-(r-T.card : ℕ)) * ‖split m s r i f T‖^2) -
        ‖lower m s r i f‖^2

theorem rejected_energy : ¬ energyArena.Law rejectedEnergy := by
  intro h
  have hh := h 1 1 0 0 0
  norm_num [rejectedEnergy, realize] at hh

def energySource : Registration energyArena
    (∀ (m s r : ℕ) (i : Fin m) (f : Space m s r),
      (inner ℂ f (defect m s r i f)).re =
      (∑ T : Finset (Outside m s i),
        ((r-T.card : ℕ) : ℝ) * ((s : ℝ)+1-(r-T.card : ℕ)) * ‖split m s r i f T‖^2) -
        ‖lower m s r i f‖^2) where
  actual := actualEnergy
  bridge := Iff.rfl
  variation := ⟨energy, rejectedEnergy, rejected_energy⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    energyArena.Law actualEnergy rejectedEnergy rejected_energy
  dependence := energy_dependence

structure SliceParameters extends Parameters where
  outside : Finset (Outside m s i)

abbrev projectionSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature SliceParameters
    (fun p => Space p.m p.s p.r) (fun p => FiberSpace p.m p.s p.r p.i p.outside)

def actualProjection : Realization projectionSignature :=
  realize projectionSignature
    (fun _ p f => split p.m p.s p.r p.i (projection p.m p.s p.r p.i f) p.outside)
    (fun e => nomatch e)

def rejectedProjection : Realization projectionSignature :=
  realize projectionSignature (fun _ _ _ => WithLp.toLp 2 fun _ => -1)
    (fun e => nomatch e)

def projectionArena : Arena where
  signature := projectionSignature
  Law R := ∀ (m s r : ℕ) (i : Fin m) (f : Space m s r) (T : Finset (Outside m s i)),
    R.readout () ⟨⟨m,s,r,i⟩,T⟩ f =
      WithLp.toLp 2 (fun _ : Fiber m s r i T =>
        (Fintype.card (Fiber m s r i T) : ℂ)⁻¹ * ∑ A, split m s r i f T A)

theorem rejected_projection : ¬ projectionArena.Law rejectedProjection := by
  intro h
  have hh := congrArg (fun v : FiberSpace 1 1 0 0 ∅ => v ⟨∅, by simp⟩)
    (h 1 1 0 0 0 ∅)
  norm_num [rejectedProjection, realize] at hh

theorem projection_dependence : ObservationalDependence projectionSignature actualProjection := by
  intro role
  let f : Space 1 1 0 := WithLp.toLp 2 fun _ => 1
  have hf : f ∈ invariantSubspace 1 1 0 0 := by
    intro π
    ext S
    rfl
  have hp : projection 1 1 0 0 f = f :=
    (invariantSubspace 1 1 0 0).starProjection_eq_self_iff.mpr hf
  refine ⟨⟨⟨1,1,0,0⟩,∅⟩, 0, f, ?_⟩
  intro he
  have hh := congrArg (fun v : FiberSpace 1 1 0 0 ∅ => v ⟨∅, by simp⟩) he
  change split 1 1 0 0 (projection 1 1 0 0 0) ∅ ⟨∅, by simp⟩ =
    split 1 1 0 0 (projection 1 1 0 0 f) ∅ ⟨∅, by simp⟩ at hh
  rw [map_zero, map_zero, hp] at hh
  change (0 : ℂ) = 1 at hh
  exact zero_ne_one hh

def projectionSource : Registration projectionArena
    (∀ (m s r : ℕ) (i : Fin m) (f : Space m s r) (T : Finset (Outside m s i)),
      split m s r i (projection m s r i f) T =
        WithLp.toLp 2 (fun _ : Fiber m s r i T =>
          (Fintype.card (Fiber m s r i T) : ℂ)⁻¹ * ∑ A, split m s r i f T A)) where
  actual := actualProjection
  bridge := Iff.rfl
  variation := ⟨projection_counting_slices, rejectedProjection, rejected_projection⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    projectionArena.Law actualProjection rejectedProjection rejected_projection
  dependence := projection_dependence

def coercivityRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.SpinChains.TokenBlockLocalDefect.result)
      (Realization energySignature) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.TokenBlockLocalDefect.coercivityUnit
  realizationName := `Reg.D5.S3.Quantum.SpinChains.TokenBlockLocalDefect.coercivitySource
  realizationSource := none
  generated := false
  arena := .source ⟨coercivityArena⟩
  objectArena := .source ⟨coercivityArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source coercivityArena ⟨coercivitySource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize energySignature (fun _ p f => (inner ℂ f (defect p.m p.s p.r p.i f)).re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.TokenBlockLocalDefect
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def energyRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.SpinChains.TokenBlockLocalDefect.energy)
      (Realization energySignature) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.TokenBlockLocalDefect.energyUnit
  realizationName := `Reg.D5.S3.Quantum.SpinChains.TokenBlockLocalDefect.energySource
  realizationSource := none
  generated := false
  arena := .source ⟨energyArena⟩
  objectArena := .source ⟨energyArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source energyArena ⟨energySource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize energySignature (fun _ p f => (inner ℂ f (defect p.m p.s p.r p.i f)).re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.TokenBlockLocalDefect
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def projectionRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.SpinChains.TokenBlockLocalDefect.projection_counting_slices)
      (Realization projectionSignature) Type Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.TokenBlockLocalDefect.projectionUnit
  realizationName := `Reg.D5.S3.Quantum.SpinChains.TokenBlockLocalDefect.projectionSource
  realizationSource := none
  generated := false
  arena := .source ⟨projectionArena⟩
  objectArena := .source ⟨projectionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source projectionArena ⟨projectionSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize projectionSignature (fun _ p f => split p.m p.s p.r p.i (projection p.m p.s p.r p.i f) p.outside) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.TokenBlockLocalDefect
    definition := none
    coordinates := #[0, 1, 2, 3, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.SpinChains.TokenBlockLocalDefect
