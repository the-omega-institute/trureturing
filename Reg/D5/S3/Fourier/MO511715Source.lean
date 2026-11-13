import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.MO511715Source
import Reg.Support.SingleDependentReadout

/-! Full-source audits of the time restriction, finite support and lattice-block bounds. -/

set_option autoImplicit false

noncomputable section
open _root_.D5.S3.Fourier.MO511715Source
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Fourier.MO511715Source

namespace Time

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ h => Real.exp (-1) * h ^ 3) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => timeIntegral 1 0 0 0 + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (L A B h : ℝ), 0 ≤ L → 0 ≤ A → 0 ≤ B →
    0 < h → h ≤ 1 / 2 → (L + 3 * A + 3 * B) * h ≤ 1 →
      R.readout () () h ≤ timeIntegral 1 L A B

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 0 0 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  change timeIntegral 1 0 0 0 + 1 ≤ timeIntegral 1 0 0 0 at hh
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1 / 4, 1 / 2, ?_⟩
  dsimp [actual, realize]
  norm_num

def family : Registration arena (type_of% @time_integral_ge) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨time_integral_ge, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@time_integral_ge) (Realization signature) Unit Unit where
  unitName := `D5.S3.Fourier.MO511715Source.time_integral_ge.information_unit
  realizationName := `Reg.D5.S3.Fourier.MO511715Source.Time.family
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
    owner := `D5.S3.Fourier.MO511715Source
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Time

namespace Kernel

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ N => kernelConstant / (N : ℝ) ^ 10) (fun e => nomatch e)

def ones : Lattice := fun _ => 1

def rejected : Realization signature :=
  realize signature (fun _ _ _ => kernel selectedMask 1 firstUnit (ones + ones) ones + 1)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (N : ℕ), 1 ≤ N → ∀ (a b : Lattice),
    a ∈ blockBox N → b ∈ blockBox N →
      R.readout () () N ≤ kernel selectedMask 1 firstUnit (a + b) b

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hm : ones ∈ blockBox 1 := by simp [ones, blockBox]
  have hh := h 1 (by norm_num) ones ones hm hm
  change kernel selectedMask 1 firstUnit (ones + ones) ones + 1 ≤
    kernel selectedMask 1 firstUnit (ones + ones) ones at hh
  linarith

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  have hp : 0 < kernelConstant := by unfold kernelConstant eta; positivity
  dsimp [actual, realize]
  norm_num
  nlinarith

def family : Registration arena (type_of% @kernel_block_lower) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨kernel_block_lower, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@kernel_block_lower) (Realization signature) Unit Unit where
  unitName := `D5.S3.Fourier.MO511715Source.kernel_block_lower.information_unit
  realizationName := `Reg.D5.S3.Fourier.MO511715Source.Kernel.family
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
    owner := `D5.S3.Fourier.MO511715Source
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Kernel

namespace Support

universe u

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => (Lattice × Lattice) → ℝ) (fun _ => Set (Lattice × Lattice))

def actual : Realization signature :=
  realize signature (fun _ _ f => Function.support f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => Set.univ) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {F : Type u} [NormedAddCommGroup F] (ζ : Space → F),
    HasCompactSupport ζ → ∀ (ε : ℝ), 0 < ε →
      (R.readout () () (fun m : Lattice × Lattice =>
        cutoffWeight ζ ε m.1 m.2)).Finite

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h (fun _ : Space => (0 : PUnit.{u + 1}))
    (by simp [HasCompactSupport])
    1 (by norm_num)
  exact Set.infinite_univ hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  simp only [actual, realize]
  intro he
  have hm : (0, 0) ∈ Function.support (fun _ : Lattice × Lattice => (1 : ℝ)) := by
    simp [Function.mem_support]
  rw [← he] at hm
  exact hm rfl

def family : Registration arena.{u} (type_of% @cutoff_finite_support.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cutoff_finite_support, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@cutoff_finite_support.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Fourier.MO511715Source.cutoff_finite_support.information_unit
  realizationName := `Reg.D5.S3.Fourier.MO511715Source.Support.family
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
    owner := `D5.S3.Fourier.MO511715Source
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Support

namespace Growth

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℝ) (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ J x => decide (blockConstant * (J + 1) ≤ x)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {F : Type} [RCLike F] (ζ : Space → F),
    ContinuousAt ζ 0 → ζ 0 = 1 → HasCompactSupport ζ →
      ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ J : ℕ,
        R.readout () J (phi ζ selectedMask (ρ / (5 * (2 : ℝ) ^ J)) 1 firstUnit) = true

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let f : ContDiffBump (0 : Space) := ⟨1, 2, by norm_num, by norm_num⟩
  obtain ⟨ρ, _, _, hh⟩ := h (f : Space → ℝ) f.continuous.continuousAt
    (f.one_of_mem_closedBall (by simp [f])) f.hasCompactSupport
  exact Bool.noConfusion (hh 0)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, blockConstant, blockConstant - 1, ?_⟩
  simp [actual, realize]

def family : Registration arena (type_of% @phi_dyadic_growth) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by
    intro F inst ζ hc hz hs
    simpa only [actual, realize, decide_eq_true_eq] using phi_dyadic_growth ζ hc hz hs,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@phi_dyadic_growth) (Realization signature) Unit Unit where
  unitName := `D5.S3.Fourier.MO511715Source.phi_dyadic_growth.information_unit
  realizationName := `Reg.D5.S3.Fourier.MO511715Source.Growth.family
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
    owner := `D5.S3.Fourier.MO511715Source
    definition := none
    coordinates := #[7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Growth

end Reg.D5.S3.Fourier.MO511715Source
