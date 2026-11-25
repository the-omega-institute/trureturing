import D5.S3.Weil.Mertens.RobinFiniteMesh
import Reg.D5.S3.Weil.Mertens.RobinCenteredChord

/-! The finite mesh estimates observe the true mass as a function of the
Chebyshev kernel while holding the sampled chords fixed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Real Set LeanInformationAudit
open Finset (range)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (psiErrorKernel)
open _root_.D5.S3.Weil.Mertens.RobinFiniteMesh
open _root_.D5.S3.Weil.Mertens.WeightedTailWindowMass (weightedNegativeMass)
open _root_.Reg.D5.S3.Weil.Mertens.RobinCenteredChord (massSignature massEvidence)

namespace Reg.D5.S3.Weil.Mertens.RobinFiniteMesh

private def observe (f : (ℝ → ℝ) → ℝ → ℝ → ℝ) : Realization massSignature :=
  realize massSignature (fun _ _ => f) (fun e => nomatch e)

def endpointArena : Arena where
  signature := massSignature
  Law V := ∀ {A B h : ℝ} {N : ℕ} {x : ℕ → ℝ},
    exp 1 ≤ A → B ≤ 2 * A → x 0 = A → x N = B →
    StrictMonoOn x (Iic N) → (∀ i < N, x (i + 1) - x i ≤ h) →
    |V.readout () () psiErrorKernel A B -
        (∑ i ∈ range N, chordMass (x i) (x (i + 1)))| ≤
      (3 * h ^ 2 / (4 * A ^ 2 * sqrt A)) * (Chebyshev.psi B - Chebyshev.psi A + B - A)

def uniformArena : Arena where
  signature := massSignature
  Law V := ∀ {A B h η : ℝ} {N : ℕ} {x : ℕ → ℝ},
    exp 1 ≤ A → B ≤ 2 * A → x 0 = A → x N = B →
    StrictMonoOn x (Iic N) → (∀ i < N, x (i + 1) - x i ≤ h) →
    h ≤ η * A ^ (3 / 4 : ℝ) →
    |V.readout () () psiErrorKernel A B -
        (∑ i ∈ range N, chordMass (x i) (x (i + 1)))| ≤ 9 * η ^ 2

private def shifted : Realization massSignature :=
  observe (fun k a b => weightedNegativeMass k a b + 1)

private lemma empty_mono : StrictMonoOn (fun _ : ℕ => (3 : ℝ)) (Iic 0) := by
  intro i hi j hj hij
  exact (Nat.not_lt_zero i (hij.trans_le (mem_Iic.mp hj))).elim

private lemma empty_step (i : ℕ) (hi : i < 0) : (3 : ℝ) - 3 ≤ 0 :=
  (Nat.not_lt_zero i hi).elim

private lemma endpoint_rejected : ¬ endpointArena.Law shifted := by
  intro law
  have h := law (A := 3) (B := 3) (h := 0) (N := 0) (x := fun _ => 3)
    exp_one_lt_three.le (by norm_num) rfl rfl empty_mono empty_step
  change |weightedNegativeMass psiErrorKernel 3 3 + 1 -
    (∑ _i ∈ range 0, chordMass 3 3)| ≤ _ at h
  norm_num [weightedNegativeMass] at h

private lemma uniform_rejected : ¬ uniformArena.Law shifted := by
  intro law
  have h := law (A := 3) (B := 3) (h := 0) (η := 0) (N := 0) (x := fun _ => 3)
    exp_one_lt_three.le (by norm_num) rfl rfl empty_mono empty_step (by simp)
  change |weightedNegativeMass psiErrorKernel 3 3 + 1 -
    (∑ _i ∈ range 0, chordMass 3 3)| ≤ _ at h
  norm_num [weightedNegativeMass] at h

def endpointEvidence : Registration endpointArena (type_of% @abs_mass_sub_mesh_le) where
  actual := observe weightedNegativeMass
  bridge := Iff.rfl
  variation := ⟨@abs_mass_sub_mesh_le, shifted, endpoint_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    endpointArena.Law (observe weightedNegativeMass) shifted endpoint_rejected
  dependence := massEvidence.dependence

def uniformEvidence : Registration uniformArena (type_of% @abs_mass_sub_mesh_le_nine_mul_sq) where
  actual := observe weightedNegativeMass
  bridge := Iff.rfl
  variation := ⟨@abs_mass_sub_mesh_le_nine_mul_sq, shifted, uniform_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    uniformArena.Law (observe weightedNegativeMass) shifted uniform_rejected
  dependence := massEvidence.dependence

def endpointAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@abs_mass_sub_mesh_le) (Realization massSignature) Unit Unit where
  unitName := .str ``abs_mass_sub_mesh_le "__information_unit"
  realizationName := ``endpointEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨endpointArena⟩
  objectArena := .source ⟨endpointArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source endpointArena ⟨endpointEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize massSignature (fun _ _ => weightedNegativeMass) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.RobinFiniteMesh
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "fn", "arg", "arg", "fn", "arg", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def uniformAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@abs_mass_sub_mesh_le_nine_mul_sq) (Realization massSignature) Unit Unit where
  unitName := .str ``abs_mass_sub_mesh_le_nine_mul_sq "__information_unit"
  realizationName := ``uniformEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨uniformArena⟩
  objectArena := .source ⟨uniformArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source uniformArena ⟨uniformEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize massSignature (fun _ _ => weightedNegativeMass) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.RobinFiniteMesh
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "arg", "arg", "fn", "arg", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.RobinFiniteMesh
