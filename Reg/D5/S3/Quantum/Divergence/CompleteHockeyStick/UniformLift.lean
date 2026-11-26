import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Divergence.CompleteHockeyStick.UniformLift

/-! Source-bound norm and amplified lift readouts. -/

set_option autoImplicit false

noncomputable section

open LeanInformationAudit Matrix
open scoped CStarAlgebra ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Divergence.CompleteHockeyStickUniformLift
open _root_.D5.S3.Quantum.Divergence.CanonicalChannelDPI (krausColumn)

universe u v k w

namespace Reg.D5.S3.Quantum.Divergence.CompleteHockeyStick.UniformLift.Reindex

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ x y => x ≠ y) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m : Type u} {n : Type v}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) (X : Matrix m m ℂ),
      R.readout () () ‖Matrix.reindex e e X‖ ‖X‖

private theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  let e : ULift.{u} Unit ≃ ULift.{v} Unit := Equiv.ofUnique _ _
  exact h e 0 (norm_reindex e 0)

private theorem sensitivity : Sensitivity arena.{u, v} actual :=
  _root_.Reg.Support.SingleDependentReadout.sensitivity arena.{u, v}.Law actual rejected rejected_law

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he : (1 : ℝ) = 0 := (congrFun h 0).mp rfl
  exact one_ne_zero he

def family : Registration arena.{u, v} (type_of% @norm_reindex.{u, v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@norm_reindex.{u, v}, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{
    _, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@norm_reindex.{u, v}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.CompleteHockeyStickUniformLift.norm_reindex.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.CompleteHockeyStick.UniformLift.Reindex.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.CompleteHockeyStick.UniformLift
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S3.Quantum.Divergence.CompleteHockeyStick.UniformLift.Reindex

namespace Reg.D5.S3.Quantum.Divergence.CompleteHockeyStick.UniformLift.Lift

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y ∧ y < 1) (fun e => nomatch e)

private theorem singleton_span {A : Type u} [DecidableEq A] [Unique A]
    {B : Type v} [Fintype B] {κ : Type k} (K : κ → Matrix B A ℂ)
    (hK : ∃ p, (K p)ᴴ * K p = 1) :
    Submodule.span ℂ (Set.range fun p : κ × κ => (K p.1)ᴴ * K p.2) = ⊤ := by
  obtain ⟨p, hp⟩ := hK
  apply top_unique
  intro X _
  have hone : (1 : Matrix A A ℂ) ∈ Submodule.span ℂ
      (Set.range fun p : κ × κ => (K p.1)ᴴ * K p.2) :=
    Submodule.subset_span ⟨(p, p), hp⟩
  have hX : X = X default default • (1 : Matrix A A ℂ) := by
    ext i j
    rw [Subsingleton.elim i default, Subsingleton.elim j default]
    simp
  rw [hX]
  exact Submodule.smul_mem _ _ hone

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {A : Type u} {B : Type v} {κ : Type k}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix B A ℂ)
    (_hspan : Submodule.span ℂ (Set.range fun p : κ × κ => (K p.1)ᴴ * K p.2) = ⊤),
    ∃ C : ℝ, R.readout () () 1 C ∧
      ∀ (R' : Type w) [Fintype R'] [DecidableEq R']
        (U : Matrix (R' × A) (R' × A) ℂ), ‖U‖ ≤ 1 →
        ∃ W : Matrix (R' × κ) (R' × κ) ℂ,
          amplifiedComplementCompression (krausColumn K) W = U ∧ ‖W‖ ≤ C

private theorem rejected_law : ¬ arena.{u, v, k, w}.Law rejected := by
  intro h
  let K : ULift.{k} Unit → Matrix (ULift.{v} Unit) (ULift.{u} Unit) ℂ := fun _ _ _ => 1
  have hadjoint (a : ULift.{u} Unit) (b : ULift.{v} Unit) : (K default)ᴴ a b = 1 := by
    change star (1 : ℂ) = 1
    exact star_one ℂ
  have hK : (K default)ᴴ * K default = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    simp [hadjoint, K, Matrix.one_apply, eq_iff_true_of_subsingleton]
  have hspan : Submodule.span ℂ (Set.range fun p : ULift.{k} Unit × ULift.{k} Unit =>
      (K p.1)ᴴ * K p.2) = ⊤ := singleton_span (K := K) ⟨default, hK⟩
  obtain ⟨C, ⟨hC, hlt⟩, _⟩ := h K hspan
  exact (not_lt_of_ge hC) hlt

private theorem sensitivity : Sensitivity arena.{u, v, k, w} actual :=
  _root_.Reg.Support.SingleDependentReadout.sensitivity arena.{u, v, k, w}.Law actual rejected rejected_law

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he : (1 : ℝ) ≤ 0 := (congrFun h 0).mp le_rfl
  exact (not_le.mpr zero_lt_one) he

def family : Registration arena.{u, v, k, w} (type_of% @exists_uniform_complement_lift_of_full_span.{u, v, k, w}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_uniform_complement_lift_of_full_span.{u, v, k, w}, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{
    _, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_uniform_complement_lift_of_full_span.{u, v, k, w}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.CompleteHockeyStickUniformLift.exists_uniform_complement_lift_of_full_span.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.CompleteHockeyStick.UniformLift.Lift.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.CompleteHockeyStick.UniformLift
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S3.Quantum.Divergence.CompleteHockeyStick.UniformLift.Lift
