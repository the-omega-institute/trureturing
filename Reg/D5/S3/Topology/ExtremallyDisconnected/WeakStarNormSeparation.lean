import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.ExtremallyDisconnected.WeakStarNormSeparation

/-!
# Source family for uniform strong-dual norm separation

The source family retains both universes, the normed space, all topological
structures, and the continuous injective weak-star map. Its state is a real
candidate gap. Raw source reconstruction remains a separate obligation.
-/

namespace Reg.D5.S3.Topology.ExtremallyDisconnected.WeakStarNormSeparation

open Set Filter _root_.Topology
open _root_.D5.S3.Topology.ExtremallyDisconnected.WeakStarNormSeparation
open _root_.D5.S3.ConceptDynamics.InformationEscape

universe u v

structure Inputs where
  X : Type u
  normed : NormedAddCommGroup X
  scalar : letI := normed; NormedSpace ℝ X
  K : Type v
  top : TopologicalSpace K
  compact : @CompactSpace K top
  hausdorff : @T2Space K top
  disconnected : @ExtremallyDisconnected K top
  h : letI := normed; letI := scalar; K → WeakDual ℝ X
  continuous : letI := normed; letI := scalar; letI := top; Continuous h
  injective : Function.Injective h

attribute [instance] Inputs.normed Inputs.scalar Inputs.top Inputs.compact
  Inputs.hausdorff Inputs.disconnected

def readout (P : Inputs.{u, v}) (c : ℝ) : Prop :=
  0 < c ∧ ∀ p q : P.K, p ≠ q → c ≤ ‖WeakDual.toStrongDual (P.h p - P.h q)‖

def signature : DependentFamily.Signature where
  Params := Inputs.{u, v}
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature.{u, v} :=
  DependentFamily.realize signature (fun _ P c => readout P c) (fun a => nomatch a)

def arena : DependentFamily.Arena where
  signature := signature.{u, v}
  Law := fun R => ∀ P, ∃ c, R.readout () P c

abbrev sourceScope := type_of% (@exists_pos_le_norm_sub.{u, v})

theorem source_bridge : sourceScope.{u, v} ↔ arena.{u, v}.Law actual.{u, v} := by
  constructor
  · intro h P
    letI := P.normed
    letI := P.scalar
    letI := P.top
    letI := P.compact
    letI := P.hausdorff
    letI := P.disconnected
    exact h P.h P.continuous P.injective
  · intro h X normed scalar K top compact hausdorff disconnected f hf hi
    exact h ⟨X, normed, scalar, K, top, compact, hausdorff, disconnected, f, hf, hi⟩

theorem actual_positive : arena.{u, v}.Law actual.{u, v} :=
  source_bridge.mp (@exists_pos_le_norm_sub.{u, v})

def rejected : DependentFamily.Realization signature.{u, v} :=
  DependentFamily.realize signature (fun _ _ _ => False) (fun a => nomatch a)

noncomputable def sampleInputs : Inputs.{u, v} where
  X := ULift.{u} ℝ
  normed := inferInstance
  scalar := inferInstance
  K := ULift.{v} Unit
  top := inferInstance
  compact := inferInstance
  hausdorff := inferInstance
  disconnected := ⟨fun U _ => isOpen_discrete (closure U)⟩
  h := fun _ => 0
  continuous := continuous_const
  injective := fun _ _ _ => Subsingleton.elim _ _

theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  obtain ⟨c, hc⟩ := h sampleInputs.{u, v}
  exact hc

theorem sample_readout_one : readout sampleInputs.{u, v} 1 := by
  refine ⟨by norm_num, ?_⟩
  intro p q hpq
  haveI : Subsingleton sampleInputs.{u, v}.K := by
    change Subsingleton (ULift.{v} Unit)
    infer_instance
  exact (hpq (Subsingleton.elim _ _)).elim

theorem sample_readout_zero_false : ¬ readout sampleInputs.{u, v} 0 := by
  intro h
  exact (lt_irrefl (0 : ℝ)) h.1

noncomputable def familyRegistration :
    DependentFamily.Registration arena.{u, v} sourceScope.{u, v} where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (show j = i from by change Unit at j i; cases j; cases i; rfl)).elim
    · intro a
      change Empty at a
      exact nomatch a
  dependence := by
    intro i
    refine ⟨sampleInputs.{u, v}, (1 : ℝ), (0 : ℝ), ?_⟩
    intro he
    have h : readout sampleInputs.{u, v} 1 = readout sampleInputs.{u, v} 0 := he
    exact sample_readout_zero_false (h ▸ sample_readout_one)

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@exists_pos_le_norm_sub.{u, v})
      (DependentFamily.Realization signature.{u, v}) Type Unit where
  unitName := `D5.S3.Topology.ExtremallyDisconnected.WeakStarNormSeparation.exists_pos_le_norm_sub.__information_unit
  realizationName := `Reg.D5.S3.Topology.ExtremallyDisconnected.WeakStarNormSeparation.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v}⟩
  objectArena := .source ⟨arena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u, v} ⟨familyRegistration.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature.{u, v}
    (fun _ P c => readout P c) (fun a => nomatch a))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Topology.ExtremallyDisconnected.WeakStarNormSeparation
