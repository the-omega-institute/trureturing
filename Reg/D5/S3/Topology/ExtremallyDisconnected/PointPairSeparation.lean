import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.ExtremallyDisconnected.PointPairSeparation

/-!
# Source family for eventual point-pair equality

The full space, topology, separation structures, two sequences and per-clopen
eventual agreement are retained. The readout tests an actual candidate cutoff.
Raw source reconstruction is a separate obligation from the kernel bridge.
-/

namespace Reg.D5.S3.Topology.ExtremallyDisconnected.PointPairSeparation

open Set Filter _root_.Topology
open _root_.D5.S3.Topology.ExtremallyDisconnected.PointPairSeparation
open _root_.D5.S3.ConceptDynamics.InformationEscape

universe u

structure Inputs where
  E : Type u
  top : TopologicalSpace E
  hausdorff : @T2Space E top
  disconnected : @ExtremallyDisconnected E top
  p : ℕ → E
  q : ℕ → E
  agree : ∀ U : Set E, @IsClopen E top U → ∀ᶠ n in atTop, (p n ∈ U ↔ q n ∈ U)

def readout (P : Inputs.{u}) (N : ℕ) : Prop := ∀ n, N ≤ n → P.p n = P.q n

def signature : DependentFamily.Signature where
  Params := Inputs.{u}
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature.{u} :=
  DependentFamily.realize signature (fun _ P N => readout P N) (fun a => nomatch a)

def arena : DependentFamily.Arena where
  signature := signature.{u}
  Law := fun R => ∀ P, ∃ N, R.readout () P N

abbrev sourceScope := type_of% (@eventually_eq_of_eventually_mem_isClopen_iff.{u})

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    letI := P.top
    letI := P.hausdorff
    letI := P.disconnected
    exact eventually_atTop.mp (h P.p P.q P.agree)
  · intro h E top hausdorff disconnected p q hagree
    exact eventually_atTop.mpr (h ⟨E, top, hausdorff, disconnected, p, q, hagree⟩)

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp (@eventually_eq_of_eventually_mem_isClopen_iff.{u})

def sampleInputs : Inputs.{u} where
  E := ULift.{u} Bool
  top := inferInstance
  hausdorff := inferInstance
  disconnected := ⟨fun U _ => isOpen_discrete (closure U)⟩
  p := fun _ => ⟨false⟩
  q := fun n => if n = 0 then ⟨true⟩ else ⟨false⟩
  agree := by
    intro U _
    apply eventually_atTop.mpr
    refine ⟨1, ?_⟩
    intro n hn
    have h : n ≠ 0 := by omega
    simp only [h, ite_false]

def rejected : DependentFamily.Realization signature.{u} :=
  DependentFamily.realize signature (fun _ _ _ => False) (fun a => nomatch a)

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨N, hN⟩ := h sampleInputs.{u}
  exact hN

theorem sample_readout_one : readout sampleInputs.{u} 1 := by
  intro n hn
  have h : n ≠ 0 := by omega
  simp [sampleInputs, h]

theorem sample_readout_zero_false : ¬ readout sampleInputs.{u} 0 := by
  intro h
  have he := h 0 (Nat.zero_le 0)
  simp [sampleInputs] at he

noncomputable def familyRegistration : DependentFamily.Registration arena.{u} sourceScope.{u} where
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
    refine ⟨sampleInputs.{u}, (1 : ℕ), (0 : ℕ), ?_⟩
    intro he
    have h : readout sampleInputs.{u} 1 = readout sampleInputs.{u} 0 := he
    exact sample_readout_zero_false (h ▸ sample_readout_one)

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@eventually_eq_of_eventually_mem_isClopen_iff.{u})
      (DependentFamily.Realization signature.{u}) Type Unit where
  unitName := `D5.S3.Topology.ExtremallyDisconnected.PointPairSeparation.eventually_eq_of_eventually_mem_isClopen_iff.__information_unit
  realizationName := `Reg.D5.S3.Topology.ExtremallyDisconnected.PointPairSeparation.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨familyRegistration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature.{u}
    (fun _ P N => readout P N) (fun a => nomatch a))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Topology.ExtremallyDisconnected.PointPairSeparation
