import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.Separation.SynchronizedClopenSupports
import Mathlib.Topology.Separation.Regular

/-!
# Source family for synchronized ambient supports

The parameter telescope retains the space, topology, compactness,
Hausdorffness, zero-dimensionality, closed domain and actual map with all
its hypotheses. States retain the separating set, source sequence and
ambient support sequence. The readout includes every conclusion clause.
Raw source selection for these separately quantified outputs is unfinished.
-/

namespace Reg.D5.S3.Topology.Separation.SynchronizedClopenSupports

open Set Function
open _root_.D5.S3.Topology.Separation.SynchronizedClopenSupports
open _root_.D5.S3.ConceptDynamics.InformationEscape

universe u

structure SourceInputs where
  X : Type u
  top : TopologicalSpace X
  compact : @CompactSpace X top
  hausdorff : @T2Space X top
  zeroDimensional : @ZeroDimensionalSpace X top
  F : Set X
  closed : @IsClosed X top F
  f : F → X
  continuous : letI := top; Continuous f
  infinite : (range f).Infinite
  disjoint : Disjoint F (range f)

attribute [instance] SourceInputs.top SourceInputs.compact SourceInputs.hausdorff
  SourceInputs.zeroDimensional

def SourceState (p : SourceInputs.{u}) :=
  Set p.X × (ℕ → p.F) × (ℕ → Set p.X)

def certificate (p : SourceInputs.{u}) (w : SourceState p) : Prop :=
  IsClopen w.1 ∧ p.F ⊆ w.1 ∧ range p.f ⊆ w.1ᶜ ∧
    (∀ n, IsClopen (w.2.2 n)) ∧ Pairwise (Disjoint on w.2.2) ∧
    (∀ n, (w.2.1 n).val ∈ w.2.2 n ∧ p.f (w.2.1 n) ∈ w.2.2 n)

def signature : DependentFamily.Signature where
  Params := SourceInputs.{u}
  State := SourceState
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature.{u} :=
  DependentFamily.realize signature.{u} (fun _ p w => certificate p w)
    (fun a => Empty.elim a)

def arena : DependentFamily.Arena where
  signature := signature.{u}
  Law := fun r => ∀ p, ∃ w, r.readout () p w

abbrev sourceScope := type_of% (@exists_synchronized_clopen_supports.{u})

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h p
    letI := p.top
    letI := p.compact
    letI := p.hausdorff
    letI := p.zeroDimensional
    obtain ⟨P, hP, hFP, hrP, a, W, hW, hd, hm⟩ :=
      h p.F p.closed p.f p.continuous p.infinite p.disjoint
    exact ⟨⟨P, a, W⟩, hP, hFP, hrP, hW, hd, hm⟩
  · intro h X top compact hausdorff zeroDimensional F closed f continuous infinite disjoint
    let p : SourceInputs.{u} :=
      ⟨X, top, compact, hausdorff, zeroDimensional, F, closed, f, continuous, infinite, disjoint⟩
    obtain ⟨⟨P, a, W⟩, hP, hFP, hrP, hW, hd, hm⟩ := h p
    exact ⟨P, hP, hFP, hrP, a, W, hW, hd, hm⟩

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp @exists_synchronized_clopen_supports.{u}

private abbrev Cantor := ℕ → ULift.{u} Bool
private abbrev Ambient := Cantor.{u} × Bool
private def domain : Set Ambient.{u} := {x | x.2 = false}
private def swapSide (x : domain.{u}) : Ambient.{u} := (x.val.1, true)

private def signal (n : ℕ) : Cantor.{u} := fun k => ULift.up (decide (k = n))

private theorem signal_injective : Injective signal.{u} := by
  intro n m h
  by_contra hnm
  have hh := congrArg (fun g : Cantor.{u} => (g n).down) h
  simp [signal, hnm] at hh

def cantorInputs : SourceInputs.{u} where
  X := Ambient.{u}
  top := inferInstance
  compact := inferInstance
  hausdorff := inferInstance
  zeroDimensional := inferInstance
  F := domain
  closed := isClosed_singleton.preimage continuous_snd
  f := swapSide
  continuous := (continuous_fst.comp continuous_subtype_val).prodMk continuous_const
  infinite := by
    apply Set.infinite_of_injective_forall_mem (f := fun n => (signal.{u} n, true))
    · intro n m h
      exact signal_injective (congrArg Prod.fst h)
    · intro n
      exact ⟨⟨(signal n, false), rfl⟩, rfl⟩
  disjoint := by
    apply Set.disjoint_left.mpr
    rintro x hx ⟨a, rfl⟩
    exact Bool.noConfusion hx

def rejected : DependentFamily.Realization signature.{u} :=
  DependentFamily.realize signature.{u} (fun _ _ _ => False) (fun a => Empty.elim a)

theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  obtain ⟨w, hw⟩ := h cantorInputs.{u}
  exact hw

private def origin : cantorInputs.{u}.F := ⟨(fun _ => ULift.up false, false), rfl⟩

def emptyState : SourceState cantorInputs.{u} :=
  ⟨∅, fun _ => origin, fun _ => ∅⟩

theorem empty_invalid : ¬ certificate cantorInputs.{u} emptyState.{u} := by
  intro h
  exact h.2.1 origin.property

def familyRegistration : DependentFamily.Registration arena.{u} sourceScope.{u} where
  actual := actual.{u}
  bridge := source_bridge.{u}
  variation := ⟨actual_positive.{u}, rejected.{u}, rejected_law.{u}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected.{u}, ?_, rfl, rejected_law.{u}⟩
      intro j hji
      exact False.elim (hji (@Subsingleton.elim Unit _ j i))
    · intro a
      exact Empty.elim a
  dependence := by
    intro i
    obtain ⟨w, hw⟩ := actual_positive.{u} cantorInputs.{u}
    refine ⟨cantorInputs.{u}, w, emptyState.{u}, ?_⟩
    intro h
    have hcert : certificate cantorInputs.{u} w := hw
    change certificate cantorInputs.{u} w = certificate cantorInputs.{u} emptyState.{u} at h
    rw [h] at hcert
    exact empty_invalid.{u} hcert

/- The enrolled template retains the complete typed family proof. The raw
source reconstruction of the separately quantified P, a and W is not supplied. -/
noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@exists_synchronized_clopen_supports.{u})
      (DependentFamily.Realization signature.{u}) Unit Unit where
  unitName :=
    `D5.S3.Topology.Separation.SynchronizedClopenSupports.exists_synchronized_clopen_supports.__information_unit
  realizationName :=
    `Reg.D5.S3.Topology.Separation.SynchronizedClopenSupports.familyRegistration
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
    (fun _ p w => certificate p w) (fun a => Empty.elim a))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Topology.Separation.SynchronizedClopenSupports
