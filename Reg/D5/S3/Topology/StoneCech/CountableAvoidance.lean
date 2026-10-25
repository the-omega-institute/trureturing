import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.StoneCech.CountableAvoidance

/-! # Exact source family for countable free-ultrafilter avoidance

The sole readout is infinitude of the actual selected subset of ℕ.
The law retains all forbidden ultrafilters and their freeness hypotheses.
-/

noncomputable section

namespace Reg.D5.S3.Topology.StoneCech.CountableAvoidance

open Set Filter
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.Topology.StoneCech.CountableAvoidance

@[reducible] def signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => Set ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ A => A.Infinite) (fun a => nomatch a)

@[reducible] def arena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ (p : ℕ → Ultrafilter ℕ)
    (_hp : ∀ n, (p n : Filter ℕ) ≤ cofinite),
    ∃ A : Set ℕ, R.readout () () A ∧ ∀ n, A ∉ p n

abbrev sourceScope := type_of% (@exists_infinite_notMem)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem actual_positive : arena.Law actual := source_bridge.mp exists_infinite_notMem

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => False) (fun a => nomatch a)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨A, hA, _⟩ := h (fun _ => hyperfilter ℕ) (fun _ => hyperfilter_le_cofinite)
  exact hA

def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := by
    intro i
    refine ⟨(), (univ : Set ℕ), ∅, ?_⟩
    change (univ : Set ℕ).Infinite ≠ (∅ : Set ℕ).Infinite
    intro he
    have hi : (∅ : Set ℕ).Infinite := he ▸ Set.infinite_univ
    obtain ⟨n, hn⟩ := hi.nonempty
    exact hn

def registration :
    LeanInformationAudit.Contract.Registration.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      (@exists_infinite_notMem) (DependentFamily.Realization signature) Unit True where
  unitName := `D5.S3.Topology.StoneCech.CountableAvoidance.exists_infinite_notMem.__information_unit
  realizationName := `Reg.D5.S3.Topology.StoneCech.CountableAvoidance.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (DependentFamily.realize signature (fun _ _ A => A.Infinite)
    (fun a => nomatch a))
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Topology.StoneCech.CountableAvoidance
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

universe v

@[reducible] def reindexSignature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => ℕ → ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def reindexActual : DependentFamily.Realization reindexSignature :=
  DependentFamily.realize reindexSignature (fun _ _ j => StrictMono j) (fun a => nomatch a)

@[reducible] def reindexArena : DependentFamily.Arena where
  signature := reindexSignature
  Law R := ∀ {Y : Type v} (h : Ultrafilter ℕ → Y),
    Function.Injective (h ∘ (pure : ℕ → Ultrafilter ℕ)) →
    Set.InjOn h {p | (p : Filter ℕ) ≤ cofinite} →
    ∃ j : ℕ → ℕ, R.readout () () j ∧ Function.Injective (h ∘ Ultrafilter.map j)

abbrev reindexScope := type_of% (@exists_strictMono_injective_reindex.{v})

theorem reindexBridge : reindexScope.{v} ↔ reindexArena.{v}.Law reindexActual := Iff.rfl

def reindexRejected : DependentFamily.Realization reindexSignature :=
  DependentFamily.realize reindexSignature (fun _ _ _ => False) (fun a => nomatch a)

theorem reindexPositive : reindexArena.{v}.Law reindexActual :=
  reindexBridge.mp (@exists_strictMono_injective_reindex.{v})

theorem reindexNegative : ¬ reindexArena.{v}.Law reindexRejected := by
  intro h
  let f : Ultrafilter ℕ → ULift.{v} (Ultrafilter ℕ) := ULift.up
  have hi : Function.Injective f := fun _ _ he => congrArg ULift.down he
  obtain ⟨j, hj, _⟩ := h f (hi.comp Ultrafilter.pure_injective) hi.injOn
  exact hj

def reindexFamily : DependentFamily.Registration reindexArena.{v} reindexScope.{v} where
  actual := reindexActual
  bridge := reindexBridge
  variation := ⟨reindexPositive, reindexRejected, reindexNegative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨reindexRejected, ?_, rfl, reindexNegative⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := by
    intro i
    refine ⟨(), id, (fun _ => 0), ?_⟩
    change StrictMono (id : ℕ → ℕ) ≠ StrictMono (fun _ : ℕ => 0)
    intro he
    have hm : StrictMono (fun _ : ℕ => 0) := he ▸ strictMono_id
    exact (lt_irrefl (0 : ℕ)) (hm Nat.zero_lt_one)

def reindexRegistration :
    LeanInformationAudit.Contract.Registration.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      (@exists_strictMono_injective_reindex.{v})
      (DependentFamily.Realization reindexSignature) Unit True where
  unitName := `D5.S3.Topology.StoneCech.CountableAvoidance.exists_strictMono_injective_reindex.__information_unit
  realizationName := `Reg.D5.S3.Topology.StoneCech.CountableAvoidance.reindexFamily
  realizationSource := none
  generated := false
  arena := .source ⟨reindexArena.{v}⟩
  objectArena := .source ⟨reindexArena.{v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source reindexArena.{v} ⟨reindexFamily.{v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (DependentFamily.realize reindexSignature (fun _ _ j => StrictMono j)
    (fun a => nomatch a))
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Topology.StoneCech.CountableAvoidance
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

universe a b

structure MapSpaces where
  A : Type a
  B : Type b

@[reducible] def mapSignature : DependentFamily.Signature where
  Params := MapSpaces.{a, b}
  State := fun P => P.A → P.B
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ P => Ultrafilter P.A → Ultrafilter P.B
  Anchor := Empty
  finiteAnchor := inferInstance

def mapActual : DependentFamily.Realization mapSignature.{a, b} :=
  DependentFamily.realize mapSignature (fun _ _ j => Ultrafilter.map j) (fun a => nomatch a)

@[reducible] def mapArena : DependentFamily.Arena where
  signature := mapSignature.{a, b}
  Law R := ∀ (P : MapSpaces.{a, b}) (j : P.A → P.B), Continuous (R.readout () P j)

abbrev mapScope := type_of% (@continuous_map.{a, b})

/-- Exact continuity source law; the intervention and source-selection
parts of its four-slot registration remain unfinished. -/
theorem mapBridge : mapScope.{a, b} ↔ mapArena.{a, b}.Law mapActual.{a, b} := by
  constructor
  · intro h P j
    exact h j
  · intro h A B j
    exact h ⟨A, B⟩ j

end Reg.D5.S3.Topology.StoneCech.CountableAvoidance
