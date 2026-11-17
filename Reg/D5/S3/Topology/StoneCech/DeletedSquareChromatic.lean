import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.StoneCech.DeletedSquareChromatic

/-! # Source families for the deleted-square chromatic obstruction

The cover family observes independence of the actual proposed cover. The
endpoint family observes the finite bound for the actual graph. Typed source
bridges retain the complete original assertions. Raw source occurrence
selection is separate from these kernel-checked mathematical fields.
-/

open Set Filter Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.Topology.StoneCech.DeletedSquareChromatic

noncomputable section

namespace Reg.D5.S3.Topology.StoneCech.DeletedSquareChromatic

abbrev X := DeletedSquare (Ultrafilter ℕ)

private def forward : X := ⟨(pure 0, pure 1),
  fun h => Nat.zero_ne_one (Ultrafilter.pure_injective h)⟩

private def backward : X := ⟨(pure 1, pure 0),
  fun h => Nat.one_ne_zero (Ultrafilter.pure_injective h)⟩

@[reducible] def coverSignature : DependentFamily.Signature where
  Params := ℕ
  State m := Fin m → Set X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def coverActual : DependentFamily.Realization coverSignature :=
  DependentFamily.realize coverSignature (fun _ _ U =>
    ∀ i x, x ∈ U i → ∀ y, y ∈ U i → ¬ (swapGraph (Ultrafilter ℕ)).Adj x y)
    (fun a => nomatch a)

@[reducible] def coverArena : DependentFamily.Arena where
  signature := coverSignature
  Law R := ∀ (m : ℕ) (U : Fin m → Set X),
    (∀ i, IsOpen (U i)) → (∀ x, ∃ i, x ∈ U i) → R.readout () m U → False

abbrev coverScope := type_of% (@no_finite_open_independent_cover)

theorem coverBridge : coverScope ↔ coverArena.Law coverActual := Iff.rfl

def coverRejected : DependentFamily.Realization coverSignature :=
  DependentFamily.realize coverSignature (fun _ _ _ => True) (fun a => nomatch a)

theorem coverNegative : ¬ coverArena.Law coverRejected := by
  intro h
  exact h 1 (fun _ => univ) (fun _ => isOpen_univ) (fun _ => ⟨0, mem_univ _⟩) trivial

def coverFamily : DependentFamily.Registration coverArena coverScope where
  actual := coverActual
  bridge := coverBridge
  variation := ⟨no_finite_open_independent_cover, coverRejected, coverNegative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨coverRejected, ?_, rfl, coverNegative⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro a
      exact nomatch a
  dependence := by
    intro i
    refine ⟨1, (fun _ => ∅), (fun _ => univ), ?_⟩
    intro heq
    have hempty : coverActual.readout i 1 (fun _ => ∅) := by
      intro _ _ hx
      exact hx.elim
    have huniv : coverActual.readout i 1 (fun _ => univ) := Eq.mp heq hempty
    exact huniv 0 forward (mem_univ _) backward (mem_univ _) ⟨rfl, rfl⟩

def coverRegistration :
    LeanInformationAudit.Contract.Registration.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      (@no_finite_open_independent_cover) (DependentFamily.Realization coverSignature) Unit True where
  unitName := `D5.S3.Topology.StoneCech.DeletedSquareChromatic.no_finite_open_independent_cover.__information_unit
  realizationName := `Reg.D5.S3.Topology.StoneCech.DeletedSquareChromatic.coverFamily
  realizationSource := none
  generated := false
  arena := .source ⟨coverArena⟩
  objectArena := .source ⟨coverArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source coverArena ⟨coverFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (DependentFamily.realize coverSignature (fun _ _ U =>
    ∀ i x, x ∈ U i → ∀ y, y ∈ U i → ¬ (swapGraph (Ultrafilter ℕ)).Adj x y)
    (fun a => nomatch a))
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Topology.StoneCech.DeletedSquareChromatic
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "domain"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

@[reducible] def endpointSignature : DependentFamily.Signature where
  Params := Unit
  State _ := SimpleGraph X
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def endpointActual : DependentFamily.Realization endpointSignature :=
  DependentFamily.realize endpointSignature (fun _ _ G =>
    ∃ N : ℕ, ∀ S : Set X, G.IsClique S → S.Finite ∧ S.ncard ≤ N)
    (fun a => nomatch a)

@[reducible] def endpointArena : DependentFamily.Arena where
  signature := endpointSignature
  Law R := T2Space X ∧
    (∀ G : SimpleGraph X, IsClosed {p : X × X | G.Adj p.1 p.2} → R.readout () () G) ∧
    ¬ FiniteOpenChromaticProperty X

abbrev endpointScope := type_of% (@result)

theorem endpointBridge : endpointScope ↔ endpointArena.Law endpointActual := Iff.rfl

def endpointRejected : DependentFamily.Realization endpointSignature :=
  DependentFamily.realize endpointSignature (fun _ _ _ => False) (fun a => nomatch a)

private theorem bottomClosed : IsClosed {p : X × X | (⊥ : SimpleGraph X).Adj p.1 p.2} := by
  simpa using (isClosed_empty : IsClosed (∅ : Set (X × X)))

theorem endpointNegative : ¬ endpointArena.Law endpointRejected := by
  intro h
  exact h.2.1 ⊥ bottomClosed

private theorem bottomBounded : endpointActual.readout () () (⊥ : SimpleGraph X) := by
  refine ⟨1, fun S hS => ?_⟩
  have hsub : S.Subsingleton := by
    intro x hx y hy
    by_contra hne
    exact hS hx hy hne
  exact ⟨hsub.finite, (Set.ncard_le_one hsub.finite).mpr hsub⟩

private theorem topUnbounded : ¬ endpointActual.readout () () (⊤ : SimpleGraph X) := by
  intro h
  let e : ℕ → X := fun n => ⟨(pure n, pure (n + 1)),
    fun heq => Nat.ne_of_lt (Nat.lt_succ_self n) (Ultrafilter.pure_injective heq)⟩
  have he : Function.Injective e := by
    intro n m hnm
    exact Ultrafilter.pure_injective (congrArg (fun x : X => x.val.1) hnm)
  haveI : Infinite X := Infinite.of_injective e he
  have hclique : (⊤ : SimpleGraph X).IsClique univ := by
    intro x _ y _ hxy
    exact hxy
  obtain ⟨N, hN⟩ := h
  exact Set.infinite_univ (hN univ hclique).1

def endpointFamily : DependentFamily.Registration endpointArena endpointScope where
  actual := endpointActual
  bridge := endpointBridge
  variation := ⟨result, endpointRejected, endpointNegative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨endpointRejected, ?_, rfl, endpointNegative⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro a
      exact nomatch a
  dependence := by
    intro i
    refine ⟨(), ⊥, ⊤, ?_⟩
    intro heq
    exact topUnbounded (Eq.mp heq bottomBounded)

def endpointRegistration :
    LeanInformationAudit.Contract.Registration.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      (@result) (DependentFamily.Realization endpointSignature) Unit True where
  unitName := `D5.S3.Topology.StoneCech.DeletedSquareChromatic.result.__information_unit
  realizationName := `Reg.D5.S3.Topology.StoneCech.DeletedSquareChromatic.endpointFamily
  realizationSource := none
  generated := false
  arena := .source ⟨endpointArena⟩
  objectArena := .source ⟨endpointArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source endpointArena ⟨endpointFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (DependentFamily.realize endpointSignature (fun _ _ G =>
    ∃ N : ℕ, ∀ S : Set X, G.IsClique S → S.Finite ∧ S.ncard ≤ N)
    (fun a => nomatch a))
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Topology.StoneCech.DeletedSquareChromatic
    definition := some {
      owner := `D5.S3.Topology.StoneCech.DeletedSquareChromatic
      name := `D5.S3.Topology.StoneCech.DeletedSquareChromatic.BoundedCliqueProperty
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

universe u

private theorem emptyBound (Y : Type u) :
    ∃ N : ℕ, ∀ S : Set Y, (⊥ : SimpleGraph Y).IsClique S → S.Finite ∧ S.ncard ≤ N := by
  refine ⟨1, fun S hS => ?_⟩
  have hsub : S.Subsingleton := by
    intro x hx y hy
    by_contra hne
    exact hS hx hy hne
  exact ⟨hsub.finite, (Set.ncard_le_one hsub.finite).mpr hsub⟩

private theorem completeUnbounded (Y : Type u) [Infinite Y] :
    ¬ (∃ N : ℕ, ∀ S : Set Y, (⊤ : SimpleGraph Y).IsClique S → S.Finite ∧ S.ncard ≤ N) := by
  rintro ⟨N, hN⟩
  exact Set.infinite_univ (hN univ (fun _ _ _ _ hne => hne)).1

@[reducible] def boundedSignature : DependentFamily.Signature where
  Params := Σ K : Type u, TopologicalSpace K
  State p := SimpleGraph p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def boundedActual : DependentFamily.Realization boundedSignature.{u} :=
  DependentFamily.realize boundedSignature (fun _ p G =>
    ∃ N : ℕ, ∀ S : Set p.1, G.IsClique S → S.Finite ∧ S.ncard ≤ N)
    (fun a => nomatch a)

@[reducible] def boundedArena : DependentFamily.Arena where
  signature := boundedSignature.{u}
  Law R := ∀ (K : Type u) (t : TopologicalSpace K),
    letI := t
    CountablyCompactSpace (ℕ → K) →
      ∀ G : SimpleGraph K, IsClosed {p : K × K | G.Adj p.1 p.2} → R.readout () ⟨K, t⟩ G

abbrev boundedScope := type_of% (@boundedCliqueProperty_of_countablyCompact_power.{u})

theorem boundedBridge : boundedScope.{u} ↔ boundedArena.{u}.Law boundedActual := Iff.rfl

def boundedRejected : DependentFamily.Realization boundedSignature.{u} :=
  DependentFamily.realize boundedSignature (fun _ _ _ => False) (fun a => nomatch a)

theorem boundedNegative : ¬ boundedArena.{u}.Law boundedRejected := by
  intro h
  exact h PUnit inferInstance inferInstance ⊥ (by simp)

def boundedFamily : DependentFamily.Registration boundedArena.{u} boundedScope.{u} where
  actual := boundedActual
  bridge := boundedBridge
  variation := ⟨@boundedCliqueProperty_of_countablyCompact_power.{u}, boundedRejected, boundedNegative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨boundedRejected, ?_, rfl, boundedNegative⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro a
      exact nomatch a
  dependence := by
    intro i
    refine ⟨⟨ULift.{u} ℕ, inferInstance⟩, ⊥, ⊤, ?_⟩
    intro heq
    exact completeUnbounded (ULift.{u} ℕ) (Eq.mp heq (emptyBound _))

private def powerProperty (K : Type u) (t : TopologicalSpace K) : Prop :=
  letI := t
  CountablyCompactSpace (ℕ → DeletedSquare K)

@[reducible] def powerSignature : DependentFamily.Signature where
  Params := Type u
  State K := TopologicalSpace K
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def powerActual : DependentFamily.Realization powerSignature.{u} :=
  DependentFamily.realize powerSignature (fun _ K t => powerProperty K t) (fun a => nomatch a)

@[reducible] def powerArena : DependentFamily.Arena where
  signature := powerSignature.{u}
  Law R := ∀ (K : Type u) (t : TopologicalSpace K),
    letI := t
    CompactSpace K → T2Space K → ExtremallyDisconnected K → R.readout () K t

abbrev powerScope := type_of% (@countablyCompactSpace_deletedSquare_power.{u})

theorem powerBridge : powerScope.{u} ↔ powerArena.{u}.Law powerActual := Iff.rfl

def powerRejected : DependentFamily.Realization powerSignature.{u} :=
  DependentFamily.realize powerSignature (fun _ _ _ => False) (fun a => nomatch a)

theorem powerNegative : ¬ powerArena.{u}.Law powerRejected := by
  intro h
  exact h PUnit inferInstance inferInstance inferInstance inferInstance

private theorem powerPositiveFiber : powerProperty (ULift.{u} ℕ) ⊤ := by
  letI : TopologicalSpace (ULift.{u} ℕ) := ⊤
  letI : IndiscreteTopology (DeletedSquare (ULift.{u} ℕ)) :=
    inferInstanceAs (IndiscreteTopology {p : ULift.{u} ℕ × ULift.{u} ℕ // p.1 ≠ p.2})
  exact inferInstanceAs (CountablyCompactSpace (ℕ → DeletedSquare (ULift.{u} ℕ)))

private theorem powerNegativeFiber : ¬ powerProperty (ULift.{u} ℕ) ⊥ := by
  letI : TopologicalSpace (ULift.{u} ℕ) := ⊥
  letI : DiscreteTopology (ULift.{u} ℕ) := discreteTopology_bot _
  letI : DiscreteTopology (DeletedSquare (ULift.{u} ℕ)) :=
    inferInstanceAs (DiscreteTopology {p : ULift.{u} ℕ × ULift.{u} ℕ // p.1 ≠ p.2})
  intro h
  letI : CountablyCompactSpace (ℕ → DeletedSquare (ULift.{u} ℕ)) := h
  let e : ℕ → DeletedSquare (ULift.{u} ℕ) := fun n =>
    ⟨(⟨n⟩, ⟨n + 1⟩), fun heq => by
      have := congrArg ULift.down heq
      change n = n + 1 at this
      omega⟩
  have he : Function.Injective e := by
    intro n m hnm
    exact congrArg (fun x : DeletedSquare (ULift.{u} ℕ) => x.val.1.down) hnm
  haveI : Infinite (DeletedSquare (ULift.{u} ℕ)) := Infinite.of_injective e he
  exact completeUnbounded (DeletedSquare (ULift.{u} ℕ))
    (boundedCliqueProperty_of_countablyCompact_power (DeletedSquare (ULift.{u} ℕ)) ⊤
      (isClosed_discrete _))

def powerFamily : DependentFamily.Registration powerArena.{u} powerScope.{u} where
  actual := powerActual
  bridge := powerBridge
  variation := ⟨@countablyCompactSpace_deletedSquare_power.{u}, powerRejected, powerNegative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨powerRejected, ?_, rfl, powerNegative⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro a
      exact nomatch a
  dependence := by
    intro i
    refine ⟨ULift.{u} ℕ, ⊤, ⊥, ?_⟩
    intro heq
    exact powerNegativeFiber (Eq.mp heq powerPositiveFiber)

end Reg.D5.S3.Topology.StoneCech.DeletedSquareChromatic
