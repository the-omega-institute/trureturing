import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.Resolution.StoneanFiniteClosedRefinement

/-!
# Stonean refinement source scopes

The original topology and separation structures, maps, hypotheses and universe
levels remain in the source families. Empty spaces and pieces are included.
Kernel source equivalence is distinct from the raw source-selection and typed
readout reconstruction needed for a validated four-slot registration.
-/

namespace Reg.D5.S3.Topology.Resolution.StoneanFiniteClosedRefinement

open Set _root_.Topology
open _root_.D5.S3.Topology.Resolution.StoneanFiniteClosedRefinement
open _root_.D5.S3.Topology.AlmostDisjoint.AdaptiveRefinementCounterexample
open _root_.D5.S3.ConceptDynamics.InformationEscape

universe u v

namespace Local

structure Inputs where
  T : Type u
  B : Type v
  topT : TopologicalSpace T
  topB : TopologicalSpace B
  regular : @RegularSpace T topT
  disconnected : @ExtremallyDisconnected B topB
  p : T → B
  continuous : @Continuous T B topT topB p
  openMap : @IsOpenMap T B topT topB p
  closedMap : @IsClosedMap T B topT topB p
  W : Set T
  openW : @IsOpen T topT W

abbrev State (P : Inputs.{u, v}) :=
  letI := P.topT
  Set (closure P.W)

def readout (P : Inputs.{u, v}) (V : State P) : Prop :=
  letI := P.topT
  letI := P.topB
  IsOpen ((P.p ∘ (Subtype.val : closure P.W → P.T)) '' V)

def signature : DependentFamily.Signature where
  Params := Inputs.{u, v}
  State := State
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature.{u, v} :=
  DependentFamily.realize signature (fun _ P V => readout P V) (fun a => nomatch a)

def arena : DependentFamily.Arena where
  signature := signature.{u, v}
  Law := fun R => ∀ (P : Inputs.{u, v}) (V : State P),
    @IsOpen (↥(@closure P.T P.topT P.W))
      (TopologicalSpace.induced Subtype.val P.topT) V → R.readout () P V

abbrev sourceScope := type_of%
  (@isOpenMap_closure_domRestrict_of_regular_extremallyDisconnected.{u, v})

theorem source_bridge : sourceScope.{u, v} ↔ arena.{u, v}.Law actual.{u, v} := by
  constructor
  · intro h P
    letI := P.topT
    letI := P.topB
    letI := P.regular
    letI := P.disconnected
    exact h P.continuous P.openMap P.closedMap P.W P.openW
  · intro h T B topT topB regular disconnected p hp hpo hpc W hW
    exact h ⟨T, B, topT, topB, regular, disconnected, p, hp, hpo, hpc, W, hW⟩

theorem actual_positive : arena.{u, v}.Law actual.{u, v} :=
  source_bridge.mp (@isOpenMap_closure_domRestrict_of_regular_extremallyDisconnected.{u, v})

def sampleInputs : Inputs.{u, v} where
  T := ULift.{u} Bool
  B := ULift.{v} Bool
  topT := ⊤
  topB := ⊤
  regular := by
    letI : TopologicalSpace (ULift.{u} Bool) := ⊤
    constructor
    intro s a hs ha
    rcases (IndiscreteTopology.isClosed_iff s).mp hs with rfl | rfl
    · simp
    · exact (ha (mem_univ a)).elim
  disconnected := by
    letI : TopologicalSpace (ULift.{v} Bool) := ⊤
    constructor
    intro U hU
    rcases (IndiscreteTopology.isOpen_iff U).mp hU with rfl | rfl <;> simp
  p := fun t => ULift.up t.down
  continuous := by
    letI : TopologicalSpace (ULift.{u} Bool) := ⊤
    letI : TopologicalSpace (ULift.{v} Bool) := ⊤
    exact continuous_of_indiscreteTopology
  openMap := by
    letI : TopologicalSpace (ULift.{u} Bool) := ⊤
    letI : TopologicalSpace (ULift.{v} Bool) := ⊤
    intro U hU
    rcases (IndiscreteTopology.isOpen_iff U).mp hU with rfl | rfl
    · simp
    · have hr : (fun t : ULift.{u} Bool => (ULift.up t.down : ULift.{v} Bool)) '' univ = univ := by
        ext b
        constructor
        · intro _; trivial
        · intro _; exact ⟨ULift.up b.down, mem_univ _, by cases b; rfl⟩
      rw [hr]
      exact isOpen_univ
  closedMap := by
    letI : TopologicalSpace (ULift.{u} Bool) := ⊤
    letI : TopologicalSpace (ULift.{v} Bool) := ⊤
    intro U hU
    rcases (IndiscreteTopology.isClosed_iff U).mp hU with rfl | rfl
    · simp
    · have hr : (fun t : ULift.{u} Bool => (ULift.up t.down : ULift.{v} Bool)) '' univ = univ := by
        ext b
        constructor
        · intro _; trivial
        · intro _; exact ⟨ULift.up b.down, mem_univ _, by cases b; rfl⟩
      rw [hr]
      exact isClosed_univ
  W := univ
  openW := by
    letI : TopologicalSpace (ULift.{u} Bool) := ⊤
    exact isOpen_univ

def rejected : DependentFamily.Realization signature.{u, v} :=
  DependentFamily.realize signature (fun _ _ _ => False) (fun a => nomatch a)

theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  have hf := h sampleInputs.{u, v} univ (by letI := sampleInputs.{u, v}.topT; exact isOpen_univ)
  exact hf

def singletonState : State sampleInputs.{u, v} :=
  {⟨ULift.up false, @subset_closure _ sampleInputs.{u, v}.topT _ _ (mem_univ _)⟩}

theorem singleton_readout_false : ¬ readout sampleInputs.{u, v} singletonState := by
  letI : TopologicalSpace (ULift.{v} Bool) := ⊤
  intro h
  have ho : IsOpen ({ULift.up false} : Set (ULift.{v} Bool)) := by
    change @IsOpen (ULift.{v} Bool) ⊤
      ((fun t : ↥(@closure (ULift.{u} Bool) ⊤ univ) =>
        (ULift.up t.val.down : ULift.{v} Bool)) '' singletonState) at h
    have hi : (fun t : ↥(@closure (ULift.{u} Bool) ⊤ univ) =>
        (ULift.up t.val.down : ULift.{v} Bool)) '' singletonState =
        {ULift.up false} := by
      ext b
      constructor
      · rintro ⟨t, ht, rfl⟩
        have ht' : t = ⟨ULift.up false,
            @subset_closure _ sampleInputs.{u, v}.topT _ _ (mem_univ _)⟩ :=
          mem_singleton_iff.mp ht
        subst t
        rfl
      · intro hb
        have hb' := mem_singleton_iff.mp hb
        subst b
        exact ⟨⟨ULift.up false, @subset_closure _ sampleInputs.{u, v}.topT _ _ (mem_univ _)⟩,
          mem_singleton _, rfl⟩
    rw [hi] at h
    exact h
  rcases (IndiscreteTopology.isOpen_iff _).mp ho with he | he
  · have hf : (ULift.up false : ULift.{v} Bool) ∈ (∅ : Set (ULift.{v} Bool)) :=
      he ▸ mem_singleton _
    exact hf
  · have ht : (ULift.up true : ULift.{v} Bool) ∈ ({ULift.up false} : Set (ULift.{v} Bool)) :=
      he.symm ▸ mem_univ _
    have hh : true = false := congrArg ULift.down (mem_singleton_iff.mp ht)
    exact Bool.noConfusion hh

def familyRegistration : DependentFamily.Registration arena.{u, v} sourceScope.{u, v} where
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
    refine ⟨sampleInputs.{u, v}, univ, singletonState, ?_⟩
    intro heq
    have hg := actual_positive sampleInputs.{u, v} univ
      (by letI := sampleInputs.{u, v}.topT; exact isOpen_univ)
    have he : readout sampleInputs.{u, v} univ = readout sampleInputs.{u, v} singletonState := heq
    exact singleton_readout_false (he ▸ hg)

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@isOpenMap_closure_domRestrict_of_regular_extremallyDisconnected.{u, v})
      (DependentFamily.Realization signature.{u, v}) Unit Unit where
  unitName := `D5.S3.Topology.Resolution.StoneanFiniteClosedRefinement.isOpenMap_closure_domRestrict_of_regular_extremallyDisconnected.__information_unit
  realizationName := `Reg.D5.S3.Topology.Resolution.StoneanFiniteClosedRefinement.Local.familyRegistration
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
    (fun _ P V => readout P V) (fun a => nomatch a))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Local

namespace Finite

structure Inputs where
  T : Type u
  B : Type v
  topT : TopologicalSpace T
  topB : TopologicalSpace B
  regular : @RegularSpace T topT
  normal : @NormalSpace T topT
  disconnected : @ExtremallyDisconnected B topB
  p : T → B
  continuous : @Continuous T B topT topB p
  openMap : @IsOpenMap T B topT topB p
  closedMap : @IsClosedMap T B topT topB p
  n : ℕ
  U : Fin n → Set T
  openU : ∀ i, @IsOpen T topT (U i)
  cover : iUnion U = univ

abbrev State (P : Inputs.{u, v}) :=
  Σ m : ℕ, (Fin m → Set P.T) × (Fin m → Fin P.n)

def readout (P : Inputs.{u, v}) (w : State P) : Prop :=
  letI := P.topT
  letI := P.topB
  (∀ j, IsClosed (w.2.1 j)) ∧
    (∀ x, ∃ j, x ∈ w.2.1 j) ∧
    (∀ j, w.2.1 j ⊆ P.U (w.2.2 j)) ∧
    (∀ j, IsOpenMap (fun x : w.2.1 j => P.p x.val))

def signature : DependentFamily.Signature where
  Params := Inputs.{u, v}
  State := State
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature.{u, v} :=
  DependentFamily.realize signature (fun _ P w => readout P w) (fun a => nomatch a)

def arena : DependentFamily.Arena where
  signature := signature.{u, v}
  Law := fun R => ∀ P, ∃ w, R.readout () P w

abbrev sourceScope := type_of%
  (@hasFiniteClosedRefinement_of_regular_normal_extremallyDisconnected.{u, v})

theorem source_bridge : sourceScope.{u, v} ↔ arena.{u, v}.Law actual.{u, v} := by
  constructor
  · intro h P
    letI := P.topT
    letI := P.topB
    letI := P.regular
    letI := P.normal
    letI := P.disconnected
    obtain ⟨m, K, side, hK⟩ := h P.continuous P.openMap P.closedMap P.U P.openU P.cover
    exact ⟨⟨m, K, side⟩, hK⟩
  · intro h T B topT topB regular normal disconnected p hp hpo hpc n U hU hcover
    obtain ⟨⟨m, K, side⟩, hw⟩ :=
      h ⟨T, B, topT, topB, regular, normal, disconnected, p, hp, hpo, hpc, n, U, hU, hcover⟩
    exact ⟨m, K, side, hw⟩

theorem actual_positive : arena.{u, v}.Law actual.{u, v} :=
  source_bridge.mp (@hasFiniteClosedRefinement_of_regular_normal_extremallyDisconnected.{u, v})

def sampleInputs : Inputs.{u, v} where
  T := PUnit.{u+1}
  B := PUnit.{v+1}
  topT := inferInstance
  topB := inferInstance
  regular := inferInstance
  normal := inferInstance
  disconnected := inferInstance
  p := fun _ => PUnit.unit
  continuous := continuous_const
  openMap := fun _ _ => isOpen_discrete _
  closedMap := fun _ _ => isClosed_discrete _
  n := 1
  U := fun _ => univ
  openU := fun _ => isOpen_univ
  cover := by
    ext x
    constructor
    · intro _; trivial
    · intro _; exact mem_iUnion.mpr ⟨0, mem_univ _⟩

def rejected : DependentFamily.Realization signature.{u, v} :=
  DependentFamily.realize signature (fun _ _ _ => False) (fun a => nomatch a)

theorem rejected_law : ¬ arena.{u, v}.Law rejected := by
  intro h
  obtain ⟨w, hw⟩ := h sampleInputs.{u, v}
  exact hw

def emptyState : State sampleInputs.{u, v} := ⟨0, Fin.elim0, Fin.elim0⟩

theorem empty_readout_false : ¬ readout sampleInputs.{u, v} emptyState := by
  intro h
  obtain ⟨j, _⟩ := h.2.1 PUnit.unit
  exact Fin.elim0 j

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
    obtain ⟨w, hw⟩ := actual_positive sampleInputs.{u, v}
    refine ⟨sampleInputs.{u, v}, w, emptyState, ?_⟩
    intro heq
    have he : readout sampleInputs.{u, v} w = readout sampleInputs.{u, v} emptyState := heq
    exact empty_readout_false (he ▸ hw)

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@hasFiniteClosedRefinement_of_regular_normal_extremallyDisconnected.{u, v})
      (DependentFamily.Realization signature.{u, v}) Unit Unit where
  unitName := `D5.S3.Topology.Resolution.StoneanFiniteClosedRefinement.hasFiniteClosedRefinement_of_regular_normal_extremallyDisconnected.__information_unit
  realizationName := `Reg.D5.S3.Topology.Resolution.StoneanFiniteClosedRefinement.Finite.familyRegistration
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
    (fun _ P w => readout P w) (fun a => nomatch a))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Finite

end Reg.D5.S3.Topology.Resolution.StoneanFiniteClosedRefinement
