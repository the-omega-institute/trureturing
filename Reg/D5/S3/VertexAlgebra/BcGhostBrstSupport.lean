import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.BcGhostBrstSupport
import Reg.Support.DependentFamily

set_option autoImplicit false

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.BcGhostFockSupport
open scoped BigOperators

namespace Reg.D5.S3.VertexAlgebra.BcGhostBrstSupport

universe u

noncomputable section

abbrev deletionSignature : Signature where
  Params := Σ K : Type u, CommRing K × ℕ
  State p := @Fock p.1 p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Finset ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def deletionActual : Realization deletionSignature.{u} :=
  realize deletionSignature (fun _ p g => @occupied p.1 p.2.1
    (@annihilate p.1 p.2.1 p.2.2 g)) (fun empty => nomatch empty)

def deletionRejected : Realization deletionSignature.{u} :=
  realize deletionSignature (fun _ _ _ => {0}) (fun empty => nomatch empty)

abbrev deletionArena : Arena where
  signature := deletionSignature.{u}
  Law readout := ∀ {K : Type u} [CommRing K] (i : ℕ) (g : Fock K),
    readout.readout () ⟨K, inferInstance, i⟩ g ⊆ (occupied g).erase i

private theorem deletion_rejected : ¬ deletionArena.{u}.Law deletionRejected := by
  intro hlaw
  have h := hlaw (K := ULift.{u} ℤ) 0 0
  have hzero := h (show 0 ∈ deletionRejected.readout ()
    ⟨ULift.{u} ℤ, inferInstance, 0⟩ 0 by simp [deletionRejected, realize])
  simpa [occupied] using hzero

def deletionEvidence : Registration deletionArena.{u}
    (∀ {K : Type u} [CommRing K] (i : ℕ) (g : Fock K),
      occupied (annihilate i g) ⊆ (occupied g).erase i) where
  actual := deletionActual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.occupied_annihilate_subset,
    deletionRejected, deletion_rejected⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨deletionRejected, ?_, rfl, deletion_rejected⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro empty
      exact nomatch empty
  dependence := by
    intro role
    refine ⟨⟨ULift.{u} ℤ, inferInstance, 0⟩, 0, Finsupp.single {0, 1} 1, ?_⟩
    simp [deletionActual, realize, occupied, annihilate,
      Finsupp.linearCombination_single, annihilateBasis, sign]

def deletionRegistration : Contract.Registration
    (@_root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.occupied_annihilate_subset.{u})
    (Realization deletionSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.BcGhostBrstSupport.deletionUnit
  realizationName := `Reg.D5.S3.VertexAlgebra.BcGhostBrstSupport.deletionEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨deletionArena⟩
  objectArena := .source ⟨deletionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source deletionArena ⟨deletionEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize deletionSignature (fun _ p g => @occupied p.1 p.2.1
    (@annihilate p.1 p.2.1 p.2.2 g)) (fun empty => nomatch empty))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.BcGhostBrstSupport
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms deletionEvidence
#print axioms deletionRegistration

abbrev cSignature : Signature where
  Params := Σ K : Type u, CommRing K × ℤ
  State p := @Fock p.1 p.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := @Fock p.1 p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def cActual : Realization cSignature.{u} :=
  realize cSignature (fun _ p g => @c p.1 p.2.1 (-p.2.2) g)
    (fun empty => nomatch empty)

def cRejected : Realization cSignature.{u} :=
  realize cSignature (fun _ p _ => @vacuum p.1 p.2.1) (fun empty => nomatch empty)

abbrev cArena : Arena where
  signature := cSignature.{u}
  Law readout := ∀ {K : Type u} [CommRing K] (g : Fock K) (n : ℤ),
    n < -_root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.bound g - 2 →
      readout.readout () ⟨K, inferInstance, n⟩ g = 0

private theorem c_rejected : ¬ cArena.{u}.Law cRejected := by
  intro hlaw
  have h := hlaw (K := ULift.{u} ℤ) 0 (-3) (by
    simp [_root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.bound, occupied])
  simpa [cRejected, realize, vacuum] using h

def cEvidence : Registration cArena.{u}
    (∀ {K : Type u} [CommRing K] (g : Fock K) (n : ℤ),
      n < -_root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.bound g - 2 → c (-n) g = 0) where
  actual := cActual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.c_vanish_below,
    cRejected, c_rejected⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨cRejected, ?_, rfl, c_rejected⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro empty
      exact nomatch empty
  dependence := by
    intro role
    refine ⟨⟨ULift.{u} ℤ, inferInstance, 0⟩, 0, vacuum, ?_⟩
    simp [cActual, realize, c, vacuum, create, Finsupp.linearCombination_single,
      createBasis, sign, eq_comm, Finsupp.single_eq_zero]

def cRegistration : Contract.Registration
    (@_root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.c_vanish_below.{u})
    (Realization cSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.BcGhostBrstSupport.cUnit
  realizationName := `Reg.D5.S3.VertexAlgebra.BcGhostBrstSupport.cEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨cArena⟩
  objectArena := .source ⟨cArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source cArena ⟨cEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize cSignature (fun _ p g => @c p.1 p.2.1 (-p.2.2) g)
    (fun empty => nomatch empty))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.BcGhostBrstSupport
    definition := none
    coordinates := #[0, 1, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms cEvidence
#print axioms cRegistration

abbrev arraySignature : Signature where
  Params := Σ K : Type u, CommRing K
  State parameter := @Fock parameter.1 parameter.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ℤ × ℤ → @Fock parameter.1 parameter.2
  Anchor := Empty
  finiteAnchor := inferInstance

def arrayActual : Realization arraySignature.{u} :=
  realize arraySignature
    (fun _ parameter state =>
      @_root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.expanded parameter.1 parameter.2 state)
    (fun empty => nomatch empty)

def arrayRejected : Realization arraySignature.{u} :=
  realize arraySignature
    (fun _ parameter _ _ => @vacuum parameter.1 parameter.2)
    (fun empty => nomatch empty)

abbrev arrayArena : Arena where
  signature := arraySignature.{u}
  Law readout := ∀ {K : Type u} [CommRing K] (state : Fock K),
    Function.support (readout.readout () ⟨K, inferInstance⟩ state) ⊆
      (_root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.rectangle state : Set (ℤ × ℤ))

private theorem array_rejected : ¬ arrayArena.{u}.Law arrayRejected := by
  intro hlaw
  have hbound := hlaw (K := ULift.{u} ℤ) 0
  have hout := hbound (show (5, 0) ∈ Function.support
      (arrayRejected.readout () ⟨ULift.{u} ℤ, inferInstance⟩ 0) by
    simp [arrayRejected, realize, Function.mem_support, vacuum])
  norm_num [_root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.rectangle,
    _root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.modeInterval,
    _root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.bound, occupied] at hout

def arrayEvidence : Registration arrayArena.{u}
    (∀ {K : Type u} [CommRing K] (state : Fock K),
      Function.support (_root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.expanded state) ⊆
        (_root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.rectangle state : Set (ℤ × ℤ))) where
  actual := arrayActual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.expanded_support_rectangle,
    arrayRejected, array_rejected⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨arrayRejected, ?_, rfl, array_rejected⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro empty
      exact nomatch empty
  dependence := by
    intro role
    refine ⟨⟨ULift.{u} ℤ, inferInstance⟩, 0, Finsupp.single {1} 1, ?_⟩
    intro hequal
    have hvalue := congrArg (fun array : ℤ × ℤ → Fock (ULift.{u} ℤ) =>
      array (0, -1) {1, 3}) hequal
    norm_num [arrayActual, realize,
      _root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.expanded, normalPair, b, c,
      create, annihilate, Finsupp.linearCombination_single,
      createBasis, annihilateBasis, sign, Finset.filter_singleton,
      Finsupp.single_apply, Finset.insert_comm] at hvalue
    exact hvalue (Finset.pair_comm 3 1)

def arrayRegistration : Contract.Registration
    (@_root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.expanded_support_rectangle.{u})
    (Realization arraySignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.BcGhostBrstSupport.arrayUnit
  realizationName := `Reg.D5.S3.VertexAlgebra.BcGhostBrstSupport.arrayEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨arrayArena⟩
  objectArena := .source ⟨arrayArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arrayArena ⟨arrayEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize arraySignature
    (fun _ parameter state =>
      @_root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.expanded parameter.1 parameter.2 state)
    (fun empty => nomatch empty))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.BcGhostBrstSupport
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms arrayEvidence
#print axioms arrayRegistration

abbrev outerSignature : Signature where
  Params := Σ K : Type u, CommRing K
  State parameter := @Fock parameter.1 parameter.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := ℤ → @Fock parameter.1 parameter.2
  Anchor := Empty
  finiteAnchor := inferInstance

def outerActual : Realization outerSignature.{u} :=
  realize outerSignature (fun _ parameter state mode =>
    @_root_.D5.S3.VertexAlgebra.BcGhostStressTails.outerNormalPair
      parameter.1 parameter.2 mode state) (fun empty => nomatch empty)

abbrev outerArena : Arena where
  signature := outerSignature.{u}
  Law readout := ∀ {K : Type u} [CommRing K] (state : Fock K),
    Function.support (readout.readout () ⟨K, inferInstance⟩ state) ⊆
      Set.Icc (-_root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.bound state - 2)
        (2 * _root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.bound state + 4)

theorem outerActualPositive : outerArena.{u}.Law outerActual :=
  _root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.normalGhost_support_interval

abbrev jointSignature : Signature where
  Params := Σ K : Type u, CommRing K
  State parameter := @Fock parameter.1 parameter.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ parameter := @Fock parameter.1 parameter.2
  Anchor := Empty
  finiteAnchor := inferInstance

def jointActual : Realization jointSignature.{u} :=
  realize jointSignature (fun _ parameter state =>
    letI := parameter.2
    ∑ᶠ index : ℤ × ℤ, (index.1 - index.2 : parameter.1) •
      @_root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.expanded
        parameter.1 parameter.2 state index) (fun empty => nomatch empty)

abbrev jointArena : Arena where
  signature := jointSignature.{u}
  Law readout := ∀ {K : Type u} [CommRing K] (state : Fock K),
    readout.readout () ⟨K, inferInstance⟩ state =
      ∑ mode ∈ _root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.modeInterval state,
        ∑ index ∈ _root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.rowInterval state,
          (mode - index : K) •
            _root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.expanded state (mode, index)

theorem jointActualPositive : jointArena.{u}.Law jointActual :=
  _root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.expanded_joint_sum

def outerSumActual : Realization jointSignature.{u} :=
  realize jointSignature (fun _ parameter state =>
    ∑ᶠ mode : ℤ, @_root_.D5.S3.VertexAlgebra.BcGhostStressTails.outerNormalPair
      parameter.1 parameter.2 mode state) (fun empty => nomatch empty)

abbrev outerSumArena : Arena where
  signature := jointSignature.{u}
  Law readout := ∀ {K : Type u} [CommRing K] (state : Fock K),
    readout.readout () ⟨K, inferInstance⟩ state =
      ∑ᶠ index : ℤ × ℤ, (index.1 - index.2 : K) •
        _root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.expanded state index

theorem outerSumActualPositive : outerSumArena.{u}.Law outerSumActual :=
  _root_.D5.S3.VertexAlgebra.BcGhostBrstSupport.normalGhost_joint_finsum

#print axioms outerActualPositive
#print axioms jointActualPositive
#print axioms outerSumActualPositive

end

end Reg.D5.S3.VertexAlgebra.BcGhostBrstSupport
