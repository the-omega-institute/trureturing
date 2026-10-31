import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.Measures.FiniteObservationVariation

namespace Reg.D5.S3.Topology.Measures.FiniteObservationVariation

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set MeasureTheory
open _root_.D5.S3.Topology.Measures.NormPreservingLifts
open _root_.D5.S3.ConceptDynamics.CanonicalImage.FiniteObservationQuotientRange

abbrev uniformScope.{u,v,w,z} :=
  ∀ {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    {I : Type v} {O : I → Type w}
    [∀ i, TopologicalSpace (O i)] [∀ i, DiscreteTopology (O i)]
    [∀ i, Fintype (O i)] [ZeroDimensionalSpace K]
    [MeasurableSpace K] [BorelSpace K]
    [∀ i, MeasurableSpace (O i)] [∀ i, BorelSpace (O i)]
    {A : Type z}
    (q : ∀ i, C(K, O i))
    (hsep : Function.Injective (fun x : K => fun i => q i x))
    (s : A → SignedMeasure K)
    (hp : ∀ a, (s a).toJordanDecomposition.posPart.Regular)
    (hn : ∀ a, (s a).toJordanDecomposition.negPart.Regular)
    (hcompact : IsCompact (Set.range (fun a => signedFunctional (s a))))
    (ε : ℝ) (hε : 0 < ε),
    ∃ J : Finset I, ∀ a,
      (s a).totalVariation.real univ - ε <
          (SignedMeasure.totalVariation
            ((s a).map (finiteObservationReadout (fun i x => q i x) J))).real univ ∧
        (SignedMeasure.totalVariation
            ((s a).map (finiteObservationReadout (fun i x => q i x) J))).real univ ≤
          (s a).totalVariation.real univ

theorem uniform_source_proof.{u,v,w,z} : uniformScope.{u,v,w,z} :=
  @_root_.D5.S3.Topology.Measures.FiniteObservationVariation.exists_uniform_finite_readout_variation.{u,v,w,z}

/-- The four non-dictionary source coordinates in the original telescope.
Topology, measurability and proof dictionaries remain in the law's complete
source telescope; the ε occurrence is the registered state. -/
abbrev signature.{u,v,w,z} : _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature where
  Params := Σ K : Type u, Σ I : Type v, Σ O : I → Type w, Type z
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual.{u,v,w,z} : _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization
    signature.{u,v,w,z} :=
  _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize signature.{u,v,w,z}
    (fun _ _ ε => ε) (fun a => Empty.elim a)

abbrev arena.{u,v,w,z} : _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena where
  signature := signature.{u,v,w,z}
  Law r :=
    ∀ {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
      {I : Type v} {O : I → Type w}
      [∀ i, TopologicalSpace (O i)] [∀ i, DiscreteTopology (O i)]
      [∀ i, Fintype (O i)] [ZeroDimensionalSpace K]
      [MeasurableSpace K] [BorelSpace K]
      [∀ i, MeasurableSpace (O i)] [∀ i, BorelSpace (O i)]
      {A : Type z}
      (q : ∀ i, C(K, O i))
      (hsep : Function.Injective (fun x : K => fun i => q i x))
      (s : A → SignedMeasure K)
      (hp : ∀ a, (s a).toJordanDecomposition.posPart.Regular)
      (hn : ∀ a, (s a).toJordanDecomposition.negPart.Regular)
      (hcompact : IsCompact (Set.range (fun a => signedFunctional (s a))))
      (ε : ℝ) (hε : 0 < ε),
      ∃ J : Finset I, ∀ a,
        (s a).totalVariation.real univ - r.readout ()
            ⟨K, ⟨I, ⟨O, A⟩⟩⟩ ε <
          (SignedMeasure.totalVariation
            ((s a).map (finiteObservationReadout (fun i x => q i x) J))).real univ ∧
        (SignedMeasure.totalVariation
            ((s a).map (finiteObservationReadout (fun i x => q i x) J))).real univ ≤
          (s a).totalVariation.real univ

theorem source_bridge.{u,v,w,z} : uniformScope.{u,v,w,z} ↔
    arena.{u,v,w,z}.Law actual.{u,v,w,z} := by
  rfl

theorem actual_positive.{u,v,w,z} : arena.{u,v,w,z}.Law actual.{u,v,w,z} :=
  (source_bridge.{u,v,w,z}).mp (uniform_source_proof.{u,v,w,z})

def rejected.{u,v,w,z} : _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization
    signature.{u,v,w,z} :=
  _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize signature.{u,v,w,z}
    (fun _ _ _ => 0) (fun a => Empty.elim a)

theorem rejected_law.{u,v,w,z} : ¬ arena.{u,v,w,z}.Law rejected.{u,v,w,z} := by
  intro h
  let K : Type u := ULift.{u} Unit
  let I : Type v := ULift.{v} Unit
  let O : I → Type w := fun _ => ULift.{w} Unit
  let A : Type z := ULift.{z} Unit
  let q : ∀ i, C(K, O i) := fun _ => ContinuousMap.const _ (ULift.up ())
  have hsep : Function.Injective (fun x : K => fun i => q i x) := by
    intro x y hxy
    exact Subsingleton.elim x y
  let s : A → SignedMeasure K := fun _ => 0
  have hp : ∀ a, (s a).toJordanDecomposition.posPart.Regular := by
    intro a
    infer_instance
  have hn : ∀ a, (s a).toJordanDecomposition.negPart.Regular := by
    intro a
    infer_instance
  have hcompact : IsCompact (Set.range (fun a =>
      _root_.D5.S3.Topology.Measures.NormPreservingLifts.signedFunctional (s a))) := by
    simpa [s] using (isCompact_singleton :
      IsCompact ({(0 : StrongDual ℝ C(K, ℝ))} : Set (StrongDual ℝ C(K, ℝ))))
  obtain ⟨J, hJ⟩ := h (K := K) (I := I) (O := O) (A := A)
    q hsep s hp hn hcompact 1 (by norm_num)
  have hz := hJ (ULift.up () : A)
  have hbad := hz.1
  norm_num [rejected, s,
    _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize] at hbad
  have hbad' : (0 : ℝ) < 0 := by
    simpa [SignedMeasure.totalVariation_zero] using hbad
  exact (lt_irrefl _ hbad')

private theorem actual_dependence.{u,v,w,z} :
    _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.ObservationalDependence
      signature.{u,v,w,z} actual.{u,v,w,z} := by
  intro i
  let p : signature.{u,v,w,z}.Params :=
    ⟨ULift.{u} Unit, ⟨ULift.{v} Unit, ⟨fun _ => ULift.{w} Unit, ULift.{z} Unit⟩⟩⟩
  refine ⟨p, 0, 1, ?_⟩
  norm_num [actual, _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize]

noncomputable def familyRegistration.{u,v,w,z} :
    _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration
      arena.{u,v,w,z} uniformScope.{u,v,w,z} where
  actual := actual.{u,v,w,z}
  bridge := source_bridge.{u,v,w,z}
  variation := ⟨actual_positive.{u,v,w,z}, rejected.{u,v,w,z}, rejected_law.{u,v,w,z}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected.{u,v,w,z}, ?_, rfl, rejected_law.{u,v,w,z}⟩
      intro j hji
      exact False.elim (hji (@Subsingleton.elim Unit _ j i))
    · intro a
      exact Empty.elim a
  dependence := actual_dependence.{u,v,w,z}

noncomputable def registration.{u,v,w,z} :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Topology.Measures.FiniteObservationVariation.exists_uniform_finite_readout_variation.{u,v,w,z})
      (_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization
        signature.{u,v,w,z}) Type Unit where
  unitName := `D5.S3.Topology.Measures.FiniteObservationVariation.exists_uniform_finite_readout_variation.__information_unit
  realizationName := `Reg.D5.S3.Topology.Measures.FiniteObservationVariation.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v,w,z}⟩
  objectArena := .source ⟨arena.{u,v,w,z}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v,w,z} ⟨familyRegistration.{u,v,w,z}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize
    signature.{u,v,w,z} (fun _ _ ε => ε) (fun a => Empty.elim a))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Topology.Measures.FiniteObservationVariation
    definition := none
    coordinates := #[0, 4, 5, 14]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 21
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Topology.Measures.FiniteObservationVariation
