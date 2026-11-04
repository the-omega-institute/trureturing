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

/-- Parameters are exactly the raw source carriers and the existential budget.
Only the selected lower joint observation varies; all original dictionaries,
premises, the upper bound and the existential quantifier remain in the law. -/
abbrev signature.{u,v,w} : _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature where
  Params := Σ K : Type u, Σ I : Type v, Σ O : I → Type w, Finset I
  State := fun p => ∀ i, p.1 → p.2.2.1 i
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ p => p.1 → FiniteObservationOutput p.2.2.1 p.2.2.2
  Anchor := Empty
  finiteAnchor := inferInstance

open _root_.D5.S3.ConceptDynamics.InformationEscape

def actual.{u,v,w} : DependentFamily.Realization signature.{u,v,w} :=
  DependentFamily.realize signature.{u,v,w}
    (fun _ p q => finiteObservationReadout q p.2.2.2) (fun a => Empty.elim a)

abbrev arena.{u,v,w,z} : DependentFamily.Arena where
  signature := signature.{u,v,w}
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
        (s a).totalVariation.real univ - ε <
          (SignedMeasure.totalVariation
            ((s a).map (r.readout () ⟨K, ⟨I, ⟨O, J⟩⟩⟩ (fun i x => q i x)))).real univ ∧
        (SignedMeasure.totalVariation
            ((s a).map (finiteObservationReadout (fun i x => q i x) J))).real univ ≤
          (s a).totalVariation.real univ

theorem source_bridge.{u,v,w,z} : uniformScope.{u,v,w,z} ↔
    arena.{u,v,w,z}.Law actual.{u,v,w} := by rfl

theorem actual_positive.{u,v,w,z} : arena.{u,v,w,z}.Law actual.{u,v,w} :=
  source_bridge.mp uniform_source_proof

/-- Collapse the input only when it is inhabited. This is a total family even
for empty carriers and empty output fibers; no inhabitant is postulated. -/
noncomputable def rejected.{u,v,w} : DependentFamily.Realization signature.{u,v,w} :=
  by
  classical
  exact DependentFamily.realize signature.{u,v,w}
    (fun _ p q => if h : Nonempty p.1 then
      fun _ j => q j.val (Classical.choice h)
      else finiteObservationReadout q p.2.2.2) (fun a => Empty.elim a)

private theorem collapse_map_zero.{u,v,w} (J : Finset (ULift.{v} Unit)) :
    let K := ULift.{u} Bool
    let O : ULift.{v} Unit → Type w := fun _ => ULift.{w} Bool
    let q : ∀ i, K → O i := fun _ x => ULift.up x.down
    let s : SignedMeasure K := (Measure.dirac (ULift.up false)).toSignedMeasure -
      (Measure.dirac (ULift.up true)).toSignedMeasure
    s.map (rejected.readout () ⟨K, ⟨ULift.{v} Unit, ⟨O, J⟩⟩⟩ q) = 0 := by
  classical
  dsimp
  let c : FiniteObservationOutput (fun _ : ULift.{v} Unit => ULift.{w} Bool) J :=
    fun j => ULift.up (Classical.choice (inferInstance : Nonempty (ULift.{u} Bool))).down
  have heq : rejected.readout ()
      ⟨ULift.{u} Bool, ⟨ULift.{v} Unit, ⟨fun _ => ULift.{w} Bool, J⟩⟩⟩
      (fun _ x => ULift.up x.down) = fun _ => c := by
    dsimp [rejected, DependentFamily.realize]
    rw [dif_pos (inferInstance : Nonempty (ULift.{u} Bool))]
  rw [heq]
  ext B hB
  rw [VectorMeasure.map_apply _ measurable_const hB]
  by_cases hc : c ∈ B
  · have hpre : (fun _ : ULift.{u} Bool => c) ⁻¹' B = univ := by ext; simp [hc]
    simp [hpre, Measure.toSignedMeasure_apply_measurable]
  · have hpre : (fun _ : ULift.{u} Bool => c) ⁻¹' B = ∅ := by ext; simp [hc]
    simp [hpre]

theorem rejected_law.{u,v,w,z} : ¬ arena.{u,v,w,z}.Law rejected.{u,v,w} := by
  classical
  intro h
  let K := ULift.{u} Bool
  let I := ULift.{v} Unit
  let O : I → Type w := fun _ => ULift.{w} Bool
  let A := ULift.{z} Unit
  let q : ∀ i, C(K, O i) := fun _ => ⟨fun x => ULift.up x.down, continuous_of_discreteTopology⟩
  have hsep : Function.Injective (fun x : K => fun i => q i x) := by
    intro x y hxy
    have hh := congrFun hxy (ULift.up ())
    change (ULift.up x.down : ULift.{w} Bool) = ULift.up y.down at hh
    exact ULift.ext (congrArg (fun t : ULift.{w} Bool => t.down) hh)
  let t : SignedMeasure K := (Measure.dirac (ULift.up false)).toSignedMeasure -
    (Measure.dirac (ULift.up true)).toSignedMeasure
  let s : A → SignedMeasure K := fun _ => t
  have hp : ∀ a, (s a).toJordanDecomposition.posPart.Regular := by intro; infer_instance
  have hn : ∀ a, (s a).toJordanDecomposition.negPart.Regular := by intro; infer_instance
  have hc : IsCompact (Set.range (fun a => signedFunctional (s a))) := by
    simpa [s] using (isCompact_singleton : IsCompact ({signedFunctional t} : Set (StrongDual ℝ C(K, ℝ))))
  obtain ⟨J,hJ⟩ := h q hsep s hp hn hc (1/2) (by norm_num)
  have hl := (hJ (ULift.up ())).1
  have hm : t.map (rejected.readout () ⟨K, ⟨I, ⟨O, J⟩⟩⟩ (fun i x => q i x)) = 0 :=
    collapse_map_zero J
  change t.totalVariation.real univ - 1/2 < (SignedMeasure.totalVariation
    (t.map (rejected.readout () ⟨K, ⟨I, ⟨O, J⟩⟩⟩ (fun i x => q i x)))).real univ at hl
  rw [hm] at hl
  have hv := t.norm_le_totalVariation ({ULift.up false} : Set K)
  have heval : t ({ULift.up false} : Set K) = 1 := by
    simp [t, Measure.toSignedMeasure_apply_measurable]
  rw [heval] at hv
  have hmono : t.totalVariation.real ({ULift.up false} : Set K) ≤ t.totalVariation.real univ :=
    measureReal_mono (subset_univ _)
  norm_num [SignedMeasure.totalVariation_zero] at hl hv
  linarith

private theorem actual_dependence.{u,v,w} :
    DependentFamily.ObservationalDependence signature.{u,v,w} actual.{u,v,w} := by
  classical
  intro i
  let p : signature.{u,v,w}.Params :=
    ⟨ULift.{u} Bool, ⟨ULift.{v} Unit,
      ⟨fun _ => ULift.{w} Bool, {ULift.up ()}⟩⟩⟩
  refine ⟨p, (fun _ _ => ULift.up false), (fun _ x => ULift.up x.down), ?_⟩
  intro h
  have hh := congrFun (congrFun h (ULift.up true)) ⟨ULift.up (), by simp [p]⟩
  exact Bool.false_ne_true (congrArg ULift.down hh)

noncomputable def familyRegistration.{u,v,w,z} :
    DependentFamily.Registration arena.{u,v,w,z} uniformScope.{u,v,w,z} where
  actual := actual.{u,v,w}
  bridge := source_bridge.{u,v,w,z}
  variation := ⟨actual_positive.{u,v,w,z}, rejected.{u,v,w}, rejected_law.{u,v,w,z}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected.{u,v,w}, ?_, rfl, rejected_law.{u,v,w,z}⟩
      intro j hji
      exact False.elim (hji (@Subsingleton.elim Unit _ j i))
    · intro a; exact Empty.elim a
  dependence := actual_dependence.{u,v,w}

noncomputable def registration.{u,v,w,z} :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Topology.Measures.FiniteObservationVariation.exists_uniform_finite_readout_variation.{u,v,w,z})
      (_root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization
        signature.{u,v,w}) Type Unit where
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
    signature.{u,v,w} (fun _ p q => finiteObservationReadout q p.2.2.2) (fun a => Empty.elim a))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Topology.Measures.FiniteObservationVariation
    definition := none
    coordinates := #[0, 4, 5, 23]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "fn", "arg", "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Topology.Measures.FiniteObservationVariation
