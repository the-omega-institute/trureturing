import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Topology.LegalFiberReconstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Topology.LegalFiberReconstruction

open _root_.D5.S3.Topology.LegalFiberReconstruction
open _root_.D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open _root_.D5.S3.ConceptDynamics.InformationEscape
open Set Filter _root_.Topology

universe u

/-- The complete source telescope, including every legal fiber and all branchwise hypotheses. -/
structure SourceInputs where
  X : Type u
  metric : MetricSpace X
  compact : @CompactSpace X metric.toUniformSpace.toTopologicalSpace
  K : (n : ℕ) → Prefix n → Set X
  hne : ∀ n s, (K n s).Nonempty
  hc : ∀ n s, @IsCompact X metric.toUniformSpace.toTopologicalSpace (K n s)
  hroot : K 0 (legalPrefix ⟨fun _ => false, by simp⟩ 0) = univ
  hcover : ∀ n (s : Prefix n) x, x ∈ K n s ↔
    ∃ t : Prefix (n + 1), (∀ i : Fin n, t.val i.castSucc = s.val i) ∧
      x ∈ K (n + 1) t
  hdiam : ∀ p : LegalDigits,
    Tendsto (fun n => @Metric.diam X metric.toPseudoMetricSpace (K n (legalPrefix p n)))
      atTop (𝓝 (0 : ℝ))

attribute [instance] SourceInputs.metric SourceInputs.compact

/-- Candidate reconstruction maps have the full infinite legal-name domain. -/
def SourceState (P : SourceInputs.{u}) := LegalDigits → P.X

/-- All three conclusion clauses use the same candidate reconstruction map. -/
def certificate (P : SourceInputs.{u}) (f : SourceState P) : Prop :=
  Continuous f ∧ Function.Surjective f ∧
    ∀ p x, f p = x ↔ ∀ n, x ∈ P.K n (legalPrefix p n)

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
  DependentFamily.realize signature (fun _ P f => certificate P f) (fun a => Empty.elim a)

def arena : DependentFamily.Arena where
  signature := signature.{u}
  Law := fun r => ∀ P, ∃ f, r.readout () P f

abbrev sourceStatement := type_of% (@continuous_reconstruction.{u})

/-- Packing the telescope preserves precisely the original theorem. -/
theorem source_bridge : sourceStatement.{u} ↔ arena.{u}.Law actual.{u} := by
  constructor
  · intro h P
    letI := P.metric
    letI := P.compact
    exact h P.K P.hne P.hc P.hroot P.hcover P.hdiam
  · intro h X metric compact K hne hc hroot hcover hdiam
    exact h ⟨X, metric, compact, K, hne, hc, hroot, hcover, hdiam⟩

theorem actual_positive : arena.{u}.Law actual.{u} :=
  source_bridge.mp @continuous_reconstruction.{u}

/-- A legal name with its only possible occupied digit at zero. -/
private def pointName (b : Bool) : LegalDigits :=
  ⟨fun n => if n = 0 then b else false, by
    intro n h
    have hn : n + 1 ≠ 0 := Nat.succ_ne_zero n
    simpa [hn] using h.2⟩

/-- A two-point member witnesses dependence of the full family; it does not
restrict the source's arbitrary compact metric carrier. -/
@[instance_reducible] private noncomputable def twoPointMetric : MetricSpace (ULift.{u} Bool) :=
  MetricSpace.induced (fun x : ULift.{u} Bool => if x.down then (1 : ℝ) else 0) (by
    intro ⟨b⟩ ⟨c⟩ h
    apply ULift.ext
    cases b <;> cases c <;> simp_all) inferInstance

private def twoPointFibers (n : ℕ) (s : Prefix n) : Set (ULift.{u} Bool) :=
  {x | ∃ p : LegalDigits, legalPrefix p n = s ∧ x.down = p.val 0}

private noncomputable def twoPoint : SourceInputs.{u} := by
  letI := twoPointMetric.{u}
  letI : TopologicalSpace (ULift.{u} Bool) :=
    twoPointMetric.toUniformSpace.toTopologicalSpace
  refine ⟨ULift.{u} Bool, inferInstance, inferInstance, twoPointFibers, ?_, ?_, ?_, ?_, ?_⟩
  · intro n s
    obtain ⟨p, hp⟩ := s.property
    exact ⟨⟨p.val 0⟩, p, Subtype.ext (funext hp), rfl⟩
  · intro n s
    exact (Set.toFinite _).isCompact
  · apply Set.eq_univ_of_forall
    intro x
    exact ⟨pointName x.down, Subtype.ext (funext fun i => Fin.elim0 i), by simp [pointName]⟩
  · intro n s x
    constructor
    · rintro ⟨p, hp, hx⟩
      refine ⟨legalPrefix p (n + 1), ?_, p, rfl, hx⟩
      intro i
      exact congrArg (fun t : Prefix n => t.val i) hp
    · rintro ⟨t, ht, p, hp, hx⟩
      refine ⟨p, Subtype.ext (funext fun i => ?_), hx⟩
      exact (congrArg (fun t : Prefix (n + 1) => t.val i.castSucc) hp).trans (ht i)
  · intro p
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
    symm
    apply Metric.diam_subsingleton
    rintro x ⟨q, hq, hx⟩ y ⟨r, hr, hy⟩
    apply ULift.ext
    have hq0 := congrArg (fun s : Prefix n => s.val ⟨0, by omega⟩) hq
    have hr0 := congrArg (fun s : Prefix n => s.val ⟨0, by omega⟩) hr
    exact (hx.trans hq0).trans (hy.trans hr0).symm

private def rejected : DependentFamily.Realization signature.{u} :=
  DependentFamily.realize signature (fun _ _ _ => False) (fun a => Empty.elim a)

private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  obtain ⟨_, hfalse⟩ := h twoPoint
  exact hfalse

private theorem constant_not_certificate :
    ¬ certificate twoPoint.{u} (fun _ => ⟨false⟩) := by
  intro h
  obtain ⟨p, hp⟩ := h.2.1 ⟨true⟩
  have he : false = true := congrArg ULift.down hp
  exact Bool.false_ne_true he

/-- The actual predicate distinguishes reconstruction maps within one genuine
member of the unrestricted source family. -/
private theorem actual_dependence :
    DependentFamily.ObservationalDependence signature.{u} actual.{u} := by
  intro i
  obtain ⟨f, hf⟩ := actual_positive twoPoint.{u}
  refine ⟨twoPoint, f, (fun _ => ⟨false⟩), ?_⟩
  intro he
  change certificate twoPoint f = certificate twoPoint (fun _ => ⟨false⟩) at he
  change certificate twoPoint f at hf
  exact constant_not_certificate (he ▸ hf)

/-- Whole-family evidence retains every hypothesis and every conclusion clause
through the exact source equivalence. -/
def evidence : DependentFamily.Registration arena.{u} sourceStatement.{u} where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (@Subsingleton.elim Unit inferInstance j i)).elim
    · intro a
      exact Empty.elim a
  dependence := actual_dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@continuous_reconstruction.{u}) (DependentFamily.Realization signature.{u}) Unit Unit where
  unitName :=
    `D5.S3.Topology.LegalFiberReconstruction.continuous_reconstruction.__information_unit
  realizationName := `Reg.D5.S3.Topology.LegalFiberReconstruction.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (DependentFamily.realize signature
    (fun _ P f => certificate P f) (fun a => Empty.elim a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Topology.LegalFiberReconstruction
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Topology.LegalFiberReconstruction
