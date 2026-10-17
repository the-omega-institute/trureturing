import Reg.Support.DependentFamily
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

end Reg.D5.S3.Topology.LegalFiberReconstruction
