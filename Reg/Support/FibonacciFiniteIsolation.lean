import Reg.Support.FibonacciBranchSeparation
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas

namespace Reg.Support.FibonacciFiniteIsolation
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open _root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
open Reg.Support.FibonacciConsensus
open Set
noncomputable section

local instance : Fintype Label :=
  ⟨{.L3,.L0,.L5,.L2,.L25},by intro l; cases l <;> simp⟩
local instance : Fintype Guard := ⟨{.G0,.G1},by intro s; cases s <;> simp⟩
local instance : TopologicalSpace Label := ⊥
local instance : TopologicalSpace Guard := ⊥
local instance : TopologicalSpace (Option Guard) := ⊥
local instance : DiscreteTopology Label := discreteTopology_bot _
local instance : DiscreteTopology Guard := discreteTopology_bot _
local instance : DiscreteTopology (Option Guard) := discreteTopology_bot _

private abbrev Witness := (ℕ → Label) × (ℕ → Guard) × (ℕ → ℝ)

private def coherent (v : Witness) : Prop :=
  v.2.1 0 = .G0 ∧
  (∀ p, nextGuard (v.2.1 p) (v.1 p) = some (v.2.1 (p+1))) ∧
  (∀ p, InSupport (v.2.1 p) (v.2.2 p)) ∧
  (∀ p, v.2.2 p = branch (v.1 p) (v.2.2 (p+1)))

private def observed (theta : ℝ) (r : ℕ → Color) (N : ℕ) (v : Witness) : Prop :=
  ∀ p, p < N → ClosedExpanded theta (r p) (v.2.2 p)

private def badPrefix (alpha : ℕ → Label) (p : ℕ) (v : Witness) : Prop :=
  ∃ j : Fin (p+1), v.1 j ≠ alpha j

private theorem label_cont (p : ℕ) : Continuous (fun v : Witness => v.1 p) :=
  (continuous_apply p).comp continuous_fst

private theorem guard_cont (p : ℕ) : Continuous (fun v : Witness => v.2.1 p) :=
  (continuous_apply p).comp (continuous_fst.comp continuous_snd)

private theorem scalar_cont (p : ℕ) : Continuous (fun v : Witness => v.2.2 p) :=
  (continuous_apply p).comp (continuous_snd.comp continuous_snd)

private theorem coherent_closed : IsClosed {v : Witness | coherent v} := by
  have initial : IsClosed {v : Witness | v.2.1 0 = .G0} :=
    isClosed_eq (guard_cont 0) continuous_const
  have edge (p : ℕ) :
      IsClosed {v : Witness | nextGuard (v.2.1 p) (v.1 p) = some (v.2.1 (p+1))} := by
    exact isClosed_eq
      ((continuous_of_discreteTopology (f := fun q : Guard × Label => nextGuard q.1 q.2)).comp
        ((guard_cont p).prodMk (label_cont p)))
      ((continuous_of_discreteTopology (f := @Option.some Guard)).comp (guard_cont (p+1)))
  have support (p : ℕ) : IsClosed {v : Witness | InSupport (v.2.1 p) (v.2.2 p)} := by
    exact (isClosed_le continuous_const (scalar_cont p)).inter
      (isClosed_le (scalar_cont p)
        ((continuous_of_discreteTopology (f := supportUpper)).comp (guard_cont p)))
  have recurrence (p : ℕ) :
      IsClosed {v : Witness | v.2.2 p = branch (v.1 p) (v.2.2 (p+1))} := by
    exact isClosed_eq (scalar_cont p)
      (((continuous_of_discreteTopology (f := shift)).comp (label_cont p)).sub
        ((continuous_const (y := g)).mul (scalar_cont (p+1))))
  simpa only [coherent,Set.setOf_and,Set.setOf_forall] using
    initial.inter ((isClosed_iInter edge).inter
      ((isClosed_iInter support).inter (isClosed_iInter recurrence)))

private theorem observed_closed (theta : ℝ) (r : ℕ → Color) (N : ℕ) :
    IsClosed {v : Witness | observed theta r N v} := by
  simp only [observed,Set.setOf_forall]
  apply isClosed_iInter
  intro p
  apply isClosed_iInter
  intro hp
  exact ((isClosed_le continuous_const (scalar_cont p)).inter
    (isClosed_le (scalar_cont p) continuous_const)).inter
    ((isClosed_le continuous_const (scalar_cont p)).inter
      (isClosed_le (scalar_cont p) continuous_const))

private theorem bad_closed (alpha : ℕ → Label) (p : ℕ) :
    IsClosed {v : Witness | badPrefix alpha p v} := by
  simp only [badPrefix,Set.setOf_exists]
  apply isClosed_iUnion_of_finite
  intro j
  exact (isClosed_discrete {l : Label | l ≠ alpha j}).preimage (label_cont j)

private def ambient : Set Witness :=
  Set.univ ×ˢ (Set.univ ×ˢ Set.pi Set.univ (fun _ : ℕ => Set.Icc (-1 : ℝ) phi))

private theorem ambient_compact : IsCompact ambient :=
  isCompact_univ.prod (isCompact_univ.prod (isCompact_univ_pi fun _ => isCompact_Icc))

private theorem coherent_bounded {v : Witness} (hv : coherent v) : v ∈ ambient := by
  refine ⟨Set.mem_univ _,Set.mem_univ _,?_⟩
  intro p hp
  have hs := hv.2.2.1 p
  refine ⟨hs.1,hs.2.trans ?_⟩
  cases v.2.1 p <;> simp only [supportUpper]
  · exact le_refl _
  · dsimp [phi]; linarith

/-- Compactness retains every infinite legal source and every closed observation
constraint. A persistent bad finite prefix would give a full bad candidate. -/
theorem isolation_below (o : Ownership) (theta : ℝ) (htheta : theta < lam) :
    FiniteIsolation o theta := by
  classical
  intro alpha r record finite p
  by_contra failure
  push_neg at failure
  let sets : ℕ → Set Witness := fun N =>
    {v | coherent v ∧ observed theta r (N+p+1) v ∧ badPrefix alpha p v}
  have closed (N : ℕ) : IsClosed (sets N) :=
    coherent_closed.inter ((observed_closed theta r _).inter (bad_closed alpha p))
  have decreasing (N : ℕ) : sets (N+1) ⊆ sets N := by
    intro v hv
    exact ⟨hv.1,fun j hj => hv.2.1 j (by omega),hv.2.2⟩
  have nonempty (N : ℕ) : (sets N).Nonempty := by
    obtain ⟨beta,candidate,j,hj,different⟩ := failure (N+p+1) (by omega)
    obtain ⟨y,⟨path,h0,edges,support,recurrence⟩,obs⟩ := candidate
    refine ⟨(beta,path,y),⟨h0,edges,support,recurrence⟩,?_,
      ⟨⟨j,by omega⟩,different⟩⟩
    intro q hq
    simpa only [front,List.getElem_ofFn] using
      obs q (by simpa only [front,List.length_ofFn] using hq)
  have compact : IsCompact (sets 0) :=
    ambient_compact.of_isClosed_subset (closed 0) (fun v hv => coherent_bounded hv.1)
  obtain ⟨v,hv⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    sets decreasing nonempty compact closed
  have all (N : ℕ) : v ∈ sets N := Set.mem_iInter.mp hv N
  have omegaV : OperationOmega v.1 v.2.2 := ⟨v.2.1,(all 0).1⟩
  have compatible (j : ℕ) : ClosedExpanded theta (r j) (v.2.2 j) :=
    (all (j+1)).2.1 j (by omega)
  have finiteV := Reg.Support.FibonacciFiniteSource.compatible_finite
    o theta htheta.le alpha r record finite v.1 v.2.2 omegaV compatible
  obtain ⟨x,omegaX,error,bound,observedX⟩ := record
  have compatibleX (j : ℕ) : ClosedExpanded theta (r j) (x j) := by
    by_cases ht : 0 ≤ theta
    · have hs := omegaX.choose_spec.2.2.1 j
      have hs0 : InSupport .G0 (x j) := by
        refine ⟨hs.1,hs.2.trans ?_⟩
        cases omegaX.choose j <;> simp only [supportUpper]
        · exact le_refl _
        · dsimp [phi]; linarith
      have owned := (owned_color_error o theta (r j) (x j) hs0).mpr
        ⟨error j,bound j,observedX j⟩
      have interval := (owned_color_interval o theta ht (r j) (x j)).mp owned
      exact ⟨interval.1,interval.2.1,interval.2.2.1⟩
    · have hb := bound j
      exact False.elim (ht ((abs_nonneg _).trans hb))
  have same := Reg.Support.FibonacciBranchSeparation.finite_compatible_unique_below
    theta htheta alpha v.1 x v.2.2 omegaX omegaV finite finiteV r compatibleX compatible
  obtain ⟨j,different⟩ := (all 0).2.2
  exact different (congrFun same j).symm

theorem liveness_below (o : Ownership) (theta : ℝ) (hzero : 0 ≤ theta)
    (htheta : theta < lam) :
    ∀ alpha r, OperationRecord o theta .closed alpha r → OperationFiniteSource alpha → ∀ p,
      ∃ t, _root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.Run (action theta)
        (_root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace.full r)
        ⟨initial,0,[]⟩ t ∧ p < t.output.length :=
  liveness_of_isolation o theta hzero (isolation_below o theta htheta)

#print axioms isolation_below
#print axioms liveness_below
end
end Reg.Support.FibonacciFiniteIsolation
