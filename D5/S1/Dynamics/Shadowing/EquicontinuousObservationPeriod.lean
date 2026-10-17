/- GID: D5/S1/Dynamics/Shadowing/EquicontinuousObservationPeriod
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/EquicontinuousObservationPeriod
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Onto equicontinuous compact dynamics give positive discrete-observation periods. -/

import D5.S1.Dynamics.Shadowing.CompactObservationSubshift
import Mathlib.Topology.UniformSpace.Equicontinuity
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Instances.Discrete
import Mathlib.Dynamics.PeriodicPts.Lemmas

open TopologicalSpace Topology Set Function Filter UniformSpace
open scoped Uniformity

namespace D5.S1.Dynamics.Shadowing

/-- Equicontinuity gives one neighborhood on which every coordinate of an
observation name agrees. The observer needs only a discrete topology. -/
private theorem observation_name_is_locally_constant_of_equicontinuous
    {D A : Type*} [UniformSpace D] [CompactSpace D]
    [TopologicalSpace A] [DiscreteTopology A]
    (T : D → D) (q : D → A) (hq : Continuous q)
    (heq : Equicontinuous (fun n : ℕ => T^[n])) :
    IsLocallyConstant (fun x n => q (T^[n] x)) := by
  let E : Set (D × D) := {p | q p.1 = q p.2}
  have hpair : Continuous (fun p : D × D => (q p.1, q p.2)) :=
    (hq.comp continuous_fst).prodMk (hq.comp continuous_snd)
  have hEopen : IsOpen E :=
    (isOpen_discrete {p : A × A | p.1 = p.2}).preimage hpair
  have hE : E ∈ 𝓤 D := by
    rw [← nhdsSet_diagonal_eq_uniformity]
    apply hEopen.mem_nhdsSet.mpr
    rintro ⟨a, b⟩ hab
    change a = b at hab
    change q a = q b
    exact congrArg q hab
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  apply mem_of_superset (heq x E hE)
  intro y hy
  funext n
  exact (show q (T^[n] x) = q (T^[n] y) from hy n).symm

/-- An onto self-map with equicontinuous forward iterates on a compact uniform
space has a positive period for every continuous discrete observation.

In particular this applies to any finite discrete observer, without any
zero-dimensionality, metric, countability, nonemptiness or injectivity
assumption on the source. The period depends on the observer.

The statement also allows an infinite discrete codomain: local constancy and
compactness make the image of the complete-name map finite. No uniform
structure on the observer codomain is assumed. A separate continuity
hypothesis on `T` is redundant, since `heq.continuous 1` supplies it. -/
theorem finite_observation_period_of_equicontinuous_surjective
    {D A : Type*} [UniformSpace D] [CompactSpace D]
    [TopologicalSpace A] [DiscreteTopology A]
    (T : D → D) (q : D → A) (hT : Surjective T) (hq : Continuous q)
    (heq : Equicontinuous (fun n : ℕ => T^[n])) :
    ∃ M : ℕ, 0 < M ∧ ∀ x : D, q (T^[M] x) = q x := by
  classical
  let W : D → ℕ → A := fun x n => q (T^[n] x)
  have hW : IsLocallyConstant W :=
    observation_name_is_locally_constant_of_equicontinuous T q hq heq
  let S : Set (ℕ → A) := Set.range W
  have hS : S.Finite := hW.range_finite
  let : Fintype S := hS.fintype
  let name : D → S := fun x => ⟨W x, ⟨x, rfl⟩⟩
  let shift : S → S := fun w =>
    ⟨(fun n => w.val (n + 1)), observationLanguage_shift_invariant T q w.property⟩
  have hsem : Semiconj name T shift := by
    intro x
    apply Subtype.ext
    funext n
    change q (T^[n] (T x)) = q (T^[n + 1] x)
    rw [Function.iterate_succ_apply]
  have hshift_surjective : Surjective shift := by
    intro w
    obtain ⟨x, hx⟩ := w.property
    obtain ⟨y, hy⟩ := hT x
    refine ⟨name y, ?_⟩
    apply Subtype.ext
    funext n
    change q (T^[n + 1] y) = w.val n
    rw [Function.iterate_succ_apply, hy]
    exact congrFun hx n
  have hshift_injective : Injective shift :=
    Finite.injective_iff_surjective.mpr hshift_surjective
  let M : ℕ := Nat.factorial (Fintype.card S)
  have hM : 0 < M := Nat.factorial_pos _
  have hperiod : shift^[M] = id :=
    Function.injective_iff_iterate_factorial_card_eq_id.mp hshift_injective
  refine ⟨M, hM, ?_⟩
  intro x
  have hname : name (T^[M] x) = name x := by
    calc
      name (T^[M] x) = shift^[M] (name x) := hsem.iterate_right M x
      _ = name x := congrFun hperiod (name x)
  have hzero := congrArg (fun w : S => w.val 0) hname
  simpa only [name, W, Function.iterate_zero_apply] using hzero

#print axioms finite_observation_period_of_equicontinuous_surjective

end D5.S1.Dynamics.Shadowing
