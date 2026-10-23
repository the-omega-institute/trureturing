/- GID: D5/S1/Dynamics/Shadowing/FiniteObservationSofic
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/FiniteObservationSofic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite continuous observations of shadowing sources have exact sofic histories. -/

import D5.S1.Dynamics.Shadowing.MittagLefflerInverseLimit
import Mathlib.Topology.Instances.Discrete
import Mathlib.Data.Fintype.EquivFin

/- The graph witness uses the source's finite error cover crossed with its
observation alphabet. An edge has one actual source witness. A whole graph
path yields a whole pseudo-orbit, not merely compatible finite prefixes.
No compactness, separation, or surjectivity hypothesis is required beyond
the existing finite-open-cover definition of HasShadowing.

Library reuse: the source history is the definitional expansion of the existing
completeItinerary map. The mathematical S1 module does not import that S3 owner;
the retained Reg mirror imports it explicitly and checks the same statement
by definitional equality.
Pinned Mathlib supplies finite discrete fibers and finite carrier equivalences;
its SymbolicDynamics.Basic does not provide the exact sofic graph statement.
Public Loogle name searches found no "sofic" declaration; its six "shadowing"
hits concern Lean compiler name shadowing, not dynamics. Loogle indexes only
Lean and Mathlib, so this is not an exhaustive third-party ecosystem search.
The result is an implementation of the ordinary finite-observation graph
mechanism, with no originality or Peng Q5.1/Q5.2 resolution claim.
All declarations have utility kind none: this is a general graph construction,
not a finite computational instance, checker, enumeration, or numeric reduction. -/

open TopologicalSpace Set Function

namespace D5.S1.Dynamics.Shadowing

universe u v w

/-- The label language of all complete forward graph paths. Every vertex is
allowed at time zero; transient vertices need no predecessor. -/
def graphLanguage {V : Type u} {A : Type v} (edge : V → V → Prop)
    (label : V → A) : Set (ℕ → A) :=
  {word | ∃ path : ℕ → V,
    (∀ n, edge (path n) (path (n + 1))) ∧ ∀ n, label (path n) = word n}

/-- A one-sided language presented by one finite vertex-labelled graph.
The empty graph is permitted and has empty complete-path language. -/
def IsSofic {A : Type u} (S : Set (ℕ → A)) : Prop :=
  ∃ (n : ℕ) (edge : Fin n → Fin n → Prop) (label : Fin n → A),
    S = graphLanguage edge label

private theorem sofic_of_finite_graph {V : Type u} [Finite V] {A : Type v}
    (edge : V → V → Prop) (label : V → A) : IsSofic (graphLanguage edge label) := by
  classical
  letI := Fintype.ofFinite V
  let e := Fintype.equivFin V
  refine ⟨Fintype.card V, (fun i j => edge (e.symm i) (e.symm j)),
    (fun i => label (e.symm i)), ?_⟩
  ext word
  constructor
  · rintro ⟨path, hp, hl⟩
    refine ⟨fun n => e (path n), ?_, ?_⟩
    · simpa using hp
    · simpa using hl
  · rintro ⟨path, hp, hl⟩
    exact ⟨fun n => e.symm (path n), hp, hl⟩

/-- The complete image of a continuous finite discrete observation of any
finite-cover shadowing source is an entire finite graph language. The statement
includes empty sources and time zero, and does not require onto dynamics. -/
theorem finite_observation_isSofic {X : Type u} [TopologicalSpace X]
    {A : Type v} [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    (f : X → X) (a : X → A) (ha : Continuous a) (hs : HasShadowing f) :
    IsSofic (Set.range (fun x n => a (f^[n] x))) := by
  classical
  letI := Fintype.ofFinite A
  let fiber : A → Opens X := fun c => ⟨a ⁻¹' {c}, (isOpen_discrete _).preimage ha⟩
  let C : Finset (Opens X) := Finset.univ.image fiber
  have hC : IsOpenCover (fun U : C => U.1) := by
    rw [IsOpenCover, eq_top_iff]
    intro x _
    refine Opens.mem_iSup.mpr ⟨⟨fiber (a x), ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨a x, Finset.mem_univ _, rfl⟩
    · exact rfl
  obtain ⟨D, hD, htrace⟩ := hs C hC
  let V := D × A
  let edge : V → V → Prop := fun i j =>
    ∃ x : X, x ∈ i.1.1 ∧ a x = i.2 ∧ f x ∈ j.1.1 ∧ a (f x) = j.2
  let label : V → A := fun i => i.2
  have heq : Set.range (fun x n => a (f^[n] x)) = graphLanguage edge label := by
    ext word
    constructor
    · rintro ⟨x, rfl⟩
      have hcover : ∀ n : ℕ, ∃ U : D, (f^[n] x) ∈ U.1 :=
        fun n => hD.exists_mem (f^[n] x)
      choose U hU using hcover
      refine ⟨fun n => (U n, a (f^[n] x)), ?_, fun _ => rfl⟩
      intro n
      refine ⟨f^[n] x, hU n, rfl, ?_, ?_⟩
      · simpa only [iterate_succ_apply'] using hU (n + 1)
      · simp only [iterate_succ_apply']
    · rintro ⟨path, hp, hl⟩
      choose x hx ha' hfx hafx using hp
      have hpo : PseudoOrbit f D x := by
        intro n
        exact ⟨(path (n + 1)).1.1, (path (n + 1)).1.2, hfx n, hx (n + 1)⟩
      obtain ⟨z, hz⟩ := htrace x hpo
      refine ⟨z, funext fun n => ?_⟩
      obtain ⟨U, hUC, hzn, hxn⟩ := hz n
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hUC
      change a (f^[n] z) = c at hzn
      change a (x n) = c at hxn
      change a (f^[n] z) = word n
      exact hzn.trans (hxn.symm.trans ((ha' n).trans (hl n)))
  rw [heq]
  exact sofic_of_finite_graph edge label

#print axioms finite_observation_isSofic

end D5.S1.Dynamics.Shadowing
