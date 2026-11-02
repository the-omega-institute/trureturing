/- GID: D5/S1/Dynamics/Shadowing/FreeFibreBoundary
   generality: G
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Marked finite observations of shadowing systems have exact finite-initial graph languages. -/

import D5.S1.Dynamics.Shadowing.FiniteObservationSofic
import Mathlib.Topology.Baire.LocallyCompactRegular

open TopologicalSpace Set Function

namespace D5.S1.Dynamics.Shadowing.FreeFibreBoundary

universe u v w

abbrev BinaryName := ℕ → Bool

/- A Baire-category form of the generic-point step.  It is stated for an
arbitrary countable closed family so that the later finite-graph coding can
consume it without baking coding choices into this topological lemma. -/
theorem exists_binary_name_locally_deciding
    {ι : Type*} [Countable ι] (C : ι → Set BinaryName)
    (hC : ∀ i, IsClosed (C i)) :
    ∃ a : BinaryName, ∀ i, ∃ U : Set BinaryName,
      IsOpen U ∧ a ∈ U ∧ (U ⊆ C i ∨ U ⊆ (C i)ᶜ) := by
  let F : ι → Set BinaryName := fun i => frontier (C i)
  have hFclosed : ∀ i, IsClosed (F i) := fun i => isClosed_frontier
  have hFnd : ∀ i, IsNowhereDense (F i) := by
    intro i
    rw [IsNowhereDense, isClosed_frontier.closure_eq]
    exact interior_frontier (hC i)
  have hopen : ∀ i, IsOpen (F i)ᶜ := fun i => (hFclosed i).isOpen_compl
  have hdense : ∀ i, Dense (F i)ᶜ := by
    intro i
    apply interior_eq_empty_iff_dense_compl.mp
    exact (IsClosed.isNowhereDense_iff (hFclosed i)).mp (hFnd i)
  have hres : Dense (⋂ i, (F i)ᶜ) := dense_iInter_of_isOpen hopen hdense
  obtain ⟨a, ha⟩ := hres.nonempty
  refine ⟨a, fun i => ?_⟩
  have hai : a ∉ frontier (C i) := by
    exact mem_iInter.mp ha i
  have hsplit : a ∈ interior (C i) ∪ interior (C i)ᶜ := by
    rw [← compl_frontier_eq_union_interior]
    exact hai
  rcases hsplit with h | h
  · exact ⟨interior (C i), isOpen_interior, h, Or.inl interior_subset⟩
  · exact ⟨interior (C i)ᶜ, isOpen_interior, h, Or.inr interior_subset⟩

/- A finite graph language with an explicitly restricted set of initial
vertices.  The initial restriction is essential for the transient marker in
the generic-shift construction. -/
def initialGraphLanguage {V : Type u} {A : Type v}
    (edge : V → V → Prop) (label : V → A) (initial : Set V) : Set (ℕ → A) :=
  {word | ∃ path : ℕ → V, path 0 ∈ initial ∧
    (∀ n, edge (path n) (path (n + 1))) ∧
    ∀ n, label (path n) = word n}

def HasFiniteInitialPresentation {A : Type u} (S : Set (ℕ → A)) : Prop :=
  ∃ (n : ℕ) (edge : Fin n → Fin n → Prop)
    (label : Fin n → A) (initial : Set (Fin n)),
    S = initialGraphLanguage edge label initial

/- Restricting the initial marker in the complete joint graph language gives
an exact presentation.  No surjectivity or invariance of the dynamics is
used, and the zeroth coordinate is retained. -/
theorem finite_initial_marked_names
    {Y : Type u} [TopologicalSpace Y]
    {A : Type v} [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    {B : Type w} [TopologicalSpace B] [DiscreteTopology B] [Finite B]
    (T : Y → Y) (a : Y → A) (ha : Continuous a)
    (mark : Y → B) (hmark : Continuous mark) (b₀ : B)
    (hs : HasShadowing T) :
    HasFiniteInitialPresentation
      (range (fun y : {y : Y // mark y = b₀} =>
        fun n => a (T^[n] y.val))) := by
  classical
  let obs : Y → A × B := fun y => (a y, mark y)
  have hobs : Continuous obs := ha.prodMk hmark
  obtain ⟨m, edge, label, hlang⟩ :=
    finite_observation_isSofic T obs hobs hs
  refine ⟨m, edge, (fun v => (label v).1),
    {v | (label v).2 = b₀}, ?_⟩
  ext word
  constructor
  · rintro ⟨y, rfl⟩
    have hw : (fun n => obs (T^[n] y.val)) ∈
        range (fun z n => obs (T^[n] z)) := ⟨y.val, rfl⟩
    rw [hlang] at hw
    obtain ⟨path, hpath, hlabel⟩ := hw
    refine ⟨path, ?_, hpath, ?_⟩
    · change (label (path 0)).2 = b₀
      have h₀ := congrArg Prod.snd (hlabel 0)
      change (label (path 0)).2 = mark y.val at h₀
      exact h₀.trans y.property
    · intro n
      exact congrArg Prod.fst (hlabel n)
  · rintro ⟨path, hinitial, hpath, hlabel⟩
    let joint : ℕ → A × B := fun n => label (path n)
    have hw : joint ∈ graphLanguage edge label :=
      ⟨path, hpath, fun _ => rfl⟩
    rw [← hlang] at hw
    obtain ⟨y, hy⟩ := hw
    have hy₀ : mark y = b₀ := by
      have h₀ := congrArg (fun s : ℕ → A × B => (s 0).2) hy
      change mark y = (label (path 0)).2 at h₀
      exact h₀.trans hinitial
    refine ⟨⟨y, hy₀⟩, funext fun n => ?_⟩
    have hn := congrArg (fun s : ℕ → A × B => (s n).1) hy
    change a (T^[n] y) = (label (path n)).1 at hn
    exact hn.trans (hlabel n)

end D5.S1.Dynamics.Shadowing.FreeFibreBoundary

