/- GID: D5/S1/Dynamics/Shadowing/FreeFibreBoundary
   generality: G
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Marked finite observations of shadowing systems have exact finite-initial graph languages. -/

import D5.S1.Dynamics.Shadowing.FiniteObservationSofic
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactification.OnePoint.Basic

/-! Marked finite observations, generic binary names, and the first-disagreement
map used by the free-fibre boundary construction. -/

open TopologicalSpace Set Function

namespace D5.S1.Dynamics.Shadowing.FreeFibreBoundary

noncomputable section
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

def boolInitialGraphLanguage {V : Type u} {A : Type v}
    (edge : V → V → Bool) (label : V → A) (initial : Set V) : Set (ℕ → A) :=
  initialGraphLanguage (fun x y => edge x y = true) label initial

/- Complete paths of a finite graph form a closed subset of the compact path
space.  Their continuous label image is therefore closed in the binary name
space. -/
theorem initialGraphLanguage_isClosed
    {V : Type u} {A : Type v} [TopologicalSpace V] [DiscreteTopology V]
    [Finite V] [TopologicalSpace A] [T2Space A]
    (edge : V → V → Bool) (label : V → A) (initial : Set V) :
    IsClosed (boolInitialGraphLanguage edge label initial) := by
  let paths : Set (ℕ → V) :=
    {p | p 0 ∈ initial ∧ ∀ n, edge (p n) (p (n + 1)) = true}
  have hpaths : IsClosed paths := by
    have hEq : paths = ({p : ℕ → V | p 0 ∈ initial} ∩
        ⋂ n : ℕ, {p : ℕ → V | edge (p n) (p (n + 1)) = true}) := by
      ext p
      simp [paths]
    rw [hEq]
    apply IsClosed.inter
    · exact (isClosed_discrete initial).preimage (continuous_apply 0)
    · apply isClosed_iInter
      intro n
      have hpair : Continuous (fun p : ℕ → V => (p n, p (n + 1))) :=
        (continuous_apply n).prodMk (continuous_apply (n + 1))
      have hedge : Continuous (fun p : ℕ → V => edge (p n) (p (n + 1))) :=
        (continuous_of_discreteTopology :
          Continuous (fun q : V × V => edge q.1 q.2)).comp hpair
      exact (isClosed_discrete {true}).preimage hedge
  let P := {p : ℕ → V // p ∈ paths}
  letI : CompactSpace P := hpaths.isClosedEmbedding_subtypeVal.compactSpace
  have hname : Continuous (fun p : P => fun n => label (p.val n)) := by
    exact continuous_pi fun n =>
      (continuous_of_discreteTopology : Continuous label).comp
        ((continuous_apply n).comp continuous_subtype_val)
  have hrange : boolInitialGraphLanguage edge label initial =
      Set.range (fun p : P => fun n => label (p.val n)) := by
    ext word
    constructor
    · rintro ⟨p, hp0, hpath, hlabel⟩
      exact ⟨⟨p, ⟨hp0, hpath⟩⟩, funext hlabel⟩
    · rintro ⟨p, rfl⟩
      exact ⟨p.val, p.property.1, p.property.2, fun n => rfl⟩
  have hclosedRange : IsClosed (Set.range (fun p : P => fun n => label (p.val n))) :=
    (isCompact_range hname).isClosed
  rw [← hrange] at hclosedRange
  simpa only [boolInitialGraphLanguage] using hclosedRange

/- A countable code for all finite binary-labelled graphs with an arbitrary
initial vertex set.  The two Bool-valued relations avoid any hidden
countability assumption on clopen subsets of a later hypothetical cover. -/
abbrev FiniteGraphCode :=
  Σ n : ℕ, (Fin n → Fin n → Bool) × (Fin n → Bool) × (Fin n → Bool)

def finiteGraphLanguage (c : FiniteGraphCode) : Set BinaryName :=
  boolInitialGraphLanguage c.2.1 c.2.2.1 {v | c.2.2.2 v = true}

theorem finiteGraphLanguage_isClosed (c : FiniteGraphCode) :
    IsClosed (finiteGraphLanguage c) := by
  exact initialGraphLanguage_isClosed c.2.1 c.2.2.1 {v | c.2.2.2 v = true}

theorem exists_generic_finite_graph_decision :
    ∃ a : BinaryName, ∀ c : FiniteGraphCode, ∃ U : Set BinaryName,
      IsOpen U ∧ a ∈ U ∧
        (U ⊆ finiteGraphLanguage c ∨ U ⊆ (finiteGraphLanguage c)ᶜ) := by
  simpa only [finiteGraphLanguage] using
    (exists_binary_name_locally_deciding finiteGraphLanguage finiteGraphLanguage_isClosed)

open scoped OnePoint

def firstDifferenceFiber (a : BinaryName) (n : ℕ) : Set BinaryName :=
  {s | (∀ k < n, s k = a k) ∧ s n ≠ a n}

noncomputable def firstDifference (a s : BinaryName) : OnePoint ℕ :=
  by
    classical
    exact if h : ∃ n, s n ≠ a n then (Nat.find h : OnePoint ℕ) else ∞

theorem firstDifference_eq_coe_iff (a s : BinaryName) (n : ℕ) :
    firstDifference a s = (n : OnePoint ℕ) ↔ s ∈ firstDifferenceFiber a n := by
  constructor
  · intro h
    by_cases hd : ∃ k, s k ≠ a k
    · have hfind : Nat.find hd = n := by
        apply OnePoint.coe_injective
        simpa [firstDifference, hd] using h
      have hf := (Nat.find_eq_iff hd).mp hfind
      refine ⟨?_, hf.1⟩
      intro k hk
      by_contra hne
      exact hf.2 k hk hne
    · simp [firstDifference, hd] at h
  · intro hs
    change (∀ k < n, s k = a k) ∧ s n ≠ a n at hs
    have hd : ∃ k, s k ≠ a k := ⟨n, hs.2⟩
    have hfind : Nat.find hd = n := by
      apply (Nat.find_eq_iff hd).mpr
      exact ⟨hs.2, fun k hk hne => hne (hs.1 k hk)⟩
    simp [firstDifference, hd, hfind]

theorem firstDifference_eq_infty_iff (a s : BinaryName) :
    firstDifference a s = ∞ ↔ s = a := by
  by_cases h : s = a
  · subst h
    simp [firstDifference]
  · have hd : ∃ n, s n ≠ a n := by
      by_contra hn
      apply h
      funext n
      by_contra hne
      exact hn ⟨n, hne⟩
    simp [firstDifference, hd, h]

theorem firstDifferenceFiber_isClopen (a : BinaryName) (n : ℕ) :
    IsClopen (firstDifferenceFiber a n) := by
  let pref : Set BinaryName := ⋂ k : Fin n, {s | s k.val = a k.val}
  have hprefix : IsClopen pref := by
    have hcoord (k : Fin n) : IsClopen {s : BinaryName | s k.val = a k.val} :=
      by
        have hc : IsClosed {s : BinaryName | s k.val = a k.val} := by
          change IsClosed ((fun s : BinaryName => s k.val) ⁻¹' {a k.val})
          exact (isClosed_discrete _).preimage (continuous_apply k.val)
        have ho : IsOpen {s : BinaryName | s k.val = a k.val} := by
          change IsOpen ((fun s : BinaryName => s k.val) ⁻¹' {a k.val})
          exact (isOpen_discrete _).preimage (continuous_apply k.val)
        exact ⟨hc, ho⟩
    refine ⟨?_, ?_⟩
    · exact isClosed_iInter fun k => (hcoord k).1
    · exact isOpen_iInter_of_finite fun k => (hcoord k).2
  have hlast : IsClopen {s : BinaryName | s n ≠ a n} := by
    change IsClopen ({s : BinaryName | s n = a n} : Set BinaryName)ᶜ
    have hcoord : IsClopen {s : BinaryName | s n = a n} :=
      by
        have hc : IsClosed {s : BinaryName | s n = a n} := by
          change IsClosed ((fun s : BinaryName => s n) ⁻¹' {a n})
          exact (isClosed_discrete _).preimage (continuous_apply n)
        have ho : IsOpen {s : BinaryName | s n = a n} := by
          change IsOpen ((fun s : BinaryName => s n) ⁻¹' {a n})
          exact (isOpen_discrete _).preimage (continuous_apply n)
        exact ⟨hc, ho⟩
    exact hcoord.compl
  have hEq : firstDifferenceFiber a n = pref ∩ {s : BinaryName | s n ≠ a n} := by
    ext s
    constructor
    · intro hs
      refine ⟨mem_iInter.mpr fun k => hs.1 k.val k.isLt, hs.2⟩
    · rintro ⟨hs, hsn⟩
      refine ⟨?_, hsn⟩
      intro k hk
      exact mem_iInter.mp hs ⟨k, hk⟩
  rw [hEq]
  exact hprefix.inter hlast

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

end
end D5.S1.Dynamics.Shadowing.FreeFibreBoundary

