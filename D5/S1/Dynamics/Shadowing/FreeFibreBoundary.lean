/- GID: D5/S1/Dynamics/Shadowing/FreeFibreBoundary
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/FreeFibreBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Dynamics/Shadowing/FreeFibreBoundary.claim; result=D5/S1/Dynamics/Shadowing/FreeFibreBoundary.result; claim=D5/S1/Dynamics/Shadowing/FreeFibreBoundary.claim
   digest: A compact Hausdorff shadowing system admits no zero-dimensional compact Hausdorff shadowing cover. -/

import D5.S1.Dynamics.Shadowing.FiniteObservationSofic
import D5.S1.Dynamics.Shadowing.MetricTracing
import D5.S3.Topology.AlmostDisjoint.AdaptiveRefinementCounterexample
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.ShrinkingLemma
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Topology.UniformSpace.OfCompactT2

/-! Marked finite observations, generic binary names, and the first-disagreement
map used by the free-fibre boundary construction. -/

open TopologicalSpace Set Function Filter UniformSpace
open scoped Topology Uniformity SetRel
open D5.S3.Topology.AlmostDisjoint.AdaptiveRefinementCounterexample
open D5.S3.Topology.AlmostDisjoint.TaggedCompactSpace
open D5.S3.Topology.AlmostDisjoint.ConvergentBranches
open D5.S3.Topology.AlmostDisjoint.BranchLabeledMaximalFamily

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

/- The first-disagreement map is continuous.  Away from the distinguished
point it is locally constant on a clopen fibre; at the distinguished point,
the compact sets occurring in the one-point neighbourhood basis meet only
finitely many such fibres. -/
theorem continuous_firstDifference (a : BinaryName) :
    Continuous (firstDifference a) := by
  rw [continuous_iff_continuousAt]
  intro s
  rw [continuousAt_def]
  intro V hV
  by_cases hsa : s = a
  · subst s
    have haInf : firstDifference a a = ∞ :=
      (firstDifference_eq_infty_iff a a).2 rfl
    have hVInf : V ∈ 𝓝 (∞ : OnePoint ℕ) := by simpa [haInf] using hV
    obtain ⟨O, hOV, hO, hInfO⟩ := mem_nhds_iff.mp hVInf
    have hObasis : O ∈ 𝓝 (∞ : OnePoint ℕ) :=
      mem_nhds_iff.mpr ⟨O, subset_rfl, hO, hInfO⟩
    obtain ⟨K, ⟨hKclosed, hKcompact⟩, hKsub⟩ :=
      (OnePoint.hasBasis_nhds_infty (X := ℕ)).mem_iff.mp hObasis
    let F : Set BinaryName := ⋃ n ∈ K, firstDifferenceFiber a n
    have hKfinite : K.Finite := hKcompact.finite_of_discrete
    have hFcompact : IsCompact F := by
      exact hKfinite.isCompact_biUnion fun n hn =>
        (firstDifferenceFiber_isClopen a n).1.isCompact
    have hFclosed : IsClosed F := hFcompact.isClosed
    have haF : a ∉ F := by
      intro haF'
      rcases mem_iUnion₂.mp haF' with ⟨n, hnK, han⟩
      exact han.2 rfl
    have hFopen : IsOpen Fᶜ := hFclosed.isOpen_compl
    have haFopen : Fᶜ ∈ 𝓝 a := hFopen.mem_nhds (show a ∈ Fᶜ from haF)
    apply Filter.mem_of_superset haFopen
    intro t ht
    by_cases hta : t = a
    · subst t
      change firstDifference a a ∈ V
      rw [haInf]
      exact hOV (hKsub (mem_union_right _ (by simp)))
    · have hd : ∃ n, t n ≠ a n := by
        by_contra hnone
        apply hta
        funext n
        by_contra hne
        exact hnone ⟨n, hne⟩
      let n := Nat.find hd
      have hval : firstDifference a t = (n : OnePoint ℕ) := by
        simp [firstDifference, n, hd]
      have hnK : n ∉ K := by
        intro hnK
        apply ht
        exact mem_iUnion₂.mpr
          ⟨n, hnK, (firstDifference_eq_coe_iff a t n).mp hval⟩
      change firstDifference a t ∈ V
      rw [hval]
      exact hOV (hKsub (mem_union_left _ ⟨n, hnK, rfl⟩))
  · have hd : ∃ n, s n ≠ a n := by
      by_contra hnone
      apply hsa
      funext n
      by_contra hne
      exact hnone ⟨n, hne⟩
    let n := Nat.find hd
    have hval : firstDifference a s = (n : OnePoint ℕ) := by
      simp [firstDifference, n, hd]
    rcases mem_nhds_iff.mp hV with ⟨O, hOV, hO, hxO⟩
    have hnO : (n : OnePoint ℕ) ∈ O := by simpa [hval] using hxO
    have hsingleton : IsOpen ({(n : OnePoint ℕ)} : Set (OnePoint ℕ)) := by
      simpa using
        (OnePoint.isOpen_image_coe (s := ({n} : Set ℕ))).2 (isOpen_discrete _)
    have hsingletonV : ({(n : OnePoint ℕ)} : Set (OnePoint ℕ)) ⊆ V := by
      intro z hz
      have hz' : z = (n : OnePoint ℕ) := by simpa using hz
      subst z
      exact hOV hnO
    have hpre : (firstDifference a) ⁻¹' ({(n : OnePoint ℕ)} : Set (OnePoint ℕ)) =
        firstDifferenceFiber a n := by
      ext t
      change firstDifference a t = (n : OnePoint ℕ) ↔ _
      exact firstDifference_eq_coe_iff a t n
    apply Filter.mem_of_superset
      (hpre ▸ (firstDifferenceFiber_isClopen a n).2.mem_nhds
        ((firstDifference_eq_coe_iff a s n).mp hval))
    exact preimage_mono hsingletonV

def flipBit (b : Bool) : Bool := if b then false else true

theorem flipBit_ne (b : Bool) : flipBit b ≠ b := by
  cases b <;> simp [flipBit]

def convergentSectionName (a : BinaryName) (n : ℕ) : BinaryName :=
  fun k => if k = n then flipBit (a k) else a k

theorem convergentSectionName_mem_fiber (a : BinaryName) (n : ℕ) :
    convergentSectionName a n ∈ firstDifferenceFiber a n := by
  constructor
  · intro k hk
    simp [convergentSectionName, Nat.ne_of_lt hk]
  · simp [convergentSectionName, flipBit_ne]

theorem convergentSectionName_firstDifference (a : BinaryName) (n : ℕ) :
    firstDifference a (convergentSectionName a n) = (n : OnePoint ℕ) :=
  (firstDifference_eq_coe_iff a (convergentSectionName a n) n).2
    (convergentSectionName_mem_fiber a n)

theorem convergentSectionName_tendsto (a : BinaryName) :
    Filter.Tendsto (convergentSectionName a) atTop (𝓝 a) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply Filter.tendsto_def.mpr
  intro V hV
  have hai : a i ∈ V := mem_of_mem_nhds hV
  filter_upwards [eventually_gt_atTop i] with n hin
  have hne : i ≠ n := Nat.ne_of_lt hin
  simpa [convergentSectionName, hne] using hai

def convergentSectionSet (a : BinaryName) : Set BinaryName :=
  insert a (range (convergentSectionName a))

theorem convergentSectionSet_isCompact (a : BinaryName) :
    IsCompact (convergentSectionSet a) := by
  exact (convergentSectionName_tendsto a).isCompact_insert_range

theorem convergentSectionSet_mem_or_eq (a : BinaryName) (s : BinaryName)
    (hs : s ∈ convergentSectionSet a) :
    s = a ∨ ∃ n, s = convergentSectionName a n := by
  have hs' : s = a ∨ s ∈ range (convergentSectionName a) := by
    simpa [convergentSectionSet, mem_insert_iff] using hs
  rcases hs' with hs' | ⟨n, hn⟩
  · exact Or.inl hs'
  · exact Or.inr ⟨n, hn.symm⟩

theorem convergentSectionSet_firstDifference_finite (a : BinaryName) (s : BinaryName)
    (hs : s ∈ convergentSectionSet a) (hsa : s ≠ a) :
    ∃ n : ℕ, firstDifference a s = (n : OnePoint ℕ) := by
  rcases (convergentSectionSet_mem_or_eq a s hs) with rfl | ⟨n, rfl⟩
  · exact False.elim (hsa rfl)
  · exact ⟨n, convergentSectionName_firstDifference a n⟩

def firstDifferenceOnSection (a : BinaryName) :
    convergentSectionSet a → OnePoint ℕ := fun s => firstDifference a s.val

theorem firstDifferenceOnSection_bijective (a : BinaryName) :
    Function.Bijective (firstDifferenceOnSection a) := by
  have hfinite_unique : ∀ (n : ℕ) (s : convergentSectionSet a),
      firstDifferenceOnSection a s = (n : OnePoint ℕ) →
        s = ⟨convergentSectionName a n,
          Or.inr ⟨n, rfl⟩⟩ := by
    intro n s hs
    rcases convergentSectionSet_mem_or_eq a s.val s.property with hsa | ⟨m, hsm⟩
    · exfalso
      have hInf : firstDifference a s.val = ∞ :=
        (firstDifference_eq_infty_iff a s.val).2 hsa
      apply OnePoint.infty_ne_coe n
      calc
        (∞ : OnePoint ℕ) = firstDifference a s.val := hInf.symm
        _ = (n : OnePoint ℕ) := hs
    · have hmn : (m : OnePoint ℕ) = (n : OnePoint ℕ) := by
        calc
          (m : OnePoint ℕ) = firstDifference a (convergentSectionName a m) :=
            (convergentSectionName_firstDifference a m).symm
          _ = firstDifference a s.val := by rw [hsm]
          _ = (n : OnePoint ℕ) := hs
      have hmn' : m = n := OnePoint.coe_injective hmn
      apply Subtype.ext
      rw [hsm, hmn']
  constructor
  · intro s t hst
    cases hfs : firstDifferenceOnSection a s using OnePoint.rec with
    | infty =>
        have hsA : s.val = a :=
          (firstDifference_eq_infty_iff a s.val).1 hfs
        have htA : t.val = a := by
          apply (firstDifference_eq_infty_iff a t.val).1
          calc
            firstDifference a t.val = firstDifferenceOnSection a t := rfl
            _ = firstDifferenceOnSection a s := hst.symm
            _ = ∞ := hfs
        exact Subtype.ext (hsA.trans htA.symm)
    | coe n =>
        have hft : firstDifferenceOnSection a t = (n : OnePoint ℕ) := by
          calc
            firstDifferenceOnSection a t = firstDifferenceOnSection a s := hst.symm
            _ = (n : OnePoint ℕ) := hfs
        exact (hfinite_unique n s hfs).trans (hfinite_unique n t hft).symm
  · intro z
    cases z using OnePoint.rec with
    | infty =>
        refine ⟨⟨a, Or.inl rfl⟩, ?_⟩
        exact (firstDifference_eq_infty_iff a a).2 rfl
    | coe n =>
        refine ⟨⟨convergentSectionName a n, Or.inr ⟨n, rfl⟩⟩, ?_⟩
        exact convergentSectionName_firstDifference a n

theorem exists_firstDifference_section_homeomorph (a : BinaryName) :
    ∃ e : convergentSectionSet a ≃ₜ OnePoint ℕ,
      ∀ s, e s = firstDifferenceOnSection a s := by
  letI : CompactSpace (convergentSectionSet a) :=
    (convergentSectionSet_isCompact a).isClosed.isClosedEmbedding_subtypeVal.compactSpace
  let g : convergentSectionSet a → OnePoint ℕ := firstDifferenceOnSection a
  have hg : Continuous g := by
    change Continuous (firstDifference a ∘ Subtype.val)
    exact (continuous_firstDifference a).comp continuous_subtype_val
  have hgc : IsClosedMap g := hg.isClosedMap
  let e : convergentSectionSet a ≃ OnePoint ℕ :=
    Equiv.ofBijective g (firstDifferenceOnSection_bijective a)
  exact ⟨e.toHomeomorphOfContinuousClosed hg hgc, fun s => rfl⟩

abbrev FibrePullback {T S B : Type*} (p : T → B) (rho : S → B) :=
  {z : T × S // p z.1 = rho z.2}

def fibrePullbackSecond {T S B : Type*} (p : T → B) (rho : S → B) :
    FibrePullback p rho → S := fun z => z.val.2

theorem fibrePullbackSecond_continuous {T S B : Type*}
    [TopologicalSpace T] [TopologicalSpace S] [TopologicalSpace B]
    (p : T → B) (rho : S → B) :
    Continuous (fibrePullbackSecond p rho) := by
  exact continuous_snd.comp continuous_subtype_val

theorem fibrePullbackSecond_surjective {T S B : Type*}
    [TopologicalSpace T] [TopologicalSpace S] [TopologicalSpace B]
    (p : T → B) (rho : S → B) (hp : Function.Surjective p) :
    Function.Surjective (fibrePullbackSecond p rho) := by
  intro s
  obtain ⟨t, ht⟩ := hp (rho s)
  exact ⟨⟨(t, s), ht⟩, rfl⟩

theorem fibrePullbackSecond_isOpenMap {T S B : Type*}
    [TopologicalSpace T] [TopologicalSpace S] [TopologicalSpace B]
    (p : T → B) (rho : S → B) (hp : IsOpenMap p) (hrho : Continuous rho) :
    IsOpenMap (fibrePullbackSecond p rho) := by
  apply IsOpenMap.of_nhds_le
  intro z
  apply le_map_iff.2
  intro N hN
  obtain ⟨u, hu, hsub⟩ :=
    (mem_nhds_subtype ({z : T × S | p z.1 = rho z.2}) z N).mp hN
  obtain ⟨A, hA, C, hC, hAC⟩ := mem_nhds_prod_iff.mp hu
  have hpa : p '' A ∈ 𝓝 (p z.val.1) := hp.image_mem_nhds hA
  have hpa' : p '' A ∈ 𝓝 (rho z.val.2) := by
    rw [← z.property]
    exact hpa
  have hpre : rho ⁻¹' (p '' A) ∈ 𝓝 z.val.2 :=
    hrho.continuousAt.preimage_mem_nhds hpa'
  apply Filter.mem_of_superset (inter_mem hC hpre)
  intro s hs
  rcases hs.2 with ⟨t, htA, hpt⟩
  let z' : FibrePullback p rho := ⟨(t, s), hpt⟩
  refine ⟨z', ?_, rfl⟩
  apply hsub
  exact hAC ⟨htA, hs.1⟩

theorem fibrePullback_isClosed {T S B : Type*}
    [TopologicalSpace T] [TopologicalSpace S] [TopologicalSpace B] [T2Space B]
    (p : T → B) (rho : S → B) (hp : Continuous p) (hrho : Continuous rho) :
    IsClosed {z : T × S | p z.1 = rho z.2} := by
  exact isClosed_eq (hp.comp continuous_fst) (hrho.comp continuous_snd)

theorem fibrePullback_compactSpace {T S B : Type*}
    [TopologicalSpace T] [TopologicalSpace S] [TopologicalSpace B] [T2Space B]
    [CompactSpace T] [CompactSpace S]
    (p : T → B) (rho : S → B) (hp : Continuous p) (hrho : Continuous rho) :
    CompactSpace (FibrePullback p rho) := by
  exact (fibrePullback_isClosed p rho hp hrho).isClosedEmbedding_subtypeVal.compactSpace

theorem fibrePullback_t2Space {T S B : Type*}
    [TopologicalSpace T] [TopologicalSpace S] [TopologicalSpace B]
    [T2Space B] [T2Space T] [T2Space S]
    (p : T → B) (rho : S → B) : T2Space (FibrePullback p rho) := by
  infer_instance

theorem firstDifference_surjective (a : BinaryName) :
    Function.Surjective (firstDifference a) := by
  obtain ⟨e, he⟩ := exists_firstDifference_section_homeomorph a
  intro b
  obtain ⟨s, hs⟩ := e.surjective b
  exact ⟨s.val, (he s).symm.trans hs⟩

abbrev CoreShift : BinaryName → BinaryName :=
  SymbolicDynamics.FullShift.shift (1 : ℕ)

abbrev FreeFibreSource {T : Type*} (p : T → OnePoint ℕ) (a : BinaryName) :=
  FibrePullback p (firstDifference a) ⊕ BinaryName

def sourceDynamics {T : Type*} (p : T → OnePoint ℕ) (a : BinaryName)
    (z : FibrePullback p (firstDifference a) ⊕ BinaryName) :
    FibrePullback p (firstDifference a) ⊕ BinaryName :=
  Sum.elim (fun z => Sum.inr z.val.2) (fun s => Sum.inr (CoreShift s)) z

def sourceObservation {T : Type*} (p : T → OnePoint ℕ) (a : BinaryName)
    (z : FibrePullback p (firstDifference a) ⊕ BinaryName) : BinaryName :=
  Sum.elim (fun z => z.val.2) CoreShift z

theorem sourceDynamics_continuous {T : Type*} [TopologicalSpace T]
    (p : T → OnePoint ℕ) (a : BinaryName) :
    Continuous (sourceDynamics p a) := by
  exact (continuous_inr.comp (continuous_snd.comp continuous_subtype_val)).sumElim
    (continuous_inr.comp (SymbolicDynamics.FullShift.continuous_shift 1))

theorem sourceObservation_continuous {T : Type*} [TopologicalSpace T]
    (p : T → OnePoint ℕ) (a : BinaryName)
    (hH : Continuous (fibrePullbackSecond p (firstDifference a))) :
    Continuous (sourceObservation p a) := by
  exact hH.sumElim (SymbolicDynamics.FullShift.continuous_shift 1)

theorem sourceDynamics_semiconj {T : Type*} (p : T → OnePoint ℕ) (a : BinaryName) :
    Semiconj (sourceObservation p a) (sourceDynamics p a) CoreShift := by
  intro z
  cases z <;> rfl

theorem sourceDynamics_core_image {T : Type*} (p : T → OnePoint ℕ) (a : BinaryName)
    (z : FibrePullback p (firstDifference a) ⊕ BinaryName) :
    sourceDynamics p a z = Sum.inr (sourceObservation p a z) := by
  cases z <;> rfl

theorem sourceObservation_surjective {T : Type*} (p : T → OnePoint ℕ) (a : BinaryName) :
    Function.Surjective (sourceObservation p a) := by
  intro s
  refine ⟨Sum.inr (fun n => if n = 0 then false else s (n - 1)), ?_⟩
  funext n
  cases n with
  | zero => rfl
  | succ n => simp [sourceObservation, CoreShift, SymbolicDynamics.FullShift.shift_apply]

def boolPrefixRel (k : ℕ) : SetRel BinaryName BinaryName :=
  {p | ∀ i < k, p.1 i = p.2 i}

theorem boolPrefixRel_mem (k : ℕ) : boolPrefixRel k ∈ 𝓤 BinaryName := by
  have hi (i : Fin k) : {p : BinaryName × BinaryName | p.1 i.val = p.2 i.val} ∈
      𝓤 BinaryName := by
    simpa only [Filter.mem_map, SetRel.id, Prod.map, Set.mem_ofPred_eq,
      Set.preimage_ofPred_eq] using
      (Pi.uniformContinuous_proj (fun _ : ℕ => Bool) i.val)
        (DiscreteUniformity.relId_mem_uniformity Bool)
  have h : (⋂ i : Fin k, {p : BinaryName × BinaryName | p.1 i.val = p.2 i.val}) ∈
      𝓤 BinaryName := Filter.iInter_mem.mpr hi
  apply Filter.mem_of_superset h
  intro p hp i hi
  exact Set.mem_iInter.mp hp ⟨i, hi⟩

theorem boolPrefixRel_cofinal (U : SetRel BinaryName BinaryName)
    (hU : U ∈ 𝓤 BinaryName) :
    ∃ k : ℕ, 0 < k ∧ boolPrefixRel k ⊆ U := by
  letI : MetricSpace BinaryName := PiNat.metricSpaceOfDiscreteUniformity
    (fun _ : ℕ => DiscreteUniformity.eq_principal_setRelId Bool)
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_uniformity_dist.mp hU
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨k + 1, by omega, ?_⟩
  intro p hp
  apply hεU
  have hdist : dist p.1 p.2 ≤ (1 / 2 : ℝ) ^ k :=
    PiNat.mem_cylinder_iff_dist_le.mp
      (show p.1 ∈ PiNat.cylinder p.2 k from fun i hi => hp i (by omega))
  exact hdist.trans_lt hk

theorem coreShift_uniformHasShadowing : UniformHasShadowing CoreShift := by
  intro E hE
  obtain ⟨k, hk, hEk⟩ := boolPrefixRel_cofinal E hE
  let D := boolPrefixRel (k + 1)
  have hD : D ∈ 𝓤 BinaryName := boolPrefixRel_mem (k + 1)
  refine ⟨D, hD, ?_⟩
  intro z hz
  refine ⟨diagonalSplice z, ?_⟩
  intro i
  apply hEk
  intro j hj
  change CoreShift^[i] (diagonalSplice z) j = z i j
  rw [shift_one_iterate_apply]
  exact diagonal_splice_overlap z k (fun n l hl => by
    have hn := hz n
    change (CoreShift (z n), z (n + 1)) ∈ boolPrefixRel (k + 1) at hn
    have hnl := hn l (by simpa [boolPrefixRel] using hl)
    simpa [CoreShift, SymbolicDynamics.FullShift.shift_apply, Nat.add_comm] using hnl) i j
    (by omega)

def prependBinaryName (b : Bool) (s : BinaryName) : BinaryName :=
  fun n => if n = 0 then b else s (n - 1)

theorem prependBinaryName_shift (b : Bool) (s : BinaryName) :
    CoreShift (prependBinaryName b s) = s := by
  funext n
  simp [CoreShift, prependBinaryName, SymbolicDynamics.FullShift.shift_apply]

theorem coreShift_isOpenMap : IsOpenMap CoreShift := by
  refine (isTopologicalBasis_pi (fun _ => isTopologicalBasis_opens)).isOpenMap_iff.2 ?_
  rintro _ ⟨U, F, hUF, rfl⟩
  apply isOpen_pi_iff.mpr
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  let I : Finset ℕ := F.filter (fun n => 0 < n) |>.image (fun n => n - 1)
  let W : ℕ → Set Bool := fun j =>
    if j + 1 ∈ F then U (j + 1) else Set.univ
  refine ⟨I, W, ?_, ?_⟩
  · intro j hj
    have hj' : ∃ n ∈ F, 0 < n ∧ n - 1 = j := by
      rcases Finset.mem_image.mp hj with ⟨n, hn, rfl⟩
      exact ⟨n, (Finset.mem_filter.mp hn).1, (Finset.mem_filter.mp hn).2, rfl⟩
    obtain ⟨n, hnF, hnpos, hnj⟩ := hj'
    subst j
    have hnmem : n ∈ F := hnF
    have hopen : IsOpen (U n) := hUF n hnmem
    have hmem : x n ∈ U n := Set.mem_pi.mp hx n hnF
    have hW : W (n - 1) = U n := by
      dsimp [W]
      rw [show n - 1 + 1 = n by omega, if_pos hnF]
    have hshiftmem : (CoreShift x) (n - 1) ∈ U n := by
      have hidx : 1 + (n - 1) = n := by omega
      simpa [CoreShift, SymbolicDynamics.FullShift.shift_apply, hidx] using hmem
    simpa [hW, hshiftmem]
  · intro s hs
    let x' := prependBinaryName (x 0) s
    have hx' : x' ∈ (F : Set ℕ).pi U := by
      apply Set.mem_pi.mpr
      intro n hnF
      by_cases hn0 : n = 0
      · subst n
        simpa [x', prependBinaryName] using Set.mem_pi.mp hx 0 hnF
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        have hj : n - 1 ∈ I := by
          apply Finset.mem_image.mpr
          exact ⟨n, Finset.mem_filter.mpr ⟨hnF, hnpos⟩, rfl⟩
        have hsW := Set.mem_pi.mp hs (n - 1) hj
        have hW : W (n - 1) = U n := by
          dsimp [W]
          have hnF' : n ∈ F := hnF
          simp [show n - 1 + 1 = n by omega, hnF']
        have hsU : s (n - 1) ∈ U n := by simpa [hW] using hsW
        simpa [x', prependBinaryName, hn0] using hsU
    refine ⟨x', hx', ?_⟩
    exact prependBinaryName_shift (x 0) s

theorem open_core_extension_hasShadowing
    {P S : Type*} [UniformSpace P] [UniformSpace S] [CompactSpace P] [CompactSpace S]
    [T2Space P] [T2Space S]
    (h : P ⊕ S → S) (g : S → S)
    (hcont : Continuous h) (hopen : IsOpenMap h) (honto : Function.Surjective h)
    (hcore : ∀ s, h (Sum.inr s) = g s) (hgcont : Continuous g)
    (hgs : HasShadowing g) :
    HasShadowing (fun x : P ⊕ S => Sum.inr (h x)) := by
  let F : P ⊕ S → P ⊕ S := fun x => Sum.inr (h x)
  have hF : Continuous F := continuous_inr.comp hcont
  have hgu : UniformHasShadowing g := (cover_shadowing_iff_uniform g).mp hgs
  apply (cover_shadowing_iff_uniform F).mpr
  intro E hE
  obtain ⟨V, hV, hVo, hVs, hVcomp⟩ := comp_open_symm_mem_uniformity_sets hE
  obtain ⟨C, hC⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (P ⊕ S))).elim_finite_subcover
      (fun x => UniformSpace.ball x V)
      (fun x => UniformSpace.isOpen_ball _ hVo)
      (by
        intro x _
        exact Set.mem_iUnion.mpr ⟨x, mem_ball_self x hV⟩)
  let ι := C
  let Uι : ι → Set (P ⊕ S) := fun i => UniformSpace.ball (i : P ⊕ S) V
  have hUι : ∀ i, IsOpen (Uι i) := fun i => UniformSpace.isOpen_ball _ hVo
  have hUcover : (Set.univ : Set (P ⊕ S)) ⊆ ⋃ i : ι, Uι i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hC hx)
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨v, hvcover, hvopen, hvcl, hvcompact⟩ :=
    exists_subset_iUnion_closure_subset_t2space (s := (Set.univ : Set (P ⊕ S)))
      isCompact_univ hUι (fun x _ => Set.toFinite _) hUcover
  let Ki : ι → Set S := fun i => h '' closure (v i)
  have hKi : ∀ i, IsCompact (Ki i) := fun i => (hvcompact i).image hcont
  have hKiU : ∀ i, Ki i ⊆ h '' Uι i := by
    intro i y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨x, hvcl i hx, rfl⟩
  have hUi : ∀ i, IsOpen (h '' Uι i) := fun i => hopen _ (hUι i)
  have hRexist : ∀ i, ∃ R : SetRel S S, R ∈ 𝓤 S ∧ IsOpen R ∧
      ∀ x ∈ Ki i, UniformSpace.ball x R ⊆ h '' Uι i := fun i =>
    lebesgue_number_of_compact_open (hKi i) (hUi i) (hKiU i)
  choose Ri hRi hRopen hRball using hRexist
  let L : SetRel S S := ⋂ i : ι, Ri i
  have hL : L ∈ 𝓤 S := Filter.iInter_mem.mpr (fun i => hRi i)
  have hLift : ∀ x : P ⊕ S, ∀ b : S, (h x, b) ∈ L →
      ∃ y : P ⊕ S, h y = b ∧ (y, x) ∈ E := by
    intro x b hxb
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hvcover (Set.mem_univ x))
    have hxs : x ∈ closure (v i) := subset_closure hxi
    have hhb : b ∈ UniformSpace.ball (h x) (Ri i) :=
      Set.mem_iInter.mp hxb i
    have hhb' : b ∈ h '' Uι i := hRball i (h x) ⟨x, hxs, rfl⟩ hhb
    rcases hhb' with ⟨y, hy, hhy⟩
    have hxiU : x ∈ Uι i := hvcl i hxs
    have hye : (y, x) ∈ V ○ V :=
      mem_comp_of_mem_ball (V := V) (W := V) (x := y) (y := x) (z := (i : P ⊕ S))
        (show y ∈ UniformSpace.ball (i : P ⊕ S) V from hy)
        (show x ∈ UniformSpace.ball (i : P ⊕ S) V from hxiU)
    exact ⟨y, hhy, hVcomp hye⟩
  obtain ⟨R, hR, hRo, hRs, hRcomp⟩ :=
    comp_open_symm_mem_uniformity_sets (inter_mem hL
      ((uniformContinuous_inr : UniformContinuous (Sum.inr : S → P ⊕ S)) hE))
  let Dcore : SetRel S S := Classical.choose (hgu R hR)
  have hDcore : Dcore ∈ 𝓤 S := (Classical.choose_spec (hgu R hR)).1
  have htrace_spec := (Classical.choose_spec (hgu R hR)).2
  let Q : SetRel S S := R ∩ (fun z : S × S => (g z.1, g z.2)) ⁻¹' Dcore
  have hQg : Q ∈ 𝓤 S := inter_mem hR ((CompactSpace.uniformContinuous_of_continuous hgcont) hDcore)
  let D : SetRel (P ⊕ S) (P ⊕ S) :=
    Prod.map Sum.inl Sum.inl '' (Set.univ : SetRel P P) ∪
      Prod.map Sum.inr Sum.inr '' Q
  have hD : D ∈ 𝓤 (P ⊕ S) := union_mem_uniformity_sum univ_mem hQg
  refine ⟨D, hD, ?_⟩
  intro z hz
  have hnext : ∀ n, ∃ s : S, z (n + 1) = Sum.inr s ∧ (h (z n), s) ∈ Q := by
    intro n
    have hn : (F (z n), z (n + 1)) ∈ D := by simpa [F, D] using hz n
    cases hz1 : z (n + 1) with
    | inl p => simp [D, F, hz1] at hn
    | inr s =>
      refine ⟨s, rfl, ?_⟩
      simpa [D, F, hz1] using hn
  have hcorepseudo : UniformPseudoOrbit g Dcore (fun n => h (z n)) := by
    intro n
    obtain ⟨s, hs, hqs⟩ := hnext n
    have hpre := hqs.2
    have hstep : (g (h (z n)), g s) ∈ Dcore := hpre
    simpa [hs, hcore] using hstep
  obtain ⟨b, hb⟩ := htrace_spec (fun n => h (z n)) hcorepseudo
  have hRb : (h (z 0), b) ∈ R := by
    have hb0 := hb 0
    letI : SetRel.IsSymm R := hRs
    have h' : h (z 0) ∈ UniformSpace.ball (b) R := by
      change (b, h (z 0)) ∈ R
      exact hb0
    have h'' := (mem_ball_symmetry).mp h'
    change (h (z 0), b) ∈ R at h''
    exact h''
  obtain ⟨y, hyb, hyE⟩ := hLift (z 0) b ((hRcomp (mem_comp_of_mem_ball
    (V := R) (W := R) (mem_ball_self _ hR) hRb)).1)
  refine ⟨y, ?_⟩
  have hyiter : ∀ n : ℕ, F^[n + 1] y = Sum.inr (g^[n] b) := by
    intro n
    induction n with
    | zero => simpa [F, hyb]
    | succ n ih =>
      rw [show n + 1 + 1 = 1 + (n + 1) by omega, iterate_add_apply]
      simp [F, ih, hcore]
      exact (iterate_succ_apply' g n b).symm.trans (iterate_succ_apply g n b)
  intro n
  cases n with
  | zero => simpa [F] using hyE
  | succ n =>
    obtain ⟨s, hs, hqs⟩ := hnext n
    have hcomp : (g^[n] b, s) ∈ R ○ R :=
      ⟨h (z n), hb n, hqs.1⟩
    have hEcore := (hRcomp hcomp).2
    simpa [hyiter, hs] using hEcore

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

theorem finite_initial_presentation_to_graphLanguage
    {S : Set BinaryName} (hS : HasFiniteInitialPresentation S) :
    ∃ c : FiniteGraphCode, S = finiteGraphLanguage c := by
  classical
  rcases hS with ⟨n, edge, label, initial, hEq⟩
  let c : FiniteGraphCode :=
    ⟨n, (fun v w => decide (edge v w), label, fun v => decide (v ∈ initial))⟩
  refine ⟨c, ?_⟩
  rw [hEq]
  ext word
  constructor
  · rintro ⟨path, hp0, hpath, hlabel⟩
    refine ⟨path, ?_, ?_, hlabel⟩
    · simpa [finiteGraphLanguage, boolInitialGraphLanguage, c] using hp0
    · intro n
      simpa [finiteGraphLanguage, boolInitialGraphLanguage, c] using hpath n
  · rintro ⟨path, hp0, hpath, hlabel⟩
    refine ⟨path, ?_, ?_, hlabel⟩
    · simpa [finiteGraphLanguage, boolInitialGraphLanguage, c] using hp0
    · intro n
      simpa [finiteGraphLanguage, boolInitialGraphLanguage, c] using hpath n

theorem semiconj_clopen_image_is_finiteGraphLanguage
    {Y : Type*} [TopologicalSpace Y]
    (T : Y → Y) (phi : Y → BinaryName) (hphi : Continuous phi)
    (hsem : Semiconj phi T CoreShift) (hT : HasShadowing T)
    (W : Set Y) (hW : IsClopen W) :
    ∃ c : FiniteGraphCode, phi '' W = finiteGraphLanguage c := by
  let mark : Y → Bool := W.boolIndicator
  have hmark : Continuous mark :=
    (continuous_boolIndicator_iff_isClopen W).2 hW
  have hcoord : Continuous (fun y : Y => phi y 0) :=
    (continuous_apply 0).comp hphi
  obtain ⟨n, edge, label, initial, hpres⟩ := finite_initial_marked_names
    T (fun y => phi y 0) hcoord mark hmark true hT
  have hrange : Set.range (fun y : {y : Y // mark y = true} =>
      fun n => phi (T^[n] y.val) 0) = phi '' W := by
    ext s
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨y.val, ?_, ?_⟩
      · exact (Set.mem_iff_boolIndicator W y.val).mpr y.property
      · funext n
        have hn := congrFun (hsem.iterate_right n y.val) 0
        exact (hn.trans (by simpa [CoreShift] using
          shift_one_iterate_apply (phi y.val) n 0)).symm
    · rintro ⟨y, hyW, rfl⟩
      refine ⟨⟨y, ?_⟩, ?_⟩
      · exact (Set.mem_iff_boolIndicator W y).mp hyW
      · funext n
        have hn := congrFun (hsem.iterate_right n y) 0
        exact hn.trans (by simpa [CoreShift] using
          shift_one_iterate_apply (phi y) n 0)
  obtain ⟨c, hc⟩ := finite_initial_presentation_to_graphLanguage
    ⟨n, edge, label, initial, hpres⟩
  exact ⟨c, hrange.symm.trans hc⟩

theorem convergentSection_singleton_isClopen (a : BinaryName) (n : ℕ) :
    IsClopen ({⟨convergentSectionName a n,
      Or.inr ⟨n, rfl⟩⟩} : Set (convergentSectionSet a)) := by
  let g : convergentSectionSet a → OnePoint ℕ := firstDifferenceOnSection a
  have hg : Continuous g := by
    change Continuous (firstDifference a ∘ Subtype.val)
    exact (continuous_firstDifference a).comp continuous_subtype_val
  have hsingle : IsClopen ({(n : OnePoint ℕ)} : Set (OnePoint ℕ)) := by
    refine ⟨isClosed_singleton, ?_⟩
    simpa using
      (OnePoint.isOpen_image_coe (s := ({n} : Set ℕ))).2 (isOpen_discrete _)
  have hpre : IsClopen (g ⁻¹' ({(n : OnePoint ℕ)} : Set (OnePoint ℕ))) :=
    hsingle.preimage hg
  have heq : g ⁻¹' ({(n : OnePoint ℕ)} : Set (OnePoint ℕ)) =
      ({⟨convergentSectionName a n, Or.inr ⟨n, rfl⟩⟩} : Set (convergentSectionSet a)) := by
    ext s
    constructor
    · intro hs
      have hcan := convergentSectionName_firstDifference a n
      have hsn : firstDifferenceOnSection a s = (n : OnePoint ℕ) := hs
      apply Subtype.ext
      exact congrArg Subtype.val
        ((firstDifferenceOnSection_bijective a).1 (hsn.trans hcan.symm))
    · intro hs
      have hs' : s = ⟨convergentSectionName a n, Or.inr ⟨n, rfl⟩⟩ := by simpa using hs
      subst s
      exact convergentSectionName_firstDifference a n
  rw [heq] at hpre
  exact hpre

theorem finiteGraphLanguage_section_isClopen
    (a : BinaryName) (c : FiniteGraphCode)
    (hdec : ∃ U : Set BinaryName, IsOpen U ∧ a ∈ U ∧
      (U ⊆ finiteGraphLanguage c ∨ U ⊆ (finiteGraphLanguage c)ᶜ)) :
    IsClopen (((↑) : convergentSectionSet a → BinaryName) ⁻¹'
      finiteGraphLanguage c) := by
  let S₀ := convergentSectionSet a
  let C := finiteGraphLanguage c
  let E : Set S₀ := ((↑) : S₀ → BinaryName) ⁻¹' C
  have hpoint (s : S₀) (hs : s ∈ E) : E ∈ 𝓝 s := by
    by_cases hsa : s.val = a
    · let a₀ : S₀ := ⟨a, Or.inl rfl⟩
      have hsa₀ : s = a₀ := by
        apply Subtype.ext
        exact hsa
      subst s
      obtain ⟨U, hU, haU, hside⟩ := hdec
      have haC : a ∈ C := hs
      rcases hside with hUC | hUcomp
      · apply Filter.mem_of_superset
          ((hU.preimage continuous_subtype_val).mem_nhds (show a₀ ∈
            (Subtype.val : S₀ → BinaryName) ⁻¹' U from haU))
        intro x hx
        exact hUC hx
      · exact False.elim (hUcomp haU haC)
    · obtain ⟨n, hn⟩ := convergentSectionSet_firstDifference_finite a s.val s.property hsa
      let cn : S₀ := ⟨convergentSectionName a n, Or.inr ⟨n, rfl⟩⟩
      have hsn : s = cn := by
        exact (firstDifferenceOnSection_bijective a).1 (show firstDifferenceOnSection a s =
          firstDifferenceOnSection a cn from hn.trans
            (convergentSectionName_firstDifference a n).symm)
      have hcn := convergentSection_singleton_isClopen a n
      subst s
      apply Filter.mem_of_superset (hcn.2.mem_nhds (by
        change cn = ⟨convergentSectionName a n, Or.inr ⟨n, rfl⟩⟩
        rfl))
      intro x hx
      have hxc : x = cn := by simpa using hx
      simpa [hxc] using hs
  have hpoint_compl (s : S₀) (hs : s ∈ Eᶜ) : Eᶜ ∈ 𝓝 s := by
    by_cases hsa : s.val = a
    · let a₀ : S₀ := ⟨a, Or.inl rfl⟩
      have hsa₀ : s = a₀ := by
        apply Subtype.ext
        exact hsa
      subst s
      obtain ⟨U, hU, haU, hside⟩ := hdec
      have haC : a ∉ C := by
        intro haC
        exact hs haC
      rcases hside with hUC | hUcomp
      · exact False.elim (haC (hUC haU))
      · apply Filter.mem_of_superset
          ((hU.preimage continuous_subtype_val).mem_nhds (show a₀ ∈
            (Subtype.val : S₀ → BinaryName) ⁻¹' U from haU))
        intro x hx hCx
        exact (hUcomp hx) hCx
    · obtain ⟨n, hn⟩ := convergentSectionSet_firstDifference_finite a s.val s.property hsa
      let cn : S₀ := ⟨convergentSectionName a n, Or.inr ⟨n, rfl⟩⟩
      have hsn : s = cn := by
        exact (firstDifferenceOnSection_bijective a).1 (show firstDifferenceOnSection a s =
          firstDifferenceOnSection a cn from hn.trans
            (convergentSectionName_firstDifference a n).symm)
      have hcn := convergentSection_singleton_isClopen a n
      subst s
      apply Filter.mem_of_superset (hcn.2.mem_nhds (by
        change cn = ⟨convergentSectionName a n, Or.inr ⟨n, rfl⟩⟩
        rfl))
      intro x hx
      have hxc : x = cn := by simpa using hx
      simpa [hxc] using hs
  refine ⟨?_, ?_⟩
  · apply isOpen_compl_iff.mp
    rw [isOpen_iff_mem_nhds]
    exact hpoint_compl
  · rw [isOpen_iff_mem_nhds]
    exact hpoint

theorem clopen_subtype_extension
    {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    [ZeroDimensionalSpace Y] {P K : Set Y} (hP : IsClopen P)
    (hK : IsClosed K) (hKP : K ⊆ P) {E : Set K} (hE : IsClopen E) :
    ∃ W : Set Y, IsClopen W ∧ W ⊆ P ∧
      ((Subtype.val : K → Y) ⁻¹' W = E) := by
  letI : CompactSpace K := hK.isClosedEmbedding_subtypeVal.compactSpace
  let EI : Set Y := Subtype.val '' E
  let FI : Set Y := Subtype.val '' Eᶜ
  have hEI : IsClosed EI := by
    exact (hE.1.isCompact.image continuous_subtype_val).isClosed
  have hFI : IsClosed FI := by
    exact (hE.2.isClosed_compl.isCompact.image continuous_subtype_val).isClosed
  have hdis : Disjoint EI FI := by
    refine Set.disjoint_left.2 ?_
    intro y hyE hyF
    obtain ⟨x, hxE, hxy⟩ := hyE
    obtain ⟨z, hzF, hzy⟩ := hyF
    have hxz : x = z := Subtype.ext (hxy.trans hzy.symm)
    exact hzF (hxz ▸ hxE)
  obtain ⟨W, hW, hEW, hWF⟩ := exists_clopen_of_closed_subset_open
    hEI hFI.isOpen_compl (by
      intro y hy
      intro hyF
      exact Set.disjoint_left.1 hdis hy hyF)
  let W' := W ∩ P
  have hW' : IsClopen W' := hW.inter hP
  refine ⟨W', hW', inter_subset_right, ?_⟩
  ext x
  constructor
  · intro hx
    have hxW : (x : Y) ∈ W := hx.1
    by_contra hxE
    have hxEc : x ∈ Eᶜ := hxE
    exact hWF hxW ⟨(x : K), hxEc, rfl⟩
  · intro hx
    exact ⟨hEW ⟨(x : K), hx, rfl⟩, hKP x.property⟩

theorem freeFibreSource_hasShadowing
    {T : Type*} [TopologicalSpace T] [CompactSpace T] [T2Space T]
    (p : T → OnePoint ℕ) (a : BinaryName) (hp : Continuous p)
    (honto : Function.Surjective p) (hopen : IsOpenMap p) :
    HasShadowing (sourceDynamics p a) := by
  letI : CompactSpace (FibrePullback p (firstDifference a)) :=
    fibrePullback_compactSpace p (firstDifference a) hp (continuous_firstDifference a)
  letI : T2Space (FibrePullback p (firstDifference a)) :=
    fibrePullback_t2Space p (firstDifference a)
  letI : UniformSpace (FibrePullback p (firstDifference a)) := uniformSpaceOfCompactR1
  have hHcont : Continuous (fibrePullbackSecond p (firstDifference a)) :=
    fibrePullbackSecond_continuous p (firstDifference a)
  have hHopen : IsOpenMap (fibrePullbackSecond p (firstDifference a)) :=
    fibrePullbackSecond_isOpenMap p (firstDifference a) hopen (continuous_firstDifference a)
  have hHonto : Function.Surjective (fibrePullbackSecond p (firstDifference a)) :=
    fibrePullbackSecond_surjective p (firstDifference a) honto
  let hExt : FibrePullback p (firstDifference a) ⊕ BinaryName → BinaryName :=
    Sum.elim (fibrePullbackSecond p (firstDifference a)) CoreShift
  have hExtcont : Continuous hExt :=
    hHcont.sumElim (SymbolicDynamics.FullShift.continuous_shift 1)
  have hExtopen : IsOpenMap hExt := hHopen.sumElim coreShift_isOpenMap
  have hExtonto : Function.Surjective hExt := by
    intro s
    refine ⟨Sum.inr (prependBinaryName false s), ?_⟩
    simpa [hExt] using (prependBinaryName_shift false s)
  have hcore : HasShadowing CoreShift :=
    (cover_shadowing_iff_uniform CoreShift).mpr coreShift_uniformHasShadowing
  have hs := open_core_extension_hasShadowing
    (h := hExt) (g := CoreShift)
    hExtcont hExtopen hExtonto (by
      intro s
      change CoreShift s = CoreShift s
      rfl)
    (SymbolicDynamics.FullShift.continuous_shift 1) hcore
  have heq : sourceDynamics p a = (fun x => Sum.inr (hExt x)) := by
    funext x
    cases x <;> rfl
  rw [heq]
  exact hs

theorem freeFibre_cover_forces_resolution
    {T : Type u} [TopologicalSpace T] [CompactSpace T] [T2Space T]
    (p : T → OnePoint ℕ) (hp : Continuous p) (honto : Function.Surjective p)
    (hopen : IsOpenMap p) (a : BinaryName)
    (hgeneric : ∀ c : FiniteGraphCode, ∃ U : Set BinaryName, IsOpen U ∧ a ∈ U ∧
      (U ⊆ finiteGraphLanguage c ∨ U ⊆ (finiteGraphLanguage c)ᶜ))
    {Y : Type v} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    [TotallyDisconnectedSpace Y] (τ : Y → Y) (_hτc : Continuous τ)
    (hτs : HasShadowing τ) (q : Y → FreeFibreSource p a)
    (hq : Continuous q) (hqonto : Function.Surjective q)
    (hsemq : Semiconj q τ (sourceDynamics p a)) :
    HasOpenZeroDimensionalResolution.{u, 0, v} p := by
  letI : CompactSpace (FibrePullback p (firstDifference a)) :=
    fibrePullback_compactSpace p (firstDifference a) hp (continuous_firstDifference a)
  letI : T2Space (FibrePullback p (firstDifference a)) :=
    fibrePullback_t2Space p (firstDifference a)
  let S₀ : Set BinaryName := convergentSectionSet a
  have hS₀closed : IsClosed S₀ := (convergentSectionSet_isCompact a).isClosed
  have hobs : Continuous (sourceObservation p a) :=
    sourceObservation_continuous p a (fibrePullbackSecond_continuous p (firstDifference a))
  let ϕ : Y → BinaryName := sourceObservation p a ∘ q
  have hϕ : Continuous ϕ := hobs.comp hq
  have hsemϕ : Semiconj ϕ τ CoreShift := by
    intro y
    change sourceObservation p a (q (τ y)) = CoreShift (sourceObservation p a (q y))
    rw [hsemq y]
    exact sourceDynamics_semiconj p a (q y)
  let Pset : Set (FreeFibreSource p a) :=
    range (Sum.inl : FibrePullback p (firstDifference a) → FreeFibreSource p a) ∩
      (sourceObservation p a ⁻¹' S₀)
  have hPset : IsClosed Pset := by
    exact isClosed_range_inl.inter (hS₀closed.preimage hobs)
  let YP : Set Y := q ⁻¹' range (Sum.inl : FibrePullback p (firstDifference a) →
    FreeFibreSource p a)
  have hYP : IsClopen YP := by
    exact (isClopen_range_inl.preimage hq)
  let Y₀set : Set Y := q ⁻¹' Pset
  have hY₀closed : IsClosed Y₀set := hPset.preimage hq
  let Y₀ := {y : Y // y ∈ Y₀set}
  let t₀ : T := Classical.choose (honto (∞ : OnePoint ℕ))
  let rBase : FreeFibreSource p a → T :=
    Sum.elim (fun z => z.val.1) (fun _ => t₀)
  have hrBase : Continuous rBase := by
    exact (continuous_fst.comp continuous_subtype_val).sumElim continuous_const
  let r : Y₀ → T := rBase ∘ q ∘ Subtype.val
  have hr : Continuous r := hrBase.comp (hq.comp continuous_subtype_val)
  letI : CompactSpace Y₀ := hY₀closed.isClosedEmbedding_subtypeVal.compactSpace
  have hY₀subYP : Y₀set ⊆ YP := by
    intro y hy
    exact hy.1
  have hronto : Function.Surjective r := by
    obtain ⟨e, he⟩ := exists_firstDifference_section_homeomorph a
    intro t
    obtain ⟨s, hs⟩ := e.surjective (p t)
    have hps : p t = firstDifference a s.val := by
      calc
        p t = e s := (hs).symm
        _ = firstDifferenceOnSection a s := he s
        _ = firstDifference a s.val := rfl
    let z : FibrePullback p (firstDifference a) := ⟨(t, s.val), hps⟩
    obtain ⟨y, hy⟩ := hqonto (Sum.inl z)
    have hyP : q y ∈ Pset := by
      refine ⟨⟨z, hy.symm⟩, ?_⟩
      change sourceObservation p a (q y) ∈ S₀
      rw [hy]
      exact s.property
    refine ⟨⟨y, hyP⟩, ?_⟩
    simp [r, rBase, hy, z]
  have himage : ∀ E : Set Y₀, IsClopen E →
      IsOpen (p '' (r '' E)) := by
    intro E hE
    obtain ⟨W, hW, hWP, htrace⟩ := clopen_subtype_extension hYP hY₀closed
      hY₀subYP hE
    obtain ⟨c, hc⟩ := semiconj_clopen_image_is_finiteGraphLanguage
      τ ϕ hϕ hsemϕ hτs W hW
    obtain ⟨U, hU, haU, hside⟩ := hgeneric c
    have hCsection : IsClopen (((↑) : S₀ → BinaryName) ⁻¹'
        finiteGraphLanguage c) := finiteGraphLanguage_section_isClopen a c
      ⟨U, hU, haU, hside⟩
    let Ebase : Set Y := Subtype.val '' E
    have hEbaseW : Ebase ⊆ W := by
      rintro y ⟨y₀, hy₀, rfl⟩
      change y₀ ∈ (Subtype.val : Y₀ → Y) ⁻¹' W
      rw [htrace]
      exact hy₀
    have hϕE : ϕ '' Ebase = (ϕ '' W) ∩ S₀ := by
      ext s
      constructor
      · rintro ⟨y, hyEbase, hys⟩
        obtain ⟨y₀, hy₀, rfl⟩ := hyEbase
        have hyW : (y₀ : Y) ∈ W := hEbaseW ⟨y₀, hy₀, rfl⟩
        refine ⟨⟨(y₀ : Y), hyW, hys⟩, ?_⟩
        have hsection : sourceObservation p a (q y₀) ∈ S₀ := by
          exact y₀.property.2
        have hϕsection : ϕ (y₀ : Y) ∈ S₀ := by
          change sourceObservation p a (q y₀) ∈ S₀
          exact hsection
        exact hys ▸ hϕsection
      · rintro ⟨⟨y, hyW, hys⟩, hs⟩
        have hyP : q y ∈ Pset := by
          refine ⟨?_, ?_⟩
          · exact hWP hyW
          · change ϕ y ∈ S₀
            simpa [hys] using hs
        have hy₀ : y ∈ Y₀set := hyP
        have hyE : (⟨y, hy₀⟩ : Y₀) ∈ E := by
          have hmem : (⟨y, hy₀⟩ : Y₀) ∈
              (Subtype.val : Y₀ → Y) ⁻¹' W := hyW
          rw [htrace] at hmem
          exact hmem
        exact ⟨y, ⟨⟨y, hy₀⟩, hyE, rfl⟩, hys⟩
    have hEsection : IsClopen (((↑) : S₀ → BinaryName) ⁻¹' (ϕ '' Ebase)) := by
      have heq : ((↑) : S₀ → BinaryName) ⁻¹' (ϕ '' Ebase) =
          ((↑) : S₀ → BinaryName) ⁻¹' finiteGraphLanguage c := by
        ext s
        rw [hϕE, hc]
        simp [s.property]
      rw [heq]
      exact hCsection
    obtain ⟨e, he⟩ := exists_firstDifference_section_homeomorph a
    have himagePR : p '' (r '' E) = e ''
        (((↑) : S₀ → BinaryName) ⁻¹' (ϕ '' Ebase)) := by
      ext b
      constructor
      · rintro ⟨u, ⟨y₀, hy₀, rfl⟩, rfl⟩
        obtain ⟨z, hz⟩ := y₀.property.1
        have hqz : q y₀.val = Sum.inl z := by
          exact hz.symm
        have hzS : z.val.2 ∈ S₀ := by
          have hsection : sourceObservation p a (q y₀) ∈ S₀ := by
            exact y₀.property.2
          rw [hqz] at hsection
          simpa [sourceObservation] using hsection
        let s : S₀ := ⟨z.val.2, hzS⟩
        have hϕs : ϕ y₀.val = s.val := by
          simp [ϕ, Function.comp_def, hqz, sourceObservation, s]
        have hpr : p (r y₀) = firstDifference a z.val.2 := by
          simp [r, rBase, hqz]
          exact z.property
        refine ⟨s, ?_, ?_⟩
        · exact ⟨y₀.val, ⟨y₀, hy₀, rfl⟩, hϕs⟩
        · rw [he s]
          change firstDifference a z.val.2 = p (r y₀)
          exact hpr.symm
      · rintro ⟨s, hsE, hse⟩
        obtain ⟨y, hyEbase, hϕy⟩ := hsE
        obtain ⟨y₀, hyE, rfl⟩ := hyEbase
        obtain ⟨z, hz⟩ := y₀.property.1
        have hqz : q y₀.val = Sum.inl z := hz.symm
        have hps : p (r y₀) = firstDifference a z.val.2 := by
          simp [r, rBase, hqz]
          exact z.property
        have hsz : s.val = z.val.2 := by
          calc
            s.val = ϕ y₀.val := hϕy.symm
            _ = sourceObservation p a (q y₀.val) := rfl
            _ = z.val.2 := by rw [hqz]; rfl
        refine ⟨r y₀, ⟨y₀, hyE, rfl⟩, ?_⟩
        have hEq : e s = p (r y₀) := by
          calc
            e s = firstDifferenceOnSection a s := he s
            _ = firstDifference a s.val := rfl
            _ = firstDifference a z.val.2 := by rw [hsz]
            _ = p (r y₀) := hps.symm
        exact hEq.symm.trans hse
    have hopenImage : IsOpen (e ''
        (((↑) : S₀ → BinaryName) ⁻¹' (ϕ '' Ebase))) :=
      e.isOpenMap _ hEsection.2
    rw [himagePR]
    exact hopenImage
  have hopenComp : IsOpenMap (p ∘ r) := by
    apply IsOpenMap.of_nhds_le
    intro y
    apply le_map_iff.2
    intro V hV
    obtain ⟨U, hUV, hUopen, hyU⟩ := mem_nhds_iff.mp hV
    obtain ⟨E, hE, hyE, hEU⟩ := exists_isClopen_mem_of_isOpen hUopen hyU
    have hopenE := himage E hE
    have hsub : p '' (r '' E) ⊆ (p ∘ r) '' V := by
      rintro b ⟨t, ⟨y₀, hy₀, rfl⟩, hpb⟩
      exact ⟨y₀, hUV (hEU hy₀), hpb⟩
    apply Filter.mem_of_superset (hopenE.mem_nhds
      ⟨r y, ⟨y, hyE, rfl⟩, rfl⟩)
    exact hsub
  refine ⟨Y₀, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  refine ⟨r, hr, hronto, ?_⟩
  exact hopenComp

/- The original extension assertion, with compact Hausdorff source and
zero-dimensional compact Hausdorff upstairs systems, retaining the forward
shadowing and time-zero factor quantifiers. -/
def claim : Prop :=
  ∀ (X : Type) (tX : TopologicalSpace X) (cX : @CompactSpace X tX)
    (hX : @T2Space X tX) (f : X → X),
    letI := tX
    letI := cX
    letI := hX
    Continuous f → HasShadowing f →
      ∃ (Y : Type) (tY : TopologicalSpace Y) (cY : @CompactSpace Y tY)
        (hY : @T2Space Y tY) (zY : @ZeroDimensionalSpace Y tY),
        letI := tY
        letI := cY
        letI := hY
        letI := zY
        ∃ (τ : Y → Y), Continuous τ ∧ HasShadowing τ ∧
          ∃ q : Y → X, Continuous q ∧ Function.Surjective q ∧ Semiconj q τ f

theorem result : ¬ claim := by
  intro hclaim
  obtain ⟨A, ell, hAD, hconv, _hclosed, hcompact, hp, hopen, honto, _hU, hnores⟩ :=
    exists_compact_open_map_no_finite_closed_refinement
  obtain ⟨a, hgeneric⟩ := exists_generic_finite_graph_decision
  letI : CompactSpace (Space A natValue ell) := isCompact_iff_compactSpace.mp hcompact
  let p : Space A natValue ell → OnePoint ℕ := projection A natValue ell
  have hp' : Continuous p := by simpa [p] using hp
  have hopen' : IsOpenMap p := by simpa [p] using hopen
  have honto' : Function.Surjective p := by simpa [p] using honto
  letI : CompactSpace (FibrePullback p (firstDifference a)) :=
    fibrePullback_compactSpace p (firstDifference a) hp' (continuous_firstDifference a)
  letI : T2Space (FibrePullback p (firstDifference a)) :=
    fibrePullback_t2Space p (firstDifference a)
  letI : CompactSpace (FreeFibreSource p a) := inferInstance
  letI : T2Space (FreeFibreSource p a) := inferInstance
  have hsourcec : Continuous (sourceDynamics p a) := sourceDynamics_continuous p a
  have hsources : HasShadowing (sourceDynamics p a) :=
    freeFibreSource_hasShadowing p a hp' honto' hopen'
  obtain ⟨Y, tY, cY, hY, zY, τ, hτc, hτs, q, hq, hqonto, hsem⟩ :=
    hclaim (FreeFibreSource p a) inferInstance inferInstance inferInstance
      (sourceDynamics p a) hsourcec hsources
  letI := tY
  letI := cY
  letI := hY
  letI := zY
  have hres := freeFibre_cover_forces_resolution
    p hp' honto' hopen' a hgeneric τ hτc hτs q hq hqonto hsem
  apply hnores
  simpa [p] using hres

end
end D5.S1.Dynamics.Shadowing.FreeFibreBoundary
