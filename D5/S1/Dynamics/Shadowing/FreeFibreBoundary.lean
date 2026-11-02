/- GID: D5/S1/Dynamics/Shadowing/FreeFibreBoundary
   generality: G
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Marked finite observations of shadowing systems have exact finite-initial graph languages. -/

import D5.S1.Dynamics.Shadowing.FiniteObservationSofic
import D5.S1.Dynamics.Shadowing.MetricTracing
import D5.S3.Topology.AlmostDisjoint.AdaptiveRefinementCounterexample
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Instances.Nat

/-! Marked finite observations, generic binary names, and the first-disagreement
map used by the free-fibre boundary construction. -/

open TopologicalSpace Set Function Filter
open scoped Topology

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
    ∃ n, firstDifference a s = (n : OnePoint ℕ) := by
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

theorem firstDifference_surjective (a : BinaryName) :
    Function.Surjective (firstDifference a) := by
  obtain ⟨e, he⟩ := exists_firstDifference_section_homeomorph a
  intro b
  obtain ⟨s, hs⟩ := e.surjective b
  exact ⟨s.val, (he s).symm.trans hs⟩

abbrev CoreShift : BinaryName → BinaryName :=
  SymbolicDynamics.FullShift.shift (1 : ℕ)

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

