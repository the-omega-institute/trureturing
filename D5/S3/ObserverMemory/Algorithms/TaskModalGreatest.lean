/- GID: D5/S3/ObserverMemory/Algorithms/TaskModalGreatest
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/TaskModalGreatest
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Set.Finite.Basic, mathlib/module/Mathlib.Tactic.Common]
   utility: none
   digest: Finite task-modal tests determine the greatest task-preserving successor equivalence. -/

import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Common

/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
HML authors: Fabrizio Montesi, Marco Peressotti, Alexandre Rademaker.
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
LTS/Bisimulation authors: Fabrizio Montesi, Thomas Waring.
Released under Apache 2.0; the complete upstream license is retained in
docs/reports/cslib-hml-LICENSE.txt.

Source: https://github.com/leanprover/cslib/tree/3951377e5a3f5772737f11cd62bc5bb6a72f95d1
Cslib/Logics/HML/Basic.lean: Proposition, Satisfies, finiteAnd,
finiteAnd_iff_forall, not_theoryEq_satisfies, theoryEq_satisfies,
propositions, propositions_complete, propositions_satisfies_conjunction,
theoryEq_isBisimulation, bisimulation_satisfies.
Cslib/Foundations/Semantics/LTS/Basic.lean: LTS.Tr and image.
Cslib/Foundations/Semantics/LTS/Bisimulation.lean: IsBisimulation and IsHomBisimulation.

MODIFIED EXTRACTION: LTS and inference-system bundles are lowered to raw
relations and predicates; notation is replaced by constructors; support proofs
are local terms of result. The finite distinguishing-formula construction and
formula induction are the upstream proofs, with their tactic steps made explicit.
Independent task syntax and the two recursive semantics translations are added.
The source pins Lean v4.33.0 and Mathlib db584cd6d46c92f209a44c0f1c829460d327499d.
Retirement: when this repository's actual pinned Mathlib closure supplies
equivalent HML syntax, semantics, and the image-finite theorem, replace the
extraction by direct use through migration preserving existing frozen identities.
-/

namespace D5.S3.ObserverMemory.Algorithms.TaskModalGreatest

universe u v w z

/-- Finite task-modal formulas, with dependent task-value atoms. -/
inductive TaskFormula (U : Type u) (J : Type v) (Y : J → Type w) :
    Type (max u v w) where
  | top
  | atom (j : J) (value : Y j)
  | neg (φ : TaskFormula U J Y)
  | conj (φ ψ : TaskFormula U J Y)
  | diamond (label : U) (φ : TaskFormula U J Y)

/-- A modality chooses one actual successor at which its entire argument holds. -/
def task_satisfies {X : Type z} {U : Type u} {J : Type v} {Y : J → Type w}
    (R : U → X → X → Prop) (f : ∀ j, X → Y j) (x : X) : TaskFormula U J Y → Prop
  | .top => True
  | .atom j value => f j x = value
  | .neg φ => ¬task_satisfies R f x φ
  | .conj φ ψ => task_satisfies R f x φ ∧ task_satisfies R f x ψ
  | .diamond label φ => ∃ x', R label x x' ∧ task_satisfies R f x' φ

/-- Agreement on all independently generated finite task-modal formulas. -/
def task_modal_eq {X : Type z} {U : Type u} {J : Type v} {Y : J → Type w}
    (R : U → X → X → Prop) (f : ∀ j, X → Y j) (x y : X) : Prop :=
  ∀ φ, task_satisfies R f x φ ↔ task_satisfies R f y φ

/-- Cslib's minimal HML syntax, with notation wrappers removed. -/
inductive HmlFormula (L : Type u) : Type u where
  | top
  | conj (φ ψ : HmlFormula L)
  | neg (φ : HmlFormula L)
  | diamond (label : L) (φ : HmlFormula L)

/-- Cslib's HML satisfaction, with the LTS transition field unbundled. -/
def hml_satisfies {X : Type z} {L : Type u}
    (T : L → X → X → Prop) (x : X) : HmlFormula L → Prop
  | .top => True
  | .conj φ ψ => hml_satisfies T x φ ∧ hml_satisfies T x ψ
  | .neg φ => ¬hml_satisfies T x φ
  | .diamond label φ => ∃ x', T label x x' ∧ hml_satisfies T x' φ

/-- For image-finite transitions, task-modal agreement is an equivalence preserving
all tasks and matching successors in both directions. Every equivalence with
those two properties is contained in it. -/
theorem result {X : Type z} {U : Type u} {J : Type v} {Y : J → Type w}
    (R : U → X → X → Prop) (f : ∀ j, X → Y j)
    (finite_image : ∀ label x, Set.Finite {x' | R label x x'}) :
    Equivalence (task_modal_eq R f) ∧
    (∀ x y, task_modal_eq R f x y → ∀ j, f j x = f j y) ∧
    (∀ x y, task_modal_eq R f x y → ∀ label,
      (∀ x', R label x x' → ∃ y', R label y y' ∧ task_modal_eq R f x' y') ∧
      (∀ y', R label y y' → ∃ x', R label x x' ∧ task_modal_eq R f x' y')) ∧
    (∀ E : X → X → Prop, Equivalence E →
      (∀ x y, E x y → ∀ j, f j x = f j y) →
      (∀ x y, E x y → ∀ label,
        (∀ x', R label x x' → ∃ y', R label y y' ∧ E x' y') ∧
        (∀ y', R label y y' → ∃ x', R label x x' ∧ E x' y')) →
      ∀ x y, E x y → task_modal_eq R f x y) := by
  classical
  let T : (U ⊕ (Σ j, Y j)) → X → X → Prop
    | .inl label, x, x' => R label x x'
    | .inr ⟨j, value⟩, x, x' => x' = x ∧ f j x = value
  let forward : TaskFormula U J Y → HmlFormula (U ⊕ (Σ j, Y j)) :=
    TaskFormula.rec (motive := fun _ => HmlFormula (U ⊕ (Σ j, Y j)))
      .top (fun j value => .diamond (.inr ⟨j, value⟩) .top)
      (fun _ φ => .neg φ) (fun _ _ φ ψ => .conj φ ψ)
      (fun label _ φ => .diamond (.inl label) φ)
  let backward : HmlFormula (U ⊕ (Σ j, Y j)) → TaskFormula U J Y :=
    HmlFormula.rec (motive := fun _ => TaskFormula U J Y)
      .top (fun _ _ φ ψ => .conj φ ψ) (fun _ φ => .neg φ)
      (fun label _ φ => match label with
        | .inl label => .diamond label φ
        | .inr ⟨j, value⟩ => .conj (.atom j value) φ)
  have forward_sat (φ : TaskFormula U J Y) :
      ∀ x, hml_satisfies T x (forward φ) ↔ task_satisfies R f x φ := by
    induction φ with
    | top => intro x; rfl
    | atom j value => intro x; simp [forward, hml_satisfies, task_satisfies, T]
    | neg φ ih => intro x; exact not_congr (ih x)
    | conj φ ψ ihφ ihψ => intro x; exact and_congr (ihφ x) (ihψ x)
    | diamond label φ ih =>
        intro x
        simp only [forward, hml_satisfies, task_satisfies, T, ih]
  have backward_sat (φ : HmlFormula (U ⊕ (Σ j, Y j))) :
      ∀ x, task_satisfies R f x (backward φ) ↔ hml_satisfies T x φ := by
    induction φ with
    | top => intro x; rfl
    | conj φ ψ ihφ ihψ => intro x; exact and_congr (ihφ x) (ihψ x)
    | neg φ ih => intro x; exact not_congr (ih x)
    | diamond label φ ih =>
        intro x
        cases label with
        | inl label => simp only [backward, task_satisfies, hml_satisfies, T, ih]
        | inr observation =>
            rcases observation with ⟨j, value⟩
            simp [backward, task_satisfies, hml_satisfies, T, ih]
  let TheoryEq (x y : X) := ∀ φ, hml_satisfies T x φ ↔ hml_satisfies T y φ
  have correspondence (x y : X) : task_modal_eq R f x y ↔ TheoryEq x y := by
    constructor
    · intro h φ
      exact (backward_sat φ x).symm.trans ((h (backward φ)).trans (backward_sat φ y))
    · intro h φ
      exact (forward_sat φ x).symm.trans ((h (forward φ)).trans (forward_sat φ y))
  have finite_T (label) (x : X) : Set.Finite {x' | T label x x'} := by
    cases label with
    | inl label => exact finite_image label x
    | inr observation =>
        exact (Set.finite_singleton x).subset (fun _ h => h.1)
  -- The following local predicate is the unbundled Cslib IsHomBisimulation.
  let Bisimulation (r : X → X → Prop) := ∀ ⦃s₁ s₂⦄, r s₁ s₂ → ∀ label,
    (∀ s₁', T label s₁ s₁' → ∃ s₂', T label s₂ s₂' ∧ r s₁' s₂') ∧
    (∀ s₂', T label s₂ s₂' → ∃ s₁', T label s₁ s₁' ∧ r s₁' s₂')
  -- Cslib finiteAnd and finiteAnd_iff_forall; the empty list gives truth.
  let finiteAnd (φs : List (HmlFormula (U ⊕ (Σ j, Y j)))) :=
    φs.foldr HmlFormula.conj HmlFormula.top
  have finiteAnd_sat (x : X) (φs) :
      hml_satisfies T x (finiteAnd φs) ↔ ∀ φ ∈ φs, hml_satisfies T x φ := by
    induction φs with
    | nil => simp [finiteAnd, hml_satisfies]
    | cons φ φs ih => simp [finiteAnd, hml_satisfies, ← ih]
  -- Cslib not_theoryEq_satisfies: negate a distinguishing formula if needed.
  have distinguish (x y : X) (h : ¬TheoryEq x y) :
      ∃ φ, hml_satisfies T x φ ∧ ¬hml_satisfies T y φ := by
    by_contra hn
    apply h
    intro φ
    constructor
    · intro hx
      by_contra hy
      exact hn ⟨φ, hx, hy⟩
    · intro hy
      by_contra hx
      exact hn ⟨.neg φ, hx, fun hny => hny hy⟩
  -- Cslib theoryEq_isBisimulation, with propositions and its support inlined.
  have theoryEq_isBisimulation : Bisimulation TheoryEq := by
    intro s1 s2 h label
    let (s : X) : Fintype {s' // T label s s'} := (finite_T label s).fintype
    constructor
    · intro s1' htr
      by_contra hn
      have hdist : ∀ s2' : {s' // T label s2 s'},
          ∃ φ, hml_satisfies T s1' φ ∧ ¬hml_satisfies T s2'.val φ := by
        intro ⟨s2', hs2'⟩
        apply distinguish
        intro heq
        exact hn ⟨s2', hs2', heq⟩
      choose dist_formula hdist_spec using hdist
      let propositions := (Finset.univ : Finset {s' // T label s2 s'}).toList.map dist_formula
      let conjunction := finiteAnd propositions
      have hs1_diamond : hml_satisfies T s1 (.diamond label conjunction) := by
        refine ⟨s1', htr, (finiteAnd_sat s1' propositions).mpr ?_⟩
        intro φ hφ
        obtain ⟨s2', _, rfl⟩ := List.mem_map.mp hφ
        exact (hdist_spec s2').1
      obtain ⟨s2'', htr2, hsat⟩ := (h (.diamond label conjunction)).mp hs1_diamond
      have hmem : dist_formula ⟨s2'', htr2⟩ ∈ propositions :=
        List.mem_map.mpr ⟨⟨s2'', htr2⟩, by simp, rfl⟩
      exact (hdist_spec ⟨s2'', htr2⟩).2 ((finiteAnd_sat s2'' propositions).mp hsat _ hmem)
    · intro s2' htr
      by_contra hn
      have hdist : ∀ s1' : {s' // T label s1 s'},
          ∃ φ, hml_satisfies T s2' φ ∧ ¬hml_satisfies T s1'.val φ := by
        intro ⟨s1', hs1'⟩
        apply distinguish
        intro heq
        exact hn ⟨s1', hs1', fun φ => (heq φ).symm⟩
      choose dist_formula hdist_spec using hdist
      let propositions := (Finset.univ : Finset {s' // T label s1 s'}).toList.map dist_formula
      let conjunction := finiteAnd propositions
      have hs2_diamond : hml_satisfies T s2 (.diamond label conjunction) := by
        refine ⟨s2', htr, (finiteAnd_sat s2' propositions).mpr ?_⟩
        intro φ hφ
        obtain ⟨s1', _, rfl⟩ := List.mem_map.mp hφ
        exact (hdist_spec s1').1
      obtain ⟨s1'', htr1, hsat⟩ := (h (.diamond label conjunction)).mpr hs2_diamond
      have hmem : dist_formula ⟨s1'', htr1⟩ ∈ propositions :=
        List.mem_map.mpr ⟨⟨s1'', htr1⟩, by simp, rfl⟩
      exact (hdist_spec ⟨s1'', htr1⟩).2 ((finiteAnd_sat s1'' propositions).mp hsat _ hmem)
  -- Cslib bisimulation_satisfies: the same induction, with connective rules explicit.
  have bisimulation_satisfies {r : X → X → Prop} (hrb : Bisimulation r)
      {s1 s2 : X} (hr : r s1 s2) (φ : HmlFormula (U ⊕ (Σ j, Y j))) :
      hml_satisfies T s1 φ ↔ hml_satisfies T s2 φ := by
    induction φ generalizing s1 s2 with
    | top => rfl
    | conj φ ψ ihφ ihψ => exact and_congr (ihφ hr) (ihψ hr)
    | neg φ ih => exact not_congr (ih hr)
    | diamond label φ ih =>
        constructor
        · rintro ⟨s1', htr, hsat⟩
          obtain ⟨s2', htr2, hr'⟩ := (hrb hr label).1 s1' htr
          exact ⟨s2', htr2, (ih hr').mp hsat⟩
        · rintro ⟨s2', htr, hsat⟩
          obtain ⟨s1', htr1, hr'⟩ := (hrb hr label).2 s2' htr
          exact ⟨s1', htr1, (ih hr').mpr hsat⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨fun _ _ => Iff.rfl, fun h φ => (h φ).symm,
      fun hxy hyz φ => (hxy φ).trans (hyz φ)⟩
  · intro x y h j
    exact ((h (.atom j (f j x))).mp rfl).symm
  · intro x y h label
    have hm := theoryEq_isBisimulation ((correspondence x y).mp h) (.inl label)
    constructor
    · intro x' hx'
      obtain ⟨y', hy', heq⟩ := hm.1 x' hx'
      exact ⟨y', hy', (correspondence x' y').mpr heq⟩
    · intro y' hy'
      obtain ⟨x', hx', heq⟩ := hm.2 y' hy'
      exact ⟨x', hx', (correspondence x' y').mpr heq⟩
  · intro E _hE htask hmatch x y hxy
    have hb : Bisimulation E := by
      intro s1 s2 h label
      cases label with
      | inl label => exact hmatch s1 s2 h label
      | inr observation =>
          rcases observation with ⟨j, value⟩
          constructor
          · rintro s1' ⟨hs, hvalue⟩
            subst s1'
            exact ⟨s2, ⟨rfl, (htask s1 s2 h j).symm.trans hvalue⟩, h⟩
          · rintro s2' ⟨hs, hvalue⟩
            subst s2'
            exact ⟨s1, ⟨rfl, (htask s1 s2 h j).trans hvalue⟩, h⟩
    exact (correspondence x y).mpr (fun φ => bisimulation_satisfies hb hxy φ)

end D5.S3.ObserverMemory.Algorithms.TaskModalGreatest
