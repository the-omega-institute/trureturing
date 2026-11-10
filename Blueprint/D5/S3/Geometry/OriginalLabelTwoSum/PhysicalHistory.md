# PhysicalHistory

## Abstract

Actual arbitrary-width retained-port wheel steps, literal corners and finite mixed histories.

 The count, handoff and list proofs apply to finite mixed histories. MixedHistory retains every finite prescribed width >=3 and every retained old/interior port. The stronger all-corner recursion is treated in the separate recursion module; an unrestricted arbitrary-plane supplier is not assumed.

## Source text

Lean module source and proofs:

/- GID: D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory

   generality: G

   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory

   mirror-E: none(waiver:arbitrary-width-physical-history)

   anchors: [mathlib/module/Mathlib.SetTheory.Cardinal.Finite, mathlib/module/Mathlib.Logic.Equiv.Set, mathlib/module/Mathlib.Data.Fintype.Sum]

   utility: none

   digest: Actual arbitrary-width retained-port wheel steps, literal corners and finite mixed histories. -/

/-

   Mathematical scope:

   WheelInput, MixedHistory and History range over arbitrary histories and labels. The module constructs actual graph gluing, row/root identities, equivalences and symbolic cardinality/list formulas for these families. These are not bounded enumeration, a certificate checker, numerical reduction or certification of a fixed finite instance; the fixed-width History remains unbounded in its history index.

   

-/

import D5.S3.Geometry.OriginalLabelTwoSum.PhysicalMWheel

import D5.S3.Geometry.OriginalLabelTwoSum.PhysicalCertificate

import D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners

import D5.S3.Geometry.OriginalLabelTwoSum.RowIteration

import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.Logic.Equiv.Set

import Mathlib.Data.Fintype.Sum

Definitions and proofs are in the paired Lean module.

/-!  WheelInput contains only an old actual GraphData,

a retained edge, its orientation, and fresh injective labels. The carrier is

the existing CutTree coproduct: old vertices plus right nonterminals. Its two

injections overlap exactly at the terminal pair. Both physical interfaces are

deleted by PhysicalGlue.graph; no graph or path equation is assumed.

Definitions and proofs are in the paired Lean module.

MixedHistory is the finite prescribed arbitrary-width class. Its constructors

store no root/corner/certificate supplier. In particular the all-corner strong

certificate induction is NOT asserted here. The fixed-W4 History at the end

retains the genuine PhysicalCertificate interface for existing consumers;

the appended canonical handoff/count/list proofs are 

They do not supply the universal mixed-width all-corner constructor. -/

set_option backward.isDefEq.respectTransparency false

set_option backward.isDefEq.respectTransparency.types false

Definitions and proofs are in the paired Lean module.

noncomputable section

open Set Finset SimpleGraph

namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

/-- Geometric inputs only, at ANY actual retained old or interior tree edge.

Freshness concerns current retained labels; inactive original coordinates stay

in V. Fresh vertices are supplied by the explicit coproduct construction. -/

structure WheelInput {A : Type*} (g : GraphData A V) where

  width : Nat

  atLeastThree : 3 ≤ width

  e : V

  retained : e ∈ g.ground

  a : A

  b : A

  edge : g.edge e = s(a,b)

  labels : AllMWheel.Label width ↪ V

  zero : labels 0 = e

  fresh : Disjoint g.ground ((AllMWheel.ground width).image labels)

Definitions and proofs are in the paired Lean module.

/-- Choose only an orientation of the ACTUAL old edge, not a path or graph.

Thus every retained old/interior port is admitted without an orientation

restriction. The fresh wheel vertices are subsequently built canonically. -/

def wheelInputAtPort {A : Type*} (g : GraphData A V) (m : Nat) (hm : 3 ≤ m)

    (e : V) (he : e ∈ g.ground) (f : AllMWheel.Label m ↪ V) (hf0 : f 0 = e)

    (hf : Disjoint g.ground ((AllMWheel.ground m).image f)) : WheelInput g := by

  have all : ∀ d : Sym2 A, ∃ a b : A, d = s(a,b) := by

    apply Sym2.ind

    intro a b

    exact ⟨a,b,rfl⟩

  let h := all (g.edge e)

  let a := Classical.choose h

  let hb := Classical.choose_spec h

  exact {

    width := m

    atLeastThree := hm

    e := e

    retained := he

    a := a

    b := Classical.choose hb

    edge := Classical.choose_spec hb

    labels := f

    zero := hf0

    fresh := hf }

Definitions and proofs are in the paired Lean module.

def physicalWheelStep {A : Type*} (g : GraphData A V) (i : WheelInput g) :

    PhysicalGlue A (AllMWheel.Label i.width) V where

  left := g

  right := PhysicalMWheel.ambientGraph i.width i.atLeastThree i.labels

  selected := AllMWheel.interfaceRow i.width i.atLeastThree

  X := g.ground.erase i.e

  Y := (AllMWheel.ground i.width).image i.labels

  e := i.e

  left_ground := (Finset.insert_erase i.retained).symm

  right_ground := rfl

  e_not_X := Finset.notMem_erase _ _

  e_not_Y := i.zero ▸ PhysicalMWheel.zero_outside_ground i.width i.labels

  disjoint := i.fresh.mono_left (Finset.erase_subset _ _)

  aL := i.a

  bL := i.b

  edge_e := i.edge

Definitions and proofs are in the paired Lean module.

def physicalWheelStep_chords {A : Type*} (g : GraphData A V) (i : WheelInput g) :

    (physicalWheelStep g i).data.chords ≃

      g.chords ⊕ {d : Fin i.width // d ≠ AllMWheel.interfaceRow i.width i.atLeastThree} :=

  (physicalWheelStep g i).uniqueChordEquiv

    (PhysicalMWheel.ambient_uniqueInterface i.width i.atLeastThree i.labels)

Definitions and proofs are in the paired Lean module.

/-- The public missing bridge: both formulas follow from ACTUAL unique tree

paths, first inside the wheel, then through the existing CutPaths substitution.

The index equivalence preserves every old chord index and every noninterface

rim index, including any duplicate old chord indices. -/

theorem physicalWheelStep_rows {A : Type*} (g : GraphData A V) (i : WheelInput g)

    (c : (physicalWheelStep g i).data.chords) :

    (physicalWheelStep g i).data.rows.row c =

      match physicalWheelStep_chords g i c with

      | .inl d => substitute i.e ((AllMWheel.rim i.width i.atLeastThree).image i.labels)

          (g.rows.row d)

      | .inr d => (AllMWheel.rimEdge i.width (by have := i.atLeastThree; omega) d.1).image i.labels := by

  cases c with

  | inl c =>

    change (physicalWheelStep g i).data.rows.row (.inl c) = _

    rw [(physicalWheelStep g i).left_row]

    exact congrArg (fun t => substitute i.e t (g.rows.row c))

      (PhysicalMWheel.ambient_interface_row i.width i.atLeastThree i.labels)

  | inr d =>

    change (physicalWheelStep g i).data.rows.row (.inr d) = _

    rw [(physicalWheelStep g i).right_row]

    exact PhysicalMWheel.ambient_row i.width i.atLeastThree i.labels d.1

Definitions and proofs are in the paired Lean module.

theorem physicalWheelStep_rows_left {A : Type*} (g : GraphData A V) (i : WheelInput g)

    (c : g.chords) :

    (physicalWheelStep g i).data.rows.row ((physicalWheelStep_chords g i).symm (.inl c)) =

      substitute i.e ((AllMWheel.rim i.width i.atLeastThree).image i.labels) (g.rows.row c) := by

  simpa using physicalWheelStep_rows g i ((physicalWheelStep_chords g i).symm (.inl c))

Definitions and proofs are in the paired Lean module.

theorem physicalWheelStep_rows_right {A : Type*} (g : GraphData A V) (i : WheelInput g)

    (d : {d : Fin i.width // d ≠ AllMWheel.interfaceRow i.width i.atLeastThree}) :

    (physicalWheelStep g i).data.rows.row ((physicalWheelStep_chords g i).symm (.inr d)) =

      (AllMWheel.rimEdge i.width (by have := i.atLeastThree; omega) d.1).image i.labels := by

  simpa using physicalWheelStep_rows g i ((physicalWheelStep_chords g i).symm (.inr d))

Definitions and proofs are in the paired Lean module.

/-- Literal physical root before nonempty projection. The right factor is

the actual wheel with its physical 1--2 interface removed. -/

theorem physicalWheelStep_root {A : Type*} (g : GraphData A V) (i : WheelInput g) :

    (physicalWheelStep g i).data.rows.root =

      phi (g.ground.erase i.e) ((AllMWheel.ground i.width).image i.labels)

        ((AllMWheel.tailGround i.width i.atLeastThree).image i.labels)

        (restrict (g.ground.erase i.e) g.rows.root)

        (rawLink (g.ground.erase i.e) i.e g.rows.root)

        (renameFamily i.labels (AllMWheel.pathRoot i.width i.atLeastThree)) := by

  have h := (physicalWheelStep g i).root_formula_of_unique

    (PhysicalMWheel.ambient_uniqueInterface i.width i.atLeastThree i.labels)

  change (physicalWheelStep g i).data.rows.root =

    phi (g.ground.erase i.e) ((AllMWheel.ground i.width).image i.labels)

      ((AllMWheel.ground i.width).image i.labels \

        (PhysicalMWheel.ambientGraph i.width i.atLeastThree i.labels).rows.row

          (AllMWheel.interfaceRow i.width i.atLeastThree))

      (restrict (g.ground.erase i.e) g.rows.root)

      (rawLink (g.ground.erase i.e) i.e g.rows.root)

      (((PhysicalMWheel.ambientGraph i.width i.atLeastThree i.labels).rows.without

        (AllMWheel.interfaceRow i.width i.atLeastThree)).root) at h

  rw [PhysicalMWheel.ambient_interface_row,PhysicalMWheel.ambient_without,

    ← Finset.image_sdiff _ _ i.labels.injective] at h

  exact h

Definitions and proofs are in the paired Lean module.

/-- This is a derived row PRESENTATION, after physicalWheelStep_rows. It is

never substituted for construction of the actual graph or its unique paths. -/

def wheelStepRows {A : Type*} (g : GraphData A V) (i : WheelInput g) : Rows V where

  ground := g.ground.erase i.e ∪ (AllMWheel.ground i.width).image i.labels

  chords := g.chords ⊕ {d : Fin i.width // d ≠ AllMWheel.interfaceRow i.width i.atLeastThree}

  row

    | .inl c => substitute i.e ((AllMWheel.rim i.width i.atLeastThree).image i.labels) (g.rows.row c)

    | .inr d => (AllMWheel.rimEdge i.width (by have := i.atLeastThree; omega) d.1).image i.labels

  row_supported := by

    intro c

    have hs := (physicalWheelStep g i).data.rows.row_supported

      ((physicalWheelStep_chords g i).symm c)

    change (physicalWheelStep g i).data.rows.row _ ⊆

      g.ground.erase i.e ∪ (AllMWheel.ground i.width).image i.labels at hs

    cases c with

    | inl c => simpa only [physicalWheelStep_rows_left] using hs

    | inr d => simpa only [physicalWheelStep_rows_right] using hs

Definitions and proofs are in the paired Lean module.

theorem physicalWheelStep_rowRoot {A : Type*} (g : GraphData A V) (i : WheelInput g) :

    (physicalWheelStep g i).data.rows.root = (wheelStepRows g i).root := by

  apply SetLike.ext

  intro s

  constructor

  · rintro ⟨c,hc⟩

    refine ⟨physicalWheelStep_chords g i c,?_⟩

    have he := physicalWheelStep_rows g i c

    change (physicalWheelStep g i).data.rows.row c =

      (wheelStepRows g i).row (physicalWheelStep_chords g i c) at he

    change s ⊆ (g.ground.erase i.e ∪ (AllMWheel.ground i.width).image i.labels) \ _ at hc ⊢

    simpa only [he] using hc

  · rintro ⟨c,hc⟩

    refine ⟨(physicalWheelStep_chords g i).symm c,?_⟩

    change s ⊆ (g.ground.erase i.e ∪ (AllMWheel.ground i.width).image i.labels) \ _ at hc ⊢

    cases c with

    | inl d => simpa only [wheelStepRows,physicalWheelStep_rows_left] using hc

    | inr d => simpa only [wheelStepRows,physicalWheelStep_rows_right] using hc

Definitions and proofs are in the paired Lean module.

/-- Every original disjoint mask, with the FULL residual ground, singleton

and empty projected rows and all ghosts. Filtering precedes projection. -/

theorem physicalWheelStep_corner {A : Type*} (g : GraphData A V) (i : WheelInput g)

    (A B : Finset V)

    (hA : A ⊆ (physicalWheelStep g i).data.ground)

    (_hB : B ⊆ (physicalWheelStep g i).data.ground) (_hAB : Disjoint A B) :

    HistoryCorners.corner (physicalWheelStep g i).data.ground A B

        (physicalWheelStep g i).data.rows.root =

      (HistoryCorners.cornerRows (wheelStepRows g i) A B).root := by

  rw [physicalWheelStep_rowRoot]

  exact HistoryCorners.corner_root (wheelStepRows g i) A B hA

Definitions and proofs are in the paired Lean module.

/-- Exact indexed old/rim corner rows. In particular no projected row is

silently dropped merely because it is empty or a singleton. -/

theorem physicalWheelStep_corner_row {A : Type*} (g : GraphData A V) (i : WheelInput g)

    (A B : Finset V) (c : (HistoryCorners.cornerRows (wheelStepRows g i) A B).chords) :

    (HistoryCorners.cornerRows (wheelStepRows g i) A B).row c =

      match c.1 with

      | .inl d => substitute i.e ((AllMWheel.rim i.width i.atLeastThree).image i.labels)

          (g.rows.row d) \ B

      | .inr d => ((AllMWheel.rimEdge i.width (by have := i.atLeastThree; omega) d.1).image i.labels) \ B := by

  rcases c with ⟨c,hc⟩

  cases c <;> rfl

Definitions and proofs are in the paired Lean module.

/-- Physical deletion and fresh-block ground, independent of the row model. -/

theorem physicalWheelStep_ground {A : Type*} (g : GraphData A V) (i : WheelInput g) :

    (physicalWheelStep g i).data.ground =

      g.ground.erase i.e ∪ (AllMWheel.ground i.width).image i.labels ∧

    i.e ∉ (physicalWheelStep g i).data.ground := by

  refine ⟨rfl,?_⟩

  intro h

  rcases Finset.mem_union.mp h with ho | hn

  · exact Finset.notMem_erase _ _ ho

  · exact PhysicalMWheel.zero_outside_ground i.width i.labels (i.zero.symm ▸ hn)

Definitions and proofs are in the paired Lean module.

def seedGraph (f : K4.SeedLabel ↪ V) : GraphData (Fin 4) V :=

  PhysicalLabels.data K4.seedGraphData f s(0,0)

Definitions and proofs are in the paired Lean module.

theorem seed_root (f : K4.SeedLabel ↪ V) :

    (seedGraph f).rows.root = delta {f 0} ⊔ delta {f 1} ⊔ delta {f 2} := by

  rw [seedGraph,PhysicalLabels.root,K4.seedOriginalRoot]

  apply SetLike.ext

  intro s

  change (∃ t, (∃ q ∈ ({({0} : Finset K4.SeedLabel),{1},{2}} : Finset (Finset K4.SeedLabel)),

    t ⊆ q) ∧ t.image f = s) ↔ _

  simp only [Finset.mem_insert,Finset.mem_singleton,LowerSet.mem_sup_iff]

  constructor

  · rintro ⟨t,⟨q,hq,ht⟩,rfl⟩

    rcases hq with rfl | rfl | rfl

    · exact Or.inl (Or.inl (by simpa using Finset.image_subset_image ht))

    · exact Or.inl (Or.inr (by simpa using Finset.image_subset_image ht))

    · exact Or.inr (by simpa using Finset.image_subset_image ht)

  · intro hs

    rcases hs with (hs | hs) | hs

    · obtain ⟨t,ht,he⟩ := Finset.subset_image_iff.mp

        (show s ⊆ ({0} : Finset K4.SeedLabel).image f by simpa using hs)

      exact ⟨t,⟨{0},Or.inl rfl,ht⟩,he⟩

    · obtain ⟨t,ht,he⟩ := Finset.subset_image_iff.mp

        (show s ⊆ ({1} : Finset K4.SeedLabel).image f by simpa using hs)

      exact ⟨t,⟨{1},Or.inr (Or.inl rfl),ht⟩,he⟩

    · obtain ⟨t,ht,he⟩ := Finset.subset_image_iff.mp

        (show s ⊆ ({2} : Finset K4.SeedLabel).image f by simpa using hs)

      exact ⟨t,⟨{2},Or.inr (Or.inr rfl),ht⟩,he⟩

Definitions and proofs are in the paired Lean module.

/-- Finite prescribed mixed-width history from the ACTUAL marked K4.

Every step chooses an arbitrary retained port in its current actual graph. -/

inductive MixedHistory : Nat → (A : Type) → GraphData A V → Type _

  | seed (f : K4.SeedLabel ↪ V) : MixedHistory 0 (Fin 4) (seedGraph f)

  | attach {n : Nat} {A : Type} {g : GraphData A V}

      (old : MixedHistory n A g) (i : WheelInput g) :

      MixedHistory (n+1) (physicalWheelStep g i).Carrier (physicalWheelStep g i).data

Definitions and proofs are in the paired Lean module.

/- Fixed-W4 compatibility is a separate genuine constructor, not an arbitrary

width certificate inferred from the fixed-W4 compiler. -/

abbrev Ambient (n ghosts : Nat) := Fin (3 + 4*n + ghosts)

Definitions and proofs are in the paired Lean module.

structure Input {A : Type*} (g : GraphData A V) where

  e : V

  retained : e ∈ g.ground

  a : A

  b : A

  edge : g.edge e = s(a,b)

  labels : Wheel.Label ↪ V

  zero : labels 0 = e

  fresh : Disjoint g.ground (Wheel.Y.image labels)

Definitions and proofs are in the paired Lean module.

/-- Finite fresh W4 block used by PhysicalClosedChain. Its bounds construct

the label injection and freshness; neither is assumed by the closed chain. -/

def blockInput {A : Type} {n ghosts k : Nat}

    (g : GraphData A (Ambient n ghosts)) (hk : k < n)

    (bound : ∀ x ∈ g.ground, x.val < 3 + 4*k)

    (e : Ambient n ghosts) (he : e ∈ g.ground)

    (a b : A) (hedge : g.edge e = s(a,b)) : Input g := by

  let f : Wheel.Label → Ambient n ghosts := fun j =>

    if j = 0 then e else ⟨3 + 4*k + (j.val - 1),by have := j.isLt; omega⟩

  have hb := bound e he

  have hf : Function.Injective f := by

    intro x y h

    by_cases hx : x = 0 <;> by_cases hy : y = 0

    · exact hx.trans hy.symm

    · have hv := congrArg Fin.val h

      simp only [f,if_pos hx,if_neg hy] at hv

      omega

    · have hv := congrArg Fin.val h

      simp only [f,if_neg hx,if_pos hy] at hv

      omega

    · apply Fin.ext

      have hxx : x.val ≠ 0 := fun h0 => hx (Fin.ext h0)

      have hyy : y.val ≠ 0 := fun h0 => hy (Fin.ext h0)

      have hv := congrArg Fin.val h

      simp only [f,if_neg hx,if_neg hy] at hv

      omega

  have fresh : Disjoint g.ground (Wheel.Y.image f) := by

    apply Finset.disjoint_left.mpr

    intro x hx hnew

    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hnew

    have hj0 : j ≠ (0 : Wheel.Label) := by

      intro hz

      subst j

      exact (by decide : (0 : Wheel.Label) ∉ Wheel.Y) hj

    have hv := bound (f j) hx

    simp only [f,if_neg hj0] at hv

    omega

  exact {

    e := e

    retained := he

    a := a

    b := b

    edge := hedge

    labels := ⟨f,hf⟩

    zero := by change f 0 = e; simp only [f,if_pos rfl]

    fresh := fresh }

Definitions and proofs are in the paired Lean module.

def step {A : Type*} (g : GraphData A V) (i : Input g) : PhysicalGlue A Wheel.Label V :=

  PhysicalCertificate.attachment g i.e i.retained i.a i.b i.edge i.labels i.zero i.fresh

Definitions and proofs are in the paired Lean module.

theorem step_rows {A : Type*} (g : GraphData A V) (i : Input g) :

    (∀ c : g.chords, (step g i).data.rows.row (.inl c) =

      substitute i.e (Wheel.R.image i.labels) (g.rows.row c)) ∧

    (∀ d : (Wheel.ambientGraph i.labels).PhysicalSurvivor (0 : Fin 4),

      (step g i).data.rows.row (.inr d) =

        ((![{(1 : Wheel.Label),2},{2,3},{3,4},{4,1}] : Fin 4 → Finset Wheel.Label) d.1).image i.labels) := by

  constructor

  · exact (PhysicalCertificate.attachment_rows g i.e i.retained i.a i.b i.edge

      i.labels i.zero i.fresh).1

  · intro d

    exact ((PhysicalCertificate.attachment_rows g i.e i.retained i.a i.b

      i.edge i.labels i.zero i.fresh).2 d).trans

      ((Wheel.ambient_row i.labels d.1).trans

        (congrArg (fun t : Finset Wheel.Label => t.image i.labels)

          (Wheel.fundamental_rows d.1)))

Definitions and proofs are in the paired Lean module.

inductive History : Nat → (A : Type) → GraphData A V → Type _

  | seed (f : K4.SeedLabel ↪ V) : History 0 (Fin 4) (seedGraph f)

  | attach {n : Nat} {A : Type} {g : GraphData A V} (old : History n A g) (i : Input g) :

      History (n+1) (step g i).Carrier (step g i).data

Definitions and proofs are in the paired Lean module.

/-- Only the fixed-W4 history consumes the existing fixed-W4 native compiler.

This recursion assumes no parent or corner certificate. -/

def certificate {n : Nat} {A : Type} {g : GraphData A V} (h : History n A g) :

    Certificate g.ground g.rows.root := by

  induction h with

  | seed f =>

    let c := renameCertificate f K4.seedGraphCertificate

    exact {

      supported := by rw [seedGraph,PhysicalLabels.root]; exact c.supported

      core := c.core

      critical := c.critical

      vertex := c.vertex

      vertex_mem := c.vertex_mem

      core_supported := c.core_supported

      critical_supported := c.critical_supported

      cells := c.cells

      main := c.main.cast (congrArg project (PhysicalLabels.root K4.seedGraphData f s(0,0))).symm rfl

      separate := c.separate }

  | attach old i ih =>

    exact PhysicalCertificate.certificate _ i.e i.retained i.a i.b i.edge

      i.labels i.zero i.fresh ih

Definitions and proofs are in the paired Lean module.

/-- The fixed-W4 critical counts are consequences of its actual recursive

compiler; this theorem makes no arbitrary-width critical-size assertion. -/

theorem statistics {n : Nat} {A : Type} {g : GraphData A V} (h : History n A g) :

    (certificate h).critical.card = 2 ∧

      ∀ s ∈ (certificate h).critical, s.card = 2*n+1 := by

  induction h with

  | seed f =>

    change (K4.seed.critical.image (fun t => t.image f)).card = 2 ∧

      ∀ s ∈ K4.seed.critical.image (fun t => t.image f), s.card = 2*0+1

    constructor

    · rw [Finset.card_image_of_injective _ (Finset.image_injective f.injective)]

      decide

    · intro s hs

      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hs

      have htcard : t.card = 1 := by

        have hh : t = {1} ∨ t = {2} := by simpa [K4.seed] using ht

        rcases hh with rfl | rfl <;> simp

      rw [Finset.card_image_of_injective _ f.injective,htcard]

  | @attach n A g old i ih =>

    let c := certificate old

    let out := PhysicalCertificate.certificate g i.e i.retained i.a i.b i.edge

      i.labels i.zero i.fresh c

    have hs := PhysicalCertificate.certificate_statistics g i.e i.retained i.a i.b i.edge

      i.labels i.zero i.fresh c

    change out.critical.card = 2 ∧ ∀ s ∈ out.critical, s.card = 2*(n+1)+1

    constructor

    · exact hs.1.trans ih.1

    · intro s hmem

      change s ∈ (PhysicalCertificate.certificate g i.e i.retained i.a i.b i.edge

        i.labels i.zero i.fresh c).critical at hmem

      rw [PhysicalCertificate.certificate_critical] at hmem

      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hmem

      have hsize := hs.2 t ht

      have hold := ih.2 t ht

      omega

Definitions and proofs are in the paired Lean module.

theorem boundaries {n : Nat} {A : Type} {g : GraphData A V} (h : History n A g)

    {s : Finset V} (hs : s ∈ (certificate h).critical) :

    s.Nonempty ∧ s ∉ (certificate h).core ∧

      delta s ⊓ (certificate h).core =

        (⟨{t | t ⊂ s},by intro a b hab hbs; exact lt_of_le_of_lt hab hbs⟩ : Family V) ∧

      ∀ t ∈ (certificate h).critical, s ⊆ t → s = t := by

  let c := certificate h

  exact ⟨c.cells.nonempty s hs,c.cells.absent s hs,

    critical_intersection c.core c.critical c.cells hs,c.cells.antichain s hs⟩

Definitions and proofs are in the paired Lean module.

theorem survives {n : Nat} {A : Type} {g : GraphData A V} (h : History n A g) :

    (certificate h).vertex ∈ g.ground :=

  (certificate h).core_supported _ (certificate h).vertex_mem (by simp)

Definitions and proofs are in the paired Lean module.

/-- Finiteness comes from the actual K4 carrier and the actual cut coproduct,

not from a finite-cardinality hypothesis on a purported output graph. -/

theorem finite_carrier {n : Nat} {A : Type} {g : GraphData A V}

    (h : History n A g) : Finite A := by

  induction h with

  | seed f => infer_instance

  | @attach n A g old i ih =>

    letI : Finite A := ih

    change Finite (A ⊕ {z : Wheel.Label // z ≠ 1 ∧ z ≠ 2})

    infer_instance

Definitions and proofs are in the paired Lean module.

/-- The right summand is the actual hub and the two nonterminal rim vertices.

The two terminals are identified with old vertices, so only three are new. -/

theorem vertex_card {n : Nat} {A : Type} {g : GraphData A V}

    (h : History n A g) : Nat.card A = 4 + 3*n := by

  induction h with

  | seed f => simp only [Nat.card_eq_fintype_card,Fintype.card_fin] <;> omega

  | @attach n A g old i ih =>

    letI : Finite A := finite_carrier old

    change Nat.card (A ⊕ {z : Wheel.Label // z ≠ 1 ∧ z ≠ 2}) = _

    have hright : Nat.card {z : Wheel.Label // z ≠ 1 ∧ z ≠ 2} = 3 := by

      rw [Nat.card_eq_fintype_card]

      decide

    rw [Nat.card_sum,hright,ih]

    omega

Definitions and proofs are in the paired Lean module.

/-- Erasing the retained interface and adjoining four injectively labelled

fresh spokes increases the ACTUAL retained ground by three. -/

theorem ground_card {n : Nat} {A : Type} {g : GraphData A V}

    (h : History n A g) : g.ground.card = 3 + 3*n := by

  induction h with

  | seed f =>

    change (Finset.univ.image f).card = _

    rw [Finset.card_image_of_injective _ f.injective]

    simp only [Finset.card_univ,Fintype.card_fin]

  | @attach n A g old i ih =>

    change (g.ground.erase i.e ∪ Wheel.Y.image i.labels).card = _

    rw [Finset.card_union_of_disjoint

      (i.fresh.mono_left (Finset.erase_subset _ _)),

      Finset.card_image_of_injective _ i.labels.injective]

    have hy : Wheel.Y.card = 4 := by decide

    have he := Finset.card_erase_add_one i.retained

    rw [hy]

    omega

Definitions and proofs are in the paired Lean module.

/-- The actual tree-edge labels give an equivalence, including surjectivity

onto physical unordered edges. No chord injectivity or finite carrier is used. -/

def treeEdgeEquiv {A : Type*} (g : GraphData A V) :

    {i // i ∈ g.ground} ≃ {d : Sym2 A // d ∈ g.tree.edgeSet} := by

  let f : {i // i ∈ g.ground} → {d : Sym2 A // d ∈ g.tree.edgeSet} := fun i =>

    ⟨g.edge i.1,by

      have hm : ∀ d : Sym2 A, g.edge i.1 = d → d ∈ g.tree.edgeSet := by

        apply Sym2.ind

        intro x y he

        exact (g.tree_edges x y).mpr ⟨i.1,i.2,he⟩

      exact hm _ rfl⟩

  apply Equiv.ofBijective f

  constructor

  · intro i j he

    apply Subtype.ext

    exact g.labels_injective i.1 i.2 j.1 j.2 (congrArg Subtype.val he)

  · rintro ⟨d,hd⟩

    induction d using Sym2.ind with

    | h x y =>

      obtain ⟨i,hi,he⟩ := (g.tree_edges x y).mp hd

      exact ⟨⟨i,hi⟩,Subtype.ext he⟩

Definitions and proofs are in the paired Lean module.

/-- Count PHYSICAL tree edges through their proved original-label bijection. -/

theorem tree_edge_card {n : Nat} {A : Type} {g : GraphData A V}

    (h : History n A g) :

    Nat.card {d : Sym2 A // d ∈ g.tree.edgeSet} = 3 + 3*n := by

  rw [← Nat.card_congr (treeEdgeEquiv g),Nat.card_eq_fintype_card,Fintype.card_coe]

  exact ground_card h

Definitions and proofs are in the paired Lean module.

/-- Both deleted physical graph images are disjoint by the existing terminal

intersection theorem. This equivalence does not count chord indices. -/

def physicalEdgeEquiv {A B : Type*} (s : PhysicalGlue A B V) :

    {d : Sym2 s.Carrier // d ∈ s.data.graph.edgeSet} ≃

      {d : Sym2 A // d ∈ s.leftKept.edgeSet} ⊕

        {d : Sym2 B // d ∈ s.rightKept.edgeSet} := by

  classical

  exact ((Set.equivOfEq s.graph_edgeSet).trans

    (Equiv.Set.union s.graph_images_disjoint)).trans

      (Equiv.sumCongr

        (Equiv.Set.image (Sym2.map s.qL) s.leftKept.edgeSet

          (Sym2.map.injective s.input.qL_injective)).symm

        (Equiv.Set.image (Sym2.map s.qR) s.rightKept.edgeSet

          (Sym2.map.injective s.input.qR_injective)).symm)

Definitions and proofs are in the paired Lean module.

private theorem deleted_card {A : Type*} [Finite A] (G : SimpleGraph A)

    (d : Sym2 A) (hd : d ∈ G.edgeSet) :

    Nat.card {z : Sym2 A // z ∈ (G.deleteEdges {d}).edgeSet} + 1 =

      Nat.card {z : Sym2 A // z ∈ G.edgeSet} := by

  classical

  have hu : (G.edgeSet \ {d}) ∪ {d} = G.edgeSet := by

    ext z

    simp only [Set.mem_union,Set.mem_diff,Set.mem_singleton_iff]

    constructor

    · rintro (⟨hz,_⟩ | rfl)

      · exact hz

      · exact hd

    · intro hz

      by_cases he : z = d

      · exact Or.inr he

      · exact Or.inl ⟨hz,he⟩

  have hdj : Disjoint (G.edgeSet \ {d}) ({d} : Set (Sym2 A)) :=

    Set.disjoint_left.mpr (fun _ hz hs => hz.2 hs)

  have hc := Nat.card_congr ((Set.equivOfEq hu).symm.trans (Equiv.Set.union hdj))

  rw [Nat.card_sum] at hc

  have hone : Nat.card ({d} : Set (Sym2 A)) = 1 := by

    rw [Nat.card_eq_fintype_card]

    exact Fintype.card_unique

  rw [hone] at hc

  simpa only [SimpleGraph.edgeSet_deleteEdges] using hc.symm

Definitions and proofs are in the paired Lean module.

/-- Count graph edges from the actual physical disjoint edge union. The old

retained tree interface removes one old edge; the W4 rim interface removes

one of its eight edges. Thus each actual attachment adds six graph edges. -/

theorem graph_edge_card {n : Nat} {A : Type} {g : GraphData A V}

    (h : History n A g) :

    Nat.card {d : Sym2 A // d ∈ g.graph.edgeSet} = 6 + 6*n := by

  induction h with

  | seed f =>

    change Nat.card {d : Sym2 (Fin 4) // d ∈ (⊤ : SimpleGraph (Fin 4)).edgeSet} = _

    rw [Nat.card_eq_fintype_card]

    decide

  | @attach n A g old i ih =>

    letI : Finite A := finite_carrier old

    let s := step g i

    have he : g.edge i.e ∈ g.graph.edgeSet := by

      rw [i.edge]

      exact g.tree_le ((g.tree_edges i.a i.b).mpr ⟨i.e,i.retained,i.edge⟩)

    have hold := deleted_card g.graph (g.edge i.e) he

    have hright : Nat.card {d : Sym2 Wheel.Label //

        d ∈ (Wheel.wheelGraphData.graph.deleteEdges

          {Wheel.wheelGraphData.kappa (0 : Fin 4)}).edgeSet} = 7 := by

      letI : DecidableRel Wheel.wheelGraphData.graph.Adj := by

        intro x y

        change Decidable ((x ≠ y ∧ (x = 0 ∨ y = 0)) ∨

          ∃ j : Fin 4, s(x,y) =

            s((![(1,2),(2,3),(3,4),(4,1)] j : Wheel.Label × Wheel.Label).1,

              (![(1,2),(2,3),(3,4),(4,1)] j : Wheel.Label × Wheel.Label).2))

        infer_instance

      letI : Fintype {d : Sym2 Wheel.Label //

          d ∈ (Wheel.wheelGraphData.graph.deleteEdges

            {Wheel.wheelGraphData.kappa (0 : Fin 4)}).edgeSet} :=

        SimpleGraph.fintypeEdgeSet _

      rw [Nat.card_eq_fintype_card]

      decide

    have hc := Nat.card_congr (physicalEdgeEquiv s)

    rw [Nat.card_sum] at hc

    change Nat.card {d : Sym2 s.Carrier // d ∈ s.data.graph.edgeSet} = _

    change Nat.card {d : Sym2 s.Carrier // d ∈ s.data.graph.edgeSet} =

      Nat.card {d : Sym2 A // d ∈ (g.graph.deleteEdges {g.edge i.e}).edgeSet} +

      Nat.card {d : Sym2 Wheel.Label // d ∈ (Wheel.wheelGraphData.graph.deleteEdges

        {Wheel.wheelGraphData.kappa (0 : Fin 4)}).edgeSet} at hc

    rw [hc,hright]

    omega

Definitions and proofs are in the paired Lean module.

/-- An OUTPUT relation: every actual physical chord index is retained, the

full original ground agrees, and EVERY path-derived row is identified. -/

structure RowBinding {A : Type*} (g : GraphData A V) (r : Rows V) where

  index : g.chords ≃ r.chords

  ground : g.ground = r.ground

  row : ∀ c : g.chords, g.rows.row c = r.row (index c)

Definitions and proofs are in the paired Lean module.

/-- Construct the actual existing row history, recursively from K4 and the

physical path-row theorem. No row history or binding is an input premise. -/

def handoff {n : Nat} {A : Type} {g : GraphData A V} (h : History n A g) :

    Σ r : Rows V, RowHistory n r × RowBinding g r := by

  induction h with

  | seed f =>

    exact ⟨renameRows f K4.seedGraphData.rows,RowHistory.seed f,{

      index := Equiv.refl _

      ground := rfl

      row := fun c => PhysicalLabels.row K4.seedGraphData f s(0,0) c }⟩

  | @attach n A g old i ih =>

    let r := ih.1

    let b := ih.2.2

    have he : i.e ∈ r.ground := b.ground ▸ i.retained

    have hf : Disjoint r.ground (Wheel.Y.image i.labels) := b.ground ▸ i.fresh

    refine ⟨appendWheelRows r i.e he i.labels i.zero,

      RowHistory.attach ih.2.1 i.e he i.labels i.zero hf,{

        index := (PhysicalCertificate.attachment_chords g i.e i.retained i.a i.b

          i.edge i.labels i.zero i.fresh).trans

            (Equiv.sumCongr b.index (Equiv.refl _))

        ground := ?_

        row := ?_ }⟩

    · change g.ground.erase i.e ∪ Wheel.Y.image i.labels =

        r.ground.erase i.e ∪ Wheel.Y.image i.labels

      rw [b.ground]

    · intro c

      cases c with

      | inl c =>

        change (step g i).data.rows.row (.inl c) =

          substitute i.e (Wheel.R.image i.labels) (r.row (b.index c))

        rw [(step_rows g i).1 c,b.row c]

      | inr d =>

        change (step g i).data.rows.row (.inr d) =

          (Wheel.wheelGraphData.rows.row d.1).image i.labels

        exact ((step g i).right_row d).trans (Wheel.ambient_row i.labels d.1)

Definitions and proofs are in the paired Lean module.

/-- Raw equality before nonempty projection; the inverse index equivalence

proves the reverse inclusion, so no duplicate row index is silently omitted. -/

theorem root_handoff {n : Nat} {A : Type} {g : GraphData A V} (h : History n A g) :

    g.rows.root = (handoff h).1.root := by

  apply SetLike.ext

  intro s

  constructor

  · rintro ⟨c,hc⟩

    refine ⟨(handoff h).2.2.index c,?_⟩

    change s ⊆ g.ground \ g.rows.row c at hc

    simpa only [(handoff h).2.2.ground,(handoff h).2.2.row c] using hc

  · rintro ⟨c,hc⟩

    refine ⟨(handoff h).2.2.index.symm c,?_⟩

    change s ⊆ g.ground \ g.rows.row ((handoff h).2.2.index.symm c)

    simpa only [(handoff h).2.2.ground,(handoff h).2.2.row,

      Equiv.apply_symm_apply] using hc

Definitions and proofs are in the paired Lean module.

/-- Physical certificate data agrees with the independent row seed recursion.

The terminal update includes the case when the selected port was the core point. -/

theorem schedule_data {n : Nat} {A : Type} {g : GraphData A V} (h : History n A g) :

    (certificate h).critical = rowHistoryCriticalSchedule (handoff h).2.1 ∧

    (certificate h).vertex = rowHistoryVertexSchedule (handoff h).2.1 := by

  induction h with

  | seed f => exact ⟨rfl,rfl⟩

  | @attach n A g old i ih =>

    change (PhysicalCertificate.certificate g i.e i.retained i.a i.b i.edge

      i.labels i.zero i.fresh (certificate old)).critical =

        (rowHistoryCriticalSchedule (handoff old).2.1).image

          (wheelCell i.e (i.labels 1) (i.labels 3) (i.labels 4)) ∧

      (PhysicalCertificate.certificate g i.e i.retained i.a i.b i.edge

        i.labels i.zero i.fresh (certificate old)).vertex =

        finishVertex ((handoff old).1.ground.erase i.e) (Wheel.R.image i.labels)

          i.e (rowHistoryVertexSchedule (handoff old).2.1) _

    constructor

    · rw [PhysicalCertificate.certificate_critical,ih.1]

    · rw [PhysicalCertificate.certificate_vertex,ih.2,

        (handoff old).2.2.ground]

Definitions and proofs are in the paired Lean module.

/-- ACTUAL physical main pairs equal the independently enumerated row schedule.

The induction consumes the previous equality through the one-step flatMap;

this is not a list re-extracted from the target certificate. -/

theorem main_order {n : Nat} {A : Type} {g : GraphData A V} (h : History n A g) :

    orderedPairs (certificate h).main = rowHistoryMainSchedule (handoff h).2.1 := by

  induction h with

  | seed f =>

    change orderedPairs (certificate (History.seed f)).main = []

    simp only [certificate, renameCertificate, orderedPairs_cast]

    unfold orderedPairs orderedPair

    simpa only [K4.seedGraphCertificate,K4.seed,

      FiniteRelativeSimplicialCollapse.Sequence.pairs_cast,

      FiniteRelativeSimplicialCollapse.Sequence.pairs,List.map_nil] using

      renameSequence_pairs f K4.seedGraphCertificate.main

  | @attach n A g old i ih =>

    change orderedPairs (PhysicalCertificate.certificate g i.e i.retained i.a i.b

      i.edge i.labels i.zero i.fresh (certificate old)).main =

        WheelSupplier.oneStepMainFrom i.e i.labels

          (rowHistoryCriticalSchedule (handoff old).2.1)

          (rowHistoryMainSchedule (handoff old).2.1)

    rw [PhysicalCertificate.certificate_main_order,ih,(schedule_data old).1]

Definitions and proofs are in the paired Lean module.

/-- ACTUAL physical core pairs equal the independent separate schedule, on

C ALONE. Collars precede old-core replay, followed by the terminal; skipped

pairs retain their ORIGINAL order in the reused compiler. -/

theorem separate_order {n : Nat} {A : Type} {g : GraphData A V} (h : History n A g) :

    orderedPairs (certificate h).separate = rowHistorySeparateSchedule (handoff h).2.1 := by

  induction h with

  | seed f =>

    change orderedPairs (certificate (History.seed f)).separate = []

    simp only [certificate, renameCertificate, orderedPairs_cast]

    unfold orderedPairs orderedPair

    simpa only [K4.seedGraphCertificate,K4.seed,

      FiniteRelativeSimplicialCollapse.Sequence.pairs_cast,

      FiniteRelativeSimplicialCollapse.Sequence.pairs,List.map_nil] using

      renameSequence_pairs f K4.seedGraphCertificate.separate

  | @attach n A g old i ih =>

    change orderedPairs (PhysicalCertificate.certificate g i.e i.retained i.a i.b

      i.edge i.labels i.zero i.fresh (certificate old)).separate =

        WheelSupplier.oneStepSeparateFrom ((handoff old).1.ground.erase i.e)

          i.e i.labels (rowHistoryCriticalSchedule (handoff old).2.1)

          (rowHistoryVertexSchedule (handoff old).2.1)

          (rowHistorySeparateSchedule (handoff old).2.1)

    rw [PhysicalCertificate.certificate_separate_order,ih,

      (schedule_data old).1,(schedule_data old).2,(handoff old).2.2.ground]

Definitions and proofs are in the paired Lean module.

/-- Actual total number of new vertices along a prescribed mixed history.

No constant-width specialization appears in this recursion. -/

def mixed_excess {n : Nat} {A : Type} {g : GraphData A V} (h : MixedHistory n A g) : Nat := by

  induction h with

  | seed f => exact 0

  | attach old i ih => exact ih + (i.width - 1)

Definitions and proofs are in the paired Lean module.

/-- Every finite mixed physical history has a finite actual coproduct carrier. -/

theorem mixed_finite_carrier {n : Nat} {A : Type} {g : GraphData A V}

    (h : MixedHistory n A g) : Finite A := by

  induction h with

  | seed f => infer_instance

  | @attach n A g old i ih =>

    letI : Finite A := ih

    change Finite (A ⊕ {z : AllMWheel.Label i.width //

      z ≠ (physicalWheelStep g i).input.aR ∧ z ≠ (physicalWheelStep g i).input.bR})

    infer_instance

Definitions and proofs are in the paired Lean module.

private theorem nonterminal_card {B : Type*} [Fintype B] [DecidableEq B]

    (a b : B) (hab : a ≠ b) :

    Nat.card {z : B // z ≠ a ∧ z ≠ b} = Nat.card B - 2 := by

  let e : {z : B // z ≠ a ∧ z ≠ b} ≃ {z : B // ¬ (z = a ∨ z = b)} :=

    Equiv.subtypeEquivRight (fun _ => not_or.symm)

  rw [Nat.card_congr e,Nat.card_eq_fintype_card,

    Fintype.card_subtype_compl,Fintype.card_subtype_eq_or_eq_of_ne hab,

    Nat.card_eq_fintype_card]

Definitions and proofs are in the paired Lean module.

/-- Arbitrary widths and every retained old/interior port: count the actual

carrier, using the right two-terminal complement rather than assuming a count. -/

theorem mixed_vertex_card {n : Nat} {A : Type} {g : GraphData A V}

    (h : MixedHistory n A g) : Nat.card A = 4 + mixed_excess h := by

  induction h with

  | seed f => simp only [mixed_excess,Nat.card_eq_fintype_card,Fintype.card_fin]

  | @attach n A g old i ih =>

    letI : Finite A := mixed_finite_carrier old

    let s := physicalWheelStep g i

    have hc : Nat.card s.Carrier = Nat.card A + (i.width - 1) := by

      change Nat.card (A ⊕ {z : AllMWheel.Label i.width //

        z ≠ s.input.aR ∧ z ≠ s.input.bR}) = _

      rw [Nat.card_sum,nonterminal_card s.input.aR s.input.bR s.input.neR]

      have hw : Nat.card (AllMWheel.Label i.width) = i.width + 1 := by

        simp only [Nat.card_eq_fintype_card,Fintype.card_fin]

      rw [hw]

      have hm := i.atLeastThree

      omega

    change Nat.card s.Carrier = 4 + (mixed_excess old + (i.width - 1))

    rw [hc,ih]

    omega

Definitions and proofs are in the paired Lean module.

/-- The physical retained ground grows by width-1, with the deleted interface

absent and the full original ambient type, including inactive ghosts, retained. -/

theorem mixed_ground_card {n : Nat} {A : Type} {g : GraphData A V}

    (h : MixedHistory n A g) : g.ground.card = 3 + mixed_excess h := by

  induction h with

  | seed f =>

    change (Finset.univ.image f).card = 3 + 0

    rw [Finset.card_image_of_injective _ f.injective]

    simp only [Finset.card_univ,Fintype.card_fin]

  | @attach n A g old i ih =>

    change (g.ground.erase i.e ∪ (AllMWheel.ground i.width).image i.labels).card =

      3 + (mixed_excess old + (i.width - 1))

    rw [Finset.card_union_of_disjoint

      (i.fresh.mono_left (Finset.erase_subset _ _)),

      Finset.card_image_of_injective _ i.labels.injective]

    have he := Finset.card_erase_add_one i.retained

    have hw : (AllMWheel.ground i.width).card + 1 = i.width + 1 := by

      change ((Finset.univ : Finset (AllMWheel.Label i.width)).erase 0).card + 1 = _

      simpa only [Finset.card_univ,Fintype.card_fin] using

        (Finset.card_erase_add_one (Finset.mem_univ (0 : AllMWheel.Label i.width)))

    have hm := i.atLeastThree

    omega

Definitions and proofs are in the paired Lean module.

/-- Physical tree-edge count for the unchanged arbitrary-width mixed class. -/

theorem mixed_tree_edge_card {n : Nat} {A : Type} {g : GraphData A V}

    (h : MixedHistory n A g) :

    Nat.card {d : Sym2 A // d ∈ g.tree.edgeSet} = 3 + mixed_excess h := by

  rw [← Nat.card_congr (treeEdgeEquiv g),Nat.card_eq_fintype_card,Fintype.card_coe]

  exact mixed_ground_card h

Definitions and proofs are in the paired Lean module.

end D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory

Definitions and proofs are in the paired Lean module.

**Definition 1.1 (WheelInput).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.WheelInput`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.WheelInput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Preserved frozen predecessor declaration. 

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

structure WheelInput {A : Type*} (g : GraphData A V) where

  width : Nat

  atLeastThree : 3 ≤ width

  e : V

  retained : e ∈ g.ground

  a : A

  b : A

  edge : g.edge e = s(a,b)

  labels : AllMWheel.Label width ↪ V

  zero : labels 0 = e

  fresh : Disjoint g.ground ((AllMWheel.ground width).image labels)

**Definition 1.2 (wheelInputAtPort).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.wheelInputAtPort`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.wheelInputAtPort` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Preserved frozen predecessor declaration. 

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

def wheelInputAtPort {A : Type*} (g : GraphData A V) (m : Nat) (hm : 3 ≤ m)

    (e : V) (he : e ∈ g.ground) (f : AllMWheel.Label m ↪ V) (hf0 : f 0 = e)

    (hf : Disjoint g.ground ((AllMWheel.ground m).image f)) : WheelInput g := by

  have all : ∀ d : Sym2 A, ∃ a b : A, d = s(a,b) := by

    apply Sym2.ind

    intro a b

    exact ⟨a,b,rfl⟩

  let h := all (g.edge e)

  let a := Classical.choose h

  let hb := Classical.choose_spec h

  exact {

    width := m

    atLeastThree := hm

    e := e

    retained := he

    a := a

    b := Classical.choose hb

    edge := Classical.choose_spec hb

    labels := f

    zero := hf0

    fresh := hf }

**Definition 1.3 (physicalWheelStep).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.physicalWheelStep`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.physicalWheelStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Preserved frozen predecessor declaration. 

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

def physicalWheelStep {A : Type*} (g : GraphData A V) (i : WheelInput g) :

    PhysicalGlue A (AllMWheel.Label i.width) V where

  left := g

  right := PhysicalMWheel.ambientGraph i.width i.atLeastThree i.labels

  selected := AllMWheel.interfaceRow i.width i.atLeastThree

  X := g.ground.erase i.e

  Y := (AllMWheel.ground i.width).image i.labels

  e := i.e

  left_ground := (Finset.insert_erase i.retained).symm

  right_ground := rfl

  e_not_X := Finset.notMem_erase _ _

  e_not_Y := i.zero ▸ PhysicalMWheel.zero_outside_ground i.width i.labels

  disjoint := i.fresh.mono_left (Finset.erase_subset _ _)

  aL := i.a

  bL := i.b

  edge_e := i.edge

**Definition 1.4 (physicalWheelStep_chords).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.physicalWheelStep_chords`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.physicalWheelStep_chords` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Preserved frozen predecessor declaration. 

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

def physicalWheelStep_chords {A : Type*} (g : GraphData A V) (i : WheelInput g) :

    (physicalWheelStep g i).data.chords ≃

      g.chords ⊕ {d : Fin i.width // d ≠ AllMWheel.interfaceRow i.width i.atLeastThree} :=

  (physicalWheelStep g i).uniqueChordEquiv

    (PhysicalMWheel.ambient_uniqueInterface i.width i.atLeastThree i.labels)

**Theorem 1.5 (physicalWheelStep_rows).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.physicalWheelStep_rows`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.physicalWheelStep_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Preserved frozen predecessor declaration. 

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

theorem physicalWheelStep_rows {A : Type*} (g : GraphData A V) (i : WheelInput g)

    (c : (physicalWheelStep g i).data.chords) :

    (physicalWheelStep g i).data.rows.row c =

      match physicalWheelStep_chords g i c with

      | .inl d => substitute i.e ((AllMWheel.rim i.width i.atLeastThree).image i.labels)

          (g.rows.row d)

      | .inr d => (AllMWheel.rimEdge i.width (by have := i.atLeastThree; omega) d.1).image i.labels := by

  cases c with

  | inl c =>

    change (physicalWheelStep g i).data.rows.row (.inl c) = _

    rw [(physicalWheelStep g i).left_row]

    exact congrArg (fun t => substitute i.e t (g.rows.row c))

      (PhysicalMWheel.ambient_interface_row i.width i.atLeastThree i.labels)

  | inr d =>

    change (physicalWheelStep g i).data.rows.row (.inr d) = _

    rw [(physicalWheelStep g i).right_row]

    exact PhysicalMWheel.ambient_row i.width i.atLeastThree i.labels d.1

**Theorem 1.6 (physicalWheelStep_rows_left).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.physicalWheelStep_rows_left`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.physicalWheelStep_rows_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Preserved frozen predecessor declaration. 

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

theorem physicalWheelStep_rows_left {A : Type*} (g : GraphData A V) (i : WheelInput g)

    (c : g.chords) :

    (physicalWheelStep g i).data.rows.row ((physicalWheelStep_chords g i).symm (.inl c)) =

      substitute i.e ((AllMWheel.rim i.width i.atLeastThree).image i.labels) (g.rows.row c) := by

  simpa using physicalWheelStep_rows g i ((physicalWheelStep_chords g i).symm (.inl c))

**Theorem 1.7 (physicalWheelStep_rows_right).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.physicalWheelStep_rows_right`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.physicalWheelStep_rows_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Preserved frozen predecessor declaration. 

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

theorem physicalWheelStep_rows_right {A : Type*} (g : GraphData A V) (i : WheelInput g)

    (d : {d : Fin i.width // d ≠ AllMWheel.interfaceRow i.width i.atLeastThree}) :

    (physicalWheelStep g i).data.rows.row ((physicalWheelStep_chords g i).symm (.inr d)) =

      (AllMWheel.rimEdge i.width (by have := i.atLeastThree; omega) d.1).image i.labels := by

  simpa using physicalWheelStep_rows g i ((physicalWheelStep_chords g i).symm (.inr d))

**Theorem 1.8 (physicalWheelStep_root).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.physicalWheelStep_root`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.physicalWheelStep_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Preserved frozen predecessor declaration. 

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

theorem physicalWheelStep_root {A : Type*} (g : GraphData A V) (i : WheelInput g) :

    (physicalWheelStep g i).data.rows.root =

      phi (g.ground.erase i.e) ((AllMWheel.ground i.width).image i.labels)

        ((AllMWheel.tailGround i.width i.atLeastThree).image i.labels)

        (restrict (g.ground.erase i.e) g.rows.root)

        (rawLink (g.ground.erase i.e) i.e g.rows.root)

        (renameFamily i.labels (AllMWheel.pathRoot i.width i.atLeastThree)) := by

  have h := (physicalWheelStep g i).root_formula_of_unique

    (PhysicalMWheel.ambient_uniqueInterface i.width i.atLeastThree i.labels)

  change (physicalWheelStep g i).data.rows.root =

    phi (g.ground.erase i.e) ((AllMWheel.ground i.width).image i.labels)

      ((AllMWheel.ground i.width).image i.labels \

        (PhysicalMWheel.ambientGraph i.width i.atLeastThree i.labels).rows.row

          (AllMWheel.interfaceRow i.width i.atLeastThree))

      (restrict (g.ground.erase i.e) g.rows.root)

      (rawLink (g.ground.erase i.e) i.e g.rows.root)

      (((PhysicalMWheel.ambientGraph i.width i.atLeastThree i.labels).rows.without

        (AllMWheel.interfaceRow i.width i.atLeastThree)).root) at h

  rw [PhysicalMWheel.ambient_interface_row,PhysicalMWheel.ambient_without,

    ← Finset.image_sdiff _ _ i.labels.injective] at h

  exact h

**Definition 1.9 (wheelStepRows).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.wheelStepRows`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.wheelStepRows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Preserved frozen predecessor declaration. 

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

def wheelStepRows {A : Type*} (g : GraphData A V) (i : WheelInput g) : Rows V where

  ground := g.ground.erase i.e ∪ (AllMWheel.ground i.width).image i.labels

  chords := g.chords ⊕ {d : Fin i.width // d ≠ AllMWheel.interfaceRow i.width i.atLeastThree}

  row

    | .inl c => substitute i.e ((AllMWheel.rim i.width i.atLeastThree).image i.labels) (g.rows.row c)

    | .inr d => (AllMWheel.rimEdge i.width (by have := i.atLeastThree; omega) d.1).image i.labels

  row_supported := by

    intro c

    have hs := (physicalWheelStep g i).data.rows.row_supported

      ((physicalWheelStep_chords g i).symm c)

    change (physicalWheelStep g i).data.rows.row _ ⊆

      g.ground.erase i.e ∪ (AllMWheel.ground i.width).image i.labels at hs

    cases c with

    | inl c => simpa only [physicalWheelStep_rows_left] using hs

    | inr d => simpa only [physicalWheelStep_rows_right] using hs

**Theorem 1.10 (physicalWheelStep_rowRoot).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.physicalWheelStep_rowRoot`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.physicalWheelStep_rowRoot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Preserved frozen predecessor declaration. 

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

theorem physicalWheelStep_rowRoot {A : Type*} (g : GraphData A V) (i : WheelInput g) :

    (physicalWheelStep g i).data.rows.root = (wheelStepRows g i).root := by

  apply SetLike.ext

  intro s

  constructor

  · rintro ⟨c,hc⟩

    refine ⟨physicalWheelStep_chords g i c,?_⟩

    have he := physicalWheelStep_rows g i c

    change (physicalWheelStep g i).data.rows.row c =

      (wheelStepRows g i).row (physicalWheelStep_chords g i c) at he

    change s ⊆ (g.ground.erase i.e ∪ (AllMWheel.ground i.width).image i.labels) \ _ at hc ⊢

    simpa only [he] using hc

  · rintro ⟨c,hc⟩

    refine ⟨(physicalWheelStep_chords g i).symm c,?_⟩

    change s ⊆ (g.ground.erase i.e ∪ (AllMWheel.ground i.width).image i.labels) \ _ at hc ⊢

    cases c with

    | inl d => simpa only [wheelStepRows,physicalWheelStep_rows_left] using hc

    | inr d => simpa only [wheelStepRows,physicalWheelStep_rows_right] using hc

**Theorem 1.11 (physicalWheelStep_corner).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.physicalWheelStep_corner`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.physicalWheelStep_corner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Preserved frozen predecessor declaration. 

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

theorem physicalWheelStep_corner {A : Type*} (g : GraphData A V) (i : WheelInput g)

    (A B : Finset V)

    (hA : A ⊆ (physicalWheelStep g i).data.ground)

    (_hB : B ⊆ (physicalWheelStep g i).data.ground) (_hAB : Disjoint A B) :

    HistoryCorners.corner (physicalWheelStep g i).data.ground A B

        (physicalWheelStep g i).data.rows.root =

      (HistoryCorners.cornerRows (wheelStepRows g i) A B).root := by

  rw [physicalWheelStep_rowRoot]

  exact HistoryCorners.corner_root (wheelStepRows g i) A B hA

**Theorem 1.12 (physicalWheelStep_corner_row).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.physicalWheelStep_corner_row`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.physicalWheelStep_corner_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Preserved frozen predecessor declaration. 

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

theorem physicalWheelStep_corner_row {A : Type*} (g : GraphData A V) (i : WheelInput g)

    (A B : Finset V) (c : (HistoryCorners.cornerRows (wheelStepRows g i) A B).chords) :

    (HistoryCorners.cornerRows (wheelStepRows g i) A B).row c =

      match c.1 with

      | .inl d => substitute i.e ((AllMWheel.rim i.width i.atLeastThree).image i.labels)

          (g.rows.row d) \ B

      | .inr d => ((AllMWheel.rimEdge i.width (by have := i.atLeastThree; omega) d.1).image i.labels) \ B := by

  rcases c with ⟨c,hc⟩

  cases c <;> rfl

**Theorem 1.13 (physicalWheelStep_ground).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.physicalWheelStep_ground`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.physicalWheelStep_ground` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Preserved frozen predecessor declaration. 

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

theorem physicalWheelStep_ground {A : Type*} (g : GraphData A V) (i : WheelInput g) :

    (physicalWheelStep g i).data.ground =

      g.ground.erase i.e ∪ (AllMWheel.ground i.width).image i.labels ∧

    i.e ∉ (physicalWheelStep g i).data.ground := by

  refine ⟨rfl,?_⟩

  intro h

  rcases Finset.mem_union.mp h with ho | hn

  · exact Finset.notMem_erase _ _ ho

  · exact PhysicalMWheel.zero_outside_ground i.width i.labels (i.zero.symm ▸ hn)

**Definition 1.14 (seedGraph).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.seedGraph`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.seedGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Preserved frozen predecessor declaration. 

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

def seedGraph (f : K4.SeedLabel ↪ V) : GraphData (Fin 4) V :=

  PhysicalLabels.data K4.seedGraphData f s(0,0)

**Theorem 1.15 (seed_root).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.seed_root`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.seed_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Preserved frozen predecessor declaration. 

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

theorem seed_root (f : K4.SeedLabel ↪ V) :

    (seedGraph f).rows.root = delta {f 0} ⊔ delta {f 1} ⊔ delta {f 2} := by

  rw [seedGraph,PhysicalLabels.root,K4.seedOriginalRoot]

  apply SetLike.ext

  intro s

  change (∃ t, (∃ q ∈ ({({0} : Finset K4.SeedLabel),{1},{2}} : Finset (Finset K4.SeedLabel)),

    t ⊆ q) ∧ t.image f = s) ↔ _

  simp only [Finset.mem_insert,Finset.mem_singleton,LowerSet.mem_sup_iff]

  constructor

  · rintro ⟨t,⟨q,hq,ht⟩,rfl⟩

    rcases hq with rfl | rfl | rfl

    · exact Or.inl (Or.inl (by simpa using Finset.image_subset_image ht))

    · exact Or.inl (Or.inr (by simpa using Finset.image_subset_image ht))

    · exact Or.inr (by simpa using Finset.image_subset_image ht)

  · intro hs

    rcases hs with (hs | hs) | hs

    · obtain ⟨t,ht,he⟩ := Finset.subset_image_iff.mp

        (show s ⊆ ({0} : Finset K4.SeedLabel).image f by simpa using hs)

      exact ⟨t,⟨{0},Or.inl rfl,ht⟩,he⟩

    · obtain ⟨t,ht,he⟩ := Finset.subset_image_iff.mp

        (show s ⊆ ({1} : Finset K4.SeedLabel).image f by simpa using hs)

      exact ⟨t,⟨{1},Or.inr (Or.inl rfl),ht⟩,he⟩

    · obtain ⟨t,ht,he⟩ := Finset.subset_image_iff.mp

        (show s ⊆ ({2} : Finset K4.SeedLabel).image f by simpa using hs)

      exact ⟨t,⟨{2},Or.inr (Or.inr rfl),ht⟩,he⟩

**Definition 1.16 (MixedHistory).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.MixedHistory`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.MixedHistory` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Preserved frozen predecessor declaration. 

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

inductive MixedHistory : Nat → (A : Type) → GraphData A V → Type _

  | seed (f : K4.SeedLabel ↪ V) : MixedHistory 0 (Fin 4) (seedGraph f)

  | attach {n : Nat} {A : Type} {g : GraphData A V}

      (old : MixedHistory n A g) (i : WheelInput g) :

      MixedHistory (n+1) (physicalWheelStep g i).Carrier (physicalWheelStep g i).data

Definitions and proofs are in the paired Lean module.

/- Fixed-W4 compatibility is a separate genuine constructor, not an arbitrary

width certificate inferred from the fixed-W4 compiler. -/

**Definition 1.17 (Ambient).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.Ambient`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.Ambient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Preserved frozen predecessor declaration. 

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

abbrev Ambient (n ghosts : Nat) := Fin (3 + 4*n + ghosts)

**Definition 1.18 (Input).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.Input`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.Input` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Preserved frozen predecessor declaration. 

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

structure Input {A : Type*} (g : GraphData A V) where

  e : V

  retained : e ∈ g.ground

  a : A

  b : A

  edge : g.edge e = s(a,b)

  labels : Wheel.Label ↪ V

  zero : labels 0 = e

  fresh : Disjoint g.ground (Wheel.Y.image labels)

**Definition 1.19 (blockInput).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.blockInput`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.blockInput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Preserved frozen predecessor declaration. 

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

def blockInput {A : Type} {n ghosts k : Nat}

    (g : GraphData A (Ambient n ghosts)) (hk : k < n)

    (bound : ∀ x ∈ g.ground, x.val < 3 + 4*k)

    (e : Ambient n ghosts) (he : e ∈ g.ground)

    (a b : A) (hedge : g.edge e = s(a,b)) : Input g := by

  let f : Wheel.Label → Ambient n ghosts := fun j =>

    if j = 0 then e else ⟨3 + 4*k + (j.val - 1),by have := j.isLt; omega⟩

  have hb := bound e he

  have hf : Function.Injective f := by

    intro x y h

    by_cases hx : x = 0 <;> by_cases hy : y = 0

    · exact hx.trans hy.symm

    · have hv := congrArg Fin.val h

      simp only [f,if_pos hx,if_neg hy] at hv

      omega

    · have hv := congrArg Fin.val h

      simp only [f,if_neg hx,if_pos hy] at hv

      omega

    · apply Fin.ext

      have hxx : x.val ≠ 0 := fun h0 => hx (Fin.ext h0)

      have hyy : y.val ≠ 0 := fun h0 => hy (Fin.ext h0)

      have hv := congrArg Fin.val h

      simp only [f,if_neg hx,if_neg hy] at hv

      omega

  have fresh : Disjoint g.ground (Wheel.Y.image f) := by

    apply Finset.disjoint_left.mpr

    intro x hx hnew

    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hnew

    have hj0 : j ≠ (0 : Wheel.Label) := by

      intro hz

      subst j

      exact (by decide : (0 : Wheel.Label) ∉ Wheel.Y) hj

    have hv := bound (f j) hx

    simp only [f,if_neg hj0] at hv

    omega

  exact {

    e := e

    retained := he

    a := a

    b := b

    edge := hedge

    labels := ⟨f,hf⟩

    zero := by change f 0 = e; simp only [f,if_pos rfl]

    fresh := fresh }

**Definition 1.20 (step).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.step`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.step` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Preserved frozen predecessor declaration. 

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

def step {A : Type*} (g : GraphData A V) (i : Input g) : PhysicalGlue A Wheel.Label V :=

  PhysicalCertificate.attachment g i.e i.retained i.a i.b i.edge i.labels i.zero i.fresh

**Theorem 1.21 (step_rows).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.step_rows`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.step_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Preserved frozen predecessor declaration. 

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

theorem step_rows {A : Type*} (g : GraphData A V) (i : Input g) :

    (∀ c : g.chords, (step g i).data.rows.row (.inl c) =

      substitute i.e (Wheel.R.image i.labels) (g.rows.row c)) ∧

    (∀ d : (Wheel.ambientGraph i.labels).PhysicalSurvivor (0 : Fin 4),

      (step g i).data.rows.row (.inr d) =

        ((![{(1 : Wheel.Label),2},{2,3},{3,4},{4,1}] : Fin 4 → Finset Wheel.Label) d.1).image i.labels) := by

  constructor

  · exact (PhysicalCertificate.attachment_rows g i.e i.retained i.a i.b i.edge

      i.labels i.zero i.fresh).1

  · intro d

    exact ((PhysicalCertificate.attachment_rows g i.e i.retained i.a i.b

      i.edge i.labels i.zero i.fresh).2 d).trans

      ((Wheel.ambient_row i.labels d.1).trans

        (congrArg (fun t : Finset Wheel.Label => t.image i.labels)

          (Wheel.fundamental_rows d.1)))

**Definition 1.22 (History).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.History`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.History` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Preserved frozen predecessor declaration. 

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

inductive History : Nat → (A : Type) → GraphData A V → Type _

  | seed (f : K4.SeedLabel ↪ V) : History 0 (Fin 4) (seedGraph f)

  | attach {n : Nat} {A : Type} {g : GraphData A V} (old : History n A g) (i : Input g) :

      History (n+1) (step g i).Carrier (step g i).data

**Definition 1.23 (certificate).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.certificate`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.certificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Preserved frozen predecessor declaration. 

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

def certificate {n : Nat} {A : Type} {g : GraphData A V} (h : History n A g) :

    Certificate g.ground g.rows.root := by

  induction h with

  | seed f =>

    let c := renameCertificate f K4.seedGraphCertificate

    exact {

      supported := by rw [seedGraph,PhysicalLabels.root]; exact c.supported

      core := c.core

      critical := c.critical

      vertex := c.vertex

      vertex_mem := c.vertex_mem

      core_supported := c.core_supported

      critical_supported := c.critical_supported

      cells := c.cells

      main := c.main.cast (congrArg project (PhysicalLabels.root K4.seedGraphData f s(0,0))).symm rfl

      separate := c.separate }

  | attach old i ih =>

    exact PhysicalCertificate.certificate _ i.e i.retained i.a i.b i.edge

      i.labels i.zero i.fresh ih

**Theorem 1.24 (statistics).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.statistics`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.statistics` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Preserved frozen predecessor declaration. 

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

theorem statistics {n : Nat} {A : Type} {g : GraphData A V} (h : History n A g) :

    (certificate h).critical.card = 2 ∧

      ∀ s ∈ (certificate h).critical, s.card = 2*n+1 := by

  induction h with

  | seed f =>

    change (K4.seed.critical.image (fun t => t.image f)).card = 2 ∧

      ∀ s ∈ K4.seed.critical.image (fun t => t.image f), s.card = 2*0+1

    constructor

    · rw [Finset.card_image_of_injective _ (Finset.image_injective f.injective)]

      decide

    · intro s hs

      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hs

      have htcard : t.card = 1 := by

        have hh : t = {1} ∨ t = {2} := by simpa [K4.seed] using ht

        rcases hh with rfl | rfl <;> simp

      rw [Finset.card_image_of_injective _ f.injective,htcard]

  | @attach n A g old i ih =>

    let c := certificate old

    let out := PhysicalCertificate.certificate g i.e i.retained i.a i.b i.edge

      i.labels i.zero i.fresh c

    have hs := PhysicalCertificate.certificate_statistics g i.e i.retained i.a i.b i.edge

      i.labels i.zero i.fresh c

    change out.critical.card = 2 ∧ ∀ s ∈ out.critical, s.card = 2*(n+1)+1

    constructor

    · exact hs.1.trans ih.1

    · intro s hmem

      change s ∈ (PhysicalCertificate.certificate g i.e i.retained i.a i.b i.edge

        i.labels i.zero i.fresh c).critical at hmem

      rw [PhysicalCertificate.certificate_critical] at hmem

      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hmem

      have hsize := hs.2 t ht

      have hold := ih.2 t ht

      omega

**Theorem 1.25 (boundaries).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.boundaries`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.boundaries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Preserved frozen predecessor declaration. 

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

theorem boundaries {n : Nat} {A : Type} {g : GraphData A V} (h : History n A g)

    {s : Finset V} (hs : s ∈ (certificate h).critical) :

    s.Nonempty ∧ s ∉ (certificate h).core ∧

      delta s ⊓ (certificate h).core =

        (⟨{t | t ⊂ s},by intro a b hab hbs; exact lt_of_le_of_lt hab hbs⟩ : Family V) ∧

      ∀ t ∈ (certificate h).critical, s ⊆ t → s = t := by

  let c := certificate h

  exact ⟨c.cells.nonempty s hs,c.cells.absent s hs,

    critical_intersection c.core c.critical c.cells hs,c.cells.antichain s hs⟩

**Theorem 1.26 (survives).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.survives`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.survives` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Preserved frozen predecessor declaration. 

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

theorem survives {n : Nat} {A : Type} {g : GraphData A V} (h : History n A g) :

    (certificate h).vertex ∈ g.ground :=

  (certificate h).core_supported _ (certificate h).vertex_mem (by simp)

**Theorem 1.27 (finite_carrier).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.finite_carrier`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.finite_carrier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Finiteness is a consequence of the actual K4 seed and the CutTree coproduct with its finite three-vertex right nonterminal complement. It is not a premise on an output graph.

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

theorem finite_carrier {n : Nat} {A : Type} {g : GraphData A V}

    (h : History n A g) : Finite A := by

  induction h with

  | seed f => infer_instance

  | @attach n A g old i ih =>

    letI : Finite A := ih

    change Finite (A ⊕ {z : Wheel.Label // z ≠ 1 ∧ z ≠ 2})

    infer_instance

**Theorem 1.28 (vertex_card).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.vertex_card`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.vertex_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Induct on the actual History. The seed carrier is Fin 4. The CutTree right summand excludes its two actual terminals from Fin 5; the hub and two rim vertices give three new vertices. finite_carrier justifies the finite Nat.card coproduct identity. No desired count is assumed.

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

theorem vertex_card {n : Nat} {A : Type} {g : GraphData A V}

    (h : History n A g) : Nat.card A = 4 + 3*n := by

  induction h with

  | seed f => simp only [Nat.card_eq_fintype_card,Fintype.card_fin] <;> omega

  | @attach n A g old i ih =>

    letI : Finite A := finite_carrier old

    change Nat.card (A ⊕ {z : Wheel.Label // z ≠ 1 ∧ z ≠ 2}) = _

    have hright : Nat.card {z : Wheel.Label // z ≠ 1 ∧ z ≠ 2} = 3 := by

      rw [Nat.card_eq_fintype_card]

      decide

    rw [Nat.card_sum,hright,ih]

    omega

**Theorem 1.29 (ground_card).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.ground_card`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.ground_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

The literal physical ground is old.erase e union the fresh image of Wheel.Y. Freshness proves disjointness; injection counts four new labels and actual retention proves erase loses one. This counts the full retained ground rather than support.

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

theorem ground_card {n : Nat} {A : Type} {g : GraphData A V}

    (h : History n A g) : g.ground.card = 3 + 3*n := by

  induction h with

  | seed f =>

    change (Finset.univ.image f).card = _

    rw [Finset.card_image_of_injective _ f.injective]

    simp only [Finset.card_univ,Fintype.card_fin]

  | @attach n A g old i ih =>

    change (g.ground.erase i.e ∪ Wheel.Y.image i.labels).card = _

    rw [Finset.card_union_of_disjoint

      (i.fresh.mono_left (Finset.erase_subset _ _)),

      Finset.card_image_of_injective _ i.labels.injective]

    have hy : Wheel.Y.card = 4 := by decide

    have he := Finset.card_erase_add_one i.retained

    rw [hy]

    omega

**Definition 1.30 (treeEdgeEquiv).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.treeEdgeEquiv`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.treeEdgeEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Map each retained original label to its actual unordered tree edge. GraphData.labels_injective proves injection and GraphData.tree_edges proves surjection by Sym2 induction. No finite-vertex or chord-injectivity hypothesis is used.

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

def treeEdgeEquiv {A : Type*} (g : GraphData A V) :

    {i // i ∈ g.ground} ≃ {d : Sym2 A // d ∈ g.tree.edgeSet} := by

  let f : {i // i ∈ g.ground} → {d : Sym2 A // d ∈ g.tree.edgeSet} := fun i =>

    ⟨g.edge i.1,by

      have hm : ∀ d : Sym2 A, g.edge i.1 = d → d ∈ g.tree.edgeSet := by

        apply Sym2.ind

        intro x y he

        exact (g.tree_edges x y).mpr ⟨i.1,i.2,he⟩

      exact hm _ rfl⟩

  apply Equiv.ofBijective f

  constructor

  · intro i j he

    apply Subtype.ext

    exact g.labels_injective i.1 i.2 j.1 j.2 (congrArg Subtype.val he)

  · rintro ⟨d,hd⟩

    induction d using Sym2.ind with

    | h x y =>

      obtain ⟨i,hi,he⟩ := (g.tree_edges x y).mp hd

      exact ⟨⟨i,hi⟩,Subtype.ext he⟩

**Theorem 1.31 (tree_edge_card).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.tree_edge_card`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.tree_edge_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Count physical tree edges through treeEdgeEquiv and ground_card. No Euler count or assumed tree size is a premise.

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

theorem tree_edge_card {n : Nat} {A : Type} {g : GraphData A V}

    (h : History n A g) :

    Nat.card {d : Sym2 A // d ∈ g.tree.edgeSet} = 3 + 3*n := by

  rw [← Nat.card_congr (treeEdgeEquiv g),Nat.card_eq_fintype_card,Fintype.card_coe]

  exact ground_card h

**Definition 1.32 (physicalEdgeEquiv).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.physicalEdgeEquiv`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.physicalEdgeEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Consume PhysicalGlue.graph_edgeSet and graph_images_disjoint. Existing Set image equivalences use the proved qL/qR injections; Set.union separates their disjoint physical images. This counts edge sets without counting duplicate chord indices.

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

def physicalEdgeEquiv {A B : Type*} (s : PhysicalGlue A B V) :

    {d : Sym2 s.Carrier // d ∈ s.data.graph.edgeSet} ≃

      {d : Sym2 A // d ∈ s.leftKept.edgeSet} ⊕

        {d : Sym2 B // d ∈ s.rightKept.edgeSet} := by

  classical

  exact ((Set.equivOfEq s.graph_edgeSet).trans

    (Equiv.Set.union s.graph_images_disjoint)).trans

      (Equiv.sumCongr

        (Equiv.Set.image (Sym2.map s.qL) s.leftKept.edgeSet

          (Sym2.map.injective s.input.qL_injective)).symm

        (Equiv.Set.image (Sym2.map s.qR) s.rightKept.edgeSet

          (Sym2.map.injective s.input.qR_injective)).symm)

**Theorem 1.33 (graph_edge_card).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.graph_edge_card`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.graph_edge_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

K4 has six physical edges. deleted_card partitions the old actual edge set into the deleted singleton and its complement; the retained port belongs to the graph by tree_le. The actual W4 graph with its actual interface removed has seven edges. physicalEdgeEquiv gives their disjoint sum, hence increase six. The closed finite Lean decide proof terms have not been executed by a compiler or kernel here.

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

theorem graph_edge_card {n : Nat} {A : Type} {g : GraphData A V}

    (h : History n A g) :

    Nat.card {d : Sym2 A // d ∈ g.graph.edgeSet} = 6 + 6*n := by

  induction h with

  | seed f =>

    change Nat.card {d : Sym2 (Fin 4) // d ∈ (⊤ : SimpleGraph (Fin 4)).edgeSet} = _

    rw [Nat.card_eq_fintype_card]

    decide

  | @attach n A g old i ih =>

    letI : Finite A := finite_carrier old

    let s := step g i

    have he : g.edge i.e ∈ g.graph.edgeSet := by

      rw [i.edge]

      exact g.tree_le ((g.tree_edges i.a i.b).mpr ⟨i.e,i.retained,i.edge⟩)

    have hold := deleted_card g.graph (g.edge i.e) he

    have hright : Nat.card {d : Sym2 Wheel.Label //

        d ∈ (Wheel.wheelGraphData.graph.deleteEdges

          {Wheel.wheelGraphData.kappa (0 : Fin 4)}).edgeSet} = 7 := by

      letI : DecidableRel Wheel.wheelGraphData.graph.Adj := by

        intro x y

        change Decidable ((x ≠ y ∧ (x = 0 ∨ y = 0)) ∨

          ∃ j : Fin 4, s(x,y) =

            s((![(1,2),(2,3),(3,4),(4,1)] j : Wheel.Label × Wheel.Label).1,

              (![(1,2),(2,3),(3,4),(4,1)] j : Wheel.Label × Wheel.Label).2))

        infer_instance

      letI : Fintype {d : Sym2 Wheel.Label //

          d ∈ (Wheel.wheelGraphData.graph.deleteEdges

            {Wheel.wheelGraphData.kappa (0 : Fin 4)}).edgeSet} :=

        SimpleGraph.fintypeEdgeSet _

      rw [Nat.card_eq_fintype_card]

      decide

    have hc := Nat.card_congr (physicalEdgeEquiv s)

    rw [Nat.card_sum] at hc

    change Nat.card {d : Sym2 s.Carrier // d ∈ s.data.graph.edgeSet} = _

    change Nat.card {d : Sym2 s.Carrier // d ∈ s.data.graph.edgeSet} =

      Nat.card {d : Sym2 A // d ∈ (g.graph.deleteEdges {g.edge i.e}).edgeSet} +

      Nat.card {d : Sym2 Wheel.Label // d ∈ (Wheel.wheelGraphData.graph.deleteEdges

        {Wheel.wheelGraphData.kappa (0 : Fin 4)}).edgeSet} at hc

    rw [hc,hright]

    omega

**Definition 1.34 (RowBinding).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.RowBinding`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.RowBinding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

This is the relation PRODUCED by handoff: an equivalence of every chord index, equality of the full ground, and equality of every actual path row. It is not a History/Input field or an assumed supplier.

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

structure RowBinding {A : Type*} (g : GraphData A V) (r : Rows V) where

  index : g.chords ≃ r.chords

  ground : g.ground = r.ground

  row : ∀ c : g.chords, g.rows.row c = r.row (index c)

**Definition 1.35 (handoff).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.handoff`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.handoff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Build the existing renameRows/RowHistory.seed recursively. At attachment the previous produced binding establishes retention/freshness on its row model. Use RowHistory.attach and appendWheelRows; compose the actual physical survivor equivalence with the previous index equivalence. step_rows and Wheel.ambient_row prove the two row branches. Every duplicate old index and original right survivor is retained.

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

def handoff {n : Nat} {A : Type} {g : GraphData A V} (h : History n A g) :

    Σ r : Rows V, RowHistory n r × RowBinding g r := by

  induction h with

  | seed f =>

    exact ⟨renameRows f K4.seedGraphData.rows,RowHistory.seed f,{

      index := Equiv.refl _

      ground := rfl

      row := fun c => PhysicalLabels.row K4.seedGraphData f s(0,0) c }⟩

  | @attach n A g old i ih =>

    let r := ih.1

    let b := ih.2.2

    have he : i.e ∈ r.ground := b.ground ▸ i.retained

    have hf : Disjoint r.ground (Wheel.Y.image i.labels) := b.ground ▸ i.fresh

    refine ⟨appendWheelRows r i.e he i.labels i.zero,

      RowHistory.attach ih.2.1 i.e he i.labels i.zero hf,{

        index := (PhysicalCertificate.attachment_chords g i.e i.retained i.a i.b

          i.edge i.labels i.zero i.fresh).trans

            (Equiv.sumCongr b.index (Equiv.refl _))

        ground := ?_

        row := ?_ }⟩

    · change g.ground.erase i.e ∪ Wheel.Y.image i.labels =

        r.ground.erase i.e ∪ Wheel.Y.image i.labels

      rw [b.ground]

    · intro c

      cases c with

      | inl c =>

        change (step g i).data.rows.row (.inl c) =

          substitute i.e (Wheel.R.image i.labels) (r.row (b.index c))

        rw [(step_rows g i).1 c,b.row c]

      | inr d =>

        change (step g i).data.rows.row (.inr d) =

          (Wheel.wheelGraphData.rows.row d.1).image i.labels

        exact ((step g i).right_row d).trans (Wheel.ambient_row i.labels d.1)

**Theorem 1.36 (root_handoff).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.root_handoff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.root_handoff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Forward raw membership uses the produced index equivalence and reverse membership uses its inverse. The full ground and every row agree before project, preserving VOID versus UNIT and inactive coordinates.

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

theorem root_handoff {n : Nat} {A : Type} {g : GraphData A V} (h : History n A g) :

    g.rows.root = (handoff h).1.root := by

  apply SetLike.ext

  intro s

  constructor

  · rintro ⟨c,hc⟩

    refine ⟨(handoff h).2.2.index c,?_⟩

    change s ⊆ g.ground \ g.rows.row c at hc

    simpa only [(handoff h).2.2.ground,(handoff h).2.2.row c] using hc

  · rintro ⟨c,hc⟩

    refine ⟨(handoff h).2.2.index.symm c,?_⟩

    change s ⊆ g.ground \ g.rows.row ((handoff h).2.2.index.symm c)

    simpa only [(handoff h).2.2.ground,(handoff h).2.2.row,

      Equiv.apply_symm_apply] using hc

**Theorem 1.37 (schedule_data).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.schedule_data`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.schedule_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Induct on the same physical history. PhysicalCertificate.certificate_critical/certificate_vertex supply exact updates; the induction hypotheses and produced ground equality identify the independent row schedules. The core-port case is retained through finishVertex.

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

theorem schedule_data {n : Nat} {A : Type} {g : GraphData A V} (h : History n A g) :

    (certificate h).critical = rowHistoryCriticalSchedule (handoff h).2.1 ∧

    (certificate h).vertex = rowHistoryVertexSchedule (handoff h).2.1 := by

  induction h with

  | seed f => exact ⟨rfl,rfl⟩

  | @attach n A g old i ih =>

    change (PhysicalCertificate.certificate g i.e i.retained i.a i.b i.edge

      i.labels i.zero i.fresh (certificate old)).critical =

        (rowHistoryCriticalSchedule (handoff old).2.1).image

          (wheelCell i.e (i.labels 1) (i.labels 3) (i.labels 4)) ∧

      (PhysicalCertificate.certificate g i.e i.retained i.a i.b i.edge

        i.labels i.zero i.fresh (certificate old)).vertex =

        finishVertex ((handoff old).1.ground.erase i.e) (Wheel.R.image i.labels)

          i.e (rowHistoryVertexSchedule (handoff old).2.1) _

    constructor

    · rw [PhysicalCertificate.certificate_critical,ih.1]

    · rw [PhysicalCertificate.certificate_vertex,ih.2,

        (handoff old).2.2.ground]

**Theorem 1.38 (main_order).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.main_order`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.main_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

The actual empty seed main survives its label/source casts. At attachment consume PhysicalCertificate.certificate_main_order, the preceding main-list equality and schedule_data. The existing independent row schedule flatMaps the previous list and appends actual filling blocks. No target-list equation is an assumption.

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

theorem main_order {n : Nat} {A : Type} {g : GraphData A V} (h : History n A g) :

    orderedPairs (certificate h).main = rowHistoryMainSchedule (handoff h).2.1 := by

  induction h with

  | seed f =>

    change orderedPairs (certificate (History.seed f)).main = []

    simp only [certificate, renameCertificate, orderedPairs_cast]

    unfold orderedPairs orderedPair

    simpa only [K4.seedGraphCertificate,K4.seed,

      FiniteRelativeSimplicialCollapse.Sequence.pairs_cast,

      FiniteRelativeSimplicialCollapse.Sequence.pairs,List.map_nil] using

      renameSequence_pairs f K4.seedGraphCertificate.main

  | @attach n A g old i ih =>

    change orderedPairs (PhysicalCertificate.certificate g i.e i.retained i.a i.b

      i.edge i.labels i.zero i.fresh (certificate old)).main =

        WheelSupplier.oneStepMainFrom i.e i.labels

          (rowHistoryCriticalSchedule (handoff old).2.1)

          (rowHistoryMainSchedule (handoff old).2.1)

    rw [PhysicalCertificate.certificate_main_order,ih,(schedule_data old).1]

**Theorem 1.39 (separate_order).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.separate_order`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.separate_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Use the actual empty seed core list. At attachment consume PhysicalCertificate.certificate_separate_order, its own previous-list equality, schedule_data and produced ground equality. The independent separate schedule appends collars, old-core replay and the full-ground terminal. Its source is C ALONE. Critical tops are not interleaved and the ORIGINAL skipped order is preserved by the reused compiler. Its chosen Gamma and predecessor proofs remain unverified source premises.

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

theorem separate_order {n : Nat} {A : Type} {g : GraphData A V} (h : History n A g) :

    orderedPairs (certificate h).separate = rowHistorySeparateSchedule (handoff h).2.1 := by

  induction h with

  | seed f =>

    change orderedPairs (certificate (History.seed f)).separate = []

    simp only [certificate, renameCertificate, orderedPairs_cast]

    unfold orderedPairs orderedPair

    simpa only [K4.seedGraphCertificate,K4.seed,

      FiniteRelativeSimplicialCollapse.Sequence.pairs_cast,

      FiniteRelativeSimplicialCollapse.Sequence.pairs,List.map_nil] using

      renameSequence_pairs f K4.seedGraphCertificate.separate

  | @attach n A g old i ih =>

    change orderedPairs (PhysicalCertificate.certificate g i.e i.retained i.a i.b

      i.edge i.labels i.zero i.fresh (certificate old)).separate =

        WheelSupplier.oneStepSeparateFrom ((handoff old).1.ground.erase i.e)

          i.e i.labels (rowHistoryCriticalSchedule (handoff old).2.1)

          (rowHistoryVertexSchedule (handoff old).2.1)

          (rowHistorySeparateSchedule (handoff old).2.1)

    rw [PhysicalCertificate.certificate_separate_order,ih,

      (schedule_data old).1,(schedule_data old).2,(handoff old).2.2.ground]

**Definition 1.40 (mixed_excess).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.mixed_excess`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.mixed_excess` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Sum width minus one along the actual finite MixedHistory. This reads prescribed widths and has no output certificate field.

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

def mixed_excess {n : Nat} {A : Type} {g : GraphData A V} (h : MixedHistory n A g) : Nat := by

  induction h with

  | seed f => exact 0

  | attach old i ih => exact ih + (i.width - 1)

**Theorem 1.41 (mixed_finite_carrier).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.mixed_finite_carrier`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.mixed_finite_carrier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Induct from actual K4 through the CutTree coproduct and the finite right two-terminal complement at every prescribed width.

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

theorem mixed_finite_carrier {n : Nat} {A : Type} {g : GraphData A V}

    (h : MixedHistory n A g) : Finite A := by

  induction h with

  | seed f => infer_instance

  | @attach n A g old i ih =>

    letI : Finite A := ih

    change Finite (A ⊕ {z : AllMWheel.Label i.width //

      z ≠ (physicalWheelStep g i).input.aR ∧ z ≠ (physicalWheelStep g i).input.bR})

    infer_instance

**Theorem 1.42 (mixed_vertex_card).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.mixed_vertex_card`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.mixed_vertex_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Count the actual right two-terminal complement by the finite subtype-complement identity and the two-element terminal set. Distinctness comes from actual chord adjacency. Sum width minus one along mixed_excess, uniformly over every MixedHistory.

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

theorem mixed_vertex_card {n : Nat} {A : Type} {g : GraphData A V}

    (h : MixedHistory n A g) : Nat.card A = 4 + mixed_excess h := by

  induction h with

  | seed f => simp only [mixed_excess,Nat.card_eq_fintype_card,Fintype.card_fin]

  | @attach n A g old i ih =>

    letI : Finite A := mixed_finite_carrier old

    let s := physicalWheelStep g i

    have hc : Nat.card s.Carrier = Nat.card A + (i.width - 1) := by

      change Nat.card (A ⊕ {z : AllMWheel.Label i.width //

        z ≠ s.input.aR ∧ z ≠ s.input.bR}) = _

      rw [Nat.card_sum,nonterminal_card s.input.aR s.input.bR s.input.neR]

      have hw : Nat.card (AllMWheel.Label i.width) = i.width + 1 := by

        simp only [Nat.card_eq_fintype_card,Fintype.card_fin]

      rw [hw]

      have hm := i.atLeastThree

      omega

    change Nat.card s.Carrier = 4 + (mixed_excess old + (i.width - 1))

    rw [hc,ih]

    omega

**Theorem 1.43 (mixed_ground_card).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.mixed_ground_card`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.mixed_ground_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

The actual erase/union equation, retained port, injective labels and freshness give increase width minus one. AllMWheel.ground is Fin(width+1) with hub zero erased. The full original ambient type and ghosts remain.

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

theorem mixed_ground_card {n : Nat} {A : Type} {g : GraphData A V}

    (h : MixedHistory n A g) : g.ground.card = 3 + mixed_excess h := by

  induction h with

  | seed f =>

    change (Finset.univ.image f).card = 3 + 0

    rw [Finset.card_image_of_injective _ f.injective]

    simp only [Finset.card_univ,Fintype.card_fin]

  | @attach n A g old i ih =>

    change (g.ground.erase i.e ∪ (AllMWheel.ground i.width).image i.labels).card =

      3 + (mixed_excess old + (i.width - 1))

    rw [Finset.card_union_of_disjoint

      (i.fresh.mono_left (Finset.erase_subset _ _)),

      Finset.card_image_of_injective _ i.labels.injective]

    have he := Finset.card_erase_add_one i.retained

    have hw : (AllMWheel.ground i.width).card + 1 = i.width + 1 := by

      change ((Finset.univ : Finset (AllMWheel.Label i.width)).erase 0).card + 1 = _

      simpa only [Finset.card_univ,Fintype.card_fin] using

        (Finset.card_erase_add_one (Finset.mem_univ (0 : AllMWheel.Label i.width)))

    have hm := i.atLeastThree

    omega

**Theorem 1.44 (mixed_tree_edge_card).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.mixed_tree_edge_card`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.mixed_tree_edge_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Apply the actual label-to-tree-edge equivalence to the arbitrary-width mixed ground count. No universal all-corner certificate is claimed.

Source namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory. Literal declaration/proof; not elaborated metadata:

theorem mixed_tree_edge_card {n : Nat} {A : Type} {g : GraphData A V}

    (h : MixedHistory n A g) :

    Nat.card {d : Sym2 A // d ∈ g.tree.edgeSet} = 3 + mixed_excess h := by

  rw [← Nat.card_congr (treeEdgeEquiv g),Nat.card_eq_fintype_card,Fintype.card_coe]

  exact mixed_ground_card h

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.Ambient`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.History`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.Input`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.MixedHistory`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.RowBinding`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.WheelInput`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.blockInput`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.boundaries`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.certificate`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.finite_carrier`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.graph_edge_card`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.ground_card`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.handoff`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.main_order`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.mixed_excess`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.mixed_finite_carrier`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.mixed_ground_card`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.mixed_tree_edge_card`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.mixed_vertex_card`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.physicalEdgeEquiv`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.physicalWheelStep`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.physicalWheelStep_chords`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.physicalWheelStep_corner`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.physicalWheelStep_corner_row`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.physicalWheelStep_ground`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.physicalWheelStep_root`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.physicalWheelStep_rowRoot`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.physicalWheelStep_rows`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.physicalWheelStep_rows_left`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.physicalWheelStep_rows_right`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.root_handoff`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.schedule_data`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.seedGraph`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.seed_root`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.separate_order`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.statistics`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.step`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.step_rows`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.survives`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.treeEdgeEquiv`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.tree_edge_card`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.vertex_card`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.wheelInputAtPort`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory.wheelStepRows`
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/HistoryCorners](HistoryCorners.md)
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/PhysicalCertificate](PhysicalCertificate.md)
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/PhysicalMWheel](PhysicalMWheel.md)
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/RowIteration](RowIteration.md)
