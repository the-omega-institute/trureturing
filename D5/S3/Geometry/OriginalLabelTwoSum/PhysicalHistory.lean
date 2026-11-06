/- GID: D5/S3/Geometry/OriginalLabelTwoSum/PhysicalHistory
   generality: G
   digest: Actual arbitrary-width retained-port wheel steps, literal corners and finite mixed histories. -/
import D5.S3.Geometry.OriginalLabelTwoSum.PhysicalMWheel
import D5.S3.Geometry.OriginalLabelTwoSum.PhysicalCertificate
import D5.S3.Geometry.OriginalLabelTwoSum.HistoryCorners
import D5.S3.Geometry.OriginalLabelTwoSum.RowIteration
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Fintype.Sum

/-! SOURCE_ONLY_UNCOMPILED. WheelInput contains only an old actual GraphData,
a retained edge, its orientation, and fresh injective labels. The carrier is
the existing CutTree coproduct: old vertices plus right nonterminals. Its two
injections overlap exactly at the terminal pair. Both physical interfaces are
deleted by PhysicalGlue.graph; no graph or path equation is assumed.

MixedHistory is the finite prescribed arbitrary-width class. Its constructors
store no root/corner/certificate supplier. In particular the all-corner strong
certificate induction is NOT asserted here. The fixed-W4 History at the end
retains the genuine PhysicalCertificate interface for existing consumers;
the appended canonical handoff/count/list proofs are SOURCE_ONLY_UNCOMPILED.
They do not supply the universal mixed-width all-corner constructor. -/
noncomputable section
open Set Finset SimpleGraph
namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Geometric inputs only, at ANY actual retained old or interior tree edge.
Freshness concerns current retained labels; inactive original coordinates stay
in V. Fresh vertices are supplied by the explicit coproduct construction. -/
structure WheelInput {A : Type*} (g : GraphData A V) where
  width : Nat
  atLeastThree : 3 ≤ width
  e : V
  retained : e ∈ g.ground
  a b : A
  edge : g.edge e = s(a,b)
  labels : AllMWheel.Label width ↪ V
  zero : labels 0 = e
  fresh : Disjoint g.ground ((AllMWheel.ground width).image labels)

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
  e_not_X := Finset.not_mem_erase _ _
  e_not_Y := i.zero ▸ PhysicalMWheel.zero_outside_ground i.width i.labels
  disjoint := i.fresh.mono_left (Finset.erase_subset _ _)
  aL := i.a
  bL := i.b
  edge_e := i.edge

def physicalWheelStep_chords {A : Type*} (g : GraphData A V) (i : WheelInput g) :
    (physicalWheelStep g i).data.chords ≃
      g.chords ⊕ {d : Fin i.width // d ≠ AllMWheel.interfaceRow i.width i.atLeastThree} :=
  (physicalWheelStep g i).uniqueChordEquiv
    (PhysicalMWheel.ambient_uniqueInterface i.width i.atLeastThree i.labels)

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

theorem physicalWheelStep_rows_left {A : Type*} (g : GraphData A V) (i : WheelInput g)
    (c : g.chords) :
    (physicalWheelStep g i).data.rows.row ((physicalWheelStep_chords g i).symm (.inl c)) =
      substitute i.e ((AllMWheel.rim i.width i.atLeastThree).image i.labels) (g.rows.row c) := by
  simpa using physicalWheelStep_rows g i ((physicalWheelStep_chords g i).symm (.inl c))

theorem physicalWheelStep_rows_right {A : Type*} (g : GraphData A V) (i : WheelInput g)
    (d : {d : Fin i.width // d ≠ AllMWheel.interfaceRow i.width i.atLeastThree}) :
    (physicalWheelStep g i).data.rows.row ((physicalWheelStep_chords g i).symm (.inr d)) =
      (AllMWheel.rimEdge i.width (by have := i.atLeastThree; omega) d.1).image i.labels := by
  simpa using physicalWheelStep_rows g i ((physicalWheelStep_chords g i).symm (.inr d))

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
    cases c with
    | inl c => simpa only [physicalWheelStep_rows_left] using hs
    | inr d => simpa only [physicalWheelStep_rows_right] using hs

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
    simpa only [he] using hc
  · rintro ⟨c,hc⟩
    refine ⟨(physicalWheelStep_chords g i).symm c,?_⟩
    cases c with
    | inl d => simpa only [wheelStepRows,physicalWheelStep_rows_left] using hc
    | inr d => simpa only [wheelStepRows,physicalWheelStep_rows_right] using hc

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

/-- Physical deletion and fresh-block ground, independent of the row model. -/
theorem physicalWheelStep_ground {A : Type*} (g : GraphData A V) (i : WheelInput g) :
    (physicalWheelStep g i).data.ground =
      g.ground.erase i.e ∪ (AllMWheel.ground i.width).image i.labels ∧
    i.e ∉ (physicalWheelStep g i).data.ground := by
  refine ⟨rfl,?_⟩
  intro h
  rcases Finset.mem_union.mp h with ho | hn
  · exact Finset.not_mem_erase _ _ ho
  · exact PhysicalMWheel.zero_outside_ground i.width i.labels (i.zero.symm ▸ hn)

def seedGraph (f : K4.SeedLabel ↪ V) : GraphData (Fin 4) V :=
  PhysicalLabels.data K4.seedGraphData f s(0,0)

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

/-- Finite prescribed mixed-width history from the ACTUAL marked K4.
Every step chooses an arbitrary retained port in its current actual graph. -/
inductive MixedHistory : Nat → (A : Type) → GraphData A V → Type _
  | seed (f : K4.SeedLabel ↪ V) : MixedHistory 0 (Fin 4) (seedGraph f)
  | attach {n : Nat} {A : Type} {g : GraphData A V}
      (old : MixedHistory n A g) (i : WheelInput g) :
      MixedHistory (n+1) (physicalWheelStep g i).Carrier (physicalWheelStep g i).data

/- Fixed-W4 compatibility is a separate genuine constructor, not an arbitrary
width certificate inferred from the fixed-W4 compiler. -/
abbrev Ambient (n ghosts : Nat) := Fin (3 + 4*n + ghosts)

structure Input {A : Type*} (g : GraphData A V) where
  e : V
  retained : e ∈ g.ground
  a b : A
  edge : g.edge e = s(a,b)
  labels : Wheel.Label ↪ V
  zero : labels 0 = e
  fresh : Disjoint g.ground (Wheel.Y.image labels)

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
    zero := by simp only [f,if_pos rfl]
    fresh := fresh }

def step {A : Type*} (g : GraphData A V) (i : Input g) : PhysicalGlue A Wheel.Label V :=
  PhysicalCertificate.attachment g i.e i.retained i.a i.b i.edge i.labels i.zero i.fresh

theorem step_rows {A : Type*} (g : GraphData A V) (i : Input g) :
    (∀ c : g.chords, (step g i).data.rows.row (.inl c) =
      substitute i.e (Wheel.R.image i.labels) (g.rows.row c)) ∧
    (∀ d : (Wheel.ambientGraph i.labels).PhysicalSurvivor (0 : Fin 4),
      (step g i).data.rows.row (.inr d) =
        (![{(1 : Wheel.Label),2},{2,3},{3,4},{4,1}] d.1).image i.labels) := by
  constructor
  · exact (PhysicalCertificate.attachment_rows g i.e i.retained i.a i.b i.edge
      i.labels i.zero i.fresh).1
  · intro d
    rw [(step g i).right_row,Wheel.ambient_row,Wheel.fundamental_rows]

inductive History : Nat → (A : Type) → GraphData A V → Type _
  | seed (f : K4.SeedLabel ↪ V) : History 0 (Fin 4) (seedGraph f)
  | attach {n : Nat} {A : Type} {g : GraphData A V} (old : History n A g) (i : Input g) :
      History (n+1) (step g i).Carrier (step g i).data

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
      rfl
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

theorem boundaries {n : Nat} {A : Type} {g : GraphData A V} (h : History n A g)
    {s : Finset V} (hs : s ∈ (certificate h).critical) :
    s.Nonempty ∧ s ∉ (certificate h).core ∧
      delta s ⊓ (certificate h).core =
        (⟨{t | t ⊂ s},by intro a b hab hbs; exact lt_of_le_of_lt hab hbs⟩ : Family V) ∧
      ∀ t ∈ (certificate h).critical, s ⊆ t → s = t := by
  let c := certificate h
  exact ⟨c.cells.nonempty s hs,c.cells.absent s hs,
    critical_intersection c.core c.critical c.cells hs,c.cells.antichain s hs⟩

theorem survives {n : Nat} {A : Type} {g : GraphData A V} (h : History n A g) :
    (certificate h).vertex ∈ g.ground :=
  (certificate h).core_supported _ (certificate h).vertex_mem (by simp)

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

/-- The right summand is the actual hub and the two nonterminal rim vertices.
The two terminals are identified with old vertices, so only three are new. -/
theorem vertex_card {n : Nat} {A : Type} {g : GraphData A V}
    (h : History n A g) : Nat.card A = 4 + 3*n := by
  induction h with
  | seed f => simp only [Nat.card_eq_fintype_card,Fintype.card_fin]; omega
  | @attach n A g old i ih =>
    letI : Finite A := finite_carrier old
    change Nat.card (A ⊕ {z : Wheel.Label // z ≠ 1 ∧ z ≠ 2}) = _
    have hright : Nat.card {z : Wheel.Label // z ≠ 1 ∧ z ≠ 2} = 3 := by
      rw [Nat.card_eq_fintype_card]
      decide
    rw [Nat.card_sum,hright,ih]
    omega

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

/-- Count PHYSICAL tree edges through their proved original-label bijection. -/
theorem tree_edge_card {n : Nat} {A : Type} {g : GraphData A V}
    (h : History n A g) :
    Nat.card {d : Sym2 A // d ∈ g.tree.edgeSet} = 3 + 3*n := by
  rw [← Nat.card_congr (treeEdgeEquiv g),Nat.card_eq_fintype_card,Fintype.card_coe]
  exact ground_card h

/-- Both deleted physical graph images are disjoint by the existing terminal
intersection theorem. This equivalence does not count chord indices. -/
def physicalEdgeEquiv {A B : Type*} (s : PhysicalGlue A B V) :
    {d : Sym2 s.Carrier // d ∈ s.data.graph.edgeSet} ≃
      {d : Sym2 A // d ∈ s.leftKept.edgeSet} ⊕
        {d : Sym2 B // d ∈ s.rightKept.edgeSet} := by
  classical
  exact ((Equiv.setCongr s.graph_edgeSet).trans
    (Equiv.Set.union s.graph_images_disjoint)).trans
      (Equiv.sumCongr
        (Equiv.Set.image (Sym2.map s.qL) s.leftKept.edgeSet
          (Sym2.map.injective s.input.qL_injective)).symm
        (Equiv.Set.image (Sym2.map s.qR) s.rightKept.edgeSet
          (Sym2.map.injective s.input.qR_injective)).symm)

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
  have hc := Nat.card_congr ((Equiv.setCongr hu).symm.trans (Equiv.Set.union hdj))
  rw [Nat.card_sum] at hc
  have hone : Nat.card ({d} : Set (Sym2 A)) = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_unique
  rw [hone] at hc
  simpa only [SimpleGraph.edgeSet_deleteEdges] using hc.symm

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

/-- An OUTPUT relation: every actual physical chord index is retained, the
full original ground agrees, and EVERY path-derived row is identified. -/
structure RowBinding {A : Type*} (g : GraphData A V) (r : Rows V) where
  index : g.chords ≃ r.chords
  ground : g.ground = r.ground
  row : ∀ c : g.chords, g.rows.row c = r.row (index c)

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
        rw [(PhysicalCertificate.attachment_rows g i.e i.retained i.a i.b
          i.edge i.labels i.zero i.fresh).2 d,Wheel.ambient_row]

/-- Raw equality before nonempty projection; the inverse index equivalence
proves the reverse inclusion, so no duplicate row index is silently omitted. -/
theorem root_handoff {n : Nat} {A : Type} {g : GraphData A V} (h : History n A g) :
    g.rows.root = (handoff h).1.root := by
  apply SetLike.ext
  intro s
  constructor
  · rintro ⟨c,hc⟩
    refine ⟨(handoff h).2.2.index c,?_⟩
    simpa only [(handoff h).2.2.ground,(handoff h).2.2.row c] using hc
  · rintro ⟨c,hc⟩
    refine ⟨(handoff h).2.2.index.symm c,?_⟩
    simpa only [(handoff h).2.2.ground,(handoff h).2.2.row,
      Equiv.apply_symm_apply] using hc

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

/-- ACTUAL physical main pairs equal the independently enumerated row schedule.
The induction consumes the previous equality through the one-step flatMap;
this is not a list re-extracted from the target certificate. -/
theorem main_order {n : Nat} {A : Type} {g : GraphData A V} (h : History n A g) :
    orderedPairs (certificate h).main = rowHistoryMainSchedule (handoff h).2.1 := by
  induction h with
  | seed f =>
    change orderedPairs (certificate (History.seed f)).main = []
    simpa only [certificate,renameCertificate,orderedPairs_cast,orderedPairs,
      orderedPair,K4.seedGraphCertificate,K4.seed,
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

/-- ACTUAL physical core pairs equal the independent separate schedule, on
C ALONE. Collars precede old-core replay, followed by the terminal; skipped
pairs retain their ORIGINAL order in the reused compiler. -/
theorem separate_order {n : Nat} {A : Type} {g : GraphData A V} (h : History n A g) :
    orderedPairs (certificate h).separate = rowHistorySeparateSchedule (handoff h).2.1 := by
  induction h with
  | seed f =>
    change orderedPairs (certificate (History.seed f)).separate = []
    simpa only [certificate,renameCertificate,orderedPairs_cast,orderedPairs,
      orderedPair,K4.seedGraphCertificate,K4.seed,
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

/-- Actual total number of new vertices along a prescribed mixed history.
No constant-width specialization appears in this recursion. -/
def mixed_excess {n : Nat} {A : Type} {g : GraphData A V} (h : MixedHistory n A g) : Nat := by
  induction h with
  | seed f => exact 0
  | attach old i ih => exact ih + (i.width - 1)

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

private theorem nonterminal_card {B : Type*} [Fintype B] [DecidableEq B]
    (a b : B) (hab : a ≠ b) :
    Nat.card {z : B // z ≠ a ∧ z ≠ b} = Nat.card B - 2 := by
  let e : {z : B // z ≠ a ∧ z ≠ b} ≃ {z : B // ¬ (z = a ∨ z = b)} :=
    Equiv.subtypeEquivRight (fun _ => not_or.symm)
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl,Fintype.card_subtype_eq_or_eq_of_ne hab,
    Nat.card_eq_fintype_card]

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

/-- Physical tree-edge count for the unchanged arbitrary-width mixed class. -/
theorem mixed_tree_edge_card {n : Nat} {A : Type} {g : GraphData A V}
    (h : MixedHistory n A g) :
    Nat.card {d : Sym2 A // d ∈ g.tree.edgeSet} = 3 + mixed_excess h := by
  rw [← Nat.card_congr (treeEdgeEquiv g),Nat.card_eq_fintype_card,Fintype.card_coe]
  exact mixed_ground_card h

end D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory
