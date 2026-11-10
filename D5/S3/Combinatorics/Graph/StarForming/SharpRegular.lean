/- GID: D5/S3/Combinatorics/Graph/StarForming/SharpRegular
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/SharpRegular
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: The actual all-degree sharp bipartite construction and its minimal selection. -/

import D5.S3.Combinatorics.Graph.StarForming.RegularCompensation
import D5.S3.Combinatorics.Graph.StarForming.PrivateClauses
import D5.S3.Combinatorics.Graph.StarForming.SubcubicCertificate
import D5.S3.Combinatorics.Graph.StarForming.SquareCapacity
import D5.S3.Combinatorics.Graph.SubQuorum.C4RepresentativeBounds
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Fintype.Option

/-! The graph G_d from SHARP_REGULAR_BIPARTITE_GAP, at
subquorum-colorings 48728b42d39ab3de5de251c61da5a404ec418a69,
Apache-2.0. The two Bool sides contain a high class, an outside class,
and one hub. With next the cyclic shift, the outside incidence excludes
the first and second forward shifts. No finite upper bound on d is used. -/

namespace D5.S3.Combinatorics.Graph.StarForming.SharpRegular
open StarFormingDissociationRefutation Regular
open scoped BigOperators
set_option synthInstance.maxSize 4096
set_option maxSynthPendingDepth 128
variable {I : Type} [Fintype I] [DecidableEq I]

abbrev Side (I : Type) := Option (Bool × I)
abbrev Vertex (I : Type) := Bool × Side I

def link (next : Equiv.Perm I) : Side I → Side I → Prop
  | none,none => False
  | none,some (k,_) => k = true
  | some (k,_),none => k = true
  | some (false,i),some (false,j) => i ≠ j
  | some (false,i),some (true,j) => i = j
  | some (true,i),some (false,j) => i = j
  | some (true,i),some (true,j) => j ≠ next i ∧ j ≠ next (next i)

instance (next : Equiv.Perm I) : DecidableRel (link next) := fun a b =>
  match a,b with
  | none,none => isFalse id
  | none,some (k,_) => inferInstanceAs (Decidable (k = true))
  | some (k,_),none => inferInstanceAs (Decidable (k = true))
  | some (false,i),some (false,j) => inferInstanceAs (Decidable (i ≠ j))
  | some (false,i),some (true,j) => inferInstanceAs (Decidable (i = j))
  | some (true,i),some (false,j) => inferInstanceAs (Decidable (i = j))
  | some (true,i),some (true,j) =>
      inferInstanceAs (Decidable (j ≠ next i ∧ j ≠ next (next i)))

def graph (next : Equiv.Perm I) : SimpleGraph (Vertex I) where
  Adj x y := (x.1 = false ∧ y.1 = true ∧ link next x.2 y.2) ∨
    (x.1 = true ∧ y.1 = false ∧ link next y.2 x.2)
  symm := ⟨by intro x y; tauto⟩
  loopless := ⟨by rintro ⟨b,x⟩ h; cases b <;> simp_all⟩

instance (next : Equiv.Perm I) : DecidableRel (graph next).Adj := fun x y =>
  inferInstanceAs (Decidable ((_ ∧ _ ∧ link next x.2 y.2) ∨
    (_ ∧ _ ∧ link next y.2 x.2)))

/-- The construction's two displayed parts are an actual proper coloring. -/
theorem bipartite (next : Equiv.Perm I) : (graph next).Colorable 2 := by
  refine ⟨SimpleGraph.Coloring.mk (fun x => if x.1 then (1 : Fin 2) else 0) ?_⟩
  rintro ⟨b,x⟩ ⟨c,y⟩ h
  cases b <;> cases c <;> simp_all [graph]

private def sideNeighbors (next : Equiv.Perm I) : Side I → Finset (Side I)
  | none => Finset.univ.image (fun i => some (true,i))
  | some (false,i) => insert (some (true,i))
      ((Finset.univ.erase i).image (fun j => some (false,j)))
  | some (true,i) => insert none (insert (some (false,i))
      ((Finset.univ \ {next i,next (next i)}).image (fun j => some (true,j))))

private theorem mem_sideNeighbors (next : Equiv.Perm I) (a b : Side I) :
    b ∈ sideNeighbors next a ↔ link next a b := by
  cases a with
  | none => cases b with
    | none => simp [sideNeighbors,link]
    | some b => rcases b with ⟨k,j⟩; cases k <;> simp [sideNeighbors,link]
  | some a => rcases a with ⟨k,i⟩; cases k <;> cases b with
    | none => simp [sideNeighbors,link]
    | some b => rcases b with ⟨l,j⟩; cases l <;>
        simp [sideNeighbors,link,eq_comm,and_comm]

private theorem right_neighbors (next : Equiv.Perm I) (a b : Side I) :
    link next a b ↔ link next.symm b a := by
  cases a with
  | none => cases b with
    | none => simp [link]
    | some b => rcases b with ⟨k,j⟩; cases k <;> simp [link]
  | some a => rcases a with ⟨k,i⟩; cases k <;> cases b with
    | none => simp [link]
    | some b => rcases b with ⟨l,j⟩; cases l <;>
        simp [link,Equiv.eq_symm_apply,eq_comm]

private theorem sideNeighbors_card (next : Equiv.Perm I)
    (hnext : ∀ i, next i ≠ i) (a : Side I) :
    (sideNeighbors next a).card = Fintype.card I := by
  have hi (b : Bool) : Function.Injective (fun i : I => some (b,i)) := by
    intro i j h; simpa using h
  cases a with
  | none => simp [sideNeighbors,Finset.card_image_of_injective _ (hi true)]
  | some a =>
    rcases a with ⟨k,i⟩
    cases k with
    | false =>
      have hn : some (true,i) ∉ (Finset.univ.erase i).image (fun j => some (false,j)) := by simp
      have hd : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨i⟩
      simp [sideNeighbors,Finset.card_insert_of_notMem hn,
        Finset.card_image_of_injective _ (hi false)]
      omega
    | true =>
      have hne : next i ≠ next (next i) := fun h => hnext i (next.injective h).symm
      have hc := Finset.card_sdiff_add_card_eq_card
        (Finset.subset_univ ({next i,next (next i)} : Finset I))
      simp only [Finset.card_univ,Finset.card_pair hne] at hc
      have hnone : none ∉ insert (some (false,i))
          ((Finset.univ \ {next i,next (next i)}).image (fun j => some (true,j))) := by simp
      have hfalse : some (false,i) ∉
          (Finset.univ \ {next i,next (next i)}).image (fun j => some (true,j)) := by simp
      rw [sideNeighbors,Finset.card_insert_of_notMem hnone,
        Finset.card_insert_of_notMem hfalse,Finset.card_image_of_injective _ (hi true)]
      omega

/-- Every vertex has degree d; the proof counts symbolic neighborhoods. -/
theorem regular (next : Equiv.Perm I) (hnext : ∀ i, next i ≠ i)
    (v : Vertex I) : DegreeCapacity.degree (graph next) v = Fintype.card I := by
  classical
  have hrev : ∀ i, next.symm i ≠ i := by
    intro i he
    have := congrArg next he
    exact hnext i (by simpa using this.symm)
  rcases v with ⟨b,a⟩
  cases b with
  | false =>
    have he : Finset.univ.filter ((graph next).Adj (false,a)) =
        (sideNeighbors next a).image (fun w => (true,w)) := by
      ext v
      rcases v with ⟨b,w⟩
      cases b <;> simp [graph,mem_sideNeighbors]
    change (Finset.univ.filter _).card = _
    rw [he,Finset.card_image_of_injective _ (by intro x y h; exact congrArg Prod.snd h)]
    exact sideNeighbors_card next hnext a
  | true =>
    have he : Finset.univ.filter ((graph next).Adj (true,a)) =
        (sideNeighbors next.symm a).image (fun w => (false,w)) := by
      ext v
      rcases v with ⟨b,w⟩
      cases b <;> simp [graph,mem_sideNeighbors,← right_neighbors]
    change (Finset.univ.filter _).card = _
    rw [he,Finset.card_image_of_injective _ (by intro x y h; exact congrArg Prod.snd h)]
    exact sideNeighbors_card next.symm hrev a

def selected : Side I → Prop
  | none => True
  | some (k,_) => k = false

instance : DecidablePred (@selected I) := fun a => by
  cases a <;> simp only [selected] <;> infer_instance

def selection : Finset (Vertex I) := Finset.univ.filter (fun x => selected x.2)

private theorem selected_outside_neighbors (next : Equiv.Perm I)
    (b : Bool) (i : I) (w : Vertex I) (hw : selected w.2) :
    (graph next).Adj (b,some (true,i)) w ↔
      w = (!b,some (false,i)) ∨ w = (!b,none) := by
  rcases w with ⟨c,a⟩
  cases b <;> cases c <;> cases a with
  | none => simp_all [graph,link]
    | some a => rcases a with ⟨k,j⟩; cases k <;> simp_all [selected,graph,link] <;> tauto

private theorem hub_no_selected_neighbor (next : Equiv.Perm I)
    (b : Bool) (w : Vertex I) (hw : selected w.2) :
    ¬ (graph next).Adj (b,none) w := by
  rcases w with ⟨c,a⟩
  cases b <;> cases c <;> cases a with
  | none => simp [graph,link]
  | some a => rcases a with ⟨k,j⟩; cases k <;> simp_all [selected,graph,link]

/-- The written high vertices and two hubs form an actual minimal selection.
Every outside vertex has its high mate and opposite hub; deletion of a high
vertex leaves just the isolate hub, while a deleted hub fails at itself. -/
theorem selection_minimal (next : Equiv.Perm I) :
    IsMinimalStarForming (graph next) 2 selection := by
  apply (regular_minimal_iff _ _).mp
  apply Subcubic.minimal_of_deletion_failures
  · rintro ⟨b,a⟩ ha
    simp only [selection,Finset.mem_filter,Finset.mem_univ,true_and] at ha
    cases a with
    | none => exact (ha trivial).elim
    | some a =>
      rcases a with ⟨k,i⟩
      cases k with
      | false => exact (ha rfl).elim
      | true =>
        refine Or.inl ⟨(!b,some (false,i)),(!b,none),?_,?_,by simp,?_,?_⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,trivial⟩
        · cases b <;> simp [graph,link]
        · cases b <;> simp [graph,link]
  · rintro ⟨b,a⟩ ha
    have hs : selected a := by simpa [selection] using ha
    cases a with
    | none =>
      refine ⟨(b,none),by simp,?_⟩
      rintro (⟨u,v,hu,hv,_,huv,_⟩ | ⟨u,v,hu,hv,huv,_⟩)
      · exact hub_no_selected_neighbor next b u (by simpa [selection] using hu.1) huv
      · exact hub_no_selected_neighbor next b u (by simpa [selection] using hu.1) huv
    | some a =>
      rcases a with ⟨k,i⟩
      have hk : k = false := hs
      subst k
      refine ⟨(!b,some (true,i)),?_,?_⟩
      · intro hn
        exact Bool.noConfusion (Finset.mem_filter.mp hn.1).2
      have hsingle (w : Vertex I) (hw : w ∈ selection ∧ w ≠ (b,some (false,i)))
          (hadj : (graph next).Adj (!b,some (true,i)) w) : w = (b,none) := by
        rcases (selected_outside_neighbors next (!b) i w
          (by simpa [selection] using hw.1)).mp hadj with he | he
        · exact (hw.2 (by simpa using he)).elim
        · simpa using he
      rintro (⟨u,v,hu,hv,hne,huv,hvv⟩ | ⟨u,v,hu,hv,huv,hev⟩)
      · exact hne ((hsingle u hu huv).trans (hsingle v hv hvv).symm)
      · have he := hsingle u hu huv
        subst u
        exact hub_no_selected_neighbor next b v (by simpa [selection] using hv.1) hev

/-- The displayed minimal selection has exactly two high classes and two hubs. -/
theorem selection_card : (selection : Finset (Vertex I)).card = 2 * Fintype.card I + 2 := by
  classical
  let A : Finset (Side I) := insert none (Finset.univ.image (fun i : I => some (false,i)))
  have he : (selection : Finset (Vertex I)) = Finset.univ.product A := by
    ext v
    rcases v with ⟨b,a⟩
    simp only [selection,Finset.mem_filter,Finset.mem_univ,true_and,
      Finset.product_eq_sprod,Finset.mem_product]
    cases a with
    | none => simp [selected,A]
    | some a => rcases a with ⟨k,i⟩; cases k <;> simp [selected,A]
  rw [he,Finset.product_eq_sprod,Finset.card_product]
  have hi : Function.Injective (fun i : I => some (false,i)) := by intro i j h; simpa using h
  simp [A,Finset.card_image_of_injective _ hi]
  omega

/-- Degree capacity closes the all-size SF upper bound without enumerating
any family parameter. The beta upper bound is a separate argument. -/
theorem sf_graph (next : Equiv.Perm I) (hnext : ∀ i, next i ≠ i)
    (hd : 3 ≤ Fintype.card I) :
    SF (graph next) 2 = 2 * Fintype.card I + 2 := by
  classical
  have hl : 2 * Fintype.card I + 2 ≤ SF (graph next) 2 := by
    rw [← selection_card]
    exact Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,selection_minimal next⟩)
  obtain ⟨S,hS,hc⟩ := sf_attained (graph next) 2
  have hb := DegreeCapacity.regular_selection_bound (graph next) S hS
    (Fintype.card I) (by omega) (regular next hnext)
  have hn : Fintype.card (Vertex I) = 4 * Fintype.card I + 2 := by
    simp [Vertex,Side,Fintype.card_prod]; omega
  rw [hc,hn] at hb
  have hm : 2 * Fintype.card I - 1 + 1 = 2 * Fintype.card I := by omega
  nlinarith

private def part (D : Finset (Vertex I)) (b k : Bool) : Finset I :=
  Finset.univ.filter (fun i => (b,some (k,i)) ∈ D)

private theorem card_parts (D : Finset (Vertex I)) :
    D.card = (part D false false).card + (part D true false).card +
      (part D false true).card + (part D true true).card +
      (if (false,none) ∈ D then 1 else 0) +
      (if (true,none) ∈ D then 1 else 0) := by
  have hc : D.card = ∑ v : Vertex I, if v ∈ D then 1 else 0 := by simp
  rw [hc]
  simp only [Vertex,Side,Fintype.sum_prod_type,Fintype.sum_bool,Fintype.sum_option]
  have hp (b k : Bool) : (∑ i : I, if (b,some (k,i)) ∈ D then 1 else 0) =
      (part D b k).card := by simp [part]
  simp only [hp]
  omega

private theorem part_cap (next : Equiv.Perm I) (D : Finset (Vertex I))
    (hD : IsKIndependent (graph next) 2 D) (v : Vertex I) (hv : v ∈ D)
    (b k : Bool) (E : Finset I)
    (hE : ∀ i ∈ part D b k, i ∉ E → (graph next).Adj v (b,some (k,i))) :
    (part D b k).card ≤ E.card + 1 := by
  have hs : (part D b k \ E).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    have hai := Finset.mem_sdiff.mp hi
    have haj := Finset.mem_sdiff.mp hj
    have he := (SubQuorum.DoubleStarGrafting.independent_iff _ _).mp hD v hv
      (b,some (k,i)) (Finset.mem_filter.mp hai.1).2
      (b,some (k,j)) (Finset.mem_filter.mp haj.1).2
      (hE i hai.1 hai.2) (hE j haj.1 haj.2)
    simpa using he
  have hsub : part D b k ⊆ (part D b k \ E) ∪ E := by
    intro i hi
    by_cases he : i ∈ E
    · exact Finset.mem_union_right _ he
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hi,he⟩)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  omega

private theorem high_mixed_caps (next : Equiv.Perm I) (D : Finset (Vertex I))
    (hD : IsKIndependent (graph next) 2 D) :
    (part D false false).card = 0 ∨ (part D true false).card = 0 ∨
      ((part D false false).card ≤ 2 ∧ (part D true false).card ≤ 2) := by
  by_cases ha : (part D false false).Nonempty
  · by_cases hb : (part D true false).Nonempty
    · obtain ⟨i,hi⟩ := ha
      obtain ⟨j,hj⟩ := hb
      right; right
      constructor
      · have h := part_cap next D hD (true,some (false,j))
          (Finset.mem_filter.mp hj).2 false false {j} (by
            intro k _ hk
            have hne : k ≠ j := by simpa using hk
            simp [graph,link,hne])
        simpa using h
      · have h := part_cap next D hD (false,some (false,i))
          (Finset.mem_filter.mp hi).2 true false {i} (by
            intro k _ hk
            have hne : i ≠ k := Ne.symm (by simpa using hk)
            simp [graph,link,hne])
        simpa using h
    · right; left; exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hb)
  · left; exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp ha)

private theorem outside_mixed_caps (next : Equiv.Perm I) (D : Finset (Vertex I))
    (hD : IsKIndependent (graph next) 2 D) :
    (part D false true).card = 0 ∨ (part D true true).card = 0 ∨
      ((part D false true).card ≤ 3 ∧ (part D true true).card ≤ 3) := by
  by_cases ha : (part D false true).Nonempty
  · by_cases hb : (part D true true).Nonempty
    · obtain ⟨i,hi⟩ := ha
      obtain ⟨j,hj⟩ := hb
      right; right
      constructor
      · have h := part_cap next D hD (true,some (true,j))
          (Finset.mem_filter.mp hj).2 false true {next.symm j,next.symm (next.symm j)} (by
            intro k _ hk
            have he : k ≠ next.symm j ∧ k ≠ next.symm (next.symm j) := by simpa using hk
            exact Or.inr ⟨rfl,rfl,
              (right_neighbors next (some (true,k)) (some (true,j))).mpr he⟩)
        have hc := Finset.card_le_card (Finset.subset_univ
          ({next.symm j,next.symm (next.symm j)} : Finset I))
        have hp : ({next.symm j,next.symm (next.symm j)} : Finset I).card ≤ 2 :=
          Finset.card_le_two
        omega
      · have h := part_cap next D hD (false,some (true,i))
          (Finset.mem_filter.mp hi).2 true true {next i,next (next i)} (by
            intro k _ hk
            have he : k ≠ next i ∧ k ≠ next (next i) := by simpa using hk
            exact Or.inl ⟨rfl,rfl,he⟩)
        have hp : ({next i,next (next i)} : Finset I).card ≤ 2 := Finset.card_le_two
        omega
    · right; left; exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hb)
  · left; exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp ha)

private theorem hub_caps (next : Equiv.Perm I) (D : Finset (Vertex I))
    (hD : IsKIndependent (graph next) 2 D) :
    ((false,none) ∈ D → (part D true true).card ≤ 1) ∧
      ((true,none) ∈ D → (part D false true).card ≤ 1) := by
  constructor
  · intro hp
    have h := part_cap next D hD (false,none) hp true true ∅ (by
      intro i _ _; exact Or.inl ⟨rfl,rfl,rfl⟩)
    simpa using h
  · intro hq
    have h := part_cap next D hD (true,none) hq false true ∅ (by
      intro i _ _; exact Or.inr ⟨rfl,rfl,rfl⟩)
    simpa using h

/-- The original neighborhood case proof for every degree at least five.
The two excluded outside neighbors and the missing crown diagonal are counted
in the actual graph, before the six class sizes are combined. -/
theorem dissociation_cap_ge_five (next : Equiv.Perm I) (hd : 5 ≤ Fintype.card I)
    (D : Finset (Vertex I)) (hD : IsKIndependent (graph next) 2 D) :
    D.card ≤ 2 * Fintype.card I + 1 := by
  have ht := card_parts D
  have ha := high_mixed_caps next D hD
  have hx := outside_mixed_caps next D hD
  have hh := hub_caps next D hD
  have hb (b k : Bool) : (part D b k).card ≤ Fintype.card I :=
    Finset.card_le_univ _
  have h0 := hb false false
  have h1 := hb true false
  have h2 := hb false true
  have h3 := hb true true
  by_cases hp : (false,none) ∈ D <;> by_cases hq : (true,none) ∈ D <;>
    simp only [hp,hq,ite_true,ite_false] at ht <;>
    rcases ha with ha | ha | ⟨ha,hb⟩ <;>
    rcases hx with hx | hx | ⟨hx,hy⟩ <;>
    first | (have := hh.1 hp; have := hh.2 hq; omega)
          | (have := hh.1 hp; omega)
          | (have := hh.2 hq; omega)
          | omega

/-- Actual beta attainment for all symbolic constructions of degree at least
five. The cyclic d=3,4 boundary constructions are separate cases. -/
theorem beta_graph_ge_five (next : Equiv.Perm I) (hd : 5 ≤ Fintype.card I) :
    beta (graph next) 2 = 2 * Fintype.card I + 1 := by
  classical
  have hu : beta (graph next) 2 ≤ 2 * Fintype.card I + 1 := by
    apply Finset.sup_le
    intro D hD
    exact dissociation_cap_ge_five next hd D (Finset.mem_filter.mp hD).2
  have hl := BipartiteBounds.card_le_two_beta (graph next) (bipartite next)
  have hn : Fintype.card (Vertex I) = 4 * Fintype.card I + 2 := by
    simp [Vertex,Side,Fintype.card_prod]; omega
  rw [hn] at hl
  omega

private theorem rotate_ne {d : ℕ} (hd : 2 ≤ d) (i : Fin d) : finRotate d i ≠ i := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  intro he
  have hv := congrArg Fin.val he
  rw [coe_finRotate] at hv
  split_ifs at hv with hi
  · have hii := congrArg Fin.val hi
    simp only [Fin.val_last] at hii
    omega
  · omega

private abbrev cycleGraph (d : ℕ) : SimpleGraph (Vertex (Fin d)) := graph (finRotate d)

private theorem cubic_free :
    SubQuorum.C4FreeRepresentatives.NoFourCycle (cycleGraph 3).Adj := by
  unfold SubQuorum.C4FreeRepresentatives.NoFourCycle
  decide +kernel

private theorem cubic_beta : beta (cycleGraph 3) 2 = 7 := by
  have hc : ∀ v w, (cycleGraph 3).Adj v w → v.1 ≠ w.1 := by
    rintro ⟨b,v⟩ ⟨c,w⟩ h
    cases b <;> cases c <;> simp_all [cycleGraph,graph]
  have hr : ∀ v, DegreeCapacity.degree (cycleGraph 3) v = 3 := by
    intro v
    simpa [cycleGraph] using regular (finRotate 3) (rotate_ne (by decide)) v
  have hs : ∀ b : Bool, (Finset.univ.filter (fun v : Vertex (Fin 3) => v.1 = b)).card = 7 := by
    decide +kernel
  exact (SubQuorum.C4FreeRepresentatives.threshold_parameters (cycleGraph 3)
    Prod.fst hc cubic_free 3 7 (by decide) hr hs (by decide)).1
private def fourCycles : List (List (Vertex (Fin 4))) := [
  [(false,none), (true,some (true,0)), (false,some (true,0)), (true,some (true,3))],
  [(false,none), (true,some (true,0)), (false,some (true,1)), (true,some (true,1))],
  [(false,none), (true,some (true,1)), (false,some (true,2)), (true,some (true,2))],
  [(false,none), (true,some (true,2)), (false,some (true,3)), (true,some (true,3))],
  [(false,some (false,0)), (true,some (false,2)), (false,some (false,1)), (true,some (false,3))],
  [(false,some (false,0)), (true,some (false,1)), (false,some (false,2)), (true,some (false,3))],
  [(false,some (false,0)), (true,some (false,1)), (false,some (false,3)), (true,some (false,2))],
  [(false,some (false,0)), (true,some (false,1)), (false,some (true,1)), (true,some (true,0))],
  [(false,some (false,1)), (true,some (false,0)), (false,some (false,2)), (true,some (false,3))],
  [(false,some (false,1)), (true,some (false,0)), (false,some (false,3)), (true,some (false,2))],
  [(false,some (false,1)), (true,some (false,2)), (false,some (true,2)), (true,some (true,1))],
  [(false,some (false,2)), (true,some (false,0)), (false,some (false,3)), (true,some (false,1))],
  [(false,some (false,2)), (true,some (false,3)), (false,some (true,3)), (true,some (true,2))],
  [(false,some (false,3)), (true,some (false,0)), (false,some (true,0)), (true,some (true,3))],
  [(false,some (true,0)), (true,none), (false,some (true,1)), (true,some (true,0))],
  [(false,some (true,0)), (true,none), (false,some (true,3)), (true,some (true,3))],
  [(false,some (true,1)), (true,none), (false,some (true,2)), (true,some (true,1))],
  [(false,some (true,2)), (true,none), (false,some (true,3)), (true,some (true,2))]]

private def fourCycleVertex (q : Fin 18) (t : Fin 4) : Vertex (Fin 4) :=
  ((fourCycles.getD q.val []).getD t.val (false,none))

private theorem fourCycleFacts : ∀ q : Fin 18,
    Function.Injective (fourCycleVertex q) ∧
      (cycleGraph 4).Adj (fourCycleVertex q 0) (fourCycleVertex q 1) ∧
      (cycleGraph 4).Adj (fourCycleVertex q 1) (fourCycleVertex q 2) ∧
      (cycleGraph 4).Adj (fourCycleVertex q 2) (fourCycleVertex q 3) ∧
      (cycleGraph 4).Adj (fourCycleVertex q 3) (fourCycleVertex q 0) := by
  decide +kernel

private def fourSquare (q : Fin 18) : SquareCapacity.Square (cycleGraph 4) where
  vertex := fourCycleVertex q
  injective := (fourCycleFacts q).1
  edge01 := (fourCycleFacts q).2.1
  edge12 := (fourCycleFacts q).2.2.1
  edge23 := (fourCycleFacts q).2.2.2.1
  edge30 := (fourCycleFacts q).2.2.2.2

private theorem four_uniform : ∀ v : Vertex (Fin 4),
    (∑ q : Fin 18, if v ∈ (fourSquare q).carrier then (1/4 : ℚ) else 0) = 1 := by
  decide +kernel

private theorem quartic_beta : beta (cycleGraph 4) 2 = 9 := by
  have h := SquareCapacity.beta_exact (cycleGraph 4) (bipartite (finRotate 4))
    fourSquare (fun _ => (1/4 : ℚ)) (by intro _; norm_num) four_uniform
  norm_num [Vertex,Side] at h
  omega

/-- For every d at least three, the actual cyclic graph G_d attains the sharp
positive gap one. The two boundary cases use their actual C4-free or square
certificate; every d at least five uses symbolic neighborhood counting. -/
theorem cyclic_parameters (d : ℕ) (hd : 3 ≤ d) :
    Fintype.card (Vertex (Fin d)) = 4*d+2 ∧
      (graph (finRotate d)).Colorable 2 ∧
      (∀ v, DegreeCapacity.degree (graph (finRotate d)) v = d) ∧
      beta (graph (finRotate d)) 2 = 2*d+1 ∧
      SF (graph (finRotate d)) 2 = 2*d+2 := by
  refine ⟨by simp [Vertex,Side]; omega,bipartite _,?_,?_,?_⟩
  · intro v; simpa only [Fintype.card_fin] using regular (finRotate d) (rotate_ne (by omega)) v
  · by_cases he : d = 3
    · subst d; exact cubic_beta
    · by_cases hf : d = 4
      · subst d; exact quartic_beta
      · simpa only [Fintype.card_fin] using beta_graph_ge_five (finRotate d)
          (by simpa only [Fintype.card_fin] using (show 5 ≤ d by omega))
  · simpa only [Fintype.card_fin] using sf_graph (finRotate d) (rotate_ne (by omega))
      (by simpa only [Fintype.card_fin] using hd)

end D5.S3.Combinatorics.Graph.StarForming.SharpRegular
