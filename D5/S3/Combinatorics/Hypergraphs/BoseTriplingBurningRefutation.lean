/- GID: D5/S3/Combinatorics/Hypergraphs/BoseTriplingBurningRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Hypergraphs/BoseTriplingBurningRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Hypergraphs/BoseTriplingBurningRefutation.claim; result=D5/S3/Combinatorics/Hypergraphs/BoseTriplingBurningRefutation.result; claim=D5/S3/Combinatorics/Hypergraphs/BoseTriplingBurningRefutation.claim
   digest: Ordinary burning of a cyclic Steiner triple system and its Bose tripling. -/

/-
result:
  proof_shape: content
  direct_frozen_dependencies: none
  escape_witness: burning13 and burning39 certify the exact increase from 5 to 6.
  admission_basis: open-problem-resolution (#34982; Refuted)
  utility: certified-instance, refutes claim for the cited Bose tripling.
The designated refutation result is exempt from four-slot escape registration.
-/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import OmegaBuild.Commands

/-!
# Burning under Bose tripling

The translates of `{0,1,4}` and `{0,2,7}` modulo 13 give a nondegenerate
system with burning number 5. Its Bose tripling has burning number 6.

Source question: Burgess, Danziger, Jones, Marbach and Pike,
arXiv:2608.25627v1, §5. Registered scope: trureturing issue #34982.
-/

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.Combinatorics.Hypergraphs.BoseTriplingBurningRefutation

/-- Pair completion of a Steiner triple system, with the diagonal extended idempotently. -/
structure Steiner (α : Type) where
  complete : α → α → α
  comm : ∀ x y, complete x y = complete y x
  idem : ∀ x, complete x x = x
  cancel : ∀ x y, complete x (complete x y) = y

variable {α : Type} [LinearOrder α]

private def pairs (s : Finset α) : Finset (α × α) :=
  (s.product s).filter fun p => p.1 < p.2

/-- Simultaneously add the completions of all pairs in the preceding burned set. -/
def spread (H : Steiner α) (s : Finset α) : Finset α :=
  s ∪ (pairs s).image fun p => H.complete p.1 p.2

/-- A round propagates from the preceding burned set and adds its chosen source. -/
def step (H : Steiner α) (s : Finset α) (u : α) : Finset α :=
  insert u (spread H s)

/-- Burned set after the given sources, starting from an arbitrary initial set. -/
def burned (H : Steiner α) (s : Finset α) (sources : List α) : Finset α :=
  sources.foldl (step H) s

/-- A legal source can be reached by same-round propagation, but cannot already be burned. -/
def legal (H : Steiner α) (s : Finset α) : List α → Bool
  | [] => true
  | u :: rest => decide (u ∉ s) && legal H (step H s u) rest

/-- A complete ordinary burning run from the empty set. -/
def Run [Fintype α] (H : Steiner α) (sources : List α) : Prop :=
  legal H ∅ sources = true ∧ burned H ∅ sources = Finset.univ

-- Offsets of the third point from the first, indexed by the signed difference y - x.
private def offsets : Array (Fin 13) := #[0, 4, 7, 12, 1, 11, 8, 2, 6, 10, 9, 5, 3]

private def complete13 (x y : Fin 13) : Fin 13 :=
  x + offsets[(y - x).val]!

private theorem complete13_comm : ∀ x y, complete13 x y = complete13 y x := by decide
private theorem complete13_idem : ∀ x, complete13 x x = x := by decide
private theorem complete13_cancel : ∀ x y, complete13 x (complete13 x y) = y := by decide

private def cyclic13 : Steiner (Fin 13) :=
  ⟨complete13, complete13_comm, complete13_idem, complete13_cancel⟩

private def tiltedLayer (i j : Fin 3) : Fin 3 :=
  if i = j then i + 1 else if j = i + 1 then i else j

private def verticalLayer (i j : Fin 3) : Fin 3 := 0 - i - j

private theorem tilted_comm : ∀ i j, tiltedLayer i j = tiltedLayer j i := by decide
private theorem tilted_cancel : ∀ i j, tiltedLayer i (tiltedLayer i j) = j := by decide
private theorem vertical_comm : ∀ i j, verticalLayer i j = verticalLayer j i := by decide
private theorem vertical_idem : ∀ i, verticalLayer i i = i := by decide
private theorem vertical_cancel : ∀ i j, verticalLayer i (verticalLayer i j) = j := by decide

omit [LinearOrder α] in
private theorem complete_ne_left (H : Steiner α) {x y : α} (h : x ≠ y) :
    H.complete x y ≠ x := by
  intro e
  apply h
  calc
    x = H.complete x x := (H.idem x).symm
    _ = H.complete x (H.complete x y) := congrArg (H.complete x) e.symm
    _ = y := H.cancel x y

private def boseComplete (H : Steiner α) (x y : α × Fin 3) : α × Fin 3 :=
  if x.1 = y.1 then (x.1, verticalLayer x.2 y.2)
  else (H.complete x.1 y.1, tiltedLayer x.2 y.2)

/-- Bose tripling has the vertical triples and the triples
`{(x,i), (y,i), (H.complete x y,i+1)}` with `x ≠ y`. -/
private def boseOnProduct (H : Steiner α) : Steiner (α × Fin 3) where
  complete := boseComplete H
  comm x y := by
    by_cases h : x.1 = y.1
    · simp [boseComplete, h, vertical_comm]
    · simp [boseComplete, h, Ne.symm h, H.comm x.1 y.1, tilted_comm]
  idem x := by simp [boseComplete, vertical_idem]
  cancel x y := by
    by_cases h : x.1 = y.1
    · simp [boseComplete, h, vertical_cancel]
    · simp [boseComplete, h, Ne.symm (complete_ne_left H h), H.cancel, tilted_cancel]

/-- Encode Bose points by `(x,i) ↦ 3*x+i`. -/
def bose {n : ℕ} (H : Steiner (Fin n)) : Steiner (Fin (n * 3)) where
  complete x y :=
    finProdFinEquiv ((boseOnProduct H).complete (finProdFinEquiv.symm x) (finProdFinEquiv.symm y))
  comm x y := by rw [(boseOnProduct H).comm]
  idem x := by simp only [(boseOnProduct H).idem, Equiv.apply_symm_apply]
  cancel x y := by
    simp only [Equiv.symm_apply_apply, (boseOnProduct H).cancel, Equiv.apply_symm_apply]

private def schedule13 : List (Fin 13) := [0, 1, 2, 3, 6]

-- Encoded by (x,i) ↦ 3*x+i, the sources are 0, 1, 3, 6, 4, 7.
private def schedule39 : List (Fin 39) := [0, 1, 3, 6, 4, 7]

private theorem run13 : Run cyclic13 schedule13 := by
  unfold Run
  exact ⟨by decide, by decide⟩

set_option maxRecDepth 4096 in
private theorem run39 : Run (bose cyclic13) schedule39 := by
  unfold Run
  exact ⟨by decide, by decide⟩

/-- A subsystem is a set closed under pair completion. -/
def Closed (H : Steiner α) (s : Finset α) : Prop :=
  ∀ ⦃x y⦄, x ∈ s → y ∈ s → H.complete x y ∈ s

private theorem mem_spread (H : Steiner α) (s : Finset α) (z : α) :
    z ∈ spread H s ↔ z ∈ s ∨
      ∃ x ∈ s, ∃ y ∈ s, H.complete x y = z := by
  constructor
  · intro hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact Or.inl hz
    · obtain ⟨⟨x, y⟩, hp, hz⟩ := Finset.mem_image.mp hz
      have hm := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      exact Or.inr ⟨x, hm.1, y, hm.2, hz⟩
  · rintro (hz | ⟨x, hx, y, hy, rfl⟩)
    · exact Finset.mem_union_left _ hz
    · rcases lt_trichotomy x y with h | rfl | h
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨(x, y), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, h⟩, rfl⟩)
      · exact Finset.mem_union_left _ (by simpa only [H.idem] using hx)
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨(y, x), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hy, hx⟩, h⟩, H.comm y x⟩)

private theorem spread_subset_of_closed (H : Steiner α) {s t : Finset α}
    (ht : Closed H t) (hs : s ⊆ t) : spread H s ⊆ t := by
  intro z hz
  rcases (mem_spread H s z).mp hz with h | ⟨x, hx, y, hy, rfl⟩
  · exact hs h
  · exact ht (hs hx) (hs hy)

private theorem spread_insert (H : Steiner α) (s : Finset α) (a : α) :
    spread H (insert a s) = insert a (spread H s ∪ s.image (H.complete a)) := by
  ext z
  simp only [mem_spread, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ((rfl | hz) | ⟨x, rfl | hx, y, rfl | hy, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (Or.inl hz))
    · exact Or.inl (H.idem _)
    · exact Or.inr (Or.inr ⟨y, hy, rfl⟩)
    · exact Or.inr (Or.inr ⟨x, hx, H.comm _ x⟩)
    · exact Or.inr (Or.inl (Or.inr ⟨x, hx, y, hy, rfl⟩))
  · rintro (rfl | (hz | ⟨x, hx, y, hy, rfl⟩) | ⟨y, hy, rfl⟩)
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr hz)
    · exact Or.inr ⟨x, Or.inr hx, y, Or.inr hy, rfl⟩
    · exact Or.inr ⟨a, Or.inl rfl, y, Or.inr hy, rfl⟩

private theorem spread_empty (H : Steiner α) : spread H ∅ = ∅ := by
  ext x
  simp [mem_spread]

private def block (H : Steiner α) (a b : α) : Finset α := {a, b, H.complete a b}

private theorem block_closed (H : Steiner α) (a b : α) : Closed H (block H a b) := by
  have hbc : H.complete b (H.complete a b) = a := by
    rw [H.comm a b, H.cancel]
  intro x y hx hy
  simp only [block, Finset.mem_insert, Finset.mem_singleton] at hx hy ⊢
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    grind [H.idem, H.comm, H.cancel]

private theorem spread_block (H : Steiner α) (a b : α) :
    spread H (block H a b) = block H a b :=
  Finset.Subset.antisymm (spread_subset_of_closed H (block_closed H a b) fun _ h => h)
    Finset.subset_union_left

private theorem burned_four (H : Steiner α) (a b c d : α) :
    (burned H ∅ [a, b, c, d]).card ≤ 8 := by
  have hs : spread H {a} = {a} := by
    rw [show ({a} : Finset α) = insert a ∅ by simp, spread_insert, spread_empty]
    simp
  have hp : spread H {b, a} = block H b a := by
    rw [spread_insert, hs]
    simp [block]
  change (step H (step H (step H (step H ∅ a) b) c) d).card ≤ 8
  simp only [step, spread_empty]
  change (insert d (spread H (insert c (spread H (insert b (spread H {a})))))).card ≤ 8
  rw [hs, hp, spread_insert, spread_block]
  have hb : (block H b a).card ≤ 3 := by
    unfold block
    have h₁ := Finset.card_insert_le b ({a, H.complete b a} : Finset α)
    have h₂ := Finset.card_insert_le a ({H.complete b a} : Finset α)
    rw [Finset.card_singleton] at h₂
    omega
  have himage := Finset.card_image_le (s := block H b a) (f := H.complete c)
  have hunion := Finset.card_union_le (block H b a) ((block H b a).image (H.complete c))
  have hc := Finset.card_insert_le c (block H b a ∪ (block H b a).image (H.complete c))
  have hd := Finset.card_insert_le d (insert c (block H b a ∪ (block H b a).image (H.complete c)))
  omega

private theorem card_pairs_le (s : Finset α) : (pairs s).card ≤ s.card.choose 2 := by
  rw [← Finset.card_powersetCard]
  apply Finset.card_le_card_of_injOn (fun p : α × α => ({p.1, p.2} : Finset α))
  · intro p hp
    obtain ⟨hm, hlt⟩ := Finset.mem_filter.mp hp
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hm
    exact Finset.mem_powersetCard.mpr ⟨by
      rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hx, hy⟩,
      by simp [Finset.card_insert_of_notMem, ne_of_lt hlt]⟩
  · rintro ⟨a, b⟩ hp ⟨c, d⟩ hq he
    change ({a, b} : Finset α) = {c, d} at he
    have hab : a < b := (Finset.mem_filter.mp hp).2
    have hcd : c < d := (Finset.mem_filter.mp hq).2
    have ha : a = c ∨ a = d := by
      have hm : a ∈ ({c, d} : Finset α) := he ▸ Finset.mem_insert_self _ _
      simpa using hm
    have hb : b = c ∨ b = d := by
      have hm : b ∈ ({c, d} : Finset α) :=
        he ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
      simpa using hm
    grind

private theorem card_step_le (H : Steiner α) (s : Finset α) (a : α) :
    (step H s a).card ≤ s.card + s.card.choose 2 + 1 := by
  unfold step spread
  exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right
    ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left (Finset.card_image_le.trans (card_pairs_le s)) _)) _)

private theorem burned_append (H : Steiner α) (s : Finset α) (xs ys : List α) :
    burned H s (xs ++ ys) = burned H (burned H s xs) ys := by
  exact List.foldl_append

private theorem subset_step (H : Steiner α) (s : Finset α) (a : α) : s ⊆ step H s a :=
  fun _ h => Finset.mem_insert_of_mem (Finset.mem_union_left _ h)

private theorem subset_burned (H : Steiner α) (s : Finset α) (xs : List α) :
    s ⊆ burned H s xs := by
  induction xs generalizing s with
  | nil => exact fun _ h => h
  | cons a xs ih => exact (subset_step H s a).trans (ih (step H s a))

private theorem burned_le_four [Inhabited α] (H : Steiner α) (xs : List α)
    (h : xs.length ≤ 4) : (burned H ∅ xs).card ≤ 8 := by
  let ys := List.replicate (4 - xs.length) (default : α)
  have hlen : (xs ++ ys).length = 4 := by simp [ys]; omega
  obtain ⟨a, b, c, d, he⟩ := List.length_eq_four.mp hlen
  have hcard := burned_four H a b c d
  rw [← he, burned_append] at hcard
  exact (Finset.card_le_card (subset_burned H (burned H ∅ xs) ys)).trans hcard

-- The unrestricted pair count in round five suffices at order 39.
private theorem burned_le_five [Inhabited α] (H : Steiner α) (xs : List α)
    (h : xs.length ≤ 5) : (burned H ∅ xs).card ≤ 37 := by
  induction xs using List.reverseRecOn with
  | nil => simp [burned]
  | append_singleton ys a _ =>
      have hlen : ys.length ≤ 4 := by simpa using h
      rw [burned_append]
      change (step H (burned H ∅ ys) a).card ≤ 37
      have hy := burned_le_four H ys hlen
      have hp := Nat.choose_le_choose 2 hy
      exact (card_step_le H _ _).trans (Nat.add_le_add_right (Nat.add_le_add hy hp) 1)

private theorem exists_legal_completion [Fintype α] (H : Steiner α) (s : Finset α) :
    ∃ xs, legal H s xs = true ∧ burned H s xs = Finset.univ := by
  by_cases h : s = Finset.univ
  · exact ⟨[], rfl, h⟩
  · have hs : s ⊂ Finset.univ := lt_of_le_of_ne (Finset.subset_univ _) h
    obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card (Finset.card_lt_card hs)
    have hg : s ⊂ step H s a :=
      lt_of_le_of_ne (subset_step H s a) fun e =>
        ha (e.symm ▸ Finset.mem_insert_self a (spread H s))
    obtain ⟨xs, hxs, hdone⟩ := exists_legal_completion H (step H s a)
    exact ⟨a :: xs, by simp [legal, ha, hxs], hdone⟩
termination_by (Finset.univ : Finset α).card - s.card
decreasing_by
  have h₁ := Finset.card_lt_card hg
  have h₂ := Finset.card_le_card (Finset.subset_univ (step H s a))
  omega

private theorem exists_run_length [Fintype α] (H : Steiner α) :
    ∃ k, ∃ xs : List α, Run H xs ∧ xs.length = k := by
  obtain ⟨xs, hxs, hdone⟩ := exists_legal_completion H ∅
  exact ⟨xs.length, xs, ⟨hxs, hdone⟩, rfl⟩

/-- The least length of a complete legal ordinary burning run. -/
noncomputable def burning [Fintype α] (H : Steiner α) : ℕ := by
  classical
  exact Nat.find (exists_run_length H)

private theorem burning_eq_of_run [Fintype α] {H : Steiner α} {xs : List α} (hx : Run H xs)
    (hmin : ∀ ys : List α, Run H ys → xs.length ≤ ys.length) : burning H = xs.length := by
  classical
  have hle := Nat.find_min' (exists_run_length H) ⟨xs, hx, rfl⟩
  obtain ⟨ys, hy, he⟩ := Nat.find_spec (exists_run_length H)
  unfold burning
  exact le_antisymm hle (he ▸ hmin ys hy)

private theorem burning13 : burning cyclic13 = 5 := by
  refine burning_eq_of_run run13 fun ys hy => ?_
  change 5 ≤ ys.length
  by_contra! h
  have hcard := burned_le_four cyclic13 ys (by omega)
  rw [hy.2] at hcard
  have hc : (Finset.univ : Finset (Fin 13)).card = 13 := by simp
  omega

private theorem burning39 : burning (bose cyclic13) = 6 := by
  refine burning_eq_of_run run39 fun ys hy => ?_
  change 6 ≤ ys.length
  by_contra! h
  have hcard := burned_le_five (bose cyclic13) ys (by omega)
  rw [hy.2] at hcard
  have hc : (Finset.univ : Finset (Fin 39)).card = 39 := by simp
  omega

/-- The least closed superset of the seed contains the target. -/
def Generates (H : Steiner α) (seed target : Finset α) : Prop :=
  ∀ s, Closed H s → seed ⊆ s → target ⊆ s

omit [LinearOrder α] in
private theorem exists_seed_size (H : Steiner α) (target : Finset α) :
    ∃ k, ∃ seed ⊆ target, Generates H seed target ∧ seed.card = k :=
  ⟨target.card, target, fun _ h => h, fun _ _ h => h, rfl⟩

/-- The smallest seed inside the subsystem whose closure contains the subsystem. -/
noncomputable def lazyBurning (H : Steiner α) (target : Finset α) : ℕ := by
  classical
  exact Nat.find (exists_seed_size H target)

omit [LinearOrder α] in
private theorem lazy_eq_of_seed {H : Steiner α} {target seed : Finset α}
    (hseed : seed ⊆ target) (hgen : Generates H seed target)
    (hmin : ∀ s ⊆ target, Generates H s target → seed.card ≤ s.card) :
    lazyBurning H target = seed.card := by
  classical
  have hle := Nat.find_min' (exists_seed_size H target) ⟨seed, hseed, hgen, rfl⟩
  obtain ⟨s, hs, hg, he⟩ := Nat.find_spec (exists_seed_size H target)
  unfold lazyBurning
  exact le_antisymm hle (he ▸ hmin s hs hg)

/-- All inclusion-maximal nonempty proper subsystems have lazy burning number one less. -/
def Nondegenerate [Fintype α] (H : Steiner α) : Prop :=
  ∀ K : Finset α, K.Nonempty → K ≠ Finset.univ → Closed H K →
    (∀ L : Finset α, K ⊂ L → Closed H L → L = Finset.univ) →
    lazyBurning H K = lazyBurning H Finset.univ - 1

/-- Isomorphism to the nonzero binary vectors, with distinct-pair completion by addition. -/
def Projective (H : Steiner α) : Prop :=
  ∃ d : ℕ, ∃ e : α ≃ {v : Fin (d + 1) → Fin 2 // v ≠ fun _ => 0},
    ∀ x y, x ≠ y → ∀ i, (e (H.complete x y)).val i = (e x).val i + (e y).val i

/-- Isomorphism to the ternary affine space, with completion given by the third point on a line. -/
def Affine (H : Steiner α) : Prop :=
  ∃ d : ℕ, ∃ e : α ≃ (Fin d → Fin 3),
    ∀ x y i, e (H.complete x y) i = 0 - e x i - e y i

private theorem not_projective13 : ¬ Projective cyclic13 := by
  classical
  rintro ⟨d, e, _⟩
  have hzero : Fintype.card {v : Fin (d + 1) → Fin 2 // v = fun _ => 0} = 1 := by
    let : Unique {v : Fin (d + 1) → Fin 2 // v = fun _ => 0} :=
      ⟨⟨⟨fun _ => 0, rfl⟩⟩, fun v => Subtype.ext v.property⟩
    exact Fintype.card_unique
  have hc := Fintype.card_congr e
  rw [Fintype.card_fin, Fintype.card_subtype_compl (fun v => v = fun _ => 0),
    hzero, Fintype.card_pi_const, Fintype.card_fin] at hc
  by_cases h : d ≤ 2
  · have hb : (2 : ℕ) ^ (d + 1) ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · have hb : (2 : ℕ) ^ 4 ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega

private theorem not_affine13 : ¬ Affine cyclic13 := by
  rintro ⟨d, e, _⟩
  have hc := Fintype.card_congr e
  rw [Fintype.card_fin, Fintype.card_pi_const, Fintype.card_fin] at hc
  by_cases h : d ≤ 2
  · have hb : (3 : ℕ) ^ d ≤ 3 ^ 2 := Nat.pow_le_pow_right (by decide) h
    omega
  · have hb : (3 : ℕ) ^ 3 ≤ 3 ^ d := Nat.pow_le_pow_right (by decide) (by omega)
    omega

/-- The tripling implication of §5 of arXiv:2608.25627v1 for the cited Bose construction. -/
def claim : Prop :=
  ∀ (n : ℕ) (H : Steiner (Fin n)), 0 < n → Nondegenerate H →
    burning H < burning (bose H) → Projective H ∨ Affine H

private theorem complete13_translate (t x y : Fin 13) :
    cyclic13.complete (x + t) (y + t) = cyclic13.complete x y + t := by
  change complete13 (x + t) (y + t) = complete13 x y + t
  simp only [complete13, add_sub_add_right_eq_sub]
  ac_rfl

private def spreadThree (s : Finset (Fin 13)) : Finset (Fin 13) :=
  spread cyclic13 (spread cyclic13 (spread cyclic13 s))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
-- Kernel reduction checks every nonblock seed containing 0 in one finite decision.
private theorem zero_triples_generate :
    ∀ y z : Fin 13, 0 < y → y < z → z ≠ cyclic13.complete 0 y →
      spreadThree {0, y, z} = Finset.univ := by decide

private theorem normalized_generation {y z : Fin 13} (hy : y ≠ 0) (hz : z ≠ 0)
    (hyz : y ≠ z) (hn : z ≠ cyclic13.complete 0 y) :
    Generates cyclic13 {0, y, z} Finset.univ := by
  have hc : spreadThree {0, y, z} = Finset.univ := by
    rcases lt_or_gt_of_ne hyz with h | h
    · exact zero_triples_generate y z (bot_lt_iff_ne_bot.mpr hy) h hn
    · rw [show ({0, y, z} : Finset (Fin 13)) = {0, z, y} by ext; simp [or_comm]]
      refine zero_triples_generate z y (bot_lt_iff_ne_bot.mpr hz) h ?_
      intro e
      apply hn
      rw [e, cyclic13.cancel]
  intro s hs hseed
  rw [← hc]
  exact spread_subset_of_closed _ hs
    (spread_subset_of_closed _ hs (spread_subset_of_closed _ hs hseed))

private theorem nonblock_generates {x y z : Fin 13} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) (hn : z ≠ cyclic13.complete x y) :
    Generates cyclic13 {x, y, z} Finset.univ := by
  intro K hK hseed
  let K' : Finset (Fin 13) := Finset.univ.filter fun u => u + x ∈ K
  have mem_K' (u : Fin 13) : u ∈ K' ↔ u + x ∈ K := by simp [K']
  have hK' : Closed cyclic13 K' := by
    intro u v hu hv
    rw [mem_K', ← complete13_translate]
    exact hK ((mem_K' _).mp hu) ((mem_K' _).mp hv)
  have hy : y - x ≠ 0 := by simpa [sub_eq_zero] using hxy.symm
  have hz : z - x ≠ 0 := by simpa [sub_eq_zero] using hxz.symm
  have hyz' : y - x ≠ z - x := fun e => hyz (sub_left_injective e)
  have hn' : z - x ≠ cyclic13.complete 0 (y - x) := by
    intro e
    have he := congrArg (fun u : Fin 13 => u + x) e
    apply hn
    simpa [← complete13_translate] using he
  have hseed' : ({0, y - x, z - x} : Finset (Fin 13)) ⊆ K' := by
    rw [Finset.insert_subset_iff, Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨(mem_K' _).mpr (by simpa using hseed (by simp)),
      (mem_K' _).mpr (by simpa using hseed (by simp)),
      (mem_K' _).mpr (by simpa using hseed (by simp))⟩
  intro u _
  have hm := normalized_generation hy hz hyz' hn' K' hK' hseed' (Finset.mem_univ (u - x))
  simpa using (mem_K' _).mp hm

private theorem card_block (H : Steiner α) {x y : α} (h : x ≠ y) :
    (block H x y).card = 3 := by
  have hx := complete_ne_left H h
  have hy : H.complete x y ≠ y := H.comm x y ▸ complete_ne_left H h.symm
  exact Finset.card_eq_three.mpr ⟨x, y, H.complete x y, h, hx.symm, hy.symm, rfl⟩

omit [LinearOrder α] in
private theorem closed_small (H : Steiner α) {s : Finset α} (h : s.card ≤ 1) :
    Closed H s := by
  intro x y hx hy
  rw [Finset.card_le_one.mp h x hx y hy, H.idem]
  exact hy

private theorem pair_generates_block (H : Steiner α) (x y : α) :
    Generates H {x, y} (block H x y) := by
  intro s hs hpair
  have hx := hpair (Finset.mem_insert_self x {y})
  have hy := hpair (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
  simp [block, Finset.insert_subset_iff, hx, hy, hs hx hy]

private theorem lazy_block (H : Steiner α) {x y : α} (h : x ≠ y) :
    lazyBurning H (block H x y) = 2 := by
  have hseed : ({x, y} : Finset α).card = 2 := Finset.card_eq_two.mpr ⟨x, y, h, rfl⟩
  rw [← hseed]
  apply lazy_eq_of_seed (by simp [block, Finset.insert_subset_iff]) (pair_generates_block H x y)
  intro s _ hs
  rw [hseed]
  by_contra! hn
  have hc := Finset.card_le_card (hs s (closed_small H (by omega)) fun _ h => h)
  rw [card_block H h] at hc
  omega

private theorem lazy13 : lazyBurning cyclic13 Finset.univ = 3 := by
  let seed : Finset (Fin 13) := {0, 1, 2}
  have hseed : seed.card = 3 := by decide
  rw [← hseed]
  have hgen : Generates cyclic13 seed Finset.univ :=
    nonblock_generates (by decide) (by decide) (by decide) (by decide)
  apply lazy_eq_of_seed (Finset.subset_univ _) hgen
  intro s _ hs
  rw [hseed]
  by_contra! hn
  have hc : (Finset.univ : Finset (Fin 13)).card = 13 := by simp
  by_cases hsmall : s.card ≤ 1
  · have hcard := Finset.card_le_card (hs s (closed_small cyclic13 hsmall) fun _ h => h)
    omega
  · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp (show s.card = 2 by omega)
    have hcard := Finset.card_le_card (hs (block cyclic13 x y) (block_closed cyclic13 x y)
      (by simp [block, Finset.insert_subset_iff]))
    rw [card_block cyclic13 hxy] at hcard
    omega

private theorem nondegenerate13 : Nondegenerate cyclic13 := by
  intro K hK hproper hclosed hmax
  obtain ⟨x, hx⟩ := hK
  have hy : ∃ y ∈ K, x ≠ y := by
    by_contra! h
    let L := block cyclic13 x (x + 1)
    have hLcard : L.card = 3 := card_block _ (by
      exact fun e => (by decide : (0 : Fin 13) ≠ 1) (by simpa using congrArg (· - x) e))
    have hKL : K ⊆ L := by
      intro u hu
      rw [← h u hu]
      simp [L, block]
    have hcard : K.card ≤ 1 :=
      Finset.card_le_one.mpr fun a ha b hb => (h a ha).symm.trans (h b hb)
    have he := hmax L (lt_of_le_of_ne hKL fun e => by rw [e, hLcard] at hcard; omega)
      (block_closed _ _ _)
    rw [he] at hLcard
    simp at hLcard
  obtain ⟨y, hy, hxy⟩ := hy
  have hb : block cyclic13 x y ⊆ K := pair_generates_block cyclic13 x y K hclosed
    (by simp [Finset.insert_subset_iff, hx, hy])
  have he : K = block cyclic13 x y := by
    apply Finset.Subset.antisymm _ hb
    intro z hz
    by_contra hn
    simp only [block, Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    have hgen := nonblock_generates hxy (fun e => hn.1 e.symm) (fun e => hn.2.1 e.symm) hn.2.2
    have hall : Finset.univ ⊆ K := hgen K hclosed
      (by simp [Finset.insert_subset_iff, hx, hy, hz])
    exact hproper (Finset.Subset.antisymm (Finset.subset_univ _) hall)
  rw [he, lazy_block _ hxy, lazy13]

/-- The cyclic order-13 system refutes the registered Bose tripling implication. -/
theorem result : ¬ claim := by
  intro h
  have hincrease : burning cyclic13 < burning (bose cyclic13) := by
    rw [burning13, burning39]
    decide
  exact (h 13 cyclic13 (by decide) nondegenerate13 hincrease).elim not_projective13 not_affine13

end D5.S3.Combinatorics.Hypergraphs.BoseTriplingBurningRefutation
