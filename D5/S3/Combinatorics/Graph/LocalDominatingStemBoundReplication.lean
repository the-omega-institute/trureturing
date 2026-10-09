/- GID: D5/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LocalDominatingStemBoundReplication
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Finite]
   utility: none
   digest: A hub with one pendant leaf connects arbitrary replicated partial dominating families. -/

import D5.S3.Combinatorics.Graph.DominatingSetAverage
import D5.S3.Combinatorics.Graph.LocalDominatingStemBoundArithmetic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.LocalDominatingStemBoundReplication

open Finset DominatingSetAverage

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev RepVertex (r : ℕ) (V : Type*) := (Fin r × V) ⊕ Fin 2

def hub (r : ℕ) : RepVertex r V := Sum.inr 0

def pendant (r : ℕ) : RepVertex r V := Sum.inr 1

/-- Copies of H joined to a hub at precisely the vertices of U, with one pendant leaf. -/
def replicated (H : SimpleGraph V) (U : Finset V) (r : ℕ) : SimpleGraph (RepVertex r V) where
  Adj x y := match x, y with
    | Sum.inl (i, v), Sum.inl (j, w) => i = j ∧ H.Adj v w
    | Sum.inl (_, v), Sum.inr k => k = 0 ∧ v ∈ U
    | Sum.inr k, Sum.inl (_, v) => k = 0 ∧ v ∈ U
    | Sum.inr k, Sum.inr l => k ≠ l
  symm := ⟨by
    intro x y h
    cases x with
    | inl x => cases y with
      | inl y => exact ⟨h.1.symm, h.2.symm⟩
      | inr y => exact h
    | inr x => cases y with
      | inl y => exact h
      | inr y => exact h.symm⟩
  loopless := ⟨by
    intro x
    cases x with
    | inl x => exact fun h => H.irrefl h.2
    | inr x => exact fun h => h rfl⟩

noncomputable instance replicated_decidable (H : SimpleGraph V) (U : Finset V) (r : ℕ) :
    DecidableRel (replicated H U r).Adj := Classical.decRel _

/-- Restrict a set of replicated vertices to one copy. -/
def copySlice (r : ℕ) (S : Finset (RepVertex r V)) (i : Fin r) : Finset V :=
  univ.filter (fun x => Sum.inl (i, x) ∈ S)

@[simp] theorem mem_copySlice (r : ℕ) (S : Finset (RepVertex r V)) (i : Fin r) (x : V) :
    x ∈ copySlice r S i ↔ Sum.inl (i, x) ∈ S := by simp [copySlice]

/-- Domination required outside U; the hub will dominate the remaining vertices. -/
def PartialDominating (H : SimpleGraph V) (U : Finset V) (S : Finset V) : Prop :=
  ∀ x, x ∉ U → x ∈ S ∨ ∃ y ∈ S, H.Adj x y

noncomputable def partialSets (H : SimpleGraph V) (U : Finset V) : Finset (Finset V) := by
  classical
  exact univ.powerset.filter (PartialDominating H U)

omit [DecidableEq V] in
@[simp] theorem mem_partialSets (H : SimpleGraph V) (U : Finset V) (S : Finset V) :
    S ∈ partialSets H U ↔ PartialDominating H U S := by
  classical
  simp [partialSets]

omit [DecidableEq V] in
theorem domSets_subset_partialSets (H : SimpleGraph V) (U : Finset V) :
    domSets H ⊆ partialSets H U := by
  classical
  intro S hS
  exact (mem_partialSets H U S).mpr (fun x _ => mem_domSets.mp hS x)

omit [DecidableEq V] in
theorem replicated_card (r : ℕ) :
    Fintype.card (RepVertex r V) = r * Fintype.card V + 2 := by
  simp [RepVertex]

omit [DecidableEq V] in
theorem replicated_no_isolates (H : SimpleGraph V) (U : Finset V) (r : ℕ)
    [DecidableRel H.Adj]
    (hH : ∀ x, 0 < H.degree x) : ∀ x, 0 < (replicated H U r).degree x := by
  classical
  intro x
  apply ((replicated H U r).degree_pos_iff_exists_adj x).mpr
  cases x with
  | inl x =>
    obtain ⟨y, hy⟩ := (H.degree_pos_iff_exists_adj x.2).mp (hH x.2)
    exact ⟨Sum.inl (x.1, y), rfl, hy⟩
  | inr x =>
    by_cases hx : x = 0
    · exact ⟨pendant r, by simp [replicated, pendant, hx]⟩
    · exact ⟨hub r, by simpa [replicated, hub] using hx⟩

/-- With the hub selected, domination separates into the partially dominated copies. -/
theorem dominating_with_hub_iff (H : SimpleGraph V) (U : Finset V) (r : ℕ)
    (S : Finset (RepVertex r V)) (hz : hub r ∈ S) :
    (replicated H U r).IsDominating (S : Set (RepVertex r V)) ↔
      ∀ i, PartialDominating H U (copySlice r S i) := by
  constructor
  · intro h i x hx
    rcases h (Sum.inl (i, x)) with hmem | ⟨y, hy, hadj⟩
    · exact Or.inl ((mem_copySlice r S i x).mpr hmem)
    · cases y with
      | inl y =>
        change i = y.1 ∧ H.Adj x y.2 at hadj
        exact Or.inr ⟨y.2, (mem_copySlice r S i y.2).mpr (hadj.1 ▸ hy), hadj.2⟩
      | inr y => exact False.elim (hx hadj.2)
  · intro h x
    cases x with
    | inl x =>
      by_cases hx : x.2 ∈ U
      · exact Or.inr ⟨hub r, hz, rfl, hx⟩
      · rcases h x.1 x.2 hx with hm | ⟨y, hy, hadj⟩
        · exact Or.inl ((mem_copySlice r S x.1 x.2).mp hm)
        · exact Or.inr ⟨Sum.inl (x.1, y),
            (mem_copySlice r S x.1 y).mp hy, rfl, hadj⟩
    | inr x =>
      by_cases hx : x = 0
      · exact Or.inl (hx ▸ hz)
      · exact Or.inr ⟨hub r, hz, hx⟩

/-- Omitting the hub forces its leaf and internal domination of every copy. -/
theorem dominating_without_hub_iff (H : SimpleGraph V) (U : Finset V) (r : ℕ)
    (S : Finset (RepVertex r V)) (hz : hub r ∉ S) :
    (replicated H U r).IsDominating (S : Set (RepVertex r V)) ↔
      pendant r ∈ S ∧ ∀ i, H.IsDominating (copySlice r S i : Set V) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rcases h (pendant r) with hmem | ⟨y, hy, hadj⟩
      · exact hmem
      · cases y with
        | inl y => exact False.elim (by simp [replicated, pendant] at hadj)
        | inr y =>
          have hyzero : y = 0 := by
            change (1 : Fin 2) ≠ y at hadj
            fin_cases y <;> simp_all
          exact False.elim (hz (by simpa only [hub, hyzero, Finset.mem_coe] using hy))
    · intro i x
      rcases h (Sum.inl (i, x)) with hm | ⟨y, hy, hadj⟩
      · exact Or.inl ((mem_copySlice r S i x).mpr hm)
      · cases y with
        | inl y =>
          change i = y.1 ∧ H.Adj x y.2 at hadj
          exact Or.inr ⟨y.2, (mem_copySlice r S i y.2).mpr (hadj.1 ▸ hy), hadj.2⟩
        | inr y => exact False.elim (hz (by simpa only [hub, hadj.1, Finset.mem_coe] using hy))
  · rintro ⟨hw, h⟩ x
    cases x with
    | inl x =>
      rcases h x.1 x.2 with hm | ⟨y, hy, hadj⟩
      · exact Or.inl ((mem_copySlice r S x.1 x.2).mp hm)
      · exact Or.inr ⟨Sum.inl (x.1, y),
          (mem_copySlice r S x.1 y).mp hy, rfl, hadj⟩
    | inr x =>
      by_cases hx : x = 1
      · exact Or.inl (hx ▸ hw)
      · exact Or.inr ⟨pendant r, hw, hx⟩

/-- Assemble arbitrary copy subsets with independent choices for the hub and its leaf. -/
def assemble (r : ℕ) (z w : Bool) (f : Fin r → Finset V) : Finset (RepVertex r V) := by
  let p : RepVertex r V → Prop := fun x => match x with
    | Sum.inl (i, v) => v ∈ f i
    | Sum.inr k => if k = 0 then z = true else w = true
  letI : DecidablePred p := by
    intro x
    cases x with
    | inl x => change Decidable (x.2 ∈ f x.1); infer_instance
    | inr x => change Decidable (if x = 0 then z = true else w = true); infer_instance
  exact univ.filter p

@[simp] theorem mem_assemble_copy (r : ℕ) (z w : Bool) (f : Fin r → Finset V)
    (i : Fin r) (x : V) : Sum.inl (i, x) ∈ assemble r z w f ↔ x ∈ f i := by
  simp [assemble]

@[simp] theorem hub_mem_assemble (r : ℕ) (z w : Bool) (f : Fin r → Finset V) :
    hub r ∈ assemble r z w f ↔ z = true := by simp [assemble, hub]

@[simp] theorem pendant_mem_assemble (r : ℕ) (z w : Bool) (f : Fin r → Finset V) :
    pendant r ∈ assemble r z w f ↔ w = true := by simp [assemble, pendant]

@[simp] theorem copySlice_assemble (r : ℕ) (z w : Bool) (f : Fin r → Finset V)
    (i : Fin r) : copySlice r (assemble r z w f) i = f i := by
  ext x
  simp

theorem assemble_card (r : ℕ) (z w : Bool) (f : Fin r → Finset V) :
    (assemble r z w f).card =
      (∑ i, (f i).card) + (if z then 1 else 0) + (if w then 1 else 0) := by
  classical
  rw [assemble, card_eq_sum_ones, sum_filter, Fintype.sum_sum_type,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  have hs (i : Fin r) : (∑ x : V, if x ∈ f i then (1 : ℕ) else 0) = (f i).card := by
    rw [sum_boole]
    simp
  simp_rw [hs]
  cases z <;> cases w <;> norm_num [add_assoc]

theorem assemble_reconstruct (r : ℕ) (S : Finset (RepVertex r V)) :
    assemble r (decide (hub r ∈ S)) (decide (pendant r ∈ S)) (copySlice r S) = S := by
  classical
  ext x
  cases x with
  | inl x => exact (mem_assemble_copy _ _ _ _ _ _).trans (mem_copySlice _ _ _ _)
  | inr x =>
    fin_cases x
    · change hub r ∈ assemble r _ _ _ ↔ hub r ∈ S
      rw [hub_mem_assemble]
      exact decide_eq_true_iff
    · change pendant r ∈ assemble r _ _ _ ↔ pendant r ∈ S
      rw [pendant_mem_assemble]
      exact decide_eq_true_iff

/-- Domination configurations containing the hub are a leaf bit and one partial set per copy. -/
noncomputable def hubEquiv (H : SimpleGraph V) (U : Finset V) (r : ℕ) :
    ↥(domSetsAt (replicated H U r) (hub r)) ≃ Bool × (Fin r → ↥(partialSets H U)) := by
  classical
  exact {
    toFun := fun S => (decide (pendant r ∈ S.val), fun i => ⟨copySlice r S.val i,
      (mem_partialSets H U _).mpr ((dominating_with_hub_iff H U r S.val
        (mem_domSetsAt.mp S.property).2).mp (mem_domSetsAt.mp S.property).1 i)⟩)
    invFun := fun p => ⟨assemble r true p.1 (fun i => (p.2 i).val),
      mem_domSetsAt.mpr ⟨(dominating_with_hub_iff H U r _ (by simp)).mpr
        (fun i => by simpa using (mem_partialSets H U _).mp (p.2 i).property), by simp⟩⟩
    left_inv := by
      intro S
      apply Subtype.ext
      have hz := (mem_domSetsAt.mp S.property).2
      simpa only [decide_eq_true hz] using assemble_reconstruct r S.val
    right_inv := by
      intro p
      apply Prod.ext
      · rcases p with ⟨w, f⟩
        cases w <;> simp
      · funext i
        apply Subtype.ext
        simp }

/-- Domination configurations omitting the hub. -/
noncomputable def omittedSets (H : SimpleGraph V) (U : Finset V) (r : ℕ) :
    Finset (Finset (RepVertex r V)) := by
  classical
  exact (domSets (replicated H U r)).filter (fun S => hub r ∉ S)

@[simp] theorem mem_omittedSets (H : SimpleGraph V) (U : Finset V) (r : ℕ)
    (S : Finset (RepVertex r V)) :
    S ∈ omittedSets H U r ↔ (replicated H U r).IsDominating (S : Set _) ∧ hub r ∉ S := by
  classical
  simp [omittedSets]

/-- Omitting the hub corresponds to internally dominating each copy, with the pendant fixed. -/
noncomputable def omittedEquiv (H : SimpleGraph V) (U : Finset V) (r : ℕ) :
    ↥(omittedSets H U r) ≃ (Fin r → ↥(domSets H)) := by
  classical
  exact {
    toFun := by
      intro S i
      refine ⟨copySlice r S.val i, mem_domSets.mpr ?_⟩
      have hd := (mem_omittedSets H U r S.val).mp S.property
      exact ((dominating_without_hub_iff H U r S.val hd.2).mp hd.1).2 i
    invFun := fun f => ⟨assemble r false true (fun i => (f i).val),
      (mem_omittedSets H U r _).mpr ⟨(dominating_without_hub_iff H U r _
        (by simp)).mpr ⟨by simp, fun i => by simpa using mem_domSets.mp (f i).property⟩,
        by simp⟩⟩
    left_inv := by
      intro S
      apply Subtype.ext
      have hz := (mem_omittedSets H U r S.val).mp S.property |>.2
      have hw := ((dominating_without_hub_iff H U r S.val hz).mp
        ((mem_omittedSets H U r S.val).mp S.property).1).1
      simpa only [decide_eq_false hz, decide_eq_true hw] using assemble_reconstruct r S.val
    right_inv := by
      intro f
      funext i
      apply Subtype.ext
      simp }

theorem hubSets_card (H : SimpleGraph V) (U : Finset V) (r : ℕ) :
    (domSetsAt (replicated H U r) (hub r)).card = 2 * (partialSets H U).card ^ r := by
  classical
  simpa only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_coe] using Fintype.card_congr (hubEquiv H U r)

theorem omittedSets_card (H : SimpleGraph V) (U : Finset V) (r : ℕ) :
    (omittedSets H U r).card = (domSets H).card ^ r := by
  classical
  simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe] using
    Fintype.card_congr (omittedEquiv H U r)

/-- Independent uniform choices add their coordinate means. -/
private theorem sum_independent_choices {X : Type*} [Fintype X] [Nonempty X]
    (r : ℕ) (w : X → ℚ) :
    (∑ f : Fin r → X, ∑ i, w (f i)) =
      (Fintype.card X : ℚ) ^ r * r * ((∑ x, w x) / Fintype.card X) := by
  classical
  have hc : (Fintype.card X : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos))
  have coordinate (i : Fin r) :
      (∑ f : Fin r → X, w (f i)) =
        (Fintype.card X : ℚ) ^ r * ((∑ x, w x) / Fintype.card X) := by
    let e := Equiv.piSplitAt i (fun _ : Fin r => X)
    have hsum : (∑ f : Fin r → X, w (f i)) =
        (Fintype.card ((j : {j : Fin r // j ≠ i}) → X) : ℚ) * ∑ x, w x := by
      rw [Fintype.sum_equiv e (fun f => w (f i)) (fun p => w p.1) (fun _ => rfl),
        Fintype.sum_prod_type]
      simp [mul_comm, ← Finset.sum_mul]
    have hcard : Fintype.card X ^ r = Fintype.card X *
        Fintype.card ((j : {j : Fin r // j ≠ i}) → X) := by
      simpa using Fintype.card_congr e
    have hcardq : (Fintype.card X : ℚ) ^ r = (Fintype.card X : ℚ) *
        (Fintype.card ((j : {j : Fin r // j ≠ i}) → X) : ℚ) := by exact_mod_cast hcard
    rw [hsum, hcardq]
    field_simp
  rw [sum_comm]
  simp only [coordinate, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The size sum of hub-containing configurations. -/
theorem hubSets_sum (H : SimpleGraph V) (U : Finset V) (r : ℕ) :
    (∑ S ∈ domSetsAt (replicated H U r) (hub r), (S.card : ℚ)) =
      2 * (partialSets H U).card ^ r *
        (3 / 2 + (r : ℚ) * familyAverage (partialSets H U)) := by
  classical
  let F := partialSets H U
  have : Nonempty ↥F := ⟨⟨univ, (mem_partialSets H U _).mpr
    (fun x _ => Or.inl (mem_univ x))⟩⟩
  have hsum := sum_independent_choices r (fun S : ↥F => (S.val.card : ℚ))
  have hf : (∑ S : ↥F, (S.val.card : ℚ)) = ∑ S ∈ F, (S.card : ℚ) :=
    by simpa only [Finset.univ_eq_attach] using sum_attach F (fun S => (S.card : ℚ))
  have heq := Fintype.sum_equiv (hubEquiv H U r).symm
    (fun p => ((assemble r true p.1 (fun i => (p.2 i).val)).card : ℚ))
    (fun S => (S.val.card : ℚ)) (fun _ => rfl)
  have hfamily : (∑ S : ↥(domSetsAt (replicated H U r) (hub r)), (S.val.card : ℚ)) =
      ∑ S ∈ domSetsAt (replicated H U r) (hub r), (S.card : ℚ) := by
    simpa only [Finset.univ_eq_attach] using
      sum_attach (domSetsAt (replicated H U r) (hub r)) (fun S => (S.card : ℚ))
  have heq' := heq.trans hfamily
  rw [← heq', Fintype.sum_prod_type]
  simp_rw [assemble_card, Nat.cast_add, Nat.cast_sum]
  rw [Fintype.sum_bool]
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_one, Nat.cast_zero,
    sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, Nat.cast_pow] at *
  rw [hsum, hf]
  dsimp [familyAverage]
  ring

/-- The size sum of configurations omitting the hub. -/
theorem omittedSets_sum (H : SimpleGraph V) (U : Finset V) (r : ℕ) :
    (∑ S ∈ omittedSets H U r, (S.card : ℚ)) =
      (domSets H).card ^ r * (1 + (r : ℚ) * avd H) := by
  classical
  let F := domSets H
  have : Nonempty ↥F := ⟨⟨univ, mem_domSets.mpr (univ_dominating H)⟩⟩
  have hsum := sum_independent_choices r (fun S : ↥F => (S.val.card : ℚ))
  have hf : (∑ S : ↥F, (S.val.card : ℚ)) = ∑ S ∈ F, (S.card : ℚ) :=
    by simpa only [Finset.univ_eq_attach] using sum_attach F (fun S => (S.card : ℚ))
  have heq := Fintype.sum_equiv (omittedEquiv H U r).symm
    (fun f => ((assemble r false true (fun i => (f i).val)).card : ℚ))
    (fun S => (S.val.card : ℚ)) (fun _ => rfl)
  have hfamily : (∑ S : ↥(omittedSets H U r), (S.val.card : ℚ)) =
      ∑ S ∈ omittedSets H U r, (S.card : ℚ) := by
    simpa only [Finset.univ_eq_attach] using
      sum_attach (omittedSets H U r) (fun S => (S.card : ℚ))
  have heq' := heq.trans hfamily
  rw [← heq']
  simp_rw [assemble_card, Nat.cast_add, Nat.cast_sum]
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_one, Nat.cast_zero,
    sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, add_zero]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, Nat.cast_pow] at *
  rw [hsum, hf]
  dsimp [avd, familyAverage]
  ring

omit [DecidableEq V] in
theorem replicated_domSets_card (H : SimpleGraph V) (U : Finset V) (r : ℕ) :
    (domSets (replicated H U r)).card =
      2 * (partialSets H U).card ^ r + (domSets H).card ^ r := by
  classical
  rw [← hubSets_card H U r, ← omittedSets_card H U r]
  exact (card_filter_add_card_filter_not (s := domSets (replicated H U r))
    (fun S => hub r ∈ S)).symm

omit [DecidableEq V] in
theorem replicated_domSets_sum (H : SimpleGraph V) (U : Finset V) (r : ℕ) :
    (∑ S ∈ domSets (replicated H U r), (S.card : ℚ)) =
      2 * (partialSets H U).card ^ r * (3 / 2 + (r : ℚ) * familyAverage (partialSets H U)) +
      (domSets H).card ^ r * (1 + (r : ℚ) * avd H) := by
  classical
  rw [← hubSets_sum H U r, ← omittedSets_sum H U r]
  exact (sum_filter_add_sum_filter_not (domSets (replicated H U r))
    (fun S => hub r ∈ S) (fun S => (S.card : ℚ))).symm

omit [DecidableEq V] in
/-- The exact average of the hub graph, including zero copies. -/
theorem replicated_average (H : SimpleGraph V) (U : Finset V) (r : ℕ) :
    avd (replicated H U r) =
      (2 * (partialSets H U).card ^ r * (3 / 2 + (r : ℚ) * familyAverage (partialSets H U)) +
        (domSets H).card ^ r * (1 + (r : ℚ) * avd H)) /
      (2 * (partialSets H U).card ^ r + (domSets H).card ^ r) := by
  classical
  rw [avd, familyAverage, replicated_domSets_card, replicated_domSets_sum]
  push_cast
  rfl

omit [DecidableEq V] in
/-- A global average upper bound on the replicated graphs gives the replication inequalities. -/
theorem replication_inequality (H : SimpleGraph V) (U : Finset V)
    (hbound : ∀ r : ℕ, avd (replicated H U r) ≤
      2 * (Fintype.card (RepVertex r V) : ℚ) / 3) (r : ℕ) :
    (partialSets H U).card ^ r *
      (1 + 6 * (r : ℚ) * (familyAverage (partialSets H U) - 2 * Fintype.card V / 3)) ≤
    (domSets H).card ^ r * (1 + 3 * (r : ℚ) * (2 * Fintype.card V / 3 - avd H)) := by
  classical
  have hb : (0 : ℚ) < (domSets H).card := by exact_mod_cast domSets_card_pos H
  have hden : (0 : ℚ) < 2 * (partialSets H U).card ^ r + (domSets H).card ^ r := by
    positivity
  have hh := hbound r
  rw [replicated_average, div_le_iff₀ hden, replicated_card] at hh
  push_cast at hh
  nlinarith

omit [DecidableEq V] in
/-- Replication transfers the global bound to the partial dominating family, with rigidity. -/
theorem relaxed_average_le (H : SimpleGraph V) (U : Finset V)
    (hHbound : avd H ≤ 2 * (Fintype.card V : ℚ) / 3)
    (hbound : ∀ r : ℕ, avd (replicated H U r) ≤
      2 * (Fintype.card (RepVertex r V) : ℚ) / 3) :
    familyAverage (partialSets H U) ≤ 2 * (Fintype.card V : ℚ) / 3 ∧
      (familyAverage (partialSets H U) = 2 * (Fintype.card V : ℚ) / 3 →
        partialSets H U = domSets H) := by
  classical
  have hsub := domSets_subset_partialSets H U
  have hsame : (partialSets H U).card = (domSets H).card →
      familyAverage (partialSets H U) = avd H := by
    intro hc
    have heq := eq_of_subset_of_card_le hsub hc.le
    rw [← heq]
    rfl
  have hd := LocalDominatingStemBoundArithmetic.relaxed_mean_bound (partialSets H U).card (domSets H).card
    (Fintype.card V) (familyAverage (partialSets H U)) (avd H) (domSets_card_pos H)
    (card_le_card hsub) (avd_nonneg H) hHbound hsame (replication_inequality H U hbound)
  exact ⟨hd.1, fun hc => (eq_of_subset_of_card_le hsub (hd.2 hc).le).symm⟩

end D5.S3.Combinatorics.Graph.LocalDominatingStemBoundReplication
