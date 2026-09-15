/- GID: D5/S1/Words/GraphRepresentation/ExplicitNonTwoUniform
   generality: G
   mirror-B: D5/B/S1/Words/GraphRepresentation/ExplicitNonTwoUniform
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prefix cuts reconstruct projections and exclude the membership graph U24. -/

import D5.S0.Diagonal.PigeonholeFiber
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum

/-!
The graph representation uses equality of actual two-letter List projections,
with two occurrences of every vertex in each word. The new structural step
reconstructs projections for arbitrary words from their ordered left restriction
and prefix cuts. Equal cuts and unequal left orders between words are allowed.

Utility is `none`: this is an unbounded structural word argument, with no graph
enumeration, certificate checker, numerical reduction obligation or computation
of a positive finite instance. The final small cardinal inequality is ordinary
arithmetic inside the structural obstruction. The source question and qualified
literature boundary are recorded in the corresponding Library and Problems notes.
-/

namespace D5.S1.Words.GraphRepresentation.ExplicitNonTwoUniform

/-- Delete all letters other than the two specified vertices. -/
def twoProjection {V : Type*} [DecidableEq V] (a b : V) (w : List V) : List V :=
  w.filter fun z => z == a || z == b

/-- The source's class G₂, with two occurrences of every vertex in both words. -/
def InG2 {V : Type*} [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∃ w v : List V, (∀ z, w.count z = 2) ∧ (∀ z, v.count z = 2) ∧
    ∀ x y, x ≠ y → (G.Adj x y ↔ twoProjection x y w = twoProjection x y v)

/-- At every occurrence of `b`, record the number of preceding left letters. -/
def leftCuts {A B : Type*} [DecidableEq B] (b : B) : List (A ⊕ B) → List ℕ
  | [] => []
  | Sum.inl _ :: w => (leftCuts b w).map Nat.succ
  | Sum.inr c :: w => if c = b then 0 :: leftCuts b w else leftCuts b w

/-- Insert unit markers at the absolute cuts of an ordered left word.
The empty-list branch with a positive cut is irrelevant for cuts of real words. -/
def reconstruct {A : Type*} : List A → List ℕ → List (A ⊕ Unit)
  | r, [] => r.map Sum.inl
  | r, 0 :: cs => Sum.inr () :: reconstruct r cs
  | [], (_ + 1) :: _ => []
  | a :: r, (n + 1) :: cs => Sum.inl a :: reconstruct r (n :: cs.map Nat.pred)
termination_by r cs => r.length + cs.length
decreasing_by all_goals simp_wf

/-- Reconstruct the actual two-letter projection, including tied cuts, for every word. -/
theorem projection_eq_reconstruction {A B : Type*} [DecidableEq A] [DecidableEq B]
    (a : A) (b : B) (w : List (A ⊕ B)) :
    twoProjection (Sum.inl a) (Sum.inr b) w =
      (twoProjection (Sum.inl a) (Sum.inr ())
        (reconstruct (w.filterMap Sum.getLeft?) (leftCuts b w))).map
          (Sum.map id (fun _ => b)) := by
  induction w with
  | nil => simp [twoProjection, leftCuts, reconstruct]
  | cons z w ih =>
    cases z with
    | inl c =>
      have shift (r : List A) (cs : List ℕ) :
          reconstruct (c :: r) (cs.map Nat.succ) =
            Sum.inl c :: reconstruct r cs := by
        cases cs <;> simp [reconstruct, List.map_map, Function.comp_def]
      simp only [leftCuts, List.filterMap_cons, Sum.getLeft?_inl, shift]
      by_cases h : c = a
      · subst c; simpa [twoProjection] using congrArg (Sum.inl a :: ·) ih
      · simpa [twoProjection, h] using ih
    | inr c =>
      by_cases h : c = b
      · subst c
        simpa [twoProjection, leftCuts, reconstruct, List.filterMap_cons,
          Sum.getLeft?_inr] using congrArg (Sum.inr b :: ·) ih
      · simpa [twoProjection, leftCuts, h, List.filterMap_cons, Sum.getLeft?_inr] using ih

/-- The explicit graph on tagged points and all their subsets. -/
def U24 : SimpleGraph (Fin 24 ⊕ Finset (Fin 24)) where
  Adj x y := match x, y with
    | Sum.inl a, Sum.inr s => a ∈ s
    | Sum.inr s, Sum.inl a => a ∈ s
    | _, _ => False
  symm := ⟨by intro x y h; cases x <;> cases y <;> exact h⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

/-- No pair of two-uniform words represents the explicit membership graph. -/
theorem u24_not_in_g2 : ¬ InG2 U24 := by
  classical
  let : BEq (Fin 24 ⊕ Finset (Fin 24)) := instBEqOfDecidableEq
  rintro ⟨w, v, hw, hv, hadj⟩
  have cut_data (u : List (Fin 24 ⊕ Finset (Fin 24)))
      (hu : ∀ z, u.count z = 2) (s : Finset (Fin 24)) :
      ∃ p : Fin 49 × Fin 49, leftCuts s u = [p.1.val, p.2.val] := by
    let r := u.filterMap Sum.getLeft?
    have rcount (a : Fin 24) : r.count a = 2 := by
      calc
        r.count a = u.count (Sum.inl a) := by
          change (u.filterMap Sum.getLeft?).count a = _
          rw [List.count_filterMap, List.count_eq_countP]
          congr 1
          funext z
          cases z <;> simp
        _ = 2 := hu _
    have rall : r.toFinset = Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro a
      apply List.mem_toFinset.mpr
      apply List.count_pos_iff.mp
      rw [rcount]
      decide
    have rlength : r.length = 48 := by
      rw [← List.sum_toFinset_count_eq_length, rall]
      simp [rcount]
    have count_cuts (l : List (Fin 24 ⊕ Finset (Fin 24))) :
        (leftCuts s l).length = l.count (Sum.inr s) := by
      induction l with
      | nil => simp [leftCuts]
      | cons z l ih =>
        cases z with
        | inl a => simpa [leftCuts, List.count_cons] using ih
        | inr t => by_cases h : t = s <;> simp [leftCuts, h, ih]
    have bound_cuts (l : List (Fin 24 ⊕ Finset (Fin 24))) :
        ∀ k ∈ leftCuts s l, k ≤ (l.filterMap Sum.getLeft?).length := by
      induction l with
      | nil => simp [leftCuts]
      | cons z l ih =>
        cases z with
        | inl a =>
          intro k hk
          obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hk
          simpa [List.filterMap_cons, Sum.getLeft?_inl] using Nat.succ_le_succ (ih j hj)
        | inr t =>
          by_cases h : t = s
          · subst t
            intro k hk
            simp only [leftCuts, if_pos, List.mem_cons] at hk
            rcases hk with rfl | hk
            · exact Nat.zero_le _
            · simpa [List.filterMap_cons, Sum.getLeft?_inr] using ih k hk
          · simpa [leftCuts, h, List.filterMap_cons, Sum.getLeft?_inr] using ih
    obtain ⟨i, j, hij⟩ := List.length_eq_two.mp ((count_cuts u).trans (hu _))
    have hi : i < 49 := by
      have := bound_cuts u i (by simp [hij])
      change i ≤ r.length at this
      omega
    have hj : j < 49 := by
      have := bound_cuts u j (by simp [hij])
      change j ≤ r.length at this
      omega
    exact ⟨(⟨i, hi⟩, ⟨j, hj⟩), hij⟩
  let cw (s : Finset (Fin 24)) : Fin 49 × Fin 49 := (cut_data w hw s).choose
  let cv (s : Finset (Fin 24)) : Fin 49 × Fin 49 := (cut_data v hv s).choose
  let signature (s : Finset (Fin 24)) := (cw s, cv s)
  obtain ⟨s, t, hne, hsig⟩ :=
    D5.S0.Diagonal.PigeonholeFiber.finite_reading_has_fiber signature (by
      simp only [Cardinal.mk_fintype, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_finset]
      norm_num)
  have hwcuts : leftCuts s w = leftCuts t w := by
    rw [(cut_data w hw s).choose_spec, (cut_data w hw t).choose_spec]
    change [((cw s).1 : ℕ), ((cw s).2 : ℕ)] = [((cw t).1 : ℕ), ((cw t).2 : ℕ)]
    rw [show cw s = cw t from congrArg Prod.fst hsig]
  have hvcuts : leftCuts s v = leftCuts t v := by
    rw [(cut_data v hv s).choose_spec, (cut_data v hv t).choose_spec]
    change [((cv s).1 : ℕ), ((cv s).2 : ℕ)] = [((cv t).1 : ℕ), ((cv t).2 : ℕ)]
    rw [show cv s = cv t from congrArg Prod.snd hsig]
  apply hne
  apply Finset.ext
  intro a
  have hs := hadj (Sum.inl a) (Sum.inr s) (by simp)
  have ht := hadj (Sum.inl a) (Sum.inr t) (by simp)
  change (a ∈ s ↔ _) at hs
  change (a ∈ t ↔ _) at ht
  rw [projection_eq_reconstruction a s w, projection_eq_reconstruction a s v] at hs
  rw [projection_eq_reconstruction a t w, projection_eq_reconstruction a t v] at ht
  have hinj (b : Finset (Fin 24)) :
      Function.Injective (Sum.map (id : Fin 24 → Fin 24) (fun _ : Unit => b)) :=
    Sum.map_injective.mpr ⟨Function.injective_id, fun _ _ _ => Subsingleton.elim _ _⟩
  rw [List.map_inj_right (hinj s)] at hs
  rw [List.map_inj_right (hinj t)] at ht
  rw [hwcuts, hvcuts] at hs
  exact hs.trans ht.symm

end D5.S1.Words.GraphRepresentation.ExplicitNonTwoUniform
