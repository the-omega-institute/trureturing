/- GID: D5/S1/Words/TraceProjection
   generality: G
   mirror-B: D5/B/S1/Words/TraceProjection
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Dependent-pair projections classify finite words modulo independent adjacent swaps. -/

import Mathlib.Data.List.Basic
import Mathlib.Logic.Relation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.TraceProjection

universe u
variable {α : Type u}

/-- One adjacent interchange in an arbitrary unchanged left and right context. -/
inductive Swap (I : α → α → Prop) : List α → List α → Prop
  | exchange (p q : List α) (a b : α) (h : I a b) :
      Swap I (p ++ a :: b :: q) (p ++ b :: a :: q)

/-- A finite sequence of legal adjacent interchanges, including the empty sequence. -/
def Connected (I : α → α → Prop) : List α → List α → Prop :=
  Relation.ReflTransGen (Swap I)

/-- Delete every letter other than the two specified letters, preserving order. -/
noncomputable def pairProjection (a b : α) (s : List α) : List α := by
  classical
  exact s.filter (fun x => decide (x = a ∨ x = b))

/-- Equality of every ordered readout belonging to a dependent pair, including diagonals. -/
def SameProjections (I : α → α → Prop) (s t : List α) : Prop :=
  ∀ a b, ¬ I a b → pairProjection a b s = pairProjection a b t

private theorem projection_cons_cancel (a x y : α) (s t : List α)
    (h : pairProjection x y (a :: s) = pairProjection x y (a :: t)) :
    pairProjection x y s = pairProjection x y t := by
  classical
  by_cases ha : a = x ∨ a = y <;>
    simpa [pairProjection, List.filter_cons, ha] using h

private theorem swap_preserves (I : α → α → Prop)
    (hs : ∀ a b, I a b → I b a) (hi : ∀ a, ¬ I a a)
    {s t : List α} (h : Swap I s t) : SameProjections I s t := by
  classical
  cases h with
  | exchange p q a b hab =>
      intro x y hxy
      have hn : ¬ ((a = x ∨ a = y) ∧ (b = x ∨ b = y)) := by
        rintro ⟨hax | hay, hbx | hby⟩
        · subst a; subst b; exact hi x hab
        · subst a; subst b; exact hxy hab
        · subst a; subst b; exact hxy (hs y x hab)
        · subst a; subst b; exact hi y hab
      by_cases ha : a = x ∨ a = y <;> by_cases hb : b = x ∨ b = y
      · exact False.elim (hn ⟨ha, hb⟩)
      all_goals simp [pairProjection, ha, hb]

private theorem connected_preserves (I : α → α → Prop)
    (hs : ∀ a b, I a b → I b a) (hi : ∀ a, ¬ I a a)
    {s t : List α} (h : Connected I s t) : SameProjections I s t := by
  intro a b hab
  have hc : Relation.ReflTransGen Eq (pairProjection a b s) (pairProjection a b t) :=
    Relation.ReflTransGen.lift (pairProjection a b)
      (fun _ _ hstep => swap_preserves I hs hi hstep a b hab) s t h
  simpa only [Relation.reflTransGen_eq_self] using hc

private theorem connected_cons (I : α → α → Prop) (a : α)
    {s t : List α} (h : Connected I s t) : Connected I (a :: s) (a :: t) := by
  apply Relation.ReflTransGen.lift (List.cons a) (fun s t hst => ?_) s t h
  cases hst with
  | exchange p q x y hxy =>
      exact Swap.exchange (a :: p) q x y hxy

private theorem move_head_right (I : α → α → Prop) (a : α) (p q : List α)
    (hp : ∀ b ∈ p, I a b) : Connected I (a :: (p ++ q)) (p ++ a :: q) := by
  induction p with
  | nil => exact .refl
  | cons b p ih =>
      have hstep : Swap I (a :: b :: (p ++ q)) (b :: a :: (p ++ q)) :=
        Swap.exchange [] (p ++ q) a b (hp b (by simp))
      exact Relation.ReflTransGen.head hstep
        (connected_cons I b (ih (fun c hc => hp c (by simp [hc]))))

private theorem projection_prefix_nil (a b : α) (p q r : List α)
    (ha : a ∉ p)
    (h : pairProjection a b (a :: r) = pairProjection a b (p ++ a :: q)) :
    pairProjection a b p = [] := by
  classical
  cases he : pairProjection a b p with
  | nil => rfl
  | cons c cs =>
      have hcons : pairProjection a b (a :: r) = a :: pairProjection a b r := by
        simp [pairProjection]
      have happ : pairProjection a b (p ++ a :: q) =
          pairProjection a b p ++ a :: pairProjection a b q := by
        simp [pairProjection]
      rw [hcons, happ, he] at h
      have hca : c = a := (List.cons.inj h).1.symm
      have hcp : c ∈ p := by
        have hm : c ∈ pairProjection a b p := by rw [he]; simp
        exact (List.mem_filter.mp hm).1
      exact False.elim (ha (hca ▸ hcp))

/-- Equal dependent-pair readouts expose the source head after a commuting prefix,
and deleting that occurrence leaves exactly the same dependent-pair readouts. -/
theorem head_exposure (I : α → α → Prop)
    (hs : ∀ a b, I a b → I b a) (hi : ∀ a, ¬ I a a)
    (a : α) (r t : List α) (h : SameProjections I (a :: r) t) :
    ∃ p q, t = p ++ a :: q ∧ (∀ b ∈ p, I a b) ∧
      SameProjections I r (p ++ q) := by
  classical
  have hat : a ∈ t := by
    have hm : a ∈ pairProjection a a (a :: r) := by simp [pairProjection]
    rw [h a a (hi a)] at hm
    exact (List.mem_filter.mp hm).1
  obtain ⟨p, q, ht, hap⟩ := List.eq_append_cons_of_mem hat
  subst t
  have hp : ∀ b ∈ p, I a b := by
    intro b hbp
    by_contra hab
    have hempty := projection_prefix_nil a b p q r hap (h a b hab)
    have hm : b ∈ pairProjection a b p := by simp [pairProjection, hbp]
    rw [hempty] at hm
    exact List.not_mem_nil hm
  refine ⟨p, q, rfl, hp, ?_⟩
  intro x y hxy
  apply projection_cons_cancel a x y
  exact (h x y hxy).trans
    (connected_preserves I hs hi (move_head_right I a p q hp) x y hxy).symm

/-- For every alphabet, dependent-pair ordered projections classify native finite
lists up to legal independent adjacent swaps. No finiteness or equality oracle is assumed. -/
theorem connected_iff_same_projections (I : α → α → Prop)
    (hs : ∀ a b, I a b → I b a) (hi : ∀ a, ¬ I a a)
    (s t : List α) : Connected I s t ↔ SameProjections I s t := by
  constructor
  · exact connected_preserves I hs hi
  · intro h
    induction s generalizing t with
    | nil =>
        cases t with
        | nil => exact .refl
        | cons b t =>
            have hh := h b b (hi b)
            simp [pairProjection] at hh
    | cons a r ih =>
        obtain ⟨p, q, ht, hp, hr⟩ := head_exposure I hs hi a r t h
        subst t
        exact Relation.ReflTransGen.trans (connected_cons I a (ih (p ++ q) hr))
          (move_head_right I a p q hp)

end D5.S1.Words.TraceProjection
