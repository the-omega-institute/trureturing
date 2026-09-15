/- GID: D5/S3/Factorization/Automata/PrimeHistoryComposition
   generality: G
   mirror-B: D5/B/S3/Factorization/Automata/PrimeHistoryComposition
   mirror-E: none(waiver:all-intervals-all-contexts)
   anchors: []
   utility: none
   digest: The exact history normal form composes by translated interval intersection and classifies contextual legality. -/

import D5.S0.Automata.TypedPartialDFAOOverBase
import D5.S3.Factorization.Automata.BoundedPrimeHorizon
import D5.S3.Factorization.Automata.PrimeHistoryNormalForm
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Factorization.Automata.PrimeHistoryComposition

open BoundedPrimeHorizon PrimeHistoryNormalForm WordExcursionLowerBound
open D5.S0.Automata.TypedPartialDFAOOverBase

/-- Chronological composition: execute s first and t second. The actual domain
is the first domain intersected with the translated second domain. -/
def compose {a : Nat} (s t : Option (IntervalMap a)) : Option (IntervalMap a) :=
  s.bind fun u => t.bind fun v =>
    if h : max u.lo (v.lo - u.shift) ≤ min u.hi (v.hi - u.shift) then
      some {
        lo := max u.lo (v.lo - u.shift)
        hi := min u.hi (v.hi - u.shift)
        shift := u.shift + v.shift
        lo_nonneg := by have := u.lo_nonneg; omega
        ordered := h
        hi_le := by have := u.hi_le; omega
        image_lo := by have := v.image_lo; omega
        image_hi := by have := v.image_hi; omega }
    else none

/-- Normalizing concatenated histories agrees with the closed-form composition.
The visited extrema are translated, not simply added or separately forgotten. -/
theorem normal_append (a : Nat) (v w : List Bool) :
    normal a (v ++ w) = compose (normal a v) (normal a w) := by
  have evaluate_compose {s t : Option (IntervalMap a)} (x : Int) :
      evaluate (compose s t) x = (evaluate s x).bind (evaluate t) := by
    cases s with
    | none => rfl
    | some u =>
        cases t with
        | none =>
            by_cases h : u.lo ≤ x ∧ x ≤ u.hi <;>
              simp [compose, evaluate, h]
        | some z =>
            by_cases h : max u.lo (z.lo - u.shift) ≤ min u.hi (z.hi - u.shift)
            · have hc :
                  (max u.lo (z.lo - u.shift) ≤ x ∧ x ≤ min u.hi (z.hi - u.shift)) ↔
                  ((u.lo ≤ x ∧ x ≤ u.hi) ∧
                    (z.lo ≤ x + u.shift ∧ x + u.shift ≤ z.hi)) := by omega
              by_cases hu : u.lo ≤ x ∧ x ≤ u.hi
              · by_cases hz : z.lo ≤ x + u.shift ∧ x + u.shift ≤ z.hi
                · have hx := hc.mpr ⟨hu, hz⟩
                  simp only [compose, Option.bind_some, dif_pos h, evaluate,
                    if_pos hx, if_pos hu, if_pos hz, add_assoc]
                · have hx : ¬ (max u.lo (z.lo - u.shift) ≤ x ∧
                      x ≤ min u.hi (z.hi - u.shift)) := by
                    intro hx
                    exact hz (hc.mp hx).2
                  simp only [compose, Option.bind_some, dif_pos h, evaluate,
                    if_neg hx, if_pos hu, if_neg hz]
              · have hx : ¬ (max u.lo (z.lo - u.shift) ≤ x ∧
                    x ≤ min u.hi (z.hi - u.shift)) := by
                  intro hx
                  exact hu (hc.mp hx).1
                simp only [compose, Option.bind_some, dif_pos h, evaluate,
                  if_neg hx, if_neg hu]
                rfl
            · have hc : ¬ ((u.lo ≤ x ∧ x ≤ u.hi) ∧
                  (z.lo ≤ x + u.shift ∧ x + u.shift ≤ z.hi)) := by omega
              by_cases hu : u.lo ≤ x ∧ x ≤ u.hi
              · have hz : ¬ (z.lo ≤ x + u.shift ∧ x + u.shift ≤ z.hi) := by tauto
                simp only [compose, Option.bind_some, dif_neg h, evaluate,
                  if_pos hu, if_neg hz]
                rfl
              · simp only [compose, Option.bind_some, dif_neg h, evaluate,
                  if_neg hu]
                rfl
  have evaluate_normal (u : List Bool) (x : Int) :
      evaluate (normal a u) x =
        if 0 ≤ x + low u ∧ x + high u ≤ (a : Int)
        then some (x + displacement u) else none := by
    unfold normal
    split
    · have hc : (-low u ≤ x ∧ x ≤ (a : Int) - high u) ↔
          (0 ≤ x + low u ∧ x + high u ≤ (a : Int)) := by omega
      simp [evaluate, hc]
    · rename_i h
      have hc : ¬ (0 ≤ x + low u ∧ x + high u ≤ (a : Int)) := by omega
      simp [evaluate, hc]
  have excursion_bounds : ∀ u : List Bool,
      low u ≤ 0 ∧ 0 ≤ high u ∧ low u ≤ displacement u ∧ displacement u ≤ high u := by
    intro u
    induction u with
    | nil => simp [low, high, displacement]
    | cons b u ih => simp only [low, high, displacement]; omega
  have append_signature (u z : List Bool) :
      displacement (u ++ z) = displacement u + displacement z ∧
      low (u ++ z) = min (low u) (displacement u + low z) ∧
      high (u ++ z) = max (high u) (displacement u + high z) := by
    induction u with
    | nil =>
        have hb := excursion_bounds z
        simp only [List.nil_append, displacement, low, high]
        constructor
        · omega
        constructor <;> omega
    | cons b u ih =>
        simp only [List.cons_append, displacement, low, high]
        rcases ih with ⟨hd, hl, hh⟩
        rw [hd, hl, hh]
        constructor
        · omega
        constructor <;> omega
  apply evaluate_injective a
  funext x
  rw [evaluate_compose, evaluate_normal, evaluate_normal]
  rcases append_signature v w with ⟨hd, hl, hh⟩
  rw [hd, hl, hh]
  have hc :
      (0 ≤ x + min (low v) (displacement v + low w) ∧
        x + max (high v) (displacement v + high w) ≤ (a : Int)) ↔
      ((0 ≤ x + low v ∧ x + high v ≤ (a : Int)) ∧
        (0 ≤ x + displacement v + low w ∧
          x + displacement v + high w ≤ (a : Int))) := by omega
  by_cases hv : 0 ≤ x + low v ∧ x + high v ≤ (a : Int)
  · simp only [if_pos hv, Option.bind_some]
    rw [evaluate_normal]
    simp [hc, hv, add_assoc]
  · simp [hc, hv]

/-- Endpoint semantics alone already has a contextual meaning: replacing a word
with an equal partial map preserves execution inside every prefix/suffix context. -/
theorem normal_eq_iff_contextual_run (a : Nat) (v w : List Bool) :
    normal a v = normal a w ↔
      ∀ (before after : List Bool) (e : Fin (a + 1)),
        run a e (before ++ v ++ after) = run a e (before ++ w ++ after) := by
  have excursion_bounds : ∀ u : List Bool,
      low u ≤ 0 ∧ 0 ≤ high u ∧ low u ≤ displacement u ∧ displacement u ≤ high u := by
    intro u
    induction u with
    | nil => simp [low, high, displacement]
    | cons b u ih => simp only [low, high, displacement]; omega
  have run_spec (u : List Bool) (e f : Fin (a + 1)) :
      run a e u = some f ↔
        0 ≤ (e.val : Int) + low u ∧ (e.val : Int) + high u ≤ (a : Int) ∧
          (f.val : Int) = (e.val : Int) + displacement u := by
    induction u generalizing e f with
    | nil =>
        have he := e.isLt
        simp only [run, runTransition, Option.some.injEq, low, high, displacement, add_zero]
        constructor
        · intro h
          subst f
          omega
        · rintro ⟨_, _, h⟩
          apply Fin.ext
          omega
    | cons b u ih =>
        have he := e.isLt
        rcases excursion_bounds u with ⟨hlo, hhi, hld, hdh⟩
        cases b with
        | false =>
            by_cases hpos : 0 < e.val
            · let next : Fin (a + 1) := ⟨e.val - 1, by omega⟩
              have hr : run a e (false :: u) = run a next u := by
                simp [run, runTransition, step, hpos, next]
              rw [hr, ih]
              simp only [low, high, displacement, reduceCtorEq, if_false]
              dsimp [next]
              omega
            · have hr : run a e (false :: u) = none := by
                simp [run, runTransition, step, hpos]
              rw [hr]
              simp only [reduceCtorEq, low, high, displacement, if_false]
              constructor
              · intro impossible
                contradiction
              · rintro ⟨hlower, _, _⟩
                have hmin : min 0 (-1 + low u) ≤ -1 + low u := min_le_right _ _
                omega
        | true =>
            by_cases hroom : e.val < a
            · let next : Fin (a + 1) := ⟨e.val + 1, by omega⟩
              have hr : run a e (true :: u) = run a next u := by
                simp [run, runTransition, step, hroom, next]
              rw [hr, ih]
              simp only [low, high, displacement, if_true]
              dsimp [next]
              omega
            · have hr : run a e (true :: u) = none := by
                simp [run, runTransition, step, hroom]
              rw [hr]
              simp only [reduceCtorEq, low, high, displacement, if_true]
              constructor
              · intro impossible
                contradiction
              · rintro ⟨_, hupper, _⟩
                have hmax : 1 + high u ≤ max 0 (1 + high u) := le_max_right _ _
                omega
  have evaluate_normal (u : List Bool) (x : Int) :
      evaluate (normal a u) x =
        if 0 ≤ x + low u ∧ x + high u ≤ (a : Int)
        then some (x + displacement u) else none := by
    unfold normal
    split
    · have hc : (-low u ≤ x ∧ x ≤ (a : Int) - high u) ↔
          (0 ≤ x + low u ∧ x + high u ≤ (a : Int)) := by omega
      simp [evaluate, hc]
    · rename_i h
      have hc : ¬ (0 ≤ x + low u ∧ x + high u ≤ (a : Int)) := by omega
      simp [evaluate, hc]
  have normal_correct (u : List Bool) (e : Fin (a + 1)) :
      (run a e u).map (fun f => (f.val : Int)) = evaluate (normal a u) (e.val : Int) := by
    rw [evaluate_normal]
    by_cases h : 0 ≤ (e.val : Int) + low u ∧ (e.val : Int) + high u ≤ (a : Int)
    · rw [if_pos h]
      have hb := excursion_bounds u
      let z : Int := (e.val : Int) + displacement u
      have hz0 : 0 ≤ z := by dsimp [z]; omega
      have hza : z ≤ (a : Int) := by dsimp [z]; omega
      let f : Fin (a + 1) := ⟨z.toNat, by omega⟩
      have hf : (f.val : Int) = z := by dsimp [f]; omega
      have hr : run a e u = some f := (run_spec u e f).mpr ⟨h.1, h.2, hf⟩
      rw [hr]
      exact congrArg some hf
    · rw [if_neg h]
      cases hr : run a e u with
      | none => rfl
      | some f =>
          have hs := (run_spec u e f).mp hr
          exact False.elim (h ⟨hs.1, hs.2.1⟩)
  have run_eq_of_normal {v w : List Bool} (heq : normal a v = normal a w)
      (e : Fin (a + 1)) : run a e v = run a e w := by
    have hm : (run a e v).map (fun f => (f.val : Int)) =
        (run a e w).map (fun f => (f.val : Int)) := by
      rw [normal_correct, normal_correct, heq]
    cases hv : run a e v <;> cases hw : run a e w <;> simp [hv, hw] at hm ⊢
    apply Fin.ext
    omega
  constructor
  · intro h before after e
    apply run_eq_of_normal
    simp only [normal_append]
    rw [h]
  · intro h
    apply evaluate_injective a
    funext x
    by_cases hx : 0 ≤ x ∧ x ≤ (a : Int)
    · let e : Fin (a + 1) := ⟨x.toNat, by omega⟩
      have he : (e.val : Int) = x := by dsimp [e]; omega
      have hr := h [] [] e
      simp only [List.nil_append, List.append_nil] at hr
      have hv := normal_correct v e
      have hw := normal_correct w e
      rw [he] at hv hw
      exact hv.symm.trans ((congrArg (Option.map (fun f : Fin (a + 1) => (f.val : Int))) hr).trans hw)
    · rcases excursion_bounds v with ⟨vl, vh, _, _⟩
      rcases excursion_bounds w with ⟨wl, wh, _, _⟩
      have hv : ¬ (0 ≤ x + low v ∧ x + high v ≤ (a : Int)) := by omega
      have hw : ¬ (0 ≤ x + low w ∧ x + high w ≤ (a : Int)) := by omega
      simp [evaluate_normal, hv, hw]

#print axioms normal_append
#print axioms normal_eq_iff_contextual_run

end D5.S3.Factorization.Automata.PrimeHistoryComposition
