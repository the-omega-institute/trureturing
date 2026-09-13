/- GID: D5/S3/Factorization/Automata/PrimeHistoryComposition
   generality: G
   mirror-B: D5/B/S3/Factorization/Automata/PrimeHistoryComposition
   mirror-E: none(waiver:all-intervals-all-contexts)
   anchors: []
   utility: none
   digest: The exact history normal form composes by translated interval
     intersection, supports partial reversal, and classifies contextual legality. -/

import D5.S3.Factorization.Automata.PrimeHistoryNormalForm
import D5.S3.Factorization.Automata.BoundedPrimeHorizon

set_option autoImplicit false

namespace D5.S3.Factorization.Automata.PrimeHistoryComposition

open PrimeHistoryNormalForm BoundedPrimeWalk
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

/-- Closed-form composition has precisely the real intermediate-state semantics. -/
theorem evaluate_compose {a : Nat} (s t : Option (IntervalMap a)) (x : Int) :
    evaluate (compose s t) x = (evaluate s x).bind (evaluate t) := by
  cases s with
  | none => rfl
  | some u =>
      cases t with
      | none =>
          by_cases h : u.lo ≤ x ∧ x ≤ u.hi <;>
            simp [compose, evaluate, h]
      | some v =>
          by_cases h : max u.lo (v.lo - u.shift) ≤ min u.hi (v.hi - u.shift)
          · have hc :
                (max u.lo (v.lo - u.shift) ≤ x ∧ x ≤ min u.hi (v.hi - u.shift)) ↔
                ((u.lo ≤ x ∧ x ≤ u.hi) ∧
                  (v.lo ≤ x + u.shift ∧ x + u.shift ≤ v.hi)) := by omega
            by_cases hu : u.lo ≤ x ∧ x ≤ u.hi <;>
              by_cases hv : v.lo ≤ x + u.shift ∧ x + u.shift ≤ v.hi <;>
              simp [compose, h, evaluate, hc, hu, hv, add_assoc]
          · have hc : ¬ ((u.lo ≤ x ∧ x ≤ u.hi) ∧
                (v.lo ≤ x + u.shift ∧ x + u.shift ≤ v.hi)) := by omega
            by_cases hu : u.lo ≤ x ∧ x ≤ u.hi
            · have hv : ¬ (v.lo ≤ x + u.shift ∧ x + u.shift ≤ v.hi) := by tauto
              simp [compose, h, evaluate, hu, hv]
            · simp [compose, h, evaluate, hu]

/-- Normalizing concatenated histories agrees with the closed-form composition.
The visited extrema are translated, not simply added or separately forgotten. -/
theorem normal_append (a : Nat) (v w : List Bool) :
    normal a (v ++ w) = compose (normal a v) (normal a w) := by
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

/-- Reversing an interval translation exchanges its source and image intervals.
This is a partial inverse, not a total group inverse at boundary states. -/
def inverse {a : Nat} (s : Option (IntervalMap a)) : Option (IntervalMap a) :=
  s.map fun t => {
    lo := t.lo + t.shift
    hi := t.hi + t.shift
    shift := -t.shift
    lo_nonneg := t.image_lo
    ordered := by have := t.ordered; omega
    hi_le := t.image_hi
    image_lo := by have := t.lo_nonneg; omega
    image_hi := by have := t.hi_le; omega }

/-- The inverse reverses exactly the graph, including singleton intervals. -/
theorem inverse_graph {a : Nat} (s : Option (IntervalMap a)) (x y : Int) :
    evaluate (inverse s) y = some x ↔ evaluate s x = some y := by
  cases s with
  | none => simp [inverse, evaluate]
  | some t =>
      simp only [inverse, Option.map_some, evaluate, Option.bind_some]
      by_cases hy : t.lo + t.shift ≤ y ∧ y ≤ t.hi + t.shift <;>
        by_cases hx : t.lo ≤ x ∧ x ≤ t.hi <;>
        simp [hy, hx] <;> omega

/-- Endpoint semantics alone already has a contextual meaning: replacing a word
with an equal partial map preserves execution inside every prefix/suffix context. -/
theorem normal_eq_iff_contextual_run (a : Nat) (v w : List Bool) :
    normal a v = normal a w ↔
      ∀ (before after : List Bool) (e : Fin (a + 1)),
        run a e (before ++ v ++ after) = run a e (before ++ w ++ after) := by
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
      have hv := normal_correct a v e
      have hw := normal_correct a w e
      rw [he] at hv hw
      exact hv.symm.trans ((congrArg (Option.map (fun f : Fin (a + 1) => (f.val : Int))) hr).trans hw)
    · rcases excursion_bounds v with ⟨vl, vh, _, _⟩
      rcases excursion_bounds w with ⟨wl, wh, _, _⟩
      have hv : ¬ (0 ≤ x + low v ∧ x + high v ≤ (a : Int)) := by omega
      have hw : ¬ (0 ≤ x + low w ∧ x + high w ≤ (a : Int)) := by omega
      simp [evaluate_normal, hv, hw]

/-- Even if the only output is success/failure, every contextual distinction of
the exact partial map is observable. A suffix separates different live endpoints;
the old exact horizon theorem supplies that suffix semantically. -/
theorem normal_eq_iff_contextual_accepts (a : Nat) (v w : List Bool) :
    normal a v = normal a w ↔
      ∀ (before after : List Bool) (e : Fin (a + 1)),
        accepts a e (before ++ v ++ after) = accepts a e (before ++ w ++ after) := by
  constructor
  · intro h before after e
    exact congrArg Option.isSome
      ((normal_eq_iff_contextual_run a v w).mp h before after e)
  · intro h
    apply (normal_eq_iff_contextual_run a v w).mpr
    intro before after e
    have htail (tail : List Bool) :
        accepts a e ((before ++ v ++ after) ++ tail) =
          accepts a e ((before ++ w ++ after) ++ tail) := by
      simpa only [List.append_assoc] using h before (after ++ tail) e
    cases hv : run a e (before ++ v ++ after) with
    | none =>
        cases hw : run a e (before ++ w ++ after) with
        | none => rfl
        | some f =>
            have hh := htail []
            simp [accepts, List.append_nil, hv, hw] at hh
    | some f =>
        cases hw : run a e (before ++ w ++ after) with
        | none =>
            have hh := htail []
            simp [accepts, List.append_nil, hv, hw] at hh
        | some g =>
            have heq : f = g :=
              (BoundedPrimeHorizon.full_separation_threshold a a).mpr (by omega) f g (by
                intro tail _
                have hh := htail tail
                have append_run (u z : List Bool) :
                    run a e (u ++ z) = (run a e u).bind (fun f => run a f z) :=
                  PartialDFA.evalFrom_append {start := e, step := step a} e u z
                unfold accepts at hh
                rw [append_run, append_run, hv, hw] at hh
                exact hh)
            simpa [heq]

#print axioms evaluate_compose
#print axioms normal_append
#print axioms inverse_graph
#print axioms normal_eq_iff_contextual_accepts

end D5.S3.Factorization.Automata.PrimeHistoryComposition
