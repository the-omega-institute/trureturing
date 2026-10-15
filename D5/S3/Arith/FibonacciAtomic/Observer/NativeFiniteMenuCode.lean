/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteMenuCode
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Original branch-first finite-menu ranks with strict-left constructor overlap. -/

import D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuCode

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address)

abbrev Menu := List Address

/-- Child menus retain the public order. -/
def child (b : Bool) (S : Menu) : Menu :=
  S.filterMap fun q => match q with
    | [] => none
    | c :: r => if c = b then some r else none

/-- Strictly below the left child is the unique constructor-overlap case. -/
def eta (S : Menu) : Bool :=
  !S.all (fun q => match q with
    | false :: _ :: _ => true
    | _ => false)

private def weight (S : Menu) : Nat := (S.map (fun q => q.length + 1)).sum

private theorem child_weight_le (b : Bool) (S : Menu) : weight (child b S) ≤ weight S := by
  induction S with
  | nil => simp [child, weight]
  | cons q S ih =>
    cases q with
    | nil => simpa [child, weight] using Nat.le_trans ih (Nat.le_add_left _ _)
    | cons c q =>
      by_cases h : c = b
      · simp only [child, List.filterMap_cons, h, ↓reduceIte, List.filterMap,
          weight, List.map_cons, List.sum_cons, List.length_cons] at *
        omega
      · simp only [child, List.filterMap_cons, h, ↓reduceIte, weight,
          List.map_cons, List.sum_cons, List.length_cons] at *
        omega

private theorem child_weight_lt (b : Bool) (S : Menu) (h : S ≠ []) :
    weight (child b S) < weight S := by
  cases S with
  | nil => contradiction
  | cons q S =>
    have ih := child_weight_le b S
    cases q with
    | nil =>
      simp only [child, List.filterMap_cons, weight, List.map_cons, List.sum_cons,
        List.length_nil] at *
      omega
    | cons c q =>
      by_cases hc : c = b <;>
        simp only [child, List.filterMap_cons, hc, ↓reduceIte, weight,
          List.map_cons, List.sum_cons, List.length_cons] at * <;> omega

/-- Count and rank are computed jointly by the original menu recursion. -/
def grammar (S : Menu) : Nat × (Source → Nat) :=
  if h : S = [] then (1, fun _ => 0) else
    let L := grammar (child false S)
    let R := grammar (child true S)
    let J := L.1 * R.1
    (J + 1 + (if eta S then 1 else 0), fun u => match u with
      | .mul x y => L.2 x * R.1 + R.2 y
      | .of true => J
      | .of false => if eta S then J + 1 else
          L.2 (.of true) * R.1 + R.2 (.of true))
termination_by weight S
decreasing_by all_goals exact child_weight_lt _ _ h

/-- Original FM.16 count, with one state for an empty menu. -/
def N (S : Menu) : Nat := (grammar S).1

/-- Original FM.17 numerical rank; branch digits precede leaf tags. -/
def code (S : Menu) (u : Source) : Nat := (grammar S).2 u

private theorem grammar_empty : grammar [] = (1, fun _ => 0) := by
  rw [grammar]; simp

private theorem grammar_nonempty (S : Menu) (h : S ≠ []) :
    grammar S =
      (N (child false S) * N (child true S) + 1 + (if eta S then 1 else 0),
       fun u => match u with
       | .mul x y => code (child false S) x * N (child true S) + code (child true S) y
       | .of true => N (child false S) * N (child true S)
       | .of false => if eta S then N (child false S) * N (child true S) + 1 else
           code (child false S) (.of true) * N (child true S) +
             code (child true S) (.of true)) := by
  rw [grammar]; simp only [h, ↓reduceDIte, N, code]

private theorem N_empty : N [] = 1 := congrArg Prod.fst grammar_empty
private theorem code_empty (u : Source) : code [] u = 0 :=
  congrArg (fun g => g.2 u) grammar_empty

private theorem N_nonempty (S : Menu) (h : S ≠ []) :
    N S = N (child false S) * N (child true S) + 1 + (if eta S then 1 else 0) :=
  congrArg Prod.fst (grammar_nonempty S h)

private theorem code_node (S : Menu) (h : S ≠ []) (x y : Source) :
    code S (.mul x y) = code (child false S) x * N (child true S) +
      code (child true S) y := congrArg (fun g => g.2 (.mul x y)) (grammar_nonempty S h)

private theorem code_alpha (S : Menu) (h : S ≠ []) :
    code S (.of true) = N (child false S) * N (child true S) :=
  congrArg (fun g => g.2 (.of true)) (grammar_nonempty S h)

private theorem code_beta (S : Menu) (h : S ≠ []) :
    code S (.of false) = if eta S then N (child false S) * N (child true S) + 1 else
      code (child false S) (.of true) * N (child true S) + code (child true S) (.of true) :=
  congrArg (fun g => g.2 (.of false)) (grammar_nonempty S h)

/-- Exact source equations and the original branch digit range, for every ordered menu. -/
theorem original_code_grammar (S : Menu) :
    (S = [] → N S = 1 ∧ ∀ u, code S u = 0) ∧
    (S ≠ [] →
      N S = N (child false S) * N (child true S) + 1 + (if eta S then 1 else 0) ∧
      (∀ x y, code S (.mul x y) = code (child false S) x * N (child true S) + code (child true S) y) ∧
      code S (.of true) = N (child false S) * N (child true S) ∧
      code S (.of false) = if eta S then N (child false S) * N (child true S) + 1 else
        code (child false S) (.of true) * N (child true S) + code (child true S) (.of true)) ∧
    0 < N S ∧ (∀ u, code S u < N S) := by
  have bounds : ∀ S : Menu, 0 < N S ∧ ∀ u, code S u < N S := by
    intro S
    induction S using (measure weight).wf.induction with
    | h S ih =>
      by_cases hs : S = []
      · subst S; simp [N_empty, code_empty]
      · have hl := ih (child false S) (child_weight_lt false S hs)
        have hr := ih (child true S) (child_weight_lt true S hs)
        rw [N_nonempty S hs]
        refine ⟨by omega, ?_⟩
        intro u
        cases u with
        | of b =>
          cases b with
          | false =>
            rw [code_beta S hs]
            have ha := hl.2 (.of true)
            have hb := hr.2 (.of true)
            split
            · omega
            · nlinarith
          | true => rw [code_alpha S hs]; omega
        | mul x y =>
          rw [code_node S hs]
          have hx := hl.2 x
          have hy := hr.2 y
          have hm := Nat.mul_le_mul_right (N (child true S)) (Nat.succ_le_of_lt hx)
          simp only [Nat.succ_eq_add_one, Nat.add_mul, one_mul] at hm
          omega
  exact ⟨by rintro rfl; exact ⟨N_empty, code_empty⟩,
    fun h => ⟨N_nonempty S h, code_node S h, code_alpha S h, code_beta S h⟩,
    (bounds S).1, (bounds S).2⟩

/-- The prescribed FM.21 context, with alpha at every side sibling. -/
def spine (a : Address) (z : Source) : Source :=
  a.foldr (fun b t => if b then .mul (.of true) t else .mul t (.of true)) z

theorem mem_child (b : Bool) (S : Menu) (r : Address) :
    r ∈ child b S ↔ b :: r ∈ S := by
  simp only [child, List.mem_filterMap]
  constructor
  · rintro ⟨q, hq, he⟩
    cases q with
    | nil => simp at he
    | cons c q =>
      by_cases hc : c = b
      · subst c; simp only [↓reduceIte, Option.some.injEq] at he
        subst q; exact hq
      · simp [hc] at he
  · intro h
    exact ⟨b :: r, h, by simp⟩

private theorem alpha_beta_distinct (S : Menu) (h : S ≠ []) :
    code S (.of true) ≠ code S (.of false) := by
  rw [code_alpha S h, code_beta S h]
  split
  · omega
  · have hl := (original_code_grammar (child false S)).2.2.2 (.of true)
    have hr := (original_code_grammar (child true S)).2.2.2 (.of true)
    have hp := (original_code_grammar (child true S)).2.2.1
    have hm := Nat.mul_le_mul_right (N (child true S)) (Nat.succ_le_of_lt hl)
    nlinarith

/-- The same original-code distinction propagates through each actual path context. -/
theorem original_code_context_separation (S : Menu) (a r : Address)
    (selected : a ++ r ∈ S) :
    code S (spine a (.of true)) ≠ code S (spine a (.of false)) := by
  induction a generalizing S with
  | nil =>
    have hn : S ≠ [] := by intro he; simp [he] at selected
    exact alpha_beta_distinct S hn
  | cons b a ih =>
    have hn : S ≠ [] := by intro he; simp [he] at selected
    have hc : a ++ r ∈ child b S := (mem_child b S _).mpr selected
    have hd := ih (child b S) hc
    cases b
    · simp only [spine, List.foldr, Bool.false_eq_true, ↓reduceIte]
      rw [code_node S hn, code_node S hn]
      have hp := (original_code_grammar (child true S)).2.2.1
      intro he
      have hm := Nat.add_right_cancel he
      apply hd
      change code (child false S) (spine a (.of true)) * N (child true S) =
        code (child false S) (spine a (.of false)) * N (child true S) at hm
      exact Nat.eq_of_mul_eq_mul_right hp hm
    · simp only [spine, List.foldr, ↓reduceIte]
      rw [code_node S hn, code_node S hn]
      intro he
      exact hd (Nat.add_left_cancel he)

end D5.S3.Arith.FibonacciAtomic.Observer.NativeFiniteMenuCode
