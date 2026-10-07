/- GID: D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDecoder
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchingsDecoder
   mirror-E: none(waiver:queue-decoder)
   anchors: []
   utility: none
   digest: Accepted scan words construct disjoint pairs covering every vertex. -/

import D5.S3.Combinatorics.PatternMatchings.TripleAvoidingMatchingsEncoding

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PatternMatchings.TripleAvoidingMatchings

open TripleAvoidingMatchingsDefs

/-- The normal and forced phases of the scan automaton. In the forced phase,
openings preserve the obligation, and only an oldest closure clears it. -/
def AcceptFrom : ℕ → Bool → List Action → Prop
  | h, f, [] => h = 0 ∧ f = false
  | h, f, .opening :: w => AcceptFrom (h + 1) f w
  | h, _, .oldest :: w => 0 < h ∧ AcceptFrom (h - 1) false w
  | h, f, .second :: w => f = false ∧ 2 ≤ h ∧ AcceptFrom (h - 1) (decide (3 ≤ h)) w

/-- Accepted labeled words of length `2 * n`. -/
def Accepted (n : ℕ) :=
  {w : Fin (2 * n) → Action // AcceptFrom 0 false (List.ofFn w)}

/-- The queue algorithm pairs each closing vertex with the selected queued opener. -/
def decodePairs {α : Type} : List α → List α → List Action → Option (List (α × α))
  | [], [], [] => some []
  | q, t :: vs, .opening :: w => decodePairs (q ++ [t]) vs w
  | x :: q, t :: vs, .oldest :: w => (decodePairs q vs w).map ((x, t) :: ·)
  | x :: y :: q, t :: vs, .second :: w =>
      (decodePairs (x :: q) vs w).map ((y, t) :: ·)
  | _, _, _ => none

/-- Every accepted word decodes. The resulting pairs use each queued or unscanned
vertex exactly once, as witnessed by a permutation of their endpoint lists. -/
theorem decode_pairs {α : Type} (w : List Action) :
    ∀ (q vs : List α) (f : Bool), vs.length = w.length → AcceptFrom q.length f w →
      ∃ p, decodePairs q vs w = some p ∧
        (p.flatMap fun e => [e.1, e.2]).Perm (q ++ vs) := by
  induction w with
  | nil =>
    intro q vs f hv ha
    have hq : q = [] := List.length_eq_zero_iff.mp ha.1
    have hvs : vs = [] := List.length_eq_zero_iff.mp hv
    subst q
    subst vs
    exact ⟨[], rfl, .refl _⟩
  | cons a w ih =>
    intro q vs f hv ha
    cases vs with
    | nil => simp at hv
    | cons t vs =>
      have hvs : vs.length = w.length := by simpa using hv
      cases a with
      | opening =>
        have ha' : AcceptFrom (q ++ [t]).length f w := by
          simpa [AcceptFrom, List.length_append] using ha
        obtain ⟨p, hp, perm⟩ := ih (q ++ [t]) vs f hvs ha'
        refine ⟨p, by simpa only [decodePairs] using hp, ?_⟩
        simpa only [List.append_assoc, List.singleton_append] using perm
      | oldest =>
        cases q with
        | nil => simp [AcceptFrom] at ha
        | cons x q =>
          have ha' : AcceptFrom q.length false w := by
            simpa [AcceptFrom] using ha.2
          obtain ⟨p, hp, perm⟩ := ih q vs false hvs ha'
          refine ⟨(x, t) :: p, by simp [decodePairs, hp], ?_⟩
          change (x :: t :: p.flatMap (fun e => [e.1, e.2])).Perm
            (x :: (q ++ t :: vs))
          apply List.Perm.cons x
          exact (perm.cons t).trans (List.perm_middle.symm)
      | second =>
        cases q with
        | nil => simp [AcceptFrom] at ha
        | cons x q =>
          cases q with
          | nil => simp [AcceptFrom] at ha
          | cons y q =>
            have ha' : AcceptFrom (x :: q).length
                (decide (3 ≤ (x :: y :: q).length)) w := by
              simpa [AcceptFrom] using ha.2.2
            obtain ⟨p, hp, perm⟩ := ih (x :: q) vs _ hvs ha'
            refine ⟨(y, t) :: p, by simp [decodePairs, hp], ?_⟩
            change (y :: t :: p.flatMap (fun e => [e.1, e.2])).Perm
              (x :: y :: (q ++ t :: vs))
            exact ((perm.cons t).cons y).trans
              (((List.Perm.swap _ _ _).cons y).trans
                ((List.Perm.swap _ _ _).trans ((List.perm_middle.symm.cons y).cons x)))

/-- Turn disjoint pairs into their partner map, fixing vertices not used by a pair. -/
def pairFunction {α : Type} [DecidableEq α] : List (α × α) → α → α
  | [], x => x
  | (a, b) :: p, x => if x = a then b else if x = b then a else pairFunction p x

/-- A list of pairs with no repeated endpoint constructs an involution whose
nonfixed points are exactly the endpoints in that list. -/
theorem pairFunction_spec {α : Type} [DecidableEq α] (p : List (α × α))
    (hn : (p.flatMap fun e => [e.1, e.2]).Nodup) :
    Function.Involutive (pairFunction p) ∧
      ∀ x, pairFunction p x = x ↔ x ∉ p.flatMap (fun e => [e.1, e.2]) := by
  induction p with
  | nil => simp [pairFunction, Function.Involutive]
  | cons e p ih =>
    rcases e with ⟨a, b⟩
    change (a :: b :: p.flatMap (fun e => [e.1, e.2])).Nodup at hn
    obtain ⟨ha, hb, hp⟩ := List.nodup_cons.mp hn |>.imp_right List.nodup_cons.mp
    have hab : a ≠ b := fun h => ha (by simp [h])
    have hap : a ∉ p.flatMap (fun e => [e.1, e.2]) := fun h => ha (by simp [h])
    obtain ⟨hinv, hfix⟩ := ih hp
    have fa : pairFunction p a = a := (hfix a).mpr hap
    have fb : pairFunction p b = b := (hfix b).mpr hb
    have partner_ne (x : α) (hxa : x ≠ a) (hxb : x ≠ b) :
        pairFunction p x ≠ a ∧ pairFunction p x ≠ b := by
      constructor
      · intro h
        have hi := congrArg (pairFunction p) h
        rw [hinv, fa] at hi
        exact hxa hi
      · intro h
        have hi := congrArg (pairFunction p) h
        rw [hinv, fb] at hi
        exact hxb hi
    constructor
    · intro x
      by_cases hxa : x = a
      · subst x
        simp [pairFunction, hab.symm]
      · by_cases hxb : x = b
        · subst x
          simp [pairFunction, hab.symm]
        · obtain ⟨hfa, hfb⟩ := partner_ne x hxa hxb
          simp only [pairFunction, if_neg hxa, if_neg hxb, if_neg hfa, if_neg hfb]
          exact hinv x
    · intro x
      by_cases hxa : x = a
      · subst x
        simp [pairFunction, hab.symm]
      · by_cases hxb : x = b
        · subst x
          simp [pairFunction, hab, hab.symm]
        · simpa [pairFunction, hxa, hxb] using hfix x

/-- Decoding an accepted word gives an actual fixed-point-free involution of the
fixed vertex type. The queue coverage theorem supplies every vertex exactly once. -/
noncomputable def decodeMatching {n : ℕ} (w : Accepted n) : Matching n := by
  classical
  have hex := decode_pairs (List.ofFn w.1) [] (List.finRange (2 * n)) false
    (by simp) w.2
  let p := Classical.choose hex
  have hs := Classical.choose_spec hex
  have hperm : (p.flatMap fun e => [e.1, e.2]).Perm (List.finRange (2 * n)) := by
    simpa using hs.2
  have hn : (p.flatMap fun e => [e.1, e.2]).Nodup :=
    hperm.nodup_iff.mpr (List.nodup_finRange _)
  have hf := pairFunction_spec p hn
  refine ⟨pairFunction p, fun v => ⟨hf.1 v, ?_⟩⟩
  intro h
  have hnot := (hf.2 v).mp h
  exact hnot (hperm.mem_iff.mpr (List.mem_finRange v))

end D5.S3.Combinatorics.PatternMatchings.TripleAvoidingMatchings
