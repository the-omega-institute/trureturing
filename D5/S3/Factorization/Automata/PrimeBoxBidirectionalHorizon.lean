/- GID: D5/S3/Factorization/Automata/PrimeBoxBidirectionalHorizon
   generality: G
   mirror-B: D5/B/S3/Factorization/Automata/PrimeBoxBidirectionalHorizon
   mirror-E: none(waiver:all-prime-boxes-all-mixed-words)
   anchors: []
   utility: none
   digest: Mixed multiply/divide continuations on a finite prime box induce exactly the product of realized two-boundary horizon profiles. -/

import D5.S3.Factorization.Automata.BoundedPrimeHorizon
import D5.S3.Factorization.Automata.PrimeCapacityHorizon

set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.Factorization.Automata.PrimeBoxBidirectionalHorizon

open BoundedPrimeHorizon
open D5.S0.Automata.TypedPartialDFAOOverBase

variable {I : Type*} [DecidableEq I]

/-- Retain the ordered commands on one register; commands on other registers
neither consume its capacity nor erase its previous guard failures. -/
def localWord : List (I × Bool) → I → List Bool
  | [], _ => []
  | (j, b) :: w, i => if j = i then b :: localWord w i else localWord w i

/-- Joint arithmetic legality requires the SAME starting exponent tuple and
every ordered local run to succeed. In particular, net exponent cancellation
cannot turn an earlier failed exact division into a legal history. -/
def allowed (a : I → Nat) : Option (PrimeCapacityHorizon.Capacity a) → List (I × Bool) → Prop
  | none, _ => False
  | some e, w => ∀ i, accepts (a i) (e i) (localWord w i) = true

abbrev Profile (a : I → Nat) (H : Nat) := ∀ i, Fin (min (a i) (2 * H) + 1)

def boxCode (a : I → Nat) (H : Nat) (q : Option (PrimeCapacityHorizon.Capacity a)) :
    Option (Profile a H) := q.map (fun e i => code (a i) H (e i))

/-- Exact mixed-word horizon quotient, with a realized profile on every axis.
The reject point is retained even for an empty alphabet; reachability of that
point is not claimed in the degenerate empty-alphabet case. -/
theorem mixed_word_profile_classification [Fintype I] (a : I → Nat) (H : Nat) :
    Function.Surjective (boxCode a H) ∧
    (∀ q r : Option (PrimeCapacityHorizon.Capacity a),
      (∀ w : List (I × Bool), w.length ≤ H → (allowed a q w ↔ allowed a r w)) ↔
        boxCode a H q = boxCode a H r) ∧
    Fintype.card (Option (Profile a H)) = 1 + ∏ i, (min (a i) (2 * H) + 1) := by
  have hlen (w : List (I × Bool)) (i : I) : (localWord w i).length ≤ w.length := by
    induction w with
    | nil => simp [localWord]
    | cons c w ih =>
        rcases c with ⟨j, b⟩
        by_cases h : j = i <;> simp [localWord, h] <;> omega
  have hlift (w : List Bool) (i j : I) :
      localWord (w.map (fun b => (i, b))) j = if i = j then w else [] := by
    induction w with
    | nil => simp [localWord]
    | cons b w ih =>
        by_cases h : i = j
        · subst j
          simp at ih
          simp [List.map_cons, localWord, ih]
        · simp [List.map_cons, localWord, h, ih]
  have hliftAllowed (e : PrimeCapacityHorizon.Capacity a) (i : I) (w : List Bool) :
      allowed a (some e) (w.map (fun b => (i, b))) ↔ accepts (a i) (e i) w = true := by
    constructor
    · intro he
      simpa [hlift] using he i
    · intro he j
      by_cases hij : i = j
      · subst j
        simpa [hlift] using he
      · simp [hlift, hij, accepts, run, runTransition]
  have hscalar (i : I) (e f : Fin (a i + 1)) :
      (∀ w : List Bool, w.length ≤ H → accepts (a i) e w = accepts (a i) f w) ↔
        code (a i) H e = code (a i) H f := by
    simpa only [observed, Option.map_some, Option.some.injEq] using
      (profile_classification (a i) H).2.1 (some e) (some f)
  have hlive (e f : PrimeCapacityHorizon.Capacity a) :
      (∀ w : List (I × Bool), w.length ≤ H →
        (allowed a (some e) w ↔ allowed a (some f) w)) ↔
      (∀ i, code (a i) H (e i) = code (a i) H (f i)) := by
    constructor
    · intro h i
      apply (hscalar i (e i) (f i)).mp
      intro w hw
      have hc := h (w.map (fun b => (i, b))) (by simpa using hw)
      rw [hliftAllowed, hliftAllowed] at hc
      exact Bool.eq_iff_iff.mpr hc
    · intro h w hw
      have hs (i : I) :
          accepts (a i) (e i) (localWord w i) = accepts (a i) (f i) (localWord w i) :=
        (hscalar i (e i) (f i)).mpr (h i) (localWord w i) ((hlen w i).trans hw)
      constructor
      · intro he i
        rw [← hs i]
        exact he i
      · intro hf i
        rw [hs i]
        exact hf i
  refine ⟨?_, ?_, ?_⟩
  · intro q
    cases q with
    | none => exact ⟨none, rfl⟩
    | some q =>
        have hex (i : I) : ∃ e : Fin (a i + 1), code (a i) H e = q i := by
          obtain ⟨s, hs⟩ := (profile_classification (a i) H).1 (some (q i))
          cases s with
          | none => simp at hs
          | some e => exact ⟨e, Option.some.inj hs⟩
        choose e he using hex
        refine ⟨some e, ?_⟩
        simp only [boxCode, Option.map_some, Option.some.injEq]
        funext i
        exact he i
  · intro q r
    cases q with
    | none =>
        cases r with
        | none => simp [allowed, boxCode]
        | some f =>
            constructor
            · intro h
              have hf := (h [] (by simp)).mpr
                (by simp [allowed, localWord, accepts, run, runTransition])
              exact hf.elim
            · simp [boxCode]
    | some e =>
        cases r with
        | none =>
            constructor
            · intro h
              have he := (h [] (by simp)).mp
                (by simp [allowed, localWord, accepts, run, runTransition])
              exact he.elim
            · simp [boxCode]
        | some f =>
            rw [hlive]
            simp only [boxCode, Option.map_some, Option.some.injEq, funext_iff]
  · simp [Profile, Fintype.card_pi, Nat.add_comm]

#print axioms mixed_word_profile_classification

end D5.S3.Factorization.Automata.PrimeBoxBidirectionalHorizon
