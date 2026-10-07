/- GID: D5/S3/Arith/FibonacciAtomic/AtomicPrefixParser
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/AtomicPrefixParser
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Literal two-letter tree codes have exact recursive parsing boundaries and prefix-free image. -/

import D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport
import D5.S0.Computability.Coding.PrefixFreeCode
import Mathlib.Computability.Encoding

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.AtomicPrefixParser

open GenealogicalFiberTransport (Source)
open D5.S0.Computability.Coding.PrefixFreeCode (IsPrefixFree)

/-- Literal serialization; true denotes alpha and false denotes beta. -/
def code : Source → List Bool
  | .of b => [true, b]
  | .mul s t => false :: (code s ++ code t)

/-- Depth fuel bounds recursion; the right child reads the actual left remainder. -/
private def parseFuel : ℕ → List Bool → Option (Source × List Bool)
  | 0, _ => none
  | n + 1, true :: b :: r => some (.of b, r)
  | n + 1, false :: w =>
      match parseFuel n w with
      | none => none
      | some (s, r) =>
          match parseFuel n r with
          | none => none
          | some (t, r') => some (.mul s t, r')
  | _ + 1, _ => none

/-- Parse one complete tree and retain all following letters. -/
def parse (w : List Bool) : Option (Source × List Bool) := parseFuel w.length w

/-- Decode exactly one complete codeword, rejecting every nonempty remainder. -/
def decode (w : List Bool) : Option Source :=
  match parse w with
  | some (t, []) => some t
  | _ => none

/-- Exact consumption, injectivity, prefix freedom, and full-word decoding. -/
theorem result :
    (∀ (w : List Bool) (t : Source) (r : List Bool),
      parse w = some (t, r) ↔ w = code t ++ r) ∧
    Function.Injective code ∧ IsPrefixFree (Set.range code) ∧
    (∀ (w : List Bool) (t : Source), decode w = some t ↔ w = code t) := by
  have sound : ∀ (n : ℕ) (w : List Bool) (t : Source) (r : List Bool),
      parseFuel n w = some (t, r) → w = code t ++ r := by
    intro n
    induction n with
    | zero => intro w t r h; simp [parseFuel] at h
    | succ n ih =>
      intro w t r h
      cases w with
      | nil => simp [parseFuel] at h
      | cons a w =>
        cases a with
        | false =>
          cases hl : parseFuel n w with
          | none => simp [parseFuel, hl] at h
          | some p =>
            rcases p with ⟨s, v⟩
            cases hr : parseFuel n v with
            | none => simp [parseFuel, hl, hr] at h
            | some p =>
              rcases p with ⟨u, z⟩
              simp only [parseFuel, hl, hr, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              rw [ih w s v hl, ih v u z hr]
              simp only [code, List.cons_append, List.append_assoc]
        | true =>
          cases w with
          | nil => simp [parseFuel] at h
          | cons b v =>
            simp only [parseFuel, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rfl
  have complete : ∀ (t : Source) (r : List Bool) (n : ℕ),
      (code t).length ≤ n → parseFuel n (code t ++ r) = some (t, r) := by
    intro t
    induction t with
    | of b =>
      intro r n hn
      cases n with
      | zero => simp [code] at hn
      | succ n => rfl
    | mul s t hs ht =>
      intro r n hn
      cases n with
      | zero => simp [code] at hn
      | succ n =>
        have hlen : 1 + ((code s).length + (code t).length) ≤ n + 1 := by
          simpa only [code, List.length_cons, List.length_append, Nat.add_comm] using hn
        have hsn : (code s).length ≤ n := by omega
        have htn : (code t).length ≤ n := by omega
        simp only [code, List.cons_append, List.append_assoc, parseFuel]
        simp only [hs (code t ++ r) n hsn, ht r n htn]
  have parsed : ∀ (w : List Bool) (t : Source) (r : List Bool),
      parse w = some (t, r) ↔ w = code t ++ r := by
    intro w t r
    constructor
    · exact sound w.length w t r
    · intro h
      subst w
      apply complete
      simp only [List.length_append]
      omega
  have decoded : ∀ (w : List Bool) (t : Source), decode w = some t ↔ w = code t := by
    intro w t
    constructor
    · intro h
      cases hp : parse w with
      | none => simp [decode, hp] at h
      | some p =>
        rcases p with ⟨u, r⟩
        cases r with
        | nil =>
          simp only [decode, hp, Option.some.injEq] at h
          subst u
          simpa only [List.append_nil] using (parsed w t []).mp hp
        | cons b r => simp [decode, hp] at h
    · intro h
      subst w
      have hp : parse (code t) = some (t, []) :=
        (parsed (code t) t []).mpr (List.append_nil (code t)).symm
      simp only [decode, hp]
  let encoding : Computability.Encoding Source Bool :=
    ⟨code, decode, fun t => (decoded (code t) t).mpr rfl⟩
  refine ⟨parsed, encoding.encode_injective, ?_, decoded⟩
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ hprefix
  obtain ⟨r, hr⟩ := hprefix
  have hs : parse (code t) = some (s, r) := (parsed (code t) s r).mpr hr.symm
  have ht : parse (code t) = some (t, []) :=
    (parsed (code t) t []).mpr (List.append_nil (code t)).symm
  have hpair : (s, r) = (t, []) := Option.some.inj (hs.symm.trans ht)
  exact congrArg code (congrArg Prod.fst hpair)

end D5.S3.Arith.FibonacciAtomic.AtomicPrefixParser
