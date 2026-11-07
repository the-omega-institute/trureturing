/- GID: D5/S3/Quantum/Entanglement/EJM/Frontier/EJMOriginalPrefixDecoder
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/Frontier/EJMOriginalPrefixDecoder
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.original_score_lower_bound; instance=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.accepted_original_root
   digest: The base-four decoder reads exactly the requested original coordinate prefix. -/

/- Prepared transient prefix decoder; uncompiled.
Library search: the original Assembly supplies coordinate and prefixPartial;
the separate OriginalPrefixAssociation supplies future-none and association.
No matching partial-to-complete-prefix decoder was found in the existing EJM
or finite-certificate modules. Nat.digits omits leading zeros and uses the
opposite digit order, so it does not directly encode this depth-indexed partial.
The existing Nat.mod_mul theorem supplies the base-four truncation arithmetic.

The intended consumer is a future adaptive frontier selector keyed by the
actual (depth, code), with semantic receipts for that exact prefix. This module
does not supply a selector, receipt table, cut coverage or complete root proof.
It preserves the original Assembly and all active certificate inputs. No cache
equality is inferred from reading a partial assignment. The original twenty
coordinates, four values, F1/F2 and scale 6987435 are unchanged.
These two substantive interfaces are transient integration, not separately
delivered canonical wrappers. Compiled source-owned Reg evidence and binding
remain unfinished under
https://github.com/the-omega-institute/trureturing/issues/16309. -/

import D5.S3.Quantum.Entanglement.EJM.EJMOriginalPrefixAssociation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.TransientEJMOriginalPrefixDecoder
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial Event Compatible)
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalReplayAssembly
  (coordinate prefixPartial)
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalPrefixAssociation
  (prefixPartial_future_none)
open D5.S3.Quantum.Entanglement.EJM.EJMOriginalCachedGlobalReplay (Valid)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState (Cache)
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)
open D5.S3.Quantum.Entanglement.EJMInflationScore (score)

/-- Read exactly depth original coordinates in chronological order.
Each coordinate must be some value, including each leading zero. Depth remains
an independent input; the natural result does not encode length by itself.
The soundness statements restrict depth to at most twenty. -/
def readPrefix : ℕ → Partial (Fin 20) (Fin 4) → Option ℕ
  | 0, _ => some 0
  | depth + 1, p =>
    match readPrefix depth p, p (coordinate depth) with
    | some code, some a => some (4 * code + a.val)
    | _, _ => none

private theorem readPrefix_congr (depth : ℕ) :
    ∀ (p q : Partial (Fin 20) (Fin 4)), depth ≤ 20 →
      (∀ g : Fin 20, g.val < depth → p g = q g) →
      readPrefix depth p = readPrefix depth q := by
  induction depth with
  | zero =>
    intro p q within same
    rfl
  | succ depth ih =>
    intro p q within same
    have below : depth < 20 := by omega
    have previous : readPrefix depth p = readPrefix depth q := by
      apply ih p q (by omega)
      intro g earlier
      exact same g (by omega)
    have current : p (coordinate depth) = q (coordinate depth) := by
      apply same (coordinate depth)
      change depth % 20 < depth + 1
      rw [Nat.mod_eq_of_lt below]
      omega
    simp only [readPrefix, previous, current]

/-- Any natural code constructs only its low depth base-four digits.
Reading recovers that residue, not an arbitrary high-bit representative.
The depth input preserves leading zeros even when the returned code is zero. -/
theorem readPrefix_prefixPartial (depth : ℕ) :
    ∀ (code : ℕ), depth ≤ 20 →
      readPrefix depth (prefixPartial depth code) = some (code % 4 ^ depth) := by
  induction depth with
  | zero =>
    intro code within
    simp only [readPrefix, pow_zero, Nat.mod_one]
  | succ depth ih =>
    intro code within
    have below : depth < 20 := by omega
    have actualCoordinate : (coordinate depth).val = depth :=
      Nat.mod_eq_of_lt below
    have previous : readPrefix depth (prefixPartial (depth + 1) code) =
        readPrefix depth (prefixPartial depth (code / 4)) := by
      apply readPrefix_congr depth _ _ (by omega)
      intro g earlier
      have different : g ≠ coordinate depth := by
        intro same
        have sameValue := congrArg Fin.val same
        omega
      rw [prefixPartial, Function.update_of_ne different]
    have arithmetic :
        4 * (code / 4 % 4 ^ depth) + code % 4 = code % 4 ^ (depth + 1) := by
      rw [pow_succ', Nat.mod_mul]
      omega
    rw [readPrefix, previous, ih (code / 4) (by omega)]
    simp only [prefixPartial, Function.update_self]
    exact congrArg some arithmetic

private theorem readPrefix_sound (depth : ℕ) :
    ∀ (p : Partial (Fin 20) (Fin 4)) (code : ℕ), depth ≤ 20 →
      readPrefix depth p = some code →
      code < 4 ^ depth ∧
        ∀ g : Fin 20, g.val < depth → p g = prefixPartial depth code g := by
  induction depth with
  | zero =>
    intro p code within accepted
    have zero : 0 = code := by
      simpa only [readPrefix, Option.some.injEq] using accepted
    subst code
    constructor
    · exact Nat.zero_lt_one
    · intro g earlier
      omega
  | succ depth ih =>
    intro p code within accepted
    have below : depth < 20 := by omega
    have actualCoordinate : (coordinate depth).val = depth :=
      Nat.mod_eq_of_lt below
    cases previous : readPrefix depth p with
    | none => simp only [readPrefix, previous, reduceCtorEq] at accepted
    | some previousCode =>
      cases current : p (coordinate depth) with
      | none => simp only [readPrefix, previous, current, reduceCtorEq] at accepted
      | some a =>
        have codeEq : 4 * previousCode + a.val = code := by
          simpa only [readPrefix, previous, current, Option.some.injEq] using accepted
        have codeDiv : code / 4 = previousCode := by omega
        have codeMod : code % 4 = a.val := by omega
        obtain ⟨previousBound, previousSame⟩ := ih p previousCode (by omega) previous
        constructor
        · rw [pow_succ']
          have digitBound := a.isLt
          omega
        · intro g earlier
          by_cases last : g = coordinate depth
          · subst g
            rw [prefixPartial, Function.update_self, current]
            apply congrArg some
            apply Fin.ext
            exact codeMod.symm
          · have earlier' : g.val < depth := by
              have differentValue : g.val ≠ depth := by
                intro sameValue
                apply last
                apply Fin.ext
                omega
              omega
            rw [prefixPartial, Function.update_of_ne last, codeDiv]
            exact previousSame g earlier'

/-- On a valid original fuel context, reading is equivalent to a canonical
bounded code and equality with its complete original prefix partial.
The forward implication uses only Valid's future-none condition; it does not
assert that the actual cache equals prefixCache or transfer raw acceptance.
For arbitrary input codes, the separate roundtrip theorem gives truncation. -/
theorem readPrefix_eq_some_iff (depth code : ℕ)
    (p : Partial (Fin 20) (Fin 4)) (cache : Cache) (within : depth ≤ 20)
    (valid : Valid (21 - depth) cache p) :
    readPrefix depth p = some code ↔
      code < 4 ^ depth ∧ p = prefixPartial depth code := by
  constructor
  · intro accepted
    obtain ⟨bound, same⟩ := readPrefix_sound depth p code within accepted
    refine ⟨bound, ?_⟩
    funext g
    by_cases earlier : g.val < depth
    · exact same g earlier
    · have future : depth ≤ g.val := by omega
      have actualDepth : 21 - (21 - depth) = depth := by omega
      have unknown : p g = none := by
        apply valid.1.2 g
        simpa only [actualDepth] using future
      rw [unknown, prefixPartial_future_none depth code within g future]
  · rintro ⟨bound, rfl⟩
    rw [readPrefix_prefixPartial depth code within, Nat.mod_eq_of_lt bound]


#print axioms readPrefix_prefixPartial
#print axioms readPrefix_eq_some_iff
end D5.S3.Quantum.Entanglement.EJM.TransientEJMOriginalPrefixDecoder
