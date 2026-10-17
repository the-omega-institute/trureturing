/- GID: D5/S1/Digit/Infinite/NaturalSequenceCodec
   generality: G
   mirror-B: D5/B/S1/Digit/Infinite/NaturalSequenceCodec
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Paired unary streams encode natural sequences with executable prefix recovery. -/

import D5.S0.Computability.BinaryMachine.UnaryWords
import D5.S1.Digit.Infinite.SuccessorContinuity
import Mathlib.Data.Stream.Init

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S1.Digit.Infinite.NaturalSequenceCodec

open Complexity.SAT
open Complexity.SATBounds
open scoped Stream'

/-- The literal finite block consisting of `n` copies of `10`, followed by `00`. -/
def block (n : ℕ) : List Bool :=
  (List.replicate n [true, false]).flatten ++ [false, false]

/-- The first `n` blocks of the infinite code. -/
def encodedPrefix (p : ℕ → ℕ) : ℕ → List Bool
  | 0 => []
  | n + 1 => block (p 0) ++ encodedPrefix (fun k => p (k + 1)) n

private def unaryPrefix (p : ℕ → ℕ) : ℕ → List Bool
  | 0 => []
  | n + 1 => writeNat (p 0) ++ unaryPrefix (fun k => p (k + 1)) n

/-- Random access to the concatenation of the nonempty unary words. The recursive
index decreases by at least one, even when a source entry is zero. -/
private def unaryStream (p : ℕ → ℕ) (j : ℕ) : Bool :=
  if h : j < (writeNat (p 0)).length then (writeNat (p 0))[j]
  else unaryStream (fun k => p (k + 1)) (j - (writeNat (p 0)).length)
termination_by j
 decreasing_by simp only [writeNat_length] at *; omega

/-- Interleave the unary stream with zeros: `1` becomes `10`, and `0` becomes `00`. -/
def encode (p : ℕ → ℕ) : SuccessorContinuity.LegalDigits :=
  ⟨Stream'.interleave (unaryStream p) (Stream'.const false), by
    intro j h
    have ho (k : ℕ) :
        Stream'.interleave (unaryStream p) (Stream'.const false) (2 * k + 1) = false :=
      Stream'.get_interleave_right k _ _
    have hj := Nat.mod_add_div j 2
    have hm := Nat.mod_lt j (by decide : 0 < 2)
    by_cases hz : j % 2 = 0
    · have he : j + 1 = 2 * (j / 2) + 1 := by omega
      rw [he, ho] at h
      exact Bool.noConfusion h.2
    · have he : j = 2 * (j / 2) + 1 := by omega
      rw [he, ho] at h
      exact Bool.noConfusion h.1⟩

/-- Parse `n` unary numbers from a finite word; ignore the unused suffix. -/
def parsePrefix : ℕ → List Bool → Option (List ℕ)
  | 0, _ => some []
  | n + 1, input => do
      let (a, rest) ← readNat input
      let as ← parsePrefix n rest
      pure (a :: as)

/-- Read the first coordinate of each of `fuel` pairs, then parse `n` numbers.
Only positions below `2 * fuel` of the input stream are queried. -/
def decodePrefix (x : ℕ → Bool) (n fuel : ℕ) : Option (List ℕ) :=
  parsePrefix n (Stream'.take fuel (fun j => x (2 * j)))

private theorem unary_expansion (p : ℕ → ℕ) :
    unaryStream p = writeNat (p 0) ++ₛ unaryStream (fun k => p (k + 1)) := by
  funext j
  by_cases h : j < (writeNat (p 0)).length
  · rw [unaryStream, dif_pos h]
    exact (Stream'.get_append_left j _ _ h).symm
  · rw [unaryStream, dif_neg h]
    have hj : j = (writeNat (p 0)).length + (j - (writeNat (p 0)).length) := by omega
    conv_rhs => rw [hj]
    exact (Stream'.get_append_right _ _ _).symm

private theorem unary_prefix_expansion (p : ℕ → ℕ) (n : ℕ) :
    ∃ s : Stream' Bool, unaryStream p = unaryPrefix p n ++ₛ s := by
  induction n generalizing p with
  | zero => exact ⟨unaryStream p, rfl⟩
  | succ n ih =>
    obtain ⟨s, hs⟩ := ih (fun k => p (k + 1))
    exact ⟨s, by rw [unary_expansion p, hs, unaryPrefix, Stream'.append_append_stream]⟩

private theorem expand_writeNat (n : ℕ) :
    (writeNat n).flatMap (fun b => [b, false]) = block n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [writeNat, block, List.replicate_succ, List.flatten_cons] using ih

private theorem expand_prefix (p : ℕ → ℕ) (n : ℕ) :
    (unaryPrefix p n).flatMap (fun b => [b, false]) = encodedPrefix p n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp only [unaryPrefix, encodedPrefix, List.flatMap_append,
      expand_writeNat, ih]

private theorem interleave_append (w : List Bool) (s : Stream' Bool) :
    Stream'.interleave (w ++ₛ s) (Stream'.const false) =
      w.flatMap (fun b => [b, false]) ++ₛ Stream'.interleave s (Stream'.const false) := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [Stream'.cons_append_stream, Stream'.interleave_eq]
    simpa [List.flatMap_cons, Stream'.cons_append_stream] using congrArg
      (fun t => Stream'.cons b (Stream'.cons false t)) ih

private theorem encode_prefix (p : ℕ → ℕ) (n : ℕ) :
    Stream'.take (encodedPrefix p n).length (encode p).val = encodedPrefix p n := by
  obtain ⟨s, hs⟩ := unary_prefix_expansion p n
  change Stream'.take _ (Stream'.interleave (unaryStream p) (Stream'.const false)) = _
  rw [hs, interleave_append, expand_prefix]
  simpa using Stream'.take_append_of_le_length (encodedPrefix p n).length
    (encodedPrefix p n) (Stream'.interleave s (Stream'.const false)) le_rfl

private theorem parse_prefix (p : ℕ → ℕ) (n : ℕ) (rest : List Bool) :
    parsePrefix n (unaryPrefix p n ++ rest) = some (Stream'.take n p) := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    simp [unaryPrefix, List.append_assoc, parsePrefix, ih,
      Stream'.take_succ, Stream'.head, Stream'.get]
    rfl

private theorem parse_append (n : ℕ) (w rest : List Bool) (v : List ℕ)
    (h : parsePrefix n w = some v) : parsePrefix n (w ++ rest) = some v := by
  induction n generalizing w v with
  | zero => exact h
  | succ n ih =>
    cases hr : readNat w with
    | none => simp [parsePrefix, hr] at h
    | some pair =>
      obtain ⟨a, tail⟩ := pair
      have hw := readNat_eq_some hr
      subst w
      simp only [parsePrefix, readNat_writeNat] at h
      rw [List.append_assoc]
      simp only [parsePrefix, readNat_writeNat]
      cases ht : parsePrefix n tail with
      | none => simp [ht] at h
      | some vs =>
        have he := ih tail vs ht
        simpa [he, ht] using h

private theorem decode_large (p : ℕ → ℕ) (n fuel : ℕ)
    (h : (unaryPrefix p n).length ≤ fuel) :
    decodePrefix (encode p).val n fuel = some (Stream'.take n p) := by
  have heven : (fun j => (encode p).val (2 * j)) = unaryStream p := by
    funext j
    exact Stream'.get_interleave_left j _ _
  obtain ⟨s, hs⟩ := unary_prefix_expansion p n
  unfold decodePrefix
  rw [heven, hs]
  have hf : fuel = (unaryPrefix p n).length + (fuel - (unaryPrefix p n).length) := by omega
  rw [hf, ← Stream'.append_take]
  exact parse_prefix p n _

private theorem decode_sound (p : ℕ → ℕ) (n fuel : ℕ) (v : List ℕ)
    (h : decodePrefix (encode p).val n fuel = some v) : v = Stream'.take n p := by
  let m := max fuel (unaryPrefix p n).length
  have hlarge := decode_large p n m (Nat.le_max_right _ _)
  have hext : decodePrefix (encode p).val n m = some v := by
    unfold decodePrefix at h ⊢
    have hm : m = fuel + (m - fuel) := by dsimp [m]; omega
    rw [hm, Stream'.take_add]
    exact parse_append _ _ _ _ h
  exact Option.some.inj (hext.symm.trans hlarge)

private theorem decode_exists (x : ℕ → Bool) (hx : ∃ p, (encode p).val = x) (n : ℕ) :
    ∃ fuel, (decodePrefix x n fuel).isSome = true := by
  obtain ⟨p, rfl⟩ := hx
  exact ⟨(unaryPrefix p n).length, by rw [decode_large p n _ le_rfl]; rfl⟩

/-- On the image, search finite windows until parsing succeeds. The image
hypothesis is a proof erased at execution; no preimage is supplied as data. -/
def recoverPrefix (x : ℕ → Bool) (hx : ∃ p, (encode p).val = x) (n : ℕ) : List ℕ :=
  let h := decode_exists x hx n
  (decodePrefix x n (Nat.find h)).get (Nat.find_spec h)

private theorem recover_correct (p : ℕ → ℕ) (n : ℕ) :
    recoverPrefix (encode p).val ⟨p, rfl⟩ n = Stream'.take n p := by
  unfold recoverPrefix
  exact decode_sound p n _ _ (Option.some_get _).symm

private theorem prefix_length (p : ℕ → ℕ) (n : ℕ) :
    2 * n ≤ (encodedPrefix p n).length := by
  induction n generalizing p with
  | zero => simp [encodedPrefix]
  | succ n ih =>
    have h := ih (fun k => p (k + 1))
    simp only [encodedPrefix, block, List.length_append, List.length_cons,
      List.length_nil] at *
    omega

/-- Every natural sequence has the literal legal paired-unary code. Every
finite source prefix is recovered by finite-window search on the image, and
this recovery distinguishes the source from every other natural sequence. -/
theorem natural_sequence_transport (p : ℕ → ℕ) :
    (∀ n : ℕ, Stream'.take (encodedPrefix p n).length (encode p).val = encodedPrefix p n ∧
      2 * n ≤ (encodedPrefix p n).length) ∧
    (∀ n, recoverPrefix (encode p).val ⟨p, rfl⟩ n = Stream'.take n p) ∧
    (∀ q : ℕ → ℕ, encode p = encode q → p = q) := by
  refine ⟨fun n => ⟨encode_prefix p n, prefix_length p n⟩, recover_correct p, ?_⟩
  intro q h
  funext k
  have hp := recover_correct p (k + 1)
  have hq := recover_correct q (k + 1)
  have hv : Stream'.take (k + 1) p = Stream'.take (k + 1) q := by
    rw [← hp, ← hq]
    simp only [h]
  have hh := congrArg (fun w : List ℕ => w[k]?) hv
  rw [Stream'.getElem?_take_succ, Stream'.getElem?_take_succ] at hh
  exact Option.some.inj hh

end D5.S1.Digit.Infinite.NaturalSequenceCodec
