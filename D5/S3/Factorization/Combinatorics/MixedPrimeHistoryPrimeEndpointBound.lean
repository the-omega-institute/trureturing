/- GID: D5/S3/Factorization/Combinatorics/MixedPrimeHistoryPrimeEndpointBound
   generality: G
   mirror-B: D5/B/S3/Factorization/Combinatorics/MixedPrimeHistoryPrimeEndpointBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prime endpoints and all but the last letter determine each mixed prime history of length at least two, giving an exponential counting bound. -/

import D5.S3.Factorization.Combinatorics.MixedPrimeHistoryCount
import D5.S3.Factorization.Combinatorics.MixedPrimeHistoryGenerating
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false

namespace D5.S3.Factorization.Combinatorics.MixedPrimeHistoryPrimeEndpointBound

open D5.S3.Factorization.Combinatorics.MixedPrimeHistoryCount
open D5.S3.Factorization.Combinatorics.MixedPrimeHistoryGenerating
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality

set_option maxHeartbeats 800000 in
/-- If m primes are at most X, at most m times (2m) to the power k minus one histories
of length k end at these primes, whenever X and k are at least two. -/
theorem prime_endpoint_count_bound (X k : ℕ) (hX : 2 ≤ X) (hk : 2 ≤ k) :
    (∑ p ∈ Nat.primesLE X, lengthCount k p) ≤
      (Nat.primesLE X).card * (2 * (Nat.primesLE X).card) ^ (k - 1) := by
  classical
  let label : PrimeLetter → ℕ := Sum.elim Subtype.val Subtype.val
  have growth (a : PrimeLetter) (n : ℕ) (hn : 0 < n) :
      n ≤ primeStep a n ∧ label a ≤ primeStep a n := by
    cases a with
    | inl q =>
        change n ≤ n + q.val ∧ q.val ≤ n + q.val
        omega
    | inr q =>
        have hq := q.property.two_le
        change n ≤ q.val * n ∧ q.val ≤ q.val * n
        constructor <;> nlinarith
  have bounds (w : List PrimeLetter) (n : ℕ) (hn : 0 < n) :
      n ≤ runWord primeStep w n ∧
        ∀ a ∈ w, label a ≤ runWord primeStep w n := by
    induction w generalizing n with
    | nil => simp [runWord]
    | cons a w ih =>
        have hg := growth a n hn
        have hi := ih (primeStep a n) (by omega)
        simp only [runWord]
        constructor
        · exact hg.1.trans hi.1
        · intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact hg.2.trans hi.1
          · exact hi.2 b hb
  have run_append (u v : List PrimeLetter) (n : ℕ) :
      runWord primeStep (u ++ v) n = runWord primeStep v (runWord primeStep u n) := by
    induction u generalizing n with
    | nil => rfl
    | cons a u ih => simpa only [List.cons_append, runWord] using ih (primeStep a n)
  have end_append (u : List PrimeLetter) (a : PrimeLetter) :
      endpoint (u ++ [a]) = primeStep a (endpoint u) := run_append u [a] 1
  have last_additive (w : List PrimeLetter) (hp : (endpoint w).Prime)
      (hl : 2 ≤ w.length) : ∃ q : Nat.Primes, w = w.dropLast ++ [.inl q] := by
    rcases w.eq_nil_or_concat' with rfl | ⟨u, a, rfl⟩
    · simp at hl
    · have hu : u ≠ [] := by
        intro he
        simp [he] at hl
      have hs := sharp_length_bound u hu
      have hlen : 1 ≤ u.length := List.length_pos_iff.mpr hu
      rw [end_append] at hp
      cases a with
      | inl q => exact ⟨q, by simp⟩
      | inr q =>
          exact False.elim (Nat.not_prime_mul q.property.ne_one (by omega) hp)
  let P := {q : ℕ // q ∈ Nat.primesLE X}
  let A := Sum P P
  let forget : A → PrimeLetter := Sum.map
    (fun q => ⟨q.val, Nat.prime_of_mem_primesLE q.property⟩)
    (fun q => ⟨q.val, Nat.prime_of_mem_primesLE q.property⟩)
  let lift : {a : PrimeLetter // label a ≤ X} → A := fun a =>
    match h : a.val with
    | .inl q => .inl ⟨q.val, Nat.mem_primesLE.mpr ⟨by
        have ha := a.property
        rw [h] at ha
        exact ha, q.property⟩⟩
    | .inr q => .inr ⟨q.val, Nat.mem_primesLE.mpr ⟨by
        have ha := a.property
        rw [h] at ha
        exact ha, q.property⟩⟩
  have forget_lift (a : {a : PrimeLetter // label a ≤ X}) : forget (lift a) = a.val := by
    rcases a with ⟨a, ha⟩
    cases a <;> rfl
  have per_prime (p : ℕ) (hp : p ∈ Nat.primesLE X) :
      lengthCount k p ≤ (2 * (Nat.primesLE X).card) ^ (k - 1) := by
    let H := {w : List PrimeLetter // endpoint w = p ∧ w.length = k}
    have bounded (w : H) (a : PrimeLetter) (ha : a ∈ w.val.dropLast) : label a ≤ X := by
      have hb := (bounds w.val 1 (by omega)).2 a (List.mem_of_mem_dropLast ha)
      change label a ≤ endpoint w.val at hb
      rw [w.property.1] at hb
      exact hb.trans (Nat.le_of_mem_primesLE hp)
    let encode : H → List.Vector A (k - 1) := fun w =>
      ⟨w.val.dropLast.attach.map (fun a => lift ⟨a.val, bounded w a.val a.property⟩), by
        simp [w.property.2]⟩
    have decode (w : H) : (encode w).val.map forget = w.val.dropLast := by
      change (w.val.dropLast.attach.map _).map forget = _
      rw [List.map_map]
      have hf : (fun a : {a // a ∈ w.val.dropLast} =>
          forget (lift ⟨a.val, bounded w a.val a.property⟩)) = Subtype.val := by
        funext a
        exact forget_lift _
      simp only [Function.comp_def, hf, List.attach_map_subtype_val]
    have injective : Function.Injective encode := by
      intro u v huv
      have prefixes : u.val.dropLast = v.val.dropLast := by
        rw [← decode u, ← decode v, huv]
      have prime_u : (endpoint u.val).Prime := by
        rw [u.property.1]
        exact Nat.prime_of_mem_primesLE hp
      have prime_v : (endpoint v.val).Prime := by
        rw [v.property.1]
        exact Nat.prime_of_mem_primesLE hp
      obtain ⟨q, hq⟩ := last_additive u.val prime_u (by rw [u.property.2]; exact hk)
      obtain ⟨r, hr⟩ := last_additive v.val prime_v (by rw [v.property.2]; exact hk)
      have eq_q : endpoint u.val.dropLast + q.val = p := by
        have he := u.property.1
        rw [hq, end_append] at he
        exact he
      have eq_r : endpoint v.val.dropLast + r.val = p := by
        have he := v.property.1
        rw [hr, end_append] at he
        exact he
      have qr : q = r := by
        apply Subtype.ext
        rw [prefixes] at eq_q
        omega
      apply Subtype.ext
      rw [hq, hr, prefixes, qr]
    have hc := Nat.card_le_card_of_injective encode injective
    change Nat.card H ≤ _
    calc
      Nat.card H ≤ Nat.card (List.Vector A (k - 1)) := hc
      _ = (2 * (Nat.primesLE X).card) ^ (k - 1) := by
        rw [Nat.card_eq_fintype_card, card_vector]
        simp [A, P, two_mul]
  calc
    (∑ p ∈ Nat.primesLE X, lengthCount k p) ≤
        ∑ _p ∈ Nat.primesLE X, (2 * (Nat.primesLE X).card) ^ (k - 1) :=
      Finset.sum_le_sum per_prime
    _ = _ := by simp

end D5.S3.Factorization.Combinatorics.MixedPrimeHistoryPrimeEndpointBound
