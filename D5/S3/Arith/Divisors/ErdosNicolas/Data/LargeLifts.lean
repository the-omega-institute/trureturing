/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/LargeLifts
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/LargeLifts.large_ok
   digest: All large exceptional-lift triples from complete integer certificates. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.Large00
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Large01
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Large02
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Large03
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Large04
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Large05
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Large06
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Large07
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Large08
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Large09
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Large10
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Large11
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Large12
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Large13
import D5.S3.Arith.Divisors.ErdosNicolas.Data.Large14

/-! The triple domain is checked for exact equality, including both second powers. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ErdosNicolas.Data.LargeLifts

open D5.S3.Arith.ErdosNicolas

private def triples : List (ℕ × ℕ × ℕ) :=
  Large00.triples ++
  Large01.triples ++
  Large02.triples ++
  Large03.triples ++
  Large04.triples ++
  Large05.triples ++
  Large06.triples ++
  Large07.triples ++
  Large08.triples ++
  Large09.triples ++
  Large10.triples ++
  Large11.triples ++
  Large12.triples ++
  Large13.triples ++
  Large14.triples

private def primeValues : List ℕ :=
  (List.range 674).filter fun p => decide (19 ≤ p) && checkPrime p

private def exceptionValues : List ℕ :=
  [12, 24, 60, 120, 180, 240, 360, 420, 720, 840, 1260, 1680, 2520, 5040]

private def exponentValues (p : ℕ) : List ℕ :=
  if p < 29 then [1, 2] else [1]

private theorem mem_primeValues {p : ℕ} : p ∈ primeValues ↔ p ∈ largePrimes 674 := by
  simp only [primeValues, List.mem_filter, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq, checkPrime_iff, largePrimes, Finset.mem_filter, Finset.mem_Ico]
  tauto

private theorem mem_exceptionValues {e : ℕ} : e ∈ exceptionValues ↔ e ∈ exceptions := by
  simp [exceptionValues, exceptions]

private theorem mem_exponentValues {p a : ℕ} :
    a ∈ exponentValues p ↔ a ∈ largeLiftExponents p := by
  by_cases hp : p < 29
  · simp only [exponentValues, largeLiftExponents, if_pos hp, Finset.mem_Icc,
      List.mem_cons, List.not_mem_nil, or_false]
    omega
  · simp only [exponentValues, largeLiftExponents, if_neg hp, Finset.mem_Icc,
      List.mem_cons, List.not_mem_nil, or_false]
    omega

private def canonicalLargeTriples : List (ℕ × ℕ × ℕ) :=
  primeValues.flatMap fun p =>
    exceptionValues.flatMap fun e => (exponentValues p).map fun a => (e, p, a)

set_option maxRecDepth 8192 in
private theorem list_eq : triples = canonicalLargeTriples := by decide +kernel

private theorem canonical_toFinset : canonicalLargeTriples.toFinset = largeLiftTriples := by
  ext v
  simp only [canonicalLargeTriples, List.mem_toFinset, List.mem_flatMap, List.mem_map,
    mem_primeValues, mem_exceptionValues, mem_exponentValues, largeLiftTriples,
    Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, e, he, a, ha, hv⟩
    exact ⟨e, he, p, hp, a, ha, hv⟩
  · rintro ⟨e, he, p, hp, a, ha, hv⟩
    exact ⟨p, hp, e, he, a, ha, hv⟩

private theorem coverage : largeLiftTriples = triples.toFinset := by
  rw [list_eq, canonical_toFinset]

private theorem append_strict {xs ys : List (ℕ × ℕ × ℕ)}
    (hx : ∀ v ∈ xs, hHat (largeLiftValue v) < ((largeLiftValue v).divisors.card : ℚ))
    (hy : ∀ v ∈ ys, hHat (largeLiftValue v) < ((largeLiftValue v).divisors.card : ℚ)) :
    ∀ v ∈ xs ++ ys, hHat (largeLiftValue v) < ((largeLiftValue v).divisors.card : ℚ) := by
  intro v hv
  exact (List.mem_append.mp hv).elim (hx v) (hy v)

theorem large_ok : LargeLiftsOK := by
  intro v hv
  have hm : v ∈ triples := List.mem_toFinset.mp (by rwa [← coverage])
  have hall :=
    append_strict Large00.strict_on_triples
      (append_strict Large01.strict_on_triples
        (append_strict Large02.strict_on_triples
          (append_strict Large03.strict_on_triples
            (append_strict Large04.strict_on_triples
              (append_strict Large05.strict_on_triples
                (append_strict Large06.strict_on_triples
                  (append_strict Large07.strict_on_triples
                    (append_strict Large08.strict_on_triples
                      (append_strict Large09.strict_on_triples
                        (append_strict Large10.strict_on_triples
                          (append_strict Large11.strict_on_triples
                            (append_strict Large12.strict_on_triples
                              (append_strict Large13.strict_on_triples
                                Large14.strict_on_triples)))))))))))))
  exact hall v (by simpa only [triples, List.append_assoc] using hm)

#print axioms large_ok

end D5.S3.Arith.ErdosNicolas.Data.LargeLifts
