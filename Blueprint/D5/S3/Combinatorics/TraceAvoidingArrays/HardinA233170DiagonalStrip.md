# Horizontal and both diagonal exclusions

## Abstract

The full generating series of normalized four-column six-colour arrays.

OEIS A233170, revision 10, defines literal n by four arrays with colours zero through five. Every horizontal bond and both diagonals between consecutive rows exclude equal colours and colours summing to five. Vertical bonds and wraparound are unconstrained. The upper-left value is zero. Every occurrence of 2, 3 or 4 has a strictly earlier 1, and every 3 has a strictly earlier 2, in row-major order. Colours may be absent. No group action or orbit divisor enters the count.

**Definition 1.1 (An independent literal count).**

$$\forall n: Nat, (\operatorname{a}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(\lambda A: ((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(4\right))) \to \operatorname{Fin}\left(6\right) \mapsto ((\exists i: \operatorname{Fin}\left(n\right), ((\operatorname{Fin}.\operatorname{val}\left(i\right) = 0) \land (A\left((i, 0)\right) = 0))) \land ((\forall i: \operatorname{Fin}\left(n\right), (\forall j: \operatorname{Fin}\left(3\right), ((A\left((i, \operatorname{Fin}.\operatorname{castSucc}\left(j\right))\right) \neq A\left((i, \operatorname{Fin}.\operatorname{succ}\left(j\right))\right)) \land (\operatorname{Fin}.\operatorname{val}\left(A\left((i, \operatorname{Fin}.\operatorname{castSucc}\left(j\right))\right)\right) + \operatorname{Fin}.\operatorname{val}\left(A\left((i, \operatorname{Fin}.\operatorname{succ}\left(j\right))\right)\right) \neq 5)))) \land ((\forall i: \operatorname{Fin}\left(n\right), (\forall h: \operatorname{Fin}.\operatorname{val}\left(i\right) + 1 < n, (\forall j: \operatorname{Fin}\left(3\right), (((A\left((i, \operatorname{Fin}.\operatorname{castSucc}\left(j\right))\right) \neq A\left((\operatorname{Fin}.\operatorname{mk}\left(\operatorname{Fin}.\operatorname{val}\left(i\right) + 1, h\right), \operatorname{Fin}.\operatorname{succ}\left(j\right))\right)) \land (\operatorname{Fin}.\operatorname{val}\left(A\left((i, \operatorname{Fin}.\operatorname{castSucc}\left(j\right))\right)\right) + \operatorname{Fin}.\operatorname{val}\left(A\left((\operatorname{Fin}.\operatorname{mk}\left(\operatorname{Fin}.\operatorname{val}\left(i\right) + 1, h\right), \operatorname{Fin}.\operatorname{succ}\left(j\right))\right)\right) \neq 5)) \land ((A\left((i, \operatorname{Fin}.\operatorname{succ}\left(j\right))\right) \neq A\left((\operatorname{Fin}.\operatorname{mk}\left(\operatorname{Fin}.\operatorname{val}\left(i\right) + 1, h\right), \operatorname{Fin}.\operatorname{castSucc}\left(j\right))\right)) \land (\operatorname{Fin}.\operatorname{val}\left(A\left((i, \operatorname{Fin}.\operatorname{succ}\left(j\right))\right)\right) + \operatorname{Fin}.\operatorname{val}\left(A\left((\operatorname{Fin}.\operatorname{mk}\left(\operatorname{Fin}.\operatorname{val}\left(i\right) + 1, h\right), \operatorname{Fin}.\operatorname{castSucc}\left(j\right))\right)\right) \neq 5)))))) \land (\forall p: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(4\right)), ((((A\left(p\right) = 2) \lor ((A\left(p\right) = 3) \lor (A\left(p\right) = 4))) \implies (\exists q: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(4\right)), ((4 \cdot \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right) + \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right) < 4 \cdot \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right) + \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right)) \land (A\left(q\right) = 1)))) \land ((A\left(p\right) = 3) \implies (\exists q: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(4\right)), ((4 \cdot \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right) + \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right) < 4 \cdot \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right) + \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right)) \land (A\left(q\right) = 2))))))))), \operatorname{Finset}.\operatorname{univ}\left(\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233170DiagonalStrip.a` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

Finset.univ ranges over every function on the displayed finite cell domain. Fin.val gives the natural coordinate. Fin.castSucc and Fin.succ are the two endpoints in adjacent columns; Fin.mk constructs the next row with its displayed bound proof. The rank 4 times row plus column is strictly row-major. The first-cell existential is false when n is zero, so the added constant coefficient is zero. The source counting problem concerns every positive n.

**Theorem 1.2 (The complete rational formal power series).**

$$\operatorname{PowerSeries}.\operatorname{mk}\left(\lambda n: Nat \mapsto (\operatorname{a}\left(n\right): Rat)\right) = 2 \cdot X \cdot \left(5 - 240 \cdot X + 2048 \cdot (X)^{2}\right) \cdot ((\left(1 - 16 \cdot X\right) \cdot \left(1 - 112 \cdot X + 1024 \cdot (X)^{2}\right)))^{-1} \operatorname{in} \operatorname{PowerSeries}\left(Rat\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233170DiagonalStrip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233170` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233170DiagonalStrip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233170","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233170DiagonalStrip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233170: normalized six-colour four-column arrays with horizontal and diagonal exclusion*. URL: <https://oeis.org/A233170>.

*Commentary.*

The private finite_certificate verifies preservation of valid boundary states, the first two continuation weights and the next-step identity, and first-row aggregation totals 10, 800 and 78336. The private continuation_recurrence proves, by induction for every continuation length, the recurrence with coefficients 128, -2816 and 16384. The literal counting bridge transports it to a(n+4)=128 a(n+3)-2816 a(n+2)+16384 a(n+1) for every natural n. Coefficient comparison retains the numerator, and formal inversion is valid because the denominator has constant coefficient one. Thus the identity includes every positive height and the initial coefficients, rather than only an eventual recurrence.

The scanner Seen, good and finish is reused from HardinA233175PairStrip. The width-independent widthNormal, widthLegal, widthStep, widthV, widthTotal and width_counting_bridge, together with colour_bond_iff, are reused from HardinA233251TriangleStrip. Pair labels are BooleanRankThreeK4.beta, with fibres {0,5}, {1,4}, {2,3}. These reused results supply the literal transfer interface; the four-column continuation certificate and its unbounded induction supply the new combinatorial content. The assertion is about finite combinatorial counts and rational formal series. It makes no claim of global priority.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233170DiagonalStrip.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233170DiagonalStrip.result`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip](HardinA233251TriangleStrip.md)
