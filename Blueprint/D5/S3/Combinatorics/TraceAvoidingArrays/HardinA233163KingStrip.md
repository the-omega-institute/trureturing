# Horizontal, vertical and both diagonal exclusions

## Abstract

The full generating series of normalized three-column eight-colour king strips.

OEIS A233163, revision 8, defines literal n by three arrays with colours zero through seven. Every horizontal, vertical and both diagonal bonds exclude equal colours and colours summing to seven. There is no wraparound. The upper-left value is zero. Every occurrence of 2, 3, 4, 5 or 6 has a strictly earlier 1; every 3, 4 or 5 has a strictly earlier 2; every 4 has a strictly earlier 3, in row-major order. Colours may be absent, and no precedence condition is imposed on 7. No group action or orbit divisor enters the count.

**Definition 1.1 (An independent literal count).**

$$\forall n: Nat, (\operatorname{a}\left(n\right) = \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(\lambda A: ((\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(3\right))) \to (\operatorname{Fin}\left(8\right)) \mapsto ((\exists i: \operatorname{Fin}\left(n\right), ((\operatorname{Fin}.\operatorname{val}\left(i\right) = 0) \land (A\left((i, 0)\right) = 0))) \land ((\forall i: \operatorname{Fin}\left(n\right), (\forall j: \operatorname{Fin}\left(2\right), ((A\left((i, \operatorname{Fin}.\operatorname{castSucc}\left(j\right))\right) \neq A\left((i, \operatorname{Fin}.\operatorname{succ}\left(j\right))\right)) \land (\operatorname{Fin}.\operatorname{val}\left(A\left((i, \operatorname{Fin}.\operatorname{castSucc}\left(j\right))\right)\right) + \operatorname{Fin}.\operatorname{val}\left(A\left((i, \operatorname{Fin}.\operatorname{succ}\left(j\right))\right)\right) \neq 7)))) \land (((\forall i: \operatorname{Fin}\left(n\right), (\forall h: \operatorname{Fin}.\operatorname{val}\left(i\right) + 1 < n, (\forall j: \operatorname{Fin}\left(3\right), ((A\left((i, j)\right) \neq A\left((\operatorname{Fin}.\operatorname{mk}\left(\operatorname{Fin}.\operatorname{val}\left(i\right) + 1, h\right), j)\right)) \land (\operatorname{Fin}.\operatorname{val}\left(A\left((i, j)\right)\right) + \operatorname{Fin}.\operatorname{val}\left(A\left((\operatorname{Fin}.\operatorname{mk}\left(\operatorname{Fin}.\operatorname{val}\left(i\right) + 1, h\right), j)\right)\right) \neq 7))))) \land (\forall i: \operatorname{Fin}\left(n\right), (\forall h: \operatorname{Fin}.\operatorname{val}\left(i\right) + 1 < n, (\forall j: \operatorname{Fin}\left(2\right), (((A\left((i, \operatorname{Fin}.\operatorname{castSucc}\left(j\right))\right) \neq A\left((\operatorname{Fin}.\operatorname{mk}\left(\operatorname{Fin}.\operatorname{val}\left(i\right) + 1, h\right), \operatorname{Fin}.\operatorname{succ}\left(j\right))\right)) \land (\operatorname{Fin}.\operatorname{val}\left(A\left((i, \operatorname{Fin}.\operatorname{castSucc}\left(j\right))\right)\right) + \operatorname{Fin}.\operatorname{val}\left(A\left((\operatorname{Fin}.\operatorname{mk}\left(\operatorname{Fin}.\operatorname{val}\left(i\right) + 1, h\right), \operatorname{Fin}.\operatorname{succ}\left(j\right))\right)\right) \neq 7)) \land ((A\left((i, \operatorname{Fin}.\operatorname{succ}\left(j\right))\right) \neq A\left((\operatorname{Fin}.\operatorname{mk}\left(\operatorname{Fin}.\operatorname{val}\left(i\right) + 1, h\right), \operatorname{Fin}.\operatorname{castSucc}\left(j\right))\right)) \land (\operatorname{Fin}.\operatorname{val}\left(A\left((i, \operatorname{Fin}.\operatorname{succ}\left(j\right))\right)\right) + \operatorname{Fin}.\operatorname{val}\left(A\left((\operatorname{Fin}.\operatorname{mk}\left(\operatorname{Fin}.\operatorname{val}\left(i\right) + 1, h\right), \operatorname{Fin}.\operatorname{castSucc}\left(j\right))\right)\right) \neq 7))))))) \land (\forall p: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(3\right)), ((((A\left(p\right) = 2) \lor ((A\left(p\right) = 3) \lor ((A\left(p\right) = 4) \lor ((A\left(p\right) = 5) \lor (A\left(p\right) = 6))))) \implies (\exists q: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(3\right)), ((3 \cdot \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right) + \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right) < 3 \cdot \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right) + \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right)) \land (A\left(q\right) = 1)))) \land ((((A\left(p\right) = 3) \lor ((A\left(p\right) = 4) \lor (A\left(p\right) = 5))) \implies (\exists q: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(3\right)), ((3 \cdot \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right) + \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right) < 3 \cdot \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right) + \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right)) \land (A\left(q\right) = 2)))) \land ((A\left(p\right) = 4) \implies (\exists q: (\operatorname{Fin}\left(n\right)) \times (\operatorname{Fin}\left(3\right)), ((3 \cdot \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(q\right)\right) + \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(q\right)\right) < 3 \cdot \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right)\right) + \operatorname{Fin}.\operatorname{val}\left(\operatorname{Prod}.\operatorname{snd}\left(p\right)\right)) \land (A\left(q\right) = 3)))))))))), \operatorname{Finset}.\operatorname{univ}\left(\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip.a` (`✓ std3`).

*Citation.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233163: normalized eight-colour three-column king strips*. URL: <https://oeis.org/A233163>.

*Commentary.*

Finset.univ ranges over every function on the displayed finite cell domain. Fin.val gives the natural coordinate. Fin.castSucc and Fin.succ are the two endpoints in adjacent columns; Fin.mk constructs the next row with its displayed bound proof. The rank 3 times row plus column is strictly row-major. The first-cell existential is false when n is zero, so the added constant coefficient is zero. The source counting problem concerns every positive n.

**Definition 1.2 (Row).**

$$\operatorname{Row}\left(\right) = (\operatorname{Fin}\left(3\right)) \to (\operatorname{Fin}\left(8\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip.Row` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233163: normalized eight-colour three-column king strips*. URL: <https://oeis.org/A233163>.

*Commentary.*

Signed colours on the ordered row.

**Definition 1.3 (Boundary).**

$$\operatorname{Boundary}\left(\right) = (\operatorname{Fin}\left(3\right)) \to (\operatorname{Fin}\left(4\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip.Boundary` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233163: normalized eight-colour three-column king strips*. URL: <https://oeis.org/A233163>.

*Commentary.*

Complementary-pair colours on the same row.

**Definition 1.4 (rowLegal).**

$$\forall c: (\operatorname{Fin}\left(3\right)) \to (\operatorname{Fin}\left(8\right)), ((\operatorname{rowLegal}\left(c\right)) \iff (\forall j: \operatorname{Fin}\left(2\right), ((c\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right) \neq c\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)) \land (\operatorname{Fin}.\operatorname{val}\left(c\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)\right) + \operatorname{Fin}.\operatorname{val}\left(c\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)\right) \neq 7))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip.rowLegal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233163: normalized eight-colour three-column king strips*. URL: <https://oeis.org/A233163>.

*Commentary.*

Adjacent signed colours exclude equality and complementarity.

**Definition 1.5 (pairs).**

$$\forall c: (\operatorname{Fin}\left(3\right)) \to (\operatorname{Fin}\left(8\right)), (\forall j: \operatorname{Fin}\left(3\right), (\operatorname{pairs}\left(c\right)\left(j\right) = \operatorname{HardinA233196Strip}.\operatorname{beta}\left(c\left(j\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip.pairs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233163: normalized eight-colour three-column king strips*. URL: <https://oeis.org/A233163>.

*Commentary.*

The pair map is applied in each column.

**Definition 1.6 (compatible).**

$$\forall p: (\operatorname{Fin}\left(3\right)) \to (\operatorname{Fin}\left(4\right)), (\forall c: (\operatorname{Fin}\left(3\right)) \to (\operatorname{Fin}\left(8\right)), ((\operatorname{compatible}\left(p, c\right)) \iff ((\forall j: \operatorname{Fin}\left(3\right), (p\left(j\right) \neq \operatorname{HardinA233196Strip}.\operatorname{beta}\left(c\left(j\right)\right))) \land (\forall j: \operatorname{Fin}\left(2\right), ((p\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right) \neq \operatorname{HardinA233196Strip}.\operatorname{beta}\left(c\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right)\right)) \land (p\left(\operatorname{Fin}.\operatorname{succ}\left(j\right)\right) \neq \operatorname{HardinA233196Strip}.\operatorname{beta}\left(c\left(\operatorname{Fin}.\operatorname{castSucc}\left(j\right)\right)\right)))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip.compatible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233163: normalized eight-colour three-column king strips*. URL: <https://oeis.org/A233163>.

*Commentary.*

Vertical and both diagonal pair colours differ.

**Definition 1.7 (step).**

$$\forall w: ((Bool) \times ((Bool) \times (Bool))) \to (((\operatorname{Fin}\left(3\right)) \to (\operatorname{Fin}\left(4\right))) \to (Int)), (\forall t: (Bool) \times ((Bool) \times (Bool)), (\forall p: (\operatorname{Fin}\left(3\right)) \to (\operatorname{Fin}\left(4\right)), (\operatorname{step}\left(w, t, p\right) = \sum_{(c: (\operatorname{Fin}\left(3\right)) \to (\operatorname{Fin}\left(8\right)))} ((\operatorname{if} ((\operatorname{rowLegal}\left(c\right)) \land ((\operatorname{compatible}\left(p, c\right)) \land (\operatorname{HardinA233196Strip}.\operatorname{good}\left(t, c\right)))) \operatorname{then} w\left(\operatorname{HardinA233196Strip}.\operatorname{finish}\left(t, c\right), \operatorname{pairs}\left(c\right)\right) \operatorname{else} (0: Int))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip.step` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233163: normalized eight-colour three-column king strips*. URL: <https://oeis.org/A233163>.

*Commentary.*

The scanner-weighted sum ranges over every signed next row.

**Definition 1.8 (saturated).**

$$\operatorname{saturated}\left(\right) = (true, (true, true))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip.saturated` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233163: normalized eight-colour three-column king strips*. URL: <https://oeis.org/A233163>.

*Commentary.*

All three precedence flags are true.

**Definition 1.9 (proper).**

$$\forall p: (\operatorname{Fin}\left(3\right)) \to (\operatorname{Fin}\left(4\right)), ((\operatorname{proper}\left(p\right)) \iff ((p\left(0\right) \neq p\left(1\right)) \land (p\left(1\right) \neq p\left(2\right))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip.proper` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233163: normalized eight-colour three-column king strips*. URL: <https://oeis.org/A233163>.

*Commentary.*

The productive pair-boundary predicate.

**Definition 1.10 (kind).**

$$\forall p: (\operatorname{Fin}\left(3\right)) \to (\operatorname{Fin}\left(4\right)), (\operatorname{kind}\left(p\right) = \operatorname{decide}\left((p\left(0\right) = p\left(2\right))\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip.kind` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233163: normalized eight-colour three-column king strips*. URL: <https://oeis.org/A233163>.

*Commentary.*

The alternating equality pattern determines the two rates.

**Definition 1.11 (rate).**

$$\forall b: Bool, (\operatorname{rate}\left(b\right) = (\operatorname{if} (b = true) \operatorname{then} (16: Int) \operatorname{else} (8: Int)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip.rate` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233163: normalized eight-colour three-column king strips*. URL: <https://oeis.org/A233163>.

*Commentary.*

The signed continuation count is integer valued.

**Theorem 1.12 (saturated_certificate).**

$$\forall p: (\operatorname{Fin}\left(3\right)) \to (\operatorname{Fin}\left(4\right)), ((\operatorname{proper}\left(p\right)) \implies ((\forall c: (\operatorname{Fin}\left(3\right)) \to (\operatorname{Fin}\left(8\right)), (((\operatorname{rowLegal}\left(c\right)) \land ((\operatorname{compatible}\left(p, c\right)) \land (\operatorname{HardinA233196Strip}.\operatorname{good}\left(\operatorname{saturated}\left(\right), c\right)))) \implies ((\operatorname{HardinA233196Strip}.\operatorname{finish}\left(\operatorname{saturated}\left(\right), c\right) = \operatorname{saturated}\left(\right)) \land ((\operatorname{proper}\left(\operatorname{pairs}\left(c\right)\right)) \land (\operatorname{kind}\left(\operatorname{pairs}\left(c\right)\right) = \operatorname{kind}\left(p\right)))))) \land (\operatorname{step}\left(\operatorname{Function}.\operatorname{const}\left((Bool) \times ((Bool) \times (Bool)), \operatorname{Function}.\operatorname{const}\left((\operatorname{Fin}\left(3\right)) \to (\operatorname{Fin}\left(4\right)), (1: Int)\right)\right), \operatorname{saturated}\left(\right), p\right) = \operatorname{rate}\left(\operatorname{kind}\left(p\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip.saturated_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233163: normalized eight-colour three-column king strips*. URL: <https://oeis.org/A233163>.

*Commentary.*

Every admissible signed continuation preserves saturation, properness and kind; the unweighted sum equals the displayed rate.

**Theorem 1.13 (The complete rational formal power series).**

$$\operatorname{PowerSeries}.\operatorname{mk}\left(\lambda n: Nat \mapsto (\operatorname{a}\left(n\right): Rat)\right) = X \cdot \left(3 - 64 \cdot X + 288 \cdot (X)^{2}\right) \cdot ((\left(1 - 8 \cdot X\right) \cdot \left(1 - 16 \cdot X\right)))^{-1} \operatorname{in} \operatorname{PowerSeries}\left(Rat\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip.result` (`✓ std3`). ∎

*Resolves.* `Problems/hardin233163` (proved) by `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hardin233163","declaration_gid":"D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233163: normalized eight-colour three-column king strips*. URL: <https://oeis.org/A233163>.

*Commentary.*

The four complementary colour pairs are {0,7}, {1,6}, {2,5} and {3,4}. The saturated_certificate checks that a proper pair boundary preserves its ABA or ABC type: there are 16 legal colour-row continuations of an ABA boundary and 8 of an ABC boundary. The private continuation theorem uses these premises in induction over every natural continuation length, giving the corresponding power of 16 or 8. The private finite_certificate checks that every legal two-row seed has seen 1, 2 and 3, and that there are four seeds of each type. Thus count_formula gives a(n+2)=4 times 16 to the n plus 4 times 8 to the n for every natural n, with a(1)=3. The fixed initial cases use continuation at lengths zero and one. These statements feed the coefficient proof of the entire rational series, including the initial numerator.

The public Fin8 scanner Seen, good and finish, the pair map beta and colour_bond_iff, and the width-independent widthNormal, widthLegal, widthStep, widthV, widthTotal and width_counting_bridge are reused directly from HardinA233196Strip. Normal is independently expressed with strict rank 3 times row plus column; normal_iff proves its equivalence with the scanner. Both diagonal directions and every vertical bond are present in bonds. The literal count is independent of the transfer calculation. Formal inversion uses the denominator constant coefficient one. The result concerns rational formal series at every height; there is no finite cutoff or resource assumption.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip.Boundary`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip.Row`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip.compatible`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip.kind`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip.pairs`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip.proper`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip.rate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip.rowLegal`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip.saturated`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip.saturated_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233163KingStrip.step`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233196Strip](HardinA233196Strip.md)
