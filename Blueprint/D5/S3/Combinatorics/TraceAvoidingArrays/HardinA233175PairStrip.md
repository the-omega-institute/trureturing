# Six-colour complementary-pair exclusion

## Abstract

Barker's generating function for complementary-pair exclusion on a two-row strip.

The colours are 0 through 5. Consecutive columns have all four possible bonds; there is no bond within a column. A bond forbids equal colours and complementary colours whose sum is five. The distinguished upper-left cell has colour zero. In row-major order every 2, 3 and 4 has an earlier 1, and every 3 has an earlier 2. The empty-strip coefficient is zero. OEIS A233175, revision 7, gives this NAME and labels the displayed generating function a conjecture of Colin Barker.

**Definition 1.1 (Two seen-colour flags).**

$$Seen = (Bool) \times (Bool)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.Seen` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233175: six-colour complementary-pair exclusion on a two-row strip*. URL: <https://oeis.org/A233175>.

*Commentary.*

The first flag records whether colour one has occurred; the second records colour two.

**Definition 1.2 (A column).**

$$Col = (\operatorname{Fin}\left(2\right)) \to \operatorname{Fin}\left(6\right)$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.Col` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233175: six-colour complementary-pair exclusion on a two-row strip*. URL: <https://oeis.org/A233175>.

*Commentary.*

A column is an ordered function on the two row indices.

**Definition 1.3 (The next colour).**

$$\forall s: Seen, (\forall c: \operatorname{Fin}\left(6\right), ((\operatorname{allowed}\left(s, c\right)) \iff ((((c = 2) \lor ((c = 3) \lor (c = 4))) \implies (\operatorname{proj}\left(s, 1\right) = true)) \land ((c = 3) \implies (\operatorname{proj}\left(s, 2\right) = true)))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.allowed` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233175: six-colour complementary-pair exclusion on a two-row strip*. URL: <https://oeis.org/A233175>.

*Commentary.*

The two implications impose exactly the required earlier occurrences.

**Definition 1.4 (Updating the flags).**

$$\forall s: Seen, (\forall c: \operatorname{Fin}\left(6\right), (\operatorname{advance}\left(s, c\right) = (\operatorname{proj}\left(s, 1\right) \operatorname{or} \operatorname{decide}\left(c = 1\right), \operatorname{proj}\left(s, 2\right) \operatorname{or} \operatorname{decide}\left(c = 2\right))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.advance` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233175: six-colour complementary-pair exclusion on a two-row strip*. URL: <https://oeis.org/A233175>.

*Commentary.*

A flag changes to true when its colour occurs and otherwise retains its value.

**Definition 1.5 (Scanning a word).**

$$\begin{aligned}\forall s: Seen, (\forall f: (\operatorname{Fin}\left(0\right)) \to \operatorname{Fin}\left(6\right), ((\operatorname{good}\left(s, f\right)) \iff (True)))\\\forall n: Nat, (\forall s: Seen, (\forall f: (\operatorname{Fin}\left(n + 1\right)) \to \operatorname{Fin}\left(6\right), ((\operatorname{good}\left(s, f\right)) \iff ((\operatorname{allowed}\left(s, f\left(0\right)\right)) \land (\operatorname{good}\left(\operatorname{advance}\left(s, f\left(0\right)\right), \operatorname{Fin.tail}\left(f\right)\right))))))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.good` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233175: six-colour complementary-pair exclusion on a two-row strip*. URL: <https://oeis.org/A233175>.

*Commentary.*

The empty word is accepted. A nonempty word is accepted exactly when its first colour is allowed and its tail is accepted with the updated flags.

**Definition 1.6 (Final flags of a word).**

$$\begin{aligned}\forall s: Seen, (\forall f: (\operatorname{Fin}\left(0\right)) \to \operatorname{Fin}\left(6\right), (\operatorname{finish}\left(s, f\right) = s))\\\forall n: Nat, (\forall s: Seen, (\forall f: (\operatorname{Fin}\left(n + 1\right)) \to \operatorname{Fin}\left(6\right), (\operatorname{finish}\left(s, f\right) = \operatorname{finish}\left(\operatorname{advance}\left(s, f\left(0\right)\right), \operatorname{Fin.tail}\left(f\right)\right))))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.finish` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233175: six-colour complementary-pair exclusion on a two-row strip*. URL: <https://oeis.org/A233175>.

*Commentary.*

The empty word retains its initial flags. For a nonempty word the first colour updates the flags before the tail is scanned.

**Definition 1.7 (Complementary-pair labels).**

$$\forall c: \operatorname{Fin}\left(6\right), (\operatorname{pair}\left(c\right) = [0,1,2,2,1,0]\left(c\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.pair` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233175: six-colour complementary-pair exclusion on a two-row strip*. URL: <https://oeis.org/A233175>.

*Commentary.*

The three labels have fibres {0,5}, {1,4} and {2,3}. A legal bond joins different fibres.

**Definition 1.8 (The two boundary labels).**

$$\forall c: Col, (\operatorname{pairs}\left(c\right) = (\operatorname{pair}\left(c\left(0\right)\right), \operatorname{pair}\left(c\left(1\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.pairs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233175: six-colour complementary-pair exclusion on a two-row strip*. URL: <https://oeis.org/A233175>.

*Commentary.*

Only the complementary-pair labels of the preceding column affect future bonds.

**Definition 1.9 (The literal filtered count).**

$$\forall n: Nat, (\operatorname{a}\left(n\right) = \operatorname{Finset.card}\left(\operatorname{Finset.filter}\left(\lambda A: ((\operatorname{Fin}\left(2\right)) \times (\operatorname{Fin}\left(n\right))) \to \operatorname{Fin}\left(6\right) \mapsto ((\exists j: \operatorname{Fin}\left(n\right), ((\operatorname{val}\left(j\right) = 0) \land (A\left((0, j)\right) = 0))) \land ((\forall j: \operatorname{Fin}\left(n\right), ((\operatorname{val}\left(j\right) + 1 < n) \implies (\forall r: \operatorname{Fin}\left(2\right), (\forall s: \operatorname{Fin}\left(2\right), ((A\left((r, j)\right) \neq A\left((s, \operatorname{Fin.mk}\left(\operatorname{val}\left(j\right) + 1\right))\right)) \land (\operatorname{val}\left(A\left((r, j)\right)\right) + \operatorname{val}\left(A\left((s, \operatorname{Fin.mk}\left(\operatorname{val}\left(j\right) + 1\right))\right)\right) \neq 5)))))) \land (\forall p: (\operatorname{Fin}\left(2\right)) \times (\operatorname{Fin}\left(n\right)), ((((A\left(p\right) = 2) \lor ((A\left(p\right) = 3) \lor (A\left(p\right) = 4))) \implies (\exists q: (\operatorname{Fin}\left(2\right)) \times (\operatorname{Fin}\left(n\right)), ((\operatorname{val}\left(\operatorname{proj}\left(q, 1\right)\right) \cdot n + \operatorname{val}\left(\operatorname{proj}\left(q, 2\right)\right) < \operatorname{val}\left(\operatorname{proj}\left(p, 1\right)\right) \cdot n + \operatorname{val}\left(\operatorname{proj}\left(p, 2\right)\right)) \land (A\left(q\right) = 1)))) \land ((A\left(p\right) = 3) \implies (\exists q: (\operatorname{Fin}\left(2\right)) \times (\operatorname{Fin}\left(n\right)), ((\operatorname{val}\left(\operatorname{proj}\left(q, 1\right)\right) \cdot n + \operatorname{val}\left(\operatorname{proj}\left(q, 2\right)\right) < \operatorname{val}\left(\operatorname{proj}\left(p, 1\right)\right) \cdot n + \operatorname{val}\left(\operatorname{proj}\left(p, 2\right)\right)) \land (A\left(q\right) = 2)))))))), \operatorname{Finset.univ}\left(\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.a` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233175: six-colour complementary-pair exclusion on a two-row strip*. URL: <https://oeis.org/A233175>.

*Commentary.*

The finite set contains all arrays on Fin 2 times Fin n, filtered by the displayed predicate. The rank r*n+j is the row-major order. The first-entry existential also makes a(0)=0.

**Definition 1.10 (One-column continuation).**

$$\forall w: (Seen) \to (Seen) \to (Seen) \to ((\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(3\right))) \to Int, (\forall q: Seen, (\forall t: Seen, (\forall b: Seen, (\forall p: (\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(3\right)), (\operatorname{step}\left(w, q, t, b, p\right) = \sum_{c: Col} ((\operatorname{if} ((\forall r: \operatorname{Fin}\left(2\right), ((\operatorname{pair}\left(c\left(r\right)\right) \neq \operatorname{proj}\left(p, 1\right)) \land (\operatorname{pair}\left(c\left(r\right)\right) \neq \operatorname{proj}\left(p, 2\right)))) \land ((\operatorname{allowed}\left(t, c\left(0\right)\right)) \land (\operatorname{allowed}\left(b, c\left(1\right)\right)))) \operatorname{then} w\left(q, \operatorname{advance}\left(t, c\left(0\right)\right), \operatorname{advance}\left(b, c\left(1\right)\right), \operatorname{pairs}\left(c\right)\right) \operatorname{else} 0)))))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.step` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233175: six-colour complementary-pair exclusion on a two-row strip*. URL: <https://oeis.org/A233175>.

*Commentary.*

The sum ranges over all thirty-six columns. Both new colours must avoid both preceding pair labels and satisfy their respective seen-colour flags.

**Definition 1.11 (Continuation vectors).**

$$\begin{aligned}\forall q: Seen, (\forall t: Seen, (\forall b: Seen, (\forall p: (\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(3\right)), (\operatorname{v}\left(0, q, t, b, p\right) = (\operatorname{if} (t = q) \operatorname{then} 1 \operatorname{else} 0)))))\\\forall k: Nat, (\forall q: Seen, (\forall t: Seen, (\forall b: Seen, (\forall p: (\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(3\right)), (\operatorname{v}\left(k + 1, q, t, b, p\right) = \operatorname{step}\left(\operatorname{v}\left(k\right), q, t, b, p\right))))))\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.v` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233175: six-colour complementary-pair exclusion on a two-row strip*. URL: <https://oeis.org/A233175>.

*Commentary.*

The parameter q specifies the final top-row flags. The current flags are t and b. At length zero only t=q is required. A positive continuation appends one column.

**Definition 1.12 (Closing the row-major boundary).**

$$\forall w: (Seen) \to (Seen) \to (Seen) \to ((\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(3\right))) \to Int, (\operatorname{total}\left(w\right) = \sum_{c: Col} (\sum_{q: Seen} ((\operatorname{if} ((c\left(0\right) = 0) \land (\operatorname{allowed}\left(q, c\left(1\right)\right))) \operatorname{then} w\left(q, (false, false), \operatorname{advance}\left(q, c\left(1\right)\right), \operatorname{pairs}\left(c\right)\right) \operatorname{else} 0))))$$

*Formalization.* `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.total` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233175: six-colour complementary-pair exclusion on a two-row strip*. URL: <https://oeis.org/A233175>.

*Commentary.*

The first top colour is zero. The final top flags q are also the initial bottom flags, since all top-row cells precede the bottom row. Summing over q selects the unique final top record.

**Theorem 1.13 (A finite continuation identity).**

$$(\forall q: Seen, (\forall t: Seen, (\forall b: Seen, (\forall p: (\operatorname{Fin}\left(3\right)) \times (\operatorname{Fin}\left(3\right)), (\operatorname{v}\left(7, q, t, b, p\right) = 16 \cdot \operatorname{v}\left(6, q, t, b, p\right) - 32 \cdot \operatorname{v}\left(5, q, t, b, p\right) - 320 \cdot \operatorname{v}\left(4, q, t, b, p\right) + 512 \cdot \operatorname{v}\left(3, q, t, b, p\right) + 2048 \cdot \operatorname{v}\left(2, q, t, b, p\right)))))) \land ((\operatorname{total}\left(\operatorname{v}\left(0\right)\right) = 3) \land ((\operatorname{total}\left(\operatorname{v}\left(1\right)\right) = 8) \land ((\operatorname{total}\left(\operatorname{v}\left(2\right)\right) = 80) \land ((\operatorname{total}\left(\operatorname{v}\left(3\right)\right) = 800) \land ((\operatorname{total}\left(\operatorname{v}\left(4\right)\right) = 8576) \land ((\operatorname{total}\left(\operatorname{v}\left(5\right)\right) = 92672) \land (\operatorname{total}\left(\operatorname{v}\left(6\right)\right) = 1009664)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.finite_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233175: six-colour complementary-pair exclusion on a two-row strip*. URL: <https://oeis.org/A233175>.

*Commentary.*

The seven-step identity holds on all 576 states. The listed scalar values concern continuation lengths zero through six. Linearity propagates the identity to every continuation length.

**Theorem 1.14 (Barker's generating function).**

$$\left(1 - 4 \cdot X\right) \cdot \left(1 - 8 \cdot X - 32 \cdot (X)^{2}\right) \cdot \operatorname{PowerSeries.mk}\left(\lambda n: Nat \mapsto (\operatorname{a}\left(n\right): Int)\right) = X \cdot \left(3 - 28 \cdot X - 16 \cdot (X)^{2} + 224 \cdot (X)^{3}\right) \operatorname{in} \operatorname{PowerSeries}\left(Int\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A233175: six-colour complementary-pair exclusion on a two-row strip*. URL: <https://oeis.org/A233175>.

*Commentary.*

The literal filtered count equals total(v(n-1)) at every positive width, by decomposition into the first column and its tail. The seven-step identity has polynomial z^2*(z^3-12*z^2+128)*(z^2-4*z-16). The listed initial values eliminate the extra factor for the scalar count and yield a(n)=12*a(n-1)-128*a(n-3) for n at least five. Comparing every power-series coefficient gives the identity. The cast from natural counts to integers is taken before forming the series.

## References

- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.Col`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.Seen`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.a`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.advance`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.allowed`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.finish`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.finite_certificate`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.good`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.pair`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.pairs`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.result`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.step`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.total`
- Truth anchor: `D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.v`
