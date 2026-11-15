# Repetition words with a regular incoming relation

## Abstract

Literal repetition-word counts for loopless relations of constant indegree.

The alphabet is Fin q and a word of length n is a function from Fin n to Fin q. Equality events are adjacent equal pairs, in position order, including overlapping pairs. The word is linear; neither rotations nor changes of alphabet labels are identified. The relation constrains successive event labels. The alphabet sizes q ≥ 2 in Ma and Zhang's Barker and Hardin's cyclic-repetition formulas and an extension of Fried's enumeration are included; the statement also permits the empty and one-letter alphabets whenever its hypotheses hold.

**Definition 1.1 (Ordered equality-event labels).**

$$\forall q \in \mathbb{N},\; \forall w \in \operatorname{List}\left(\operatorname{Fin}\left(q\right)\right),\; \operatorname{eventLabels}\left(w\right) = \operatorname{List.map}\left(\operatorname{Prod.snd}, \operatorname{List.filter}\left(\lambda (p: \operatorname{Fin}\left(q\right)\times\operatorname{Fin}\left(q\right)) \mapsto \operatorname{Prod.fst}\left(p\right) = \operatorname{Prod.snd}\left(p\right), \operatorname{List.zip}\left(w, \operatorname{List.tail}\left(w\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Patterns/BarkerRegularRelationCounting.eventLabels` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker (2019). *OEIS A268943: cyclic successive equality events*. URL: <https://oeis.org/A268943>.

*Commentary.*

Zip the word with its tail, retain equal pairs, and read their second coordinates. Thus a triple equal letter contributes two events. This is the same extraction as in the eight-letter cyclic model, with a variable alphabet size.

**Definition 1.2 (Admissible literal words).**

$$\forall q \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall R \in \operatorname{Fin}\left(q\right) \to \operatorname{Fin}\left(q\right) \to Prop,\; \forall w \in \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(q\right),\; \operatorname{Admissible}\left(R, w\right) = \operatorname{List.IsChain}\left(R, \operatorname{eventLabels}\left(\operatorname{List.ofFn}\left(w\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Patterns/BarkerRegularRelationCounting.Admissible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker (2019). *OEIS A268943: cyclic successive equality events*. URL: <https://oeis.org/A268943>.

*Commentary.*

An empty or singleton event list is admissible. Longer lists require R between each pair of consecutive event labels. In particular, looplessness forbids two consecutive events of the same label, including the overlap in a triple letter.

**Definition 1.3 (Actual word cardinalities).**

$$\forall q \in \mathbb{N},\; \forall R \in \operatorname{Fin}\left(q\right) \to \operatorname{Fin}\left(q\right) \to Prop,\; \forall n \in \mathbb{N},\; \operatorname{count}\left(R, n\right) = \operatorname{Nat.card}\left(\{w: \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(q\right) \mid \operatorname{Admissible}\left(R, w\right)\}\right)$$

*Formalization.* `D5/S1/Words/Patterns/BarkerRegularRelationCounting.count` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker (2019). *OEIS A268943: cyclic successive equality events*. URL: <https://oeis.org/A268943>.

*Commentary.*

The carrier is the subtype of actual words satisfying the event relation. No recurrence is used to define this cardinality.

**Definition 1.4 (Positive-index coefficient series).**

$$\forall q \in \mathbb{N},\; \forall R \in \operatorname{Fin}\left(q\right) \to \operatorname{Fin}\left(q\right) \to Prop,\; \operatorname{sourceSeries}\left(R\right) = \operatorname{PowerSeries.mk}\left(\lambda (n: \mathbb{N}) \mapsto \operatorname{if}\left(n = 0, 0, (\operatorname{count}\left(R, n\right): \mathbb{Q})\right)\right)$$

*Formalization.* `D5/S1/Words/Patterns/BarkerRegularRelationCounting.sourceSeries` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker (2019). *OEIS A268943: cyclic successive equality events*. URL: <https://oeis.org/A268943>.

*Commentary.*

The coefficient at zero is zero. Every positive coefficient is the actual cardinality cast to the rationals. The unique empty word is counted separately by count R 0 = 1.

**Theorem 1.5 (The regular-relation enumeration).**

$$\forall q \in \mathbb{N},\; \forall d \in \mathbb{N},\; \forall R \in \operatorname{Fin}\left(q\right) \to \operatorname{Fin}\left(q\right) \to Prop,\; \left(\forall a \in \operatorname{Fin}\left(q\right),\; \neg R\left(a, a\right)\right) \Rightarrow \left(\left(\forall r \in \operatorname{Fin}\left(q\right),\; \operatorname{Nat.card}\left(\{b: \operatorname{Fin}\left(q\right) \mid R\left(b, r\right)\}\right) = d\right) \Rightarrow \left((((\operatorname{count}\left(R, 0\right) = 1) \land (((\operatorname{count}\left(R, 1\right): \mathbb{Q}) = q) \land (((\operatorname{count}\left(R, 2\right): \mathbb{Q}) = q^{2}) \land ((\operatorname{count}\left(R, 3\right): \mathbb{Q}) = q^{3} - q))))) \land ((\operatorname{sourceSeries}\left(R\right) = \operatorname{PowerSeries.C}\left((q: \mathbb{Q})\right) \cdot \operatorname{PowerSeries.X} \cdot (1 - \operatorname{PowerSeries.C}\left((q - 3: \mathbb{Q})\right) \cdot \operatorname{PowerSeries.X} - \operatorname{PowerSeries.C}\left((q + d - 2: \mathbb{Q})\right) \cdot \operatorname{PowerSeries.X}^{2}) \cdot ((1 - \operatorname{PowerSeries.C}\left((q - 1: \mathbb{Q})\right) \cdot \operatorname{PowerSeries.X}) \cdot (1 - \operatorname{PowerSeries.C}\left((q - 2: \mathbb{Q})\right) \cdot \operatorname{PowerSeries.X} - \operatorname{PowerSeries.C}\left((q + d - 1: \mathbb{Q})\right) \cdot \operatorname{PowerSeries.X}^{2}))^{-1}) \land (\forall n \in \mathbb{N},\; (\operatorname{count}\left(R, n + 4\right): \mathbb{Q}) = \left(2 \cdot q - 3\right) \cdot (\operatorname{count}\left(R, n + 3\right): \mathbb{Q}) + \left(-q^{2} + 4 \cdot q + d - 3\right) \cdot (\operatorname{count}\left(R, n + 2\right): \mathbb{Q}) - \left(q - 1\right) \cdot \left(q + d - 1\right) \cdot (\operatorname{count}\left(R, n + 1\right): \mathbb{Q})))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/BarkerRegularRelationCounting.relation_enumeration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker (2019). *OEIS A268943: cyclic successive equality events*. URL: <https://oeis.org/A268943>.

*Commentary.*

Partition nonempty admissible words into U with no events, A whose first letter b is related to the first event r, and B containing the other eventful words. The initial vector is (q,0,0). For each fixed suffix, prepending every possible letter gives (U,A,B) ↦ ((q−1)U,(d−1)A+dB,U+(q−d+1)A+(q−d−1)B). Exactly d letters precede r under R. The equal-letter choice is removed from the A fiber when R(b,r) holds; duplicating b then enters B because R(b,b) fails. Removing the first letter recovers the unique suffix and deletes at most its first event. Fin.consEquiv therefore converts these exhaustive fibers to the literal cardinality sums. The coefficients are rational: d−1 is signed. When d=0, A is empty, and the same identities remain valid. Coefficientwise series equations and elimination yield the displayed unit-denominator formula. Both denominator factors have constant coefficient one. Eliminating the state counts also gives the displayed recurrence, which begins at positive length.

Only q and d occur in the answer, so two loopless relations on the same alphabet with the same indegree have equal counts at every length. For d=1, take R(a,b) to mean b=σ(a), where σ is any fixed-point-free permutation. Every b has its unique predecessor σ⁻¹(b). The cyclic successor σ(a)=a+1 modulo q is one such permutation for q≥2. Its recurrence is a(n+3)=(2q−3)a(n+2)+(−q²+4q−2)a(n+1)−q(q−1)a(n) for n≥0; the n=0 case follows from 1,q,q²,q³−q. The positive series is qx(1−(q−3)x−(q−1)x²)/((1−(q−1)x)(1−(q−2)x−qx²)). The existing eight-letter cyclic theorem supplies its unique series and positive-index radical expression directly.

For R(a,b) meaning a≠b, the indegree is q−1. Conversely a loopless relation of that indegree contains every unequal pair. This is Fried's unequal-event enumeration: arXiv:2410.07237v3, Theorem 10, equation (18), and Journal of Integer Sequences 28, Article 25.4.3, Section 3.2, Theorem 4 and Corollary 5. Its displayed rational function is the full series 1+S, with constant coefficient one, although the described sequence starts at positive index. Here 1+S=(1−(q−3)x−2(q−2)x²−(q−2)x³)/(1−(2q−3)x+(q−1)(q−4)x²+2(q−1)²x³). The homogeneous recurrence b(n+3)=(2q−3)b(n+2)+(−q²+5q−4)b(n+1)−2(q−1)²b(n) has onset n≥1; b(0)=1 does not extend that onset. The cyclic and unequal rules agree on a binary alphabet. For q≥3, the word (0,0,2,2) separates them. Other interpretations of the linked sequences are not implied.

## References

- Truth anchor: `D5/S1/Words/Patterns/BarkerRegularRelationCounting.Admissible`
- Truth anchor: `D5/S1/Words/Patterns/BarkerRegularRelationCounting.count`
- Truth anchor: `D5/S1/Words/Patterns/BarkerRegularRelationCounting.eventLabels`
- Truth anchor: `D5/S1/Words/Patterns/BarkerRegularRelationCounting.relation_enumeration`
- Truth anchor: `D5/S1/Words/Patterns/BarkerRegularRelationCounting.sourceSeries`
- Dependency: [D5/S1/Words/Patterns/BarkerCyclicRepetitionCounting](BarkerCyclicRepetitionCounting.md)
