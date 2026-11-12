# Recurrence and Tail Periods of the Literal Rich Words

## Abstract

Uniform recurrence and absence of every positive eventual tail period for the actual seven-letter source and its literal four-letter image.

The source u is RichWordTypeIOccurrence.word on Fin 7, the fixed point of the literal substitution i -> 0(i+1) for i < 6 and 6 -> 066. The output x is RichWordOutputDecoder.x on Fin 4 with dictionary (a,ab,abb,ac,acc,accdcc,accdccddccdcc). The notation factor(y,i,n) denotes the length-n window beginning at i. All positions are natural numbers, including zero; empty windows and overlapping occurrences are included.

**Theorem 1.1 (All source factors recur uniformly).**

$$\forall i \in \mathbb{N},\; \forall n \in \mathbb{N},\; \exists B \in \mathbb{N},\; \forall q \in \mathbb{N},\; \exists j \in \mathbb{N},\; q \le j \land \left(j + n \le q + B \land \operatorname{factor}\left(\operatorname{u}, j, n\right) = \operatorname{factor}\left(\operatorname{u}, i, n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/RichWordRecurrence.source_uniform_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each source window there is one bound B that works for every starting position q. The repeated window lies wholly inside [q,q+B). An iterate prefix containing the given factor is a prefix of every source block one level deeper, because every substitution image begins with zero. The actual iterated cuts partition the source, and each block at depth k has length at most 3^k. Taking the next cut supplies the uniform window bound.

**Theorem 1.2 (The source has no eventual positive period).**

$$\neg \operatorname{EventuallyPeriodicWord}\left(\operatorname{u}\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/RichWordRecurrence.source_no_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

EventuallyPeriodicWord(y) means that there exist natural numbers s and p with p > 0 and y(s+t+p)=y(s+t) for every natural t. Type-I factors have unbounded lengths and two distinct actual right extensions, phase(n) and 6. Uniform recurrence places both extended factors beyond any proposed preperiod. In a tail of period p, equality of a factor of length at least p forces equality of its following letter, contradicting those two extensions.

**Theorem 1.3 (All output factors recur uniformly).**

$$\forall i \in \mathbb{N},\; \forall n \in \mathbb{N},\; \exists B \in \mathbb{N},\; \forall q \in \mathbb{N},\; \exists j \in \mathbb{N},\; q \le j \land \left(j + n \le q + B \land \operatorname{factor}\left(\operatorname{x}, j, n\right) = \operatorname{factor}\left(\operatorname{x}, i, n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/RichWordRecurrence.output_uniform_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The bound applies to arbitrary output windows, including windows crossing image boundaries. Enclose the window in the image of a finite source block and retain its offset from that block's first marker. Source recurrence repeats the whole block. Every code word has length between 1 and 13, so bounded source gaps give bounded output gaps. Repeating the same offset reproduces the original output factor.

**Theorem 1.4 (The literal output has no eventual positive period).**

$$\neg \operatorname{EventuallyPeriodicWord}\left(\operatorname{x}\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/RichWordRecurrence.output_no_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact marker inverse identifies every output marker with one source boundary. Translating a sufficiently late marker by a proposed output period sends consecutive markers to consecutive markers: an intervening marker would translate back to an intervening original boundary. Thus translation induces a fixed positive displacement of source indices. The marked-core reconstruction identifies each translated source letter, giving a positive eventual source period and a contradiction.

These results concern recurrence and eventual periods of these precise words. The ordinary critical exponent, the full bispecial classification, richness, scalar spectral inequalities, and remaining parent clauses require their separate arguments.

## References

- Truth anchor: `D5/S1/Words/RichWordRecurrence.output_no_tail`
- Truth anchor: `D5/S1/Words/RichWordRecurrence.output_uniform_recurrence`
- Truth anchor: `D5/S1/Words/RichWordRecurrence.source_no_tail`
- Truth anchor: `D5/S1/Words/RichWordRecurrence.source_uniform_recurrence`
- Dependency: [D5/S1/Words/Complexity/MorseHedlund](Complexity/MorseHedlund.md)
- Dependency: [D5/S1/Words/RichWordOutputDecoder](RichWordOutputDecoder.md)
