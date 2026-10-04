# Run Starts in a Closed Boolean Word

## Abstract

Identify literal forbidden blocks with the bounded-run scanner and run-start count.

A word has n Boolean coordinates. TrueBlock(w,s,k) requires s+k at most n and every coordinate in [s,s+k) to be true. RunStart adds a false predecessor at s-1 when s is positive; at zero it adds no predecessor. The count sums these start indicators over exactly n-k+1 positions.

**Theorem 1.1 (Scanner, forbidden blocks, and zero run starts).**

$$\forall n,k\in\mathbb{N}, 0<k\le n\implies \forall w: Fin(n)\to Bool, (\operatorname{DBonacciAdmissible}(k,n,w)\iff\forall s\in\mathbb{N},\neg\operatorname{TrueBlock}(w,s,k)) \land ((\forall s\in\mathbb{N},\neg\operatorname{TrueBlock}(w,s,k))\iff\operatorname{startCount}(k,w)=0)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/ClosedRunStarts.closed_word_run_start_equivalence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on the word length tracks the scanner's remaining true-bit budget together with all full forbidden windows. For the start count, the earliest forbidden block either starts at zero or has a false predecessor: a true predecessor would produce an earlier block. The argument includes a block ending at the final coordinate and the boundary case n=k.

## References

- Truth anchor: `D5/S1/Words/ClosedRunStarts.closed_word_run_start_equivalence`
- Dependency: [D5/S0/Tower/DBonacci/Names](../../S0/Tower/DBonacci/Names.md)
