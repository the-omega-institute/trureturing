# Paired completion from actual occurrence counts

## Abstract

One extra actual negative LARGE occurrence permits paired completion of exceptional positive steps.

**Theorem 1.1 (Paired completion from actual occurrence counts).**

Lean statement: `D5/S3/Combinatorics/Circle/CountSurplusOrdering.exists_order_between`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/CountSurplusOrdering.exists_order_between` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any label type, integer weights f, Bool predicate E and finite list labels, let Q>=2 and C=2Q-1. The start b and endpoint e lie in [0,C], with b+sum(labels.map(f))=e. Every marked occurrence has 0<f<=Q-1. Every unmarked positive is compatible with every negative: f(p)-f(n)<=C. If a marked occurrence remains, require countP(E)+1<=countP(f<=-Q). No distinctness, magnitude bound on the negative steps, or bound on unmarked positives is assumed. The conclusion constructs a permutation of ALL labels lying in the strip from b to e. Repetitions are counted with multiplicity.

The new content is a count-sensitive paired induction. If no occurrence fits, a negative LARGE exists. Any positive outside E and that negative cannot both fail, by compatibility. Hence all positive mass belongs to E. Let s=countP(E)>0. A failed marked positive gives b>=Q+1; each of the at least s+1 negative LARGE steps must then have magnitude at least b+1. Thus e<=b+s*(Q-1)-(s+1)*(b+1)=s*(Q-b-2)-1<0, a contradiction. This is a symbolic inequality for arbitrary lists, not a finite certified instance.

Choose a fitting actual occurrence. A fitting negative LARGE is immediately followed by an actual marked positive: its landing is in [0,Q-1], and the pair lands at most 2Q-2<C. Erasing both occurrences reduces each count by exactly one. Any other fitting step is consumed singly, preserving or improving the surplus. Exact permutation and endpoint mass survive. When E is empty, reuse SmallStepOrdering.exists_order_between directly. SourceWidth.inStrip_prefix yields every natural take, including empty and overlength takes.

The full physical consumer is NegativeSuffixCountExchange.actualSource_negativeSuffix_count_exchange_full. It derives both counts from actual source filters and retains every old SMALL. This general theorem introduces no favorable-path, omitted-label or source-resource availability claim and has no literature novelty claim. Its declarations are symbolic mathematical content, with utility none; the finite enumeration and certified-instance categories do not apply.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/CountSurplusOrdering.exists_order_between`
- Dependency: [D5/S3/Combinatorics/Circle/SmallStepOrdering](SmallStepOrdering.md)
