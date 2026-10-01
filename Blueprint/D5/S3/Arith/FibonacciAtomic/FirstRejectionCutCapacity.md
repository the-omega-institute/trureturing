# First Rejection Across Arbitrary Window Cuts

## Abstract

Every coordinate cut has an exact first-rejection response count and an exact Boolean collapse.

Let n=k+1 for an arbitrary natural k. Coordinates are the complete windows 000,100,010,101,001, written from low to high. Inputs include every word of length n, with arbitrary seams and terminal zero windows. The initial state has both flags false, and End is queried after the last window. A is any subset of the coordinates; its complementary assignments range over all five-window words on the other coordinates.

Ordered diagnostic. T is the earliest bad seam, where the left high bit and right low bit are both one. If no seam fails, T is the terminal label n for a last window 000, and is acceptance otherwise. The Lean label is WithTop(Fin(n)): finite value i represents source label i+1, and top represents acceptance. F is the Boolean End readout of the actual run from (false,false).

Crossing and closed seams. C consists of seams with exactly one endpoint in A; J consists of seams with both endpoints in A. The number d is the cardinality of C. For j in J, c(j) counts crossing seams strictly before j. A crossing port is the left high bit when the left coordinate lies in A, and the right low bit otherwise. The value delta is one exactly when n>=2, the terminal coordinate lies in A, and its predecessor does not. The factor terminalOwned(A) is the numeric indicator of terminal ownership.

Independent permitted profiles. Extend an A assignment by middle windows outside A. Its diagnostic tau is the first A-closed seam failure or the A-owned terminal zero failure. A profile consists of an allowed cutoff and the crossing bits strictly before it. The allowed cutoffs are acceptance, each seam in J, and the terminal label when n lies in A. Only for a terminal cutoff is the incoming last crossing port fixed to zero. There are no other restrictions.

**Theorem 1.1 (All Cuts, All Positive Lengths).**

$$\begin{aligned}\forall n \ge 1, \forall A \subseteq \operatorname{coordinates}\left(n\right),\\\operatorname{capacityT}\left(A\right) = 2^{d} + \sum_{j \in J}2^{\operatorname{c}\left(j\right)} + \operatorname{terminalOwned}\left(A\right) \times2^{d - \delta}\\\delta \le d, \operatorname{project}\left(T\right) = F\\\operatorname{capacityF}\left(A\right) = 2^{d} + epsilon\\\forall n \ge 2, \operatorname{F}\left(\operatorname{x}\left(n\right)\right) = 0, \operatorname{F}\left(\operatorname{y}\left(n\right)\right) = 0\\\operatorname{T}\left(\operatorname{x}\left(n\right)\right) = 1, \operatorname{T}\left(\operatorname{y}\left(n\right)\right) = n\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/FirstRejectionCutCapacity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every permitted profile has an actual representative. At each coordinate, choose the low and high bits independently: middle, low, high, and ends encode the four possible bit pairs. Set the specified crossing bits, keep internal seams harmless before the selected cutoff, and put high followed by low at a selected internal failure. A terminal profile uses zero at the last coordinate. Its fixed incoming zero makes this compatible with the remaining prescribed bits. Representatives on opposite sides occupy disjoint coordinates and combine into one actual raw word.

Two assignments have the same diagnostic response exactly when their cutoffs and preceding crossing bits agree. A complementary assignment of middle windows exposes the cutoff. A single low or high complementary window tests a selected crossing port and has its other bit zero. It therefore distinguishes different preceding ports while creating no earlier complementary failure. The empty complement has its unique assignment and still distinguishes closed labels.

The actual response range is consequently in bijection with the independent profile family. Acceptance contributes 2^d profiles; an internal cutoff j contributes 2^c(j); the terminal cutoff contributes 2^(d-delta). The incoming restriction removes exactly one available bit when delta=1, and delta<=d.

The interval table is complete: the empty cut has capacity 1; the full cut has n+1; the proper prefix [1,m] has m+1; the terminal singleton has 3 for n>=2; a terminal suffix [l,n] with 1<l<n has 2(n-l+1)+2; and an interior interval [l,r] with 1<l<=r<n has 2(r-l+1)+2. Thus the first singleton has 2, an interior singleton has 4, and every nonprefix interval of length at least two has 2m+2. At n=1 the empty and full cuts have 1 and 2. There is no length-zero coordinate domain here.

Projection sends acceptance to true and every finite label to false, and equals the actual Boolean End readout. Every assignment with a finite closed cutoff has the same zero Boolean response. Assignments with an acceptance cutoff have nonzero responses and remain distinguishable exactly by their full crossing profiles. The extra zero response exists precisely when A owns the terminal coordinate or has an internal seam. Writing epsilon for that condition gives Boolean capacity 2^d+epsilon.

For every n>=2, the words x=(001,100,010^(n-2)) and y=(010^(n-1),000) both have Boolean output false. Their diagnostic outputs are the first seam label 1 and the terminal label n, respectively. Hence no function of the Boolean output alone reconstructs the diagnostic on all raw inputs. This does not restrict computation from the full raw word.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/FirstRejectionCutCapacity.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/LiteralWindowEnd](LiteralWindowEnd.md)
- Dependency: [D5/S3/ConceptDynamics/Communication/LanguagePostprocessingObstruction](../../ConceptDynamics/Communication/LanguagePostprocessingObstruction.md)
- Dependency: [D5/S3/Observer/Separation/SurjectiveColumnSharpWidth](../../Observer/Separation/SurjectiveColumnSharpWidth.md)
