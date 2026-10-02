# Neutral Gaps and Exact Histogram Counts of Legal Fibonacci Window Words

## Abstract

Neutral input positions give a unique legal gap code and exact five-window histogram counts.

Use the literal windows X=100, Y=001, Z=101, U=000 and V=010, with bits written low to high. A word is a finite list of these windows. Legal(w) means legal(false,flatten(w)): the incoming seam is zero and there are no adjacent occupied bits. The first window has no extra restriction. U and V each occupy one input position, including when neighboring gaps are empty. End acceptance is a separate condition. The existing triple(false,d,false) constructs U for false and V for true.

**Definition 1.1 (Gaps without neutral letters).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.Free`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.Free` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Free(g) means that every window in g differs from U and V. Thus g uses only X, Y and Z; the empty gap is allowed.

**Definition 1.2 (Gap exponents).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.Gap`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.Gap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A Gap is a triple (x,z,y), where x and y are arbitrary natural numbers and z is Boolean. The Boolean central exponent is zero or one.

**Definition 1.3 (The canonical gap word).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.gap`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.gap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

GapWord(x,z,y)=X^x Z^[z] Y^y, where [false]=0 and [true]=1. The powers denote literal repeated input windows.

**Definition 1.4 (An ordered decomposition).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.Cuts`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.Cuts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Cuts consists of a first gap g0 and a finite ordered list of pairs (di,gi), with di Boolean and gi a gap word.

**Definition 1.5 (Reconstructing a word).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.join`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.join` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Join(g0,[(d1,g1),...,(dt,gt)]) is g0 triple(false,d1,false) g1 ... triple(false,dt,false) gt.

**Definition 1.6 (All gaps, including empty gaps).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.gaps`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.gaps` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Gaps(p) is the ordered list [g0,g1,...,gt]. It always contains the first gap, even when the input word is empty.

**Definition 1.7 (The gap alphabet condition).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.Clean`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.Clean` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Clean(p) means Free(g) for every g in Gaps(p). Neutral letters occur only at the designated separators.

**Definition 1.8 (Splitting at actual neutral positions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.split`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.split` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Split(w) retains the first gap and every neutral letter together with the following gap. Leading, trailing and consecutive neutral letters retain their corresponding empty gaps.

**Definition 1.9 (Canonical legal-word codes).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.Code`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.Code` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A Code consists of a Gap and an ordered list of Boolean/Gap pairs. Every Boolean specifies one actual U or V input position.

**Definition 1.10 (Expanding gap exponents).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.codeCuts`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.codeCuts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

CodeCuts replaces each Gap in a Code by its canonical gap word.

**Definition 1.11 (Reconstructing the literal word).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.codeWord`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.codeWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

CodeWord(p)=Join(CodeCuts(p)).

**Definition 1.12 (Reading gap exponents).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.readGap`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.readGap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ReadGap reads the X count, whether the Z count is one, and the Y count.

**Definition 1.13 (Reading a canonical code).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.readCode`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.readCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ReadCode reads every gap and retains all ordered neutral letters.

**Definition 1.14 (The final gap).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.terminalGap`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.terminalGap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

TerminalGap(p) selects the final gap, including an empty final gap.

**Definition 1.15 (Counts recovered from gap exponents).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.inventory`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.inventory` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Inventory(p) assigns the sums of the X and Y gap exponents, the number of gaps carrying Z, and the counts of false/true neutral Booleans.

**Definition 1.16 (An exact literal-word histogram fiber).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.HistogramWords`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.HistogramWords` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any function h from Window to natural numbers, HistogramWords(h) contains exactly the legal literal words with count(f,w)=h(f) for every f.

**Definition 1.17 (The corresponding canonical-code fiber).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.HistogramCodes`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.HistogramCodes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

HistogramCodes(h) contains the Codes whose Inventory is h.

**Definition 1.18 (Exact last-window fibers).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.EndpointWords`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.EndpointWords` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

EndpointWords(h,f) retains precisely the literal words in HistogramWords(h) whose last window is f. The empty word belongs to none of these fibers.

**Definition 1.19 (Positive F labels in a terminal fiber).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.PositiveEndpointWords`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.PositiveEndpointWords` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PositiveEndpointWords(h,f) further requires End acceptance from zero initial seam and flag, using the existing run and endable definitions.

**Definition 1.20 (Indexed neutral and gap assignments).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.rawCode`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.rawCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For t indexed neutral Booleans and t+1 indexed Gaps, RawCode retains gap 0 and then each neutral Boolean together with its successor gap.

**Definition 1.21 (Five prescribed multiplicities).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.histogram`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.histogram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Histogram(a,b,c,r,s) assigns a to X, b to Y, c to Z, r to U and s to V.

**Definition 1.22 (Independent subset and weak-composition factors).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.Factors`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.Factors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

With t=r+s, Factors(a,b,c,r,s) consists of an r-element subset of Fin(t), a c-element subset of Fin(t+1), and the existing ArrowWilfGapData.Gaps weak compositions of a and b into t+1 ordered slots.

**Definition 1.23 (Reconstructing indexed assignments).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.factorRaw`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.factorRaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The first subset specifies U positions, its complement V positions; the second subset specifies Z-bearing gaps, and the two weak compositions specify the X and Y exponents of every gap.

**Theorem 1.24 (Unique decomposition, histogram counts and terminal labels).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Y. Zhuang (2015). *A generalized Goulden–Jackson cluster method and lattice path enumeration*. URL: <https://arxiv.org/abs/1508.02793>.

*Acknowledgement.* E. Kupin; D. Yuster (2008). *Generalizations of the Goulden–Jackson Cluster Method*. URL: <https://arxiv.org/abs/0810.5113>.

*Commentary.*

The assertions hold jointly. For every finite window word w there exists exactly one p in Cuts with Clean(p) and Join(p)=w. For every w, the number of separator-gap pairs in Split(w) is count(U,w)+count(V,w). For every w, Legal(w) holds if and only if, for every gap g in Gaps(Split(w)), there exists exactly one Gap q with GapWord(q)=g. For every w, Legal(w) holds if and only if there is exactly one Code p with CodeWord(p)=w. For every Code p, its word ends in X precisely when its final gap has x>0, z=false and y=0; it ends in Z precisely when its final gap has z=true and y=0. For every p and f, count(f,CodeWord(p))=Inventory(p)(f). For every histogram h there is a bijection from HistogramCodes(h) to HistogramWords(h) sending p to CodeWord(p). For all natural a,b,c,r,s and t=r+s, there is also a bijection from Factors(a,b,c,r,s) to HistogramWords(Histogram(a,b,c,r,s)), whose word is CodeWord(RawCode(FactorRaw(p))). This word fiber is finite and its exact cardinality is binom(t,r) binom(t+1,c) multichoose(t+1,a) multichoose(t+1,b). The standard multichoose counts ordered weak compositions; for these positive slot counts it equals binom(a+t,t) and binom(b+t,t), respectively. Write H for this histogram cardinality and N_f for its exact terminal-fiber cardinality. N_U is zero if r=0 and otherwise H(a,b,c,r-1,s); N_V is zero if s=0 and otherwise H(a,b,c,r,s-1); N_Y is zero if b=0 and otherwise H(a,b-1,c,r,s). N_X is zero if a=0 and otherwise binom(t,r) binom(t,c) multichoose(t+1,a-1) multichoose(t,b). N_Z is zero if c=0 and otherwise binom(t,r) binom(t,c-1) multichoose(t+1,a) multichoose(t,b). These guards implement the convention that a negative histogram parameter gives zero. The zero-slot multichoose is one at multiplicity zero and zero at every positive multiplicity. Thus at t=0, N_U=N_V=0, N_X is the indicator of a>0 and b=c=0, N_Y is the indicator of b>0 and c in {0,1}, and N_Z is the indicator of c=1 and b=0. For nonzero total multiplicity, the five terminal-fiber cardinalities sum to the histogram cardinality. The zero histogram has cardinality one and its only word is empty. Every fiber ending in a letter with zero multiplicity is empty, and every histogram with c>t+1 is empty. For every h and f, the positive F fiber has cardinality zero when f=U, and otherwise has the full terminal-fiber cardinality. All natural exponents, empty words, empty gaps and words with no neutral letters are included.

Each neutral letter removes both possible seam obstructions. Inside a gap the forbidden adjacent pairs are YX, YZ, ZX and ZZ. After Y or Z, every remaining letter must be Y; before them, every letter is X. Hence a legal gap has the displayed shape. Counts of X, Z and Y recover its three exponents. Recursive splitting and joining are inverse when the gap alphabet condition holds. Reading the exponents and rebuilding are inverse on all legal words. Since neutral letters differ from X and Z, these endpoints require a nonempty final gap of the stated form.

Index the neutral positions by Fin(t) and the gaps by Fin(t+1). Their U positions and Z-bearing gaps are independent subsets of the prescribed sizes. The X and Y exponents independently form the existing ordered weak-composition data. Reading and reconstruction give both directions of the literal-word bijection. Apply the pinned subset and weak-composition cardinalities directly. The endpoint sum uses the standard partition by the last window, and the F labels use the public execution theorem and the standard last-item decomposition. Appending U, V or Y preserves legality because its first bit is zero. Removing that last window and appending it again are inverse, including for an empty prefix, and give the three guarded H formulas. For a terminal X, the last Z slot is absent, the last Y part is zero, and the last X part is positive. For a terminal Z, the last Z slot is present and the last Y part is zero. The reversible factor encoding restricts to each of these exact fibers. Erasing the last available slot gives the Y weak composition over t slots. Subtract one from the positive last X part by the existing positive-gap equivalence; count the Z subsets by the standard powerset-cardinality formulas. These operations retain all remaining independent factors and yield the X and Z formulas.

The six closed forms are applications of the published generalized Goulden-Jackson cluster method: Zhuang, arXiv:1508.02793v3, §2 Theorem 1, and Kupin-Yuster, arXiv:0810.5113, §4 (7) and §7.2. Those sources provide the general constrained-word enumeration framework; the new content here is only the kernel-verified correspondence between actual legal words, marked neutral cuts, and factor data. The Bool-marked Cuts inverse and cleanliness obligations use the pinned fold interfaces and the finite window equations.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.Clean`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.Code`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.Cuts`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.EndpointWords`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.Factors`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.Free`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.Gap`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.HistogramCodes`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.HistogramWords`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.PositiveEndpointWords`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.codeCuts`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.codeWord`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.factorRaw`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.gap`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.gaps`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.histogram`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.inventory`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.join`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.rawCode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.readCode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.readGap`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.split`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/WindowHistogramLegalCount.terminalGap`
- Dependency: [D5/S3/Arith/FibonacciAtomic/LiteralWindowEnd](LiteralWindowEnd.md)
- Dependency: [D5/S3/Combinatorics/ArrowWilfGapData](../../Combinatorics/ArrowWilfGapData.md)
