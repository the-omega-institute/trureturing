# Actual minimum-cut conditional kernels

## 1. Carrier and conditioning

Let $U_n$ be the actual permutations of $\operatorname{Fin}(n)$ avoiding
the literal patterns $2413$ and $3142$. The empty permutation belongs to
$U_0$. Write $s_n=|U_n|$. A cut of sign $\varepsilon$ is direct when
$\varepsilon=0$ and skew when $\varepsilon=1$. Let $J_m^\varepsilon$
be the actual avoiders with no proper cut of that sign. For positive
$m,k$, let $V_{m,k}^\varepsilon$ be the subset of $U_{m+k}$ whose
minimum proper cut of that sign is $m$.

**Theorem 1.1 (actual minimum-cut Cartesian kernel).** For every sign and
every positive $m,k$, actual block sum is a bijection
$$
J_m^\varepsilon\times U_k\longrightarrow V_{m,k}^\varepsilon.
$$
For arbitrary shape predicates $A$ on $J_m^\varepsilon$ and $B$ on
$U_k$, its image event has cardinality $|A||B|$. Under the uniform law
on the actual full $U_{m+k}$, its probability is $|A||B|/s_{m+k}$.
Conditional on this minimum-cut fiber, the joint shape probability is
$$
\frac{|A||B|}{|J_m^\varepsilon|s_k}
=\frac{|A|}{|J_m^\varepsilon|}\frac{|B|}{s_k}.
$$
Ratios with zero denominator use the field convention zero; conditioning
as a probability law requires the fiber to be nonempty. A specified
left shape consequently contributes $s_k/s_{m+k}$ before sign
conditioning, and a specified right shape contributes
$|J_m^\varepsilon|/s_{m+k}$. The right numerator is not $s_m$.

*Proof.* The frozen fixed-cut factorization supplies the unique two
actual avoiding factors. For every $0<r<m$, a same-sign cut at $r$
of the block sum is equivalent to a cut at $r$ of the left factor.
The forward implication restricts comparisons to the left positions.
For the reverse implication a right position either lies in the left
factor, where its comparisons are given, or in the right factor, where
the block-sum crossing comparison applies. Thus minimality is exactly
left indecomposability. Restricting the bijection to $A\times B$ gives
the cardinality and uniform-law formulas. No recursively substituted
permutation carrier is used. $\square$

## 2. Literal labels

With zero-based indexing and $\alpha\in J_m^\varepsilon$, $\beta\in U_k$,
the actual block sum satisfies
$$
\begin{aligned}
\pi(i)&=(\varepsilon?k:0)+\alpha(i) &&(i<m),\\
\pi(m+j)&=(\varepsilon?0:m)+\beta(j) &&(j<k).
\end{aligned}
$$
An active interval with low offset $v$ adds $v$ to these values. A
left-finite direct transition emits $v+\alpha(i)$ and consumes $m$
low values. A left-finite skew transition emits $v+k+\alpha(i)$ and
consumes no low values. A right-finite skew transition discards $k$
low values; a right-finite direct transition discards high values and
does not change $v$. Right factors are pending suffixes, not emitted
prefix positions. Keeping these distinct is necessary for absolute
fixedpoint cylinders, rather than standardized block tests.

## 3. Scope of the count kernel

The minimum convention is different from the compiled, unfrozen greatest-cut
enumeration. For the identity of length four the minimum direct cut is
one and the greatest direct cut is three. The kernel above conditions
on an actual minimum-cut event and must not be obtained by identifying
those two random variables.

All-length asymptotics require the precise actual-count input
$s_{n-r}/s_n\to\rho^r$ for every fixed positive $r$, together with
the actual sign and indecomposable counts. Finite-history iteration
also needs the conditional laws of the remaining actual factor and
literal coordinate transport through both endpoint choices. Neither
the existence of this one-step kernel nor a generic measure theorem
establishes the fixed-cylinder limit, occupation estimate, hitting
transfer, or the full derangement-ratio limit.

## Sources

- Ross G. Pinsky, *The Infinite Limit of Separable Permutations*,
  arXiv:1911.05565v2, Section 3: actual minimum-cut decomposition.
- Fu, Lin, and Zeng, arXiv:1507.05184v2, Proposition 2.1 and Theorem 2.3:
  actual block sums and the distinct greatest-cut convention.

<!-- APPEND -->

## 4. Actual endpoint histories and finite-alphabet cylinders

Use source states $U$ and $J^\varepsilon$. At length at least two,
$J^\varepsilon$ is exactly the class admitting the opposite proper-cut
sign; at lengths zero and one it retains the genuine small-class
convention. An endpoint history has a terminal actual source class and
successive specified finite actual shapes. An emitted left shape belongs
to $J^\varepsilon$, with its remaining child in $U$. A removed right shape
belongs to $U$, with its remaining child in $J^\varepsilon$. The parent
is $U$ or $J^{1-\varepsilon}$, never $J^\varepsilon$. Both factors at
every continued step have positive length. These are descriptions of
events in actual permutations, not replacement permutation types.

**Theorem 4.1 (actual history count and literal cylinder transport).**
Every such finite history reconstructs an injective family of actual
avoiders indexed by its terminal actual source class. Its specified
cuts are the actual minimum cuts and every reconstructed parent belongs
to its indicated source class. Its event cardinality is exactly the
terminal actual-class cardinality. Its probability conditional on its
initial source class is the product, along the history, of the ratios
of child-class to parent-class cardinalities. A left step resets the
child to $U$; a right step conditions it to $J^\varepsilon$.

Record values $0,\ldots,B-1$ literally and all other values as a star.
If the terminal length exceeds $B$, the emitted prefix has the same
finite-alphabet word for every terminal actual shape. This word is
computed by emitting $v+\alpha(i)$ at direct left steps, stars at skew
left steps, and increasing the low offset by the right length exactly
at skew right steps. Direct left steps also increase the low offset
by the left length. Every pending right suffix stays after the
terminal active interval. Consequently any fixed-coordinate cylinder
on at most the emitted positions selects either the whole history
event or none of it, with its exact actual uniform probability.

*Proof.* At a left step, specialize the actual minimum-cut Cartesian
kernel to its specified left shape; at a right step specialize it to
its specified right shape. The surviving factor maps are injective.
Opposite cut signs cannot coexist, since comparison of the first and
last entries would require two opposite strict inequalities. Induction
therefore proves source membership, the actual minimum-cut certificates,
and injectivity of reconstruction. The terminal actual class is in
bijection with the resulting full actual-permutation event. The ratios
telescope, since each source class is nonempty: an identity or reversal
gives a concrete witness for each $J$ class, including small lengths.

For coordinate transport split each actual value list at the cut. A
left step contributes its entire first block and then the child prefix.
A right step contributes only the child prefix: the pending suffix is
after a child interval at least as long as the terminal interval.
The literal block-sum equations give precisely the stated low-offset
updates. At a skew left step every high label is at least the remaining
child length, which is no smaller than the terminal length and is
therefore outside the finite alphabet. Induction gives the same literal
prefix for every terminal shape. Restricting a cylinder to this constant
word proves the last assertion. $\square$

This theorem supplies exact finite-history products and a literal
finite-alphabet transport, not their limiting products or a probability
law on infinite histories. Exhaustive capped-history partitioning,
truncation error bounds, all-length count asymptotics, the coupled law,
and occupied/hitting instantiations remain separate obligations.

## 5. Deterministic capped exploration of the actual carrier

Fix natural numbers $m,B,H,K$. The active object is an actual member of
$U_n$ or $J_n^t$, not a randomly generated replacement. First stop when
at least $m$ positions have been emitted. Label this stop good exactly
when the remaining length exceeds $B$, and short otherwise. If the
target is not reached, stop small when the active length is below two,
and stop exhausted when no transitions remain. Otherwise recover the
unique proper-cut sign, its minimum positive cut, and its unique actual
left and right factors. Emit the left factor if its length is at most
$K$. If that test fails, remove the right factor when its length is at
most $K$, recording it as a pending suffix. If both tests fail, stop
with cap failure. A left emission resets the child to $U$; a right
removal leaves the child in $J^\varepsilon$. The parent belongs to $U$
or $J^{1-\varepsilon}$, never $J^\varepsilon$.

**Theorem 5.1 (actual deterministic restricted-fiber decomposition).**
For every $m,B,H,K,n$, including zero parameters and the empty
permutation, this procedure terminates with a supplied typed endpoint
history and an actual terminal sample reconstructing its input. Its
history has at most $H$ transitions and every selected endpoint has
length at most $K$. Its deterministic outcome fibers give a finite,
exhaustive, pairwise-disjoint partition of the actual source carrier.
For an outcome $(h,q)$, restrict the terminal carrier of $h$ to those
samples whose reconstructed permutation is classified as $(h,q)$.
Reconstruction is a bijection from this restricted terminal set to
the classifier fiber. Thus its cardinality, and its uniform actual
mass, use the restricted terminal cardinality, not an unproved full
leaf cardinality. On a good outcome every literal $m$-coordinate test
in alphabet $B$ is constant, with the supplied history word. Summing
over the finite classifier image gives its exact actual cylinder
mass; non-good outcomes retain their actual restricted cylinder mass.
When $B=m$, the same statement applies to the absolute zero-based
no-fixed-position test. No equality between a restricted classifier
fiber and the full supplied-history event is implicit.

*Proof.* Proper-cut existence and incompatibility recover the sign;
the least positive cut and the minimum-cut Cartesian equivalence
recover the unique actual factors. Recursion on the transition budget
constructs the typed history, preserving its actual terminal sample.
The history kernel supplies reconstruction injectivity, actual source
membership, and literal word transport. A permutation has exactly one
classifier value, so the fibers are disjoint and cover the source.
Restricting the injective history reconstruction gives the fiber
bijection. Finite uniform mass is actual cardinality divided by $s_n$;
partitioning each tested event then gives the finite sum. $\square$

The bound $n>HK+\max(2K,m,B)$ keeps every active length above $2K$ and
the terminal length above $B$. In particular the two permitted endpoint
choices do not overlap there. A classifier-image catalog at a given
$n$ does not itself give a stable finite catalog for convergence. A
length-independent bounded code interface, full-history fiber equality,
actual count-ratio asymptotics, sign-half and indecomposable cardinal
interfaces, infinite-law construction, truncation tails, occupation,
filtration, hitting and the full all-length limit are separate
obligations.

<!-- APPEND -->
