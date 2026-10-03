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

<!-- APPEND -->
