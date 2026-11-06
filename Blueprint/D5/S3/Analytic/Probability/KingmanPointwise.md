# Kingman's nonnegative subadditive ergodic theorem

## Abstract

On every finite measure space, nonnegative integrable subadditive cocycles have an integrable invariant real limit almost everywhere.

**Theorem 1.1 (An integrable invariant limit).**

$$\begin{aligned}\forall \alpha: \operatorname{Type} u, [\operatorname{MeasurableSpace}\left(\alpha\right)] \forall \mu: \operatorname{Measure}\left(\alpha\right), [\operatorname{IsFiniteMeasure}\left(\mu\right)] \\\forall T: \alpha \to \alpha, \operatorname{MeasurePreserving}\left(T, \mu, \mu\right) \Rightarrow\forall X: \mathbb{N} \to \left(\alpha \to \mathbb{R}\right), \\(\forall n: \mathbb{N}, \operatorname{Integrable}\left(X\left(n\right), \mu\right)) \Rightarrow\\(\forall n: \mathbb{N}, \operatorname{Eventually}\left(\lambda (x: \alpha) \mapsto 0 \leq X\left(n, x\right), \operatorname{ae}\left(\mu\right)\right)) \Rightarrow\\(\forall m: \mathbb{N}, \forall n: \mathbb{N}, \operatorname{Eventually}\left(\lambda (x: \alpha) \mapsto X\left(m+n, x\right) \leq X\left(m, x\right)+X\left(n, \operatorname{iterate}\left(T, m\right)\left(x\right)\right), \operatorname{ae}\left(\mu\right)\right)) \Rightarrow\\\exists g:\alpha \to \mathbb{R}, \operatorname{Integrable}\left(g, \mu\right) \land \operatorname{Eventually}\left(\lambda (x: \alpha) \mapsto g\left(T\left(x\right)\right)=g\left(x\right), \operatorname{ae}\left(\mu\right)\right)\land\\\operatorname{Eventually}\left(\lambda (x: \alpha) \mapsto \operatorname{Tendsto}\left(\lambda (n: \mathbb{N}) \mapsto \frac{X\left(n, x\right)}{n}, \operatorname{atTop}, \operatorname{nhds}\left(g\left(x\right)\right)\right), \operatorname{ae}\left(\mu\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/KingmanPointwise.kingman_subadditive` (`✓ std3`). ∎

*Citation.* Rick Durrett (2019). *Probability: Theory and Examples, Fifth Edition*. DOI: [10.1017/9781108591034](https://doi.org/10.1017/9781108591034). URL: <https://services.math.duke.edu/~rtd/PTE/PTE5_011119.pdf>.

*Commentary.*

The carrier alpha ranges over every universe u and has an arbitrary measurable-space structure. The measure mu is finite, including zero. The transformation T preserves mu. For each natural n the real function X(n) is integrable and nonnegative almost everywhere. For every m,n, X(m+n,x) is at most X(m,x)+X(n,T^m x) almost everywhere. The exceptional sets may depend on the indices.

There exists a real function g, integrable for the same mu, invariant under T almost everywhere, such that X(n,x)/n tends to g(x) almost everywhere along the full sequence of natural times. Real division is totalized, so the value at n=0 imposes no additional condition. The original X(0) need not vanish. No pointwise measurability of X(n), nonempty carrier, probability normalization, positive mass, ergodicity, invertibility, countability, standard Borel structure, boundedness or square integrability is assumed.

When mu is zero, choose g=0; all almost-everywhere conclusions also hold on the empty carrier. For nonzero finite mu, normalize the measure to a probability measure. Its almost-everywhere filter agrees with that of mu, and integrability is equivalent for the two measures. Choose measurable representatives for the functions at positive times and set only the internal zeroth function to zero. Quasi-measure preservation transports their equalities through every orbit shift. Countable intersections produce a measurable forward-invariant set of full measure on which nonnegativity, the zeroth identity and all subadditive inequalities hold together. Setting the family to zero outside that set gives everywhere hypotheses.

Subadditivity bounds the family by orbit sums of its first term. Fatou's lemma then bounds the integral of the nonnegative extended-real liminf rate and makes that rate finite almost everywhere. The one-step subadditive inequality makes the liminf subinvariant. Measure preservation gives equal integrals for the liminf and its composition; finiteness upgrades their one-sided inequality to equality almost everywhere.

For each positive epsilon, the sets on which every average up to a horizon exceeds the liminf plus epsilon decrease to a null set. Their first-term integrals tend to zero. The adaptive greedy block estimate bounds each long average by the liminf plus epsilon, an orbit average of the bad-set indicator times the first term, and a terminal strip. Stationary-tail decay removes that strip. The weak maximal inequality makes the remaining excess set null as the bad-set horizon grows. Countably many epsilon levels give the upper limit bound; the definition of liminf gives the lower bound. The real-valued liminf is therefore the integrable invariant limit.

Transfer this same function g, its integrability and invariance back to mu. Countably many representative equalities identify the original and internal positive-time sequences almost everywhere. Eventual equality transfers convergence without changing g or imposing an identity on X(0).

Durrett, fifth edition, Section 6.4, Theorem 6.4.1 on printed page 343 with proof on pages 344–347, treats stationary subadditive arrays and also states L1 convergence and an infimum formula. Those further conclusions and a constant ergodic limit are not asserted here. Applying the theorem to a concrete array, matrix product or first-passage model requires the actual common law, shift action, integrability, nonnegativity and subadditive identification. Signed logarithmic cocycles require a separate argument.

The Lean proof is an attributed adaptation of facebookresearch/atlas-lean, MathlibExt/Dynamics/Ergodic/Kingman.lean, revision a60759060b5616df0d5775b42da4d337719feb32. The Meta Platforms copyright and complete supplier license, including its intended-use preface, are retained. KingmanSigned.exists_invariant_limit_of_nonneg supplies the broad finite-measure specification; no signed-cocycle conclusion is used. The book is a citation-only mathematical source.

## References

- Truth anchor: `D5/S3/Analytic/Probability/KingmanPointwise.kingman_subadditive`
- Dependency: [D5/S3/Analytic/Probability/KingmanEstimates](KingmanEstimates.md)
