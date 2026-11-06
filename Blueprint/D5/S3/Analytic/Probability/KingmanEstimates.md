# Estimates for nonnegative subadditive cocycles

## Abstract

Adaptive block decompositions, stationary tails and a weak maximal inequality control nonnegative subadditive orbit sequences.

**Theorem 1.1 (Integrable stationary tails vanish after division by time).**

$$\begin{aligned}\forall \alpha: \operatorname{Type}\left(\right) u, [\operatorname{MeasurableSpace}\left(\alpha\right)] \forall \mu: \operatorname{Measure}\left(\alpha\right), [\operatorname{IsProbabilityMeasure}\left(\mu\right)] \forall T: \alpha \to \alpha, \\\operatorname{MeasurePreserving}\left(T, \mu, \mu\right) \Rightarrow\forall \phi: \alpha \to \mathbb{R}, \operatorname{Measurable}\left(\phi\right) \Rightarrow\operatorname{Integrable}\left(\phi, \mu\right) \Rightarrow(\forall x: \alpha, 0 \leq \phi\left(x\right)) \Rightarrow\\\operatorname{Eventually}\left(\lambda (x: \alpha) \mapsto \operatorname{Tendsto}\left(\lambda (m: \mathbb{N}) \mapsto \frac{\phi\left(\operatorname{iterate}\left(T, m\right)\left(x\right)\right)}{m}, \operatorname{atTop}\left(\right), \operatorname{nhds}\left(0\right)\right), \operatorname{ae}\left(\mu\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/KingmanEstimates.ae_tendsto_comp_iterate_div_nat` (`✓ std3`). ∎

*Citation.* Rick Durrett (2019). *Probability: Theory and Examples, Fifth Edition*. DOI: [10.1017/9781108591034](https://doi.org/10.1017/9781108591034). URL: <https://services.math.duke.edu/~rtd/PTE/PTE5_011119.pdf>.

*Commentary.*

For an arbitrary measurable probability space, a measure-preserving transformation T and a measurable integrable nonnegative real observable phi, the value phi at the nth orbit point divided by n converges to zero almost everywhere. No independence or ergodicity is assumed.

Integrability makes the sum of the probabilities of integer tail events finite. Measure preservation gives the same probabilities for the corresponding orbit events. The first Borel–Cantelli lemma yields an eventual bound at each reciprocal integer level. Countably many levels and nonnegativity give convergence.

**Theorem 1.2 (Adaptive greedy block bound).**

$$\begin{aligned}\forall F: \mathbb{N} \to \left(\mathbb{N} \to \mathbb{R}\right), (\forall k: \mathbb{N}, \forall n: \mathbb{N}, 0 \leq F\left(k, n\right)) \Rightarrow\\(\forall k: \mathbb{N}, F\left(k, 0\right)=0) \Rightarrow\\(\forall k: \mathbb{N}, \forall m: \mathbb{N}, \forall n: \mathbb{N}, F\left(k, m+n\right) \leq F\left(k, m\right)+F\left(k+m, n\right)) \Rightarrow\\\forall B: \mathbb{N} \to \operatorname{Prop}\left(\right), [\operatorname{DecidablePred}\left(B\right)] \forall c: \mathbb{R}, 0 \leq c \Rightarrow\forall N: \mathbb{N}, \\(\forall k: \mathbb{N},  \neg B\left(k\right) \Rightarrow\exists n:\mathbb{N}, 1 \leq n \land n \leq N \land F\left(k, n\right) \leq n \cdot c) \Rightarrow\\\forall M: \mathbb{N}, F\left(0, M\right) \leq M \cdot c+\operatorname{sum}\left(\operatorname{range}\left(M\right), \lambda (k: \mathbb{N}) \mapsto \operatorname{ite}\left(B\left(k\right), F\left(k, 1\right), 0\right)\right)+\\\operatorname{sum}\left(\operatorname{range}\left(M\right), \lambda (k: \mathbb{N}) \mapsto \operatorname{ite}\left(M \leq k+N, F\left(k, 1\right), 0\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/KingmanEstimates.greedy_block_bound` (`✓ std3`). ∎

*Citation.* Rick Durrett (2019). *Probability: Theory and Examples, Fifth Edition*. DOI: [10.1017/9781108591034](https://doi.org/10.1017/9781108591034). URL: <https://services.math.duke.edu/~rtd/PTE/PTE5_011119.pdf>.

*Commentary.*

Let F(k,n) be nonnegative real costs, with F(k,0)=0 and F(k,m+n) at most F(k,m)+F(k+m,n). Let B mark bad starting positions. At every good position assume a block of length between one and N whose cost is at most its length times a fixed nonnegative c.

For every horizon M, the total cost F(0,M) is bounded by M times c, plus the one-step costs at bad positions before M, plus the one-step costs at positions k before M with M at most k+N. The two sums can overlap, and the bound retains that overlap.

Strong induction on the remaining length implements the adaptive tiling. A bad position consumes one step and charges its cost to the bad-position sum. A good block that fits is consumed whole and charged to the linear budget. A good block that crosses the horizon consumes one step and charges its cost to the terminal strip. Nonnegativity permits the unused parts of the two sums to be retained.

**Theorem 1.3 (Weak maximal inequality for invariant divergence sets).**

$$\begin{aligned}\forall \alpha: \operatorname{Type}\left(\right) u, [\operatorname{MeasurableSpace}\left(\alpha\right)] \forall \mu: \operatorname{Measure}\left(\alpha\right), [\operatorname{IsProbabilityMeasure}\left(\mu\right)] \forall T: \alpha \to \alpha, \\\operatorname{MeasurePreserving}\left(T, \mu, \mu\right) \Rightarrow\forall \phi: \alpha \to \mathbb{R}, \operatorname{Measurable}\left(\phi\right) \Rightarrow\operatorname{Integrable}\left(\phi, \mu\right) \Rightarrow(\forall x: \alpha, 0 \leq \phi\left(x\right)) \Rightarrow\\\forall c: \mathbb{R}, 0 < c \Rightarrow\mu\left(\operatorname{DickSet}\left(T, \phi, c\right)\right) \leq \operatorname{ofReal}\left(\frac{\operatorname{integral}\left(\mu, \phi\right)}{c}\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/KingmanEstimates.measure_kingmanDick_le` (`✓ std3`). ∎

*Citation.* Rick Durrett (2019). *Probability: Theory and Examples, Fifth Edition*. DOI: [10.1017/9781108591034](https://doi.org/10.1017/9781108591034). URL: <https://services.math.duke.edu/~rtd/PTE/PTE5_011119.pdf>.

*Commentary.*

For a measurable integrable nonnegative phi on a probability space and c>0, the invariant divergence set consists of points whose orbit sums exceed n times some rational level greater than c arbitrarily late. Its measure is at most the integral of phi divided by c, interpreted as a nonnegative extended real.

Apply the maximal ergodic integral inequality to the indicator of the invariant divergence set times phi-c. Orbit invariance identifies its sums inside the set and makes them zero outside. The resulting nonnegative integral bounds c times the measure of the set by the integral of phi on that set, and then by the full integral.

The classical references are Kingman, The ergodic theory of subadditive stochastic processes (1968), and Steele, Kingman's subadditive ergodic theorem (1989). Durrett, Probability: Theory and Examples, fifth edition, Section 6.4, gives the stationary-array theorem. The Lean proof source is facebookresearch/atlas-lean, MathlibExt/Dynamics/Ergodic/Kingman.lean, revision a60759060b5616df0d5775b42da4d337719feb32. The Meta Platforms copyright and complete supplier license, including its preface, are retained separately from the citation-only book reference.

## References

- Truth anchor: `D5/S3/Analytic/Probability/KingmanEstimates.ae_tendsto_comp_iterate_div_nat`
- Truth anchor: `D5/S3/Analytic/Probability/KingmanEstimates.greedy_block_bound`
- Truth anchor: `D5/S3/Analytic/Probability/KingmanEstimates.measure_kingmanDick_le`
- Dependency: [D5/S3/Analytic/Probability/BirkhoffPointwise](BirkhoffPointwise.md)
