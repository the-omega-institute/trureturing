# Birkhoff pointwise ergodic theorem

## Abstract

Real integrable time averages of an ergodic probability transformation converge almost everywhere to their integral.

**Theorem 1.1 (Almost-everywhere convergence to the mean).**

$$\begin{aligned}\forall \alpha: \operatorname{Type} u, [\operatorname{MeasurableSpace}\left(\alpha\right)] \forall \mu: \operatorname{Measure}\left(\alpha\right), [\operatorname{IsProbabilityMeasure}\left(\mu\right)] \\\forall T: \alpha \to \alpha, \operatorname{Ergodic}\left(T, \mu\right) \Rightarrow\forall g: \alpha \to \mathbb{R}, \operatorname{Integrable}\left(g, \mu\right) \Rightarrow\\\operatorname{Eventually}\left(\lambda (x: \alpha) \mapsto \operatorname{Tendsto}\left(\lambda (n: \mathbb{N}) \mapsto \operatorname{birkhoffAverage}\left(\mathbb{R}, T, g, n, x\right), \operatorname{atTop}, \operatorname{nhds}\left(\operatorname{integral}\left(\mu, \lambda (y: \alpha) \mapsto g\left(y\right)\right)\right)\right), \operatorname{ae}\left(\mu\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/BirkhoffPointwise.birkhoff_pointwise_ergodic` (`✓ std3`). ∎

*Citation.* Rick Durrett (2019). *Probability: Theory and Examples, Fifth Edition*. DOI: [10.1017/9781108591034](https://doi.org/10.1017/9781108591034). URL: <https://services.math.duke.edu/~rtd/PTE/PTE5_011119.pdf>.

*Commentary.*

The carrier alpha ranges over every universe u and has an arbitrary measurable-space structure. The measure mu is any probability measure. Ergodic(T,mu) is the native conjunction of measure preservation and pre-ergodicity: every null-measurable almost-invariant set is null or conull. The real observable g is only assumed integrable. No pointwise measurability, boundedness, square integrability, countability, standard Borel structure, or invertibility is required.

For each fixed g, the conclusion holds for mu-almost every x along the complete sequence of natural times. The average at n=0 is canonically zero; for positive n it is the sum of g(T^j x) over j<n divided by n. The theorem retains empty-carrier quantification and all integrable constants, including zero. It asserts neither a common exceptional set for every g nor uniform, vector-valued, nonergodic conditional-expectation, or L1 convergence.

For a measurable integrable f, take the finite maximum of its initial orbit sums, including the zeroth sum. Positivity of that maximum gives a one-step inequality. Integrating over its positive set, measure preservation cancels the full integrals of the maximum and its composition with T. An increasing-set limit yields the nonnegative integral of f over the set where some orbit sum is positive.

For each level c above the mean of g, form the invariant set where orbit sums exceed n times a rational level above c arbitrarily late. Apply the maximal integral inequality to the indicator of this set times g-c. Ergodicity makes the set null or conull; the conull case contradicts the negative integral of g-c. Countably many rational levels for g and -g give the upper and lower eventual bounds, hence order convergence. Finally, an almost-everywhere equal measurable representative has the same integral, and quasi-measure preservation identifies every finite-time average almost everywhere.

Durrett, Probability: Theory and Examples, fifth edition, Section 6.2, Theorem 6.2.1 and Lemma 6.2.2, printed pages 335–337, provide the classical mathematical reference. The Lean proof is an attributed adaptation of facebookresearch/atlas-lean, MathlibExt/Dynamics/Ergodic/Birkhoff.lean, revision a60759060b5616df0d5775b42da4d337719feb32. Its Meta Platforms copyright and complete supplier license are retained. The adaptation makes auxiliary declarations private and uses pinned Mathlib fixed-set iteration and almost-everywhere transport; the literature note separates the book citation from the code provenance.

Symbolic frequencies, joint-product moments, context-dependent compositions and entropy-production rates require an actual probability law, ergodicity, an integrable observable, identification of its integral and the relevant orbit or boundary correspondence. This autonomous theorem supplies the convergence step once those mathematical bridges are established.

## References

- Truth anchor: `D5/S3/Analytic/Probability/BirkhoffPointwise.birkhoff_pointwise_ergodic`
