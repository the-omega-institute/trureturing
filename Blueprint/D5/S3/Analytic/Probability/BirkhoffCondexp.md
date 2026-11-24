# Birkhoff's conditional-expectation theorem

## Abstract

On a finite measure space, integrable real time averages converge almost everywhere and in L1 to invariant conditional expectation.

**Theorem 1.1 (Pointwise and mean convergence without ergodicity).**

Lean statement: `D5/S3/Analytic/Probability/BirkhoffCondexp.birkhoff_conditional_expectation`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Probability/BirkhoffCondexp.birkhoff_conditional_expectation` (`✓ std3`). ∎

*Citation.* Rick Durrett (2019). *Probability: Theory and Examples, Fifth Edition*. DOI: [10.1017/9781108591034](https://doi.org/10.1017/9781108591034). URL: <https://services.math.duke.edu/~rtd/PTE/PTE5_011119.pdf>.

*Commentary.*

Let alpha range over every universe and carry an arbitrary measurable-space structure. Let mu be any finite measure, let T be a measurable transformation preserving mu, and let g be any integrable real function. Write I for MeasurableSpace.invariants T: its measurable sets are the ambient measurable sets whose preimages under T equal themselves. Let c be the actual measurable version mu[g | I] of conditional expectation. For natural n, put A_n(x) = birkhoffAverage Real T g n x, the sum of g(T^j x) over j<n divided by n, with A_0(x) = 0.

Two conclusions hold together. For mu-almost every x, the complete sequence n maps to A_n(x) converges to c(x) as n tends to infinity. Along the same natural-index atTop filter, the real integral of |A_n(x) - c(x)| with respect to mu tends to zero. The latter is L1 convergence of the actual finite-time averages to the conditional version, and includes integrability of every absolute difference.

No ergodicity, invertibility, positive total mass, probability normalization, pointwise measurability or boundedness of g, countability or standard-Borel structure is assumed. The theorem includes the zero measure and arbitrary integrable constants. Its almost-everywhere conclusion concerns one fixed g and one exceptional null set for its full time sequence; it does not provide a common exceptional set for all integrable observables or a convergence rate.

For a measurable integrable input h, let D be the set where its partial orbit sums exceed every natural-number upper bound. The sum-shift identity and an Archimedean bound show T preimage D = D. Restrict mu to this measurable invariant set and apply the maximal ergodic inequality. Every point of D has some positive partial sum, so the integral of h over D is nonnegative. If E_mu[h | I] is strictly negative almost everywhere, the conditional-integral identity forces D to be null.

Outside D the partial sums have an upper bound, and division by n makes the limsup of their averages nonpositive. Apply this fact to g - (c + epsilon). The conditional expectation of this difference is the negative constant -epsilon, and the I-measurable version c is invariant under T. Repeat for -g. Countably many positive epsilon levels give the upper and lower bounds for almost-everywhere convergence. An almost-everywhere equal measurable representative and quasi-measure preservation transfer the argument to every integrable g.

For a nonnegative input g, both A_n and c are nonnegative almost everywhere. The functions min(A_n,c) converge almost everywhere to c and are dominated by c. Dominated convergence gives convergence of their integrals. At every positive time, measure preservation gives integral(A_n) = integral(g) = integral(c). The identity |a-b| = a+b-2 min(a,b) therefore makes the integral of |A_n-c| tend to zero. Split a general real g into its positive and negative parts, use linearity of averages and conditional expectation, and integrate the triangle inequality to obtain the same L1 conclusion.

Durrett, Probability: Theory and Examples, fifth edition, Theorem 6.2.1 and Lemma 6.2.2, printed pages 335–337, supply the classical probability-space result and maximal argument. The almost-everywhere Lean argument adapts Lua Viana Reis and Oliver Butterley's Mathlib contribution PR 42078 at revision ebc0f703f74bec1576e2ca3b078fb173ba11039f. The complete Apache-2.0 supplier license and copyright are retained. The finite-measure localization and real L1 argument use the existing maximal inequality and pinned Mathlib integral and conditional-expectation laws. No package dependency or claim of mathematical originality is added.

## References

- Truth anchor: `D5/S3/Analytic/Probability/BirkhoffCondexp.birkhoff_conditional_expectation`
- Dependency: [D5/S3/Analytic/Probability/BirkhoffPointwise](BirkhoffPointwise.md)
