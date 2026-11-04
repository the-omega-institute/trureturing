# A counterexample to the pseudo-coarse-grained dissipation-time trade-off

## Abstract

A positive three-state cyclic chain violates the proposed two-state lower bound on non-adiabatic entropy production.

The states are Fin n, the indices 0 through n − 1. The real entry a(i,j) is the transition rate from j to i. Write W = generator(a): its off-diagonal entries are a(i,j), and its jth diagonal entry is minus the sum of a(i,j) over i distinct from j. Thus each column sums to zero. For finite real vectors, klDivergence(v,w) is the sum of v(i) log(v(i)/w(i)). The notation ![x,1 − x] denotes the function on Fin 2 with those two real coordinates. These are the master equation, total-rate convention and divergence in the source's TeX lines 159–184.

**Definition 1.1 (The steady-state coordinate determined by two endpoints).**

$$\forall \left(x: \mathbb{R}\right), \left(\forall \left(y: \mathbb{R}\right), \left(\forall \left(k: \mathbb{R}\right), \left(\forall \left(\tau: \mathbb{R}\right), \left(\left(\operatorname{binarySteadyState}\left(x, y, k, \tau\right): \mathbb{R}\right) = x + \frac{y - x}{\left(1: \mathbb{R}\right) - \operatorname{Real.exp}\left(-\left(k \cdot \tau\right)\right)}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/PseudoCoarseGrainedTradeoffRefutation.binarySteadyState` (`✓ std3`).

*Citation.* Jie Gu (2023). *Speed limit, dissipation bound, and dissipation-time trade-off in thermal relaxation processes*. DOI: [10.1103/PhysRevE.108.L052103](https://doi.org/10.1103/PhysRevE.108.L052103). URL: <https://arxiv.org/abs/2304.08752v2>.

*Commentary.*

For a two-state process whose first-coordinate endpoints are x and y, total rate k and elapsed time τ, the first steady-state coordinate is x + (y − x)/(1 − exp(−kτ)). The other coordinate is its complement. This is the equation labelled eq:p1 in TeX lines 191–196. The real-valued definition allows arbitrary real inputs; division is total, so a zero denominator has the usual real-field value zero for the quotient.

**Definition 1.2 (The proposed bound for every nontrivial two-part partition).**

$$\left(\operatorname{claim}\right) \Leftrightarrow \left(\forall \left(n: \mathbb{N}\right), \left(\forall \left(a: \operatorname{Fin}\left(n\right) \to \left(\operatorname{Fin}\left(n\right) \to \mathbb{R}\right)\right), \left(\forall \left(u: \operatorname{Fin}\left(n\right) \to \mathbb{R}\right), \left(\forall \left(p: \mathbb{R} \to \left(\operatorname{Fin}\left(n\right) \to \mathbb{R}\right)\right), \left(\forall \left(\tau: \mathbb{R}\right), \left(\forall \left(\omega: \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right)\right), \left(\left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(\forall \left(j: \operatorname{Fin}\left(n\right)\right), \left(\left(i \ne j\right) \to \left(\left(0: \mathbb{R}\right) < a\left(i, j\right)\right)\right)\right)\right) \to \left(\left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(\left(0: \mathbb{R}\right) < u\left(i\right)\right)\right) \to \left(\left(\sum_{\left(i: \operatorname{Fin}\left(n\right)\right)} \left(u\left(i\right)\right) = \left(1: \mathbb{R}\right)\right) \to \left(\left(\operatorname{Matrix.mulVec}\left(\operatorname{D5.S3.StatisticalMechanics.MarkovMpembaTripletRefutation.generator}\left(a\right), u\right) = \operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), \left(0: \mathbb{R}\right)\right)\right) \to \left(\left(\forall \left(t: \mathbb{R}\right), \left(\operatorname{HasDerivAt}\left(p, \operatorname{Matrix.mulVec}\left(\operatorname{D5.S3.StatisticalMechanics.MarkovMpembaTripletRefutation.generator}\left(a\right), p\left(t\right)\right), t\right)\right)\right) \to \left(\left(\left(0: \mathbb{R}\right) < \tau\right) \to \left(\left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(\left(0: \mathbb{R}\right) < p\left(\left(0: \mathbb{R}\right), i\right)\right)\right) \to \left(\left(\sum_{\left(i: \operatorname{Fin}\left(n\right)\right)} \left(p\left(\left(0: \mathbb{R}\right), i\right)\right) = \left(1: \mathbb{R}\right)\right) \to \left(\left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(\left(0: \mathbb{R}\right) < p\left(\tau, i\right)\right)\right) \to \left(\left(\operatorname{Finset.Nonempty}\left(\omega\right)\right) \to \left(\left(\operatorname{Finset.Nonempty}\left(\operatorname{Compl.compl}\left(\omega\right)\right)\right) \to \left(\operatorname{let} \left(x: \mathbb{R}\right) := \left(\sum_{\left(i: \operatorname{Fin}\left(n\right)\right) \in \omega} \left(p\left(\left(0: \mathbb{R}\right), i\right)\right)\right); \left(\operatorname{let} \left(y: \mathbb{R}\right) := \left(\sum_{\left(i: \operatorname{Fin}\left(n\right)\right) \in \omega} \left(p\left(\tau, i\right)\right)\right); \left(\operatorname{let} \left(k: \mathbb{R}\right) := \left(-\left(\operatorname{Matrix.trace}\left(\operatorname{D5.S3.StatisticalMechanics.MarkovMpembaTripletRefutation.generator}\left(a\right)\right)\right)\right); \left(\operatorname{let} \left(s: \mathbb{R}\right) := \left(\operatorname{binarySteadyState}\left(x, y, k, \tau\right)\right); \left(\left(\left(0: \mathbb{R}\right) < s\right) \to \left(\left(s < \left(1: \mathbb{R}\right)\right) \to \left(\operatorname{D5.S3.Divergence.ClassicalDPI.klDivergence}\left(\left(![x, \left(1: \mathbb{R}\right) - x]: \operatorname{Fin}\left(2\right) \to \mathbb{R}\right), \left(![s, \left(1: \mathbb{R}\right) - s]: \operatorname{Fin}\left(2\right) \to \mathbb{R}\right)\right) - \operatorname{D5.S3.Divergence.ClassicalDPI.klDivergence}\left(\left(![y, \left(1: \mathbb{R}\right) - y]: \operatorname{Fin}\left(2\right) \to \mathbb{R}\right), \left(![s, \left(1: \mathbb{R}\right) - s]: \operatorname{Fin}\left(2\right) \to \mathbb{R}\right)\right) \le \operatorname{D5.S3.Divergence.ClassicalDPI.klDivergence}\left(p\left(\left(0: \mathbb{R}\right)\right), u\right) - \operatorname{D5.S3.Divergence.ClassicalDPI.klDivergence}\left(p\left(\tau\right), u\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/PseudoCoarseGrainedTradeoffRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jie Gu (2023). *Speed limit, dissipation bound, and dissipation-time trade-off in thermal relaxation processes*. DOI: [10.1103/PhysRevE.108.L052103](https://doi.org/10.1103/PhysRevE.108.L052103). URL: <https://arxiv.org/abs/2304.08752v2>.

*Commentary.*

For every natural n, choose an array a, a positive normalized vector u annihilated by W, a real-time curve p and a positive time τ. All off-diagonal entries of a are positive. At every real t, p has derivative Wp(t). The initial vector p(0) is positive and normalized, and the final vector p(τ) is positive. The finite set ω and its complement are both nonempty. Sum the initial and final probabilities over ω to obtain x and y, take k = −trace(W), and compute s with binarySteadyState. Whenever 0 < s < 1, the proposed inequality bounds the binary divergence drop relative to ![s,1 − s] by the full divergence drop relative to u. This is a reading of the source's Eq. (13), TeX lines 327–337, restricted to strictly positive off-diagonal entries and endpoints and an interior binary steady state. Detailed balance is not required. The derivative hypothesis ranges over all real times; the statement imposes positivity only at the two endpoints.

**Theorem 1.3 (A three-state cyclic counterexample).**

$$\neg \left(\operatorname{claim}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/PseudoCoarseGrainedTradeoffRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/gu-2023-pseudo-coarse-grained-tradeoff` (refuted) by `D5/S3/StatisticalMechanics/PseudoCoarseGrainedTradeoffRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"gu-2023-pseudo-coarse-grained-tradeoff","declaration_gid":"D5/S3/StatisticalMechanics/PseudoCoarseGrainedTradeoffRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jie Gu (2023). *Speed limit, dissipation bound, and dissipation-time trade-off in thermal relaxation processes*. DOI: [10.1103/PhysRevE.108.L052103](https://doi.org/10.1103/PhysRevE.108.L052103). URL: <https://arxiv.org/abs/2304.08752v2>.

*Commentary.*

Use n = 3 and the off-diagonal array a = [[0,1/100,1],[1,0,1/100],[1/100,1,0]]. Every entry between distinct states is positive. Its generator is W = [[−101,1,100],[100,−101,1],[1,100,−101]]/100. The vector u = (1/3,1/3,1/3) satisfies Wu = 0.

Set A = 303/200, B = 99√3/200, v = (2,−1,−1) and w = (0,√3,−√3). Direct multiplication gives Wv = −Av + Bw and Ww = −Bv − Aw. Define P(t) = u + exp(−At)(cos(Bt)v + sin(Bt)w)/12. Differentiate the exponential, cosine and sine coordinate by coordinate. The two matrix identities and Wu = 0 give P′(t) = WP(t) for every real t.

Choose τ = π/B and put r = exp(−Aτ). At zero the curve is P(0) = (1/2,1/4,1/4). Since Bτ = π, cos(Bτ) = −1 and sin(Bτ) = 0, its other endpoint is P(τ) = ((2 − r)/6,(4 + r)/12,(4 + r)/12).

The inequalities √3 > 17/10 and π > 3 imply B > 0, τ > 0 and Aτ = 101√3π/99 > 3. The exponential inequality exp(Aτ) ≥ 1 + Aτ > 4 then gives 0 < r < 1/4. The total rate is −trace(W) = 303/100 = 2A. Therefore exp(−(303/100)τ) = r². Substituting this identity into binarySteadyState(1/2,(2 − r)/6,303/100,τ) and clearing the nonzero denominators 1 − r and 1 − r² gives s = (2 − 3r)/(6(1 − r)). For every r in (0,1/4), its denominator is positive and 0 < s < 1/3 < 1.

Write d(z,b) = klDivergence(![z,1 − z],![b,1 − b]). Splitting the second coordinate into two equal parts gives klDivergence(![z,(1 − z)/2,(1 − z)/2],u) = d(z,1/3): the two equal summands have the same probability ratio and add to the single binary summand. For 0 < x,y,s < 1, expanding the logarithms of quotients and products gives (d(x,1/3) − d(y,1/3)) − (d(x,s) − d(y,s)) = (x − y) log(2s/(1 − s)).

Take x = 1/2, y = (2 − r)/6 and s = (2 − 3r)/(6(1 − r)). Both three-coordinate endpoints have the split form just described. The logarithm's argument simplifies to (4 − 6r)/(4 − 3r). For 0 < r < 1/4 this ratio is strictly between zero and one, so its logarithm is negative. Also x − y = (1 + r)/6 > 0. Consequently the full divergence drop is strictly smaller than the binary divergence drop.

Finally, u and P(0) are positive normalized vectors, and the displayed endpoint and the bounds on r make P(τ) positive. Take ω = {0}; its complement contains 1. All hypotheses of claim now hold for a, u, P and τ, with aggregate endpoints x = 1/2 and y = (2 − r)/6 and the interior value s above. The asserted non-strict inequality contradicts the strict reverse inequality, proving the negation of claim.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/PseudoCoarseGrainedTradeoffRefutation.binarySteadyState`
- Truth anchor: `D5/S3/StatisticalMechanics/PseudoCoarseGrainedTradeoffRefutation.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/PseudoCoarseGrainedTradeoffRefutation.result`
- Dependency: [D5/S3/StatisticalMechanics/MarkovMpembaTripletRefutation](MarkovMpembaTripletRefutation.md)
