# A four-level counterexample to the Mpemba triplet conjecture

## Abstract

Four reversible energy levels exhibit the Mpemba effect although every triplet fails the proposed three-level condition.

The states are Fin N, the indices 0 through N − 1. Energies, inverse temperatures and transition rates are real. The entry a(i,j) is the rate from j to i, and probability vectors are columns. All sums over Fin N range over the entire finite state space. The definitions allow arbitrary real arguments; positivity, ordering and detailed balance are hypotheses of the conjecture.

**Definition 1.1 (The continuous-time rate matrix).**

$$\forall (N: \mathbb{N}), (\forall (a: \operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \mathbb{R}\right)), (\forall (i: \operatorname{Fin}\left(N\right)), (\forall (j: \operatorname{Fin}\left(N\right)), (\operatorname{generator}\left(a, i, j\right) = \operatorname{if} (i = j) \operatorname{then} (-(\sum_{(k: \operatorname{Fin}\left(N\right))} (\operatorname{if} (k = j) \operatorname{then} (0) \operatorname{else} (a\left(k, j\right))))) \operatorname{else} (a\left(i, j\right))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/MarkovMpembaTripletRefutation.generator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ido Avitan; Roee Factor; David Gelbwaser-Klimovsky (2026). *Necessary conditions for the Markovian Mpemba effect*. URL: <https://arxiv.org/abs/2603.04567v1>.

*Commentary.*

Equation (1) places a(i,j) off the diagonal and the negative total rate leaving j on the diagonal. The conditional summand removes the self-transition. Each column sums to zero, as required for the population equation dp/dt = M p.

**Definition 1.2 (Balance at the bath temperature).**

$$\forall (N: \mathbb{N}), (\forall (E: \operatorname{Fin}\left(N\right) \to \mathbb{R}), (\forall (\beta_{b}: \mathbb{R}), (\forall (a: \operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \mathbb{R}\right)), ((\operatorname{DetailedBalance}\left(E, \beta_{b}, a\right)) \Leftrightarrow (\forall (j: \operatorname{Fin}\left(N\right)), (\forall (k: \operatorname{Fin}\left(N\right)), ((j \ne k) \Rightarrow (a\left(j, k\right) = a\left(k, j\right) \cdot \operatorname{Real.exp}\left(-(\beta_{b} \cdot \left(E\left(j\right) - E\left(k\right)\right))\right)))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/MarkovMpembaTripletRefutation.DetailedBalance` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ido Avitan; Roee Factor; David Gelbwaser-Klimovsky (2026). *Necessary conditions for the Markovian Mpemba effect*. URL: <https://arxiv.org/abs/2603.04567v1>.

*Commentary.*

The rate ratio between distinct levels is the Boltzmann factor at bath inverse temperature βb. This is the detailed-balance relation accompanying Eq. (1). No condition is imposed on a(i,i).

**Definition 1.3 (The two alternatives of the three-level condition).**

$$\forall (N: \mathbb{N}), (\forall (E: \operatorname{Fin}\left(N\right) \to \mathbb{R}), (\forall (\beta_{b}: \mathbb{R}), (\forall (a: \operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \mathbb{R}\right)), (\forall (i: \operatorname{Fin}\left(N\right)), (\forall (j: \operatorname{Fin}\left(N\right)), (\forall (k: \operatorname{Fin}\left(N\right)), ((\operatorname{TripletCondition}\left(E, \beta_{b}, a, i, j, k\right)) \Leftrightarrow (((1 \le \frac{a\left(i, k\right) + a\left(j, k\right)}{a\left(i, j\right) \cdot \left(1 + \operatorname{Real.exp}\left(-(\beta_{b} \cdot \left(E\left(j\right) - E\left(i\right)\right))\right)\right)}) \land (a\left(i, j\right) \cdot \left(1 - \operatorname{Real.exp}\left(-(\beta_{b} \cdot \left(E\left(j\right) - E\left(i\right)\right))\right)\right) < a\left(i, k\right) \cdot \left(1 + \frac{\operatorname{Real.exp}\left(-(\beta_{b} \cdot \left(E\left(j\right) - E\left(i\right)\right))\right) \cdot \operatorname{Real.exp}\left(-(\beta_{b} \cdot \left(E\left(k\right) - E\left(j\right)\right))\right)}{2}\right) - a\left(j, k\right) \cdot \left(1 + \frac{\operatorname{Real.exp}\left(-(\beta_{b} \cdot \left(E\left(k\right) - E\left(j\right)\right))\right)}{2}\right))) \lor ((\frac{a\left(i, k\right) + a\left(j, k\right)}{a\left(i, j\right) \cdot \left(1 + \operatorname{Real.exp}\left(-(\beta_{b} \cdot \left(E\left(j\right) - E\left(i\right)\right))\right)\right)} \le 1) \land (a\left(j, k\right) < a\left(i, k\right) \cdot \operatorname{Real.exp}\left(-(\beta_{b} \cdot \left(E\left(j\right) - E\left(i\right)\right))\right)))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/MarkovMpembaTripletRefutation.TripletCondition` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ido Avitan; Roee Factor; David Gelbwaser-Klimovsky (2026). *Necessary conditions for the Markovian Mpemba effect*. URL: <https://arxiv.org/abs/2603.04567v1>.

*Commentary.*

For ordered indices i < j < k, identify the lowest, middle and highest levels with i, j and k. Write x = exp(−βb(E(j) − E(i))), y = exp(−βb(E(k) − E(j))) and κ = (a(i,k) + a(j,k))/(a(i,j)(1 + x)); the displayed condition substitutes these expressions. The first alternative of condition (3) uses κ ≥ 1 and the second uses κ ≤ 1. At κ = 1 either strict inequality suffices. Every triplet uses the original rates a, without recalculating rates after removing other levels. Ordering of the indices is required by the conjecture, rather than by this definition.

**Definition 1.4 (A simple slowest nonzero mode).**

$$\forall (N: \mathbb{N}), (\forall (M: \operatorname{Matrix}\left(\operatorname{Fin}\left(N\right), \operatorname{Fin}\left(N\right), \mathbb{R}\right)), (\forall (\lambda: \mathbb{R}), (\forall (\ell: \operatorname{Fin}\left(N\right) \to \mathbb{R}), ((\operatorname{IsSlowMode}\left(M, \lambda, \ell\right)) \Leftrightarrow ((\lambda < 0) \land ((\ell \ne 0) \land ((\operatorname{Matrix.vecMul}\left(\ell, M\right) = \lambda \cdot \ell) \land ((\forall (\mu: \mathbb{R}), (\forall (v: \operatorname{Fin}\left(N\right) \to \mathbb{R}), ((v \ne 0) \Rightarrow ((\operatorname{Matrix.mulVec}\left(M, v\right) = \mu \cdot v) \Rightarrow ((\mu = 0) \lor (\mu \le \lambda)))))) \land (\forall (v: \operatorname{Fin}\left(N\right) \to \mathbb{R}), ((\operatorname{Matrix.vecMul}\left(v, M\right) = \lambda \cdot v) \Rightarrow (\exists (c: \mathbb{R}), (v = c \cdot \ell))))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/MarkovMpembaTripletRefutation.IsSlowMode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ido Avitan; Roee Factor; David Gelbwaser-Klimovsky (2026). *Necessary conditions for the Markovian Mpemba effect*. URL: <https://arxiv.org/abs/2603.04567v1>.

*Commentary.*

The number λ is negative and ℓ is a nonzero left eigenvector. Every real eigenvalue of M is zero or at most λ, and every left eigenvector at λ is a scalar multiple of ℓ. Matrix.vecMul is multiplication of a row vector by a matrix; Matrix.mulVec multiplies a matrix by a column vector. The dot denotes scalar multiplication in the eigenvector equations. For a detailed-balance rate matrix these conditions select the slowest nonzero mode in the decomposition (2), with a one-dimensional left eigenspace. Its coefficient for an initial Gibbs state is ℓ dotted with that state, up to a fixed nonzero normalization.

**Definition 1.5 (A smaller slow-mode coefficient farther from the bath).**

$$\forall (N: \mathbb{N}), (\forall (E: \operatorname{Fin}\left(N\right) \to \mathbb{R}), (\forall (\beta_{b}: \mathbb{R}), (\forall (\ell: \operatorname{Fin}\left(N\right) \to \mathbb{R}), ((\operatorname{MpembaEffect}\left(E, \beta_{b}, \ell\right)) \Leftrightarrow (\exists (\beta_{1}: \mathbb{R}), (\exists (\beta_{2}: \mathbb{R}), ((((0 < \beta_{1}) \land ((\beta_{1} < \beta_{2}) \land (\beta_{2} < \beta_{b}))) \lor ((\beta_{b} < \beta_{2}) \land (\beta_{2} < \beta_{1}))) \land (\left|\operatorname{dotProduct}\left(\ell, \operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.gibbs}\left(E, \beta_{1}\right)\right)\right| < \left|\operatorname{dotProduct}\left(\ell, \operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.gibbs}\left(E, \beta_{2}\right)\right)\right|))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/MarkovMpembaTripletRefutation.MpembaEffect` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ido Avitan; Roee Factor; David Gelbwaser-Klimovsky (2026). *Necessary conditions for the Markovian Mpemba effect*. URL: <https://arxiv.org/abs/2603.04567v1>.

*Commentary.*

There are two initial inverse temperatures on the same side of βb. The first is farther from the bath and has a strictly smaller absolute slow-mode coefficient than the second. The first alternative describes cooling, with 0 < β₁ < β₂ < βb; the second describes heating, with βb < β₂ < β₁. These are exactly the two alternatives in the definition. The coefficient uses the Gibbs distribution GlauberRelaxationOrderRefutation.gibbs, whose formula is:

$$
\forall (N: \mathbb{N}), (\forall (E: \operatorname{Fin}\left(N\right) \to \mathbb{R}), (\forall (\beta: \mathbb{R}), (\forall (i: \operatorname{Fin}\left(N\right)), (\operatorname{D5.S3.StatisticalMechanics.GlauberRelaxationOrderRefutation.gibbs}\left(E, \beta\right)\left(i\right) = \frac{\operatorname{Real.exp}\left(-(\beta) \cdot E\left(i\right)\right)}{\sum_{(j: \operatorname{Fin}\left(N\right))} (\operatorname{Real.exp}\left(-(\beta) \cdot E\left(j\right)\right))}))))
$$

The denominator normalizes the Boltzmann weights over all N states. The dot product in the preceding statement sums ℓ(i) times the Gibbs probability of i. For the simple slow mode of Eq. (2), comparing these absolute dot products compares the absolute coefficients independently of the eigenvector normalization.

**Definition 1.6 (The finite-temperature triplet conjecture).**

$$(\operatorname{claim}) \Leftrightarrow (\forall (N: \mathbb{N}), (\forall (E: \operatorname{Fin}\left(N\right) \to \mathbb{R}), (\forall (\beta_{b}: \mathbb{R}), (\forall (a: \operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \mathbb{R}\right)), ((3 \le N) \Rightarrow ((\operatorname{StrictMono}\left(E\right)) \Rightarrow ((0 < \beta_{b}) \Rightarrow ((\forall (i: \operatorname{Fin}\left(N\right)), (\forall (j: \operatorname{Fin}\left(N\right)), ((i \ne j) \Rightarrow (0 < a\left(i, j\right))))) \Rightarrow ((\operatorname{DetailedBalance}\left(E, \beta_{b}, a\right)) \Rightarrow ((\forall (i: \operatorname{Fin}\left(N\right)), (\forall (j: \operatorname{Fin}\left(N\right)), (\forall (k: \operatorname{Fin}\left(N\right)), ((i < j) \Rightarrow ((j < k) \Rightarrow (\neg (\operatorname{TripletCondition}\left(E, \beta_{b}, a, i, j, k\right)))))))) \Rightarrow (\forall (\lambda: \mathbb{R}), (\forall (\ell: \operatorname{Fin}\left(N\right) \to \mathbb{R}), ((\operatorname{IsSlowMode}\left(\operatorname{generator}\left(a\right), \lambda, \ell\right)) \Rightarrow (\neg (\operatorname{MpembaEffect}\left(E, \beta_{b}, \ell\right))))))))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/MarkovMpembaTripletRefutation.claim` (`✓ std3`).

*Citation.* Ido Avitan; Roee Factor; David Gelbwaser-Klimovsky (2026). *Necessary conditions for the Markovian Mpemba effect*. URL: <https://arxiv.org/abs/2603.04567v1>.

*Commentary.*

The conjecture on page 4 asserts that failure of condition (3) in every triplet excludes the Mpemba effect in the full system. Here N is at least three, E is strictly increasing, the bath inverse temperature is positive, and all rates between distinct levels are positive and satisfy detailed balance. StrictMono E means E(i) < E(j) whenever i < j. For every ordered triplet neither alternative of condition (3) holds. The conclusion excludes the two-temperature effect for every simple slowest nonzero mode of the full rate matrix.

**Theorem 1.7 (Four levels with no qualifying triplet and a Mpemba effect).**

$$\neg (\operatorname{claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/MarkovMpembaTripletRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/avitan-factor-gelbwaser-klimovsky-2026-mpemba-triplet-conjecture` (refuted) by `D5/S3/StatisticalMechanics/MarkovMpembaTripletRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"avitan-factor-gelbwaser-klimovsky-2026-mpemba-triplet-conjecture","declaration_gid":"D5/S3/StatisticalMechanics/MarkovMpembaTripletRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ido Avitan; Roee Factor; David Gelbwaser-Klimovsky (2026). *Necessary conditions for the Markovian Mpemba effect*. URL: <https://arxiv.org/abs/2603.04567v1>.

*Commentary.*

Take four levels with energies E = (0,1,2,64)·log 16 and bath inverse temperature βb = 1. Put r = 16⁻⁶⁴ and μ = 2(125 + 1024r)/(15(273 + 256r)). Then 0 < r ≤ 1/4096 and 3/50 < μ < 1/16. Define A = 47/48 − μ − 112r/25, B = 3/2 − 3μ/2 − 128r/25, and C = 31/20 − 15μ/8. The rate array, with rows and columns ordered 0,1,2,3, is [[0,A,B,C],[A/16,0,1,3/5],[B/256,1/16,0,1/10],[Cr,48r/5,128r/5,0]]. All its off-diagonal entries are positive. The unnormalized bath weights w = (1,1/16,1/256,r) satisfy a(i,j)w(j) = a(j,i)w(i), giving detailed balance.

For each of the four triplets (0,1,2), (0,1,3), (0,2,3) and (1,2,3), put x = w(j)/w(i) and y = w(k)/w(j). Direct substitution gives a(i,k)(1 + xy/2) − a(j,k)(1 + y/2) ≤ a(i,j)(1 − x) and a(i,k)x ≤ a(j,k). Thus both strict rate inequalities in (3) fail in every triplet, regardless of which side of 1 contains κ = (a(i,k) + a(j,k))/(a(i,j)(1 + x)).

Set g = (0,1,2/3,8/15), let 1 denote the vector with every entry one, and put ℓ = g − μ1. For M = generator(a), one has 1ᵀM = 0, ℓᵀM = −ℓᵀ and Mw = 0. The remaining real eigenvalues lie below −2. To see the bound, restrict M to K = {v : Σᵢv(i) = 0 and g·v = 0}, with basis (1,2,−3,0), (7,8,0,−15). Its two-by-two matrix has trace t = (−50823168r² − 60948224r − 9618245)/(7680(256r + 273)) < −4. For its characteristic polynomial p(z) = z² − tz + d, where d is its determinant, p(−2) = (6914360475648r⁴ + 14183493009408r³ + 7535913889792r² + 274800737600r + 4382303125)/(960000(256r + 273)²) > 0. If z ≥ −2, then p(z) = p(−2) + (z + 2)(z − 2 − t) > 0. Every real eigenvalue other than 0 and −1 is a root of this polynomial, hence is below −2.

Also p(−1) = (274752r + 59225)(12582912r³ + 26058752r² + 14458848r + 995875)/(480000(256r + 273)²) > 0. A left eigenvector at −1 is orthogonal to w and to both displayed basis vectors of K. These constraints make it a scalar multiple of ℓ. Thus −1 is the simple slowest nonzero mode.

For x > 0, write β = log(x⁻¹)/log 16, so 16^(−β) = x. The Gibbs probabilities are (1,x,x²,x⁶⁴)/(1 + x + x² + x⁶⁴), and their coefficient along ℓ is (x + (2/3)x² + (8/15)x⁶⁴)/(1 + x + x² + x⁶⁴) − μ. Choose β₁ = log(1024/1023)/log 16 and β₂ = log(128/127)/log 16. Then 0 < β₁ < β₂ < 1, with x₁ = 1023/1024 and x₂ = 127/128. The displayed rational expression before subtracting μ is greater than 1/16 at x₁ and strictly larger at x₂. Since μ < 1/16, both coefficients are positive and the hotter initial state, β₁, has the smaller absolute coefficient. This gives a Mpemba effect although all four triplets fail (3), contradicting the conjecture.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/MarkovMpembaTripletRefutation.DetailedBalance`
- Truth anchor: `D5/S3/StatisticalMechanics/MarkovMpembaTripletRefutation.IsSlowMode`
- Truth anchor: `D5/S3/StatisticalMechanics/MarkovMpembaTripletRefutation.MpembaEffect`
- Truth anchor: `D5/S3/StatisticalMechanics/MarkovMpembaTripletRefutation.TripletCondition`
- Truth anchor: `D5/S3/StatisticalMechanics/MarkovMpembaTripletRefutation.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/MarkovMpembaTripletRefutation.generator`
- Truth anchor: `D5/S3/StatisticalMechanics/MarkovMpembaTripletRefutation.result`
- Dependency: [D5/S3/StatisticalMechanics/GlauberRelaxationOrderRefutation](GlauberRelaxationOrderRefutation.md)
