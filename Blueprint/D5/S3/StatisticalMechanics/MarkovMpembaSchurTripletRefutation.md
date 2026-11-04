# A four-level counterexample to the static Schur-reduced triplet test

## Abstract

Four reversible energy levels exhibit the Mpemba effect although every original and every statically Schur-reduced triplet fails the three-level condition.

The rate matrix, detailed balance, condition (3), the simple slowest mode and the two-temperature Mpemba effect are the frozen definitions of MarkovMpembaTripletRefutation. There a(i,j) is the rate from j to i on the states Fin N. This module changes only the rates seen by a triplet: instead of the original rates, a triplet may use the rates of the three-level system obtained by statically eliminating the remaining level.

**Definition 1.1 (Static Schur elimination of one level).**

$$\forall (N: \mathbb{N}), (\forall (a: \operatorname{Fin}\left(N\right) \to \left(\operatorname{Fin}\left(N\right) \to \mathbb{R}\right)), (\forall (s: \operatorname{Fin}\left(N\right)), (\forall (i: \operatorname{Fin}\left(N\right)), (\forall (j: \operatorname{Fin}\left(N\right)), (\operatorname{schurRates}\left(a, s, i, j\right) = \operatorname{D5.S3.StatisticalMechanics.MarkovMpembaTripletRefutation.generator}\left(a, i, j\right) - \frac{\operatorname{D5.S3.StatisticalMechanics.MarkovMpembaTripletRefutation.generator}\left(a, i, s\right) \cdot \operatorname{D5.S3.StatisticalMechanics.MarkovMpembaTripletRefutation.generator}\left(a, s, j\right)}{\operatorname{D5.S3.StatisticalMechanics.MarkovMpembaTripletRefutation.generator}\left(a, s, s\right)})))))$$

*Formalization.* `D5/S3/StatisticalMechanics/MarkovMpembaSchurTripletRefutation.schurRates` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ido Avitan; Roee Factor; David Gelbwaser-Klimovsky (2026). *Necessary conditions for the Markovian Mpemba effect*. URL: <https://arxiv.org/abs/2603.04567v1>.

*Commentary.*

Write M = generator(a). The entries are those of the Schur complement M_TT − M_Ts M_ss⁻¹ M_sT of the one-by-one block at s, the elimination of s from the stationary equations with M_ss = −d_s and d_s the total rate leaving s. For distinct i, j different from s the reduced rate from j to i is a(i,j) + a(i,s)a(s,j)/d_s: the direct rate plus the rate of passing through s. Only these entries enter condition (3) for a triplet avoiding s. The elimination is static: it is the Schur complement at eigenvalue zero, which preserves the equilibrium weights but not the slow eigenvalue equation.

**Definition 1.2 (The static Schur-reduced triplet implication).**

$$(\operatorname{claim}) \Leftrightarrow (\forall (E: \operatorname{Fin}\left(4\right) \to \mathbb{R}), (\forall (\beta_{b}: \mathbb{R}), (\forall (a: \operatorname{Fin}\left(4\right) \to \left(\operatorname{Fin}\left(4\right) \to \mathbb{R}\right)), ((\operatorname{StrictMono}\left(E\right)) \Rightarrow ((0 < \beta_{b}) \Rightarrow ((\forall (i: \operatorname{Fin}\left(4\right)), (\forall (j: \operatorname{Fin}\left(4\right)), ((i \ne j) \Rightarrow (0 < a\left(i, j\right))))) \Rightarrow ((\operatorname{D5.S3.StatisticalMechanics.MarkovMpembaTripletRefutation.DetailedBalance}\left(E, \beta_{b}, a\right)) \Rightarrow ((\forall (i: \operatorname{Fin}\left(4\right)), (\forall (j: \operatorname{Fin}\left(4\right)), (\forall (k: \operatorname{Fin}\left(4\right)), ((i < j) \Rightarrow ((j < k) \Rightarrow (\neg (\operatorname{D5.S3.StatisticalMechanics.MarkovMpembaTripletRefutation.TripletCondition}\left(E, \beta_{b}, a, i, j, k\right)))))))) \Rightarrow ((\forall (s: \operatorname{Fin}\left(4\right)), (\forall (i: \operatorname{Fin}\left(4\right)), (\forall (j: \operatorname{Fin}\left(4\right)), (\forall (k: \operatorname{Fin}\left(4\right)), ((i < j) \Rightarrow ((j < k) \Rightarrow ((s \ne i) \Rightarrow ((s \ne j) \Rightarrow ((s \ne k) \Rightarrow (\neg (\operatorname{D5.S3.StatisticalMechanics.MarkovMpembaTripletRefutation.TripletCondition}\left(E, \beta_{b}, \operatorname{schurRates}\left(a, s\right), i, j, k\right)))))))))))) \Rightarrow (\forall (\lambda: \mathbb{R}), (\forall (\ell: \operatorname{Fin}\left(4\right) \to \mathbb{R}), ((\operatorname{D5.S3.StatisticalMechanics.MarkovMpembaTripletRefutation.IsSlowMode}\left(\operatorname{D5.S3.StatisticalMechanics.MarkovMpembaTripletRefutation.generator}\left(a\right), \lambda, \ell\right)) \Rightarrow (\neg (\operatorname{D5.S3.StatisticalMechanics.MarkovMpembaTripletRefutation.MpembaEffect}\left(E, \beta_{b}, \ell\right)))))))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/MarkovMpembaSchurTripletRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Ido Avitan; Roee Factor; David Gelbwaser-Klimovsky (2026). *Necessary conditions for the Markovian Mpemba effect*. URL: <https://arxiv.org/abs/2603.04567v1>.

*Commentary.*

For four levels with strictly increasing energies, positive bath inverse temperature and positive detailed-balance rates, suppose that every ordered triplet fails condition (3) with the original rates, and that for every level s every ordered triplet of the other three levels fails condition (3) with the reduced rates schurRates(a, s). For four levels the complement of a triplet is the single level s, so these are all static Schur-reduced triplets. The claim concludes that no simple slowest mode of the full rate matrix shows the two-temperature Mpemba effect. Both families of triplet hypotheses are assumed, so this implication is weaker than the one using reduced triplets alone, and a counterexample to it refutes both.

**Theorem 1.3 (Failed reduced triplets with a Mpemba effect).**

$$\neg (\operatorname{claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/MarkovMpembaSchurTripletRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ido Avitan; Roee Factor; David Gelbwaser-Klimovsky (2026). *Necessary conditions for the Markovian Mpemba effect*. URL: <https://arxiv.org/abs/2603.04567v1>.

*Commentary.*

The witness is the frozen four-level system of MarkovMpembaTripletRefutation: energies E = (0,1,2,64)·log 16, bath inverse temperature βb = 1, r = 16⁻⁶⁴, μ = 2(125 + 1024r)/(15(273 + 256r)), A = 47/48 − μ − 112r/25, B = 3/2 − 3μ/2 − 128r/25, C = 31/20 − 15μ/8, and the rate array [[0,A,B,C],[A/16,0,1,3/5],[B/256,1/16,0,1/10],[Cr,48r/5,128r/5,0]]. Its frozen lemmas give positivity, detailed balance with weights w = (1,1/16,1/256,r), failure of all four original triplets, the simple slowest mode −1 with left eigenvector ℓ = g − μ1 for g = (0,1,2/3,8/15), and a Mpemba effect at 16^(−β₁) = 1023/1024 and 16^(−β₂) = 127/128, where 0 < β₁ < β₂ < βb: the hotter initial state has the smaller slow-mode coefficient, a direct cooling effect.

The new facts concern the reduced triplets. Eliminating level s leaves one ordered triplet (i,j,k); the four cases are s = 3, 2, 1, 0 with triplets (0,1,2), (0,1,3), (0,2,3) and (1,2,3). With b = schurRates(a, s), x = w(j)/w(i) and y = w(k)/w(j), exact rational evaluation at r = 16⁻⁶⁴ gives b(i,k)(1 + xy/2) − b(j,k)(1 + y/2) ≤ b(i,j)(1 − x) and b(i,k)x ≤ b(j,k) in each case. The first differences are about −0.481, −0.043, −0.476 and −0.458, and the second about −0.912, −0.548, −0.130 and −0.106. Hence both strict inequalities of (3) fail for every reduced triplet, whichever side of 1 contains κ. All hypotheses of the claim hold while the Mpemba effect occurs, so the claim is false.

The static reduction sets the eigenvalue to zero in the elimination of the complement, which preserves equilibrium but changes the eigenvalue equation of the slow mode. The counterexample shows that this change can hide the effect from every three-level test.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/MarkovMpembaSchurTripletRefutation.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/MarkovMpembaSchurTripletRefutation.result`
- Truth anchor: `D5/S3/StatisticalMechanics/MarkovMpembaSchurTripletRefutation.schurRates`
- Dependency: [D5/S3/StatisticalMechanics/MarkovMpembaTripletRefutation](MarkovMpembaTripletRefutation.md)
