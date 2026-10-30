# Rational collision densities of bracket expressions

## Abstract

Every finite rational-modulus bracket expression has an existing rational collision density.

Section 1 of Larsson–Manabe defines a bracket expression using finitely many integer coefficients and positive rational moduli. Section 7, Question 20(iii), separately asks whether its collision density is always rational. The result here answers that rationality question, including existence of the limit. The other characterisation, closed-form and game questions are outside its scope.

**Definition 1.1 (A finite rational floor sum).**

$$\forall t \in \mathbb{N},\; \forall c \in \operatorname{Fin}\left(t\right) \to \mathbb{Z},\; \forall alpha \in \operatorname{Fin}\left(t\right) \to \mathbb{Q},\; \forall n \in \mathbb{N},\; \operatorname{bracket}\left(c, alpha, n\right) = \operatorname{Finset}.\operatorname{sum}\left((\operatorname{Finset}.\operatorname{univ}: \operatorname{Finset}\left(\operatorname{Fin}\left(t\right)\right)), (\operatorname{fun} (i: \operatorname{Fin}\left(t\right)) \mapsto c\left(i\right) \cdot \operatorname{Int}.\operatorname{floor}\left(((n: \mathbb{Q}) \cdot alpha\left(i\right))\right))\right)$$

*Formalization.* `D5/S3/Arith/Density/RationalBracketCollisionDensity.bracket` (`✓ std3`).

*Citation.* Urban Larsson and Hikaru Manabe (2026). *Additive Subtraction Games*. DOI: [10.48550/arXiv.2603.10414](https://doi.org/10.48550/arXiv.2603.10414). URL: <https://arxiv.org/html/2603.10414v2#Thmthm20>.

*Commentary.*

The index n is natural and includes zero. Fin t includes the empty family at t=0. Coefficients may have either sign. Int.floor takes a rational argument and returns an integer; the sum is over all i in Fin t.

**Definition 1.2 (Distinct image values at a positive shift).**

$$\forall t \in \mathbb{N},\; \forall c \in \operatorname{Fin}\left(t\right) \to \mathbb{Z},\; \forall alpha \in \operatorname{Fin}\left(t\right) \to \mathbb{Q},\; \forall k \in \mathbb{N},\; \forall x \in \mathbb{N},\; (\operatorname{collision}\left(c, alpha, k, x\right)) \Leftrightarrow ((\exists n \in \mathbb{N},\; \operatorname{bracket}\left(c, alpha, n\right) = (x: \mathbb{Z})) \land (\exists n \in \mathbb{N},\; \operatorname{bracket}\left(c, alpha, n\right) = ((x + k): \mathbb{Z})))$$

*Formalization.* `D5/S3/Arith/Density/RationalBracketCollisionDensity.collision` (`✓ std3`).

*Citation.* Urban Larsson and Hikaru Manabe (2026). *Additive Subtraction Games*. DOI: [10.48550/arXiv.2603.10414](https://doi.org/10.48550/arXiv.2603.10414). URL: <https://arxiv.org/html/2603.10414v2#Thmthm20>.

*Commentary.*

Both existential witnesses range over the complete sequence. Their indices need not agree or be unique. The predicate is on a nonnegative integer x, so filtering a finite interval counts each image value only once, even when the sequence repeats.

**Definition 1.3 (The rationality subquestion).**

$$(\operatorname{claim}) \Leftrightarrow (\forall t \in \mathbb{N},\; \forall c \in \operatorname{Fin}\left(t\right) \to \mathbb{Z},\; \forall alpha \in \operatorname{Fin}\left(t\right) \to \mathbb{Q},\; (\forall i \in \operatorname{Fin}\left(t\right),\; 0 < alpha\left(i\right)) \Rightarrow (\forall k \in \mathbb{N},\; (0 < k) \Rightarrow (\exists a \in \mathbb{Q},\; \operatorname{Filter}.\operatorname{Tendsto}\left((\operatorname{fun} (N: \mathbb{N}) \mapsto \frac{(\operatorname{Finset}.\operatorname{card}\left((\operatorname{Finset}.\operatorname{filter}\left((\operatorname{collision}\left(c, alpha, k\right)), (\operatorname{Finset}.\operatorname{range}\left((N + 1)\right))\right))\right): \mathbb{R})}{(N: \mathbb{R})}), \operatorname{Filter}.\operatorname{atTop}, (\operatorname{nhds}\left((a: \mathbb{R})\right))\right))))$$

*Formalization.* `D5/S3/Arith/Density/RationalBracketCollisionDensity.claim` (`✓ std3`).

*Citation.* Urban Larsson and Hikaru Manabe (2026). *Additive Subtraction Games*. DOI: [10.48550/arXiv.2603.10414](https://doi.org/10.48550/arXiv.2603.10414). URL: <https://arxiv.org/html/2603.10414v2#Thmthm20>.

*Commentary.*

The source question asks: Is it always rational? The limit uses real division by N and the inclusive interval from zero to N. The value at N=0 does not affect the limit at infinity. The positivity premises apply to all rational moduli and to k; there is no monotonicity, injectivity, coefficient-sign or positive-drift premise.

**Theorem 1.4 (Existence and rationality).**

$$\forall t \in \mathbb{N},\; \forall c \in \operatorname{Fin}\left(t\right) \to \mathbb{Z},\; \forall alpha \in \operatorname{Fin}\left(t\right) \to \mathbb{Q},\; (\forall i \in \operatorname{Fin}\left(t\right),\; 0 < alpha\left(i\right)) \Rightarrow (\forall k \in \mathbb{N},\; (0 < k) \Rightarrow (\exists a \in \mathbb{Q},\; \operatorname{Filter}.\operatorname{Tendsto}\left((\operatorname{fun} (N: \mathbb{N}) \mapsto \frac{(\operatorname{Finset}.\operatorname{card}\left((\operatorname{Finset}.\operatorname{filter}\left((\operatorname{collision}\left(c, alpha, k\right)), (\operatorname{Finset}.\operatorname{range}\left((N + 1)\right))\right))\right): \mathbb{R})}{(N: \mathbb{R})}), \operatorname{Filter}.\operatorname{atTop}, (\operatorname{nhds}\left((a: \mathbb{R})\right))\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Density/RationalBracketCollisionDensity.result` (`✓ std3`). ∎

*Resolves.* `Problems/larsson-manabe-2026-rational-bracket-collision-density` (proved) by `D5/S3/Arith/Density/RationalBracketCollisionDensity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"larsson-manabe-2026-rational-bracket-collision-density","declaration_gid":"D5/S3/Arith/Density/RationalBracketCollisionDensity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Urban Larsson and Hikaru Manabe (2026). *Additive Subtraction Games*. DOI: [10.48550/arXiv.2603.10414](https://doi.org/10.48550/arXiv.2603.10414). URL: <https://arxiv.org/html/2603.10414v2#Thmthm20>.

*Commentary.*

Clearing the finitely many denominators constructs a positive index period q and an integer drift d. On each index residue the sequence is an affine ray. For positive drift, image membership is periodic beyond a bound; for nonpositive drift, the nonnegative image has an empty tail. Collision membership inherits eventual periodicity. EventualCycleAverage.eventual_cycle_average gives the average of the resulting finite indicator cycle. That average is rational. Shifting the count to N+1 and multiplying by (N+1)/N gives exactly the displayed normalization. This argument includes the empty expression and zero drift. The proof is repository-derived; the paper supplies the question and definitions.

## References

- Truth anchor: `D5/S3/Arith/Density/RationalBracketCollisionDensity.bracket`
- Truth anchor: `D5/S3/Arith/Density/RationalBracketCollisionDensity.claim`
- Truth anchor: `D5/S3/Arith/Density/RationalBracketCollisionDensity.collision`
- Truth anchor: `D5/S3/Arith/Density/RationalBracketCollisionDensity.result`
- Dependency: [D5/S3/ObserverMemory/Prediction/EventualCycleAverage](../../ObserverMemory/Prediction/EventualCycleAverage.md)
