# The Kepler-Coulomb coefficient conjecture

## Abstract

For every natural m at least two, the Kepler-Coulomb coefficient system has a unique solution on indices zero through m, with positive constants in the conjectured closed forms.

The unknown coefficients form a function a from natural numbers to real numbers. Only its values at indices zero through m enter the system and the uniqueness conclusion. All index arithmetic, including subtraction in indices, factorial arguments and exponents, is natural-number arithmetic; subtraction is truncated at zero. Floors denote natural-number division by two. Explicit real type annotations denote casts. Empty sums are zero and empty products are one.

**Definition 1.1 (The coefficient equations).**

$$\forall (m: \mathbb{N}), (\forall (Q: \mathbb{R}), (\forall (\kappa: \mathbb{R}), (\forall (a: (\mathbb{N} \to \mathbb{R})), ((\operatorname{D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients.System}\left(m, Q, \kappa, a\right)) \Leftrightarrow ((((((m: \mathbb{R})) + (1)) \cdot (a\left(0\right))) - (a\left(1\right)) = 1) \land (((((((m: \mathbb{R})) \cdot (Q)) \cdot (a\left(0\right))) - ((Q) \cdot (a\left(1\right)))) - (\sum_{(k: \mathbb{N}) \in \operatorname{Finset.Icc}\left(1, \lfloor\frac{m}{2}\rfloor\right)} (a\left((2) \cdot (k)\right))) = 0) \land ((\forall (k: \mathbb{N}), ((k \in \operatorname{Finset.Icc}\left(1, \lfloor\frac{(m) - (1)}{2}\rfloor\right)) \Rightarrow ((((((m: \mathbb{R})) - ((2) \cdot ((k: \mathbb{R})))) \cdot (a\left((2) \cdot (k)\right))) - ((Q) \cdot (a\left(((2) \cdot (k)) + (1)\right)))) - (\sum_{(l: \mathbb{N}) \in \operatorname{Finset.Icc}\left((k) + (1), \lfloor\frac{m}{2}\rfloor\right)} (a\left((2) \cdot (l)\right))) = 0))) \land ((\forall (k: \mathbb{N}), ((k \in \operatorname{Finset.Icc}\left(1, (\lfloor\frac{m}{2}\rfloor) - (1)\right)) \Rightarrow (((((\kappa) \cdot ((((m: \mathbb{R})) + (1)) - ((2) \cdot ((k: \mathbb{R}))))) \cdot (a\left(((2) \cdot (k)) - (1)\right))) - ((Q) \cdot (a\left((2) \cdot (k)\right)))) - (((\kappa) \cdot ((((m: \mathbb{R})) + (1)) - ((2) \cdot ((k: \mathbb{R}))))) \cdot (a\left(((2) \cdot (k)) + (1)\right))) = 0))) \land (((\frac{(1) - (((-1: \mathbb{R}))^{m})}{2}) \cdot (((((2) \cdot (\kappa)) \cdot (a\left((m) - (2)\right))) - ((Q) \cdot (a\left((m) - (1)\right)))) - (((2) \cdot (\kappa)) \cdot (a\left(m\right))))) + ((\frac{(1) + (((-1: \mathbb{R}))^{m})}{2}) \cdot (((\kappa) \cdot (a\left((m) - (1)\right))) - ((Q) \cdot (a\left(m\right))))) = 0)))))))))$$

*Formalization.* `D5/S3/Quantum/Analysis/KeplerCoulombSphereQESCoefficients.System` (`✓ std3`).

*Citation.* C. Quesne (2023). *Quasi-exactly solvable extensions of the Kepler-Coulomb potential on the sphere*. DOI: [10.1016/j.aop.2023.169265](https://doi.org/10.1016/j.aop.2023.169265). URL: <https://arxiv.org/abs/2206.01033v3>.

*Commentary.*

Equations (4.13)-(4.17) give two initial equations, two indexed families and a final equation selected by the parity of m. The interval sums use Finset.Icc, including both endpoints.

**Definition 1.2 (A homogeneous polynomial bracket).**

$$\forall (n: \mathbb{N}), (\forall (d: (\mathbb{N} \to \mathbb{R})), (\forall (Q: \mathbb{R}), (\forall (\kappa: \mathbb{R}), (\operatorname{D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients.series}\left(n, d, Q, \kappa\right) = ((Q)^{(2) \cdot (n)}) + (\sum_{(j: \mathbb{N}) \in \operatorname{Finset.Icc}\left(1, n\right)} (((d\left(j\right)) \cdot ((\kappa)^{j})) \cdot ((Q)^{(2) \cdot ((n) - (j))})))))))$$

*Formalization.* `D5/S3/Quantum/Analysis/KeplerCoulombSphereQESCoefficients.series` (`✓ std3`).

*Citation.* C. Quesne (2023). *Quasi-exactly solvable extensions of the Kepler-Coulomb potential on the sphere*. DOI: [10.1016/j.aop.2023.169265](https://doi.org/10.1016/j.aop.2023.169265). URL: <https://arxiv.org/abs/2206.01033v3>.

*Commentary.*

The leading term is Q to the power 2n. The remaining terms have coefficients d j, with j ranging from one through n, and are homogeneous in Q squared and curvature.

**Definition 1.3 (The common denominator).**

$$\forall (\mu: \mathbb{N}), (\forall (b: (\mathbb{N} \to \mathbb{R})), (\forall (Q: \mathbb{R}), (\forall (\kappa: \mathbb{R}), (\operatorname{D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients.delta}\left(\mu, b, Q, \kappa\right) = \operatorname{D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients.series}\left(\mu, b, Q, \kappa\right)))))$$

*Formalization.* `D5/S3/Quantum/Analysis/KeplerCoulombSphereQESCoefficients.delta` (`✓ std3`).

*Citation.* C. Quesne (2023). *Quasi-exactly solvable extensions of the Kepler-Coulomb potential on the sphere*. DOI: [10.1016/j.aop.2023.169265](https://doi.org/10.1016/j.aop.2023.169265). URL: <https://arxiv.org/abs/2206.01033v3>.

*Commentary.*

The denominator in (4.19)-(4.24) is the bracket of degree mu with coefficients b.

**Definition 1.4 (The closed forms for odd m).**

$$\forall (\mu: \mathbb{N}), (\forall (Q: \mathbb{R}), (\forall (\kappa: \mathbb{R}), (\forall (b: (\mathbb{N} \to \mathbb{R})), (\forall (c: (\mathbb{N} \to \left(\mathbb{N} \to \mathbb{R}\right))), (\forall (a: (\mathbb{N} \to \mathbb{R})), ((\operatorname{D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients.OddForm}\left(\mu, Q, \kappa, b, c, a\right)) \Leftrightarrow ((a\left(0\right) = \frac{\prod_{(r: \mathbb{N}) \in \operatorname{Finset.range}\left(\mu\right)} (((Q)^{2}) + (((4) \cdot ((((r: \mathbb{R})) + (1))^{2})) \cdot (\kappa)))}{\operatorname{D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients.delta}\left(\mu, b, Q, \kappa\right)}) \land ((\forall (k: \mathbb{N}), ((1 \le k) \Rightarrow ((k \le \mu) \Rightarrow (a\left((2) \cdot (k)\right) = \frac{(((\frac{(\operatorname{Nat.factorial}\left(((2) \cdot (\mu)) + (1)\right): \mathbb{R})}{(\operatorname{Nat.factorial}\left((((2) \cdot (\mu)) - ((2) \cdot (k))) + (1)\right): \mathbb{R})}) \cdot ((\kappa)^{k})) \cdot (Q)) \cdot (\prod_{(r: \mathbb{N}) \in \operatorname{Finset.range}\left((\mu) - (k)\right)} (((Q)^{2}) + (((4) \cdot ((((r: \mathbb{R})) + (1))^{2})) \cdot (\kappa))))}{\operatorname{D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients.delta}\left(\mu, b, Q, \kappa\right)})))) \land (\forall (k: \mathbb{N}), ((k \le \mu) \Rightarrow (a\left(((2) \cdot (k)) + (1)\right) = \frac{((\frac{(\operatorname{Nat.factorial}\left(((2) \cdot (\mu)) + (1)\right): \mathbb{R})}{(\operatorname{Nat.factorial}\left(((2) \cdot (\mu)) - ((2) \cdot (k))\right): \mathbb{R})}) \cdot ((\kappa)^{k})) \cdot (\operatorname{D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients.series}\left((\mu) - (k), c\left(k\right), Q, \kappa\right))}{\operatorname{D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients.delta}\left(\mu, b, Q, \kappa\right)})))))))))))$$

*Formalization.* `D5/S3/Quantum/Analysis/KeplerCoulombSphereQESCoefficients.OddForm` (`✓ std3`).

*Citation.* C. Quesne (2023). *Quasi-exactly solvable extensions of the Kepler-Coulomb potential on the sphere*. DOI: [10.1016/j.aop.2023.169265](https://doi.org/10.1016/j.aop.2023.169265). URL: <https://arxiv.org/abs/2206.01033v3>.

*Commentary.*

Equations (4.19)-(4.21) describe the coefficients when m equals 2mu + 1. The factors in the products are Q squared plus 4(r + 1) squared times curvature. The factorials are natural-number factorials cast to real numbers before division.

**Definition 1.5 (The closed forms for even m).**

$$\forall (\mu: \mathbb{N}), (\forall (Q: \mathbb{R}), (\forall (\kappa: \mathbb{R}), (\forall (b: (\mathbb{N} \to \mathbb{R})), (\forall (c: (\mathbb{N} \to \left(\mathbb{N} \to \mathbb{R}\right))), (\forall (a: (\mathbb{N} \to \mathbb{R})), ((\operatorname{D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients.EvenForm}\left(\mu, Q, \kappa, b, c, a\right)) \Leftrightarrow ((a\left(0\right) = \frac{\prod_{(r: \mathbb{N}) \in \operatorname{Finset.range}\left(\mu\right)} (((Q)^{2}) + (((((2) \cdot ((r: \mathbb{R}))) + (1))^{2}) \cdot (\kappa)))}{\operatorname{D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients.delta}\left(\mu, b, Q, \kappa\right)}) \land ((\forall (k: \mathbb{N}), ((1 \le k) \Rightarrow ((k \le \mu) \Rightarrow (a\left((2) \cdot (k)\right) = \frac{(((\frac{(\operatorname{Nat.factorial}\left((2) \cdot (\mu)\right): \mathbb{R})}{(\operatorname{Nat.factorial}\left(((2) \cdot (\mu)) - ((2) \cdot (k))\right): \mathbb{R})}) \cdot ((\kappa)^{k})) \cdot (Q)) \cdot (\prod_{(r: \mathbb{N}) \in \operatorname{Finset.range}\left((\mu) - (k)\right)} (((Q)^{2}) + (((((2) \cdot ((r: \mathbb{R}))) + (1))^{2}) \cdot (\kappa))))}{\operatorname{D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients.delta}\left(\mu, b, Q, \kappa\right)})))) \land (\forall (k: \mathbb{N}), ((k < \mu) \Rightarrow (a\left(((2) \cdot (k)) + (1)\right) = \frac{(((\frac{(\operatorname{Nat.factorial}\left((2) \cdot (\mu)\right): \mathbb{R})}{(\operatorname{Nat.factorial}\left((((2) \cdot (\mu)) - ((2) \cdot (k))) - (1)\right): \mathbb{R})}) \cdot ((\kappa)^{k})) \cdot ((Q)^{2})) \cdot (\operatorname{D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients.series}\left(((\mu) - (k)) - (1), c\left(k\right), Q, \kappa\right))}{\operatorname{D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients.delta}\left(\mu, b, Q, \kappa\right)})))))))))))$$

*Formalization.* `D5/S3/Quantum/Analysis/KeplerCoulombSphereQESCoefficients.EvenForm` (`✓ std3`).

*Citation.* C. Quesne (2023). *Quasi-exactly solvable extensions of the Kepler-Coulomb potential on the sphere*. DOI: [10.1016/j.aop.2023.169265](https://doi.org/10.1016/j.aop.2023.169265). URL: <https://arxiv.org/abs/2206.01033v3>.

*Commentary.*

Equations (4.22)-(4.24) describe the coefficients when m equals 2mu. Here the product factors are Q squared plus (2r + 1) squared times curvature, and the odd-index numerator includes a factor Q squared.

**Definition 1.6 (The two parity cases).**

$$\forall (m: \mathbb{N}), (\forall (Q: \mathbb{R}), (\forall (\kappa: \mathbb{R}), (\forall (b: (\mathbb{N} \to \mathbb{R})), (\forall (c: (\mathbb{N} \to \left(\mathbb{N} \to \mathbb{R}\right))), (\forall (a: (\mathbb{N} \to \mathbb{R})), ((\operatorname{D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients.ClosedForms}\left(m, Q, \kappa, b, c, a\right)) \Leftrightarrow (((\operatorname{Nat.mod}\left(m, 2\right) = 1) \Rightarrow (\operatorname{D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients.OddForm}\left(\lfloor\frac{m}{2}\rfloor, Q, \kappa, b, c, a\right))) \land ((\operatorname{Nat.mod}\left(m, 2\right) = 0) \Rightarrow (\operatorname{D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients.EvenForm}\left(\lfloor\frac{m}{2}\rfloor, Q, \kappa, b, c, a\right))))))))))$$

*Formalization.* `D5/S3/Quantum/Analysis/KeplerCoulombSphereQESCoefficients.ClosedForms` (`✓ std3`).

*Citation.* C. Quesne (2023). *Quasi-exactly solvable extensions of the Kepler-Coulomb potential on the sphere*. DOI: [10.1016/j.aop.2023.169265](https://doi.org/10.1016/j.aop.2023.169265). URL: <https://arxiv.org/abs/2206.01033v3>.

*Commentary.*

The remainder m modulo two chooses the odd or even formulas, with mu equal to the floor of m divided by two.

**Definition 1.7 (Positivity of the bracket coefficients).**

$$\forall (m: \mathbb{N}), (\forall (b: (\mathbb{N} \to \mathbb{R})), (\forall (c: (\mathbb{N} \to \left(\mathbb{N} \to \mathbb{R}\right))), ((\operatorname{D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients.PositiveConstants}\left(m, b, c\right)) \Leftrightarrow ((\forall (j: \mathbb{N}), ((j \in \operatorname{Finset.Icc}\left(1, \lfloor\frac{m}{2}\rfloor\right)) \Rightarrow (0 < b\left(j\right)))) \land (\forall (k: \mathbb{N}), ((k \le \lfloor\frac{(m) - (1)}{2}\rfloor) \Rightarrow (\forall (j: \mathbb{N}), ((j \in \operatorname{Finset.Icc}\left(1, (\lfloor\frac{(m) - (1)}{2}\rfloor) - (k)\right)) \Rightarrow (0 < c\left(k, j\right))))))))))$$

*Formalization.* `D5/S3/Quantum/Analysis/KeplerCoulombSphereQESCoefficients.PositiveConstants` (`✓ std3`).

*Citation.* C. Quesne (2023). *Quasi-exactly solvable extensions of the Kepler-Coulomb potential on the sphere*. DOI: [10.1016/j.aop.2023.169265](https://doi.org/10.1016/j.aop.2023.169265). URL: <https://arxiv.org/abs/2206.01033v3>.

*Commentary.*

The constants b j are positive for one through the floor of m divided by two. For each admissible k, the constants c k j are positive throughout the degree of its bracket. Values of b and c outside these ranges are unrestricted.

**Definition 1.8 (Quesne's coefficient conjecture).**

$$(\operatorname{D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients.claim}) \Leftrightarrow (\forall (m: \mathbb{N}), ((2 \le m) \Rightarrow (\exists (b: (\mathbb{N} \to \mathbb{R})), (\exists (c: (\mathbb{N} \to \left(\mathbb{N} \to \mathbb{R}\right))), ((\operatorname{D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients.PositiveConstants}\left(m, b, c\right)) \land (\forall (Q: \mathbb{R}), (\forall (\kappa: \mathbb{R}), ((0 < Q) \Rightarrow ((0 < \kappa) \Rightarrow ((\exists (a: (\mathbb{N} \to \mathbb{R})), (\operatorname{D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients.System}\left(m, Q, \kappa, a\right))) \land ((\forall (a: (\mathbb{N} \to \mathbb{R})), ((\operatorname{D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients.System}\left(m, Q, \kappa, a\right)) \Rightarrow (\operatorname{D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients.ClosedForms}\left(m, Q, \kappa, b, c, a\right)))) \land (\forall (a: (\mathbb{N} \to \mathbb{R})), (\forall (a': (\mathbb{N} \to \mathbb{R})), ((\operatorname{D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients.System}\left(m, Q, \kappa, a\right)) \Rightarrow ((\operatorname{D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients.System}\left(m, Q, \kappa, a'\right)) \Rightarrow (\forall (i: \mathbb{N}), ((i \le m) \Rightarrow (a\left(i\right) = a'\left(i\right)))))))))))))))))))$$

*Formalization.* `D5/S3/Quantum/Analysis/KeplerCoulombSphereQESCoefficients.claim` (`✓ std3`).

*Citation.* C. Quesne (2023). *Quasi-exactly solvable extensions of the Kepler-Coulomb potential on the sphere*. DOI: [10.1016/j.aop.2023.169265](https://doi.org/10.1016/j.aop.2023.169265). URL: <https://arxiv.org/abs/2206.01033v3>.

*Commentary.*

For each m at least two, the positive constants can be chosen independently of Q and curvature. For every positive Q and curvature the system has a solution, every solution has the displayed closed forms, and any two solutions agree on zero through m. Q is the source's rescaled coupling and kappa is the curvature. Equation (4.18) is omitted because it is a combination of (4.13) and (4.14).

**Theorem 1.9 (Positive constants and the closed-form solution).**

$$\operatorname{D5.S3.Quantum.Analysis.KeplerCoulombSphereQESCoefficients.claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Analysis/KeplerCoulombSphereQESCoefficients.result` (`✓ std3`). ∎

*Resolves.* `Problems/quesne-2023-kepler-coulomb-qes-coefficient-conjecture` (proved) by `D5/S3/Quantum/Analysis/KeplerCoulombSphereQESCoefficients.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"quesne-2023-kepler-coulomb-qes-coefficient-conjecture","declaration_gid":"D5/S3/Quantum/Analysis/KeplerCoulombSphereQESCoefficients.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* C. Quesne (2023). *Quasi-exactly solvable extensions of the Kepler-Coulomb potential on the sphere*. DOI: [10.1016/j.aop.2023.169265](https://doi.org/10.1016/j.aop.2023.169265). URL: <https://arxiv.org/abs/2206.01033v3>.

*Commentary.*

Normalize with z = Q squared divided by curvature, dividing each positive even-index coefficient by Q. An explicit polynomial solution satisfies the normalized equations by telescoping identities. The recurrence forces every solution to be proportional to this polynomial solution, and the first equation fixes the proportionality constant. As polynomials in z, the common denominator of (4.19)-(4.24) and, for admissible k, the odd-index brackets have strictly positive coefficients through their degrees; for odd m each bracket is the normalized odd-index numerator, while for even m that numerator has zero constant term and the bracket is that numerator divided by z. Their coefficients give b and c, and evaluation at nonnegative z makes the denominator strictly positive. Rescaling by curvature yields the two families of factorial ratios, products and polynomial brackets.

## References

- Truth anchor: `D5/S3/Quantum/Analysis/KeplerCoulombSphereQESCoefficients.ClosedForms`
- Truth anchor: `D5/S3/Quantum/Analysis/KeplerCoulombSphereQESCoefficients.EvenForm`
- Truth anchor: `D5/S3/Quantum/Analysis/KeplerCoulombSphereQESCoefficients.OddForm`
- Truth anchor: `D5/S3/Quantum/Analysis/KeplerCoulombSphereQESCoefficients.PositiveConstants`
- Truth anchor: `D5/S3/Quantum/Analysis/KeplerCoulombSphereQESCoefficients.System`
- Truth anchor: `D5/S3/Quantum/Analysis/KeplerCoulombSphereQESCoefficients.claim`
- Truth anchor: `D5/S3/Quantum/Analysis/KeplerCoulombSphereQESCoefficients.delta`
- Truth anchor: `D5/S3/Quantum/Analysis/KeplerCoulombSphereQESCoefficients.result`
- Truth anchor: `D5/S3/Quantum/Analysis/KeplerCoulombSphereQESCoefficients.series`
- Dependency: [D5/S3/Constants/NewtonHankelRealRootCriterion](../../Constants/NewtonHankelRealRootCriterion.md)
- Dependency: [D5/S3/Zeros/Convolution/AlternatingFactorialSum](../../Zeros/Convolution/AlternatingFactorialSum.md)
