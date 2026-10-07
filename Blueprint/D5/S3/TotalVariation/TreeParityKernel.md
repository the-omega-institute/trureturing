# Tree Parity Kernels

## Abstract

A complete gap parity record preserves the total variation between the actual and reference tree laws.

**Definition 1.1 (Composition parity mass).**

$$\forall d,M \in \mathbb{N}, \forall \xi, \operatorname{R}\left(d, M, \xi\right) = \operatorname{ite}\left((h \leq M) \land (\operatorname{mod}\left(h, 2\right) = \operatorname{mod}\left(M, 2\right)), \frac{\operatorname{choose}\left(\frac{M - h}{2} + d - 1, d - 1\right)}{\operatorname{choose}\left(M + d - 1, d - 1\right)}, 0\right)$$

*Formalization.* `D5/S3/TotalVariation/TreeParityKernel.R` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yaël Dillies, Bhavik Mehta, Huỳnh Trần Khanh, Stuart Presnell and Mathlib contributors (2026). *Mathlib.Data.Sym.Card — Stars and bars*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Data/Sym/Card.lean>.

*Commentary.*

The parameters d and M are natural numbers, xi : Fin d -> Bool, and h is the number of true coordinates of xi. The guard requires h <= M and h mod 2 = M mod 2. The mass is zero when either test fails; the binomial coefficient in the nonzero branch is evaluated only for the resulting natural parameters. For d>0, its numerator counts the weak compositions of M into d parts with parity vector xi. For d=0, the binomial expression is 1 and has no zero-dimensional weak-composition interpretation.

**Definition 1.2 (Conditioned Bernoulli mass).**

$$\forall d,M \in \mathbb{N}, \forall \xi, \operatorname{Q}\left(d, M, \xi\right) = \operatorname{ite}\left(\operatorname{mod}\left(h, 2\right) = \operatorname{mod}\left(M, 2\right), \frac{\nu^{h} \cdot (1 - \nu)^{d - h}}{p_{e}}, 0\right)$$

*Formalization.* `D5/S3/TotalVariation/TreeParityKernel.Q` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Kyle Siegrist (2026). *Random: Probability, Mathematical Statistics, Stochastic Processes*. URL: <https://www.randomservices.org/random/>.

*Commentary.*

The statistical-laws reference definition prescribes the bias nu = M/(2M+d). Here eta = d/(2M+d), and p_e = (1+(-1)^M eta^d)/2. The mass is zero when h mod 2 differs from M mod 2. For positive d and M, this formula describes independent Bernoulli(nu) bits conditioned on the terminal parity. The conditioned bits are not asserted to be independent. Both masses have exactly the form used by the finite parity bound. The Bernoulli parity computation follows Siegrist.

**Definition 1.3 (Shapes and complete gaps).**

$$\operatorname{Fiber}\left(a, b\right) \sim \operatorname{Shapes}\left(n - 1\right) \times \operatorname{WeakCompositions}\left(d, M\right)$$

*Formalization.* `D5/S3/TotalVariation/TreeParityKernel.intervals` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural a and b with a+b>=1, set n=a+b, k=min(a,b), M=max(a,b), and d=k+1. An actual ordered binary tree separates into its ordered shape and the complete gaps between its minority leaves. If a<=b, alpha leaves are the separators; otherwise beta leaves are the separators. The first and last gaps are included. The d nonnegative gap sizes sum to M. The separator positions, read left to right, correspond to a positive composition of n+1 into d blocks; subtracting one from every block gives the gap sizes, a weak composition of M into d parts. Adding one reverses this operation. All ordered shapes with n-1 internal nodes are retained.

**Definition 1.4 (Complete gap parity record).**

$$\operatorname{xi}\left(t, i\right) = \operatorname{decide}\left(\operatorname{mod}\left(r_{i}, 2\right) = 1\right)$$

*Formalization.* `D5/S3/TotalVariation/TreeParityKernel.gapParity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Boolean vector has one coordinate for every gap, including both outside gaps. Its occupied-coordinate count h is the number of true coordinates, and h mod 2 equals M mod 2.

**Definition 1.5 (Reference tree mass).**

$$\operatorname{V}\left(t\right) = \frac{\operatorname{Q}\left(d, M, \operatorname{xi}\left(t\right)\right)}{\operatorname{catalan}\left(n - 1\right) \cdot \operatorname{choose}\left(\frac{M - h}{2} + d - 1, d - 1\right)}$$

*Formalization.* `D5/S3/TotalVariation/TreeParityKernel.referenceTreeMass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Yaël Dillies, Bhavik Mehta, Huỳnh Trần Khanh, Stuart Presnell and Mathlib contributors (2026). *Mathlib.Data.Sym.Card — Stars and bars*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Data/Sym/Card.lean>.

*Acknowledgement.* Kyle Siegrist (2026). *Random: Probability, Mathematical Statistics, Stochastic Processes*. URL: <https://www.randomservices.org/random/>.

*Commentary.*

The actual tree law U is the uniform mass on Fiber(a,b). The reference mass uses the conditioned Bernoulli parity law Q and the actual uniform conditional law given the complete gap parity. For a legal parity vector, the denominator is the number of actual trees with that record: catalan(n-1) times choose((M-h)/2+d-1,d-1). The parity vector of an actual tree is always legal.

**Theorem 1.6 (Equal distance and two-sided event bounds).**

$$\forall a,b \in \mathbb{N}, ((1 \leq a + b) \land (d \leq M)) \Rightarrow (\operatorname{pushforward}\left(xi, U\right) = \operatorname{R}\left(d, M\right)) \land ((\forall t, 0 \leq \operatorname{V}\left(t\right)) \land ((\sum_{t} \operatorname{V}\left(t\right) = 1) \land ((\operatorname{pushforward}\left(xi, V\right) = \operatorname{Q}\left(d, M\right)) \land ((\operatorname{totalVariation}\left(U, V\right) = \operatorname{totalVariation}\left(\operatorname{R}\left(d, M\right), \operatorname{Q}\left(d, M\right)\right)) \land ((((2 \leq d) \land (3 \cdot d \leq M)) \Rightarrow \forall A, (\operatorname{max}\left(0, \operatorname{V}\left(A\right) - epsilon\right) \leq \operatorname{U}\left(A\right)) \land (\operatorname{U}\left(A\right) \leq \operatorname{min}\left(1, \operatorname{V}\left(A\right) + epsilon\right))) \land (d = 1 \Rightarrow U = V))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/TreeParityKernel.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Yaël Dillies, Bhavik Mehta, Huỳnh Trần Khanh, Stuart Presnell and Mathlib contributors (2026). *Mathlib.Data.Sym.Card — Stars and bars*. URL: <https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Data/Sym/Card.lean>.

*Acknowledgement.* Kyle Siegrist (2026). *Random: Probability, Mathematical Statistics, Stochastic Processes*. URL: <https://www.randomservices.org/random/>.

*Commentary.*

For every natural composition a,b with a+b>=1 and M>=d, the parity pushforward of U equals R(d,M). The reference mass is nonnegative, sums to one, and its parity pushforward equals Q(d,M). The total variation of the two tree laws equals that of R and Q. When d>=2 and M>=3d, every event A in the actual composition fiber satisfies max(0,V(A)-epsilon)<=U(A)<=min(1,V(A)+epsilon), where epsilon=min(1,5(sqrt(d)/M+d(d-1)/M^2)). For d=1 the actual and reference tree laws coincide. The shape-gap equivalence and the prescribed-parity weak-composition count give, for every legal parity vector xi, exactly catalan(n-1) times choose((M-h)/2+d-1,d-1) actual trees with record xi, and none for an illegal vector. This fiber count normalizes a common uniform conditional kernel. Within each parity fiber the two tree laws differ by one sign, so the deterministic parity channel preserves their total variation. The finite parity bound and the event characterization of total variation give both event inequalities. For d=1 the single gap has the parity of M, the two parity masses agree, and so the tree laws agree.

## References

- Truth anchor: `D5/S3/TotalVariation/TreeParityKernel.Q`
- Truth anchor: `D5/S3/TotalVariation/TreeParityKernel.R`
- Truth anchor: `D5/S3/TotalVariation/TreeParityKernel.gapParity`
- Truth anchor: `D5/S3/TotalVariation/TreeParityKernel.intervals`
- Truth anchor: `D5/S3/TotalVariation/TreeParityKernel.referenceTreeMass`
- Truth anchor: `D5/S3/TotalVariation/TreeParityKernel.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport](../Arith/FibonacciAtomic/GenealogicalFiberTransport.md)
- Dependency: [D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEnumeration](../Combinatorics/Geometry/CrownOrderPolytopeEnumeration.md)
- Dependency: [D5/S3/TotalVariation/Equality/FiberwiseEqualDistanceLift](Equality/FiberwiseEqualDistanceLift.md)
- Dependency: [D5/S3/TotalVariation/Metric](Metric.md)
- Dependency: [D5/S3/TotalVariation/ParityFiniteTV](ParityFiniteTV.md)
- Dependency: [D5/S3/TotalVariation/ParityKernelMasses](ParityKernelMasses.md)
