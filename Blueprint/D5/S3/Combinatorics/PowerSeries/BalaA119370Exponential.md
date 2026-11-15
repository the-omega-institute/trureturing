# Bala's A119370 exponential identity

## Abstract

The independently normalized A119370 quadratic series equals Bala's formal exponential at every coefficient, and agrees with the printed constant-one square-root branch.

All series have rational coefficients. The topology used to express HasSum is coefficientwise convergence with discrete rational coefficients; each coefficient below is a finite sum. No analytic convergence assumption is made.

**Definition 1.1 (The independent quadratic source).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsSourceSeries}\left(A\right)) \iff ((\operatorname{constantCoeff}\left(A\right) = 1) \land (A = 1 + X \cdot (A)^{2} + (X)^{2} \cdot \left((A)^{2} - A\right)))$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/BalaA119370Exponential.IsSourceSeries` (`✓ std3`).

*Citation.* Peter Bala; Paul D. Hanna (2024). *OEIS A119370, Bala's formal-exponential identity conjecture*. URL: <https://oeis.org/A119370>.

*Commentary.*

OEIS A119370, revision 37, NAME: "G.f. satisfies A(x) = 1 + x*A(x)^2 + x^2*(A(x)^2 - A(x))." The constant coefficient is one. The source is specified by this equation before any exponential is used.

**Definition 1.2 (The full finite binomial-square row).**

$$\forall n: \mathbb{N}, \operatorname{row}\left(n\right) = \operatorname{Finset.sum}\left(\operatorname{range}\left(n + 1\right), (fun k: \mathbb{N} \mapsto \operatorname{C}\left(((\operatorname{Nat.choose}\left(n, k\right): \mathbb{Q}))^{2}\right) \cdot (1 + X)^{k})\right)$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/BalaA119370Exponential.row` (`✓ std3`).

*Citation.* Peter Bala; Paul D. Hanna (2024). *OEIS A119370, Bala's formal-exponential identity conjecture*. URL: <https://oeis.org/A119370>.

*Commentary.*

The finite sum in Bala's FORMULA runs from k=0 through k=n. Its scalar binomial square is embedded as a constant series. The X in each factor is the same formal variable as the outer power of X in the logarithm.

**Definition 1.3 (The locally finite logarithmic sum).**

$$\forall m: \mathbb{N}, \operatorname{coeff}\left(m, logarithm\right) = \operatorname{Finset.sum}\left(\operatorname{Icc}\left(1, m\right), (fun n: \mathbb{N} \mapsto \frac{1}{(n: \mathbb{Q})} \cdot \operatorname{coeff}\left(m - n, \operatorname{row}\left(n\right)\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/BalaA119370Exponential.logarithm` (`✓ std3`).

*Citation.* Peter Bala; Paul D. Hanna (2024). *OEIS A119370, Bala's formal-exponential identity conjecture*. URL: <https://oeis.org/A119370>.

*Commentary.*

This defines the whole series L by its degree-m coefficient. Only positive indices n through m occur. Equivalently L is the sum of X^n row(n)/n for n at least one. Its constant coefficient is zero.

**Definition 1.4 (The formal exponential).**

$$\forall f: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{formalExp}\left(f\right) = \operatorname{PowerSeries.subst}\left(f, \operatorname{PowerSeries.exp}\left(\mathbb{Q}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/BalaA119370Exponential.formalExp` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At a zero-constant inner series f, this is the admissible substitution of f into the formal exponential. Its coefficients are the sums of f^j/j!, including j=0. The result below proves both the whole formal sum and the explicit degree-m finite formula for L.

**Definition 1.5 (The printed discriminant).**

$$discriminant = (1 + (X)^{2})^{2} - 4 \cdot X \cdot \left(1 + X\right)$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/BalaA119370Exponential.discriminant` (`✓ std3`).

*Citation.* Peter Bala; Paul D. Hanna (2024). *OEIS A119370, Bala's formal-exponential identity conjecture*. URL: <https://oeis.org/A119370>.

*Commentary.*

OEIS A119370, FORMULA: "A(x) = ((1+x^2) - sqrt( (1+x^2)^2 - 4*x*(1+x) ))/(2*x*(1+x))." The selected square root has constant coefficient one.

**Definition 1.6 (Lawful division in the printed branch).**

$$\forall S: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{printedBranch}\left(S\right) = \operatorname{PowerSeries.mk}\left((fun n: \mathbb{N} \mapsto \operatorname{coeff}\left(n + 1, 1 + (X)^{2} - S\right))\right) \cdot (2 \cdot \left(1 + X\right))^{-1}$$

*Formalization.* `D5/S3/Combinatorics/PowerSeries/BalaA119370Exponential.printedBranch` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

After proving the numerator divisible by X, its coefficient shift removes that factor. The remaining denominator 2(1+X) has constant coefficient two and is a unit. This expression never inverts X.

**Theorem 1.7 (The complete exponential identity and branch correspondence).**

$$(\exists! A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsSourceSeries}\left(A\right)) \land ((\operatorname{constantCoeff}\left(logarithm\right) = 0) \land ((\operatorname{HasSum}\left((fun n: \mathbb{N} \mapsto \operatorname{C}\left(\frac{1}{(n + 1: \mathbb{Q})}\right) \cdot \operatorname{row}\left(n + 1\right) \cdot (X)^{n + 1}), logarithm\right)) \land ((\forall m: \mathbb{N}, \forall n: \mathbb{N}, (m<n) \Rightarrow (\operatorname{coeff}\left(m, \operatorname{C}\left(\frac{1}{(n: \mathbb{Q})}\right) \cdot \operatorname{row}\left(n\right) \cdot (X)^{n}\right) = 0)) \land ((\operatorname{HasSum}\left((fun j: \mathbb{N} \mapsto \operatorname{C}\left(\frac{1}{(\operatorname{Nat.factorial}\left(j\right): \mathbb{Q})}\right) \cdot (logarithm)^{j}), \operatorname{formalExp}\left(logarithm\right)\right)) \land ((\forall m: \mathbb{N}, \forall j: \mathbb{N}, (m<j) \Rightarrow (\operatorname{coeff}\left(m, (logarithm)^{j}\right) = 0)) \land ((\forall m: \mathbb{N}, \operatorname{coeff}\left(m, \operatorname{formalExp}\left(logarithm\right)\right) = \operatorname{Finset.sum}\left(\operatorname{range}\left(m + 1\right), (fun j: \mathbb{N} \mapsto \frac{1}{(\operatorname{Nat.factorial}\left(j\right): \mathbb{Q})} \cdot \operatorname{coeff}\left(m, (logarithm)^{j}\right))\right)) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsSourceSeries}\left(A\right)) \Rightarrow ((A = 1 + X \cdot \operatorname{formalExp}\left(logarithm\right)) \land ((\forall m: \mathbb{N}, \operatorname{coeff}\left(m, A\right) = \operatorname{coeff}\left(m, 1 + X \cdot \operatorname{formalExp}\left(logarithm\right)\right)) \land ((\exists! S: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{constantCoeff}\left(S\right) = 1) \land ((S)^{2} = discriminant)) \land (\forall S: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{constantCoeff}\left(S\right) = 1) \Rightarrow (((S)^{2} = discriminant) \Rightarrow ((X\mid1 + (X)^{2} - S) \land (A = \operatorname{printedBranch}\left(S\right)))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PowerSeries/BalaA119370Exponential.result` (`✓ std3`). ∎

*Resolves.* `Problems/bala-a119370-exponential` (proved) by `D5/S3/Combinatorics/PowerSeries/BalaA119370Exponential.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bala-a119370-exponential","declaration_gid":"D5/S3/Combinatorics/PowerSeries/BalaA119370Exponential.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala; Paul D. Hanna (2024). *OEIS A119370, Bala's formal-exponential identity conjecture*. URL: <https://oeis.org/A119370>.

*Acknowledgement.* Ira M. Gessel (2016). *Lagrange Inversion*. DOI: [10.48550/arXiv.1609.05988](https://doi.org/10.48550/arXiv.1609.05988). URL: <https://arxiv.org/abs/1609.05988v1>.

*Commentary.*

A normalized coefficient contraction constructs the unique source A independently. A second contraction constructs C in Q[Y][[z]] with C(0)=1 and C=(1+zC)(1+YzC). For each rational y, put f=zC_y and R(t)=(1+t)(1+yt). Apply the original rational power-coefficient Lagrange theorem inside the logarithmic client. The derivative of log R times R is R'; the finite coefficient sum gives n[z^n]log C_y=[t^n]R(t)^n. Binomial convolution gives the complete square-binomial row. Polynomial extensionality lifts this identity from every rational y to Q[Y]. The existing continuous diagonal evaluates z=X and Y=1+X, retaining only outer indices n<=m in degree m. It preserves the logarithmic substitution and identifies log b=L for b=D(C). Its quadratic implies that 1+Xb satisfies the original source equation. Original-source uniqueness and formal exp/log inversion give A=1+X Exp(L). Finally S=1+X^2-2X(1+X)A has the required square. Any other normalized root T satisfies (T-S)(T+S)=0; T+S is a unit with constant coefficient two, so T=S. The numerator equals X*2(1+X)A, which proves the stated shift and unit quotient. The coefficient-zero identity, all finite-row endpoints and the exponential's zeroth power are included.

## References

- Truth anchor: `D5/S3/Combinatorics/PowerSeries/BalaA119370Exponential.IsSourceSeries`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/BalaA119370Exponential.discriminant`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/BalaA119370Exponential.formalExp`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/BalaA119370Exponential.logarithm`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/BalaA119370Exponential.printedBranch`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/BalaA119370Exponential.result`
- Truth anchor: `D5/S3/Combinatorics/PowerSeries/BalaA119370Exponential.row`
- Dependency: [D5/S1/Recurrence/Invariants/PowerSeriesNormalizedContraction](../../../S1/Recurrence/Invariants/PowerSeriesNormalizedContraction.md)
- Dependency: [D5/S3/Arith/Congruence/TebniA350759PrimeCongruences](../../Arith/Congruence/TebniA350759PrimeCongruences.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge](../Nonnesting/CatalanLagrangeBridge.md)
- Dependency: [D5/S3/Combinatorics/Nonnesting/NonnestingOneThreeTwoTwo](../Nonnesting/NonnestingOneThreeTwoTwo.md)
- Dependency: [D5/S3/Combinatorics/PowerSeries/PositiveNewtonSums](PositiveNewtonSums.md)
