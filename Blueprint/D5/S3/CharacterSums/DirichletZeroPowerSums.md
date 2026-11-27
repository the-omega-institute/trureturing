# All zeros with analytic multiplicity

## Abstract

Arithmetic moments and the actual Dirichlet zero divisor

Let χ be a primitive nonprincipal complex Dirichlet character of positive modulus q. The index set is the zero set of the original L-function, including its trivial zeros. Each distinct zero ρ carries the weight m(ρ) = analyticOrderNatAt(Lχ,ρ). Thus repeated zeros are counted with their actual analytic multiplicities. No hypothesis on the location of the nontrivial zeros is imposed.

For a complex Dirichlet character χ modulo q, moment(χ,k,t) is the negative real part of the sum over n ≥ 2 of Λ(n)χ(n)(log n)^k divided by k! n^(2+it). The finite moment uses 2 ≤ n ≤ X with the same normalization. The zero and one terms vanish. The bound is independent of t and q, and includes principal and imprimitive characters and k = 0.

**Definition 1.1 (The normalized complex summand).**

$$\forall q \in \operatorname{Naturals}\left(\right),\; \forall chi \in \operatorname{ComplexDirichletCharacters}\left(q\right),\; \forall k \in \operatorname{Naturals}\left(\right),\; \forall t \in \operatorname{Reals}\left(\right),\; \forall n \in \operatorname{Naturals}\left(\right),\; \operatorname{momentTerm}\left(chi, k, t, n\right) = \operatorname{inverse}\left(\operatorname{natToComplex}\left(\operatorname{factorial}\left(k\right)\right)\right) \cdot \operatorname{LSeriesTerm}\left((fun (m: \operatorname{Naturals}\left(\right)) \mapsto \operatorname{apply}\left(chi, \operatorname{natToZMod}\left(q, m\right)\right) \cdot \operatorname{realToComplex}\left(\operatorname{vonMangoldtReal}\left(m\right)\right) \cdot \operatorname{realToComplex}\left(\operatorname{realLog}\left(\operatorname{natToReal}\left(m\right)\right)\right)^{k}), 2 + \operatorname{realToComplex}\left(t\right) \cdot \operatorname{imaginaryUnit}\left(\right), n\right)$$

*Formalization.* `D5/S3/CharacterSums/DirichletZeroPowerSums.momentTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

LSeriesTerm(f,s,n) is zero at n = 0 and equals f(n)/n^s otherwise. The coefficient function uses the real von Mangoldt value and real logarithm, each cast to the complex numbers. The inverse factorial is also a complex scalar.

**Definition 1.2 (The full negative real moment).**

$$\forall q \in \operatorname{Naturals}\left(\right),\; \forall chi \in \operatorname{ComplexDirichletCharacters}\left(q\right),\; \forall k \in \operatorname{Naturals}\left(\right),\; \forall t \in \operatorname{Reals}\left(\right),\; \operatorname{moment}\left(chi, k, t\right) = \operatorname{neg}\left(\operatorname{re}\left(\operatorname{tsum}\left((fun (n: \operatorname{Naturals}\left(\right)) \mapsto \operatorname{momentTerm}\left(chi, k, t, n\right))\right)\right)\right)$$

*Formalization.* `D5/S3/CharacterSums/DirichletZeroPowerSums.moment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The unbounded tsum ranges over all natural numbers. The zero and one summands vanish; the minus sign is outside the real-part operation.

**Definition 1.3 (The arithmetic cutoff moment).**

$$\forall q \in \operatorname{Naturals}\left(\right),\; \forall chi \in \operatorname{ComplexDirichletCharacters}\left(q\right),\; \forall k \in \operatorname{Naturals}\left(\right),\; \forall X \in \operatorname{Naturals}\left(\right),\; \forall t \in \operatorname{Reals}\left(\right),\; \operatorname{finiteMoment}\left(chi, k, X, t\right) = \operatorname{neg}\left(\operatorname{re}\left(\operatorname{finsetSum}\left(\operatorname{range}\left(X + 1\right), (fun (n: \operatorname{Naturals}\left(\right)) \mapsto \operatorname{momentTerm}\left(chi, k, t, n\right))\right)\right)\right)$$

*Formalization.* `D5/S3/CharacterSums/DirichletZeroPowerSums.finiteMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite sum is over range(X+1), namely 0 ≤ n ≤ X. It uses the same complex summand and negative real part as the full moment, with no change of normalization.

**Theorem 1.4 (An explicit arithmetic cutoff).**

$$\forall q \in \operatorname{Naturals}\left(\right),\; \forall chi \in \operatorname{ComplexDirichletCharacters}\left(q\right),\; \forall k \in \operatorname{Naturals}\left(\right),\; \forall X \in \operatorname{Naturals}\left(\right),\; \forall t \in \operatorname{Reals}\left(\right),\; \operatorname{Summable}\left(\operatorname{momentTerms}\left(chi, k, t\right)\right) \land \left(\left(\operatorname{lt}\left(0, X\right) \Rightarrow \operatorname{complexErrorNorm}\left(chi, k, X, t\right) \le \operatorname{power}\left(2, k + 2\right) \cdot \left(k + 1\right) \cdot \operatorname{realPower}\left(X, \operatorname{ratio}\left(\operatorname{neg}\left(1\right), 2\right)\right)\right) \land \left(\operatorname{exp}\left(\operatorname{mul}\left(4, \operatorname{add}\left(k, 1\right)\right)\right) \le X \Rightarrow \left(\operatorname{complexErrorNorm}\left(chi, k, X, t\right) \le \operatorname{power}\left(\frac{2}{3}, k + 1\right) \land \operatorname{abs}\left(\operatorname{sub}\left(\operatorname{moment}\left(chi, k, t\right), \operatorname{finiteMoment}\left(chi, k, X, t\right)\right)\right) \le \operatorname{power}\left(\frac{2}{3}, k + 1\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/DirichletZeroPowerSums.finite_moment_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cutoff condition is exp(4(k+1)) ≤ X. The error between the full and finite negative real parts is at most (2/3)^(k+1), as is the norm of the complex series error. The series converges without a cutoff condition. Thus X may be the ceiling of exp(4(k+1)), or any larger natural number.

Use |χ(n)| ≤ 1 and Λ(n) ≤ log n. The exponential series bounds (log n/2)^(k+1)/(k+1)! by √n. Consequently the normalized summand is bounded by 2^(k+1)(k+1)n^(-3/2). The integral test bounds its tail after every positive X by 2^(k+2)(k+1)X^(-1/2). The cutoff and k+1 ≤ 2^k reduce this to (4/exp(2))^(k+1) ≤ (2/3)^(k+1).

The cutoff estimate holds for every character, including principal and imprimitive characters. Combined with the zero power-sum identity below, it transports finite arithmetic tests to bounds on the full zero moments.

**Theorem 1.5 (The absolutely convergent moment identity).**

$$\forall q \in \operatorname{PositiveNaturals}\left(\right),\; \forall chi \in \operatorname{ComplexDirichletCharacters}\left(q\right),\; \left(\operatorname{IsPrimitive}\left(chi\right) \land \operatorname{Nonprincipal}\left(chi\right)\right) \Rightarrow \left(\forall k \in \operatorname{PositiveNaturals}\left(\right),\; \forall t \in \operatorname{Reals}\left(\right),\; \operatorname{HasSum}\left((fun (rho: \operatorname{zeroSet}\left(\operatorname{LFunction}\left(chi\right)\right)) \mapsto \operatorname{natToComplex}\left(\operatorname{analyticOrderNatAt}\left(\operatorname{LFunction}\left(chi\right), rho\right)\right) \cdot \operatorname{power}\left(\operatorname{inverse}\left(2 + \operatorname{realToComplex}\left(t\right) \cdot \operatorname{imaginaryUnit}\left(\right) - rho\right), k + 1\right)), \operatorname{neg}\left(\operatorname{tsum}\left((fun (n: \operatorname{Naturals}\left(\right)) \mapsto \operatorname{momentTerm}\left(chi, k, t, n\right))\right)\right)\right) \land \left(\operatorname{Summable}\left((fun (rho: \operatorname{zeroSet}\left(\operatorname{LFunction}\left(chi\right)\right)) \mapsto \operatorname{norm}\left(\operatorname{natToComplex}\left(\operatorname{analyticOrderNatAt}\left(\operatorname{LFunction}\left(chi\right), rho\right)\right) \cdot \operatorname{power}\left(\operatorname{inverse}\left(2 + \operatorname{realToComplex}\left(t\right) \cdot \operatorname{imaginaryUnit}\left(\right) - rho\right), k + 1\right)\right))\right) \land \operatorname{moment}\left(chi, k, t\right) = \operatorname{re}\left(\operatorname{tsum}\left((fun (rho: \operatorname{zeroSet}\left(\operatorname{LFunction}\left(chi\right)\right)) \mapsto \operatorname{natToComplex}\left(\operatorname{analyticOrderNatAt}\left(\operatorname{LFunction}\left(chi\right), rho\right)\right) \cdot \operatorname{power}\left(\operatorname{inverse}\left(2 + \operatorname{realToComplex}\left(t\right) \cdot \operatorname{imaginaryUnit}\left(\right) - rho\right), k + 1\right))\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/CharacterSums/DirichletZeroPowerSums.moment_zero_power_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real t and positive integer k, the complex zero power sum equals the negative of the normalized arithmetic series. Its real part is precisely moment(χ,k,t). The norm series also converges, so the identity is independent of the order in which zeros are summed.

To use the entire-function difference formula for the original L-function, first bound the reciprocal Gamma function globally. On the right half-plane its vertical product and the positive global minimum of the real Gamma function give an exponential height bound. On the left half-plane the reflection formula reduces it to the right-half-plane Gamma growth bound, multiplied by a sine of exponential height. Both estimates are bounded by exp(C(1+|s|)^(3/2)). Combining this with completed L-function growth proves the same type of bound for Lχ itself, including the points where the meromorphic Gamma factor has a pole.

The general logarithmic derivative power-sum theorem applies to the entire Lχ using its nonzero value at the center 2+it; the general theorem needs only this local nonvanishing. The completed growth and Gamma interfaces are reused directly from DirichletTrivialZeros. On Re(s)>1, the logarithmic derivative is the negative L-series of χΛ. Differentiating that absolutely convergent L-series k times inserts (−log n)^k. The factorial and sign normalizations then give the stated complex identity. Iterated coefficient multiplication uses Mathlib mul_left_iterate_apply on the function multiplication monoid.

The restriction k≥1 removes the undetermined constant in the logarithmic derivative. Primitivity is used for the completed functional equation and its global growth bound; nonprincipality supplies entire continuation. The result does not assert the finite arithmetic inequalities needed for zero exclusion.

## References

- Truth anchor: `D5/S3/CharacterSums/DirichletZeroPowerSums.finiteMoment`
- Truth anchor: `D5/S3/CharacterSums/DirichletZeroPowerSums.finite_moment_error`
- Truth anchor: `D5/S3/CharacterSums/DirichletZeroPowerSums.moment`
- Truth anchor: `D5/S3/CharacterSums/DirichletZeroPowerSums.momentTerm`
- Truth anchor: `D5/S3/CharacterSums/DirichletZeroPowerSums.moment_zero_power_hasSum`
- Dependency: [D5/S3/Analytic/Resolvent/EntireLogDerivPowers](../Analytic/Resolvent/EntireLogDerivPowers.md)
- Dependency: [D5/S3/CharacterSums/DirichletTrivialZeros](DirichletTrivialZeros.md)
